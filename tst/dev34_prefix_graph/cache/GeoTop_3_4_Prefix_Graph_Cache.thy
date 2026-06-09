theory GeoTop_3_4_Prefix_Graph_Cache
  imports "GeoTop34PrefixBaseDirty.GeoTop_3_4_Prefix_Base"
begin

lemma geotop_finite_complex_vertices_finite_graph_prefix:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hfin: "finite K"
  shows "finite (geotop_complex_vertices K)"
proof -
  have hverts_eq: "geotop_complex_vertices K = {v. {v} \<in> K}"
    by (rule geotop_complex_vertices_eq_0_simplexes[OF hK])
  define S where "S = {\<sigma>\<in>K. \<exists>v. \<sigma> = {v}}"
  have hS_fin: "finite S"
    unfolding S_def using hfin by (by100 simp)
  have hS_each_fin: "\<forall>\<sigma>\<in>S. finite \<sigma>"
    unfolding S_def by (by100 blast)
  have hUnion_fin: "finite (\<Union>S)"
  proof (rule finite_Union[OF hS_fin])
    fix \<sigma>
    assume h\<sigma>S: "\<sigma> \<in> S"
    show "finite \<sigma>"
      using hS_each_fin h\<sigma>S by (by100 blast)
  qed
  have hUnion_eq: "\<Union>S = {v. {v} \<in> K}"
  proof
    show "\<Union>S \<subseteq> {v. {v} \<in> K}"
    proof
      fix x
      assume hx: "x \<in> \<Union>S"
      obtain \<sigma> where h\<sigma>S: "\<sigma> \<in> S" and hx\<sigma>: "x \<in> \<sigma>"
        using hx by (by100 blast)
      obtain v where h\<sigma>eq: "\<sigma> = {v}"
        using h\<sigma>S unfolding S_def by (by100 blast)
      have "{x} \<in> K"
        using h\<sigma>S hx\<sigma> h\<sigma>eq unfolding S_def by (by100 blast)
      show "x \<in> {v. {v} \<in> K}"
        using \<open>{x} \<in> K\<close> by (by100 simp)
    qed
    show "{v. {v} \<in> K} \<subseteq> \<Union>S"
    proof
      fix x
      assume hx: "x \<in> {v. {v} \<in> K}"
      have hxK: "{x} \<in> K"
        using hx by (by100 simp)
      have "{x} \<in> S"
        unfolding S_def using hxK by (by100 blast)
      show "x \<in> \<Union>S"
        using \<open>{x} \<in> S\<close> by (by100 blast)
    qed
  qed
  show ?thesis
    using hverts_eq hUnion_eq hUnion_fin by (by100 simp)
qed

lemma geotop_finite_linear_graph_vertices_finite_graph_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  shows "finite (geotop_complex_vertices L)"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  show ?thesis
    by (rule geotop_finite_complex_vertices_finite_graph_prefix[OF hcomplex hfin])
qed

lemma geotop_finite_linear_graph_oriented_edge_states_finite_graph_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  shows "finite {(w,e). {w} \<in> L \<and> e \<in> L \<and> geotop_is_edge e \<and> w \<in> e}"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have hverts_fin: "finite (geotop_complex_vertices L)"
    by (rule geotop_finite_linear_graph_vertices_finite_graph_prefix[OF hL hfin])
  let ?S = "{(w,e). {w} \<in> L \<and> e \<in> L \<and> geotop_is_edge e \<and> w \<in> e}"
  have hprod_fin: "finite (geotop_complex_vertices L \<times> L)"
    using hverts_fin hfin by (by100 simp)
  have hsub: "?S \<subseteq> geotop_complex_vertices L \<times> L"
  proof
    fix x
    assume hx: "x \<in> ?S"
    obtain w e where hx_eq: "x = (w,e)" and hwL: "{w} \<in> L" and heL: "e \<in> L"
      using hx by (by100 blast)
    have hw_vertex: "w \<in> geotop_complex_vertices L"
      using geotop_complex_vertices_eq_0_simplexes[OF hcomplex] hwL by (by100 blast)
    show "x \<in> geotop_complex_vertices L \<times> L"
      using hx_eq hw_vertex heL by (by100 simp)
  qed
  show ?thesis
    by (rule finite_subset[OF hsub hprod_fin])
qed

lemma geotop_finite_components_homeomorphism_prefix:
  assumes hhom: "homeomorphism A B f g"
  assumes hfin: "finite (components B)"
  shows "finite (components A)"
proof -
  have hcomp_sub:
    "components A \<subseteq> (\<lambda>D. g ` D) ` components B"
  proof
    fix C
    assume hC: "C \<in> components A"
    obtain x where hxA: "x \<in> A"
      and hC_eq: "C = connected_component_set A x"
      using hC componentsE by (by100 blast)
    have hfxB: "f x \<in> B"
      using hhom hxA unfolding homeomorphism_def by (by100 blast)
    define D where "D = connected_component_set B (f x)"
    have hD_comp: "D \<in> components B"
      unfolding D_def by (rule componentsI[OF hfxB])
    have hBA: "homeomorphism B A g f"
      by (rule homeomorphism_symD[OF hhom])
    have hcc:
      "connected_component_set A (g (f x)) =
        g ` connected_component_set B (f x)"
      by (rule connected_component_set_homeomorphism[OF hBA hfxB])
    have hgf: "g (f x) = x"
      using hhom hxA by (rule homeomorphism_apply1)
    have "C = g ` D"
      using hC_eq hcc hgf unfolding D_def by (by100 simp)
    thus "C \<in> (\<lambda>D. g ` D) ` components B"
      using hD_comp by (by100 blast)
  qed
  have himage_fin: "finite ((\<lambda>D. g ` D) ` components B)"
    by (rule finite_imageI[OF hfin])
  show "finite (components A)"
    by (rule finite_subset[OF hcomp_sub himage_fin])
qed

lemma geotop_finite_components_punctured_circle_three_points_prefix:
  fixes P q\<^sub>1 q\<^sub>2 q\<^sub>3 :: "real^2"
  assumes hr: "r > 0"
  assumes hq\<^sub>1: "q\<^sub>1 \<in> sphere P r"
  assumes hq\<^sub>2: "q\<^sub>2 \<in> sphere P r"
  assumes hq\<^sub>3: "q\<^sub>3 \<in> sphere P r"
  assumes hq\<^sub>12: "q\<^sub>1 \<noteq> q\<^sub>2"
  assumes hq\<^sub>13: "q\<^sub>1 \<noteq> q\<^sub>3"
  assumes hq\<^sub>23: "q\<^sub>2 \<noteq> q\<^sub>3"
  shows "finite (components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}))"
proof -
  let ?S = "sphere P r"
  let ?A = "?S - {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
  let ?L = "{x::real^2. (q\<^sub>2 - q\<^sub>1) \<bullet> x = 0}"
  have hc_nonzero: "q\<^sub>2 - q\<^sub>1 \<noteq> 0"
    using hq\<^sub>12 by (by100 auto)
  have hpunctured_homeo_line: "(?S - {q\<^sub>1}) homeomorphic ?L"
    by (rule homeomorphic_punctured_sphere_hyperplane
        [OF hr hq\<^sub>1 hc_nonzero])
  obtain f g where hfg: "homeomorphism (?S - {q\<^sub>1}) ?L f g"
    using hpunctured_homeo_line unfolding homeomorphic_def by (by100 blast)
  define a where "a = f q\<^sub>2"
  define b where "b = f q\<^sub>3"
  have hq\<^sub>2_dom: "q\<^sub>2 \<in> ?S - {q\<^sub>1}"
    using hq\<^sub>2 hq\<^sub>12 by (by100 blast)
  have hq\<^sub>3_dom: "q\<^sub>3 \<in> ?S - {q\<^sub>1}"
    using hq\<^sub>3 hq\<^sub>13 by (by100 blast)
  have hf_img: "f ` (?S - {q\<^sub>1}) = ?L"
    using hfg by (rule homeomorphism_image1)
  have hgf: "\<And>x. x \<in> ?S - {q\<^sub>1} \<Longrightarrow> g (f x) = x"
    using hfg by (rule homeomorphism_apply1)
  have hinj: "inj_on f (?S - {q\<^sub>1})"
  proof (unfold inj_on_def, intro ballI impI)
    fix x y
    assume hx: "x \<in> ?S - {q\<^sub>1}"
      and hy: "y \<in> ?S - {q\<^sub>1}"
      and hxy: "f x = f y"
    have "g (f x) = g (f y)"
      using hxy by (by100 simp)
    thus "x = y"
      using hgf[OF hx] hgf[OF hy] by (by100 simp)
  qed
  have hcircle_line_image:
    "f ` ?A = ?L - {a, b}"
  proof
    show "f ` ?A \<subseteq> ?L - {a, b}"
    proof
      fix y
      assume hy: "y \<in> f ` ?A"
      obtain x where hxA: "x \<in> ?A" and hy_eq: "y = f x"
        using hy by (by100 blast)
      have hx_dom: "x \<in> ?S - {q\<^sub>1}"
        using hxA by (by100 blast)
      have hx_ne_q\<^sub>2: "x \<noteq> q\<^sub>2"
        using hxA by (by100 blast)
      have hx_ne_q\<^sub>3: "x \<noteq> q\<^sub>3"
        using hxA by (by100 blast)
      have hy_L: "y \<in> ?L"
        using hy_eq hx_dom hf_img by (by100 blast)
      have hy_ne_a: "y \<noteq> a"
      proof
        assume hya: "y = a"
        have "f x = f q\<^sub>2"
          using hya hy_eq unfolding a_def by (by100 simp)
        hence "x = q\<^sub>2"
          using hinj hx_dom hq\<^sub>2_dom unfolding inj_on_def by (by100 blast)
        thus False
          using hx_ne_q\<^sub>2 by (by100 blast)
      qed
      have hy_ne_b: "y \<noteq> b"
      proof
        assume hyb: "y = b"
        have "f x = f q\<^sub>3"
          using hyb hy_eq unfolding b_def by (by100 simp)
        hence "x = q\<^sub>3"
          using hinj hx_dom hq\<^sub>3_dom unfolding inj_on_def by (by100 blast)
        thus False
          using hx_ne_q\<^sub>3 by (by100 blast)
      qed
      show "y \<in> ?L - {a, b}"
        using hy_L hy_ne_a hy_ne_b by (by100 blast)
    qed
    show "?L - {a, b} \<subseteq> f ` ?A"
    proof
      fix y
      assume hy: "y \<in> ?L - {a, b}"
      have hy_L: "y \<in> ?L"
        using hy by (by100 blast)
      have hy_ne_a: "y \<noteq> a"
        using hy by (by100 blast)
      have hy_ne_b: "y \<noteq> b"
        using hy by (by100 blast)
      have hy_img: "y \<in> f ` (?S - {q\<^sub>1})"
        using hf_img hy_L by (by100 simp)
      obtain x where hx_dom: "x \<in> ?S - {q\<^sub>1}" and hfx: "f x = y"
        using hy_img by (by100 blast)
      have hx_ne_q\<^sub>2: "x \<noteq> q\<^sub>2"
      proof
        assume hxq\<^sub>2: "x = q\<^sub>2"
        hence "y = a"
          using hfx unfolding a_def by (by100 simp)
        thus False
          using hy_ne_a by (by100 blast)
      qed
      have hx_ne_q\<^sub>3: "x \<noteq> q\<^sub>3"
      proof
        assume hxq\<^sub>3: "x = q\<^sub>3"
        hence "y = b"
          using hfx unfolding b_def by (by100 simp)
        thus False
          using hy_ne_b by (by100 blast)
      qed
      have "x \<in> ?A"
        using hx_dom hx_ne_q\<^sub>2 hx_ne_q\<^sub>3 by (by100 blast)
      thus "y \<in> f ` ?A"
        using hfx by (by100 blast)
    qed
  qed
  have hcircle_line_homeomorphism:
    "homeomorphism ?A (?L - {a, b}) f g"
  proof (rule homeomorphism_of_subsets[OF hfg])
    show "?A \<subseteq> ?S - {q\<^sub>1}"
      by (by100 blast)
    show "?L - {a, b} \<subseteq> ?L"
      by (by100 blast)
    show "f ` ?A = ?L - {a, b}"
      by (rule hcircle_line_image)
  qed
  have hline_components_finite: "finite (components (?L - {a, b}))"
  proof -
    have hL_dim: "aff_dim ?L = 1"
      using hc_nonzero aff_dim_hyperplane[of "q\<^sub>2 - q\<^sub>1" 0]
      by (by100 simp)
    have hreal_dim: "aff_dim (UNIV::real set) = 1"
      by (by100 simp)
    have hL_homeo_real: "?L homeomorphic (UNIV::real set)"
    proof (rule homeomorphic_affine_sets)
      show "affine ?L"
        by (rule affine_hyperplane)
      show "affine (UNIV::real set)"
        by (rule affine_UNIV)
      show "aff_dim ?L = aff_dim (UNIV::real set)"
        using hL_dim hreal_dim by (by100 simp)
    qed
    obtain h j where hhj: "homeomorphism ?L (UNIV::real set) h j"
      using hL_homeo_real unfolding homeomorphic_def by (by100 blast)
    have ha_L: "a \<in> ?L"
      unfolding a_def using hq\<^sub>2_dom hf_img by (by100 blast)
    have hb_L: "b \<in> ?L"
      unfolding b_def using hq\<^sub>3_dom hf_img by (by100 blast)
    have hjh: "\<And>x. x \<in> ?L \<Longrightarrow> j (h x) = x"
      using hhj by (rule homeomorphism_apply1)
    have h_line_real_image:
      "h ` (?L - {a, b}) = (UNIV::real set) - {h a, h b}"
    proof
      show "h ` (?L - {a, b}) \<subseteq> (UNIV::real set) - {h a, h b}"
      proof
        fix y
        assume hy: "y \<in> h ` (?L - {a, b})"
        obtain x where hx: "x \<in> ?L - {a, b}" and hy_eq: "y = h x"
          using hy by (by100 blast)
        have hxL: "x \<in> ?L"
          using hx by (by100 blast)
        have hx_ne_a: "x \<noteq> a"
          using hx by (by100 blast)
        have hx_ne_b: "x \<noteq> b"
          using hx by (by100 blast)
        have hy_ne_ha: "y \<noteq> h a"
        proof
          assume hya: "y = h a"
          have "j (h x) = j (h a)"
            using hya hy_eq by (by100 simp)
          hence "x = a"
            using hjh[OF hxL] hjh[OF ha_L] by (by100 simp)
          thus False
            using hx_ne_a by (by100 blast)
        qed
        have hy_ne_hb: "y \<noteq> h b"
        proof
          assume hyb: "y = h b"
          have "j (h x) = j (h b)"
            using hyb hy_eq by (by100 simp)
          hence "x = b"
            using hjh[OF hxL] hjh[OF hb_L] by (by100 simp)
          thus False
            using hx_ne_b by (by100 blast)
        qed
        show "y \<in> (UNIV::real set) - {h a, h b}"
          using hy_ne_ha hy_ne_hb by (by100 blast)
      qed
      show "(UNIV::real set) - {h a, h b} \<subseteq> h ` (?L - {a, b})"
      proof
        fix y
        assume hy: "y \<in> (UNIV::real set) - {h a, h b}"
        have hjy_L: "j y \<in> ?L"
          using hhj unfolding homeomorphism_def by (by100 blast)
        have hhy: "h (j y) = y"
          using hhj by (rule homeomorphism_apply2[of ?L "UNIV::real set" h j y, simplified])
        have hjy_ne_a: "j y \<noteq> a"
        proof
          assume hja: "j y = a"
          hence "y = h a"
            using hhy by (by100 simp)
          thus False
            using hy by (by100 blast)
        qed
        have hjy_ne_b: "j y \<noteq> b"
        proof
          assume hjb: "j y = b"
          hence "y = h b"
            using hhy by (by100 simp)
          thus False
            using hy by (by100 blast)
        qed
        have "j y \<in> ?L - {a, b}"
          using hjy_L hjy_ne_a hjy_ne_b by (by100 blast)
        hence "h (j y) \<in> h ` (?L - {a, b})"
          by (rule imageI)
        thus "y \<in> h ` (?L - {a, b})"
          using hhy by (by100 simp)
      qed
    qed
    have hline_real_homeomorphism:
      "homeomorphism (?L - {a, b}) ((UNIV::real set) - {h a, h b}) h j"
    proof (rule homeomorphism_of_subsets[OF hhj])
      show "?L - {a, b} \<subseteq> ?L"
        by (by100 blast)
      show "(UNIV::real set) - {h a, h b} \<subseteq> UNIV"
        by (by100 blast)
      show "h ` (?L - {a, b}) = (UNIV::real set) - {h a, h b}"
        by (rule h_line_real_image)
    qed
    have hreal_fin: "finite (components ((UNIV::real set) - {h a, h b}))"
      by (rule finite_components_real_complement_two_points)
    show ?thesis
      by (rule geotop_finite_components_homeomorphism_prefix
          [OF hline_real_homeomorphism hreal_fin])
  qed
  show ?thesis
    by (rule geotop_finite_components_homeomorphism_prefix
        [OF hcircle_line_homeomorphism hline_components_finite])
qed

lemma geotop_punctured_circle_component_closure_three_points_bound_prefix:
  fixes P q\<^sub>1 q\<^sub>2 q\<^sub>3 :: "real^2"
  assumes hr: "r > 0"
  assumes hq\<^sub>1: "q\<^sub>1 \<in> sphere P r"
  assumes hq\<^sub>2: "q\<^sub>2 \<in> sphere P r"
  assumes hq\<^sub>3: "q\<^sub>3 \<in> sphere P r"
  assumes hq\<^sub>12: "q\<^sub>1 \<noteq> q\<^sub>2"
  assumes hq\<^sub>13: "q\<^sub>1 \<noteq> q\<^sub>3"
  assumes hq\<^sub>23: "q\<^sub>2 \<noteq> q\<^sub>3"
  assumes hK: "K \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"
  shows "card ({q\<^sub>1, q\<^sub>2, q\<^sub>3} \<inter> closure K) \<le> 2"
proof -
  have hmiss: "\<exists>q\<in>{q\<^sub>1, q\<^sub>2, q\<^sub>3}. q \<notin> closure K"
  proof -
    let ?S = "sphere P r"
    let ?L = "{x::real^2. (q\<^sub>2 - q\<^sub>1) \<bullet> x = 0}"
    have hq\<^sub>1_sphere: "q\<^sub>1 \<in> ?S"
      using hq\<^sub>1 by (by100 simp)
    have hq\<^sub>2_sphere: "q\<^sub>2 \<in> ?S"
      using hq\<^sub>2 by (by100 simp)
    have hq\<^sub>3_sphere: "q\<^sub>3 \<in> ?S"
      using hq\<^sub>3 by (by100 simp)
    have hc_nonzero: "q\<^sub>2 - q\<^sub>1 \<noteq> 0"
      using hq\<^sub>12 by (by100 auto)
    have hpunctured_homeo_line:
      "(?S - {q\<^sub>1}) homeomorphic ?L"
      by (rule homeomorphic_punctured_sphere_hyperplane
          [OF hr hq\<^sub>1_sphere hc_nonzero])
    obtain f g where hfg:
      "homeomorphism (?S - {q\<^sub>1}) ?L f g"
      using hpunctured_homeo_line unfolding homeomorphic_def by (by100 blast)
    define a where "a = f q\<^sub>2"
    define b where "b = f q\<^sub>3"
    have hK_sub_punctured:
      "K \<subseteq> ?S - {q\<^sub>1}"
    proof -
      have hK_sub_full: "K \<subseteq> ?S - {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
        using hK in_components_subset by (by100 blast)
      show ?thesis using hK_sub_full by (by100 blast)
    qed
    have hK_image_line:
      "f ` K \<subseteq> ?L - {a, b}"
    proof
      fix y assume hy: "y \<in> f ` K"
      obtain x where hxK: "x \<in> K" and hy_eq: "y = f x"
        using hy by (by100 blast)
      have hK_sub_full: "K \<subseteq> ?S - {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
        using hK in_components_subset by (by100 blast)
      have hx_dom: "x \<in> ?S - {q\<^sub>1}"
        using hxK hK_sub_punctured by (by100 blast)
      have hx_not_q\<^sub>2: "x \<noteq> q\<^sub>2"
        using hxK hK_sub_full by (by100 blast)
      have hx_not_q\<^sub>3: "x \<noteq> q\<^sub>3"
        using hxK hK_sub_full by (by100 blast)
      have hq\<^sub>2_dom: "q\<^sub>2 \<in> ?S - {q\<^sub>1}"
        using hq\<^sub>2_sphere hq\<^sub>12 by (by100 blast)
      have hq\<^sub>3_dom: "q\<^sub>3 \<in> ?S - {q\<^sub>1}"
        using hq\<^sub>3_sphere hq\<^sub>13 by (by100 blast)
      have hf_img: "f ` (?S - {q\<^sub>1}) = ?L"
        using hfg unfolding homeomorphism_def by (by100 blast)
      have hgf:
        "\<And>x. x \<in> ?S - {q\<^sub>1} \<Longrightarrow> g (f x) = x"
        using hfg unfolding homeomorphism_def by (by100 blast)
      have hinj: "inj_on f (?S - {q\<^sub>1})"
      proof (unfold inj_on_def, intro ballI impI)
        fix x y
        assume hx: "x \<in> ?S - {q\<^sub>1}"
          and hy: "y \<in> ?S - {q\<^sub>1}"
          and hxy: "f x = f y"
        have "g (f x) = g (f y)"
          using hxy by (by100 simp)
        thus "x = y"
          using hgf[OF hx] hgf[OF hy] by (by100 simp)
      qed
      have hy_L: "y \<in> ?L"
        using hy_eq hx_dom hf_img by (by100 blast)
      have hy_ne_a: "y \<noteq> a"
      proof
        assume hya: "y = a"
        have "f x = f q\<^sub>2"
          using hya hy_eq unfolding a_def by (by100 simp)
        hence "x = q\<^sub>2"
          using hinj hx_dom hq\<^sub>2_dom unfolding inj_on_def by (by100 blast)
        thus False using hx_not_q\<^sub>2 by (by100 blast)
      qed
      have hy_ne_b: "y \<noteq> b"
      proof
        assume hyb: "y = b"
        have "f x = f q\<^sub>3"
          using hyb hy_eq unfolding b_def by (by100 simp)
        hence "x = q\<^sub>3"
          using hinj hx_dom hq\<^sub>3_dom unfolding inj_on_def by (by100 blast)
        thus False using hx_not_q\<^sub>3 by (by100 blast)
      qed
      show "y \<in> ?L - {a, b}"
        using hy_L hy_ne_a hy_ne_b by (by100 blast)
    qed
    have hK_image_component:
      "\<exists>Lc \<in> components (?L - {a, b}). f ` K \<subseteq> Lc"
    proof -
      have hK_ne: "K \<noteq> {}"
        using hK in_components_nonempty by (by100 blast)
      obtain y where hyK: "y \<in> K"
        using hK_ne by (by100 blast)
      have hfy_img: "f y \<in> f ` K"
        using hyK by (by100 blast)
      have hfy_cut: "f y \<in> ?L - {a, b}"
        using hfy_img hK_image_line by (by100 blast)
      define Lc where "Lc = connected_component_set (?L - {a, b}) (f y)"
      have hLc_comp: "Lc \<in> components (?L - {a, b})"
        unfolding Lc_def by (rule componentsI[OF hfy_cut])
      have hK_conn: "connected K"
        using hK in_components_connected by (by100 blast)
      have hf_cont_dom: "continuous_on (?S - {q\<^sub>1}) f"
        using hfg unfolding homeomorphism_def by (by100 blast)
      have hf_cont_K: "continuous_on K f"
        by (rule continuous_on_subset[OF hf_cont_dom hK_sub_punctured])
      have h_img_conn: "connected (f ` K)"
        by (rule connected_continuous_image[OF hf_cont_K hK_conn])
      have h_img_sub_Lc: "f ` K \<subseteq> Lc"
        unfolding Lc_def
        by (rule connected_component_maximal
            [OF hfy_img h_img_conn hK_image_line])
      show ?thesis using hLc_comp h_img_sub_Lc by (by100 blast)
    qed
    have h_line_three_sectors:
      "\<exists>q\<in>{q\<^sub>1, q\<^sub>2, q\<^sub>3}. q \<notin> closure K"
    proof -
      obtain Lc where hLc_comp: "Lc \<in> components (?L - {a, b})"
        and hK_img_sub_Lc: "f ` K \<subseteq> Lc"
        using hK_image_component by (by100 blast)
      have hK_sub_gLc: "K \<subseteq> g ` Lc"
      proof
        fix x assume hx: "x \<in> K"
        have hx_dom: "x \<in> ?S - {q\<^sub>1}"
          using hx hK_sub_punctured by (by100 blast)
        have hfx_Lc: "f x \<in> Lc"
          using hx hK_img_sub_Lc by (by100 blast)
        have "g (f x) = x"
          using hfg hx_dom unfolding homeomorphism_def by (by100 blast)
        moreover have "g (f x) \<in> g ` Lc"
          using hfx_Lc by (rule imageI)
        ultimately show "x \<in> g ` Lc"
          by (by100 simp)
      qed
      have hq\<^sub>2_dom: "q\<^sub>2 \<in> ?S - {q\<^sub>1}"
        using hq\<^sub>2_sphere hq\<^sub>12 by (by100 blast)
      have hq\<^sub>3_dom: "q\<^sub>3 \<in> ?S - {q\<^sub>1}"
        using hq\<^sub>3_sphere hq\<^sub>13 by (by100 blast)
      have hq\<^sub>2_miss_if_a_miss:
        "a \<notin> closure Lc \<Longrightarrow> q\<^sub>2 \<notin> closure K"
      proof
        assume ha_miss: "a \<notin> closure Lc"
        assume hq\<^sub>2_clK: "q\<^sub>2 \<in> closure K"
        have hq\<^sub>2_cl_gLc: "q\<^sub>2 \<in> closure (g ` Lc)"
          using hq\<^sub>2_clK closure_mono[OF hK_sub_gLc] by (by100 blast)
        have hLc_sub_line: "Lc \<subseteq> ?L"
          using hLc_comp in_components_subset by (by100 blast)
        have hg_Lc_dom: "g ` Lc \<subseteq> ?S - {q\<^sub>1}"
        proof -
          have hg_img: "g ` ?L = ?S - {q\<^sub>1}"
            using hfg unfolding homeomorphism_def by (by100 blast)
          show ?thesis
            using image_mono[OF hLc_sub_line, of g] hg_img by (by100 blast)
        qed
        have hfg_Lc: "f ` (g ` Lc) = Lc"
        proof
          show "f ` (g ` Lc) \<subseteq> Lc"
          proof
            fix y assume hy: "y \<in> f ` (g ` Lc)"
            obtain x where hx: "x \<in> Lc" and hy_eq: "y = f (g x)"
              using hy by (by100 blast)
            have hx_line: "x \<in> ?L"
              using hx hLc_sub_line by (by100 blast)
            have "f (g x) = x"
              using hfg hx_line unfolding homeomorphism_def by (by100 blast)
            thus "y \<in> Lc"
              using hx hy_eq by (by100 simp)
          qed
          show "Lc \<subseteq> f ` (g ` Lc)"
          proof
            fix x assume hx: "x \<in> Lc"
            have hx_line: "x \<in> ?L"
              using hx hLc_sub_line by (by100 blast)
            have hfgx: "f (g x) = x"
              using hfg hx_line unfolding homeomorphism_def by (by100 blast)
            have "g x \<in> g ` Lc"
              using hx by (rule imageI)
            hence "f (g x) \<in> f ` (g ` Lc)"
              by (rule imageI)
            thus "x \<in> f ` (g ` Lc)"
            using hfgx by (by100 simp)
          qed
        qed
        have "a \<in> closure Lc"
        proof -
          obtain s where hs_in: "\<And>n. s n \<in> g ` Lc"
            and hs_lim: "(s \<longlongrightarrow> q\<^sub>2) sequentially"
            using hq\<^sub>2_cl_gLc unfolding closure_sequential by (by100 blast)
          have hs_dom: "\<And>n. s n \<in> ?S - {q\<^sub>1}"
            using hs_in hg_Lc_dom by (by100 blast)
          have hf_cont_dom: "continuous_on (?S - {q\<^sub>1}) f"
            using hfg unfolding homeomorphism_def by (by100 blast)
          have hfs_lim: "((f \<circ> s) \<longlongrightarrow> f q\<^sub>2) sequentially"
            using hf_cont_dom unfolding continuous_on_sequentially
            using hq\<^sub>2_dom hs_dom hs_lim by (by100 blast)
          have hfs_in: "\<And>n. (f \<circ> s) n \<in> Lc"
          proof -
            fix n
            have "f (s n) \<in> f ` (g ` Lc)"
              using hs_in[of n] by (rule imageI)
            thus "(f \<circ> s) n \<in> Lc"
              using hfg_Lc by (by100 simp)
          qed
          have "f q\<^sub>2 \<in> closure Lc"
            unfolding closure_sequential
            using hfs_in hfs_lim by (by100 blast)
          thus ?thesis
            unfolding a_def .
        qed
        thus False
          using ha_miss by (by100 blast)
      qed
      have hq\<^sub>3_miss_if_b_miss:
        "b \<notin> closure Lc \<Longrightarrow> q\<^sub>3 \<notin> closure K"
      proof
        assume hb_miss: "b \<notin> closure Lc"
        assume hq\<^sub>3_clK: "q\<^sub>3 \<in> closure K"
        have hq\<^sub>3_cl_gLc: "q\<^sub>3 \<in> closure (g ` Lc)"
          using hq\<^sub>3_clK closure_mono[OF hK_sub_gLc] by (by100 blast)
        have hLc_sub_line: "Lc \<subseteq> ?L"
          using hLc_comp in_components_subset by (by100 blast)
        have hg_Lc_dom: "g ` Lc \<subseteq> ?S - {q\<^sub>1}"
        proof -
          have hg_img: "g ` ?L = ?S - {q\<^sub>1}"
            using hfg unfolding homeomorphism_def by (by100 blast)
          show ?thesis
            using image_mono[OF hLc_sub_line, of g] hg_img by (by100 blast)
        qed
        have hfg_Lc: "f ` (g ` Lc) = Lc"
        proof
          show "f ` (g ` Lc) \<subseteq> Lc"
          proof
            fix y assume hy: "y \<in> f ` (g ` Lc)"
            obtain x where hx: "x \<in> Lc" and hy_eq: "y = f (g x)"
              using hy by (by100 blast)
            have hx_line: "x \<in> ?L"
              using hx hLc_sub_line by (by100 blast)
            have "f (g x) = x"
              using hfg hx_line unfolding homeomorphism_def by (by100 blast)
            thus "y \<in> Lc"
              using hx hy_eq by (by100 simp)
          qed
          show "Lc \<subseteq> f ` (g ` Lc)"
          proof
            fix x assume hx: "x \<in> Lc"
            have hx_line: "x \<in> ?L"
              using hx hLc_sub_line by (by100 blast)
            have hfgx: "f (g x) = x"
              using hfg hx_line unfolding homeomorphism_def by (by100 blast)
            have "g x \<in> g ` Lc"
              using hx by (rule imageI)
            hence "f (g x) \<in> f ` (g ` Lc)"
              by (rule imageI)
            thus "x \<in> f ` (g ` Lc)"
            using hfgx by (by100 simp)
          qed
        qed
        have "b \<in> closure Lc"
        proof -
          obtain s where hs_in: "\<And>n. s n \<in> g ` Lc"
            and hs_lim: "(s \<longlongrightarrow> q\<^sub>3) sequentially"
            using hq\<^sub>3_cl_gLc unfolding closure_sequential by (by100 blast)
          have hs_dom: "\<And>n. s n \<in> ?S - {q\<^sub>1}"
            using hs_in hg_Lc_dom by (by100 blast)
          have hf_cont_dom: "continuous_on (?S - {q\<^sub>1}) f"
            using hfg unfolding homeomorphism_def by (by100 blast)
          have hfs_lim: "((f \<circ> s) \<longlongrightarrow> f q\<^sub>3) sequentially"
            using hf_cont_dom unfolding continuous_on_sequentially
            using hq\<^sub>3_dom hs_dom hs_lim by (by100 blast)
          have hfs_in: "\<And>n. (f \<circ> s) n \<in> Lc"
          proof -
            fix n
            have "f (s n) \<in> f ` (g ` Lc)"
              using hs_in[of n] by (rule imageI)
            thus "(f \<circ> s) n \<in> Lc"
              using hfg_Lc by (by100 simp)
          qed
          have "f q\<^sub>3 \<in> closure Lc"
            unfolding closure_sequential
            using hfs_in hfs_lim by (by100 blast)
          thus ?thesis
            unfolding b_def .
        qed
        thus False
          using hb_miss by (by100 blast)
      qed
      have hq\<^sub>1_miss_if_bounded:
        "bounded Lc \<Longrightarrow> q\<^sub>1 \<notin> closure K"
      proof
        assume hLc_bounded: "bounded Lc"
        assume hq\<^sub>1_clK: "q\<^sub>1 \<in> closure K"
        have hq\<^sub>1_cl_gLc: "q\<^sub>1 \<in> closure (g ` Lc)"
          using hq\<^sub>1_clK closure_mono[OF hK_sub_gLc] by (by100 blast)
        have hLc_sub_line: "Lc \<subseteq> ?L"
          using hLc_comp in_components_subset by (by100 blast)
        have hclLc_sub_line: "closure Lc \<subseteq> ?L"
          by (rule closure_minimal[OF hLc_sub_line closed_hyperplane])
        have hclLc_compact: "compact (closure Lc)"
          using hLc_bounded by (by100 simp)
        have hg_cont_clLc: "continuous_on (closure Lc) g"
        proof -
          have hg_cont_line: "continuous_on ?L g"
            using hfg unfolding homeomorphism_def by (by100 blast)
          show ?thesis
            by (rule continuous_on_subset[OF hg_cont_line hclLc_sub_line])
        qed
        have hcl_gLc_sub_g_clLc: "closure (g ` Lc) \<subseteq> g ` closure Lc"
        proof (rule closure_minimal)
          show "g ` Lc \<subseteq> g ` closure Lc"
            by (rule image_mono[OF closure_subset])
          have "compact (g ` closure Lc)"
            by (rule compact_continuous_image[OF hg_cont_clLc hclLc_compact])
          thus "closed (g ` closure Lc)"
            by (rule compact_imp_closed)
        qed
        have hq\<^sub>1_in_g_clLc: "q\<^sub>1 \<in> g ` closure Lc"
          using hq\<^sub>1_cl_gLc hcl_gLc_sub_g_clLc by (by100 blast)
        have "q\<^sub>1 \<notin> g ` closure Lc"
        proof -
          have hg_img: "g ` ?L = ?S - {q\<^sub>1}"
            using hfg unfolding homeomorphism_def by (by100 blast)
          have "g ` closure Lc \<subseteq> ?S - {q\<^sub>1}"
            using image_mono[OF hclLc_sub_line, of g] hg_img by (by100 blast)
          thus ?thesis
            by (by100 blast)
        qed
        thus False
          using hq\<^sub>1_in_g_clLc by (by100 blast)
      qed
      have hLc_sector_case:
        "a \<notin> closure Lc \<or> b \<notin> closure Lc \<or> bounded Lc"
      proof -
        have hLc_conn: "connected Lc"
          using hLc_comp in_components_connected by (by100 blast)
        have hLc_sub_line: "Lc \<subseteq> ?L - {a, b}"
          using hLc_comp in_components_subset by (by100 blast)
        have ha_line: "a \<in> ?L"
        proof -
          have hf_img: "f ` (?S - {q\<^sub>1}) = ?L"
            using hfg unfolding homeomorphism_def by (by100 blast)
          show ?thesis
            unfolding a_def using hq\<^sub>2_dom hf_img by (by100 blast)
        qed
        have hb_line: "b \<in> ?L"
        proof -
          have hf_img: "f ` (?S - {q\<^sub>1}) = ?L"
            using hfg unfolding homeomorphism_def by (by100 blast)
          show ?thesis
            unfolding b_def using hq\<^sub>3_dom hf_img by (by100 blast)
        qed
        have hab_ne: "a \<noteq> b"
        proof
          assume hab: "a = b"
          have hgf:
            "\<And>x. x \<in> ?S - {q\<^sub>1} \<Longrightarrow> g (f x) = x"
            using hfg unfolding homeomorphism_def by (by100 blast)
          have "f q\<^sub>2 = f q\<^sub>3"
            using hab unfolding a_def b_def by (by100 simp)
          hence "g (f q\<^sub>2) = g (f q\<^sub>3)"
            by (by100 simp)
          hence "q\<^sub>2 = q\<^sub>3"
            using hgf[OF hq\<^sub>2_dom] hgf[OF hq\<^sub>3_dom] by (by100 simp)
          thus False
            using hq\<^sub>23 by (by100 blast)
        qed
        have h_line_component_trichotomy:
          "a \<notin> closure Lc \<or> b \<notin> closure Lc \<or> bounded Lc"
        proof (cases "a \<in> closure Lc \<and> b \<in> closure Lc")
          case False
          thus ?thesis
            by (by100 blast)
        next
          case True
          have ha_cl_Lc: "a \<in> closure Lc"
            using True by (by100 blast)
          have hb_cl_Lc: "b \<in> closure Lc"
            using True by (by100 blast)
          have hLc_sub_L: "Lc \<subseteq> ?L"
            using hLc_sub_line by (by100 blast)
          have hclLc_sub_L: "closure Lc \<subseteq> ?L"
            by (rule closure_minimal[OF hLc_sub_L closed_hyperplane])
          define d where "d = b - a"
          define D where "D = d \<bullet> d"
          define \<phi> where "\<phi> = (\<lambda>x::real^2. (x - a) \<bullet> d)"
          have hd_ne: "d \<noteq> 0"
            using hab_ne unfolding d_def by (by100 simp)
          have hD_pos: "D > 0"
            unfolding D_def using hd_ne by (by100 simp)
          have hL_eq_aff: "?L = affine hull {a, b}"
          proof -
            have hL_affine: "affine ?L"
              by (rule affine_hyperplane)
            have hL_dim: "aff_dim ?L = 1"
              using hc_nonzero aff_dim_hyperplane[of "q\<^sub>2 - q\<^sub>1" 0]
              by (by100 simp)
            have hab_sub_L: "{a, b} \<subseteq> ?L"
              using ha_line hb_line by (by100 blast)
            have h_aff_sub_L: "affine hull {a, b} \<subseteq> ?L"
              by (rule hull_minimal) (rule hab_sub_L, rule hL_affine)
            have h_aff_ne: "affine hull {a, b} \<noteq> {}"
              using hull_inc[of a "{a, b}"] by (by100 blast)
            have h_aff_dim: "aff_dim (affine hull {a, b}) = 1"
              using hab_ne by (by100 simp)
            have "affine hull {a, b} = ?L"
            proof (rule affine_dim_equal
                [OF affine_affine_hull hL_affine h_aff_ne
                    h_aff_sub_L])
              show "aff_dim (affine hull {a, b}) = aff_dim ?L"
                using h_aff_dim hL_dim by (by100 simp)
            qed
            thus ?thesis by (by100 simp)
          qed
          have h\<phi>_a: "\<phi> a = 0"
            unfolding \<phi>_def by (by100 simp)
          have h\<phi>_b: "\<phi> b = D"
            unfolding \<phi>_def D_def d_def by (by100 simp)
          have h\<phi>_coord:
            "\<And>x. x \<in> ?L \<Longrightarrow> x = a + (\<phi> x / D) *\<^sub>R d"
          proof -
            fix x assume hxL: "x \<in> ?L"
            have hx_aff: "x \<in> affine hull {a, b}"
              using hxL hL_eq_aff by (by100 simp)
            obtain u where hx_u: "x = a + u *\<^sub>R d"
              using hx_aff unfolding affine_hull_2_alt d_def by (by100 blast)
            have h\<phi>x: "\<phi> x = u * D"
              unfolding \<phi>_def D_def using hx_u by (simp add: algebra_simps)
            have "\<phi> x / D = u"
              using hD_pos h\<phi>x by (by100 simp)
            thus "x = a + (\<phi> x / D) *\<^sub>R d"
              using hx_u by (by100 simp)
          qed
          have h\<phi>_cont_L: "continuous_on ?L \<phi>"
            unfolding \<phi>_def by (intro continuous_intros)
          have h\<phi>_cut_avoid:
            "\<phi> ` Lc \<inter> {0, D} = {}"
          proof (rule equals0I)
            fix y assume hy: "y \<in> \<phi> ` Lc \<inter> {0, D}"
            obtain x where hxLc: "x \<in> Lc" and hy_eq: "y = \<phi> x"
              using hy by (by100 blast)
            have hxL: "x \<in> ?L"
              using hxLc hLc_sub_L by (by100 blast)
            have hx_not_a: "x \<noteq> a"
              using hxLc hLc_sub_line by (by100 blast)
            have hx_not_b: "x \<noteq> b"
              using hxLc hLc_sub_line by (by100 blast)
            consider (zero) "y = 0" | (D) "y = D"
              using hy by (by100 blast)
            thus False
            proof cases
              case zero
              have "\<phi> x / D = 0"
                using zero hy_eq hD_pos by (by100 simp)
              hence "x = a"
                using h\<phi>_coord[OF hxL] by (by100 simp)
              thus False
                using hx_not_a by (by100 blast)
            next
              case D
              have "\<phi> x / D = 1"
                using D hy_eq hD_pos by (by100 simp)
              hence "x = b"
                using h\<phi>_coord[OF hxL] unfolding d_def by (by100 simp)
              thus False
                using hx_not_b by (by100 blast)
            qed
          qed
          have h\<phi>_conn: "connected (\<phi> ` Lc)"
          proof -
            have h\<phi>_cont_Lc: "continuous_on Lc \<phi>"
              by (rule continuous_on_subset[OF h\<phi>_cont_L hLc_sub_L])
            show ?thesis
              by (rule connected_continuous_image[OF h\<phi>_cont_Lc hLc_conn])
          qed
          have h\<phi>_cl_subset:
            "\<phi> ` closure Lc \<subseteq> closure (\<phi> ` Lc)"
            by (rule continuous_image_closure_subset
                [OF h\<phi>_cont_L hclLc_sub_L])
          have h0_cl: "0 \<in> closure (\<phi> ` Lc)"
          proof -
            have h\<phi>a_img: "\<phi> a \<in> \<phi> ` closure Lc"
              using ha_cl_Lc by (rule imageI)
            have h\<phi>a_cl: "\<phi> a \<in> closure (\<phi> ` Lc)"
              using h\<phi>_cl_subset h\<phi>a_img by (rule subsetD)
            thus ?thesis
              using h\<phi>_a by (by100 simp)
          qed
          have hD_cl: "D \<in> closure (\<phi> ` Lc)"
          proof -
            have h\<phi>b_img: "\<phi> b \<in> \<phi> ` closure Lc"
              using hb_cl_Lc by (rule imageI)
            have h\<phi>b_cl: "\<phi> b \<in> closure (\<phi> ` Lc)"
              using h\<phi>_cl_subset h\<phi>b_img by (rule subsetD)
            thus ?thesis
              using h\<phi>_b by (by100 simp)
          qed
          have h\<phi>_between:
            "\<phi> ` Lc \<subseteq> {0<..<D}"
          proof
            fix t assume htT: "t \<in> \<phi> ` Lc"
            have ht_ne0: "t \<noteq> 0"
            proof
              assume ht0: "t = 0"
              have "t \<in> \<phi> ` Lc \<inter> {0, D}"
                using htT ht0 by (by100 blast)
              thus False using h\<phi>_cut_avoid by (by100 simp)
            qed
            have ht_neD: "t \<noteq> D"
            proof
              assume htD: "t = D"
              have "t \<in> \<phi> ` Lc \<inter> {0, D}"
                using htT htD by (by100 blast)
              thus False using h\<phi>_cut_avoid by (by100 simp)
            qed
            have ht_pos: "0 < t"
            proof (rule ccontr)
              assume "\<not> 0 < t"
              hence ht_le0: "t \<le> 0" by (by100 simp)
              obtain y where hyT: "y \<in> \<phi> ` Lc"
                and hy_dist: "dist D y < D / 2"
                using closure_approachableD[OF hD_cl, of "D / 2"] hD_pos
                by (by100 auto)
              have hD_minus_y: "D - y < D / 2"
              proof -
                have h_abs: "\<bar>D - y\<bar> < D / 2"
                  using hy_dist by (simp add: dist_real_def)
                have "D - y \<le> \<bar>D - y\<bar>"
                  by (by100 simp)
                thus ?thesis
                  using h_abs by (by100 linarith)
              qed
              have hy_ge0: "0 \<le> y"
                using hD_minus_y hD_pos by (by100 linarith)
              have h0_in_T: "0 \<in> \<phi> ` Lc"
                by (rule connectedD_interval
                    [OF h\<phi>_conn htT hyT ht_le0 hy_ge0])
              have "0 \<in> \<phi> ` Lc \<inter> {0, D}"
                using h0_in_T by (by100 blast)
              thus False using h\<phi>_cut_avoid by (by100 simp)
            qed
            have ht_ltD: "t < D"
            proof (rule ccontr)
              assume "\<not> t < D"
              hence hD_le_t: "D \<le> t" by (by100 simp)
              obtain y where hyT: "y \<in> \<phi> ` Lc"
                and hy_dist: "dist 0 y < D / 2"
                using closure_approachableD[OF h0_cl, of "D / 2"] hD_pos
                by (by100 auto)
              have hy_lt_half: "y < D / 2"
              proof -
                have h_abs: "\<bar>y\<bar> < D / 2"
                  using hy_dist by (simp add: dist_real_def)
                have "y \<le> \<bar>y\<bar>"
                  by (by100 simp)
                thus ?thesis
                  using h_abs by (by100 linarith)
              qed
              have hy_leD: "y \<le> D"
                using hy_lt_half hD_pos by (by100 linarith)
              have hD_in_T: "D \<in> \<phi> ` Lc"
                by (rule connectedD_interval
                    [OF h\<phi>_conn hyT htT hy_leD hD_le_t])
              have "D \<in> \<phi> ` Lc \<inter> {0, D}"
                using hD_in_T by (by100 blast)
              thus False using h\<phi>_cut_avoid by (by100 simp)
            qed
            show "t \<in> {0<..<D}"
              using ht_pos ht_ltD by (by100 simp)
          qed
          have hLc_sub_segment:
            "Lc \<subseteq> closed_segment a b"
          proof
            fix x assume hxLc: "x \<in> Lc"
            have hxL: "x \<in> ?L"
              using hxLc hLc_sub_L by (by100 blast)
            have h\<phi>x_between: "\<phi> x \<in> {0<..<D}"
              using hxLc h\<phi>_between by (by100 blast)
            define u where "u = \<phi> x / D"
            have hu0: "0 \<le> u"
              unfolding u_def using h\<phi>x_between hD_pos by (by100 simp)
            have hu1: "u \<le> 1"
              unfolding u_def using h\<phi>x_between hD_pos by (by100 simp)
            have hx_u: "x = a + u *\<^sub>R d"
              using h\<phi>_coord[OF hxL] unfolding u_def .
            have hx_conv: "x = (1 - u) *\<^sub>R a + u *\<^sub>R b"
              using hx_u unfolding d_def by (simp add: algebra_simps)
            show "x \<in> closed_segment a b"
              unfolding closed_segment_def
              using hu0 hu1 hx_conv by (by100 blast)
          qed
          have "bounded Lc"
            by (rule bounded_subset[OF bounded_closed_segment hLc_sub_segment])
          thus ?thesis
            by (by100 blast)
        qed
        show ?thesis by (rule h_line_component_trichotomy)
      qed
      show ?thesis
      proof -
        consider (miss_a) "a \<notin> closure Lc"
          | (miss_b) "b \<notin> closure Lc"
          | (bounded) "bounded Lc"
          using hLc_sector_case by (by100 blast)
        thus ?thesis
        proof cases
          case miss_a
          have "q\<^sub>2 \<notin> closure K"
            by (rule hq\<^sub>2_miss_if_a_miss[OF miss_a])
          thus ?thesis
            by (by100 blast)
        next
          case miss_b
          have "q\<^sub>3 \<notin> closure K"
            by (rule hq\<^sub>3_miss_if_b_miss[OF miss_b])
          thus ?thesis
            by (by100 blast)
        next
          case bounded
          have "q\<^sub>1 \<notin> closure K"
            by (rule hq\<^sub>1_miss_if_bounded[OF bounded])
          thus ?thesis
            by (by100 blast)
        qed
      qed
    qed
    show ?thesis by (rule h_line_three_sectors)
  qed
  show ?thesis
  proof -
    obtain q where hq_set: "q \<in> {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
      and hq_not_clK: "q \<notin> closure K"
      using hmiss by (by100 blast)
    have h_psub:
      "{q\<^sub>1, q\<^sub>2, q\<^sub>3} \<inter> closure K \<subset> {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
    proof -
      have h_sub: "{q\<^sub>1, q\<^sub>2, q\<^sub>3} \<inter> closure K \<subseteq> {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
        by (by100 blast)
      have h_ne: "{q\<^sub>1, q\<^sub>2, q\<^sub>3} \<inter> closure K \<noteq> {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
        using hq_set hq_not_clK by (by100 blast)
      show ?thesis
        using h_sub h_ne by (by100 blast)
    qed
    have h_card_lt:
      "card ({q\<^sub>1, q\<^sub>2, q\<^sub>3} \<inter> closure K) < card {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
    proof (rule psubset_card_mono)
      show "finite {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
        by (by100 simp)
      show "{q\<^sub>1, q\<^sub>2, q\<^sub>3} \<inter> closure K \<subset> {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
        by (rule h_psub)
    qed
    have h_qs_card: "card {q\<^sub>1, q\<^sub>2, q\<^sub>3} = 3"
      using hq\<^sub>12 hq\<^sub>13 hq\<^sub>23 by (by100 simp)
    show ?thesis
      using h_card_lt h_qs_card by (by100 simp)
  qed
qed

lemma geotop_radial_projection_image_segment_prefix:
  fixes P p z :: "real^2"
  assumes hz: "z \<in> closed_segment P p - {P}"
  assumes hp: "p \<noteq> P"
  assumes hr: "r > 0"
  assumes hr_le: "r \<le> dist P p"
  shows "P + (r / dist P z) *\<^sub>R (z - P)
      \<in> (closed_segment P p - {P}) \<inter> sphere P r"
proof -
  let ?rho = "P + (r / dist P z) *\<^sub>R (z - P)"
  have hz_seg: "z \<in> closed_segment P p"
    using hz by (by100 blast)
  have hz_ne: "z \<noteq> P"
    using hz by (by100 blast)
  obtain t where ht0: "0 \<le> t" and ht1: "t \<le> 1"
    and hz_t: "z = (1 - t) *\<^sub>R P + t *\<^sub>R p"
    using hz_seg unfolding closed_segment_def by (by100 blast)
  have hp_dist_pos: "dist P p > 0"
    using hp by (by100 simp)
  have ht_pos: "t > 0"
  proof -
    have "t \<noteq> 0"
    proof
      assume ht_eq0: "t = 0"
      have "z = P"
        using hz_t ht_eq0 by (by100 simp)
      thus False
        using hz_ne by (by100 blast)
    qed
    thus ?thesis
      using ht0 by (by100 simp)
  qed
  have hz_vec: "z = P + t *\<^sub>R (p - P)"
    using hz_t by (simp add: algebra_simps)
  have hz_dist: "dist P z = t * dist P p"
    using hz_vec ht0 by (simp add: dist_norm norm_minus_commute)
  have h\<rho>_eq: "?rho = P + (r / dist P p) *\<^sub>R (p - P)"
  proof -
    have "?rho = P + (r / (t * dist P p)) *\<^sub>R (t *\<^sub>R (p - P))"
      using hz_vec hz_dist by (by100 simp)
    also have "\<dots> = P + (r / dist P p) *\<^sub>R (p - P)"
      using ht_pos hp_dist_pos by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have hs0: "0 \<le> r / dist P p"
    using hr hp_dist_pos by (by100 simp)
  have hs1: "r / dist P p \<le> 1"
    using hr_le hp_dist_pos by (by100 simp)
  have h\<rho>_conv: "?rho = (1 - r / dist P p) *\<^sub>R P + (r / dist P p) *\<^sub>R p"
    using h\<rho>_eq by (simp add: algebra_simps)
  have h\<rho>_seg: "?rho \<in> closed_segment P p"
    unfolding closed_segment_def using hs0 hs1 h\<rho>_conv by (by100 blast)
  have h\<rho>_ne: "?rho \<noteq> P"
  proof
    assume h_eq: "?rho = P"
    have "(r / dist P p) *\<^sub>R (p - P) = 0"
      using h_eq h\<rho>_eq by (by100 simp)
    hence "r / dist P p = 0"
      using hp by (by100 simp)
    thus False
      using hr hp_dist_pos by (by100 simp)
  qed
  have h\<rho>_sphere: "?rho \<in> sphere P r"
  proof -
    have "dist P ?rho = r"
      unfolding h\<rho>_eq using hr hp_dist_pos
      by (simp add: dist_norm norm_minus_commute)
    thus ?thesis
      by (by100 simp)
  qed
  show ?thesis
    using h\<rho>_seg h\<rho>_ne h\<rho>_sphere by (by100 blast)
qed

lemma geotop_radial_projection_fixed_on_sphere_prefix:
  fixes P q :: "real^2"
  assumes hr: "r > 0"
  assumes hq: "q \<in> sphere P r"
  shows "P + (r / dist P q) *\<^sub>R (q - P) = q"
proof -
  have hdist: "dist P q = r"
    using hq by (by100 simp)
  show ?thesis
    using hdist hr by (by100 simp)
qed

lemma geotop_radial_projection_closure_noncenter_prefix:
  fixes P z :: "real^2"
  assumes hz: "z \<in> closure C"
  assumes hz_ne: "z \<noteq> P"
  shows "P + (r / dist P z) *\<^sub>R (z - P)
      \<in> closure ((\<lambda>x. P + (r / dist P x) *\<^sub>R (x - P)) ` C)"
proof -
  let ?rho = "\<lambda>x. P + (r / dist P x) *\<^sub>R (x - P)"
  have h\<rho>_cont_at_z: "continuous (at z) ?rho"
    apply (intro continuous_intros)
    using hz_ne
    by (by100 auto)
  show ?thesis
    unfolding closure_approachable
  proof (intro allI impI)
    fix e :: real
    assume he_pos: "e > 0"
    obtain d where hd_pos: "d > 0"
      and hd: "\<And>x. dist x z < d \<Longrightarrow> dist (?rho x) (?rho z) < e"
      using h\<rho>_cont_at_z unfolding continuous_at_eps_delta
      using he_pos by (by100 blast)
    obtain x where hxC: "x \<in> C" and hx_dist: "dist x z < d"
      using hz hd_pos unfolding closure_approachable by (by100 blast)
    have h\<rho>x: "?rho x \<in> ?rho ` C"
      using hxC by (by100 blast)
    have hdist: "dist (?rho x) (?rho z) < e"
      using hd[OF hx_dist] .
    show "\<exists>y\<in>?rho ` C. dist y (?rho z) < e"
      using h\<rho>x hdist by (by100 blast)
  qed
qed

lemma geotop_radial_projection_closure_sphere_point_prefix:
  fixes P q :: "real^2"
  assumes hr: "r > 0"
  assumes hq: "q \<in> sphere P r"
  assumes hq_cl: "q \<in> closure C"
  shows "q \<in> closure ((\<lambda>x. P + (r / dist P x) *\<^sub>R (x - P)) ` C)"
proof -
  let ?rho = "\<lambda>x. P + (r / dist P x) *\<^sub>R (x - P)"
  have hq_dist: "dist P q = r"
    using hq by (by100 simp)
  have hq_ne: "q \<noteq> P"
    using hq_dist hr by (by100 auto)
  have h\<rho>q_cl: "?rho q \<in> closure (?rho ` C)"
    by (rule geotop_radial_projection_closure_noncenter_prefix[OF hq_cl hq_ne])
  have h\<rho>q: "?rho q = q"
    by (rule geotop_radial_projection_fixed_on_sphere_prefix[OF hr hq])
  show ?thesis
    using h\<rho>q_cl h\<rho>q by (by100 simp)
qed

lemma geotop_three_radial_segments_sector_bound_prefix:
  fixes P p\<^sub>1 p\<^sub>2 p\<^sub>3 :: "real^2"
  assumes h\<delta>: "\<delta> > 0"
  assumes hp\<^sub>1: "p\<^sub>1 \<noteq> P"
  assumes hp\<^sub>2: "p\<^sub>2 \<noteq> P"
  assumes hp\<^sub>3: "p\<^sub>3 \<noteq> P"
  assumes h\<delta>p\<^sub>1: "\<delta> \<le> dist P p\<^sub>1"
  assumes h\<delta>p\<^sub>2: "\<delta> \<le> dist P p\<^sub>2"
  assumes h\<delta>p\<^sub>3: "\<delta> \<le> dist P p\<^sub>3"
  assumes h12_empty:
    "(closed_segment P p\<^sub>1 - {P}) \<inter> (closed_segment P p\<^sub>2 - {P}) \<inter> ball P \<delta> = {}"
  assumes h13_empty:
    "(closed_segment P p\<^sub>1 - {P}) \<inter> (closed_segment P p\<^sub>3 - {P}) \<inter> ball P \<delta> = {}"
  assumes h23_empty:
    "(closed_segment P p\<^sub>2 - {P}) \<inter> (closed_segment P p\<^sub>3 - {P}) \<inter> ball P \<delta> = {}"
  shows "\<forall>C \<in> components
      (ball P \<delta> -
        (closed_segment P p\<^sub>1 \<union> closed_segment P p\<^sub>2 \<union> closed_segment P p\<^sub>3)).
      card {S \<in> {closed_segment P p\<^sub>1, closed_segment P p\<^sub>2, closed_segment P p\<^sub>3}.
              (S - {P}) \<inter> ball P \<delta> \<inter> closure C \<noteq> {}} \<le> 2"
proof -
  let ?S1 = "closed_segment P p\<^sub>1"
  let ?S2 = "closed_segment P p\<^sub>2"
  let ?S3 = "closed_segment P p\<^sub>3"
  let ?R = "?S1 \<union> ?S2 \<union> ?S3"
  define r where "r = \<delta> / 2"
  define q\<^sub>1 where "q\<^sub>1 = P + (r / dist P p\<^sub>1) *\<^sub>R (p\<^sub>1 - P)"
  define q\<^sub>2 where "q\<^sub>2 = P + (r / dist P p\<^sub>2) *\<^sub>R (p\<^sub>2 - P)"
  define q\<^sub>3 where "q\<^sub>3 = P + (r / dist P p\<^sub>3) *\<^sub>R (p\<^sub>3 - P)"
  have hr_pos: "r > 0"
    unfolding r_def using h\<delta> by (by100 simp)
  have hr_lt_\<delta>: "r < \<delta>"
    unfolding r_def using h\<delta> by (by100 simp)
  have hp\<^sub>1_dist_pos: "dist P p\<^sub>1 > 0"
    using hp\<^sub>1 by (by100 simp)
  have hp\<^sub>2_dist_pos: "dist P p\<^sub>2 > 0"
    using hp\<^sub>2 by (by100 simp)
  have hp\<^sub>3_dist_pos: "dist P p\<^sub>3 > 0"
    using hp\<^sub>3 by (by100 simp)
  have hq\<^sub>1:
    "q\<^sub>1 \<in> ?S1 - {P} \<and> dist P q\<^sub>1 = r \<and> q\<^sub>1 \<in> ball P \<delta>"
  proof -
    let ?t = "r / dist P p\<^sub>1"
    have ht_nonneg: "0 \<le> ?t"
      using hr_pos hp\<^sub>1_dist_pos by (by100 simp)
    have hr_le_dist: "r \<le> dist P p\<^sub>1"
      unfolding r_def using h\<delta>p\<^sub>1 h\<delta> by (by100 linarith)
    have ht_le1: "?t \<le> 1"
      using hr_le_dist hp\<^sub>1_dist_pos by (by100 simp)
    have hq_conv: "q\<^sub>1 = (1 - ?t) *\<^sub>R P + ?t *\<^sub>R p\<^sub>1"
      unfolding q\<^sub>1_def by (simp add: algebra_simps)
    have hq_seg: "q\<^sub>1 \<in> ?S1"
      unfolding closed_segment_def using ht_nonneg ht_le1 hq_conv by (by100 blast)
    have hq_ne: "q\<^sub>1 \<noteq> P"
    proof
      assume h_eq: "q\<^sub>1 = P"
      have "?t *\<^sub>R (p\<^sub>1 - P) = 0"
        using h_eq unfolding q\<^sub>1_def by (by100 simp)
      hence "?t = 0"
        using hp\<^sub>1 by (by100 simp)
      thus False
        using hr_pos hp\<^sub>1_dist_pos by (by100 simp)
    qed
    have hq_dist: "dist P q\<^sub>1 = r"
      unfolding q\<^sub>1_def
      using hp\<^sub>1_dist_pos hr_pos
      by (simp add: dist_norm norm_minus_commute)
    have hq_ball: "q\<^sub>1 \<in> ball P \<delta>"
      using hq_dist hr_lt_\<delta> by (by100 simp)
    show ?thesis
      using hq_seg hq_ne hq_dist hq_ball by (by100 blast)
  qed
  have hq\<^sub>2:
    "q\<^sub>2 \<in> ?S2 - {P} \<and> dist P q\<^sub>2 = r \<and> q\<^sub>2 \<in> ball P \<delta>"
  proof -
    let ?t = "r / dist P p\<^sub>2"
    have ht_nonneg: "0 \<le> ?t"
      using hr_pos hp\<^sub>2_dist_pos by (by100 simp)
    have hr_le_dist: "r \<le> dist P p\<^sub>2"
      unfolding r_def using h\<delta>p\<^sub>2 h\<delta> by (by100 linarith)
    have ht_le1: "?t \<le> 1"
      using hr_le_dist hp\<^sub>2_dist_pos by (by100 simp)
    have hq_conv: "q\<^sub>2 = (1 - ?t) *\<^sub>R P + ?t *\<^sub>R p\<^sub>2"
      unfolding q\<^sub>2_def by (simp add: algebra_simps)
    have hq_seg: "q\<^sub>2 \<in> ?S2"
      unfolding closed_segment_def using ht_nonneg ht_le1 hq_conv by (by100 blast)
    have hq_ne: "q\<^sub>2 \<noteq> P"
    proof
      assume h_eq: "q\<^sub>2 = P"
      have "?t *\<^sub>R (p\<^sub>2 - P) = 0"
        using h_eq unfolding q\<^sub>2_def by (by100 simp)
      hence "?t = 0"
        using hp\<^sub>2 by (by100 simp)
      thus False
        using hr_pos hp\<^sub>2_dist_pos by (by100 simp)
    qed
    have hq_dist: "dist P q\<^sub>2 = r"
      unfolding q\<^sub>2_def
      using hp\<^sub>2_dist_pos hr_pos
      by (simp add: dist_norm norm_minus_commute)
    have hq_ball: "q\<^sub>2 \<in> ball P \<delta>"
      using hq_dist hr_lt_\<delta> by (by100 simp)
    show ?thesis
      using hq_seg hq_ne hq_dist hq_ball by (by100 blast)
  qed
  have hq\<^sub>3:
    "q\<^sub>3 \<in> ?S3 - {P} \<and> dist P q\<^sub>3 = r \<and> q\<^sub>3 \<in> ball P \<delta>"
  proof -
    let ?t = "r / dist P p\<^sub>3"
    have ht_nonneg: "0 \<le> ?t"
      using hr_pos hp\<^sub>3_dist_pos by (by100 simp)
    have hr_le_dist: "r \<le> dist P p\<^sub>3"
      unfolding r_def using h\<delta>p\<^sub>3 h\<delta> by (by100 linarith)
    have ht_le1: "?t \<le> 1"
      using hr_le_dist hp\<^sub>3_dist_pos by (by100 simp)
    have hq_conv: "q\<^sub>3 = (1 - ?t) *\<^sub>R P + ?t *\<^sub>R p\<^sub>3"
      unfolding q\<^sub>3_def by (simp add: algebra_simps)
    have hq_seg: "q\<^sub>3 \<in> ?S3"
      unfolding closed_segment_def using ht_nonneg ht_le1 hq_conv by (by100 blast)
    have hq_ne: "q\<^sub>3 \<noteq> P"
    proof
      assume h_eq: "q\<^sub>3 = P"
      have "?t *\<^sub>R (p\<^sub>3 - P) = 0"
        using h_eq unfolding q\<^sub>3_def by (by100 simp)
      hence "?t = 0"
        using hp\<^sub>3 by (by100 simp)
      thus False
        using hr_pos hp\<^sub>3_dist_pos by (by100 simp)
    qed
    have hq_dist: "dist P q\<^sub>3 = r"
      unfolding q\<^sub>3_def
      using hp\<^sub>3_dist_pos hr_pos
      by (simp add: dist_norm norm_minus_commute)
    have hq_ball: "q\<^sub>3 \<in> ball P \<delta>"
      using hq_dist hr_lt_\<delta> by (by100 simp)
    show ?thesis
      using hq_seg hq_ne hq_dist hq_ball by (by100 blast)
  qed
  have hq\<^sub>1_set: "q\<^sub>1 \<in> ?S1 - {P}"
    using hq\<^sub>1 by (by100 blast)
  have hq\<^sub>2_set: "q\<^sub>2 \<in> ?S2 - {P}"
    using hq\<^sub>2 by (by100 blast)
  have hq\<^sub>3_set: "q\<^sub>3 \<in> ?S3 - {P}"
    using hq\<^sub>3 by (by100 blast)
  have hq\<^sub>1_ball: "q\<^sub>1 \<in> ball P \<delta>"
    using hq\<^sub>1 by (by100 blast)
  have hq\<^sub>2_ball: "q\<^sub>2 \<in> ball P \<delta>"
    using hq\<^sub>2 by (by100 blast)
  have hq\<^sub>3_ball: "q\<^sub>3 \<in> ball P \<delta>"
    using hq\<^sub>3 by (by100 blast)
  have hq\<^sub>12: "q\<^sub>1 \<noteq> q\<^sub>2"
  proof
    assume h_eq: "q\<^sub>1 = q\<^sub>2"
    have "q\<^sub>1 \<in> (?S1 - {P}) \<inter> (?S2 - {P}) \<inter> ball P \<delta>"
      using hq\<^sub>1_set hq\<^sub>2_set hq\<^sub>1_ball h_eq by (by100 blast)
    thus False
      using h12_empty by (by100 blast)
  qed
  have hq\<^sub>13: "q\<^sub>1 \<noteq> q\<^sub>3"
  proof
    assume h_eq: "q\<^sub>1 = q\<^sub>3"
    have "q\<^sub>1 \<in> (?S1 - {P}) \<inter> (?S3 - {P}) \<inter> ball P \<delta>"
      using hq\<^sub>1_set hq\<^sub>3_set hq\<^sub>1_ball h_eq by (by100 blast)
    thus False
      using h13_empty by (by100 blast)
  qed
  have hq\<^sub>23: "q\<^sub>2 \<noteq> q\<^sub>3"
  proof
    assume h_eq: "q\<^sub>2 = q\<^sub>3"
    have "q\<^sub>2 \<in> (?S2 - {P}) \<inter> (?S3 - {P}) \<inter> ball P \<delta>"
      using hq\<^sub>2_set hq\<^sub>3_set hq\<^sub>2_ball h_eq by (by100 blast)
    thus False
      using h23_empty by (by100 blast)
  qed
  have hS1_sphere_r:
    "(?S1 - {P}) \<inter> sphere P r = {q\<^sub>1}"
  proof -
    have hr_le_dist: "r \<le> dist P p\<^sub>1"
      unfolding r_def using h\<delta>p\<^sub>1 h\<delta> by (by100 linarith)
    show ?thesis
      by (rule closed_segment_sphere_unique_from_center
          [OF hp\<^sub>1 hr_pos hr_le_dist q\<^sub>1_def])
  qed
  have hS2_sphere_r:
    "(?S2 - {P}) \<inter> sphere P r = {q\<^sub>2}"
  proof -
    have hr_le_dist: "r \<le> dist P p\<^sub>2"
      unfolding r_def using h\<delta>p\<^sub>2 h\<delta> by (by100 linarith)
    show ?thesis
      by (rule closed_segment_sphere_unique_from_center
          [OF hp\<^sub>2 hr_pos hr_le_dist q\<^sub>2_def])
  qed
  have hS3_sphere_r:
    "(?S3 - {P}) \<inter> sphere P r = {q\<^sub>3}"
  proof -
    have hr_le_dist: "r \<le> dist P p\<^sub>3"
      unfolding r_def using h\<delta>p\<^sub>3 h\<delta> by (by100 linarith)
    show ?thesis
      by (rule closed_segment_sphere_unique_from_center
          [OF hp\<^sub>3 hr_pos hr_le_dist q\<^sub>3_def])
  qed
  have hS1_sphere_full: "?S1 \<inter> sphere P r = {q\<^sub>1}"
  proof
    show "?S1 \<inter> sphere P r \<subseteq> {q\<^sub>1}"
    proof
      fix z
      assume hz: "z \<in> ?S1 \<inter> sphere P r"
      have hzS: "z \<in> ?S1"
        using hz by (by100 blast)
      have hzsp: "z \<in> sphere P r"
        using hz by (by100 blast)
      have hz_ne: "z \<noteq> P"
      proof
        assume h_eq: "z = P"
        have "dist P z = r"
          using hzsp by (by100 simp)
        hence "r = 0"
          using h_eq by (by100 simp)
        thus False
          using hr_pos by (by100 simp)
      qed
      have "z \<in> (?S1 - {P}) \<inter> sphere P r"
        using hzS hzsp hz_ne by (by100 blast)
      thus "z \<in> {q\<^sub>1}"
        using hS1_sphere_r by (by100 simp)
    qed
    show "{q\<^sub>1} \<subseteq> ?S1 \<inter> sphere P r"
      using hS1_sphere_r by (by100 blast)
  qed
  have hS2_sphere_full: "?S2 \<inter> sphere P r = {q\<^sub>2}"
  proof
    show "?S2 \<inter> sphere P r \<subseteq> {q\<^sub>2}"
    proof
      fix z
      assume hz: "z \<in> ?S2 \<inter> sphere P r"
      have hzS: "z \<in> ?S2"
        using hz by (by100 blast)
      have hzsp: "z \<in> sphere P r"
        using hz by (by100 blast)
      have hz_ne: "z \<noteq> P"
      proof
        assume h_eq: "z = P"
        have "dist P z = r"
          using hzsp by (by100 simp)
        hence "r = 0"
          using h_eq by (by100 simp)
        thus False
          using hr_pos by (by100 simp)
      qed
      have "z \<in> (?S2 - {P}) \<inter> sphere P r"
        using hzS hzsp hz_ne by (by100 blast)
      thus "z \<in> {q\<^sub>2}"
        using hS2_sphere_r by (by100 simp)
    qed
    show "{q\<^sub>2} \<subseteq> ?S2 \<inter> sphere P r"
      using hS2_sphere_r by (by100 blast)
  qed
  have hS3_sphere_full: "?S3 \<inter> sphere P r = {q\<^sub>3}"
  proof
    show "?S3 \<inter> sphere P r \<subseteq> {q\<^sub>3}"
    proof
      fix z
      assume hz: "z \<in> ?S3 \<inter> sphere P r"
      have hzS: "z \<in> ?S3"
        using hz by (by100 blast)
      have hzsp: "z \<in> sphere P r"
        using hz by (by100 blast)
      have hz_ne: "z \<noteq> P"
      proof
        assume h_eq: "z = P"
        have "dist P z = r"
          using hzsp by (by100 simp)
        hence "r = 0"
          using h_eq by (by100 simp)
        thus False
          using hr_pos by (by100 simp)
      qed
      have "z \<in> (?S3 - {P}) \<inter> sphere P r"
        using hzS hzsp hz_ne by (by100 blast)
      thus "z \<in> {q\<^sub>3}"
        using hS3_sphere_r by (by100 simp)
    qed
    show "{q\<^sub>3} \<subseteq> ?S3 \<inter> sphere P r"
      using hS3_sphere_r by (by100 blast)
  qed
  have hR_sphere_r: "?R \<inter> sphere P r = {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
    using hS1_sphere_full hS2_sphere_full hS3_sphere_full by (by100 blast)
  show ?thesis
  proof
    fix C
    assume hC_comp: "C \<in> components (ball P \<delta> - ?R)"
    let ?Touch = "{S \<in> {?S1, ?S2, ?S3}.
        (S - {P}) \<inter> ball P \<delta> \<inter> closure C \<noteq> {}}"
    have hR_closed: "closed ?R"
      by (intro closed_Un closed_segment)
    have hlocal_open: "open (ball P \<delta> - ?R)"
      by (rule open_Diff[OF open_ball hR_closed])
    have hC_conn: "connected C"
      using hC_comp in_components_connected by (by100 blast)
    have hC_sub_local: "C \<subseteq> ball P \<delta> - ?R"
      using hC_comp in_components_subset by (by100 blast)
    have hC_sub_ball: "C \<subseteq> ball P \<delta>"
      using hC_sub_local by (by100 blast)
    have hC_disj_R: "C \<inter> ?R = {}"
      using hC_sub_local by (by100 blast)
    have hC_path: "path_connected C"
      by (rule component_of_open_path_connected[OF hlocal_open hC_comp])
    have hP_R: "P \<in> ?R"
      by (by100 simp)
    have hP_not_C: "P \<notin> C"
      using hC_disj_R hP_R by (by100 blast)
    define \<rho> where "\<rho> = (\<lambda>x. P + (r / dist P x) *\<^sub>R (x - P))"
    have h\<rho>_cont: "continuous_on C \<rho>"
      unfolding \<rho>_def
      apply (intro continuous_intros)
      using hP_not_C
      by (by100 auto)
    have h\<rho>_sphere: "\<rho> ` C \<subseteq> sphere P r"
    proof
      fix y
      assume hy: "y \<in> \<rho> ` C"
      obtain x where hxC: "x \<in> C" and hy_eq: "y = \<rho> x"
        using hy by (by100 blast)
      have hx_ne_P: "x \<noteq> P"
        using hxC hP_not_C by (by100 blast)
      have hx_dist_pos: "dist P x > 0"
        using hx_ne_P by (by100 simp)
      have "dist P (\<rho> x) = r"
        unfolding \<rho>_def using hx_dist_pos hr_pos
        by (simp add: dist_norm norm_minus_commute)
      thus "y \<in> sphere P r"
        using hy_eq by (by100 simp)
    qed
    have h\<rho>_conn: "connected (\<rho> ` C)"
      by (rule connected_continuous_image[OF h\<rho>_cont hC_conn])
    have h_radial_preimage_segment:
      "\<And>x p. \<lbrakk>x \<in> ball P \<delta>; x \<noteq> P; p \<noteq> P; \<delta> \<le> dist P p;
                 \<rho> x \<in> closed_segment P p\<rbrakk>
        \<Longrightarrow> x \<in> closed_segment P p"
    proof -
      fix x p :: "real^2"
      assume hx_ball: "x \<in> ball P \<delta>"
        and hx_ne: "x \<noteq> P"
        and hp_ne: "p \<noteq> P"
        and h\<delta>_p: "\<delta> \<le> dist P p"
        and h\<rho>_seg: "\<rho> x \<in> closed_segment P p"
      have h\<rho>x_def: "\<rho> x = P + (r / dist P x) *\<^sub>R (x - P)"
        unfolding \<rho>_def by (by100 simp)
      have hxx: "\<rho> x \<in> closed_segment x (\<rho> x)"
        by (by100 simp)
      show "x \<in> closed_segment P p"
        by (rule closed_segment_radial_projection_preimage
            [OF hx_ball hx_ne hp_ne h\<delta>_p hr_pos h\<rho>x_def hxx h\<rho>_seg])
    qed
    have h\<rho>_avoid_R: "\<rho> ` C \<inter> ?R = {}"
    proof (rule equals0I)
      fix y
      assume hy: "y \<in> \<rho> ` C \<inter> ?R"
      obtain x where hxC: "x \<in> C" and hy_eq: "y = \<rho> x"
        using hy by (by100 blast)
      have hx_ball: "x \<in> ball P \<delta>"
        using hxC hC_sub_ball by (by100 blast)
      have hx_ne: "x \<noteq> P"
        using hxC hP_not_C by (by100 blast)
      have hyR: "y \<in> ?R"
        using hy by (by100 blast)
      consider (S1) "y \<in> ?S1" | (S2) "y \<in> ?S2" | (S3) "y \<in> ?S3"
        using hyR by (by100 blast)
      hence "x \<in> ?R"
      proof cases
        case S1
        have h\<rho>x_S1: "\<rho> x \<in> ?S1"
          using hy_eq S1 by (by100 simp)
        have "x \<in> ?S1"
          by (rule h_radial_preimage_segment
              [OF hx_ball hx_ne hp\<^sub>1 h\<delta>p\<^sub>1 h\<rho>x_S1])
        thus ?thesis by (by100 blast)
      next
        case S2
        have h\<rho>x_S2: "\<rho> x \<in> ?S2"
          using hy_eq S2 by (by100 simp)
        have "x \<in> ?S2"
          by (rule h_radial_preimage_segment
              [OF hx_ball hx_ne hp\<^sub>2 h\<delta>p\<^sub>2 h\<rho>x_S2])
        thus ?thesis by (by100 blast)
      next
        case S3
        have h\<rho>x_S3: "\<rho> x \<in> ?S3"
          using hy_eq S3 by (by100 simp)
        have "x \<in> ?S3"
          by (rule h_radial_preimage_segment
              [OF hx_ball hx_ne hp\<^sub>3 h\<delta>p\<^sub>3 h\<rho>x_S3])
        thus ?thesis by (by100 blast)
      qed
      have "x \<in> C \<inter> ?R"
        using hxC \<open>x \<in> ?R\<close> by (by100 blast)
      thus False
        using hC_disj_R by (by100 blast)
    qed
    have h\<rho>_avoid_qs: "\<rho> ` C \<inter> {q\<^sub>1, q\<^sub>2, q\<^sub>3} = {}"
    proof -
      have hq_sub_R: "{q\<^sub>1, q\<^sub>2, q\<^sub>3} \<subseteq> ?R"
        using hq\<^sub>1_set hq\<^sub>2_set hq\<^sub>3_set by (by100 blast)
      show ?thesis
        using h\<rho>_avoid_R hq_sub_R by (by100 blast)
    qed
    have h_circle_trace_bound:
      "card ({q\<^sub>1, q\<^sub>2, q\<^sub>3} \<inter> closure (\<rho> ` C)) \<le> 2"
    proof -
      have htrace_ne: "\<rho> ` C \<noteq> {}"
        using hC_comp in_components_nonempty by (by100 blast)
      obtain z where hz_trace: "z \<in> \<rho> ` C"
        using htrace_ne by (by100 blast)
      have htrace_punctured:
        "\<rho> ` C \<subseteq> sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
        using h\<rho>_sphere h\<rho>_avoid_qs by (by100 blast)
      have hz_punctured: "z \<in> sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
        using hz_trace htrace_punctured by (by100 blast)
      define K where "K = connected_component_set (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}) z"
      have hK_comp: "K \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"
        unfolding K_def by (rule componentsI[OF hz_punctured])
      have htrace_sub_K: "\<rho> ` C \<subseteq> K"
        unfolding K_def
        by (rule connected_component_maximal
            [OF hz_trace h\<rho>_conn htrace_punctured])
      have hcl_sub: "closure (\<rho> ` C) \<subseteq> closure K"
        by (rule closure_mono[OF htrace_sub_K])
      have hinter_sub:
        "{q\<^sub>1, q\<^sub>2, q\<^sub>3} \<inter> closure (\<rho> ` C)
          \<subseteq> {q\<^sub>1, q\<^sub>2, q\<^sub>3} \<inter> closure K"
        using hcl_sub by (by100 blast)
      have hK_bound:
        "card ({q\<^sub>1, q\<^sub>2, q\<^sub>3} \<inter> closure K) \<le> 2"
      proof -
        have hq\<^sub>1_sphere: "q\<^sub>1 \<in> sphere P r"
          using hq\<^sub>1 by (by100 simp)
        have hq\<^sub>2_sphere: "q\<^sub>2 \<in> sphere P r"
          using hq\<^sub>2 by (by100 simp)
        have hq\<^sub>3_sphere: "q\<^sub>3 \<in> sphere P r"
          using hq\<^sub>3 by (by100 simp)
        show ?thesis
          by (rule geotop_punctured_circle_component_closure_three_points_bound_prefix
              [OF hr_pos hq\<^sub>1_sphere hq\<^sub>2_sphere hq\<^sub>3_sphere
                  hq\<^sub>12 hq\<^sub>13 hq\<^sub>23 hK_comp])
      qed
      have hfin_inter: "finite ({q\<^sub>1, q\<^sub>2, q\<^sub>3} \<inter> closure K)"
        by (by100 simp)
      have hcard_le:
        "card ({q\<^sub>1, q\<^sub>2, q\<^sub>3} \<inter> closure (\<rho> ` C))
          \<le> card ({q\<^sub>1, q\<^sub>2, q\<^sub>3} \<inter> closure K)"
        by (rule card_mono[OF hfin_inter hinter_sub])
      show ?thesis
        using hcard_le hK_bound by (by100 linarith)
    qed
    have h_touch_q\<^sub>1:
      "?S1 \<in> ?Touch \<Longrightarrow> q\<^sub>1 \<in> closure (\<rho> ` C)"
    proof -
      assume hS1_touch: "?S1 \<in> ?Touch"
      have hne: "(?S1 - {P}) \<inter> ball P \<delta> \<inter> closure C \<noteq> {}"
        using hS1_touch by (by100 simp)
      obtain z where hzS: "z \<in> ?S1 - {P}"
        and hz_cl: "z \<in> closure C"
        using hne by (by100 blast)
      have hr_le_p\<^sub>1: "r \<le> dist P p\<^sub>1"
        unfolding r_def using h\<delta>p\<^sub>1 h\<delta> by (by100 linarith)
      have h\<rho>z_sphere:
          "\<rho> z \<in> (?S1 - {P}) \<inter> sphere P r"
        unfolding \<rho>_def
        by (rule geotop_radial_projection_image_segment_prefix
            [OF hzS hp\<^sub>1 hr_pos hr_le_p\<^sub>1])
      have h\<rho>z_q\<^sub>1: "\<rho> z = q\<^sub>1"
        using h\<rho>z_sphere hS1_sphere_r by (by100 blast)
      have hz_ne: "z \<noteq> P"
        using hzS by (by100 blast)
      have "\<rho> z \<in> closure (\<rho> ` C)"
        unfolding \<rho>_def
        by (rule geotop_radial_projection_closure_noncenter_prefix
            [OF hz_cl hz_ne])
      thus ?thesis
        using h\<rho>z_q\<^sub>1 by (by100 simp)
    qed
    have h_touch_q\<^sub>2:
      "?S2 \<in> ?Touch \<Longrightarrow> q\<^sub>2 \<in> closure (\<rho> ` C)"
    proof -
      assume hS2_touch: "?S2 \<in> ?Touch"
      have hne: "(?S2 - {P}) \<inter> ball P \<delta> \<inter> closure C \<noteq> {}"
        using hS2_touch by (by100 simp)
      obtain z where hzS: "z \<in> ?S2 - {P}"
        and hz_cl: "z \<in> closure C"
        using hne by (by100 blast)
      have hr_le_p\<^sub>2: "r \<le> dist P p\<^sub>2"
        unfolding r_def using h\<delta>p\<^sub>2 h\<delta> by (by100 linarith)
      have h\<rho>z_sphere:
          "\<rho> z \<in> (?S2 - {P}) \<inter> sphere P r"
        unfolding \<rho>_def
        by (rule geotop_radial_projection_image_segment_prefix
            [OF hzS hp\<^sub>2 hr_pos hr_le_p\<^sub>2])
      have h\<rho>z_q\<^sub>2: "\<rho> z = q\<^sub>2"
        using h\<rho>z_sphere hS2_sphere_r by (by100 blast)
      have hz_ne: "z \<noteq> P"
        using hzS by (by100 blast)
      have "\<rho> z \<in> closure (\<rho> ` C)"
        unfolding \<rho>_def
        by (rule geotop_radial_projection_closure_noncenter_prefix
            [OF hz_cl hz_ne])
      thus ?thesis
        using h\<rho>z_q\<^sub>2 by (by100 simp)
    qed
    have h_touch_q\<^sub>3:
      "?S3 \<in> ?Touch \<Longrightarrow> q\<^sub>3 \<in> closure (\<rho> ` C)"
    proof -
      assume hS3_touch: "?S3 \<in> ?Touch"
      have hne: "(?S3 - {P}) \<inter> ball P \<delta> \<inter> closure C \<noteq> {}"
        using hS3_touch by (by100 simp)
      obtain z where hzS: "z \<in> ?S3 - {P}"
        and hz_cl: "z \<in> closure C"
        using hne by (by100 blast)
      have hr_le_p\<^sub>3: "r \<le> dist P p\<^sub>3"
        unfolding r_def using h\<delta>p\<^sub>3 h\<delta> by (by100 linarith)
      have h\<rho>z_sphere:
          "\<rho> z \<in> (?S3 - {P}) \<inter> sphere P r"
        unfolding \<rho>_def
        by (rule geotop_radial_projection_image_segment_prefix
            [OF hzS hp\<^sub>3 hr_pos hr_le_p\<^sub>3])
      have h\<rho>z_q\<^sub>3: "\<rho> z = q\<^sub>3"
        using h\<rho>z_sphere hS3_sphere_r by (by100 blast)
      have hz_ne: "z \<noteq> P"
        using hzS by (by100 blast)
      have "\<rho> z \<in> closure (\<rho> ` C)"
        unfolding \<rho>_def
        by (rule geotop_radial_projection_closure_noncenter_prefix
            [OF hz_cl hz_ne])
      thus ?thesis
        using h\<rho>z_q\<^sub>3 by (by100 simp)
    qed
    show "card ?Touch \<le> 2"
    proof (rule ccontr)
      assume hnle: "\<not> card ?Touch \<le> 2"
      have hTouch_sub: "?Touch \<subseteq> {?S1, ?S2, ?S3}"
        by (by100 blast)
      have hTouch_fin: "finite ?Touch"
        by (rule finite_subset[OF hTouch_sub]) (by100 simp)
      have hTouch_card_ge: "card ?Touch \<ge> 3"
        using hnle by (by100 simp)
      have hCarrier_fin: "finite {?S1, ?S2, ?S3}"
        by (by100 simp)
      have hTouch_card_le_S: "card ?Touch \<le> card {?S1, ?S2, ?S3}"
        by (rule card_mono[OF hCarrier_fin hTouch_sub])
      have hS_card_le: "card {?S1, ?S2, ?S3} \<le> 3"
        by (rule card_three_le)
      have hS_card: "card {?S1, ?S2, ?S3} = 3"
        using hTouch_card_ge hTouch_card_le_S hS_card_le by (by100 linarith)
      have hTouch_card_le: "card ?Touch \<le> 3"
        using hTouch_card_le_S hS_card by (by100 simp)
      have hTouch_card: "card ?Touch = card {?S1, ?S2, ?S3}"
        using hTouch_card_ge hTouch_card_le hS_card by (by100 simp)
      have hTouch_eq: "?Touch = {?S1, ?S2, ?S3}"
        by (rule card_subset_eq[OF hCarrier_fin hTouch_sub hTouch_card])
      have hq\<^sub>1_cl: "q\<^sub>1 \<in> closure (\<rho> ` C)"
        using h_touch_q\<^sub>1 hTouch_eq by (by100 simp)
      have hq\<^sub>2_cl: "q\<^sub>2 \<in> closure (\<rho> ` C)"
        using h_touch_q\<^sub>2 hTouch_eq by (by100 simp)
      have hq\<^sub>3_cl: "q\<^sub>3 \<in> closure (\<rho> ` C)"
        using h_touch_q\<^sub>3 hTouch_eq by (by100 simp)
      have hq_sub: "{q\<^sub>1, q\<^sub>2, q\<^sub>3} \<subseteq> closure (\<rho> ` C)"
        using hq\<^sub>1_cl hq\<^sub>2_cl hq\<^sub>3_cl by (by100 blast)
      have hq_inter:
        "{q\<^sub>1, q\<^sub>2, q\<^sub>3} \<inter> closure (\<rho> ` C) = {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
        using hq_sub by (by100 blast)
      have hq_card:
        "card ({q\<^sub>1, q\<^sub>2, q\<^sub>3} \<inter> closure (\<rho> ` C)) = 3"
        using hq_inter hq\<^sub>12 hq\<^sub>13 hq\<^sub>23 by (by100 simp)
      show False
        using h_circle_trace_bound hq_card by (by100 simp)
    qed
  qed
qed

lemma geotop_finite_components_three_radial_segments_ball_prefix:
  fixes P p\<^sub>1 p\<^sub>2 p\<^sub>3 :: "real^2"
  assumes h\<delta>: "\<delta> > 0"
  assumes hp\<^sub>1: "p\<^sub>1 \<noteq> P"
  assumes hp\<^sub>2: "p\<^sub>2 \<noteq> P"
  assumes hp\<^sub>3: "p\<^sub>3 \<noteq> P"
  assumes h\<delta>p\<^sub>1: "\<delta> \<le> dist P p\<^sub>1"
  assumes h\<delta>p\<^sub>2: "\<delta> \<le> dist P p\<^sub>2"
  assumes h\<delta>p\<^sub>3: "\<delta> \<le> dist P p\<^sub>3"
  assumes h12_empty:
    "(closed_segment P p\<^sub>1 - {P}) \<inter> (closed_segment P p\<^sub>2 - {P}) \<inter> ball P \<delta> = {}"
  assumes h13_empty:
    "(closed_segment P p\<^sub>1 - {P}) \<inter> (closed_segment P p\<^sub>3 - {P}) \<inter> ball P \<delta> = {}"
  assumes h23_empty:
    "(closed_segment P p\<^sub>2 - {P}) \<inter> (closed_segment P p\<^sub>3 - {P}) \<inter> ball P \<delta> = {}"
  shows "finite (components
    (ball P \<delta> -
      (closed_segment P p\<^sub>1 \<union> closed_segment P p\<^sub>2 \<union> closed_segment P p\<^sub>3)))"
proof -
  let ?S1 = "closed_segment P p\<^sub>1"
  let ?S2 = "closed_segment P p\<^sub>2"
  let ?S3 = "closed_segment P p\<^sub>3"
  let ?R = "?S1 \<union> ?S2 \<union> ?S3"
  define r where "r = \<delta> / 2"
  define q\<^sub>1 where "q\<^sub>1 = P + (r / dist P p\<^sub>1) *\<^sub>R (p\<^sub>1 - P)"
  define q\<^sub>2 where "q\<^sub>2 = P + (r / dist P p\<^sub>2) *\<^sub>R (p\<^sub>2 - P)"
  define q\<^sub>3 where "q\<^sub>3 = P + (r / dist P p\<^sub>3) *\<^sub>R (p\<^sub>3 - P)"
  define \<rho> where "\<rho> = (\<lambda>x. P + (r / dist P x) *\<^sub>R (x - P))"
  have hr_pos: "r > 0"
    unfolding r_def using h\<delta> by (by100 simp)
  have hr_lt_\<delta>: "r < \<delta>"
    unfolding r_def using h\<delta> by (by100 simp)
  have hr_le_p\<^sub>1: "r \<le> dist P p\<^sub>1"
    unfolding r_def using h\<delta>p\<^sub>1 h\<delta> by (by100 linarith)
  have hr_le_p\<^sub>2: "r \<le> dist P p\<^sub>2"
    unfolding r_def using h\<delta>p\<^sub>2 h\<delta> by (by100 linarith)
  have hr_le_p\<^sub>3: "r \<le> dist P p\<^sub>3"
    unfolding r_def using h\<delta>p\<^sub>3 h\<delta> by (by100 linarith)
  have hp\<^sub>1_self: "p\<^sub>1 \<in> ?S1 - {P}"
    using hp\<^sub>1 by (by100 simp)
  have hp\<^sub>2_self: "p\<^sub>2 \<in> ?S2 - {P}"
    using hp\<^sub>2 by (by100 simp)
  have hp\<^sub>3_self: "p\<^sub>3 \<in> ?S3 - {P}"
    using hp\<^sub>3 by (by100 simp)
  have hq\<^sub>1:
      "q\<^sub>1 \<in> (?S1 - {P}) \<inter> sphere P r"
    unfolding q\<^sub>1_def
    by (rule geotop_radial_projection_image_segment_prefix
        [OF hp\<^sub>1_self hp\<^sub>1 hr_pos hr_le_p\<^sub>1])
  have hq\<^sub>2:
      "q\<^sub>2 \<in> (?S2 - {P}) \<inter> sphere P r"
    unfolding q\<^sub>2_def
    by (rule geotop_radial_projection_image_segment_prefix
        [OF hp\<^sub>2_self hp\<^sub>2 hr_pos hr_le_p\<^sub>2])
  have hq\<^sub>3:
      "q\<^sub>3 \<in> (?S3 - {P}) \<inter> sphere P r"
    unfolding q\<^sub>3_def
    by (rule geotop_radial_projection_image_segment_prefix
        [OF hp\<^sub>3_self hp\<^sub>3 hr_pos hr_le_p\<^sub>3])
  have hq\<^sub>1_set: "q\<^sub>1 \<in> ?S1 - {P}"
    using hq\<^sub>1 by (by100 blast)
  have hq\<^sub>2_set: "q\<^sub>2 \<in> ?S2 - {P}"
    using hq\<^sub>2 by (by100 blast)
  have hq\<^sub>3_set: "q\<^sub>3 \<in> ?S3 - {P}"
    using hq\<^sub>3 by (by100 blast)
  have hq\<^sub>1_sphere: "q\<^sub>1 \<in> sphere P r"
    using hq\<^sub>1 by (by100 blast)
  have hq\<^sub>2_sphere: "q\<^sub>2 \<in> sphere P r"
    using hq\<^sub>2 by (by100 blast)
  have hq\<^sub>3_sphere: "q\<^sub>3 \<in> sphere P r"
    using hq\<^sub>3 by (by100 blast)
  have hq\<^sub>1_ball: "q\<^sub>1 \<in> ball P \<delta>"
    using hq\<^sub>1_sphere hr_lt_\<delta> by (by100 simp)
  have hq\<^sub>2_ball: "q\<^sub>2 \<in> ball P \<delta>"
    using hq\<^sub>2_sphere hr_lt_\<delta> by (by100 simp)
  have hq\<^sub>3_ball: "q\<^sub>3 \<in> ball P \<delta>"
    using hq\<^sub>3_sphere hr_lt_\<delta> by (by100 simp)
  have hq\<^sub>12: "q\<^sub>1 \<noteq> q\<^sub>2"
  proof
    assume h_eq: "q\<^sub>1 = q\<^sub>2"
    have "q\<^sub>1 \<in> (?S1 - {P}) \<inter> (?S2 - {P}) \<inter> ball P \<delta>"
      using hq\<^sub>1_set hq\<^sub>2_set hq\<^sub>1_ball h_eq by (by100 blast)
    thus False
      using h12_empty by (by100 blast)
  qed
  have hq\<^sub>13: "q\<^sub>1 \<noteq> q\<^sub>3"
  proof
    assume h_eq: "q\<^sub>1 = q\<^sub>3"
    have "q\<^sub>1 \<in> (?S1 - {P}) \<inter> (?S3 - {P}) \<inter> ball P \<delta>"
      using hq\<^sub>1_set hq\<^sub>3_set hq\<^sub>1_ball h_eq by (by100 blast)
    thus False
      using h13_empty by (by100 blast)
  qed
  have hq\<^sub>23: "q\<^sub>2 \<noteq> q\<^sub>3"
  proof
    assume h_eq: "q\<^sub>2 = q\<^sub>3"
    have "q\<^sub>2 \<in> (?S2 - {P}) \<inter> (?S3 - {P}) \<inter> ball P \<delta>"
      using hq\<^sub>2_set hq\<^sub>3_set hq\<^sub>2_ball h_eq by (by100 blast)
    thus False
      using h23_empty by (by100 blast)
  qed
  have hcircle_components_finite:
      "finite (components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}))"
    by (rule geotop_finite_components_punctured_circle_three_points_prefix
        [OF hr_pos hq\<^sub>1_sphere hq\<^sub>2_sphere hq\<^sub>3_sphere hq\<^sub>12 hq\<^sub>13 hq\<^sub>23])
  have hR_components_finite:
      "finite (components (ball P \<delta> - ?R))"
  proof -
    have hR_closed: "closed ?R"
      by (intro closed_Un closed_segment)
    have hlocal_open: "open (ball P \<delta> - ?R)"
      by (rule open_Diff[OF open_ball hR_closed])
    have hP_R: "P \<in> ?R"
      by (by100 simp)
    have h_radial_preimage_segment:
      "\<And>x p. \<lbrakk>x \<in> ball P \<delta>; x \<noteq> P; p \<noteq> P; \<delta> \<le> dist P p;
                 \<rho> x \<in> closed_segment P p\<rbrakk>
        \<Longrightarrow> x \<in> closed_segment P p"
    proof -
      fix x p :: "real^2"
      assume hx_ball: "x \<in> ball P \<delta>"
        and hx_ne: "x \<noteq> P"
        and hp_ne: "p \<noteq> P"
        and h\<delta>_p: "\<delta> \<le> dist P p"
        and h\<rho>_seg: "\<rho> x \<in> closed_segment P p"
      have h\<rho>x_def: "\<rho> x = P + (r / dist P x) *\<^sub>R (x - P)"
        unfolding \<rho>_def by (by100 simp)
      have hxx: "\<rho> x \<in> closed_segment x (\<rho> x)"
        by (by100 simp)
      show "x \<in> closed_segment P p"
        by (rule closed_segment_radial_projection_preimage
            [OF hx_ball hx_ne hp_ne h\<delta>_p hr_pos h\<rho>x_def hxx h\<rho>_seg])
    qed
    have h_trace_component:
      "\<forall>C \<in> components (ball P \<delta> - ?R).
          \<exists>K \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}). \<rho> ` C \<subseteq> K"
    proof
      fix C
      assume hC_comp: "C \<in> components (ball P \<delta> - ?R)"
      have hC_conn: "connected C"
        using hC_comp in_components_connected by (by100 blast)
      have hC_sub_local: "C \<subseteq> ball P \<delta> - ?R"
        using hC_comp in_components_subset by (by100 blast)
      have hC_ne: "C \<noteq> {}"
        using hC_comp in_components_nonempty by (by100 blast)
      have hP_not_C: "P \<notin> C"
        using hC_sub_local hP_R by (by100 blast)
      have h\<rho>_cont: "continuous_on C \<rho>"
        unfolding \<rho>_def
        apply (intro continuous_intros)
        using hP_not_C
        by (by100 auto)
      have h\<rho>_conn: "connected (\<rho> ` C)"
        by (rule connected_continuous_image[OF h\<rho>_cont hC_conn])
      have h\<rho>_punctured:
          "\<rho> ` C \<subseteq> sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
      proof
        fix y
        assume hy: "y \<in> \<rho> ` C"
        obtain x where hxC: "x \<in> C" and hy_eq: "y = \<rho> x"
          using hy by (by100 blast)
        have hx_local: "x \<in> ball P \<delta> - ?R"
          using hxC hC_sub_local by (by100 blast)
        have hx_ball: "x \<in> ball P \<delta>"
          using hx_local by (by100 blast)
        have hx_not_R: "x \<notin> ?R"
          using hx_local by (by100 blast)
        have hx_ne_P: "x \<noteq> P"
          using hx_not_R hP_R by (by100 blast)
        have hx_dist_pos: "dist P x > 0"
          using hx_ne_P by (by100 simp)
        have hy_sphere: "y \<in> sphere P r"
        proof -
          have "dist P (\<rho> x) = r"
            unfolding \<rho>_def using hx_dist_pos hr_pos
            by (simp add: dist_norm norm_minus_commute)
          thus ?thesis
            using hy_eq by (by100 simp)
        qed
        have hy_not_qs: "y \<notin> {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
        proof
          assume hy_qs: "y \<in> {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
          have "x \<in> ?R"
          proof (cases "y = q\<^sub>1")
            case True
            have h\<rho>x_S1: "\<rho> x \<in> ?S1"
              using True hy_eq hq\<^sub>1_set by (by100 blast)
            have "x \<in> ?S1"
              by (rule h_radial_preimage_segment
                  [OF hx_ball hx_ne_P hp\<^sub>1 h\<delta>p\<^sub>1 h\<rho>x_S1])
            thus ?thesis by (by100 blast)
          next
            case hnot1: False
            show ?thesis
            proof (cases "y = q\<^sub>2")
              case True
              have h\<rho>x_S2: "\<rho> x \<in> ?S2"
                using True hy_eq hq\<^sub>2_set by (by100 blast)
              have "x \<in> ?S2"
                by (rule h_radial_preimage_segment
                    [OF hx_ball hx_ne_P hp\<^sub>2 h\<delta>p\<^sub>2 h\<rho>x_S2])
              thus ?thesis by (by100 blast)
            next
              case hnot2: False
              have hy_eq3: "y = q\<^sub>3"
                using hy_qs hnot1 hnot2 by (by100 blast)
              have h\<rho>x_S3: "\<rho> x \<in> ?S3"
                using hy_eq3 hy_eq hq\<^sub>3_set by (by100 blast)
              have "x \<in> ?S3"
                by (rule h_radial_preimage_segment
                    [OF hx_ball hx_ne_P hp\<^sub>3 h\<delta>p\<^sub>3 h\<rho>x_S3])
              thus ?thesis by (by100 blast)
            qed
          qed
          thus False using hx_not_R by (by100 blast)
        qed
        show "y \<in> sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
          using hy_sphere hy_not_qs by (by100 blast)
      qed
      obtain z where hzC: "z \<in> C"
        using hC_ne by (by100 blast)
      have h\<rho>z_img: "\<rho> z \<in> \<rho> ` C"
        using hzC by (by100 blast)
      have h\<rho>z_punctured: "\<rho> z \<in> sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
        using h\<rho>z_img h\<rho>_punctured by (by100 blast)
      define K where "K = connected_component_set (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}) (\<rho> z)"
      have hK_comp: "K \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"
        unfolding K_def by (rule componentsI[OF h\<rho>z_punctured])
      have h\<rho>_sub_K: "\<rho> ` C \<subseteq> K"
        unfolding K_def
        by (rule connected_component_maximal
            [OF h\<rho>z_img h\<rho>_conn h\<rho>_punctured])
      show "\<exists>K\<in>components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}). \<rho> ` C \<subseteq> K"
        using hK_comp h\<rho>_sub_K by (by100 blast)
    qed
    have h_radial_components_reduce_to_circle:
      "\<exists>F. finite F \<and>
        (\<forall>C \<in> components (ball P \<delta> - ?R).
            \<exists>K \<in> F. \<rho> ` C \<subseteq> K \<and>
              K \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}))"
    proof (intro exI[where x="components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"] conjI)
      show "finite (components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}))"
        by (rule hcircle_components_finite)
      show "\<forall>C\<in>components (ball P \<delta> - ?R).
          \<exists>K\<in>components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}).
            \<rho> ` C \<subseteq> K \<and> K \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"
      proof
        fix C
        assume hC: "C \<in> components (ball P \<delta> - ?R)"
        obtain K where hK_comp: "K \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"
          and hK_sub: "\<rho> ` C \<subseteq> K"
          using h_trace_component hC by (by100 blast)
        show "\<exists>K\<in>components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}).
            \<rho> ` C \<subseteq> K \<and> K \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"
          by (intro bexI[where x=K] conjI hK_comp hK_sub)
      qed
    qed
    have h_same_circle_component_same_disk_component:
      "\<forall>C \<in> components (ball P \<delta> - ?R).
        \<forall>D \<in> components (ball P \<delta> - ?R).
          (\<exists>K \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}).
            \<rho> ` C \<subseteq> K \<and> \<rho> ` D \<subseteq> K) \<longrightarrow> C = D"
    proof -
      have hS1_sphere_r:
          "(?S1 - {P}) \<inter> sphere P r = {q\<^sub>1}"
        by (rule closed_segment_sphere_unique_from_center
            [OF hp\<^sub>1 hr_pos hr_le_p\<^sub>1 q\<^sub>1_def])
      have hS2_sphere_r:
          "(?S2 - {P}) \<inter> sphere P r = {q\<^sub>2}"
        by (rule closed_segment_sphere_unique_from_center
            [OF hp\<^sub>2 hr_pos hr_le_p\<^sub>2 q\<^sub>2_def])
      have hS3_sphere_r:
          "(?S3 - {P}) \<inter> sphere P r = {q\<^sub>3}"
        by (rule closed_segment_sphere_unique_from_center
            [OF hp\<^sub>3 hr_pos hr_le_p\<^sub>3 q\<^sub>3_def])
      have hS1_sphere_full: "?S1 \<inter> sphere P r = {q\<^sub>1}"
      proof
        show "?S1 \<inter> sphere P r \<subseteq> {q\<^sub>1}"
        proof
          fix z
          assume hz: "z \<in> ?S1 \<inter> sphere P r"
          have hzS: "z \<in> ?S1"
            using hz by (by100 blast)
          have hzsp: "z \<in> sphere P r"
            using hz by (by100 blast)
          have hz_ne: "z \<noteq> P"
          proof
            assume h_eq: "z = P"
            have "dist P z = r"
              using hzsp by (by100 simp)
            hence "r = 0"
              using h_eq by (by100 simp)
            thus False
              using hr_pos by (by100 simp)
          qed
          have "z \<in> (?S1 - {P}) \<inter> sphere P r"
            using hzS hzsp hz_ne by (by100 blast)
          thus "z \<in> {q\<^sub>1}"
            using hS1_sphere_r by (by100 simp)
        qed
        show "{q\<^sub>1} \<subseteq> ?S1 \<inter> sphere P r"
          using hS1_sphere_r by (by100 blast)
      qed
      have hS2_sphere_full: "?S2 \<inter> sphere P r = {q\<^sub>2}"
      proof
        show "?S2 \<inter> sphere P r \<subseteq> {q\<^sub>2}"
        proof
          fix z
          assume hz: "z \<in> ?S2 \<inter> sphere P r"
          have hzS: "z \<in> ?S2"
            using hz by (by100 blast)
          have hzsp: "z \<in> sphere P r"
            using hz by (by100 blast)
          have hz_ne: "z \<noteq> P"
          proof
            assume h_eq: "z = P"
            have "dist P z = r"
              using hzsp by (by100 simp)
            hence "r = 0"
              using h_eq by (by100 simp)
            thus False
              using hr_pos by (by100 simp)
          qed
          have "z \<in> (?S2 - {P}) \<inter> sphere P r"
            using hzS hzsp hz_ne by (by100 blast)
          thus "z \<in> {q\<^sub>2}"
            using hS2_sphere_r by (by100 simp)
        qed
        show "{q\<^sub>2} \<subseteq> ?S2 \<inter> sphere P r"
          using hS2_sphere_r by (by100 blast)
      qed
      have hS3_sphere_full: "?S3 \<inter> sphere P r = {q\<^sub>3}"
      proof
        show "?S3 \<inter> sphere P r \<subseteq> {q\<^sub>3}"
        proof
          fix z
          assume hz: "z \<in> ?S3 \<inter> sphere P r"
          have hzS: "z \<in> ?S3"
            using hz by (by100 blast)
          have hzsp: "z \<in> sphere P r"
            using hz by (by100 blast)
          have hz_ne: "z \<noteq> P"
          proof
            assume h_eq: "z = P"
            have "dist P z = r"
              using hzsp by (by100 simp)
            hence "r = 0"
              using h_eq by (by100 simp)
            thus False
              using hr_pos by (by100 simp)
          qed
          have "z \<in> (?S3 - {P}) \<inter> sphere P r"
            using hzS hzsp hz_ne by (by100 blast)
          thus "z \<in> {q\<^sub>3}"
            using hS3_sphere_r by (by100 simp)
        qed
        show "{q\<^sub>3} \<subseteq> ?S3 \<inter> sphere P r"
          using hS3_sphere_r by (by100 blast)
      qed
      have hR_sphere_r: "?R \<inter> sphere P r = {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
        using hS1_sphere_full hS2_sphere_full hS3_sphere_full by (by100 blast)
      have h_radial_ray_preimage_segment:
        "\<And>x z p. \<lbrakk>x \<in> ball P \<delta> - ?R; z \<in> closed_segment x (\<rho> x);
                   z \<in> closed_segment P p; p \<noteq> P; \<delta> \<le> dist P p\<rbrakk>
          \<Longrightarrow> x \<in> closed_segment P p"
      proof -
        fix x z p :: "real^2"
        assume hx_local: "x \<in> ball P \<delta> - ?R"
          and hz_x: "z \<in> closed_segment x (\<rho> x)"
          and hz_p: "z \<in> closed_segment P p"
          and hp_ne: "p \<noteq> P"
          and h\<delta>_p: "\<delta> \<le> dist P p"
        have hx_ball: "x \<in> ball P \<delta>"
          using hx_local by (by100 blast)
        have hx_not_R: "x \<notin> ?R"
          using hx_local by (by100 blast)
        have hx_ne: "x \<noteq> P"
          using hx_not_R hP_R by (by100 blast)
        have h\<rho>x_def: "\<rho> x = P + (r / dist P x) *\<^sub>R (x - P)"
          unfolding \<rho>_def by (by100 simp)
        show "x \<in> closed_segment P p"
          by (rule closed_segment_radial_projection_preimage
              [OF hx_ball hx_ne hp_ne h\<delta>_p hr_pos h\<rho>x_def hz_x hz_p])
      qed
      have h_radial_segment_subset:
        "\<And>x. x \<in> ball P \<delta> - ?R \<Longrightarrow> closed_segment x (\<rho> x) \<subseteq> ball P \<delta> - ?R"
      proof
        fix x z
        assume hx_local: "x \<in> ball P \<delta> - ?R"
          and hz_seg: "z \<in> closed_segment x (\<rho> x)"
        have hx_ball: "x \<in> ball P \<delta>"
          using hx_local by (by100 blast)
        have hx_not_R: "x \<notin> ?R"
          using hx_local by (by100 blast)
        have hx_ne: "x \<noteq> P"
          using hx_not_R hP_R by (by100 blast)
        have hx_dist_pos: "dist P x > 0"
          using hx_ne by (by100 simp)
        have h\<rho>x_ball: "\<rho> x \<in> ball P \<delta>"
        proof -
          have "dist P (\<rho> x) = r"
            unfolding \<rho>_def using hx_dist_pos hr_pos
            by (simp add: dist_norm norm_minus_commute)
          thus ?thesis
            using hr_lt_\<delta> by (by100 simp)
        qed
        have hz_ball: "z \<in> ball P \<delta>"
          using closed_segment_subset[OF hx_ball h\<rho>x_ball convex_ball] hz_seg
          by (by100 blast)
        have hz_not_R: "z \<notin> ?R"
        proof
          assume hzR: "z \<in> ?R"
          consider (S1) "z \<in> ?S1" | (S2) "z \<in> ?S2" | (S3) "z \<in> ?S3"
            using hzR by (by100 blast)
          hence "x \<in> ?R"
          proof cases
            case S1
            have "x \<in> ?S1"
              by (rule h_radial_ray_preimage_segment
                  [OF hx_local hz_seg S1 hp\<^sub>1 h\<delta>p\<^sub>1])
            thus ?thesis by (by100 blast)
          next
            case S2
            have "x \<in> ?S2"
              by (rule h_radial_ray_preimage_segment
                  [OF hx_local hz_seg S2 hp\<^sub>2 h\<delta>p\<^sub>2])
            thus ?thesis by (by100 blast)
          next
            case S3
            have "x \<in> ?S3"
              by (rule h_radial_ray_preimage_segment
                  [OF hx_local hz_seg S3 hp\<^sub>3 h\<delta>p\<^sub>3])
            thus ?thesis by (by100 blast)
          qed
          thus False
            using hx_not_R by (by100 blast)
        qed
        show "z \<in> ball P \<delta> - ?R"
          using hz_ball hz_not_R by (by100 blast)
      qed
      have h_circle_component_subset_local:
        "\<And>K. K \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})
          \<Longrightarrow> K \<subseteq> ball P \<delta> - ?R"
      proof
        fix K z
        assume hK_comp: "K \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"
          and hzK: "z \<in> K"
        have hK_sub: "K \<subseteq> sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
          using hK_comp in_components_subset by (by100 blast)
        have hz_sphere: "z \<in> sphere P r"
          using hzK hK_sub by (by100 blast)
        have hz_not_qs: "z \<notin> {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
          using hzK hK_sub by (by100 blast)
        have hz_ball: "z \<in> ball P \<delta>"
          using hz_sphere hr_lt_\<delta> by (by100 simp)
        have hz_not_R: "z \<notin> ?R"
        proof
          assume hzR: "z \<in> ?R"
          have "z \<in> ?R \<inter> sphere P r"
            using hzR hz_sphere by (by100 blast)
          hence "z \<in> {q\<^sub>1, q\<^sub>2, q\<^sub>3}"
            using hR_sphere_r by (by100 simp)
          thus False
            using hz_not_qs by (by100 blast)
        qed
        show "z \<in> ball P \<delta> - ?R"
          using hz_ball hz_not_R by (by100 blast)
      qed
      have h_same_aux:
        "\<And>C D. \<lbrakk>C \<in> components (ball P \<delta> - ?R);
            D \<in> components (ball P \<delta> - ?R);
            \<exists>K\<in>components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}).
              \<rho> ` C \<subseteq> K \<and> \<rho> ` D \<subseteq> K\<rbrakk>
          \<Longrightarrow> C = D"
      proof -
        fix C D
        assume hC_comp: "C \<in> components (ball P \<delta> - ?R)"
          and hD_comp: "D \<in> components (ball P \<delta> - ?R)"
          and htrace_same:
            "\<exists>K\<in>components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3}).
              \<rho> ` C \<subseteq> K \<and> \<rho> ` D \<subseteq> K"
        obtain K where hK_comp: "K \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"
          and hC_trace: "\<rho> ` C \<subseteq> K"
          and hD_trace: "\<rho> ` D \<subseteq> K"
          using htrace_same by (by100 clarify)
        obtain x where hxC: "x \<in> C"
          using hC_comp in_components_nonempty by (by100 blast)
        obtain y where hyD: "y \<in> D"
          using hD_comp in_components_nonempty by (by100 blast)
        have hC_sub: "C \<subseteq> ball P \<delta> - ?R"
          using hC_comp in_components_subset by (by100 blast)
        have hD_sub: "D \<subseteq> ball P \<delta> - ?R"
          using hD_comp in_components_subset by (by100 blast)
        have hx_local: "x \<in> ball P \<delta> - ?R"
          using hxC hC_sub by (by100 blast)
        have hy_local: "y \<in> ball P \<delta> - ?R"
          using hyD hD_sub by (by100 blast)
        have h\<rho>x_K: "\<rho> x \<in> K"
          using hxC hC_trace by (by100 blast)
        have h\<rho>y_K: "\<rho> y \<in> K"
          using hyD hD_trace by (by100 blast)
        let ?T = "closed_segment x (\<rho> x) \<union> K \<union> closed_segment y (\<rho> y)"
        have hsegx_conn: "connected (closed_segment x (\<rho> x))"
          by (rule convex_connected[OF convex_closed_segment])
        have hK_conn: "connected K"
          using hK_comp in_components_connected by (by100 blast)
        have hsegy_conn: "connected (closed_segment y (\<rho> y))"
          by (rule convex_connected[OF convex_closed_segment])
        have hsegx_K_meet: "closed_segment x (\<rho> x) \<inter> K \<noteq> {}"
        proof -
          have "\<rho> x \<in> closed_segment x (\<rho> x)"
            by (by100 simp)
          thus ?thesis using h\<rho>x_K by (by100 blast)
        qed
        have hleft_conn: "connected (closed_segment x (\<rho> x) \<union> K)"
          by (rule connected_Un[OF hsegx_conn hK_conn hsegx_K_meet])
        have hleft_segy_meet:
            "(closed_segment x (\<rho> x) \<union> K) \<inter> closed_segment y (\<rho> y) \<noteq> {}"
        proof -
          have "\<rho> y \<in> closed_segment y (\<rho> y)"
            by (by100 simp)
          thus ?thesis using h\<rho>y_K by (by100 blast)
        qed
        have hT_conn: "connected ?T"
          by (rule connected_Un[OF hleft_conn hsegy_conn hleft_segy_meet])
        have hT_sub: "?T \<subseteq> ball P \<delta> - ?R"
        proof
          fix z
          assume hzT: "z \<in> ?T"
          consider (X) "z \<in> closed_segment x (\<rho> x)"
            | (K) "z \<in> K"
            | (Y) "z \<in> closed_segment y (\<rho> y)"
            using hzT by (by100 blast)
          thus "z \<in> ball P \<delta> - ?R"
          proof cases
            case X
            show ?thesis using h_radial_segment_subset[OF hx_local] X by (by100 blast)
          next
            case K
            show ?thesis using h_circle_component_subset_local[OF hK_comp] K by (by100 blast)
          next
            case Y
            show ?thesis using h_radial_segment_subset[OF hy_local] Y by (by100 blast)
          qed
        qed
        have hC_meet_T: "C \<inter> ?T \<noteq> {}"
        proof -
          have "x \<in> closed_segment x (\<rho> x)"
            by (by100 simp)
          thus ?thesis using hxC by (by100 blast)
        qed
        have hD_meet_T: "D \<inter> ?T \<noteq> {}"
        proof -
          have "y \<in> closed_segment y (\<rho> y)"
            by (by100 simp)
          thus ?thesis using hyD by (by100 blast)
        qed
        have hjoin:
            "connected ?T \<and> ?T \<subseteq> ball P \<delta> - ?R \<and>
              C \<in> components (ball P \<delta> - ?R) \<and>
              D \<in> components (ball P \<delta> - ?R) \<and>
              C \<inter> ?T \<noteq> {} \<and> D \<inter> ?T \<noteq> {}"
          using hT_conn hT_sub hC_comp hD_comp hC_meet_T hD_meet_T
          by (by100 blast)
        show "C = D"
          by (rule joinable_components_eq[OF hjoin])
      qed
      show ?thesis using h_same_aux by (by100 blast)
    qed
    have h_disk_components_inject_circle:
      "\<exists>f. inj_on f (components (ball P \<delta> - ?R)) \<and>
            f ` components (ball P \<delta> - ?R) \<subseteq>
              components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"
    proof -
      obtain F where hF_fin: "finite F"
        and hF:
          "\<forall>C \<in> components (ball P \<delta> - ?R).
            \<exists>K \<in> F. \<rho> ` C \<subseteq> K \<and>
              K \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"
        using h_radial_components_reduce_to_circle by (by100 blast)
      obtain f where hf:
        "\<forall>C \<in> components (ball P \<delta> - ?R).
            f C \<in> F \<and> \<rho> ` C \<subseteq> f C \<and>
              f C \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"
        using bchoice[of "components (ball P \<delta> - ?R)"
            "\<lambda>C K. K \<in> F \<and> \<rho> ` C \<subseteq> K \<and>
              K \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"] hF
        by (by100 blast)
      have hf_inj: "inj_on f (components (ball P \<delta> - ?R))"
      proof (unfold inj_on_def, intro ballI impI)
        fix C D
        assume hC: "C \<in> components (ball P \<delta> - ?R)"
          and hD: "D \<in> components (ball P \<delta> - ?R)"
          and hf_eq: "f C = f D"
        have hfC_comp: "f C \<in> components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"
          using hf hC by (by100 blast)
        have hC_sub: "\<rho> ` C \<subseteq> f C"
          using hf hC by (by100 blast)
        have hD_sub: "\<rho> ` D \<subseteq> f C"
          using hf hD hf_eq by (by100 blast)
        show "C = D"
          using h_same_circle_component_same_disk_component hC hD hfC_comp hC_sub hD_sub
          by (by100 blast)
      qed
      have hf_sub:
          "f ` components (ball P \<delta> - ?R) \<subseteq>
            components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"
        using hf by (by100 blast)
      show ?thesis using hf_inj hf_sub by (by100 blast)
    qed
    obtain f where hf_inj: "inj_on f (components (ball P \<delta> - ?R))"
      and hf_sub:
        "f ` components (ball P \<delta> - ?R) \<subseteq>
          components (sphere P r - {q\<^sub>1, q\<^sub>2, q\<^sub>3})"
      using h_disk_components_inject_circle by (by100 blast)
    have hf_image_finite: "finite (f ` components (ball P \<delta> - ?R))"
      by (rule finite_subset[OF hf_sub hcircle_components_finite])
    show ?thesis
      by (rule finite_imageD[OF hf_image_finite hf_inj])
  qed
  show ?thesis
    by (rule hR_components_finite)
qed

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

lemma geotop_polygon_not_broken_line_graph_prefix:
  fixes J :: "(real^2) set"
  assumes hpolygon: "geotop_is_polygon J"
  assumes hbroken: "geotop_is_broken_line J"
  shows False
proof -
  have hJsphere:
      "geotop_is_n_sphere J
        (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hpolygon unfolding geotop_is_polygon_def by (by100 blast)
  obtain f where hhomeo: "top1_homeomorphism_on J
                           (subspace_topology UNIV geotop_euclidean_topology J)
                           (geotop_std_sphere::(real^2) set)
                           (subspace_topology UNIV geotop_euclidean_topology
                              (geotop_std_sphere::(real^2) set)) f"
    using hJsphere unfolding geotop_is_n_sphere_def by (by100 blast)
  have hhomeo_HOL: "J homeomorphic (geotop_std_sphere::(real^2) set)"
    by (rule top1_homeomorphism_on_geotop_imp_HOL_homeomorphic[OF hhomeo])
  have hstd_eq: "(geotop_std_sphere::(real^2) set) = sphere 0 1"
    unfolding geotop_std_sphere_def sphere_def by (by100 simp)
  have hJ_sphere: "J homeomorphic sphere (0::real^2) 1"
    using hhomeo_HOL hstd_eq by (by100 simp)
  have hnotconn_HOL: "\<not> connected (- J)"
    using Jordan_Brouwer_separation[OF hJ_sphere] zero_less_one by (by100 blast)
  have hnot_conn:
      "\<not> top1_connected_on (UNIV - J)
        (subspace_topology UNIV geotop_euclidean_topology (UNIV - J))"
    using hnotconn_HOL top1_connected_on_geotop_iff_connected
    by (metis Compl_eq_Diff_UNIV)
  have hconn:
      "top1_connected_on (UNIV - J)
        (subspace_topology UNIV geotop_euclidean_topology (UNIV - J))"
    by (rule Theorem_GT_2_3[OF hbroken])
  show False
    using hnot_conn hconn by (by100 blast)
qed

lemma geotop_incident_edge_other_endpoint_vertex_prefix:
  fixes L :: "(real^2) set set" and w :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hwL: "{w} \<in> L"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "\<exists>q. q \<noteq> w \<and> e = closed_segment w q \<and> {q} \<in> L"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  obtain a b where hab: "a \<noteq> b" and heab: "e = closed_segment a b"
    by (rule geotop_edge_closed_segment_obtain_prefix[OF hedge])
  have hw_endpoint: "w = a \<or> w = b"
    by (rule geotop_1dim_vertex_in_1simplex_is_endpoint
        [OF hcomplex hwL heL heab hab hwe])
  show ?thesis
  proof (rule disjE[OF hw_endpoint])
    assume hwa: "w = a"
    have hb_face: "geotop_is_face {b} e"
      using geotop_closed_segment_is_face_endpoint[OF hab, of b] heab by (by100 simp)
    have hbL: "{b} \<in> L"
      using geotop_is_complex_face_closed[OF hcomplex] heL hb_face by (by100 blast)
    show ?thesis
    proof (rule exI[where x = b])
      show "b \<noteq> w \<and> e = closed_segment w b \<and> {b} \<in> L"
        using hab heab hwa hbL by (by100 simp)
    qed
  next
    assume hwb: "w = b"
    have ha_face: "geotop_is_face {a} e"
      using geotop_closed_segment_is_face_endpoint[OF hab, of a] heab by (by100 simp)
    have haL: "{a} \<in> L"
      using geotop_is_complex_face_closed[OF hcomplex] heL ha_face by (by100 blast)
    have heba: "e = closed_segment b a"
      using heab closed_segment_commute[of a b] by (by100 simp)
    show ?thesis
    proof (rule exI[where x = a])
      show "a \<noteq> w \<and> e = closed_segment w a \<and> {a} \<in> L"
        using hab heba hwb haL by (by100 simp)
    qed
  qed
qed

lemma top1_arc_non_endpoint_removal_disconnected_prefix:
  assumes hep: "top1_arc_endpoints_on D (subspace_topology X TX D) = {a, b}"
  assumes hpD: "p \<in> D"
  assumes hp_ne: "p \<notin> {a, b}"
  shows "\<not> top1_connected_on (D - {p})
    (subspace_topology X TX (D - {p}))"
proof
  assume hconn: "top1_connected_on (D - {p})
    (subspace_topology X TX (D - {p}))"
  have hsub:
      "subspace_topology D (subspace_topology X TX D) (D - {p})
      = subspace_topology X TX (D - {p})"
    by (rule subspace_topology_trans[OF Diff_subset])
  have hp_ep: "p \<in> top1_arc_endpoints_on D (subspace_topology X TX D)"
    unfolding top1_arc_endpoints_on_def
    using hpD hconn hsub by (by100 simp)
  show False
    using hep hp_ep hp_ne by (by100 simp)
qed

lemma geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix:
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
    Local graph-topology cutpoint package.  A finite linear carrier with more
    than two incident edge germs at \<open>w\<close> has at least three small punctured
    edge sectors at \<open>w\<close>; after deleting \<open>w\<close>, these sectors cannot be joined
    in the carrier without passing through \<open>w\<close>, so the punctured carrier is
    disconnected. **)
proof -
  define E where "E = {e\<in>L. geotop_is_edge e \<and> w \<in> e}"
  have hE_fin: "finite E"
    unfolding E_def using hL_fin by (by100 simp)
  have hE_card_gt2: "card E > 2"
    unfolding E_def using hbranch by (by100 simp)
  have hcard3: "3 \<le> card E"
    using hE_card_gt2 by (by100 linarith)
  obtain W where hW_sub: "W \<subseteq> E" and hW_card: "card W = 3" and hW_fin: "finite W"
    by (rule obtain_subset_with_card_n[OF hcard3])
  have hW_three:
      "\<exists>e\<^sub>1 e\<^sub>2 e\<^sub>3. W = {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> e\<^sub>1 \<noteq> e\<^sub>2 \<and> e\<^sub>2 \<noteq> e\<^sub>3 \<and> e\<^sub>1 \<noteq> e\<^sub>3"
    by (rule iffD1[OF card_3_iff hW_card])
  obtain e\<^sub>1 e\<^sub>2 e\<^sub>3 where he\<^sub>1E: "e\<^sub>1 \<in> E"
      and he\<^sub>2E: "e\<^sub>2 \<in> E"
      and he\<^sub>3E: "e\<^sub>3 \<in> E"
      and he\<^sub>12: "e\<^sub>1 \<noteq> e\<^sub>2"
      and he\<^sub>13: "e\<^sub>1 \<noteq> e\<^sub>3"
      and he\<^sub>23: "e\<^sub>2 \<noteq> e\<^sub>3"
  proof -
    obtain e\<^sub>1 e\<^sub>2 e\<^sub>3 where hW_eq: "W = {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and he\<^sub>12: "e\<^sub>1 \<noteq> e\<^sub>2" and he\<^sub>23: "e\<^sub>2 \<noteq> e\<^sub>3" and he\<^sub>13: "e\<^sub>1 \<noteq> e\<^sub>3"
      using hW_three by (elim exE conjE)
    have he\<^sub>1E: "e\<^sub>1 \<in> E" and he\<^sub>2E: "e\<^sub>2 \<in> E" and he\<^sub>3E: "e\<^sub>3 \<in> E"
      using hW_sub hW_eq by (by100 blast)+
    show ?thesis
      by (rule that[OF he\<^sub>1E he\<^sub>2E he\<^sub>3E he\<^sub>12 he\<^sub>13 he\<^sub>23])
  qed
  have he\<^sub>1L: "e\<^sub>1 \<in> L"
    using he\<^sub>1E unfolding E_def by (by100 blast)
  have he\<^sub>2L: "e\<^sub>2 \<in> L"
    using he\<^sub>2E unfolding E_def by (by100 blast)
  have he\<^sub>3L: "e\<^sub>3 \<in> L"
    using he\<^sub>3E unfolding E_def by (by100 blast)
  have he\<^sub>1_edge: "geotop_is_edge e\<^sub>1"
    using he\<^sub>1E unfolding E_def by (by100 blast)
  have he\<^sub>2_edge: "geotop_is_edge e\<^sub>2"
    using he\<^sub>2E unfolding E_def by (by100 blast)
  have he\<^sub>3_edge: "geotop_is_edge e\<^sub>3"
    using he\<^sub>3E unfolding E_def by (by100 blast)
  have hw_e\<^sub>1: "w \<in> e\<^sub>1"
    using he\<^sub>1E unfolding E_def by (by100 blast)
  have hw_e\<^sub>2: "w \<in> e\<^sub>2"
    using he\<^sub>2E unfolding E_def by (by100 blast)
  have hw_e\<^sub>3: "w \<in> e\<^sub>3"
    using he\<^sub>3E unfolding E_def by (by100 blast)
  obtain q\<^sub>1 where hq\<^sub>1w: "q\<^sub>1 \<noteq> w"
      and he\<^sub>1_seg: "e\<^sub>1 = closed_segment w q\<^sub>1"
      and hq\<^sub>1L: "{q\<^sub>1} \<in> L"
  proof -
    have he\<^sub>1L: "e\<^sub>1 \<in> L"
      using he\<^sub>1E unfolding E_def by (by100 blast)
    have he\<^sub>1_edge: "geotop_is_edge e\<^sub>1"
      using he\<^sub>1E unfolding E_def by (by100 blast)
    have hw_e\<^sub>1: "w \<in> e\<^sub>1"
      using he\<^sub>1E unfolding E_def by (by100 blast)
    have hex: "\<exists>q. q \<noteq> w \<and> e\<^sub>1 = closed_segment w q \<and> {q} \<in> L"
      by (rule geotop_incident_edge_other_endpoint_vertex_prefix
          [OF hL_linear hwL he\<^sub>1L he\<^sub>1_edge hw_e\<^sub>1])
    show ?thesis
      using hex that by (by100 blast)
  qed
  obtain q\<^sub>2 where hq\<^sub>2w: "q\<^sub>2 \<noteq> w"
      and he\<^sub>2_seg: "e\<^sub>2 = closed_segment w q\<^sub>2"
      and hq\<^sub>2L: "{q\<^sub>2} \<in> L"
  proof -
    have he\<^sub>2L: "e\<^sub>2 \<in> L"
      using he\<^sub>2E unfolding E_def by (by100 blast)
    have he\<^sub>2_edge: "geotop_is_edge e\<^sub>2"
      using he\<^sub>2E unfolding E_def by (by100 blast)
    have hw_e\<^sub>2: "w \<in> e\<^sub>2"
      using he\<^sub>2E unfolding E_def by (by100 blast)
    have hex: "\<exists>q. q \<noteq> w \<and> e\<^sub>2 = closed_segment w q \<and> {q} \<in> L"
      by (rule geotop_incident_edge_other_endpoint_vertex_prefix
          [OF hL_linear hwL he\<^sub>2L he\<^sub>2_edge hw_e\<^sub>2])
    show ?thesis
      using hex that by (by100 blast)
  qed
  obtain q\<^sub>3 where hq\<^sub>3w: "q\<^sub>3 \<noteq> w"
      and he\<^sub>3_seg: "e\<^sub>3 = closed_segment w q\<^sub>3"
      and hq\<^sub>3L: "{q\<^sub>3} \<in> L"
  proof -
    have he\<^sub>3L: "e\<^sub>3 \<in> L"
      using he\<^sub>3E unfolding E_def by (by100 blast)
    have he\<^sub>3_edge: "geotop_is_edge e\<^sub>3"
      using he\<^sub>3E unfolding E_def by (by100 blast)
    have hw_e\<^sub>3: "w \<in> e\<^sub>3"
      using he\<^sub>3E unfolding E_def by (by100 blast)
    have hex: "\<exists>q. q \<noteq> w \<and> e\<^sub>3 = closed_segment w q \<and> {q} \<in> L"
      by (rule geotop_incident_edge_other_endpoint_vertex_prefix
          [OF hL_linear hwL he\<^sub>3L he\<^sub>3_edge hw_e\<^sub>3])
    show ?thesis
      using hex that by (by100 blast)
  qed
  have hq\<^sub>12: "q\<^sub>1 \<noteq> q\<^sub>2"
  proof
    assume hq_eq: "q\<^sub>1 = q\<^sub>2"
    have "e\<^sub>1 = e\<^sub>2"
      using he\<^sub>1_seg he\<^sub>2_seg hq_eq by (by100 simp)
    then show False
      using he\<^sub>12 by (by100 blast)
  qed
  have hq\<^sub>13: "q\<^sub>1 \<noteq> q\<^sub>3"
  proof
    assume hq_eq: "q\<^sub>1 = q\<^sub>3"
    have "e\<^sub>1 = e\<^sub>3"
      using he\<^sub>1_seg he\<^sub>3_seg hq_eq by (by100 simp)
    then show False
      using he\<^sub>13 by (by100 blast)
  qed
  have hq\<^sub>23: "q\<^sub>2 \<noteq> q\<^sub>3"
  proof
    assume hq_eq: "q\<^sub>2 = q\<^sub>3"
    have "e\<^sub>2 = e\<^sub>3"
      using he\<^sub>2_seg he\<^sub>3_seg hq_eq by (by100 simp)
    then show False
      using he\<^sub>23 by (by100 blast)
  qed
  have hq_card3: "card {q\<^sub>1, q\<^sub>2, q\<^sub>3} = 3"
    using hq\<^sub>12 hq\<^sub>13 hq\<^sub>23 by (by100 simp)
  have he\<^sub>1_sub_poly: "e\<^sub>1 \<subseteq> geotop_polyhedron L"
    unfolding geotop_polyhedron_def using he\<^sub>1L by (by100 blast)
  have he\<^sub>2_sub_poly: "e\<^sub>2 \<subseteq> geotop_polyhedron L"
    unfolding geotop_polyhedron_def using he\<^sub>2L by (by100 blast)
  have he\<^sub>3_sub_poly: "e\<^sub>3 \<subseteq> geotop_polyhedron L"
    unfolding geotop_polyhedron_def using he\<^sub>3L by (by100 blast)
  have hq\<^sub>1_punctured: "q\<^sub>1 \<in> geotop_polyhedron L - {w}"
    using hq\<^sub>1L hq\<^sub>1w unfolding geotop_polyhedron_def by (by100 blast)
  have hq\<^sub>2_punctured: "q\<^sub>2 \<in> geotop_polyhedron L - {w}"
    using hq\<^sub>2L hq\<^sub>2w unfolding geotop_polyhedron_def by (by100 blast)
  have hq\<^sub>3_punctured: "q\<^sub>3 \<in> geotop_polyhedron L - {w}"
    using hq\<^sub>3L hq\<^sub>3w unfolding geotop_polyhedron_def by (by100 blast)
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL_linear])
  have hL_1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_prefix[OF hL_linear])
  have he\<^sub>12_inter: "e\<^sub>1 \<inter> e\<^sub>2 = {w}"
  proof -
    have hInt: "e\<^sub>1 \<inter> e\<^sub>2 \<noteq> {}"
      using hw_e\<^sub>1 hw_e\<^sub>2 by (by100 blast)
    obtain p where hp: "e\<^sub>1 \<inter> e\<^sub>2 = {p}"
      using geotop_complex_distinct_intersecting_edges_inter_singleton_prefix
          [OF hL_complex he\<^sub>1L he\<^sub>2L he\<^sub>1_edge he\<^sub>2_edge he\<^sub>12 hInt]
      by (by100 blast)
    have "w \<in> e\<^sub>1 \<inter> e\<^sub>2"
      using hw_e\<^sub>1 hw_e\<^sub>2 by (by100 blast)
    hence "p = w"
      using hp by (by100 simp)
    show ?thesis
      using hp \<open>p = w\<close> by (by100 simp)
  qed
  have he\<^sub>13_inter: "e\<^sub>1 \<inter> e\<^sub>3 = {w}"
  proof -
    have hInt: "e\<^sub>1 \<inter> e\<^sub>3 \<noteq> {}"
      using hw_e\<^sub>1 hw_e\<^sub>3 by (by100 blast)
    obtain p where hp: "e\<^sub>1 \<inter> e\<^sub>3 = {p}"
      using geotop_complex_distinct_intersecting_edges_inter_singleton_prefix
          [OF hL_complex he\<^sub>1L he\<^sub>3L he\<^sub>1_edge he\<^sub>3_edge he\<^sub>13 hInt]
      by (by100 blast)
    have "w \<in> e\<^sub>1 \<inter> e\<^sub>3"
      using hw_e\<^sub>1 hw_e\<^sub>3 by (by100 blast)
    hence "p = w"
      using hp by (by100 simp)
    show ?thesis
      using hp \<open>p = w\<close> by (by100 simp)
  qed
  have he\<^sub>23_inter: "e\<^sub>2 \<inter> e\<^sub>3 = {w}"
  proof -
    have hInt: "e\<^sub>2 \<inter> e\<^sub>3 \<noteq> {}"
      using hw_e\<^sub>2 hw_e\<^sub>3 by (by100 blast)
    obtain p where hp: "e\<^sub>2 \<inter> e\<^sub>3 = {p}"
      using geotop_complex_distinct_intersecting_edges_inter_singleton_prefix
          [OF hL_complex he\<^sub>2L he\<^sub>3L he\<^sub>2_edge he\<^sub>3_edge he\<^sub>23 hInt]
      by (by100 blast)
    have "w \<in> e\<^sub>2 \<inter> e\<^sub>3"
      using hw_e\<^sub>2 hw_e\<^sub>3 by (by100 blast)
    hence "p = w"
      using hp by (by100 simp)
    show ?thesis
      using hp \<open>p = w\<close> by (by100 simp)
  qed
  have he\<^sub>12_punctured_disj: "(e\<^sub>1 - {w}) \<inter> (e\<^sub>2 - {w}) = {}"
    using he\<^sub>12_inter by (by100 blast)
  have he\<^sub>13_punctured_disj: "(e\<^sub>1 - {w}) \<inter> (e\<^sub>3 - {w}) = {}"
    using he\<^sub>13_inter by (by100 blast)
  have he\<^sub>23_punctured_disj: "(e\<^sub>2 - {w}) \<inter> (e\<^sub>3 - {w}) = {}"
    using he\<^sub>23_inter by (by100 blast)
  have hincident_selected_punctured_disj:
      "\<And>e S. e \<in> E \<Longrightarrow> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3} \<Longrightarrow> e \<noteq> S
        \<Longrightarrow> (e - {w}) \<inter> (S - {w}) = {}"
  proof -
    fix e S
    assume heE: "e \<in> E"
    assume hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
    assume heS: "e \<noteq> S"
    have hSE: "S \<in> E"
      using hS he\<^sub>1E he\<^sub>2E he\<^sub>3E by (by100 blast)
    have heL': "e \<in> L"
      using heE unfolding E_def by (by100 blast)
    have hSL: "S \<in> L"
      using hSE unfolding E_def by (by100 blast)
    have he_edge': "geotop_is_edge e"
      using heE unfolding E_def by (by100 blast)
    have hS_edge: "geotop_is_edge S"
      using hSE unfolding E_def by (by100 blast)
    have hwe: "w \<in> e"
      using heE unfolding E_def by (by100 blast)
    have hwS: "w \<in> S"
      using hSE unfolding E_def by (by100 blast)
    have hInt: "e \<inter> S \<noteq> {}"
      using hwe hwS by (by100 blast)
    obtain p where hp: "e \<inter> S = {p}"
      using geotop_complex_distinct_intersecting_edges_inter_singleton_prefix
          [OF hL_complex heL' hSL he_edge' hS_edge heS hInt]
      by (by100 blast)
    have "w \<in> e \<inter> S"
      using hwe hwS by (by100 blast)
    hence hpw: "p = w"
      using hp by (by100 simp)
    have "e \<inter> S = {w}"
      using hp hpw by (by100 simp)
    then show "(e - {w}) \<inter> (S - {w}) = {}"
      by (by100 blast)
  qed
  have he\<^sub>1_punctured_sub: "e\<^sub>1 - {w} \<subseteq> geotop_polyhedron L - {w}"
    using he\<^sub>1_sub_poly by (by100 blast)
  have he\<^sub>2_punctured_sub: "e\<^sub>2 - {w} \<subseteq> geotop_polyhedron L - {w}"
    using he\<^sub>2_sub_poly by (by100 blast)
  have he\<^sub>3_punctured_sub: "e\<^sub>3 - {w} \<subseteq> geotop_polyhedron L - {w}"
    using he\<^sub>3_sub_poly by (by100 blast)
  have he\<^sub>1_germ_meets_ball:
      "\<And>\<delta>::real. 0 < \<delta> \<Longrightarrow> \<exists>x. x \<in> (e\<^sub>1 - {w}) \<inter> ball w \<delta>"
  proof -
    fix \<delta> :: real
    assume h\<delta>: "0 < \<delta>"
    obtain x where hx: "x \<in> (closed_segment w q\<^sub>1 - {w}) \<inter> ball w \<delta>"
      using nondegenerate_segment_meets_ball[OF hq\<^sub>1w h\<delta>] by (by100 blast)
    show "\<exists>x. x \<in> (e\<^sub>1 - {w}) \<inter> ball w \<delta>"
      using hx he\<^sub>1_seg by (by100 blast)
  qed
  have he\<^sub>2_germ_meets_ball:
      "\<And>\<delta>::real. 0 < \<delta> \<Longrightarrow> \<exists>x. x \<in> (e\<^sub>2 - {w}) \<inter> ball w \<delta>"
  proof -
    fix \<delta> :: real
    assume h\<delta>: "0 < \<delta>"
    obtain x where hx: "x \<in> (closed_segment w q\<^sub>2 - {w}) \<inter> ball w \<delta>"
      using nondegenerate_segment_meets_ball[OF hq\<^sub>2w h\<delta>] by (by100 blast)
    show "\<exists>x. x \<in> (e\<^sub>2 - {w}) \<inter> ball w \<delta>"
      using hx he\<^sub>2_seg by (by100 blast)
  qed
  have he\<^sub>3_germ_meets_ball:
      "\<And>\<delta>::real. 0 < \<delta> \<Longrightarrow> \<exists>x. x \<in> (e\<^sub>3 - {w}) \<inter> ball w \<delta>"
  proof -
    fix \<delta> :: real
    assume h\<delta>: "0 < \<delta>"
    obtain x where hx: "x \<in> (closed_segment w q\<^sub>3 - {w}) \<inter> ball w \<delta>"
      using nondegenerate_segment_meets_ball[OF hq\<^sub>3w h\<delta>] by (by100 blast)
    show "\<exists>x. x \<in> (e\<^sub>3 - {w}) \<inter> ball w \<delta>"
      using hx he\<^sub>3_seg by (by100 blast)
  qed
  have hdist_q\<^sub>1_pos: "0 < dist w q\<^sub>1"
    using hq\<^sub>1w by (by100 simp)
  have hdist_q\<^sub>2_pos: "0 < dist w q\<^sub>2"
    using hq\<^sub>2w by (by100 simp)
  have hdist_q\<^sub>3_pos: "0 < dist w q\<^sub>3"
    using hq\<^sub>3w by (by100 simp)
  obtain \<delta>\<^sub>L where h\<delta>\<^sub>L_pos: "0 < \<delta>\<^sub>L"
      and h\<delta>\<^sub>L_star:
        "ball w \<delta>\<^sub>L \<inter> geotop_polyhedron L
          \<subseteq> \<Union>{\<tau>\<in>L. w \<in> \<tau>}"
  proof -
    have hw_poly: "w \<in> \<Union>L"
      using hwL unfolding geotop_polyhedron_def by (by100 blast)
    obtain \<delta> where h\<delta>pos: "\<delta> > 0"
        and h\<delta>star: "ball w \<delta> \<inter> \<Union>L \<subseteq> \<Union>{\<tau>\<in>L. w \<in> \<tau>}"
      using geotop_complex_finite_subcomplex_local_point_carriers_prefix
          [OF hL_complex hL_fin subset_refl hw_poly]
      by (by100 blast)
    have hstar: "ball w \<delta> \<inter> geotop_polyhedron L
        \<subseteq> \<Union>{\<tau>\<in>L. w \<in> \<tau>}"
      using h\<delta>star unfolding geotop_polyhedron_def by (by100 simp)
    show ?thesis
      by (rule that[OF h\<delta>pos hstar])
  qed
  obtain r where hr_pos: "0 < r"
      and hr_lt_\<delta>\<^sub>L: "r < \<delta>\<^sub>L"
      and hr_lt_q\<^sub>1: "r < dist w q\<^sub>1"
      and hr_lt_q\<^sub>2: "r < dist w q\<^sub>2"
      and hr_lt_q\<^sub>3: "r < dist w q\<^sub>3"
  proof -
    let ?m = "min \<delta>\<^sub>L (min (dist w q\<^sub>1) (min (dist w q\<^sub>2) (dist w q\<^sub>3)))"
    let ?r = "?m / 2"
    have hm_pos: "0 < ?m"
      using h\<delta>\<^sub>L_pos hdist_q\<^sub>1_pos hdist_q\<^sub>2_pos hdist_q\<^sub>3_pos by (by100 simp)
    have hr_pos': "0 < ?r"
      using hm_pos by (by100 simp)
    have hm_le_\<delta>\<^sub>L: "?m \<le> \<delta>\<^sub>L"
      by (by100 simp)
    have hm_le_q\<^sub>1: "?m \<le> dist w q\<^sub>1"
      by (by100 simp)
    have hm_le_q\<^sub>2: "?m \<le> dist w q\<^sub>2"
      by (by100 simp)
    have hm_le_q\<^sub>3: "?m \<le> dist w q\<^sub>3"
      by (by100 simp)
    have hr_lt_\<delta>\<^sub>L': "?r < \<delta>\<^sub>L"
      using hm_pos hm_le_\<delta>\<^sub>L by (by100 linarith)
    have hr_lt_q\<^sub>1': "?r < dist w q\<^sub>1"
      using hm_pos hm_le_q\<^sub>1 by (by100 linarith)
    have hr_lt_q\<^sub>2': "?r < dist w q\<^sub>2"
      using hm_pos hm_le_q\<^sub>2 by (by100 linarith)
    have hr_lt_q\<^sub>3': "?r < dist w q\<^sub>3"
      using hm_pos hm_le_q\<^sub>3 by (by100 linarith)
    show ?thesis
      by (rule that[OF hr_pos' hr_lt_\<delta>\<^sub>L' hr_lt_q\<^sub>1' hr_lt_q\<^sub>2' hr_lt_q\<^sub>3'])
  qed
  have hball_poly_star:
      "ball w r \<inter> geotop_polyhedron L \<subseteq> \<Union>{\<tau>\<in>L. w \<in> \<tau>}"
  proof
    fix x
    assume hx: "x \<in> ball w r \<inter> geotop_polyhedron L"
    have hx_delta: "x \<in> ball w \<delta>\<^sub>L"
      using hx hr_lt_\<delta>\<^sub>L by (by100 simp)
    have hx_delta_poly: "x \<in> ball w \<delta>\<^sub>L \<inter> geotop_polyhedron L"
      using hx hx_delta by (by100 blast)
    show "x \<in> \<Union>{\<tau>\<in>L. w \<in> \<tau>}"
      using h\<delta>\<^sub>L_star hx_delta_poly by (by100 blast)
  qed
  have hstar_carrier_subset:
      "\<Union>{\<tau>\<in>L. w \<in> \<tau>} \<subseteq> {w} \<union> \<Union>E"
  proof
    fix x
    assume hx: "x \<in> \<Union>{\<tau>\<in>L. w \<in> \<tau>}"
    obtain \<tau> where h\<tau>L: "\<tau> \<in> L" and hw\<tau>: "w \<in> \<tau>" and hx\<tau>: "x \<in> \<tau>"
      using hx by (by100 blast)
    have hcases:
        "(\<exists>v. \<tau> = {v}) \<or> (\<exists>a b. a \<noteq> b \<and> \<tau> = closed_segment a b)"
      by (rule geotop_1dim_simplex_cases[OF hL_1dim h\<tau>L])
    show "x \<in> {w} \<union> \<Union>E"
    proof (rule disjE[OF hcases])
      assume "\<exists>v. \<tau> = {v}"
      then obtain v where h\<tau>v: "\<tau> = {v}"
        by (by100 blast)
      have "x = w"
        using hw\<tau> hx\<tau> h\<tau>v by (by100 blast)
      then show ?thesis
        by (by100 simp)
    next
      assume "\<exists>a b. a \<noteq> b \<and> \<tau> = closed_segment a b"
      then obtain a b where hab: "a \<noteq> b" and h\<tau>ab: "\<tau> = closed_segment a b"
        by (by100 blast)
      have h\<tau>edge: "geotop_is_edge \<tau>"
      proof -
        have "geotop_simplex_dim (closed_segment a b) 1"
          by (rule geotop_closed_segment_is_simplex[OF hab])
        then have "geotop_simplex_dim \<tau> 1"
          using h\<tau>ab by (by100 simp)
        then show ?thesis
          unfolding geotop_is_edge_def by (by100 simp)
      qed
      have h\<tau>E: "\<tau> \<in> E"
        unfolding E_def using h\<tau>L h\<tau>edge hw\<tau> by (by100 simp)
      show ?thesis
        using h\<tau>E hx\<tau> by (by100 blast)
    qed
  qed
  have hball_punctured_carrier_incident_germs:
      "ball w r \<inter> (geotop_polyhedron L - {w})
        \<subseteq> \<Union>((\<lambda>e. e - {w}) ` E)"
  proof
    fix x
    assume hx: "x \<in> ball w r \<inter> (geotop_polyhedron L - {w})"
    have hx_ball_poly: "x \<in> ball w r \<inter> geotop_polyhedron L"
      using hx by (by100 blast)
    have hx_star: "x \<in> \<Union>{\<tau>\<in>L. w \<in> \<tau>}"
      using hball_poly_star hx_ball_poly by (by100 blast)
    have hx_vertex_or_edge: "x \<in> {w} \<union> \<Union>E"
      using hstar_carrier_subset hx_star by (by100 blast)
    have hx_ne_w: "x \<notin> {w}"
      using hx by (by100 blast)
    have hx_edges: "x \<in> \<Union>E"
      using hx_vertex_or_edge hx_ne_w by (by100 blast)
    obtain e where heE: "e \<in> E" and hxe: "x \<in> e"
      using hx_edges by (by100 blast)
    have "x \<in> e - {w}"
      using hxe hx_ne_w by (by100 blast)
    then show "x \<in> \<Union>((\<lambda>e. e - {w}) ` E)"
      using heE by (by100 blast)
  qed
  have hother_incident_germ_in_radial_complement:
      "\<And>e. e \<in> E \<Longrightarrow> e \<notin> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<Longrightarrow> (e - {w}) \<inter> ball w r
          \<subseteq> ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3)"
  proof
    fix e x
    assume heE: "e \<in> E"
    assume he_not_selected: "e \<notin> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
    assume hx: "x \<in> (e - {w}) \<inter> ball w r"
    have hx_ball: "x \<in> ball w r"
      using hx by (by100 blast)
    have hx_e_punctured: "x \<in> e - {w}"
      using hx by (by100 blast)
    have hx_not_w: "x \<notin> {w}"
      using hx by (by100 blast)
    have hx_not_e\<^sub>1: "x \<notin> e\<^sub>1"
    proof
      assume hxe\<^sub>1: "x \<in> e\<^sub>1"
      have "x \<in> (e - {w}) \<inter> (e\<^sub>1 - {w})"
        using hx_e_punctured hxe\<^sub>1 hx_not_w by (by100 blast)
      moreover have "(e - {w}) \<inter> (e\<^sub>1 - {w}) = {}"
      proof (rule hincident_selected_punctured_disj[OF heE])
        show "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
          by (by100 simp)
        show "e \<noteq> e\<^sub>1"
          using he_not_selected by (by100 simp)
      qed
      ultimately show False
        by (by100 blast)
    qed
    have hx_not_e\<^sub>2: "x \<notin> e\<^sub>2"
    proof
      assume hxe\<^sub>2: "x \<in> e\<^sub>2"
      have "x \<in> (e - {w}) \<inter> (e\<^sub>2 - {w})"
        using hx_e_punctured hxe\<^sub>2 hx_not_w by (by100 blast)
      moreover have "(e - {w}) \<inter> (e\<^sub>2 - {w}) = {}"
      proof (rule hincident_selected_punctured_disj[OF heE])
        show "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
          by (by100 simp)
        show "e \<noteq> e\<^sub>2"
          using he_not_selected by (by100 simp)
      qed
      ultimately show False
        by (by100 blast)
    qed
    have hx_not_e\<^sub>3: "x \<notin> e\<^sub>3"
    proof
      assume hxe\<^sub>3: "x \<in> e\<^sub>3"
      have "x \<in> (e - {w}) \<inter> (e\<^sub>3 - {w})"
        using hx_e_punctured hxe\<^sub>3 hx_not_w by (by100 blast)
      moreover have "(e - {w}) \<inter> (e\<^sub>3 - {w}) = {}"
      proof (rule hincident_selected_punctured_disj[OF heE])
        show "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
          by (by100 simp)
        show "e \<noteq> e\<^sub>3"
          using he_not_selected by (by100 simp)
      qed
      ultimately show False
        by (by100 blast)
    qed
    show "x \<in> ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3)"
      using hx_ball hx_not_e\<^sub>1 hx_not_e\<^sub>2 hx_not_e\<^sub>3 by (by100 blast)
  qed
  have hlocal_punctured_carrier_sector_cover:
      "ball w r \<inter> (geotop_polyhedron L - {w})
        \<subseteq> ((e\<^sub>1 - {w}) \<inter> ball w r)
          \<union> ((e\<^sub>2 - {w}) \<inter> ball w r)
          \<union> ((e\<^sub>3 - {w}) \<inter> ball w r)
          \<union> (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))"
  proof
    fix x
    assume hx: "x \<in> ball w r \<inter> (geotop_polyhedron L - {w})"
    have hx_ball: "x \<in> ball w r"
      using hx by (by100 blast)
    have hx_incident_cover: "x \<in> \<Union>((\<lambda>e. e - {w}) ` E)"
      using hball_punctured_carrier_incident_germs hx by (by100 blast)
    obtain e where heE: "e \<in> E" and hxe_punctured: "x \<in> e - {w}"
      using hx_incident_cover by (by100 blast)
    show "x \<in> ((e\<^sub>1 - {w}) \<inter> ball w r)
          \<union> ((e\<^sub>2 - {w}) \<inter> ball w r)
          \<union> ((e\<^sub>3 - {w}) \<inter> ball w r)
          \<union> (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))"
    proof (cases "e \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}")
      case True
      then show ?thesis
        using hxe_punctured hx_ball by (by100 blast)
    next
      case False
      have "x \<in> (e - {w}) \<inter> ball w r"
        using hxe_punctured hx_ball by (by100 blast)
      then have "x \<in> ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3)"
        using hother_incident_germ_in_radial_complement[OF heE False] by (by100 blast)
      then show ?thesis
        by (by100 blast)
    qed
  qed
  define x\<^sub>1 where "x\<^sub>1 = w + (r / dist w q\<^sub>1) *\<^sub>R (q\<^sub>1 - w)"
  define x\<^sub>2 where "x\<^sub>2 = w + (r / dist w q\<^sub>2) *\<^sub>R (q\<^sub>2 - w)"
  define x\<^sub>3 where "x\<^sub>3 = w + (r / dist w q\<^sub>3) *\<^sub>R (q\<^sub>3 - w)"
  have hx\<^sub>1_edge_sphere: "x\<^sub>1 \<in> (e\<^sub>1 - {w}) \<inter> sphere w r"
  proof -
    have hr_le: "r \<le> dist w q\<^sub>1"
      using hr_lt_q\<^sub>1 by (by100 linarith)
    have hseg_sphere:
        "(closed_segment w q\<^sub>1 - {w}) \<inter> sphere w r = {x\<^sub>1}"
      by (rule closed_segment_sphere_unique_from_center
          [OF hq\<^sub>1w hr_pos hr_le x\<^sub>1_def])
    show ?thesis
      using hseg_sphere he\<^sub>1_seg by (by100 blast)
  qed
  have hx\<^sub>2_edge_sphere: "x\<^sub>2 \<in> (e\<^sub>2 - {w}) \<inter> sphere w r"
  proof -
    have hr_le: "r \<le> dist w q\<^sub>2"
      using hr_lt_q\<^sub>2 by (by100 linarith)
    have hseg_sphere:
        "(closed_segment w q\<^sub>2 - {w}) \<inter> sphere w r = {x\<^sub>2}"
      by (rule closed_segment_sphere_unique_from_center
          [OF hq\<^sub>2w hr_pos hr_le x\<^sub>2_def])
    show ?thesis
      using hseg_sphere he\<^sub>2_seg by (by100 blast)
  qed
  have hx\<^sub>3_edge_sphere: "x\<^sub>3 \<in> (e\<^sub>3 - {w}) \<inter> sphere w r"
  proof -
    have hr_le: "r \<le> dist w q\<^sub>3"
      using hr_lt_q\<^sub>3 by (by100 linarith)
    have hseg_sphere:
        "(closed_segment w q\<^sub>3 - {w}) \<inter> sphere w r = {x\<^sub>3}"
      by (rule closed_segment_sphere_unique_from_center
          [OF hq\<^sub>3w hr_pos hr_le x\<^sub>3_def])
    show ?thesis
      using hseg_sphere he\<^sub>3_seg by (by100 blast)
  qed
  have hx\<^sub>12: "x\<^sub>1 \<noteq> x\<^sub>2"
    using hx\<^sub>1_edge_sphere hx\<^sub>2_edge_sphere he\<^sub>12_punctured_disj by (by100 blast)
  have hx\<^sub>13: "x\<^sub>1 \<noteq> x\<^sub>3"
    using hx\<^sub>1_edge_sphere hx\<^sub>3_edge_sphere he\<^sub>13_punctured_disj by (by100 blast)
  have hx\<^sub>23: "x\<^sub>2 \<noteq> x\<^sub>3"
    using hx\<^sub>2_edge_sphere hx\<^sub>3_edge_sphere he\<^sub>23_punctured_disj by (by100 blast)
  have hx\<^sub>1_not_e\<^sub>2: "x\<^sub>1 \<notin> e\<^sub>2"
    using hx\<^sub>1_edge_sphere he\<^sub>12_punctured_disj by (by100 blast)
  have hx\<^sub>1_not_e\<^sub>3: "x\<^sub>1 \<notin> e\<^sub>3"
    using hx\<^sub>1_edge_sphere he\<^sub>13_punctured_disj by (by100 blast)
  have hx\<^sub>2_not_e\<^sub>1: "x\<^sub>2 \<notin> e\<^sub>1"
    using hx\<^sub>2_edge_sphere he\<^sub>12_punctured_disj by (by100 blast)
  have hx\<^sub>2_not_e\<^sub>3: "x\<^sub>2 \<notin> e\<^sub>3"
    using hx\<^sub>2_edge_sphere he\<^sub>23_punctured_disj by (by100 blast)
  have hx\<^sub>3_not_e\<^sub>1: "x\<^sub>3 \<notin> e\<^sub>1"
    using hx\<^sub>3_edge_sphere he\<^sub>13_punctured_disj by (by100 blast)
  have hx\<^sub>3_not_e\<^sub>2: "x\<^sub>3 \<notin> e\<^sub>2"
    using hx\<^sub>3_edge_sphere he\<^sub>23_punctured_disj by (by100 blast)
  have hx\<^sub>1_punctured_poly: "x\<^sub>1 \<in> geotop_polyhedron L - {w}"
    using hx\<^sub>1_edge_sphere he\<^sub>1_punctured_sub by (by100 blast)
  have hx\<^sub>2_punctured_poly: "x\<^sub>2 \<in> geotop_polyhedron L - {w}"
    using hx\<^sub>2_edge_sphere he\<^sub>2_punctured_sub by (by100 blast)
  have hx\<^sub>3_punctured_poly: "x\<^sub>3 \<in> geotop_polyhedron L - {w}"
    using hx\<^sub>3_edge_sphere he\<^sub>3_punctured_sub by (by100 blast)
  have hx_card3: "card {x\<^sub>1, x\<^sub>2, x\<^sub>3} = 3"
    using hx\<^sub>12 hx\<^sub>13 hx\<^sub>23 by (by100 simp)
  have hradial_sector_bound:
      "\<forall>C \<in> components (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3)).
        card {S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}.
                (S - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}} \<le> 2"
  proof -
    have hr_le_q\<^sub>1: "r \<le> dist w q\<^sub>1"
      using hr_lt_q\<^sub>1 by (by100 linarith)
    have hr_le_q\<^sub>2: "r \<le> dist w q\<^sub>2"
      using hr_lt_q\<^sub>2 by (by100 linarith)
    have hr_le_q\<^sub>3: "r \<le> dist w q\<^sub>3"
      using hr_lt_q\<^sub>3 by (by100 linarith)
    have h12_empty:
        "(closed_segment w q\<^sub>1 - {w}) \<inter> (closed_segment w q\<^sub>2 - {w}) \<inter> ball w r = {}"
      using he\<^sub>12_punctured_disj he\<^sub>1_seg he\<^sub>2_seg by (by100 blast)
    have h13_empty:
        "(closed_segment w q\<^sub>1 - {w}) \<inter> (closed_segment w q\<^sub>3 - {w}) \<inter> ball w r = {}"
      using he\<^sub>13_punctured_disj he\<^sub>1_seg he\<^sub>3_seg by (by100 blast)
    have h23_empty:
        "(closed_segment w q\<^sub>2 - {w}) \<inter> (closed_segment w q\<^sub>3 - {w}) \<inter> ball w r = {}"
      using he\<^sub>23_punctured_disj he\<^sub>2_seg he\<^sub>3_seg by (by100 blast)
    have hbound:
        "\<forall>C \<in> components
          (ball w r -
            (closed_segment w q\<^sub>1 \<union> closed_segment w q\<^sub>2 \<union> closed_segment w q\<^sub>3)).
          card {S \<in> {closed_segment w q\<^sub>1, closed_segment w q\<^sub>2, closed_segment w q\<^sub>3}.
                  (S - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}} \<le> 2"
      by (rule geotop_three_radial_segments_sector_bound_prefix
          [OF hr_pos hq\<^sub>1w hq\<^sub>2w hq\<^sub>3w
              hr_le_q\<^sub>1 hr_le_q\<^sub>2 hr_le_q\<^sub>3
              h12_empty h13_empty h23_empty])
    show ?thesis
      using hbound he\<^sub>1_seg he\<^sub>2_seg he\<^sub>3_seg by (by100 simp)
  qed
  have hlocal_components_fin:
      "finite (components (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3)))"
  proof -
    have hr_le_q\<^sub>1: "r \<le> dist w q\<^sub>1"
      using hr_lt_q\<^sub>1 by (by100 linarith)
    have hr_le_q\<^sub>2: "r \<le> dist w q\<^sub>2"
      using hr_lt_q\<^sub>2 by (by100 linarith)
    have hr_le_q\<^sub>3: "r \<le> dist w q\<^sub>3"
      using hr_lt_q\<^sub>3 by (by100 linarith)
    have h12_empty:
        "(closed_segment w q\<^sub>1 - {w}) \<inter> (closed_segment w q\<^sub>2 - {w}) \<inter> ball w r = {}"
      using he\<^sub>12_punctured_disj he\<^sub>1_seg he\<^sub>2_seg by (by100 blast)
    have h13_empty:
        "(closed_segment w q\<^sub>1 - {w}) \<inter> (closed_segment w q\<^sub>3 - {w}) \<inter> ball w r = {}"
      using he\<^sub>13_punctured_disj he\<^sub>1_seg he\<^sub>3_seg by (by100 blast)
    have h23_empty:
        "(closed_segment w q\<^sub>2 - {w}) \<inter> (closed_segment w q\<^sub>3 - {w}) \<inter> ball w r = {}"
      using he\<^sub>23_punctured_disj he\<^sub>2_seg he\<^sub>3_seg by (by100 blast)
    have hfin:
        "finite (components
          (ball w r -
            (closed_segment w q\<^sub>1 \<union> closed_segment w q\<^sub>2 \<union> closed_segment w q\<^sub>3)))"
      by (rule geotop_finite_components_three_radial_segments_ball_prefix
          [OF hr_pos hq\<^sub>1w hq\<^sub>2w hq\<^sub>3w
              hr_le_q\<^sub>1 hr_le_q\<^sub>2 hr_le_q\<^sub>3
              h12_empty h13_empty h23_empty])
    show ?thesis
      using hfin he\<^sub>1_seg he\<^sub>2_seg he\<^sub>3_seg by (by100 simp)
  qed
  have hcircle_components_fin:
      "finite (components (sphere w r - {x\<^sub>1, x\<^sub>2, x\<^sub>3}))"
  proof -
    have hx\<^sub>1_sphere: "x\<^sub>1 \<in> sphere w r"
      using hx\<^sub>1_edge_sphere by (by100 blast)
    have hx\<^sub>2_sphere: "x\<^sub>2 \<in> sphere w r"
      using hx\<^sub>2_edge_sphere by (by100 blast)
    have hx\<^sub>3_sphere: "x\<^sub>3 \<in> sphere w r"
      using hx\<^sub>3_edge_sphere by (by100 blast)
    show ?thesis
      by (rule geotop_finite_components_punctured_circle_three_points_prefix
          [OF hr_pos hx\<^sub>1_sphere hx\<^sub>2_sphere hx\<^sub>3_sphere hx\<^sub>12 hx\<^sub>13 hx\<^sub>23])
  qed
  have hcircle_component_closure_bound:
      "\<And>K. K \<in> components (sphere w r - {x\<^sub>1, x\<^sub>2, x\<^sub>3})
        \<Longrightarrow> card ({x\<^sub>1, x\<^sub>2, x\<^sub>3} \<inter> closure K) \<le> 2"
  proof -
    fix K
    assume hK: "K \<in> components (sphere w r - {x\<^sub>1, x\<^sub>2, x\<^sub>3})"
    have hx\<^sub>1_sphere: "x\<^sub>1 \<in> sphere w r"
      using hx\<^sub>1_edge_sphere by (by100 blast)
    have hx\<^sub>2_sphere: "x\<^sub>2 \<in> sphere w r"
      using hx\<^sub>2_edge_sphere by (by100 blast)
    have hx\<^sub>3_sphere: "x\<^sub>3 \<in> sphere w r"
      using hx\<^sub>3_edge_sphere by (by100 blast)
    show "card ({x\<^sub>1, x\<^sub>2, x\<^sub>3} \<inter> closure K) \<le> 2"
      by (rule geotop_punctured_circle_component_closure_three_points_bound_prefix
          [OF hr_pos hx\<^sub>1_sphere hx\<^sub>2_sphere hx\<^sub>3_sphere hx\<^sub>12 hx\<^sub>13 hx\<^sub>23 hK])
  qed
  obtain A\<^sub>1 A\<^sub>2 where hA_decomp: "geotop_polyhedron L = A\<^sub>1 \<union> A\<^sub>2"
      and hA_inter: "A\<^sub>1 \<inter> A\<^sub>2 = {w, q\<^sub>1}"
      and hA\<^sub>1_arc: "top1_is_arc_on A\<^sub>1
        (subspace_topology UNIV geotop_euclidean_topology A\<^sub>1)"
      and hA\<^sub>2_arc: "top1_is_arc_on A\<^sub>2
        (subspace_topology UNIV geotop_euclidean_topology A\<^sub>2)"
  proof -
    have hw_poly: "w \<in> geotop_polyhedron L"
      using hwL unfolding geotop_polyhedron_def by (by100 blast)
    have hq\<^sub>1_poly: "q\<^sub>1 \<in> geotop_polyhedron L"
      using hq\<^sub>1_punctured by (by100 blast)
    have hwq\<^sub>1: "w \<noteq> q\<^sub>1"
      using hq\<^sub>1w by (by100 simp)
    have hSCC_split:
        "\<exists>A\<^sub>1 A\<^sub>2. geotop_polyhedron L = A\<^sub>1 \<union> A\<^sub>2
          \<and> A\<^sub>1 \<inter> A\<^sub>2 = {w, q\<^sub>1}
          \<and> top1_is_arc_on A\<^sub>1
            (subspace_topology UNIV geotop_euclidean_topology A\<^sub>1)
          \<and> top1_is_arc_on A\<^sub>2
            (subspace_topology UNIV geotop_euclidean_topology A\<^sub>2)"
      by (rule SCC_decompose_at_given_points
          [OF geotop_euclidean_topology_UNIV_strict
              geotop_euclidean_topology_UNIV_hausdorff hSCC
              hw_poly hq\<^sub>1_poly hwq\<^sub>1])
    obtain A\<^sub>1 A\<^sub>2 where hdecomp: "geotop_polyhedron L = A\<^sub>1 \<union> A\<^sub>2"
        and hinter: "A\<^sub>1 \<inter> A\<^sub>2 = {w, q\<^sub>1}"
        and hA\<^sub>1: "top1_is_arc_on A\<^sub>1
          (subspace_topology UNIV geotop_euclidean_topology A\<^sub>1)"
        and hA\<^sub>2: "top1_is_arc_on A\<^sub>2
          (subspace_topology UNIV geotop_euclidean_topology A\<^sub>2)"
      using hSCC_split
      by (by100 blast)
    show ?thesis
      by (rule that[OF hdecomp hinter hA\<^sub>1 hA\<^sub>2])
  qed
  have hA\<^sub>1_ep:
      "top1_arc_endpoints_on A\<^sub>1
        (subspace_topology UNIV geotop_euclidean_topology A\<^sub>1) = {w, q\<^sub>1}"
  proof (rule scc_decomp_arc_endpoints(1)
      [OF geotop_euclidean_topology_UNIV_strict
          geotop_euclidean_topology_UNIV_hausdorff hSCC
          hA\<^sub>1_arc hA\<^sub>2_arc _ _ hA_decomp hA_inter])
    show "A\<^sub>1 \<subseteq> UNIV"
      by (by100 simp)
    show "A\<^sub>2 \<subseteq> UNIV"
      by (by100 simp)
    show "w \<noteq> q\<^sub>1"
      using hq\<^sub>1w by (by100 simp)
  qed
  have hA\<^sub>2_ep:
      "top1_arc_endpoints_on A\<^sub>2
        (subspace_topology UNIV geotop_euclidean_topology A\<^sub>2) = {w, q\<^sub>1}"
  proof (rule scc_decomp_arc_endpoints(2)
      [OF geotop_euclidean_topology_UNIV_strict
          geotop_euclidean_topology_UNIV_hausdorff hSCC
          hA\<^sub>1_arc hA\<^sub>2_arc _ _ hA_decomp hA_inter])
    show "A\<^sub>1 \<subseteq> UNIV"
      by (by100 simp)
    show "A\<^sub>2 \<subseteq> UNIV"
      by (by100 simp)
    show "w \<noteq> q\<^sub>1"
      using hq\<^sub>1w by (by100 simp)
  qed
  have hw_A\<^sub>1: "w \<in> A\<^sub>1"
    using hA_inter by (by100 blast)
  have hw_A\<^sub>2: "w \<in> A\<^sub>2"
    using hA_inter by (by100 blast)
  have hq\<^sub>1_A\<^sub>1: "q\<^sub>1 \<in> A\<^sub>1"
    using hA_inter by (by100 blast)
  have hq\<^sub>1_A\<^sub>2: "q\<^sub>1 \<in> A\<^sub>2"
    using hA_inter by (by100 blast)
  have hA\<^sub>1_geotop_arc: "geotop_arc_endpoints A\<^sub>1 {w, q\<^sub>1}"
  proof (rule geotop_top1_arc_endpoints_imp_geotop_arc_endpoints_prefix
      [OF hA\<^sub>1_arc hA\<^sub>1_ep])
    show "w \<noteq> q\<^sub>1"
      using hq\<^sub>1w by (by100 simp)
  qed
  have hA\<^sub>2_geotop_arc: "geotop_arc_endpoints A\<^sub>2 {w, q\<^sub>1}"
  proof (rule geotop_top1_arc_endpoints_imp_geotop_arc_endpoints_prefix
      [OF hA\<^sub>2_arc hA\<^sub>2_ep])
    show "w \<noteq> q\<^sub>1"
      using hq\<^sub>1w by (by100 simp)
  qed
  have hA\<^sub>1_minus_w_connected:
      "top1_connected_on (A\<^sub>1 - {w})
        (subspace_topology UNIV geotop_euclidean_topology (A\<^sub>1 - {w}))"
  proof -
    have hw_ep: "w \<in> top1_arc_endpoints_on A\<^sub>1
        (subspace_topology UNIV geotop_euclidean_topology A\<^sub>1)"
      using hA\<^sub>1_ep by (by100 simp)
    have hconn_A\<^sub>1:
        "top1_connected_on (A\<^sub>1 - {w})
          (subspace_topology A\<^sub>1
            (subspace_topology UNIV geotop_euclidean_topology A\<^sub>1)
            (A\<^sub>1 - {w}))"
      using hw_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
    have hsub:
        "subspace_topology A\<^sub>1
          (subspace_topology UNIV geotop_euclidean_topology A\<^sub>1)
          (A\<^sub>1 - {w})
        = subspace_topology UNIV geotop_euclidean_topology (A\<^sub>1 - {w})"
      by (rule subspace_topology_trans[OF Diff_subset])
    show ?thesis
      using hconn_A\<^sub>1 hsub by (by100 simp)
  qed
  have hA\<^sub>2_minus_w_connected:
      "top1_connected_on (A\<^sub>2 - {w})
        (subspace_topology UNIV geotop_euclidean_topology (A\<^sub>2 - {w}))"
  proof -
    have hw_ep: "w \<in> top1_arc_endpoints_on A\<^sub>2
        (subspace_topology UNIV geotop_euclidean_topology A\<^sub>2)"
      using hA\<^sub>2_ep by (by100 simp)
    have hconn_A\<^sub>2:
        "top1_connected_on (A\<^sub>2 - {w})
          (subspace_topology A\<^sub>2
            (subspace_topology UNIV geotop_euclidean_topology A\<^sub>2)
            (A\<^sub>2 - {w}))"
      using hw_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
    have hsub:
        "subspace_topology A\<^sub>2
          (subspace_topology UNIV geotop_euclidean_topology A\<^sub>2)
          (A\<^sub>2 - {w})
        = subspace_topology UNIV geotop_euclidean_topology (A\<^sub>2 - {w})"
      by (rule subspace_topology_trans[OF Diff_subset])
    show ?thesis
      using hconn_A\<^sub>2 hsub by (by100 simp)
  qed
  have hpunctured_carrier_arc_decomp:
      "geotop_polyhedron L - {w} = (A\<^sub>1 - {w}) \<union> (A\<^sub>2 - {w})"
    using hA_decomp by (by100 blast)
  have hpunctured_arc_overlap:
      "(A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w}) = {q\<^sub>1}"
  proof
    show "(A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w}) \<subseteq> {q\<^sub>1}"
    proof
      fix y
      assume hy: "y \<in> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w})"
      have hy_inter: "y \<in> A\<^sub>1 \<inter> A\<^sub>2"
        using hy by (by100 blast)
      have hy_cases: "y = w \<or> y = q\<^sub>1"
        using hy_inter hA_inter by (by100 blast)
      have hy_ne_w: "y \<noteq> w"
        using hy by (by100 blast)
      show "y \<in> {q\<^sub>1}"
        using hy_cases hy_ne_w by (by100 blast)
    qed
    show "{q\<^sub>1} \<subseteq> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w})"
    proof
      fix y
      assume hy: "y \<in> {q\<^sub>1}"
      have hyq: "y = q\<^sub>1"
        using hy by (by100 simp)
      have hqA: "q\<^sub>1 \<in> A\<^sub>1 \<inter> A\<^sub>2"
        using hA_inter by (by100 blast)
      show "y \<in> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w})"
        using hyq hqA hq\<^sub>1w by (by100 blast)
    qed
  qed
  have hx\<^sub>1_arc_side: "x\<^sub>1 \<in> A\<^sub>1 - {w} \<or> x\<^sub>1 \<in> A\<^sub>2 - {w}"
    using hx\<^sub>1_punctured_poly hpunctured_carrier_arc_decomp by (by100 blast)
  have hx\<^sub>2_arc_side: "x\<^sub>2 \<in> A\<^sub>1 - {w} \<or> x\<^sub>2 \<in> A\<^sub>2 - {w}"
    using hx\<^sub>2_punctured_poly hpunctured_carrier_arc_decomp by (by100 blast)
  have hx\<^sub>3_arc_side: "x\<^sub>3 \<in> A\<^sub>1 - {w} \<or> x\<^sub>3 \<in> A\<^sub>2 - {w}"
    using hx\<^sub>3_punctured_poly hpunctured_carrier_arc_decomp by (by100 blast)
  have hq\<^sub>1_in_e\<^sub>1: "q\<^sub>1 \<in> e\<^sub>1"
    using he\<^sub>1_seg by (by100 simp)
  have hq\<^sub>1_not_e\<^sub>2: "q\<^sub>1 \<notin> e\<^sub>2"
    using hq\<^sub>1_in_e\<^sub>1 he\<^sub>12_inter hq\<^sub>1w by (by100 blast)
  have hq\<^sub>1_not_e\<^sub>3: "q\<^sub>1 \<notin> e\<^sub>3"
    using hq\<^sub>1_in_e\<^sub>1 he\<^sub>13_inter hq\<^sub>1w by (by100 blast)
  have he\<^sub>1_punctured_arc_overlap_only_q\<^sub>1:
      "(e\<^sub>1 - {w, q\<^sub>1}) \<inter> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w}) = {}"
  proof
    show "(e\<^sub>1 - {w, q\<^sub>1}) \<inter> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w}) \<subseteq> {}"
    proof
      fix y
      assume hy: "y \<in> (e\<^sub>1 - {w, q\<^sub>1}) \<inter> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w})"
      have hy_overlap: "y \<in> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w})"
        using hy by (by100 blast)
      hence hyq: "y = q\<^sub>1"
        using hpunctured_arc_overlap by (by100 blast)
      show "y \<in> {}"
        using hy hyq by (by100 blast)
    qed
    show "{} \<subseteq> (e\<^sub>1 - {w, q\<^sub>1}) \<inter> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w})"
      by (by100 simp)
  qed
  have he\<^sub>2_punctured_arc_overlap_empty:
      "(e\<^sub>2 - {w}) \<inter> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w}) = {}"
  proof
    show "(e\<^sub>2 - {w}) \<inter> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w}) \<subseteq> {}"
    proof
      fix y
      assume hy: "y \<in> (e\<^sub>2 - {w}) \<inter> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w})"
      have hy_overlap: "y \<in> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w})"
        using hy by (by100 blast)
      hence hyq: "y = q\<^sub>1"
        using hpunctured_arc_overlap by (by100 blast)
      have "y \<in> e\<^sub>2"
        using hy by (by100 blast)
      thus "y \<in> {}"
        using hyq hq\<^sub>1_not_e\<^sub>2 by (by100 blast)
    qed
    show "{} \<subseteq> (e\<^sub>2 - {w}) \<inter> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w})"
      by (by100 simp)
  qed
  have he\<^sub>3_punctured_arc_overlap_empty:
      "(e\<^sub>3 - {w}) \<inter> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w}) = {}"
  proof
    show "(e\<^sub>3 - {w}) \<inter> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w}) \<subseteq> {}"
    proof
      fix y
      assume hy: "y \<in> (e\<^sub>3 - {w}) \<inter> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w})"
      have hy_overlap: "y \<in> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w})"
        using hy by (by100 blast)
      hence hyq: "y = q\<^sub>1"
        using hpunctured_arc_overlap by (by100 blast)
      have "y \<in> e\<^sub>3"
        using hy by (by100 blast)
      thus "y \<in> {}"
        using hyq hq\<^sub>1_not_e\<^sub>3 by (by100 blast)
    qed
    show "{} \<subseteq> (e\<^sub>3 - {w}) \<inter> (A\<^sub>1 - {w}) \<inter> (A\<^sub>2 - {w})"
      by (by100 simp)
  qed
  have hx\<^sub>1_ne_q\<^sub>1: "x\<^sub>1 \<noteq> q\<^sub>1"
  proof
    assume hx_eq: "x\<^sub>1 = q\<^sub>1"
    have "dist w q\<^sub>1 = r"
      using hx\<^sub>1_edge_sphere hx_eq by (by100 simp)
    then show False
      using hr_lt_q\<^sub>1 by (by100 linarith)
  qed
  have hx\<^sub>2_ne_q\<^sub>1: "x\<^sub>2 \<noteq> q\<^sub>1"
    using hx\<^sub>2_edge_sphere hq\<^sub>1_not_e\<^sub>2 by (by100 blast)
  have hx\<^sub>3_ne_q\<^sub>1: "x\<^sub>3 \<noteq> q\<^sub>1"
    using hx\<^sub>3_edge_sphere hq\<^sub>1_not_e\<^sub>3 by (by100 blast)
  have hx\<^sub>1_arc_side_unique:
      "\<not> (x\<^sub>1 \<in> A\<^sub>1 - {w} \<and> x\<^sub>1 \<in> A\<^sub>2 - {w})"
  proof
    assume hboth: "x\<^sub>1 \<in> A\<^sub>1 - {w} \<and> x\<^sub>1 \<in> A\<^sub>2 - {w}"
    have hx_inter: "x\<^sub>1 \<in> A\<^sub>1 \<inter> A\<^sub>2"
      using hboth by (by100 blast)
    have hx_cases: "x\<^sub>1 = w \<or> x\<^sub>1 = q\<^sub>1"
      using hx_inter hA_inter by (by100 blast)
    have "x\<^sub>1 \<noteq> w"
      using hx\<^sub>1_edge_sphere by (by100 blast)
    then show False
      using hx_cases hx\<^sub>1_ne_q\<^sub>1 by (by100 blast)
  qed
  have hx\<^sub>2_arc_side_unique:
      "\<not> (x\<^sub>2 \<in> A\<^sub>1 - {w} \<and> x\<^sub>2 \<in> A\<^sub>2 - {w})"
  proof
    assume hboth: "x\<^sub>2 \<in> A\<^sub>1 - {w} \<and> x\<^sub>2 \<in> A\<^sub>2 - {w}"
    have hx_inter: "x\<^sub>2 \<in> A\<^sub>1 \<inter> A\<^sub>2"
      using hboth by (by100 blast)
    have hx_cases: "x\<^sub>2 = w \<or> x\<^sub>2 = q\<^sub>1"
      using hx_inter hA_inter by (by100 blast)
    have "x\<^sub>2 \<noteq> w"
      using hx\<^sub>2_edge_sphere by (by100 blast)
    then show False
      using hx_cases hx\<^sub>2_ne_q\<^sub>1 by (by100 blast)
  qed
  have hx\<^sub>3_arc_side_unique:
      "\<not> (x\<^sub>3 \<in> A\<^sub>1 - {w} \<and> x\<^sub>3 \<in> A\<^sub>2 - {w})"
  proof
    assume hboth: "x\<^sub>3 \<in> A\<^sub>1 - {w} \<and> x\<^sub>3 \<in> A\<^sub>2 - {w}"
    have hx_inter: "x\<^sub>3 \<in> A\<^sub>1 \<inter> A\<^sub>2"
      using hboth by (by100 blast)
    have hx_cases: "x\<^sub>3 = w \<or> x\<^sub>3 = q\<^sub>1"
      using hx_inter hA_inter by (by100 blast)
    have "x\<^sub>3 \<noteq> w"
      using hx\<^sub>3_edge_sphere by (by100 blast)
    then show False
      using hx_cases hx\<^sub>3_ne_q\<^sub>1 by (by100 blast)
  qed
  have hx\<^sub>1_arc_side_exclusive:
      "(x\<^sub>1 \<in> A\<^sub>1 - {w} \<and> x\<^sub>1 \<notin> A\<^sub>2 - {w})
      \<or> (x\<^sub>1 \<in> A\<^sub>2 - {w} \<and> x\<^sub>1 \<notin> A\<^sub>1 - {w})"
    using hx\<^sub>1_arc_side hx\<^sub>1_arc_side_unique by (by100 blast)
  have hx\<^sub>2_arc_side_exclusive:
      "(x\<^sub>2 \<in> A\<^sub>1 - {w} \<and> x\<^sub>2 \<notin> A\<^sub>2 - {w})
      \<or> (x\<^sub>2 \<in> A\<^sub>2 - {w} \<and> x\<^sub>2 \<notin> A\<^sub>1 - {w})"
    using hx\<^sub>2_arc_side hx\<^sub>2_arc_side_unique by (by100 blast)
  have hx\<^sub>3_arc_side_exclusive:
      "(x\<^sub>3 \<in> A\<^sub>1 - {w} \<and> x\<^sub>3 \<notin> A\<^sub>2 - {w})
      \<or> (x\<^sub>3 \<in> A\<^sub>2 - {w} \<and> x\<^sub>3 \<notin> A\<^sub>1 - {w})"
    using hx\<^sub>3_arc_side hx\<^sub>3_arc_side_unique by (by100 blast)
  have htwo_witnesses_same_arc_side:
      "(x\<^sub>1 \<in> A\<^sub>1 - {w} \<and> x\<^sub>2 \<in> A\<^sub>1 - {w})
      \<or> (x\<^sub>1 \<in> A\<^sub>1 - {w} \<and> x\<^sub>3 \<in> A\<^sub>1 - {w})
      \<or> (x\<^sub>2 \<in> A\<^sub>1 - {w} \<and> x\<^sub>3 \<in> A\<^sub>1 - {w})
      \<or> (x\<^sub>1 \<in> A\<^sub>2 - {w} \<and> x\<^sub>2 \<in> A\<^sub>2 - {w})
      \<or> (x\<^sub>1 \<in> A\<^sub>2 - {w} \<and> x\<^sub>3 \<in> A\<^sub>2 - {w})
      \<or> (x\<^sub>2 \<in> A\<^sub>2 - {w} \<and> x\<^sub>3 \<in> A\<^sub>2 - {w})"
  proof (cases "x\<^sub>1 \<in> A\<^sub>1 - {w}")
    case True
    show ?thesis
    proof (cases "x\<^sub>2 \<in> A\<^sub>1 - {w}")
      case True
      then show ?thesis
        using \<open>x\<^sub>1 \<in> A\<^sub>1 - {w}\<close> by (by100 blast)
    next
      case False
      have hx\<^sub>2A\<^sub>2: "x\<^sub>2 \<in> A\<^sub>2 - {w}"
        using hx\<^sub>2_arc_side False by (by100 blast)
      show ?thesis
      proof (cases "x\<^sub>3 \<in> A\<^sub>1 - {w}")
        case True
        then show ?thesis
          using \<open>x\<^sub>1 \<in> A\<^sub>1 - {w}\<close> by (by100 blast)
      next
        case False
        have "x\<^sub>3 \<in> A\<^sub>2 - {w}"
          using hx\<^sub>3_arc_side False by (by100 blast)
        then show ?thesis
          using hx\<^sub>2A\<^sub>2 by (by100 blast)
      qed
    qed
  next
    case False
    have hx\<^sub>1A\<^sub>2: "x\<^sub>1 \<in> A\<^sub>2 - {w}"
      using hx\<^sub>1_arc_side False by (by100 blast)
    show ?thesis
    proof (cases "x\<^sub>2 \<in> A\<^sub>2 - {w}")
      case True
      then show ?thesis
        using hx\<^sub>1A\<^sub>2 by (by100 blast)
    next
      case False
      have hx\<^sub>2A\<^sub>1: "x\<^sub>2 \<in> A\<^sub>1 - {w}"
        using hx\<^sub>2_arc_side False by (by100 blast)
      show ?thesis
      proof (cases "x\<^sub>3 \<in> A\<^sub>1 - {w}")
        case True
        then show ?thesis
          using hx\<^sub>2A\<^sub>1 by (by100 blast)
      next
        case False
        have "x\<^sub>3 \<in> A\<^sub>2 - {w}"
          using hx\<^sub>3_arc_side False by (by100 blast)
        then show ?thesis
          using hx\<^sub>1A\<^sub>2 by (by100 blast)
      qed
    qed
  qed
  have htwo_selected_edges_same_arc_side:
      "\<exists>S T. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> (((S - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {}
              \<and> (T - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {})
            \<or> ((S - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}
              \<and> (T - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}))"
  proof -
    let ?same_edges =
      "\<exists>S T. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> (((S - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {}
              \<and> (T - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {})
            \<or> ((S - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}
              \<and> (T - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}))"
    have hx\<^sub>1e\<^sub>1: "x\<^sub>1 \<in> e\<^sub>1 - {w}"
      using hx\<^sub>1_edge_sphere by (by100 blast)
    have hx\<^sub>2e\<^sub>2: "x\<^sub>2 \<in> e\<^sub>2 - {w}"
      using hx\<^sub>2_edge_sphere by (by100 blast)
    have hx\<^sub>3e\<^sub>3: "x\<^sub>3 \<in> e\<^sub>3 - {w}"
      using hx\<^sub>3_edge_sphere by (by100 blast)
    have hpair_A\<^sub>1:
        "\<And>x y S T. x \<in> S - {w} \<Longrightarrow> y \<in> T - {w}
          \<Longrightarrow> x \<in> A\<^sub>1 - {w} \<Longrightarrow> y \<in> A\<^sub>1 - {w}
          \<Longrightarrow> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3} \<Longrightarrow> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<Longrightarrow> S \<noteq> T \<Longrightarrow> ?same_edges"
    proof -
      fix x y S T
      assume hxS: "x \<in> S - {w}"
      assume hyT: "y \<in> T - {w}"
      assume hxA: "x \<in> A\<^sub>1 - {w}"
      assume hyA: "y \<in> A\<^sub>1 - {w}"
      assume hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      assume hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      assume hST: "S \<noteq> T"
      have hSmeet: "(S - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {}"
        using hxS hxA by (by100 blast)
      have hTmeet: "(T - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {}"
        using hyT hyA by (by100 blast)
      have hside: "((S - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {}
          \<and> (T - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {})
        \<or> ((S - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}
          \<and> (T - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {})"
        using hSmeet hTmeet by (by100 blast)
      have hbody:
          "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> S \<noteq> T
          \<and> (((S - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {}
              \<and> (T - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {})
            \<or> ((S - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}
              \<and> (T - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}))"
        using hS hT hST hside by (by100 blast)
      show ?same_edges
      proof (rule exI[where x=S])
        show "\<exists>T. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> S \<noteq> T
          \<and> (((S - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {}
              \<and> (T - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {})
            \<or> ((S - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}
              \<and> (T - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}))"
        proof (rule exI[where x=T])
          show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> S \<noteq> T
            \<and> (((S - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {}
                \<and> (T - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {})
              \<or> ((S - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}
                \<and> (T - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}))"
            by (rule hbody)
        qed
      qed
    qed
    have hpair_A\<^sub>2:
        "\<And>x y S T. x \<in> S - {w} \<Longrightarrow> y \<in> T - {w}
          \<Longrightarrow> x \<in> A\<^sub>2 - {w} \<Longrightarrow> y \<in> A\<^sub>2 - {w}
          \<Longrightarrow> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3} \<Longrightarrow> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<Longrightarrow> S \<noteq> T \<Longrightarrow> ?same_edges"
    proof -
      fix x y S T
      assume hxS: "x \<in> S - {w}"
      assume hyT: "y \<in> T - {w}"
      assume hxA: "x \<in> A\<^sub>2 - {w}"
      assume hyA: "y \<in> A\<^sub>2 - {w}"
      assume hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      assume hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      assume hST: "S \<noteq> T"
      have hSmeet: "(S - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}"
        using hxS hxA by (by100 blast)
      have hTmeet: "(T - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}"
        using hyT hyA by (by100 blast)
      have hside: "((S - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {}
          \<and> (T - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {})
        \<or> ((S - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}
          \<and> (T - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {})"
        using hSmeet hTmeet by (by100 blast)
      have hbody:
          "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> S \<noteq> T
          \<and> (((S - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {}
              \<and> (T - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {})
            \<or> ((S - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}
              \<and> (T - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}))"
        using hS hT hST hside by (by100 blast)
      show ?same_edges
      proof (rule exI[where x=S])
        show "\<exists>T. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> S \<noteq> T
          \<and> (((S - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {}
              \<and> (T - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {})
            \<or> ((S - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}
              \<and> (T - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}))"
        proof (rule exI[where x=T])
          show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> S \<noteq> T
            \<and> (((S - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {}
                \<and> (T - {w}) \<inter> (A\<^sub>1 - {w}) \<noteq> {})
              \<or> ((S - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}
                \<and> (T - {w}) \<inter> (A\<^sub>2 - {w}) \<noteq> {}))"
            by (rule hbody)
        qed
      qed
    qed
    show ?thesis
      using htwo_witnesses_same_arc_side
    proof (elim disjE)
      assume hside: "x\<^sub>1 \<in> A\<^sub>1 - {w} \<and> x\<^sub>2 \<in> A\<^sub>1 - {w}"
      show ?thesis
      proof (rule hpair_A\<^sub>1[where x=x\<^sub>1 and y=x\<^sub>2 and S=e\<^sub>1 and T=e\<^sub>2])
        show "x\<^sub>1 \<in> e\<^sub>1 - {w}" by (rule hx\<^sub>1e\<^sub>1)
        show "x\<^sub>2 \<in> e\<^sub>2 - {w}" by (rule hx\<^sub>2e\<^sub>2)
        show "x\<^sub>1 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
        show "x\<^sub>2 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
        show "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>1 \<noteq> e\<^sub>2" by (rule he\<^sub>12)
      qed
    next
      assume hside: "x\<^sub>1 \<in> A\<^sub>1 - {w} \<and> x\<^sub>3 \<in> A\<^sub>1 - {w}"
      show ?thesis
      proof (rule hpair_A\<^sub>1[where x=x\<^sub>1 and y=x\<^sub>3 and S=e\<^sub>1 and T=e\<^sub>3])
        show "x\<^sub>1 \<in> e\<^sub>1 - {w}" by (rule hx\<^sub>1e\<^sub>1)
        show "x\<^sub>3 \<in> e\<^sub>3 - {w}" by (rule hx\<^sub>3e\<^sub>3)
        show "x\<^sub>1 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
        show "x\<^sub>3 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
        show "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>1 \<noteq> e\<^sub>3" by (rule he\<^sub>13)
      qed
    next
      assume hside: "x\<^sub>2 \<in> A\<^sub>1 - {w} \<and> x\<^sub>3 \<in> A\<^sub>1 - {w}"
      show ?thesis
      proof (rule hpair_A\<^sub>1[where x=x\<^sub>2 and y=x\<^sub>3 and S=e\<^sub>2 and T=e\<^sub>3])
        show "x\<^sub>2 \<in> e\<^sub>2 - {w}" by (rule hx\<^sub>2e\<^sub>2)
        show "x\<^sub>3 \<in> e\<^sub>3 - {w}" by (rule hx\<^sub>3e\<^sub>3)
        show "x\<^sub>2 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
        show "x\<^sub>3 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
        show "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>2 \<noteq> e\<^sub>3" by (rule he\<^sub>23)
      qed
    next
      assume hside: "x\<^sub>1 \<in> A\<^sub>2 - {w} \<and> x\<^sub>2 \<in> A\<^sub>2 - {w}"
      show ?thesis
      proof (rule hpair_A\<^sub>2[where x=x\<^sub>1 and y=x\<^sub>2 and S=e\<^sub>1 and T=e\<^sub>2])
        show "x\<^sub>1 \<in> e\<^sub>1 - {w}" by (rule hx\<^sub>1e\<^sub>1)
        show "x\<^sub>2 \<in> e\<^sub>2 - {w}" by (rule hx\<^sub>2e\<^sub>2)
        show "x\<^sub>1 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
        show "x\<^sub>2 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
        show "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>1 \<noteq> e\<^sub>2" by (rule he\<^sub>12)
      qed
    next
      assume hside: "x\<^sub>1 \<in> A\<^sub>2 - {w} \<and> x\<^sub>3 \<in> A\<^sub>2 - {w}"
      show ?thesis
      proof (rule hpair_A\<^sub>2[where x=x\<^sub>1 and y=x\<^sub>3 and S=e\<^sub>1 and T=e\<^sub>3])
        show "x\<^sub>1 \<in> e\<^sub>1 - {w}" by (rule hx\<^sub>1e\<^sub>1)
        show "x\<^sub>3 \<in> e\<^sub>3 - {w}" by (rule hx\<^sub>3e\<^sub>3)
        show "x\<^sub>1 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
        show "x\<^sub>3 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
        show "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>1 \<noteq> e\<^sub>3" by (rule he\<^sub>13)
      qed
    next
      assume hside: "x\<^sub>2 \<in> A\<^sub>2 - {w} \<and> x\<^sub>3 \<in> A\<^sub>2 - {w}"
      show ?thesis
      proof (rule hpair_A\<^sub>2[where x=x\<^sub>2 and y=x\<^sub>3 and S=e\<^sub>2 and T=e\<^sub>3])
        show "x\<^sub>2 \<in> e\<^sub>2 - {w}" by (rule hx\<^sub>2e\<^sub>2)
        show "x\<^sub>3 \<in> e\<^sub>3 - {w}" by (rule hx\<^sub>3e\<^sub>3)
        show "x\<^sub>2 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
        show "x\<^sub>3 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
        show "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>2 \<noteq> e\<^sub>3" by (rule he\<^sub>23)
      qed
    qed
  qed
  have htwo_selected_punctured_germs_same_arc_side:
      "\<exists>S T C x y. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> x \<in> S - {w, q\<^sub>1}
        \<and> y \<in> T - {w, q\<^sub>1}
        \<and> x \<in> C - {w}
        \<and> y \<in> C - {w}"
  proof -
    let ?germ_same_side =
      "\<exists>S T C x y. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> x \<in> S - {w, q\<^sub>1}
        \<and> y \<in> T - {w, q\<^sub>1}
        \<and> x \<in> C - {w}
        \<and> y \<in> C - {w}"
    have hx\<^sub>1e\<^sub>1_punctured: "x\<^sub>1 \<in> e\<^sub>1 - {w, q\<^sub>1}"
      using hx\<^sub>1_edge_sphere hx\<^sub>1_ne_q\<^sub>1 by (by100 blast)
    have hx\<^sub>2e\<^sub>2_punctured: "x\<^sub>2 \<in> e\<^sub>2 - {w, q\<^sub>1}"
      using hx\<^sub>2_edge_sphere hx\<^sub>2_ne_q\<^sub>1 by (by100 blast)
    have hx\<^sub>3e\<^sub>3_punctured: "x\<^sub>3 \<in> e\<^sub>3 - {w, q\<^sub>1}"
      using hx\<^sub>3_edge_sphere hx\<^sub>3_ne_q\<^sub>1 by (by100 blast)
    have hpair_germ:
        "\<And>x y S T C. C \<in> {A\<^sub>1, A\<^sub>2}
          \<Longrightarrow> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<Longrightarrow> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<Longrightarrow> S \<noteq> T
          \<Longrightarrow> x \<in> S - {w, q\<^sub>1}
          \<Longrightarrow> y \<in> T - {w, q\<^sub>1}
          \<Longrightarrow> x \<in> C - {w}
          \<Longrightarrow> y \<in> C - {w}
          \<Longrightarrow> ?germ_same_side"
    proof -
      fix x y S T C
      assume hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
      assume hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      assume hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      assume hST: "S \<noteq> T"
      assume hxS: "x \<in> S - {w, q\<^sub>1}"
      assume hyT: "y \<in> T - {w, q\<^sub>1}"
      assume hxC: "x \<in> C - {w}"
      assume hyC: "y \<in> C - {w}"
      have hbody:
          "C \<in> {A\<^sub>1, A\<^sub>2}
          \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> S \<noteq> T
          \<and> x \<in> S - {w, q\<^sub>1}
          \<and> y \<in> T - {w, q\<^sub>1}
          \<and> x \<in> C - {w}
          \<and> y \<in> C - {w}"
        using hC hS hT hST hxS hyT hxC hyC by (by100 blast)
      show ?germ_same_side
      proof (rule exI[where x=S])
        show "\<exists>T C x y. C \<in> {A\<^sub>1, A\<^sub>2}
          \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> S \<noteq> T
          \<and> x \<in> S - {w, q\<^sub>1}
          \<and> y \<in> T - {w, q\<^sub>1}
          \<and> x \<in> C - {w}
          \<and> y \<in> C - {w}"
        proof (rule exI[where x=T])
          show "\<exists>C x y. C \<in> {A\<^sub>1, A\<^sub>2}
            \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> S \<noteq> T
            \<and> x \<in> S - {w, q\<^sub>1}
            \<and> y \<in> T - {w, q\<^sub>1}
            \<and> x \<in> C - {w}
            \<and> y \<in> C - {w}"
          proof (rule exI[where x=C])
            show "\<exists>x y. C \<in> {A\<^sub>1, A\<^sub>2}
              \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
              \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
              \<and> S \<noteq> T
              \<and> x \<in> S - {w, q\<^sub>1}
              \<and> y \<in> T - {w, q\<^sub>1}
              \<and> x \<in> C - {w}
              \<and> y \<in> C - {w}"
            proof (rule exI[where x=x])
              show "\<exists>y. C \<in> {A\<^sub>1, A\<^sub>2}
                \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
                \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
                \<and> S \<noteq> T
                \<and> x \<in> S - {w, q\<^sub>1}
                \<and> y \<in> T - {w, q\<^sub>1}
                \<and> x \<in> C - {w}
                \<and> y \<in> C - {w}"
              proof (rule exI[where x=y])
                show "C \<in> {A\<^sub>1, A\<^sub>2}
                  \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
                  \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
                  \<and> S \<noteq> T
                  \<and> x \<in> S - {w, q\<^sub>1}
                  \<and> y \<in> T - {w, q\<^sub>1}
                  \<and> x \<in> C - {w}
                  \<and> y \<in> C - {w}"
                  by (rule hbody)
              qed
            qed
          qed
        qed
      qed
    qed
    show ?thesis
      using htwo_witnesses_same_arc_side
    proof (elim disjE)
      assume hside: "x\<^sub>1 \<in> A\<^sub>1 - {w} \<and> x\<^sub>2 \<in> A\<^sub>1 - {w}"
      show ?thesis
      proof (rule hpair_germ[where x=x\<^sub>1 and y=x\<^sub>2 and S=e\<^sub>1 and T=e\<^sub>2 and C=A\<^sub>1])
        show "A\<^sub>1 \<in> {A\<^sub>1, A\<^sub>2}" by (by100 simp)
        show "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>1 \<noteq> e\<^sub>2" by (rule he\<^sub>12)
        show "x\<^sub>1 \<in> e\<^sub>1 - {w, q\<^sub>1}" by (rule hx\<^sub>1e\<^sub>1_punctured)
        show "x\<^sub>2 \<in> e\<^sub>2 - {w, q\<^sub>1}" by (rule hx\<^sub>2e\<^sub>2_punctured)
        show "x\<^sub>1 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
        show "x\<^sub>2 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
      qed
    next
      assume hside: "x\<^sub>1 \<in> A\<^sub>1 - {w} \<and> x\<^sub>3 \<in> A\<^sub>1 - {w}"
      show ?thesis
      proof (rule hpair_germ[where x=x\<^sub>1 and y=x\<^sub>3 and S=e\<^sub>1 and T=e\<^sub>3 and C=A\<^sub>1])
        show "A\<^sub>1 \<in> {A\<^sub>1, A\<^sub>2}" by (by100 simp)
        show "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>1 \<noteq> e\<^sub>3" by (rule he\<^sub>13)
        show "x\<^sub>1 \<in> e\<^sub>1 - {w, q\<^sub>1}" by (rule hx\<^sub>1e\<^sub>1_punctured)
        show "x\<^sub>3 \<in> e\<^sub>3 - {w, q\<^sub>1}" by (rule hx\<^sub>3e\<^sub>3_punctured)
        show "x\<^sub>1 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
        show "x\<^sub>3 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
      qed
    next
      assume hside: "x\<^sub>2 \<in> A\<^sub>1 - {w} \<and> x\<^sub>3 \<in> A\<^sub>1 - {w}"
      show ?thesis
      proof (rule hpair_germ[where x=x\<^sub>2 and y=x\<^sub>3 and S=e\<^sub>2 and T=e\<^sub>3 and C=A\<^sub>1])
        show "A\<^sub>1 \<in> {A\<^sub>1, A\<^sub>2}" by (by100 simp)
        show "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>2 \<noteq> e\<^sub>3" by (rule he\<^sub>23)
        show "x\<^sub>2 \<in> e\<^sub>2 - {w, q\<^sub>1}" by (rule hx\<^sub>2e\<^sub>2_punctured)
        show "x\<^sub>3 \<in> e\<^sub>3 - {w, q\<^sub>1}" by (rule hx\<^sub>3e\<^sub>3_punctured)
        show "x\<^sub>2 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
        show "x\<^sub>3 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
      qed
    next
      assume hside: "x\<^sub>1 \<in> A\<^sub>2 - {w} \<and> x\<^sub>2 \<in> A\<^sub>2 - {w}"
      show ?thesis
      proof (rule hpair_germ[where x=x\<^sub>1 and y=x\<^sub>2 and S=e\<^sub>1 and T=e\<^sub>2 and C=A\<^sub>2])
        show "A\<^sub>2 \<in> {A\<^sub>1, A\<^sub>2}" by (by100 simp)
        show "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>1 \<noteq> e\<^sub>2" by (rule he\<^sub>12)
        show "x\<^sub>1 \<in> e\<^sub>1 - {w, q\<^sub>1}" by (rule hx\<^sub>1e\<^sub>1_punctured)
        show "x\<^sub>2 \<in> e\<^sub>2 - {w, q\<^sub>1}" by (rule hx\<^sub>2e\<^sub>2_punctured)
        show "x\<^sub>1 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
        show "x\<^sub>2 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
      qed
    next
      assume hside: "x\<^sub>1 \<in> A\<^sub>2 - {w} \<and> x\<^sub>3 \<in> A\<^sub>2 - {w}"
      show ?thesis
      proof (rule hpair_germ[where x=x\<^sub>1 and y=x\<^sub>3 and S=e\<^sub>1 and T=e\<^sub>3 and C=A\<^sub>2])
        show "A\<^sub>2 \<in> {A\<^sub>1, A\<^sub>2}" by (by100 simp)
        show "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>1 \<noteq> e\<^sub>3" by (rule he\<^sub>13)
        show "x\<^sub>1 \<in> e\<^sub>1 - {w, q\<^sub>1}" by (rule hx\<^sub>1e\<^sub>1_punctured)
        show "x\<^sub>3 \<in> e\<^sub>3 - {w, q\<^sub>1}" by (rule hx\<^sub>3e\<^sub>3_punctured)
        show "x\<^sub>1 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
        show "x\<^sub>3 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
      qed
    next
      assume hside: "x\<^sub>2 \<in> A\<^sub>2 - {w} \<and> x\<^sub>3 \<in> A\<^sub>2 - {w}"
      show ?thesis
      proof (rule hpair_germ[where x=x\<^sub>2 and y=x\<^sub>3 and S=e\<^sub>2 and T=e\<^sub>3 and C=A\<^sub>2])
        show "A\<^sub>2 \<in> {A\<^sub>1, A\<^sub>2}" by (by100 simp)
        show "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>2 \<noteq> e\<^sub>3" by (rule he\<^sub>23)
        show "x\<^sub>2 \<in> e\<^sub>2 - {w, q\<^sub>1}" by (rule hx\<^sub>2e\<^sub>2_punctured)
        show "x\<^sub>3 \<in> e\<^sub>3 - {w, q\<^sub>1}" by (rule hx\<^sub>3e\<^sub>3_punctured)
        show "x\<^sub>2 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
        show "x\<^sub>3 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
      qed
    qed
  qed
  have htwo_selected_germs_connected_in_arc_side:
      "\<exists>S T C x y. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> x \<in> S - {w, q\<^sub>1}
        \<and> y \<in> T - {w, q\<^sub>1}
        \<and> x \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
  proof -
    obtain S T C x y where hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
        and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        and hST: "S \<noteq> T"
        and hxS: "x \<in> S - {w, q\<^sub>1}"
        and hyT: "y \<in> T - {w, q\<^sub>1}"
        and hxC: "x \<in> C - {w}"
        and hyC: "y \<in> C - {w}"
      using htwo_selected_punctured_germs_same_arc_side by (elim exE conjE)
    have hconnC: "top1_connected_on (C - {w})
        (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
    proof -
      have hcases: "C = A\<^sub>1 \<or> C = A\<^sub>2"
        using hC by (by100 simp)
      show ?thesis
        using hcases hA\<^sub>1_minus_w_connected hA\<^sub>2_minus_w_connected
        by (by100 blast)
    qed
    have hbody:
        "C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> x \<in> S - {w, q\<^sub>1}
        \<and> y \<in> T - {w, q\<^sub>1}
        \<and> x \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
    proof (intro conjI)
      show "C \<in> {A\<^sub>1, A\<^sub>2}" by (rule hC)
      show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
      show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
      show "S \<noteq> T" by (rule hST)
      show "x \<in> S - {w, q\<^sub>1}" by (rule hxS)
      show "y \<in> T - {w, q\<^sub>1}" by (rule hyT)
      show "x \<in> C - {w}" by (rule hxC)
      show "y \<in> C - {w}" by (rule hyC)
      show "top1_connected_on (C - {w})
        (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
        by (rule hconnC)
    qed
    show ?thesis
    proof (rule exI[where x=S])
      show "\<exists>T C x y. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> x \<in> S - {w, q\<^sub>1}
        \<and> y \<in> T - {w, q\<^sub>1}
        \<and> x \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      proof (rule exI[where x=T])
        show "\<exists>C x y. C \<in> {A\<^sub>1, A\<^sub>2}
          \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> S \<noteq> T
          \<and> x \<in> S - {w, q\<^sub>1}
          \<and> y \<in> T - {w, q\<^sub>1}
          \<and> x \<in> C - {w}
          \<and> y \<in> C - {w}
          \<and> top1_connected_on (C - {w})
            (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
        proof (rule exI[where x=C])
          show "\<exists>x y. C \<in> {A\<^sub>1, A\<^sub>2}
            \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> S \<noteq> T
            \<and> x \<in> S - {w, q\<^sub>1}
            \<and> y \<in> T - {w, q\<^sub>1}
            \<and> x \<in> C - {w}
            \<and> y \<in> C - {w}
            \<and> top1_connected_on (C - {w})
              (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
          proof (rule exI[where x=x])
            show "\<exists>y. C \<in> {A\<^sub>1, A\<^sub>2}
              \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
              \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
              \<and> S \<noteq> T
              \<and> x \<in> S - {w, q\<^sub>1}
              \<and> y \<in> T - {w, q\<^sub>1}
              \<and> x \<in> C - {w}
              \<and> y \<in> C - {w}
              \<and> top1_connected_on (C - {w})
                (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
            proof (rule exI[where x=y])
              show "C \<in> {A\<^sub>1, A\<^sub>2}
                \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
                \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
                \<and> S \<noteq> T
                \<and> x \<in> S - {w, q\<^sub>1}
                \<and> y \<in> T - {w, q\<^sub>1}
                \<and> x \<in> C - {w}
                \<and> y \<in> C - {w}
                \<and> top1_connected_on (C - {w})
                  (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
                by (rule hbody)
            qed
          qed
        qed
      qed
    qed
  qed
  have htwo_selected_sphere_germs_connected_in_arc_side:
      "\<exists>S T C x y. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> x \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
  proof -
    let ?sphere_germs =
      "\<exists>S T C x y. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> x \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
    have hx\<^sub>1e\<^sub>1_sphere_punctured: "x\<^sub>1 \<in> (e\<^sub>1 - {w, q\<^sub>1}) \<inter> sphere w r"
      using hx\<^sub>1_edge_sphere hx\<^sub>1_ne_q\<^sub>1 by (by100 blast)
    have hx\<^sub>2e\<^sub>2_sphere_punctured: "x\<^sub>2 \<in> (e\<^sub>2 - {w, q\<^sub>1}) \<inter> sphere w r"
      using hx\<^sub>2_edge_sphere hx\<^sub>2_ne_q\<^sub>1 by (by100 blast)
    have hx\<^sub>3e\<^sub>3_sphere_punctured: "x\<^sub>3 \<in> (e\<^sub>3 - {w, q\<^sub>1}) \<inter> sphere w r"
      using hx\<^sub>3_edge_sphere hx\<^sub>3_ne_q\<^sub>1 by (by100 blast)
    have hpair_sphere:
        "\<And>x y S T C. C \<in> {A\<^sub>1, A\<^sub>2}
          \<Longrightarrow> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<Longrightarrow> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<Longrightarrow> S \<noteq> T
          \<Longrightarrow> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
          \<Longrightarrow> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
          \<Longrightarrow> x \<in> C - {w}
          \<Longrightarrow> y \<in> C - {w}
          \<Longrightarrow> top1_connected_on (C - {w})
            (subspace_topology UNIV geotop_euclidean_topology (C - {w}))
          \<Longrightarrow> ?sphere_germs"
    proof -
      fix x y S T C
      assume hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
      assume hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      assume hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      assume hST: "S \<noteq> T"
      assume hxS: "x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      assume hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      assume hxC: "x \<in> C - {w}"
      assume hyC: "y \<in> C - {w}"
      assume hconnC: "top1_connected_on (C - {w})
        (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      have hbody:
          "C \<in> {A\<^sub>1, A\<^sub>2}
          \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> S \<noteq> T
          \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
          \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
          \<and> x \<in> C - {w}
          \<and> y \<in> C - {w}
          \<and> top1_connected_on (C - {w})
            (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      proof (intro conjI)
        show "C \<in> {A\<^sub>1, A\<^sub>2}" by (rule hC)
        show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
        show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
        show "S \<noteq> T" by (rule hST)
        show "x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hxS)
        show "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hyT)
        show "x \<in> C - {w}" by (rule hxC)
        show "y \<in> C - {w}" by (rule hyC)
        show "top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
          by (rule hconnC)
      qed
      show ?sphere_germs
      proof (rule exI[where x=S])
        show "\<exists>T C x y. C \<in> {A\<^sub>1, A\<^sub>2}
          \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> S \<noteq> T
          \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
          \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
          \<and> x \<in> C - {w}
          \<and> y \<in> C - {w}
          \<and> top1_connected_on (C - {w})
            (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
        proof (rule exI[where x=T])
          show "\<exists>C x y. C \<in> {A\<^sub>1, A\<^sub>2}
            \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> S \<noteq> T
            \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
            \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
            \<and> x \<in> C - {w}
            \<and> y \<in> C - {w}
            \<and> top1_connected_on (C - {w})
              (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
          proof (rule exI[where x=C])
            show "\<exists>x y. C \<in> {A\<^sub>1, A\<^sub>2}
              \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
              \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
              \<and> S \<noteq> T
              \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
              \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
              \<and> x \<in> C - {w}
              \<and> y \<in> C - {w}
              \<and> top1_connected_on (C - {w})
                (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
            proof (rule exI[where x=x])
              show "\<exists>y. C \<in> {A\<^sub>1, A\<^sub>2}
                \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
                \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
                \<and> S \<noteq> T
                \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
                \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
                \<and> x \<in> C - {w}
                \<and> y \<in> C - {w}
                \<and> top1_connected_on (C - {w})
                  (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
              proof (rule exI[where x=y])
                show "C \<in> {A\<^sub>1, A\<^sub>2}
                  \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
                  \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
                  \<and> S \<noteq> T
                  \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
                  \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
                  \<and> x \<in> C - {w}
                  \<and> y \<in> C - {w}
                  \<and> top1_connected_on (C - {w})
                    (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
                  by (rule hbody)
              qed
            qed
          qed
        qed
      qed
    qed
    show ?thesis
      using htwo_witnesses_same_arc_side
    proof (elim disjE)
      assume hside: "x\<^sub>1 \<in> A\<^sub>1 - {w} \<and> x\<^sub>2 \<in> A\<^sub>1 - {w}"
      show ?thesis
      proof (rule hpair_sphere[where x=x\<^sub>1 and y=x\<^sub>2 and S=e\<^sub>1 and T=e\<^sub>2 and C=A\<^sub>1])
        show "A\<^sub>1 \<in> {A\<^sub>1, A\<^sub>2}" by (by100 simp)
        show "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>1 \<noteq> e\<^sub>2" by (rule he\<^sub>12)
        show "x\<^sub>1 \<in> (e\<^sub>1 - {w, q\<^sub>1}) \<inter> sphere w r"
          by (rule hx\<^sub>1e\<^sub>1_sphere_punctured)
        show "x\<^sub>2 \<in> (e\<^sub>2 - {w, q\<^sub>1}) \<inter> sphere w r"
          by (rule hx\<^sub>2e\<^sub>2_sphere_punctured)
        show "x\<^sub>1 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
        show "x\<^sub>2 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
        show "top1_connected_on (A\<^sub>1 - {w})
          (subspace_topology UNIV geotop_euclidean_topology (A\<^sub>1 - {w}))"
          by (rule hA\<^sub>1_minus_w_connected)
      qed
    next
      assume hside: "x\<^sub>1 \<in> A\<^sub>1 - {w} \<and> x\<^sub>3 \<in> A\<^sub>1 - {w}"
      show ?thesis
      proof (rule hpair_sphere[where x=x\<^sub>1 and y=x\<^sub>3 and S=e\<^sub>1 and T=e\<^sub>3 and C=A\<^sub>1])
        show "A\<^sub>1 \<in> {A\<^sub>1, A\<^sub>2}" by (by100 simp)
        show "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>1 \<noteq> e\<^sub>3" by (rule he\<^sub>13)
        show "x\<^sub>1 \<in> (e\<^sub>1 - {w, q\<^sub>1}) \<inter> sphere w r"
          by (rule hx\<^sub>1e\<^sub>1_sphere_punctured)
        show "x\<^sub>3 \<in> (e\<^sub>3 - {w, q\<^sub>1}) \<inter> sphere w r"
          by (rule hx\<^sub>3e\<^sub>3_sphere_punctured)
        show "x\<^sub>1 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
        show "x\<^sub>3 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
        show "top1_connected_on (A\<^sub>1 - {w})
          (subspace_topology UNIV geotop_euclidean_topology (A\<^sub>1 - {w}))"
          by (rule hA\<^sub>1_minus_w_connected)
      qed
    next
      assume hside: "x\<^sub>2 \<in> A\<^sub>1 - {w} \<and> x\<^sub>3 \<in> A\<^sub>1 - {w}"
      show ?thesis
      proof (rule hpair_sphere[where x=x\<^sub>2 and y=x\<^sub>3 and S=e\<^sub>2 and T=e\<^sub>3 and C=A\<^sub>1])
        show "A\<^sub>1 \<in> {A\<^sub>1, A\<^sub>2}" by (by100 simp)
        show "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>2 \<noteq> e\<^sub>3" by (rule he\<^sub>23)
        show "x\<^sub>2 \<in> (e\<^sub>2 - {w, q\<^sub>1}) \<inter> sphere w r"
          by (rule hx\<^sub>2e\<^sub>2_sphere_punctured)
        show "x\<^sub>3 \<in> (e\<^sub>3 - {w, q\<^sub>1}) \<inter> sphere w r"
          by (rule hx\<^sub>3e\<^sub>3_sphere_punctured)
        show "x\<^sub>2 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
        show "x\<^sub>3 \<in> A\<^sub>1 - {w}" using hside by (by100 blast)
        show "top1_connected_on (A\<^sub>1 - {w})
          (subspace_topology UNIV geotop_euclidean_topology (A\<^sub>1 - {w}))"
          by (rule hA\<^sub>1_minus_w_connected)
      qed
    next
      assume hside: "x\<^sub>1 \<in> A\<^sub>2 - {w} \<and> x\<^sub>2 \<in> A\<^sub>2 - {w}"
      show ?thesis
      proof (rule hpair_sphere[where x=x\<^sub>1 and y=x\<^sub>2 and S=e\<^sub>1 and T=e\<^sub>2 and C=A\<^sub>2])
        show "A\<^sub>2 \<in> {A\<^sub>1, A\<^sub>2}" by (by100 simp)
        show "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>1 \<noteq> e\<^sub>2" by (rule he\<^sub>12)
        show "x\<^sub>1 \<in> (e\<^sub>1 - {w, q\<^sub>1}) \<inter> sphere w r"
          by (rule hx\<^sub>1e\<^sub>1_sphere_punctured)
        show "x\<^sub>2 \<in> (e\<^sub>2 - {w, q\<^sub>1}) \<inter> sphere w r"
          by (rule hx\<^sub>2e\<^sub>2_sphere_punctured)
        show "x\<^sub>1 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
        show "x\<^sub>2 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
        show "top1_connected_on (A\<^sub>2 - {w})
          (subspace_topology UNIV geotop_euclidean_topology (A\<^sub>2 - {w}))"
          by (rule hA\<^sub>2_minus_w_connected)
      qed
    next
      assume hside: "x\<^sub>1 \<in> A\<^sub>2 - {w} \<and> x\<^sub>3 \<in> A\<^sub>2 - {w}"
      show ?thesis
      proof (rule hpair_sphere[where x=x\<^sub>1 and y=x\<^sub>3 and S=e\<^sub>1 and T=e\<^sub>3 and C=A\<^sub>2])
        show "A\<^sub>2 \<in> {A\<^sub>1, A\<^sub>2}" by (by100 simp)
        show "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>1 \<noteq> e\<^sub>3" by (rule he\<^sub>13)
        show "x\<^sub>1 \<in> (e\<^sub>1 - {w, q\<^sub>1}) \<inter> sphere w r"
          by (rule hx\<^sub>1e\<^sub>1_sphere_punctured)
        show "x\<^sub>3 \<in> (e\<^sub>3 - {w, q\<^sub>1}) \<inter> sphere w r"
          by (rule hx\<^sub>3e\<^sub>3_sphere_punctured)
        show "x\<^sub>1 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
        show "x\<^sub>3 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
        show "top1_connected_on (A\<^sub>2 - {w})
          (subspace_topology UNIV geotop_euclidean_topology (A\<^sub>2 - {w}))"
          by (rule hA\<^sub>2_minus_w_connected)
      qed
    next
      assume hside: "x\<^sub>2 \<in> A\<^sub>2 - {w} \<and> x\<^sub>3 \<in> A\<^sub>2 - {w}"
      show ?thesis
      proof (rule hpair_sphere[where x=x\<^sub>2 and y=x\<^sub>3 and S=e\<^sub>2 and T=e\<^sub>3 and C=A\<^sub>2])
        show "A\<^sub>2 \<in> {A\<^sub>1, A\<^sub>2}" by (by100 simp)
        show "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (by100 simp)
        show "e\<^sub>2 \<noteq> e\<^sub>3" by (rule he\<^sub>23)
        show "x\<^sub>2 \<in> (e\<^sub>2 - {w, q\<^sub>1}) \<inter> sphere w r"
          by (rule hx\<^sub>2e\<^sub>2_sphere_punctured)
        show "x\<^sub>3 \<in> (e\<^sub>3 - {w, q\<^sub>1}) \<inter> sphere w r"
          by (rule hx\<^sub>3e\<^sub>3_sphere_punctured)
        show "x\<^sub>2 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
        show "x\<^sub>3 \<in> A\<^sub>2 - {w}" using hside by (by100 blast)
        show "top1_connected_on (A\<^sub>2 - {w})
          (subspace_topology UNIV geotop_euclidean_topology (A\<^sub>2 - {w}))"
          by (rule hA\<^sub>2_minus_w_connected)
      qed
    qed
  qed
  have hpunctured_carrier_connected_meets_two_sphere_germs:
      "\<exists>S T N x y. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> x \<in> N
        \<and> y \<in> N
        \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
  proof -
    obtain S T C x y where hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
        and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        and hST: "S \<noteq> T"
        and hxS: "x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
        and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
        and hxC: "x \<in> C - {w}"
        and hyC: "y \<in> C - {w}"
        and hconnC: "top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      using htwo_selected_sphere_germs_connected_in_arc_side by (elim exE conjE)
    have hC_sub_poly: "C \<subseteq> geotop_polyhedron L"
    proof
      fix z
      assume hzC: "z \<in> C"
      have hcases: "C = A\<^sub>1 \<or> C = A\<^sub>2"
        using hC by (by100 simp)
      show "z \<in> geotop_polyhedron L"
        using hcases hzC hA_decomp by (by100 blast)
    qed
    have hN_sub: "C - {w} \<subseteq> geotop_polyhedron L - {w}"
      using hC_sub_poly by (by100 blast)
    have hbody:
        "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> C - {w} \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))
        \<and> x \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
    proof (intro conjI)
      show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
      show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
      show "S \<noteq> T" by (rule hST)
      show "C - {w} \<subseteq> geotop_polyhedron L - {w}" by (rule hN_sub)
      show "top1_connected_on (C - {w})
        (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
        by (rule hconnC)
      show "x \<in> C - {w}" by (rule hxC)
      show "y \<in> C - {w}" by (rule hyC)
      show "x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hxS)
      show "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hyT)
    qed
    show ?thesis
    proof (rule exI[where x=S])
      show "\<exists>T N x y. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> x \<in> N
        \<and> y \<in> N
        \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      proof (rule exI[where x=T])
        show "\<exists>N x y. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> S \<noteq> T
          \<and> N \<subseteq> geotop_polyhedron L - {w}
          \<and> top1_connected_on N
            (subspace_topology UNIV geotop_euclidean_topology N)
          \<and> x \<in> N
          \<and> y \<in> N
          \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
          \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
        proof (rule exI[where x="C - {w}"])
          show "\<exists>x y. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> S \<noteq> T
            \<and> C - {w} \<subseteq> geotop_polyhedron L - {w}
            \<and> top1_connected_on (C - {w})
              (subspace_topology UNIV geotop_euclidean_topology (C - {w}))
            \<and> x \<in> C - {w}
            \<and> y \<in> C - {w}
            \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
            \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
          proof (rule exI[where x=x])
            show "\<exists>y. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
              \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
              \<and> S \<noteq> T
              \<and> C - {w} \<subseteq> geotop_polyhedron L - {w}
              \<and> top1_connected_on (C - {w})
                (subspace_topology UNIV geotop_euclidean_topology (C - {w}))
              \<and> x \<in> C - {w}
              \<and> y \<in> C - {w}
              \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
              \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
            proof (rule exI[where x=y])
              show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
                \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
                \<and> S \<noteq> T
                \<and> C - {w} \<subseteq> geotop_polyhedron L - {w}
                \<and> top1_connected_on (C - {w})
                  (subspace_topology UNIV geotop_euclidean_topology (C - {w}))
                \<and> x \<in> C - {w}
                \<and> y \<in> C - {w}
                \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
                \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
                by (rule hbody)
            qed
          qed
        qed
      qed
    qed
  qed
  have htwo_selected_sphere_germs_same_punctured_component:
      "\<exists>S T x y. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> top1_in_same_component_on (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w})) x y"
  proof -
    obtain S T N x y where hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
      and hN_conn: "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
      and hxN: "x \<in> N"
      and hyN: "y \<in> N"
      and hxS: "x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      using hpunctured_carrier_connected_meets_two_sphere_germs by (elim exE conjE)
    have hN_subtop:
        "subspace_topology (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w})) N
          = subspace_topology UNIV geotop_euclidean_topology N"
      by (rule subspace_topology_trans[OF hN_sub])
    have hsame_component:
        "top1_in_same_component_on (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w})) x y"
      unfolding top1_in_same_component_on_def
    proof (rule exI[where x=N])
      show "N \<subseteq> geotop_polyhedron L - {w}
        \<and> x \<in> N
        \<and> y \<in> N
        \<and> top1_connected_on N
          (subspace_topology (geotop_polyhedron L - {w})
            (subspace_topology UNIV geotop_euclidean_topology
              (geotop_polyhedron L - {w})) N)"
      proof (intro conjI)
        show "N \<subseteq> geotop_polyhedron L - {w}" by (rule hN_sub)
        show "x \<in> N" by (rule hxN)
        show "y \<in> N" by (rule hyN)
        show "top1_connected_on N
          (subspace_topology (geotop_polyhedron L - {w})
            (subspace_topology UNIV geotop_euclidean_topology
              (geotop_polyhedron L - {w})) N)"
          unfolding hN_subtop by (rule hN_conn)
      qed
    qed
    show ?thesis
    proof (rule exI[where x=S])
      show "\<exists>T x y. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> top1_in_same_component_on (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w})) x y"
      proof (rule exI[where x=T])
        show "\<exists>x y. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> S \<noteq> T
          \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
          \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
          \<and> top1_in_same_component_on (geotop_polyhedron L - {w})
            (subspace_topology UNIV geotop_euclidean_topology
              (geotop_polyhedron L - {w})) x y"
        proof (rule exI[where x=x])
          show "\<exists>y. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> S \<noteq> T
            \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
            \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
            \<and> top1_in_same_component_on (geotop_polyhedron L - {w})
              (subspace_topology UNIV geotop_euclidean_topology
                (geotop_polyhedron L - {w})) x y"
          proof (rule exI[where x=y])
            show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
              \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
              \<and> S \<noteq> T
              \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
              \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
              \<and> top1_in_same_component_on (geotop_polyhedron L - {w})
                (subspace_topology UNIV geotop_euclidean_topology
                  (geotop_polyhedron L - {w})) x y"
            proof (intro conjI)
              show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
              show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
              show "S \<noteq> T" by (rule hST)
              show "x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hxS)
              show "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hyT)
              show "top1_in_same_component_on (geotop_polyhedron L - {w})
                (subspace_topology UNIV geotop_euclidean_topology
                  (geotop_polyhedron L - {w})) x y"
                by (rule hsame_component)
            qed
          qed
        qed
      qed
    qed
  qed
  have he\<^sub>1_sphere_punctured_eq:
      "(e\<^sub>1 - {w, q\<^sub>1}) \<inter> sphere w r = {x\<^sub>1}"
  proof -
    have hr_le: "r \<le> dist w q\<^sub>1"
      using hr_lt_q\<^sub>1 by (by100 linarith)
    have hseg_sphere:
        "(closed_segment w q\<^sub>1 - {w}) \<inter> sphere w r = {x\<^sub>1}"
      by (rule closed_segment_sphere_unique_from_center
          [OF hq\<^sub>1w hr_pos hr_le x\<^sub>1_def])
    show ?thesis
      using hseg_sphere he\<^sub>1_seg hx\<^sub>1_ne_q\<^sub>1 by (by100 blast)
  qed
  have he\<^sub>2_sphere_punctured_eq:
      "(e\<^sub>2 - {w, q\<^sub>1}) \<inter> sphere w r = {x\<^sub>2}"
  proof -
    have hr_le: "r \<le> dist w q\<^sub>2"
      using hr_lt_q\<^sub>2 by (by100 linarith)
    have hseg_sphere:
        "(closed_segment w q\<^sub>2 - {w}) \<inter> sphere w r = {x\<^sub>2}"
      by (rule closed_segment_sphere_unique_from_center
          [OF hq\<^sub>2w hr_pos hr_le x\<^sub>2_def])
    show ?thesis
      using hseg_sphere he\<^sub>2_seg hq\<^sub>1_not_e\<^sub>2 by (by100 blast)
  qed
  have he\<^sub>3_sphere_punctured_eq:
      "(e\<^sub>3 - {w, q\<^sub>1}) \<inter> sphere w r = {x\<^sub>3}"
  proof -
    have hr_le: "r \<le> dist w q\<^sub>3"
      using hr_lt_q\<^sub>3 by (by100 linarith)
    have hseg_sphere:
        "(closed_segment w q\<^sub>3 - {w}) \<inter> sphere w r = {x\<^sub>3}"
      by (rule closed_segment_sphere_unique_from_center
          [OF hq\<^sub>3w hr_pos hr_le x\<^sub>3_def])
    show ?thesis
      using hseg_sphere he\<^sub>3_seg hq\<^sub>1_not_e\<^sub>3 by (by100 blast)
  qed
  have hselected_sphere_germ_point_canonical:
      "\<And>S x. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<Longrightarrow> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<Longrightarrow> x \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
  proof -
    fix S x
    assume hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
    assume hxS: "x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
    have hcases: "S = e\<^sub>1 \<or> S = e\<^sub>2 \<or> S = e\<^sub>3"
      using hS by (by100 simp)
    show "x \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      using hcases
    proof (elim disjE)
      assume hS_eq: "S = e\<^sub>1"
      have hx_eq: "x = x\<^sub>1"
        using hxS hS_eq he\<^sub>1_sphere_punctured_eq by (by100 simp)
      show ?thesis
        using hx_eq by (by100 simp)
    next
      assume hS_eq: "S = e\<^sub>2"
      have hx_eq: "x = x\<^sub>2"
        using hxS hS_eq he\<^sub>2_sphere_punctured_eq by (by100 simp)
      show ?thesis
        using hx_eq by (by100 simp)
    next
      assume hS_eq: "S = e\<^sub>3"
      have hx_eq: "x = x\<^sub>3"
        using hxS hS_eq he\<^sub>3_sphere_punctured_eq by (by100 simp)
      show ?thesis
        using hx_eq by (by100 simp)
    qed
  qed
  have hselected_sphere_germ_edge_point_cases:
      "\<And>S x. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<Longrightarrow> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<Longrightarrow> (S = e\<^sub>1 \<and> x = x\<^sub>1)
          \<or> (S = e\<^sub>2 \<and> x = x\<^sub>2)
          \<or> (S = e\<^sub>3 \<and> x = x\<^sub>3)"
  proof -
    fix S x
    assume hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
    assume hxS: "x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
    have hcases: "S = e\<^sub>1 \<or> S = e\<^sub>2 \<or> S = e\<^sub>3"
      using hS by (by100 simp)
    show "(S = e\<^sub>1 \<and> x = x\<^sub>1)
        \<or> (S = e\<^sub>2 \<and> x = x\<^sub>2)
        \<or> (S = e\<^sub>3 \<and> x = x\<^sub>3)"
      using hcases
    proof (elim disjE)
      assume hS_eq: "S = e\<^sub>1"
      have hx_eq: "x = x\<^sub>1"
        using hxS hS_eq he\<^sub>1_sphere_punctured_eq by (by100 simp)
      show ?thesis
        using hS_eq hx_eq by (by100 simp)
    next
      assume hS_eq: "S = e\<^sub>2"
      have hx_eq: "x = x\<^sub>2"
        using hxS hS_eq he\<^sub>2_sphere_punctured_eq by (by100 simp)
      show ?thesis
        using hS_eq hx_eq by (by100 simp)
    next
      assume hS_eq: "S = e\<^sub>3"
      have hx_eq: "x = x\<^sub>3"
        using hxS hS_eq he\<^sub>3_sphere_punctured_eq by (by100 simp)
      show ?thesis
        using hS_eq hx_eq by (by100 simp)
    qed
  qed
  have hcanonical_pair_same_arc_side:
      "\<exists>C a b. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> a \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> a \<noteq> b
        \<and> a \<in> C - {w}
        \<and> b \<in> C - {w}
        \<and> top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
  proof -
    obtain S T C x y where hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
        and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        and hST: "S \<noteq> T"
        and hxS: "x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
        and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
        and hxC: "x \<in> C - {w}"
        and hyC: "y \<in> C - {w}"
        and hconnC: "top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      using htwo_selected_sphere_germs_connected_in_arc_side by (elim exE conjE)
    have hx_can: "x \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      by (rule hselected_sphere_germ_point_canonical[OF hS hxS])
    have hy_can: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      by (rule hselected_sphere_germ_point_canonical[OF hT hyT])
    have hx_by_edge:
        "(S = e\<^sub>1 \<and> x = x\<^sub>1)
        \<or> (S = e\<^sub>2 \<and> x = x\<^sub>2)
        \<or> (S = e\<^sub>3 \<and> x = x\<^sub>3)"
      by (rule hselected_sphere_germ_edge_point_cases[OF hS hxS])
    have hy_by_edge:
        "(T = e\<^sub>1 \<and> y = x\<^sub>1)
        \<or> (T = e\<^sub>2 \<and> y = x\<^sub>2)
        \<or> (T = e\<^sub>3 \<and> y = x\<^sub>3)"
      by (rule hselected_sphere_germ_edge_point_cases[OF hT hyT])
    have hxy_ne: "x \<noteq> y"
      using hx_by_edge hy_by_edge hST hx\<^sub>12 hx\<^sub>13 hx\<^sub>23 by (by100 blast)
    have hbody:
        "C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> x \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> x \<noteq> y
        \<and> x \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
    proof (intro conjI)
      show "C \<in> {A\<^sub>1, A\<^sub>2}" by (rule hC)
      show "x \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hx_can)
      show "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hy_can)
      show "x \<noteq> y" by (rule hxy_ne)
      show "x \<in> C - {w}" by (rule hxC)
      show "y \<in> C - {w}" by (rule hyC)
      show "top1_connected_on (C - {w})
        (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
        by (rule hconnC)
    qed
    show ?thesis
    proof (rule exI[where x=C])
      show "\<exists>a b. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> a \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> a \<noteq> b
        \<and> a \<in> C - {w}
        \<and> b \<in> C - {w}
        \<and> top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      proof (rule exI[where x=x])
        show "\<exists>b. C \<in> {A\<^sub>1, A\<^sub>2}
          \<and> x \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<and> b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<and> x \<noteq> b
          \<and> x \<in> C - {w}
          \<and> b \<in> C - {w}
          \<and> top1_connected_on (C - {w})
            (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
        proof (rule exI[where x=y])
          show "C \<in> {A\<^sub>1, A\<^sub>2}
            \<and> x \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
            \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
            \<and> x \<noteq> y
            \<and> x \<in> C - {w}
            \<and> y \<in> C - {w}
            \<and> top1_connected_on (C - {w})
              (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
            by (rule hbody)
        qed
      qed
    qed
  qed
  have hcanonical_pair_same_arc_side_cases:
      "(x\<^sub>1 \<in> A\<^sub>1 - {w} \<and> x\<^sub>2 \<in> A\<^sub>1 - {w})
      \<or> (x\<^sub>1 \<in> A\<^sub>1 - {w} \<and> x\<^sub>3 \<in> A\<^sub>1 - {w})
      \<or> (x\<^sub>2 \<in> A\<^sub>1 - {w} \<and> x\<^sub>3 \<in> A\<^sub>1 - {w})
      \<or> (x\<^sub>1 \<in> A\<^sub>2 - {w} \<and> x\<^sub>2 \<in> A\<^sub>2 - {w})
      \<or> (x\<^sub>1 \<in> A\<^sub>2 - {w} \<and> x\<^sub>3 \<in> A\<^sub>2 - {w})
      \<or> (x\<^sub>2 \<in> A\<^sub>2 - {w} \<and> x\<^sub>3 \<in> A\<^sub>2 - {w})"
  proof -
    obtain C a b where hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
      and ha: "a \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hb: "b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hab: "a \<noteq> b"
      and haC: "a \<in> C - {w}"
      and hbC: "b \<in> C - {w}"
      using hcanonical_pair_same_arc_side by (elim exE conjE)
    have hC_cases: "C = A\<^sub>1 \<or> C = A\<^sub>2"
      using hC by (by100 simp)
    have ha_cases: "a = x\<^sub>1 \<or> a = x\<^sub>2 \<or> a = x\<^sub>3"
      using ha by (by100 simp)
    have hb_cases: "b = x\<^sub>1 \<or> b = x\<^sub>2 \<or> b = x\<^sub>3"
      using hb by (by100 simp)
    show ?thesis
      using hC_cases
    proof (elim disjE)
      assume hC_eq: "C = A\<^sub>1"
      show ?thesis
        using ha_cases
      proof (elim disjE)
        assume ha_eq: "a = x\<^sub>1"
        show ?thesis
          using hb_cases
        proof (elim disjE)
          assume hb_eq: "b = x\<^sub>1"
          have False
            using hab ha_eq hb_eq by (by100 simp)
          then show ?thesis by (by100 simp)
        next
          assume hb_eq: "b = x\<^sub>2"
          show ?thesis
            using haC hbC hC_eq ha_eq hb_eq by (by100 simp)
        next
          assume hb_eq: "b = x\<^sub>3"
          show ?thesis
            using haC hbC hC_eq ha_eq hb_eq by (by100 simp)
        qed
      next
        assume ha_eq: "a = x\<^sub>2"
        show ?thesis
          using hb_cases
        proof (elim disjE)
          assume hb_eq: "b = x\<^sub>1"
          show ?thesis
            using haC hbC hC_eq ha_eq hb_eq by (by100 simp)
        next
          assume hb_eq: "b = x\<^sub>2"
          have False
            using hab ha_eq hb_eq by (by100 simp)
          then show ?thesis by (by100 simp)
        next
          assume hb_eq: "b = x\<^sub>3"
          show ?thesis
            using haC hbC hC_eq ha_eq hb_eq by (by100 simp)
        qed
      next
        assume ha_eq: "a = x\<^sub>3"
        show ?thesis
          using hb_cases
        proof (elim disjE)
          assume hb_eq: "b = x\<^sub>1"
          show ?thesis
            using haC hbC hC_eq ha_eq hb_eq by (by100 simp)
        next
          assume hb_eq: "b = x\<^sub>2"
          show ?thesis
            using haC hbC hC_eq ha_eq hb_eq by (by100 simp)
        next
          assume hb_eq: "b = x\<^sub>3"
          have False
            using hab ha_eq hb_eq by (by100 simp)
          then show ?thesis by (by100 simp)
        qed
      qed
    next
      assume hC_eq: "C = A\<^sub>2"
      show ?thesis
        using ha_cases
      proof (elim disjE)
        assume ha_eq: "a = x\<^sub>1"
        show ?thesis
          using hb_cases
        proof (elim disjE)
          assume hb_eq: "b = x\<^sub>1"
          have False
            using hab ha_eq hb_eq by (by100 simp)
          then show ?thesis by (by100 simp)
        next
          assume hb_eq: "b = x\<^sub>2"
          show ?thesis
            using haC hbC hC_eq ha_eq hb_eq by (by100 simp)
        next
          assume hb_eq: "b = x\<^sub>3"
          show ?thesis
            using haC hbC hC_eq ha_eq hb_eq by (by100 simp)
        qed
      next
        assume ha_eq: "a = x\<^sub>2"
        show ?thesis
          using hb_cases
        proof (elim disjE)
          assume hb_eq: "b = x\<^sub>1"
          show ?thesis
            using haC hbC hC_eq ha_eq hb_eq by (by100 simp)
        next
          assume hb_eq: "b = x\<^sub>2"
          have False
            using hab ha_eq hb_eq by (by100 simp)
          then show ?thesis by (by100 simp)
        next
          assume hb_eq: "b = x\<^sub>3"
          show ?thesis
            using haC hbC hC_eq ha_eq hb_eq by (by100 simp)
        qed
      next
        assume ha_eq: "a = x\<^sub>3"
        show ?thesis
          using hb_cases
        proof (elim disjE)
          assume hb_eq: "b = x\<^sub>1"
          show ?thesis
            using haC hbC hC_eq ha_eq hb_eq by (by100 simp)
        next
          assume hb_eq: "b = x\<^sub>2"
          show ?thesis
            using haC hbC hC_eq ha_eq hb_eq by (by100 simp)
        next
          assume hb_eq: "b = x\<^sub>3"
          have False
            using hab ha_eq hb_eq by (by100 simp)
          then show ?thesis by (by100 simp)
        qed
      qed
    qed
  qed
  have htwo_canonical_sphere_points_same_punctured_component:
      "top1_in_same_component_on (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w})) x\<^sub>1 x\<^sub>2
      \<or> top1_in_same_component_on (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w})) x\<^sub>1 x\<^sub>3
      \<or> top1_in_same_component_on (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w})) x\<^sub>2 x\<^sub>3"
  proof -
    let ?X = "geotop_polyhedron L - {w}"
    let ?TX = "subspace_topology UNIV geotop_euclidean_topology ?X"
    obtain S T x y where hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and hxS: "x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      and hsame: "top1_in_same_component_on ?X ?TX x y"
      using htwo_selected_sphere_germs_same_punctured_component by (elim exE conjE)
    have hx_can: "x \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      by (rule hselected_sphere_germ_point_canonical[OF hS hxS])
    have hy_can: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      by (rule hselected_sphere_germ_point_canonical[OF hT hyT])
    have hx_by_edge:
        "(S = e\<^sub>1 \<and> x = x\<^sub>1)
        \<or> (S = e\<^sub>2 \<and> x = x\<^sub>2)
        \<or> (S = e\<^sub>3 \<and> x = x\<^sub>3)"
    proof -
      have hcases: "S = e\<^sub>1 \<or> S = e\<^sub>2 \<or> S = e\<^sub>3"
        using hS by (by100 simp)
      show ?thesis
        using hcases
      proof (elim disjE)
        assume hS_eq: "S = e\<^sub>1"
        have hx_eq: "x = x\<^sub>1"
          using hxS hS_eq he\<^sub>1_sphere_punctured_eq by (by100 simp)
        show ?thesis
          using hS_eq hx_eq by (by100 simp)
      next
        assume hS_eq: "S = e\<^sub>2"
        have hx_eq: "x = x\<^sub>2"
          using hxS hS_eq he\<^sub>2_sphere_punctured_eq by (by100 simp)
        show ?thesis
          using hS_eq hx_eq by (by100 simp)
      next
        assume hS_eq: "S = e\<^sub>3"
        have hx_eq: "x = x\<^sub>3"
          using hxS hS_eq he\<^sub>3_sphere_punctured_eq by (by100 simp)
        show ?thesis
          using hS_eq hx_eq by (by100 simp)
      qed
    qed
    have hy_by_edge:
        "(T = e\<^sub>1 \<and> y = x\<^sub>1)
        \<or> (T = e\<^sub>2 \<and> y = x\<^sub>2)
        \<or> (T = e\<^sub>3 \<and> y = x\<^sub>3)"
    proof -
      have hcases: "T = e\<^sub>1 \<or> T = e\<^sub>2 \<or> T = e\<^sub>3"
        using hT by (by100 simp)
      show ?thesis
        using hcases
      proof (elim disjE)
        assume hT_eq: "T = e\<^sub>1"
        have hy_eq: "y = x\<^sub>1"
          using hyT hT_eq he\<^sub>1_sphere_punctured_eq by (by100 simp)
        show ?thesis
          using hT_eq hy_eq by (by100 simp)
      next
        assume hT_eq: "T = e\<^sub>2"
        have hy_eq: "y = x\<^sub>2"
          using hyT hT_eq he\<^sub>2_sphere_punctured_eq by (by100 simp)
        show ?thesis
          using hT_eq hy_eq by (by100 simp)
      next
        assume hT_eq: "T = e\<^sub>3"
        have hy_eq: "y = x\<^sub>3"
          using hyT hT_eq he\<^sub>3_sphere_punctured_eq by (by100 simp)
        show ?thesis
          using hT_eq hy_eq by (by100 simp)
      qed
    qed
    have hxy_ne: "x \<noteq> y"
      using hx_by_edge hy_by_edge hST hx\<^sub>12 hx\<^sub>13 hx\<^sub>23 by (by100 blast)
    have hx_cases: "x = x\<^sub>1 \<or> x = x\<^sub>2 \<or> x = x\<^sub>3"
      using hx_can by (by100 simp)
    have hy_cases: "y = x\<^sub>1 \<or> y = x\<^sub>2 \<or> y = x\<^sub>3"
      using hy_can by (by100 simp)
    show ?thesis
      using hx_cases
    proof (elim disjE)
      assume hx: "x = x\<^sub>1"
      show ?thesis
        using hy_cases
      proof (elim disjE)
        assume hy: "y = x\<^sub>1"
        have False
          using hxy_ne hx hy by (by100 simp)
        thus ?thesis by (by100 simp)
      next
        assume hy: "y = x\<^sub>2"
        show ?thesis
          using hsame hx hy by (by100 simp)
      next
        assume hy: "y = x\<^sub>3"
        show ?thesis
          using hsame hx hy by (by100 simp)
      qed
    next
      assume hx: "x = x\<^sub>2"
      show ?thesis
        using hy_cases
      proof (elim disjE)
        assume hy: "y = x\<^sub>1"
        have hsame_yx: "top1_in_same_component_on ?X ?TX y x"
          by (rule top1_in_same_component_on_sym[OF hsame])
        have hsame12: "top1_in_same_component_on ?X ?TX x\<^sub>1 x\<^sub>2"
          using hsame_yx hx hy by (by100 simp)
        show ?thesis
          using hsame12 by (by100 simp)
      next
        assume hy: "y = x\<^sub>2"
        have False
          using hxy_ne hx hy by (by100 simp)
        thus ?thesis by (by100 simp)
      next
        assume hy: "y = x\<^sub>3"
        show ?thesis
          using hsame hx hy by (by100 simp)
      qed
    next
      assume hx: "x = x\<^sub>3"
      show ?thesis
        using hy_cases
      proof (elim disjE)
        assume hy: "y = x\<^sub>1"
        have hsame_yx: "top1_in_same_component_on ?X ?TX y x"
          by (rule top1_in_same_component_on_sym[OF hsame])
        have hsame13: "top1_in_same_component_on ?X ?TX x\<^sub>1 x\<^sub>3"
          using hsame_yx hx hy by (by100 simp)
        show ?thesis
          using hsame13 by (by100 simp)
      next
        assume hy: "y = x\<^sub>2"
        have hsame_yx: "top1_in_same_component_on ?X ?TX y x"
          by (rule top1_in_same_component_on_sym[OF hsame])
        have hsame23: "top1_in_same_component_on ?X ?TX x\<^sub>2 x\<^sub>3"
          using hsame_yx hx hy by (by100 simp)
        show ?thesis
          using hsame23 by (by100 simp)
      next
        assume hy: "y = x\<^sub>3"
        have False
          using hxy_ne hx hy by (by100 simp)
        thus ?thesis by (by100 simp)
      qed
    qed
  qed
  have hcanonical_pair_connected_witness:
      "\<exists>a b N. a \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> a \<noteq> b
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> a \<in> N
        \<and> b \<in> N"
  proof -
    let ?X = "geotop_polyhedron L - {w}"
    let ?TX = "subspace_topology UNIV geotop_euclidean_topology ?X"
    have hcomponent_witness:
        "\<And>a b. top1_in_same_component_on ?X ?TX a b
          \<Longrightarrow> \<exists>N. N \<subseteq> ?X
            \<and> top1_connected_on N
              (subspace_topology UNIV geotop_euclidean_topology N)
            \<and> a \<in> N
            \<and> b \<in> N"
    proof -
      fix a b
      assume hsame: "top1_in_same_component_on ?X ?TX a b"
      obtain N where hN_sub: "N \<subseteq> ?X"
        and haN: "a \<in> N"
        and hbN: "b \<in> N"
        and hN_conn: "top1_connected_on N
          (subspace_topology ?X ?TX N)"
        using hsame unfolding top1_in_same_component_on_def by (elim exE conjE)
      have hN_subtop:
          "subspace_topology ?X ?TX N
            = subspace_topology UNIV geotop_euclidean_topology N"
        by (rule subspace_topology_trans[OF hN_sub])
      have hbody:
          "N \<subseteq> ?X
          \<and> top1_connected_on N
            (subspace_topology UNIV geotop_euclidean_topology N)
          \<and> a \<in> N
          \<and> b \<in> N"
      proof (intro conjI)
        show "N \<subseteq> ?X" by (rule hN_sub)
        show "top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)"
          using hN_conn unfolding hN_subtop .
        show "a \<in> N" by (rule haN)
        show "b \<in> N" by (rule hbN)
      qed
      show "\<exists>N. N \<subseteq> ?X
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> a \<in> N
        \<and> b \<in> N"
      proof (rule exI[where x=N])
        show "N \<subseteq> ?X
          \<and> top1_connected_on N
            (subspace_topology UNIV geotop_euclidean_topology N)
          \<and> a \<in> N
          \<and> b \<in> N"
          by (rule hbody)
      qed
    qed
    have hpack:
        "\<And>a b. a \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<Longrightarrow> b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<Longrightarrow> a \<noteq> b
          \<Longrightarrow> top1_in_same_component_on ?X ?TX a b
          \<Longrightarrow> \<exists>a b N. a \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
            \<and> b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
            \<and> a \<noteq> b
            \<and> N \<subseteq> ?X
            \<and> top1_connected_on N
              (subspace_topology UNIV geotop_euclidean_topology N)
            \<and> a \<in> N
            \<and> b \<in> N"
    proof -
      fix a b
      assume ha: "a \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      assume hb: "b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      assume hab: "a \<noteq> b"
      assume hsame: "top1_in_same_component_on ?X ?TX a b"
      obtain N where hN_sub: "N \<subseteq> ?X"
        and hN_conn: "top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)"
        and haN: "a \<in> N"
        and hbN: "b \<in> N"
        using hcomponent_witness[OF hsame] by (elim exE conjE)
      have hbody:
          "a \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<and> b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<and> a \<noteq> b
          \<and> N \<subseteq> ?X
          \<and> top1_connected_on N
            (subspace_topology UNIV geotop_euclidean_topology N)
          \<and> a \<in> N
          \<and> b \<in> N"
      proof (intro conjI)
        show "a \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule ha)
        show "b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hb)
        show "a \<noteq> b" by (rule hab)
        show "N \<subseteq> ?X" by (rule hN_sub)
        show "top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)"
          by (rule hN_conn)
        show "a \<in> N" by (rule haN)
        show "b \<in> N" by (rule hbN)
      qed
      show "\<exists>a b N. a \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> a \<noteq> b
        \<and> N \<subseteq> ?X
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> a \<in> N
        \<and> b \<in> N"
      proof (rule exI[where x=a])
        show "\<exists>b N. a \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<and> b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<and> a \<noteq> b
          \<and> N \<subseteq> ?X
          \<and> top1_connected_on N
            (subspace_topology UNIV geotop_euclidean_topology N)
          \<and> a \<in> N
          \<and> b \<in> N"
        proof (rule exI[where x=b])
          show "\<exists>N. a \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
            \<and> b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
            \<and> a \<noteq> b
            \<and> N \<subseteq> ?X
            \<and> top1_connected_on N
              (subspace_topology UNIV geotop_euclidean_topology N)
            \<and> a \<in> N
            \<and> b \<in> N"
          proof (rule exI[where x=N])
            show "a \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
              \<and> b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
              \<and> a \<noteq> b
              \<and> N \<subseteq> ?X
              \<and> top1_connected_on N
                (subspace_topology UNIV geotop_euclidean_topology N)
              \<and> a \<in> N
              \<and> b \<in> N"
              by (rule hbody)
          qed
        qed
      qed
    qed
    show ?thesis
      using htwo_canonical_sphere_points_same_punctured_component
    proof (elim disjE)
      assume hsame: "top1_in_same_component_on ?X ?TX x\<^sub>1 x\<^sub>2"
      show ?thesis
        by (rule hpack[OF _ _ hx\<^sub>12 hsame], (by100 simp)+)
    next
      assume hsame: "top1_in_same_component_on ?X ?TX x\<^sub>1 x\<^sub>3"
      show ?thesis
        by (rule hpack[OF _ _ hx\<^sub>13 hsame], (by100 simp)+)
    next
      assume hsame: "top1_in_same_component_on ?X ?TX x\<^sub>2 x\<^sub>3"
      show ?thesis
        by (rule hpack[OF _ _ hx\<^sub>23 hsame], (by100 simp)+)
    qed
  qed
  have hcanonical_connected_pair_cases:
      "(\<exists>N. N \<subseteq> geotop_polyhedron L - {w}
          \<and> top1_connected_on N
            (subspace_topology UNIV geotop_euclidean_topology N)
          \<and> x\<^sub>1 \<in> N \<and> x\<^sub>2 \<in> N)
      \<or> (\<exists>N. N \<subseteq> geotop_polyhedron L - {w}
          \<and> top1_connected_on N
            (subspace_topology UNIV geotop_euclidean_topology N)
          \<and> x\<^sub>1 \<in> N \<and> x\<^sub>3 \<in> N)
      \<or> (\<exists>N. N \<subseteq> geotop_polyhedron L - {w}
          \<and> top1_connected_on N
            (subspace_topology UNIV geotop_euclidean_topology N)
          \<and> x\<^sub>2 \<in> N \<and> x\<^sub>3 \<in> N)"
    using hcanonical_pair_connected_witness by (by100 blast)
  have hconnected_distinct_incident_germ_witness:
      "\<exists>S T x y N. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> x \<in> (S - {w}) \<inter> sphere w r
        \<and> y \<in> (T - {w}) \<inter> sphere w r
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> x \<in> N
        \<and> y \<in> N"
  proof -
    show ?thesis
      using hcanonical_connected_pair_cases
    proof (elim disjE exE conjE)
      fix N
      assume hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
        and hN_conn: "top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)"
        and hx\<^sub>1N: "x\<^sub>1 \<in> N"
        and hx\<^sub>2N: "x\<^sub>2 \<in> N"
      show ?thesis
        using hx\<^sub>1_edge_sphere hx\<^sub>2_edge_sphere he\<^sub>12 hN_sub hN_conn
          hx\<^sub>1N hx\<^sub>2N
        by (by100 blast)
    next
      fix N
      assume hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
        and hN_conn: "top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)"
        and hx\<^sub>1N: "x\<^sub>1 \<in> N"
        and hx\<^sub>3N: "x\<^sub>3 \<in> N"
      show ?thesis
        using hx\<^sub>1_edge_sphere hx\<^sub>3_edge_sphere he\<^sub>13 hN_sub hN_conn
          hx\<^sub>1N hx\<^sub>3N
        by (by100 blast)
    next
      fix N
      assume hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
        and hN_conn: "top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)"
        and hx\<^sub>2N: "x\<^sub>2 \<in> N"
        and hx\<^sub>3N: "x\<^sub>3 \<in> N"
      show ?thesis
        using hx\<^sub>2_edge_sphere hx\<^sub>3_edge_sphere he\<^sub>23 hN_sub hN_conn
          hx\<^sub>2N hx\<^sub>3N
        by (by100 blast)
    qed
  qed
  have hconnected_disjoint_incident_germ_witness:
      "\<exists>S T x y N. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> x \<in> (S - {w}) \<inter> sphere w r
        \<and> y \<in> (T - {w}) \<inter> sphere w r
        \<and> x \<noteq> y
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> x \<in> N
        \<and> y \<in> N"
  proof -
    obtain S T x y N where hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and hxS: "x \<in> (S - {w}) \<inter> sphere w r"
      and hyT: "y \<in> (T - {w}) \<inter> sphere w r"
      and hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
      and hN_conn: "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
      and hxN: "x \<in> N"
      and hyN: "y \<in> N"
      using hconnected_distinct_incident_germ_witness by (elim exE conjE)
    have hS_E: "S \<in> E"
      using hS he\<^sub>1E he\<^sub>2E he\<^sub>3E by (by100 blast)
    have hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
      by (rule hincident_selected_punctured_disj[OF hS_E hT hST])
    have hxy: "x \<noteq> y"
      using hST_disj hxS hyT by (by100 blast)
    show ?thesis
      apply (rule exI[where x=S])
      apply (rule exI[where x=T])
      apply (rule exI[where x=x])
      apply (rule exI[where x=y])
      apply (rule exI[where x=N])
      apply (intro conjI)
      apply (rule hS)
      apply (rule hT)
      apply (rule hST)
      apply (rule hST_disj)
      apply (rule hxS)
      apply (rule hyT)
      apply (rule hxy)
      apply (rule hN_sub)
      apply (rule hN_conn)
      apply (rule hxN)
      apply (rule hyN)
      done
  qed
  have harc_side_disjoint_sphere_germ_witness:
      "\<exists>S T C x y. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> x \<noteq> y
        \<and> x \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
  proof -
    obtain S T C x y where hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
      and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and hxS: "x \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      and hxC: "x \<in> C - {w}"
      and hyC: "y \<in> C - {w}"
      and hC_conn: "top1_connected_on (C - {w})
        (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      using htwo_selected_sphere_germs_connected_in_arc_side by (elim exE conjE)
    have hS_E: "S \<in> E"
      using hS he\<^sub>1E he\<^sub>2E he\<^sub>3E by (by100 blast)
    have hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
      by (rule hincident_selected_punctured_disj[OF hS_E hT hST])
    have hxy: "x \<noteq> y"
      using hST_disj hxS hyT by (by100 blast)
    show ?thesis
      apply (rule exI[where x=S])
      apply (rule exI[where x=T])
      apply (rule exI[where x=C])
      apply (rule exI[where x=x])
      apply (rule exI[where x=y])
      apply (intro conjI)
      apply (rule hC)
      apply (rule hS)
      apply (rule hT)
      apply (rule hST)
      apply (rule hST_disj)
      apply (rule hxS)
      apply (rule hyT)
      apply (rule hxy)
      apply (rule hxC)
      apply (rule hyC)
      apply (rule hC_conn)
      done
  qed
  have hcanonical_arc_side_disjoint_sphere_germ_witness:
      "\<exists>S T C a b. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> a \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> b \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> a \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> a \<noteq> b
        \<and> a \<in> C - {w}
        \<and> b \<in> C - {w}
        \<and> top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
  proof -
    obtain S T C a b where hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
      and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
      and haS: "a \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hbT: "b \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      and hab: "a \<noteq> b"
      and haC: "a \<in> C - {w}"
      and hbC: "b \<in> C - {w}"
      and hC_conn: "top1_connected_on (C - {w})
        (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      using harc_side_disjoint_sphere_germ_witness by (elim exE conjE)
    have ha_can: "a \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      by (rule hselected_sphere_germ_point_canonical[OF hS haS])
    have hb_can: "b \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      by (rule hselected_sphere_germ_point_canonical[OF hT hbT])
    show ?thesis
      apply (rule exI[where x=S])
      apply (rule exI[where x=T])
      apply (rule exI[where x=C])
      apply (rule exI[where x=a])
      apply (rule exI[where x=b])
      apply (intro conjI)
      apply (rule hC)
      apply (rule hS)
      apply (rule hT)
      apply (rule hST)
      apply (rule hST_disj)
      apply (rule haS)
      apply (rule hbT)
      apply (rule ha_can)
      apply (rule hb_can)
      apply (rule hab)
      apply (rule haC)
      apply (rule hbC)
      apply (rule hC_conn)
      done
  qed
  have hcanonical_arc_side_disjoint_pair_cases:
      "(\<exists>C. C \<in> {A\<^sub>1, A\<^sub>2}
          \<and> x\<^sub>1 \<in> C - {w}
          \<and> x\<^sub>2 \<in> C - {w}
          \<and> top1_connected_on (C - {w})
            (subspace_topology UNIV geotop_euclidean_topology (C - {w})))
      \<or> (\<exists>C. C \<in> {A\<^sub>1, A\<^sub>2}
          \<and> x\<^sub>1 \<in> C - {w}
          \<and> x\<^sub>3 \<in> C - {w}
          \<and> top1_connected_on (C - {w})
            (subspace_topology UNIV geotop_euclidean_topology (C - {w})))
      \<or> (\<exists>C. C \<in> {A\<^sub>1, A\<^sub>2}
          \<and> x\<^sub>2 \<in> C - {w}
          \<and> x\<^sub>3 \<in> C - {w}
          \<and> top1_connected_on (C - {w})
            (subspace_topology UNIV geotop_euclidean_topology (C - {w})))"
  proof -
    obtain S T C a b where hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
      and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and haS: "a \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hbT: "b \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      and haC: "a \<in> C - {w}"
      and hbC: "b \<in> C - {w}"
      and hC_conn: "top1_connected_on (C - {w})
        (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      using hcanonical_arc_side_disjoint_sphere_germ_witness by (elim exE conjE)
    have ha_by_edge:
        "(S = e\<^sub>1 \<and> a = x\<^sub>1)
        \<or> (S = e\<^sub>2 \<and> a = x\<^sub>2)
        \<or> (S = e\<^sub>3 \<and> a = x\<^sub>3)"
      by (rule hselected_sphere_germ_edge_point_cases[OF hS haS])
    have hb_by_edge:
        "(T = e\<^sub>1 \<and> b = x\<^sub>1)
        \<or> (T = e\<^sub>2 \<and> b = x\<^sub>2)
        \<or> (T = e\<^sub>3 \<and> b = x\<^sub>3)"
      by (rule hselected_sphere_germ_edge_point_cases[OF hT hbT])
    have hpack12:
        "x\<^sub>1 \<in> C - {w} \<Longrightarrow> x\<^sub>2 \<in> C - {w} \<Longrightarrow> ?thesis"
    proof -
      assume hx\<^sub>1C: "x\<^sub>1 \<in> C - {w}"
      assume hx\<^sub>2C: "x\<^sub>2 \<in> C - {w}"
      have hbody:
          "C \<in> {A\<^sub>1, A\<^sub>2}
          \<and> x\<^sub>1 \<in> C - {w}
          \<and> x\<^sub>2 \<in> C - {w}
          \<and> top1_connected_on (C - {w})
            (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      proof (intro conjI)
        show "C \<in> {A\<^sub>1, A\<^sub>2}" by (rule hC)
        show "x\<^sub>1 \<in> C - {w}" by (rule hx\<^sub>1C)
        show "x\<^sub>2 \<in> C - {w}" by (rule hx\<^sub>2C)
        show "top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
          by (rule hC_conn)
      qed
      show ?thesis
      proof (rule disjI1)
        show "\<exists>C. C \<in> {A\<^sub>1, A\<^sub>2}
          \<and> x\<^sub>1 \<in> C - {w}
          \<and> x\<^sub>2 \<in> C - {w}
          \<and> top1_connected_on (C - {w})
            (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
          by (rule exI[where x=C], rule hbody)
      qed
    qed
    have hpack13:
        "x\<^sub>1 \<in> C - {w} \<Longrightarrow> x\<^sub>3 \<in> C - {w} \<Longrightarrow> ?thesis"
    proof -
      assume hx\<^sub>1C: "x\<^sub>1 \<in> C - {w}"
      assume hx\<^sub>3C: "x\<^sub>3 \<in> C - {w}"
      have hbody:
          "C \<in> {A\<^sub>1, A\<^sub>2}
          \<and> x\<^sub>1 \<in> C - {w}
          \<and> x\<^sub>3 \<in> C - {w}
          \<and> top1_connected_on (C - {w})
            (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      proof (intro conjI)
        show "C \<in> {A\<^sub>1, A\<^sub>2}" by (rule hC)
        show "x\<^sub>1 \<in> C - {w}" by (rule hx\<^sub>1C)
        show "x\<^sub>3 \<in> C - {w}" by (rule hx\<^sub>3C)
        show "top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
          by (rule hC_conn)
      qed
      show ?thesis
      proof (rule disjI2, rule disjI1)
        show "\<exists>C. C \<in> {A\<^sub>1, A\<^sub>2}
          \<and> x\<^sub>1 \<in> C - {w}
          \<and> x\<^sub>3 \<in> C - {w}
          \<and> top1_connected_on (C - {w})
            (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
          by (rule exI[where x=C], rule hbody)
      qed
    qed
    have hpack23:
        "x\<^sub>2 \<in> C - {w} \<Longrightarrow> x\<^sub>3 \<in> C - {w} \<Longrightarrow> ?thesis"
    proof -
      assume hx\<^sub>2C: "x\<^sub>2 \<in> C - {w}"
      assume hx\<^sub>3C: "x\<^sub>3 \<in> C - {w}"
      have hbody:
          "C \<in> {A\<^sub>1, A\<^sub>2}
          \<and> x\<^sub>2 \<in> C - {w}
          \<and> x\<^sub>3 \<in> C - {w}
          \<and> top1_connected_on (C - {w})
            (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      proof (intro conjI)
        show "C \<in> {A\<^sub>1, A\<^sub>2}" by (rule hC)
        show "x\<^sub>2 \<in> C - {w}" by (rule hx\<^sub>2C)
        show "x\<^sub>3 \<in> C - {w}" by (rule hx\<^sub>3C)
        show "top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
          by (rule hC_conn)
      qed
      show ?thesis
      proof (rule disjI2, rule disjI2)
        show "\<exists>C. C \<in> {A\<^sub>1, A\<^sub>2}
          \<and> x\<^sub>2 \<in> C - {w}
          \<and> x\<^sub>3 \<in> C - {w}
          \<and> top1_connected_on (C - {w})
            (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
          by (rule exI[where x=C], rule hbody)
      qed
    qed
    show ?thesis
      using ha_by_edge
    proof (elim disjE conjE)
      assume hS_eq: "S = e\<^sub>1" and ha_eq: "a = x\<^sub>1"
      show ?thesis
        using hb_by_edge
      proof (elim disjE conjE)
        assume hT_eq: "T = e\<^sub>1" and hb_eq: "b = x\<^sub>1"
        have False
          using hST hS_eq hT_eq by (by100 simp)
        then show ?thesis by (by100 simp)
      next
        assume hT_eq: "T = e\<^sub>2" and hb_eq: "b = x\<^sub>2"
        have hx\<^sub>1C: "x\<^sub>1 \<in> C - {w}"
          using haC ha_eq by (by100 simp)
        have hx\<^sub>2C: "x\<^sub>2 \<in> C - {w}"
          using hbC hb_eq by (by100 simp)
        show ?thesis by (rule hpack12[OF hx\<^sub>1C hx\<^sub>2C])
      next
        assume hT_eq: "T = e\<^sub>3" and hb_eq: "b = x\<^sub>3"
        have hx\<^sub>1C: "x\<^sub>1 \<in> C - {w}"
          using haC ha_eq by (by100 simp)
        have hx\<^sub>3C: "x\<^sub>3 \<in> C - {w}"
          using hbC hb_eq by (by100 simp)
        show ?thesis by (rule hpack13[OF hx\<^sub>1C hx\<^sub>3C])
      qed
    next
      assume hS_eq: "S = e\<^sub>2" and ha_eq: "a = x\<^sub>2"
      show ?thesis
        using hb_by_edge
      proof (elim disjE conjE)
        assume hT_eq: "T = e\<^sub>1" and hb_eq: "b = x\<^sub>1"
        have hx\<^sub>1C: "x\<^sub>1 \<in> C - {w}"
          using hbC hb_eq by (by100 simp)
        have hx\<^sub>2C: "x\<^sub>2 \<in> C - {w}"
          using haC ha_eq by (by100 simp)
        show ?thesis by (rule hpack12[OF hx\<^sub>1C hx\<^sub>2C])
      next
        assume hT_eq: "T = e\<^sub>2" and hb_eq: "b = x\<^sub>2"
        have False
          using hST hS_eq hT_eq by (by100 simp)
        then show ?thesis by (by100 simp)
      next
        assume hT_eq: "T = e\<^sub>3" and hb_eq: "b = x\<^sub>3"
        have hx\<^sub>2C: "x\<^sub>2 \<in> C - {w}"
          using haC ha_eq by (by100 simp)
        have hx\<^sub>3C: "x\<^sub>3 \<in> C - {w}"
          using hbC hb_eq by (by100 simp)
        show ?thesis by (rule hpack23[OF hx\<^sub>2C hx\<^sub>3C])
      qed
    next
      assume hS_eq: "S = e\<^sub>3" and ha_eq: "a = x\<^sub>3"
      show ?thesis
        using hb_by_edge
      proof (elim disjE conjE)
        assume hT_eq: "T = e\<^sub>1" and hb_eq: "b = x\<^sub>1"
        have hx\<^sub>1C: "x\<^sub>1 \<in> C - {w}"
          using hbC hb_eq by (by100 simp)
        have hx\<^sub>3C: "x\<^sub>3 \<in> C - {w}"
          using haC ha_eq by (by100 simp)
        show ?thesis by (rule hpack13[OF hx\<^sub>1C hx\<^sub>3C])
      next
        assume hT_eq: "T = e\<^sub>2" and hb_eq: "b = x\<^sub>2"
        have hx\<^sub>2C: "x\<^sub>2 \<in> C - {w}"
          using hbC hb_eq by (by100 simp)
        have hx\<^sub>3C: "x\<^sub>3 \<in> C - {w}"
          using haC ha_eq by (by100 simp)
        show ?thesis by (rule hpack23[OF hx\<^sub>2C hx\<^sub>3C])
      next
        assume hT_eq: "T = e\<^sub>3" and hb_eq: "b = x\<^sub>3"
        have False
          using hST hS_eq hT_eq by (by100 simp)
        then show ?thesis by (by100 simp)
      qed
    qed
  qed
  have hcanonical_pair_arc_side_interior_cut:
      "\<exists>C p y. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> p \<noteq> y
        \<and> p \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))
        \<and> \<not> top1_connected_on (C - {p})
          (subspace_topology UNIV geotop_euclidean_topology (C - {p}))"
  proof -
    have hside_cut:
        "\<And>C p. C \<in> {A\<^sub>1, A\<^sub>2}
          \<Longrightarrow> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<Longrightarrow> p \<in> C - {w}
          \<Longrightarrow> \<not> top1_connected_on (C - {p})
            (subspace_topology UNIV geotop_euclidean_topology (C - {p}))"
    proof -
      fix C p
      assume hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
      assume hp_set: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      assume hpC: "p \<in> C - {w}"
      have hp_not_ep: "p \<notin> {w, q\<^sub>1}"
        using hp_set hpC hx\<^sub>1_ne_q\<^sub>1 hx\<^sub>2_ne_q\<^sub>1 hx\<^sub>3_ne_q\<^sub>1 by (by100 blast)
      show "\<not> top1_connected_on (C - {p})
        (subspace_topology UNIV geotop_euclidean_topology (C - {p}))"
      proof (cases "C = A\<^sub>1")
        case True
        have hpA\<^sub>1: "p \<in> A\<^sub>1"
          using hpC True by (by100 blast)
        show ?thesis
          unfolding True
          by (rule top1_arc_non_endpoint_removal_disconnected_prefix
              [OF hA\<^sub>1_ep hpA\<^sub>1 hp_not_ep])
      next
        case False
        have hC_eq: "C = A\<^sub>2"
          using hC False by (by100 simp)
        have hpA\<^sub>2: "p \<in> A\<^sub>2"
          using hpC hC_eq by (by100 blast)
        show ?thesis
          unfolding hC_eq
          by (rule top1_arc_non_endpoint_removal_disconnected_prefix
              [OF hA\<^sub>2_ep hpA\<^sub>2 hp_not_ep])
      qed
    qed
    have hpack:
        "\<And>C p y. C \<in> {A\<^sub>1, A\<^sub>2}
          \<Longrightarrow> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<Longrightarrow> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<Longrightarrow> p \<noteq> y
          \<Longrightarrow> p \<in> C - {w}
          \<Longrightarrow> y \<in> C - {w}
          \<Longrightarrow> top1_connected_on (C - {w})
            (subspace_topology UNIV geotop_euclidean_topology (C - {w}))
          \<Longrightarrow> \<exists>C p y. C \<in> {A\<^sub>1, A\<^sub>2}
            \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
            \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
            \<and> p \<noteq> y
            \<and> p \<in> C - {w}
            \<and> y \<in> C - {w}
            \<and> top1_connected_on (C - {w})
              (subspace_topology UNIV geotop_euclidean_topology (C - {w}))
            \<and> \<not> top1_connected_on (C - {p})
              (subspace_topology UNIV geotop_euclidean_topology (C - {p}))"
    proof -
      fix C p y
      assume hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
      assume hp_set: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      assume hy_set: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      assume hpy: "p \<noteq> y"
      assume hpC: "p \<in> C - {w}"
      assume hyC: "y \<in> C - {w}"
      assume hC_conn: "top1_connected_on (C - {w})
        (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      have hdisc: "\<not> top1_connected_on (C - {p})
        (subspace_topology UNIV geotop_euclidean_topology (C - {p}))"
        by (rule hside_cut[OF hC hp_set hpC])
      have hbody: "C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> p \<noteq> y
        \<and> p \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))
        \<and> \<not> top1_connected_on (C - {p})
          (subspace_topology UNIV geotop_euclidean_topology (C - {p}))"
      proof (intro conjI)
        show "C \<in> {A\<^sub>1, A\<^sub>2}" by (rule hC)
        show "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hp_set)
        show "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hy_set)
        show "p \<noteq> y" by (rule hpy)
        show "p \<in> C - {w}" by (rule hpC)
        show "y \<in> C - {w}" by (rule hyC)
        show "top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
          by (rule hC_conn)
        show "\<not> top1_connected_on (C - {p})
          (subspace_topology UNIV geotop_euclidean_topology (C - {p}))"
          by (rule hdisc)
      qed
      show "\<exists>C p y. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> p \<noteq> y
        \<and> p \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))
        \<and> \<not> top1_connected_on (C - {p})
          (subspace_topology UNIV geotop_euclidean_topology (C - {p}))"
        by (rule exI[where x=C], rule exI[where x=p],
            rule exI[where x=y], rule hbody)
    qed
    show ?thesis
      using hcanonical_arc_side_disjoint_pair_cases
    proof (elim disjE exE conjE)
      fix C
      assume hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
        and hx\<^sub>1C: "x\<^sub>1 \<in> C - {w}"
        and hx\<^sub>2C: "x\<^sub>2 \<in> C - {w}"
        and hC_conn: "top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      show ?thesis
      proof (rule hpack[OF hC _ _ hx\<^sub>12 hx\<^sub>1C hx\<^sub>2C hC_conn])
        show "x\<^sub>1 \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (by100 simp)
        show "x\<^sub>2 \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (by100 simp)
      qed
    next
      fix C
      assume hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
        and hx\<^sub>1C: "x\<^sub>1 \<in> C - {w}"
        and hx\<^sub>3C: "x\<^sub>3 \<in> C - {w}"
        and hC_conn: "top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      show ?thesis
      proof (rule hpack[OF hC _ _ hx\<^sub>13 hx\<^sub>1C hx\<^sub>3C hC_conn])
        show "x\<^sub>1 \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (by100 simp)
        show "x\<^sub>3 \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (by100 simp)
      qed
    next
      fix C
      assume hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
        and hx\<^sub>2C: "x\<^sub>2 \<in> C - {w}"
        and hx\<^sub>3C: "x\<^sub>3 \<in> C - {w}"
        and hC_conn: "top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      show ?thesis
      proof (rule hpack[OF hC _ _ hx\<^sub>23 hx\<^sub>2C hx\<^sub>3C hC_conn])
        show "x\<^sub>2 \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (by100 simp)
        show "x\<^sub>3 \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (by100 simp)
      qed
    qed
  qed
  have hcanonical_pair_arc_side_cut_separation:
      "\<exists>C p y U V. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> p \<noteq> y
        \<and> p \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> top1_connected_on (C - {w})
          (subspace_topology UNIV geotop_euclidean_topology (C - {w}))
        \<and> top1_is_separation_on (C - {p})
          (subspace_topology UNIV geotop_euclidean_topology (C - {p})) U V"
  proof -
    obtain C p y where hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
      and hp_set: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hy_set: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hpy: "p \<noteq> y"
      and hpC: "p \<in> C - {w}"
      and hyC: "y \<in> C - {w}"
      and hC_conn: "top1_connected_on (C - {w})
        (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
      and hC_minus_p_disc: "\<not> top1_connected_on (C - {p})
        (subspace_topology UNIV geotop_euclidean_topology (C - {p}))"
      using hcanonical_pair_arc_side_interior_cut by (elim exE conjE)
    have htop_UNIV: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
      using geotop_euclidean_topology_UNIV_strict
      unfolding is_topology_on_strict_def by (by100 blast)
    have htop_Cp: "is_topology_on (C - {p})
        (subspace_topology UNIV geotop_euclidean_topology (C - {p}))"
      by (rule subspace_topology_is_topology_on[OF htop_UNIV subset_UNIV])
    have hsep_ex: "\<exists>U V. top1_is_separation_on (C - {p})
        (subspace_topology UNIV geotop_euclidean_topology (C - {p})) U V"
      using htop_Cp hC_minus_p_disc
      unfolding Lemma_23_1 by (by100 blast)
    obtain U V where hsep: "top1_is_separation_on (C - {p})
        (subspace_topology UNIV geotop_euclidean_topology (C - {p})) U V"
      using hsep_ex by (elim exE)
    have hbody: "C \<in> {A\<^sub>1, A\<^sub>2}
      \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> p \<noteq> y
      \<and> p \<in> C - {w}
      \<and> y \<in> C - {w}
      \<and> top1_connected_on (C - {w})
        (subspace_topology UNIV geotop_euclidean_topology (C - {w}))
      \<and> top1_is_separation_on (C - {p})
        (subspace_topology UNIV geotop_euclidean_topology (C - {p})) U V"
    proof (intro conjI)
      show "C \<in> {A\<^sub>1, A\<^sub>2}" by (rule hC)
      show "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hp_set)
      show "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hy_set)
      show "p \<noteq> y" by (rule hpy)
      show "p \<in> C - {w}" by (rule hpC)
      show "y \<in> C - {w}" by (rule hyC)
      show "top1_connected_on (C - {w})
        (subspace_topology UNIV geotop_euclidean_topology (C - {w}))"
        by (rule hC_conn)
      show "top1_is_separation_on (C - {p})
        (subspace_topology UNIV geotop_euclidean_topology (C - {p})) U V"
        by (rule hsep)
    qed
    show ?thesis
      by (rule exI[where x=C], rule exI[where x=p], rule exI[where x=y],
          rule exI[where x=U], rule exI[where x=V], rule hbody)
  qed
  have hcanonical_pair_arc_side_split:
      "\<exists>C p y D\<^sub>w D\<^sub>q. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> p \<noteq> y
        \<and> p \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> C = D\<^sub>w \<union> D\<^sub>q
        \<and> D\<^sub>w \<inter> D\<^sub>q = {p}
        \<and> top1_is_arc_on D\<^sub>w
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)
        \<and> top1_is_arc_on D\<^sub>q
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)
        \<and> w \<in> D\<^sub>w
        \<and> q\<^sub>1 \<in> D\<^sub>q
        \<and> p \<in> D\<^sub>w
        \<and> p \<in> D\<^sub>q
        \<and> D\<^sub>w \<subseteq> UNIV
        \<and> D\<^sub>q \<subseteq> UNIV"
  proof -
    obtain C p y where hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
      and hp_set: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hy_set: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hpy: "p \<noteq> y"
      and hpC: "p \<in> C - {w}"
      and hyC: "y \<in> C - {w}"
      using hcanonical_pair_arc_side_interior_cut by (elim exE conjE)
    have hC_arc: "top1_is_arc_on C
        (subspace_topology UNIV geotop_euclidean_topology C)"
      using hC hA\<^sub>1_arc hA\<^sub>2_arc by (by100 blast)
    have hC_ep: "top1_arc_endpoints_on C
        (subspace_topology UNIV geotop_euclidean_topology C) = {w, q\<^sub>1}"
      using hC hA\<^sub>1_ep hA\<^sub>2_ep by (by100 blast)
    have hp_not_ep_set: "p \<notin> {w, q\<^sub>1}"
      using hp_set hpC hx\<^sub>1_ne_q\<^sub>1 hx\<^sub>2_ne_q\<^sub>1 hx\<^sub>3_ne_q\<^sub>1 by (by100 blast)
    have hp_not_ep: "p \<notin> top1_arc_endpoints_on C
        (subspace_topology UNIV geotop_euclidean_topology C)"
      using hC_ep hp_not_ep_set by (by100 simp)
    have hp_in_C: "p \<in> C"
      using hpC by (by100 blast)
    have hwq: "w \<noteq> q\<^sub>1"
      using hq\<^sub>1w by (by100 simp)
    obtain D\<^sub>w D\<^sub>q where hC_split: "C = D\<^sub>w \<union> D\<^sub>q"
      and hDwDq: "D\<^sub>w \<inter> D\<^sub>q = {p}"
      and hDw_arc: "top1_is_arc_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)"
      and hDq_arc: "top1_is_arc_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)"
      and hwDw: "w \<in> D\<^sub>w"
      and hqDq: "q\<^sub>1 \<in> D\<^sub>q"
      and hpDw: "p \<in> D\<^sub>w"
      and hpDq: "p \<in> D\<^sub>q"
      and hDw_sub: "D\<^sub>w \<subseteq> UNIV"
      and hDq_sub: "D\<^sub>q \<subseteq> UNIV"
      using arc_split_at_given_point
        [OF geotop_euclidean_topology_UNIV_strict
            geotop_euclidean_topology_UNIV_hausdorff subset_UNIV
            hC_arc hp_in_C hp_not_ep hC_ep hwq]
      by (elim exE conjE)
    have hbody: "C \<in> {A\<^sub>1, A\<^sub>2}
      \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> p \<noteq> y
      \<and> p \<in> C - {w}
      \<and> y \<in> C - {w}
      \<and> C = D\<^sub>w \<union> D\<^sub>q
      \<and> D\<^sub>w \<inter> D\<^sub>q = {p}
      \<and> top1_is_arc_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)
      \<and> top1_is_arc_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)
      \<and> w \<in> D\<^sub>w
      \<and> q\<^sub>1 \<in> D\<^sub>q
      \<and> p \<in> D\<^sub>w
      \<and> p \<in> D\<^sub>q
      \<and> D\<^sub>w \<subseteq> UNIV
      \<and> D\<^sub>q \<subseteq> UNIV"
    proof (intro conjI)
      show "C \<in> {A\<^sub>1, A\<^sub>2}" by (rule hC)
      show "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hp_set)
      show "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hy_set)
      show "p \<noteq> y" by (rule hpy)
      show "p \<in> C - {w}" by (rule hpC)
      show "y \<in> C - {w}" by (rule hyC)
      show "C = D\<^sub>w \<union> D\<^sub>q" by (rule hC_split)
      show "D\<^sub>w \<inter> D\<^sub>q = {p}" by (rule hDwDq)
      show "top1_is_arc_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)"
        by (rule hDw_arc)
      show "top1_is_arc_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)"
        by (rule hDq_arc)
      show "w \<in> D\<^sub>w" by (rule hwDw)
      show "q\<^sub>1 \<in> D\<^sub>q" by (rule hqDq)
      show "p \<in> D\<^sub>w" by (rule hpDw)
      show "p \<in> D\<^sub>q" by (rule hpDq)
      show "D\<^sub>w \<subseteq> UNIV" by (rule hDw_sub)
      show "D\<^sub>q \<subseteq> UNIV" by (rule hDq_sub)
    qed
    show ?thesis
      by (rule exI[where x=C], rule exI[where x=p], rule exI[where x=y],
          rule exI[where x=D\<^sub>w], rule exI[where x=D\<^sub>q], rule hbody)
  qed
  have hcanonical_pair_arc_side_split_second_point_side:
      "\<exists>C p y D\<^sub>w D\<^sub>q. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> p \<noteq> y
        \<and> p \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> C = D\<^sub>w \<union> D\<^sub>q
        \<and> D\<^sub>w \<inter> D\<^sub>q = {p}
        \<and> w \<in> D\<^sub>w
        \<and> q\<^sub>1 \<in> D\<^sub>q
        \<and> p \<in> D\<^sub>w
        \<and> p \<in> D\<^sub>q
        \<and> ((y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
          \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p}))"
  proof -
    obtain C p y D\<^sub>w D\<^sub>q where hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
      and hp_set: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hy_set: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hpy: "p \<noteq> y"
      and hpC: "p \<in> C - {w}"
      and hyC: "y \<in> C - {w}"
      and hC_split: "C = D\<^sub>w \<union> D\<^sub>q"
      and hDwDq: "D\<^sub>w \<inter> D\<^sub>q = {p}"
      and hwDw: "w \<in> D\<^sub>w"
      and hqDq: "q\<^sub>1 \<in> D\<^sub>q"
      and hpDw: "p \<in> D\<^sub>w"
      and hpDq: "p \<in> D\<^sub>q"
      using hcanonical_pair_arc_side_split by (elim exE conjE)
    have hy_in_union: "y \<in> D\<^sub>w \<union> D\<^sub>q"
      using hyC hC_split by (by100 blast)
    have hy_not_p: "y \<noteq> p"
      using hpy by (by100 simp)
    have hy_cases: "y \<in> D\<^sub>w \<or> y \<in> D\<^sub>q"
      using hy_in_union by (by100 blast)
    have hside:
        "(y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
        \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p})"
    proof (rule disjE[OF hy_cases])
      assume hyDw: "y \<in> D\<^sub>w"
      have hyDw_p: "y \<in> D\<^sub>w - {p}"
        using hyDw hy_not_p by (by100 blast)
      have hy_not_Dq_p: "y \<notin> D\<^sub>q - {p}"
      proof
        assume hyDq_p: "y \<in> D\<^sub>q - {p}"
        have "y \<in> D\<^sub>w \<inter> D\<^sub>q"
          using hyDw hyDq_p by (by100 blast)
        hence "y = p"
          using hDwDq by (by100 blast)
        thus False
          using hy_not_p by (by100 blast)
      qed
      show ?thesis
        using hyDw_p hy_not_Dq_p by (by100 blast)
    next
      assume hyDq: "y \<in> D\<^sub>q"
      have hyDq_p: "y \<in> D\<^sub>q - {p}"
        using hyDq hy_not_p by (by100 blast)
      have hy_not_Dw_p: "y \<notin> D\<^sub>w - {p}"
      proof
        assume hyDw_p: "y \<in> D\<^sub>w - {p}"
        have "y \<in> D\<^sub>w \<inter> D\<^sub>q"
          using hyDw_p hyDq by (by100 blast)
        hence "y = p"
          using hDwDq by (by100 blast)
        thus False
          using hy_not_p by (by100 blast)
      qed
      show ?thesis
        using hyDq_p hy_not_Dw_p by (by100 blast)
    qed
    have hbody: "C \<in> {A\<^sub>1, A\<^sub>2}
      \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> p \<noteq> y
      \<and> p \<in> C - {w}
      \<and> y \<in> C - {w}
      \<and> C = D\<^sub>w \<union> D\<^sub>q
      \<and> D\<^sub>w \<inter> D\<^sub>q = {p}
      \<and> w \<in> D\<^sub>w
      \<and> q\<^sub>1 \<in> D\<^sub>q
      \<and> p \<in> D\<^sub>w
      \<and> p \<in> D\<^sub>q
      \<and> ((y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
        \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p}))"
    proof (intro conjI)
      show "C \<in> {A\<^sub>1, A\<^sub>2}" by (rule hC)
      show "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hp_set)
      show "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hy_set)
      show "p \<noteq> y" by (rule hpy)
      show "p \<in> C - {w}" by (rule hpC)
      show "y \<in> C - {w}" by (rule hyC)
      show "C = D\<^sub>w \<union> D\<^sub>q" by (rule hC_split)
      show "D\<^sub>w \<inter> D\<^sub>q = {p}" by (rule hDwDq)
      show "w \<in> D\<^sub>w" by (rule hwDw)
      show "q\<^sub>1 \<in> D\<^sub>q" by (rule hqDq)
      show "p \<in> D\<^sub>w" by (rule hpDw)
      show "p \<in> D\<^sub>q" by (rule hpDq)
      show "(y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
          \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p})"
        by (rule hside)
    qed
    show ?thesis
      by (rule exI[where x=C], rule exI[where x=p], rule exI[where x=y],
          rule exI[where x=D\<^sub>w], rule exI[where x=D\<^sub>q], rule hbody)
  qed
  have hcanonical_pair_arc_side_split_endpoints:
      "\<exists>C p y D\<^sub>w D\<^sub>q. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> p \<noteq> y
        \<and> p \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> C = D\<^sub>w \<union> D\<^sub>q
        \<and> D\<^sub>w \<inter> D\<^sub>q = {p}
        \<and> top1_is_arc_on D\<^sub>w
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)
        \<and> top1_is_arc_on D\<^sub>q
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)
        \<and> top1_arc_endpoints_on D\<^sub>w
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w) = {w, p}
        \<and> top1_arc_endpoints_on D\<^sub>q
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q) = {p, q\<^sub>1}
        \<and> ((y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
          \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p}))"
  proof -
    obtain C p y D\<^sub>w D\<^sub>q where hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
      and hp_set: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hy_set: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hpy: "p \<noteq> y"
      and hpC: "p \<in> C - {w}"
      and hyC: "y \<in> C - {w}"
      and hC_split: "C = D\<^sub>w \<union> D\<^sub>q"
      and hDwDq: "D\<^sub>w \<inter> D\<^sub>q = {p}"
      and hDw_arc: "top1_is_arc_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)"
      and hDq_arc: "top1_is_arc_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)"
      and hwDw: "w \<in> D\<^sub>w"
      and hqDq: "q\<^sub>1 \<in> D\<^sub>q"
      and hpDw: "p \<in> D\<^sub>w"
      and hpDq: "p \<in> D\<^sub>q"
      and hDw_sub: "D\<^sub>w \<subseteq> UNIV"
      and hDq_sub: "D\<^sub>q \<subseteq> UNIV"
      using hcanonical_pair_arc_side_split by (elim exE conjE)
    have hC_arc: "top1_is_arc_on C
        (subspace_topology UNIV geotop_euclidean_topology C)"
      using hC hA\<^sub>1_arc hA\<^sub>2_arc by (by100 blast)
    have hC_ep: "top1_arc_endpoints_on C
        (subspace_topology UNIV geotop_euclidean_topology C) = {w, q\<^sub>1}"
      using hC hA\<^sub>1_ep hA\<^sub>2_ep by (by100 blast)
    have hp_not_ep_set: "p \<notin> {w, q\<^sub>1}"
      using hp_set hpC hx\<^sub>1_ne_q\<^sub>1 hx\<^sub>2_ne_q\<^sub>1 hx\<^sub>3_ne_q\<^sub>1 by (by100 blast)
    have hp_not_ep: "p \<notin> top1_arc_endpoints_on C
        (subspace_topology UNIV geotop_euclidean_topology C)"
      using hC_ep hp_not_ep_set by (by100 simp)
    have hDw_ep: "top1_arc_endpoints_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w) = {w, p}"
      by (rule arc_split_endpoints(1)
        [OF geotop_euclidean_topology_UNIV_strict
            geotop_euclidean_topology_UNIV_hausdorff subset_UNIV
            hC_arc hC_split hDwDq hDw_arc hDq_arc hwDw hqDq hpDw hpDq
            hDw_sub hDq_sub hC_ep hp_not_ep])
    have hDq_ep: "top1_arc_endpoints_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q) = {p, q\<^sub>1}"
      by (rule arc_split_endpoints(2)
        [OF geotop_euclidean_topology_UNIV_strict
            geotop_euclidean_topology_UNIV_hausdorff subset_UNIV
            hC_arc hC_split hDwDq hDw_arc hDq_arc hwDw hqDq hpDw hpDq
            hDw_sub hDq_sub hC_ep hp_not_ep])
    have hy_in_union: "y \<in> D\<^sub>w \<union> D\<^sub>q"
      using hyC hC_split by (by100 blast)
    have hy_not_p: "y \<noteq> p"
      using hpy by (by100 simp)
    have hy_cases: "y \<in> D\<^sub>w \<or> y \<in> D\<^sub>q"
      using hy_in_union by (by100 blast)
    have hside:
        "(y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
        \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p})"
    proof (rule disjE[OF hy_cases])
      assume hyDw: "y \<in> D\<^sub>w"
      have hyDw_p: "y \<in> D\<^sub>w - {p}"
        using hyDw hy_not_p by (by100 blast)
      have hy_not_Dq_p: "y \<notin> D\<^sub>q - {p}"
      proof
        assume hyDq_p: "y \<in> D\<^sub>q - {p}"
        have "y \<in> D\<^sub>w \<inter> D\<^sub>q"
          using hyDw hyDq_p by (by100 blast)
        hence "y = p"
          using hDwDq by (by100 blast)
        thus False
          using hy_not_p by (by100 blast)
      qed
      show ?thesis
        using hyDw_p hy_not_Dq_p by (by100 blast)
    next
      assume hyDq: "y \<in> D\<^sub>q"
      have hyDq_p: "y \<in> D\<^sub>q - {p}"
        using hyDq hy_not_p by (by100 blast)
      have hy_not_Dw_p: "y \<notin> D\<^sub>w - {p}"
      proof
        assume hyDw_p: "y \<in> D\<^sub>w - {p}"
        have "y \<in> D\<^sub>w \<inter> D\<^sub>q"
          using hyDw_p hyDq by (by100 blast)
        hence "y = p"
          using hDwDq by (by100 blast)
        thus False
          using hy_not_p by (by100 blast)
      qed
      show ?thesis
        using hyDq_p hy_not_Dw_p by (by100 blast)
    qed
    have hbody: "C \<in> {A\<^sub>1, A\<^sub>2}
      \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> p \<noteq> y
      \<and> p \<in> C - {w}
      \<and> y \<in> C - {w}
      \<and> C = D\<^sub>w \<union> D\<^sub>q
      \<and> D\<^sub>w \<inter> D\<^sub>q = {p}
      \<and> top1_is_arc_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)
      \<and> top1_is_arc_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)
      \<and> top1_arc_endpoints_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w) = {w, p}
      \<and> top1_arc_endpoints_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q) = {p, q\<^sub>1}
      \<and> ((y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
        \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p}))"
    proof (intro conjI)
      show "C \<in> {A\<^sub>1, A\<^sub>2}" by (rule hC)
      show "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hp_set)
      show "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hy_set)
      show "p \<noteq> y" by (rule hpy)
      show "p \<in> C - {w}" by (rule hpC)
      show "y \<in> C - {w}" by (rule hyC)
      show "C = D\<^sub>w \<union> D\<^sub>q" by (rule hC_split)
      show "D\<^sub>w \<inter> D\<^sub>q = {p}" by (rule hDwDq)
      show "top1_is_arc_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)"
        by (rule hDw_arc)
      show "top1_is_arc_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)"
        by (rule hDq_arc)
      show "top1_arc_endpoints_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w) = {w, p}"
        by (rule hDw_ep)
      show "top1_arc_endpoints_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q) = {p, q\<^sub>1}"
        by (rule hDq_ep)
      show "(y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
          \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p})"
        by (rule hside)
    qed
    show ?thesis
      by (rule exI[where x=C], rule exI[where x=p], rule exI[where x=y],
          rule exI[where x=D\<^sub>w], rule exI[where x=D\<^sub>q], rule hbody)
  qed
  have hcanonical_pair_arc_side_split_selected_germs:
      "\<exists>S T C p y D\<^sub>w D\<^sub>q. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> p \<noteq> y
        \<and> p \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> C = D\<^sub>w \<union> D\<^sub>q
        \<and> D\<^sub>w \<inter> D\<^sub>q = {p}
        \<and> top1_is_arc_on D\<^sub>w
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)
        \<and> top1_is_arc_on D\<^sub>q
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)
        \<and> top1_arc_endpoints_on D\<^sub>w
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w) = {w, p}
        \<and> top1_arc_endpoints_on D\<^sub>q
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q) = {p, q\<^sub>1}
        \<and> ((y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
          \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p}))"
  proof -
    obtain C p y D\<^sub>w D\<^sub>q where hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
      and hp_set: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hy_set: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hpy: "p \<noteq> y"
      and hpC: "p \<in> C - {w}"
      and hyC: "y \<in> C - {w}"
      and hC_split: "C = D\<^sub>w \<union> D\<^sub>q"
      and hDwDq: "D\<^sub>w \<inter> D\<^sub>q = {p}"
      and hDw_arc: "top1_is_arc_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)"
      and hDq_arc: "top1_is_arc_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)"
      and hDw_ep: "top1_arc_endpoints_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w) = {w, p}"
      and hDq_ep: "top1_arc_endpoints_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q) = {p, q\<^sub>1}"
      and hside: "(y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
        \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p})"
      using hcanonical_pair_arc_side_split_endpoints by (elim exE conjE)
    have hpoint_germ:
        "\<And>z. z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<Longrightarrow> \<exists>S. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> z \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
            \<and> ((S = e\<^sub>1 \<and> z = x\<^sub>1)
              \<or> (S = e\<^sub>2 \<and> z = x\<^sub>2)
              \<or> (S = e\<^sub>3 \<and> z = x\<^sub>3))"
    proof -
      fix z
      assume hz: "z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      have hz_cases: "z = x\<^sub>1 \<or> z = x\<^sub>2 \<or> z = x\<^sub>3"
        using hz by (by100 simp)
      show "\<exists>S. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> z \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> ((S = e\<^sub>1 \<and> z = x\<^sub>1)
          \<or> (S = e\<^sub>2 \<and> z = x\<^sub>2)
          \<or> (S = e\<^sub>3 \<and> z = x\<^sub>3))"
        using hz_cases
      proof (elim disjE)
        assume hz_eq: "z = x\<^sub>1"
        have hz_germ: "z \<in> (e\<^sub>1 - {w, q\<^sub>1}) \<inter> sphere w r"
          using hz_eq hx\<^sub>1_edge_sphere hx\<^sub>1_ne_q\<^sub>1 by (by100 blast)
        have hbody: "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> z \<in> (e\<^sub>1 - {w, q\<^sub>1}) \<inter> sphere w r
          \<and> ((e\<^sub>1 = e\<^sub>1 \<and> z = x\<^sub>1)
            \<or> (e\<^sub>1 = e\<^sub>2 \<and> z = x\<^sub>2)
            \<or> (e\<^sub>1 = e\<^sub>3 \<and> z = x\<^sub>3))"
          using hz_eq hz_germ by (by100 simp)
        show ?thesis
          by (rule exI[where x=e\<^sub>1], rule hbody)
      next
        assume hz_eq: "z = x\<^sub>2"
        have hz_germ: "z \<in> (e\<^sub>2 - {w, q\<^sub>1}) \<inter> sphere w r"
          using hz_eq hx\<^sub>2_edge_sphere hx\<^sub>2_ne_q\<^sub>1 by (by100 blast)
        have hbody: "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> z \<in> (e\<^sub>2 - {w, q\<^sub>1}) \<inter> sphere w r
          \<and> ((e\<^sub>2 = e\<^sub>1 \<and> z = x\<^sub>1)
            \<or> (e\<^sub>2 = e\<^sub>2 \<and> z = x\<^sub>2)
            \<or> (e\<^sub>2 = e\<^sub>3 \<and> z = x\<^sub>3))"
          using hz_eq hz_germ by (by100 simp)
        show ?thesis
          by (rule exI[where x=e\<^sub>2], rule hbody)
      next
        assume hz_eq: "z = x\<^sub>3"
        have hz_germ: "z \<in> (e\<^sub>3 - {w, q\<^sub>1}) \<inter> sphere w r"
          using hz_eq hx\<^sub>3_edge_sphere hx\<^sub>3_ne_q\<^sub>1 by (by100 blast)
        have hbody: "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> z \<in> (e\<^sub>3 - {w, q\<^sub>1}) \<inter> sphere w r
          \<and> ((e\<^sub>3 = e\<^sub>1 \<and> z = x\<^sub>1)
            \<or> (e\<^sub>3 = e\<^sub>2 \<and> z = x\<^sub>2)
            \<or> (e\<^sub>3 = e\<^sub>3 \<and> z = x\<^sub>3))"
          using hz_eq hz_germ by (by100 simp)
        show ?thesis
          by (rule exI[where x=e\<^sub>3], rule hbody)
      qed
    qed
    obtain S where hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hpS: "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hp_by_S: "(S = e\<^sub>1 \<and> p = x\<^sub>1)
        \<or> (S = e\<^sub>2 \<and> p = x\<^sub>2)
        \<or> (S = e\<^sub>3 \<and> p = x\<^sub>3)"
      using hpoint_germ[OF hp_set] by (elim exE conjE)
    obtain T where hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      and hy_by_T: "(T = e\<^sub>1 \<and> y = x\<^sub>1)
        \<or> (T = e\<^sub>2 \<and> y = x\<^sub>2)
        \<or> (T = e\<^sub>3 \<and> y = x\<^sub>3)"
      using hpoint_germ[OF hy_set] by (elim exE conjE)
    have hST: "S \<noteq> T"
    proof
      assume hST_eq: "S = T"
      have "p = y"
        using hp_by_S hy_by_T hST_eq he\<^sub>12 he\<^sub>13 he\<^sub>23 by (by100 blast)
      then show False
        using hpy by (by100 blast)
    qed
    have hS_E: "S \<in> E"
      using hS he\<^sub>1E he\<^sub>2E he\<^sub>3E by (by100 blast)
    have hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
      by (rule hincident_selected_punctured_disj[OF hS_E hT hST])
    have hbody: "C \<in> {A\<^sub>1, A\<^sub>2}
      \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> S \<noteq> T
      \<and> (S - {w}) \<inter> (T - {w}) = {}
      \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> p \<noteq> y
      \<and> p \<in> C - {w}
      \<and> y \<in> C - {w}
      \<and> C = D\<^sub>w \<union> D\<^sub>q
      \<and> D\<^sub>w \<inter> D\<^sub>q = {p}
      \<and> top1_is_arc_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)
      \<and> top1_is_arc_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)
      \<and> top1_arc_endpoints_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w) = {w, p}
      \<and> top1_arc_endpoints_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q) = {p, q\<^sub>1}
      \<and> ((y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
        \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p}))"
    proof (intro conjI)
      show "C \<in> {A\<^sub>1, A\<^sub>2}" by (rule hC)
      show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
      show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
      show "S \<noteq> T" by (rule hST)
      show "(S - {w}) \<inter> (T - {w}) = {}" by (rule hST_disj)
      show "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hpS)
      show "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hyT)
      show "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hp_set)
      show "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hy_set)
      show "p \<noteq> y" by (rule hpy)
      show "p \<in> C - {w}" by (rule hpC)
      show "y \<in> C - {w}" by (rule hyC)
      show "C = D\<^sub>w \<union> D\<^sub>q" by (rule hC_split)
      show "D\<^sub>w \<inter> D\<^sub>q = {p}" by (rule hDwDq)
      show "top1_is_arc_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)"
        by (rule hDw_arc)
      show "top1_is_arc_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)"
        by (rule hDq_arc)
      show "top1_arc_endpoints_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w) = {w, p}"
        by (rule hDw_ep)
      show "top1_arc_endpoints_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q) = {p, q\<^sub>1}"
        by (rule hDq_ep)
      show "(y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
          \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p})"
        by (rule hside)
    qed
    show ?thesis
      by (rule exI[where x=S], rule exI[where x=T], rule exI[where x=C],
          rule exI[where x=p], rule exI[where x=y],
          rule exI[where x=D\<^sub>w], rule exI[where x=D\<^sub>q], rule hbody)
  qed
  have hcanonical_pair_arc_side_split_selected_germs_clean:
      "\<exists>S T C p y D\<^sub>w D\<^sub>q. C \<in> {A\<^sub>1, A\<^sub>2}
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> p \<noteq> y
        \<and> p \<in> C - {w}
        \<and> y \<in> C - {w}
        \<and> C = D\<^sub>w \<union> D\<^sub>q
        \<and> D\<^sub>w \<inter> D\<^sub>q = {p}
        \<and> top1_is_arc_on D\<^sub>w
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)
        \<and> top1_is_arc_on D\<^sub>q
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)
        \<and> top1_arc_endpoints_on D\<^sub>w
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w) = {w, p}
        \<and> top1_arc_endpoints_on D\<^sub>q
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q) = {p, q\<^sub>1}
        \<and> w \<in> D\<^sub>w
        \<and> p \<in> D\<^sub>w
        \<and> p \<in> D\<^sub>q
        \<and> q\<^sub>1 \<in> D\<^sub>q
        \<and> w \<notin> D\<^sub>q
        \<and> q\<^sub>1 \<notin> D\<^sub>w
        \<and> ((y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
          \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p}))"
  proof -
    obtain S T C p y D\<^sub>w D\<^sub>q where hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
      and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
      and hpS: "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      and hp_set: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hy_set: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hpy: "p \<noteq> y"
      and hpC: "p \<in> C - {w}"
      and hyC: "y \<in> C - {w}"
      and hC_split: "C = D\<^sub>w \<union> D\<^sub>q"
      and hDwDq: "D\<^sub>w \<inter> D\<^sub>q = {p}"
      and hDw_arc: "top1_is_arc_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)"
      and hDq_arc: "top1_is_arc_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)"
      and hDw_ep: "top1_arc_endpoints_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w) = {w, p}"
      and hDq_ep: "top1_arc_endpoints_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q) = {p, q\<^sub>1}"
      and hside: "(y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
        \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p})"
      using hcanonical_pair_arc_side_split_selected_germs by (elim exE conjE)
    have hwDw: "w \<in> D\<^sub>w"
      using hDw_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
    have hpDw: "p \<in> D\<^sub>w"
      using hDw_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
    have hpDq: "p \<in> D\<^sub>q"
      using hDq_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
    have hqDq: "q\<^sub>1 \<in> D\<^sub>q"
      using hDq_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
    have hp_ne_w: "p \<noteq> w"
      using hpS by (by100 blast)
    have hp_ne_q\<^sub>1: "p \<noteq> q\<^sub>1"
      using hpS by (by100 blast)
    have hw_not_Dq: "w \<notin> D\<^sub>q"
    proof
      assume hwDq: "w \<in> D\<^sub>q"
      have "w \<in> D\<^sub>w \<inter> D\<^sub>q"
        using hwDw hwDq by (by100 blast)
      hence "w = p"
        using hDwDq by (by100 blast)
      thus False
        using hp_ne_w by (by100 blast)
    qed
    have hq_not_Dw: "q\<^sub>1 \<notin> D\<^sub>w"
    proof
      assume hqDw: "q\<^sub>1 \<in> D\<^sub>w"
      have "q\<^sub>1 \<in> D\<^sub>w \<inter> D\<^sub>q"
        using hqDw hqDq by (by100 blast)
      hence "q\<^sub>1 = p"
        using hDwDq by (by100 blast)
      thus False
        using hp_ne_q\<^sub>1 by (by100 blast)
    qed
    have hbody: "C \<in> {A\<^sub>1, A\<^sub>2}
      \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> S \<noteq> T
      \<and> (S - {w}) \<inter> (T - {w}) = {}
      \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> p \<noteq> y
      \<and> p \<in> C - {w}
      \<and> y \<in> C - {w}
      \<and> C = D\<^sub>w \<union> D\<^sub>q
      \<and> D\<^sub>w \<inter> D\<^sub>q = {p}
      \<and> top1_is_arc_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)
      \<and> top1_is_arc_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)
      \<and> top1_arc_endpoints_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w) = {w, p}
      \<and> top1_arc_endpoints_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q) = {p, q\<^sub>1}
      \<and> w \<in> D\<^sub>w
      \<and> p \<in> D\<^sub>w
      \<and> p \<in> D\<^sub>q
      \<and> q\<^sub>1 \<in> D\<^sub>q
      \<and> w \<notin> D\<^sub>q
      \<and> q\<^sub>1 \<notin> D\<^sub>w
      \<and> ((y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
        \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p}))"
    proof (intro conjI)
      show "C \<in> {A\<^sub>1, A\<^sub>2}" by (rule hC)
      show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
      show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
      show "S \<noteq> T" by (rule hST)
      show "(S - {w}) \<inter> (T - {w}) = {}" by (rule hST_disj)
      show "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hpS)
      show "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hyT)
      show "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hp_set)
      show "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hy_set)
      show "p \<noteq> y" by (rule hpy)
      show "p \<in> C - {w}" by (rule hpC)
      show "y \<in> C - {w}" by (rule hyC)
      show "C = D\<^sub>w \<union> D\<^sub>q" by (rule hC_split)
      show "D\<^sub>w \<inter> D\<^sub>q = {p}" by (rule hDwDq)
      show "top1_is_arc_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)"
        by (rule hDw_arc)
      show "top1_is_arc_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)"
        by (rule hDq_arc)
      show "top1_arc_endpoints_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w) = {w, p}"
        by (rule hDw_ep)
      show "top1_arc_endpoints_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q) = {p, q\<^sub>1}"
        by (rule hDq_ep)
      show "w \<in> D\<^sub>w" by (rule hwDw)
      show "p \<in> D\<^sub>w" by (rule hpDw)
      show "p \<in> D\<^sub>q" by (rule hpDq)
      show "q\<^sub>1 \<in> D\<^sub>q" by (rule hqDq)
      show "w \<notin> D\<^sub>q" by (rule hw_not_Dq)
      show "q\<^sub>1 \<notin> D\<^sub>w" by (rule hq_not_Dw)
      show "(y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
          \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p})"
        by (rule hside)
    qed
    show ?thesis
      by (rule exI[where x=S], rule exI[where x=T], rule exI[where x=C],
          rule exI[where x=p], rule exI[where x=y],
          rule exI[where x=D\<^sub>w], rule exI[where x=D\<^sub>q], rule hbody)
  qed
  have hcanonical_pair_split_side_connected_selected_germs:
      "\<exists>S T p y N. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<noteq> y
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> p \<in> N
        \<and> y \<in> N"
  proof -
    obtain S T C p y D\<^sub>w D\<^sub>q where hC: "C \<in> {A\<^sub>1, A\<^sub>2}"
      and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
      and hpS: "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      and hpy: "p \<noteq> y"
      and hC_split: "C = D\<^sub>w \<union> D\<^sub>q"
      and hDwDq: "D\<^sub>w \<inter> D\<^sub>q = {p}"
      and hDw_arc: "top1_is_arc_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)"
      and hDq_arc: "top1_is_arc_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)"
      and hDw_ep: "top1_arc_endpoints_on D\<^sub>w
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w) = {w, p}"
      and hDq_ep: "top1_arc_endpoints_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q) = {p, q\<^sub>1}"
      and hpDw: "p \<in> D\<^sub>w"
      and hpDq: "p \<in> D\<^sub>q"
      and hw_not_Dq: "w \<notin> D\<^sub>q"
      and hside: "(y \<in> D\<^sub>w - {p} \<and> y \<notin> D\<^sub>q - {p})
        \<or> (y \<in> D\<^sub>q - {p} \<and> y \<notin> D\<^sub>w - {p})"
      using hcanonical_pair_arc_side_split_selected_germs_clean
      by (elim exE conjE)
    have hC_sub_poly: "C \<subseteq> geotop_polyhedron L"
      using hC hA_decomp by (by100 blast)
    have hDw_sub_poly: "D\<^sub>w \<subseteq> geotop_polyhedron L"
      using hC_split hC_sub_poly by (by100 blast)
    have hDq_sub_poly: "D\<^sub>q \<subseteq> geotop_polyhedron L"
      using hC_split hC_sub_poly by (by100 blast)
    have hp_ne_w: "p \<noteq> w"
      using hpS by (by100 blast)
    have hy_ne_w: "y \<noteq> w"
      using hyT by (by100 blast)
    have hpack:
        "\<And>N. N \<subseteq> geotop_polyhedron L - {w}
          \<Longrightarrow> top1_connected_on N
            (subspace_topology UNIV geotop_euclidean_topology N)
          \<Longrightarrow> p \<in> N
          \<Longrightarrow> y \<in> N
          \<Longrightarrow> \<exists>S T p y N. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> S \<noteq> T
            \<and> (S - {w}) \<inter> (T - {w}) = {}
            \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
            \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
            \<and> p \<noteq> y
            \<and> N \<subseteq> geotop_polyhedron L - {w}
            \<and> top1_connected_on N
              (subspace_topology UNIV geotop_euclidean_topology N)
            \<and> p \<in> N
            \<and> y \<in> N"
    proof -
      fix N
      assume hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
      assume hN_conn: "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
      assume hpN: "p \<in> N"
      assume hyN: "y \<in> N"
      have hbody: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<noteq> y
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> p \<in> N
        \<and> y \<in> N"
      proof (intro conjI)
        show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
        show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
        show "S \<noteq> T" by (rule hST)
        show "(S - {w}) \<inter> (T - {w}) = {}" by (rule hST_disj)
        show "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hpS)
        show "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hyT)
        show "p \<noteq> y" by (rule hpy)
        show "N \<subseteq> geotop_polyhedron L - {w}" by (rule hN_sub)
        show "top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)"
          by (rule hN_conn)
        show "p \<in> N" by (rule hpN)
        show "y \<in> N" by (rule hyN)
      qed
      show "\<exists>S T p y N. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<noteq> y
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> p \<in> N
        \<and> y \<in> N"
        by (rule exI[where x=S], rule exI[where x=T],
            rule exI[where x=p], rule exI[where x=y],
            rule exI[where x=N], rule hbody)
    qed
    show ?thesis
      using hside
    proof (elim disjE conjE)
      assume hyDw: "y \<in> D\<^sub>w - {p}"
      have hw_ep: "w \<in> top1_arc_endpoints_on D\<^sub>w
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)"
        using hDw_ep by (by100 simp)
      have hDw_minus_w_conn_sub: "top1_connected_on (D\<^sub>w - {w})
        (subspace_topology D\<^sub>w
          (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)
          (D\<^sub>w - {w}))"
        using hw_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
      have hDw_minus_w_subtop:
          "subspace_topology D\<^sub>w
            (subspace_topology UNIV geotop_euclidean_topology D\<^sub>w)
            (D\<^sub>w - {w})
          = subspace_topology UNIV geotop_euclidean_topology (D\<^sub>w - {w})"
        by (rule subspace_topology_trans[OF Diff_subset])
      have hN_conn: "top1_connected_on (D\<^sub>w - {w})
        (subspace_topology UNIV geotop_euclidean_topology (D\<^sub>w - {w}))"
        using hDw_minus_w_conn_sub unfolding hDw_minus_w_subtop .
      have hN_sub: "D\<^sub>w - {w} \<subseteq> geotop_polyhedron L - {w}"
        using hDw_sub_poly by (by100 blast)
      have hpN: "p \<in> D\<^sub>w - {w}"
        using hpDw hp_ne_w by (by100 blast)
      have hyN: "y \<in> D\<^sub>w - {w}"
        using hyDw hy_ne_w by (by100 blast)
      show ?thesis
        by (rule hpack[OF hN_sub hN_conn hpN hyN])
    next
      assume hyDq: "y \<in> D\<^sub>q - {p}"
      have hN_conn: "top1_connected_on D\<^sub>q
        (subspace_topology UNIV geotop_euclidean_topology D\<^sub>q)"
        by (rule arc_connected[OF hDq_arc])
      have hN_sub: "D\<^sub>q \<subseteq> geotop_polyhedron L - {w}"
        using hDq_sub_poly hw_not_Dq by (by100 blast)
      have hyN: "y \<in> D\<^sub>q"
        using hyDq by (by100 blast)
      show ?thesis
        by (rule hpack[OF hN_sub hN_conn hpDq hyN])
    qed
  qed
  have hcanonical_pair_split_side_connected_incident_germ_hits:
      "\<exists>S T p y N. S \<in> E
        \<and> T \<in> E
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<noteq> y
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> p \<in> (S - {w}) \<inter> N
        \<and> y \<in> (T - {w}) \<inter> N"
  proof -
    obtain S T p y N where hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
      and hpS: "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      and hpy: "p \<noteq> y"
      and hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
      and hN_conn: "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
      and hpN: "p \<in> N"
      and hyN: "y \<in> N"
      using hcanonical_pair_split_side_connected_selected_germs
      by (elim exE conjE)
    have hS_E: "S \<in> E"
      using hS he\<^sub>1E he\<^sub>2E he\<^sub>3E by (by100 blast)
    have hT_E: "T \<in> E"
      using hT he\<^sub>1E he\<^sub>2E he\<^sub>3E by (by100 blast)
    have hpSN: "p \<in> (S - {w}) \<inter> N"
      using hpS hpN by (by100 blast)
    have hyTN: "y \<in> (T - {w}) \<inter> N"
      using hyT hyN by (by100 blast)
    have hbody: "S \<in> E
      \<and> T \<in> E
      \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> S \<noteq> T
      \<and> (S - {w}) \<inter> (T - {w}) = {}
      \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> p \<noteq> y
      \<and> N \<subseteq> geotop_polyhedron L - {w}
      \<and> top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)
      \<and> p \<in> (S - {w}) \<inter> N
      \<and> y \<in> (T - {w}) \<inter> N"
    proof (intro conjI)
      show "S \<in> E" by (rule hS_E)
      show "T \<in> E" by (rule hT_E)
      show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
      show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
      show "S \<noteq> T" by (rule hST)
      show "(S - {w}) \<inter> (T - {w}) = {}" by (rule hST_disj)
      show "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hpS)
      show "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hyT)
      show "p \<noteq> y" by (rule hpy)
      show "N \<subseteq> geotop_polyhedron L - {w}" by (rule hN_sub)
      show "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
        by (rule hN_conn)
      show "p \<in> (S - {w}) \<inter> N" by (rule hpSN)
      show "y \<in> (T - {w}) \<inter> N" by (rule hyTN)
    qed
    show ?thesis
      by (rule exI[where x=S], rule exI[where x=T],
          rule exI[where x=p], rule exI[where x=y],
          rule exI[where x=N], rule hbody)
  qed
  have hcanonical_pair_split_side_three_incident_germs:
      "\<exists>S T U p y N. S \<in> E
        \<and> T \<in> E
        \<and> U \<in> E
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> S \<noteq> U
        \<and> T \<noteq> U
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> (S - {w}) \<inter> (U - {w}) = {}
        \<and> (T - {w}) \<inter> (U - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<noteq> y
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> p \<in> (S - {w}) \<inter> N
        \<and> y \<in> (T - {w}) \<inter> N"
  proof -
    obtain S T p y N where hS_E: "S \<in> E"
      and hT_E: "T \<in> E"
      and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
      and hpS: "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      and hpy: "p \<noteq> y"
      and hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
      and hN_conn: "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
      and hpSN: "p \<in> (S - {w}) \<inter> N"
      and hyTN: "y \<in> (T - {w}) \<inter> N"
      using hcanonical_pair_split_side_connected_incident_germ_hits
      by (elim exE conjE)
    have hremaining:
        "\<exists>U. U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3} \<and> S \<noteq> U \<and> T \<noteq> U"
    proof -
      have hS_cases: "S = e\<^sub>1 \<or> S = e\<^sub>2 \<or> S = e\<^sub>3"
        using hS by (by100 simp)
      have hT_cases: "T = e\<^sub>1 \<or> T = e\<^sub>2 \<or> T = e\<^sub>3"
        using hT by (by100 simp)
      show ?thesis
        using hS_cases
      proof (elim disjE)
        assume hS_eq: "S = e\<^sub>1"
        show ?thesis
          using hT_cases
        proof (elim disjE)
          assume hT_eq: "T = e\<^sub>1"
          have False
            using hST hS_eq hT_eq by (by100 simp)
          then show ?thesis by (by100 simp)
        next
          assume hT_eq: "T = e\<^sub>2"
          have hbody: "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> S \<noteq> e\<^sub>3 \<and> T \<noteq> e\<^sub>3"
            using hS_eq hT_eq he\<^sub>13 he\<^sub>23 by (by100 simp)
          show ?thesis
            by (rule exI[where x=e\<^sub>3], rule hbody)
        next
          assume hT_eq: "T = e\<^sub>3"
          have hbody: "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> S \<noteq> e\<^sub>2 \<and> T \<noteq> e\<^sub>2"
            using hS_eq hT_eq he\<^sub>12 he\<^sub>23 by (by100 simp)
          show ?thesis
            by (rule exI[where x=e\<^sub>2], rule hbody)
        qed
      next
        assume hS_eq: "S = e\<^sub>2"
        show ?thesis
          using hT_cases
        proof (elim disjE)
          assume hT_eq: "T = e\<^sub>1"
          have hbody: "e\<^sub>3 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> S \<noteq> e\<^sub>3 \<and> T \<noteq> e\<^sub>3"
            using hS_eq hT_eq he\<^sub>13 he\<^sub>23 by (by100 simp)
          show ?thesis
            by (rule exI[where x=e\<^sub>3], rule hbody)
        next
          assume hT_eq: "T = e\<^sub>2"
          have False
            using hST hS_eq hT_eq by (by100 simp)
          then show ?thesis by (by100 simp)
        next
          assume hT_eq: "T = e\<^sub>3"
          have hbody: "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> S \<noteq> e\<^sub>1 \<and> T \<noteq> e\<^sub>1"
            using hS_eq hT_eq he\<^sub>12 he\<^sub>13 by (by100 simp)
          show ?thesis
            by (rule exI[where x=e\<^sub>1], rule hbody)
        qed
      next
        assume hS_eq: "S = e\<^sub>3"
        show ?thesis
          using hT_cases
        proof (elim disjE)
          assume hT_eq: "T = e\<^sub>1"
          have hbody: "e\<^sub>2 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> S \<noteq> e\<^sub>2 \<and> T \<noteq> e\<^sub>2"
            using hS_eq hT_eq he\<^sub>12 he\<^sub>23 by (by100 simp)
          show ?thesis
            by (rule exI[where x=e\<^sub>2], rule hbody)
        next
          assume hT_eq: "T = e\<^sub>2"
          have hbody: "e\<^sub>1 \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
            \<and> S \<noteq> e\<^sub>1 \<and> T \<noteq> e\<^sub>1"
            using hS_eq hT_eq he\<^sub>12 he\<^sub>13 by (by100 simp)
          show ?thesis
            by (rule exI[where x=e\<^sub>1], rule hbody)
        next
          assume hT_eq: "T = e\<^sub>3"
          have False
            using hST hS_eq hT_eq by (by100 simp)
          then show ?thesis by (by100 simp)
        qed
      qed
    qed
    obtain U where hU: "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hSU: "S \<noteq> U"
      and hTU: "T \<noteq> U"
      using hremaining by (elim exE conjE)
    have hU_E: "U \<in> E"
      using hU he\<^sub>1E he\<^sub>2E he\<^sub>3E by (by100 blast)
    have hSU_disj: "(S - {w}) \<inter> (U - {w}) = {}"
      by (rule hincident_selected_punctured_disj[OF hS_E hU hSU])
    have hTU_disj: "(T - {w}) \<inter> (U - {w}) = {}"
      by (rule hincident_selected_punctured_disj[OF hT_E hU hTU])
    have hbody: "S \<in> E
      \<and> T \<in> E
      \<and> U \<in> E
      \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> S \<noteq> T
      \<and> S \<noteq> U
      \<and> T \<noteq> U
      \<and> (S - {w}) \<inter> (T - {w}) = {}
      \<and> (S - {w}) \<inter> (U - {w}) = {}
      \<and> (T - {w}) \<inter> (U - {w}) = {}
      \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> p \<noteq> y
      \<and> N \<subseteq> geotop_polyhedron L - {w}
      \<and> top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)
      \<and> p \<in> (S - {w}) \<inter> N
      \<and> y \<in> (T - {w}) \<inter> N"
    proof (intro conjI)
      show "S \<in> E" by (rule hS_E)
      show "T \<in> E" by (rule hT_E)
      show "U \<in> E" by (rule hU_E)
      show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
      show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
      show "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hU)
      show "S \<noteq> T" by (rule hST)
      show "S \<noteq> U" by (rule hSU)
      show "T \<noteq> U" by (rule hTU)
      show "(S - {w}) \<inter> (T - {w}) = {}" by (rule hST_disj)
      show "(S - {w}) \<inter> (U - {w}) = {}" by (rule hSU_disj)
      show "(T - {w}) \<inter> (U - {w}) = {}" by (rule hTU_disj)
      show "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hpS)
      show "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hyT)
      show "p \<noteq> y" by (rule hpy)
      show "N \<subseteq> geotop_polyhedron L - {w}" by (rule hN_sub)
      show "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
        by (rule hN_conn)
      show "p \<in> (S - {w}) \<inter> N" by (rule hpSN)
      show "y \<in> (T - {w}) \<inter> N" by (rule hyTN)
    qed
    show ?thesis
      by (rule exI[where x=S], rule exI[where x=T],
          rule exI[where x=U], rule exI[where x=p],
          rule exI[where x=y], rule exI[where x=N], rule hbody)
  qed
  have hcanonical_pair_split_side_three_sphere_germ_points:
      "\<exists>S T U p y z N. S \<in> E
        \<and> T \<in> E
        \<and> U \<in> E
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> S \<noteq> U
        \<and> T \<noteq> U
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> (S - {w}) \<inter> (U - {w}) = {}
        \<and> (T - {w}) \<inter> (U - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<noteq> y
        \<and> p \<noteq> z
        \<and> y \<noteq> z
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> p \<in> (S - {w}) \<inter> N
        \<and> y \<in> (T - {w}) \<inter> N"
  proof -
    obtain S T U p y N where hS_E: "S \<in> E"
      and hT_E: "T \<in> E"
      and hU_E: "U \<in> E"
      and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hU: "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and hSU: "S \<noteq> U"
      and hTU: "T \<noteq> U"
      and hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
      and hSU_disj: "(S - {w}) \<inter> (U - {w}) = {}"
      and hTU_disj: "(T - {w}) \<inter> (U - {w}) = {}"
      and hpS: "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      and hpy: "p \<noteq> y"
      and hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
      and hN_conn: "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
      and hpSN: "p \<in> (S - {w}) \<inter> N"
      and hyTN: "y \<in> (T - {w}) \<inter> N"
      using hcanonical_pair_split_side_three_incident_germs
      by (elim exE conjE)
    have hU_sphere_hit: "\<exists>z. z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r"
    proof -
      have hU_cases: "U = e\<^sub>1 \<or> U = e\<^sub>2 \<or> U = e\<^sub>3"
        using hU by (by100 simp)
      show ?thesis
        using hU_cases
      proof (elim disjE)
        assume hU_eq: "U = e\<^sub>1"
        have hx: "x\<^sub>1 \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r"
          using hU_eq hx\<^sub>1_edge_sphere hx\<^sub>1_ne_q\<^sub>1 by (by100 blast)
        show ?thesis
          by (rule exI[where x=x\<^sub>1], rule hx)
      next
        assume hU_eq: "U = e\<^sub>2"
        have hx: "x\<^sub>2 \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r"
          using hU_eq hx\<^sub>2_edge_sphere hx\<^sub>2_ne_q\<^sub>1 by (by100 blast)
        show ?thesis
          by (rule exI[where x=x\<^sub>2], rule hx)
      next
        assume hU_eq: "U = e\<^sub>3"
        have hx: "x\<^sub>3 \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r"
          using hU_eq hx\<^sub>3_edge_sphere hx\<^sub>3_ne_q\<^sub>1 by (by100 blast)
        show ?thesis
          by (rule exI[where x=x\<^sub>3], rule hx)
      qed
    qed
    obtain z where hzU: "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r"
      using hU_sphere_hit by (elim exE)
    have hpz: "p \<noteq> z"
    proof
      assume hpz_eq: "p = z"
      have "p \<in> (S - {w}) \<inter> (U - {w})"
        using hpS hzU hpz_eq by (by100 blast)
      then show False
        using hSU_disj by (by100 blast)
    qed
    have hyz: "y \<noteq> z"
    proof
      assume hyz_eq: "y = z"
      have "y \<in> (T - {w}) \<inter> (U - {w})"
        using hyT hzU hyz_eq by (by100 blast)
      then show False
        using hTU_disj by (by100 blast)
    qed
    have hbody: "S \<in> E
      \<and> T \<in> E
      \<and> U \<in> E
      \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> S \<noteq> T
      \<and> S \<noteq> U
      \<and> T \<noteq> U
      \<and> (S - {w}) \<inter> (T - {w}) = {}
      \<and> (S - {w}) \<inter> (U - {w}) = {}
      \<and> (T - {w}) \<inter> (U - {w}) = {}
      \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> p \<noteq> y
      \<and> p \<noteq> z
      \<and> y \<noteq> z
      \<and> N \<subseteq> geotop_polyhedron L - {w}
      \<and> top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)
      \<and> p \<in> (S - {w}) \<inter> N
      \<and> y \<in> (T - {w}) \<inter> N"
    proof (intro conjI)
      show "S \<in> E" by (rule hS_E)
      show "T \<in> E" by (rule hT_E)
      show "U \<in> E" by (rule hU_E)
      show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
      show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
      show "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hU)
      show "S \<noteq> T" by (rule hST)
      show "S \<noteq> U" by (rule hSU)
      show "T \<noteq> U" by (rule hTU)
      show "(S - {w}) \<inter> (T - {w}) = {}" by (rule hST_disj)
      show "(S - {w}) \<inter> (U - {w}) = {}" by (rule hSU_disj)
      show "(T - {w}) \<inter> (U - {w}) = {}" by (rule hTU_disj)
      show "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hpS)
      show "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hyT)
      show "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hzU)
      show "p \<noteq> y" by (rule hpy)
      show "p \<noteq> z" by (rule hpz)
      show "y \<noteq> z" by (rule hyz)
      show "N \<subseteq> geotop_polyhedron L - {w}" by (rule hN_sub)
      show "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
        by (rule hN_conn)
      show "p \<in> (S - {w}) \<inter> N" by (rule hpSN)
      show "y \<in> (T - {w}) \<inter> N" by (rule hyTN)
    qed
    show ?thesis
      by (rule exI[where x=S], rule exI[where x=T],
          rule exI[where x=U], rule exI[where x=p],
          rule exI[where x=y], rule exI[where x=z],
          rule exI[where x=N], rule hbody)
  qed
  have hcanonical_pair_split_side_three_canonical_sphere_points:
      "\<exists>S T U p y z N. S \<in> E
        \<and> T \<in> E
        \<and> U \<in> E
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> S \<noteq> U
        \<and> T \<noteq> U
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> (S - {w}) \<inter> (U - {w}) = {}
        \<and> (T - {w}) \<inter> (U - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> {p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> p \<noteq> y
        \<and> p \<noteq> z
        \<and> y \<noteq> z
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> p \<in> (S - {w}) \<inter> N
        \<and> y \<in> (T - {w}) \<inter> N"
  proof -
    obtain S T U p y z N where hS_E: "S \<in> E"
      and hT_E: "T \<in> E"
      and hU_E: "U \<in> E"
      and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hU: "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and hSU: "S \<noteq> U"
      and hTU: "T \<noteq> U"
      and hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
      and hSU_disj: "(S - {w}) \<inter> (U - {w}) = {}"
      and hTU_disj: "(T - {w}) \<inter> (U - {w}) = {}"
      and hpS: "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      and hzU: "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r"
      and hpy: "p \<noteq> y"
      and hpz: "p \<noteq> z"
      and hyz: "y \<noteq> z"
      and hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
      and hN_conn: "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
      and hpSN: "p \<in> (S - {w}) \<inter> N"
      and hyTN: "y \<in> (T - {w}) \<inter> N"
      using hcanonical_pair_split_side_three_sphere_germ_points
      by (elim exE conjE)
    have hp_can: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      by (rule hselected_sphere_germ_point_canonical[OF hS hpS])
    have hy_can: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      by (rule hselected_sphere_germ_point_canonical[OF hT hyT])
    have hz_can: "z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      by (rule hselected_sphere_germ_point_canonical[OF hU hzU])
    have hpyz_eq: "{p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      using hp_can hy_can hz_can hpy hpz hyz hx\<^sub>12 hx\<^sub>13 hx\<^sub>23
      by (by100 blast)
    have hbody: "S \<in> E
      \<and> T \<in> E
      \<and> U \<in> E
      \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> S \<noteq> T
      \<and> S \<noteq> U
      \<and> T \<noteq> U
      \<and> (S - {w}) \<inter> (T - {w}) = {}
      \<and> (S - {w}) \<inter> (U - {w}) = {}
      \<and> (T - {w}) \<inter> (U - {w}) = {}
      \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> {p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> p \<noteq> y
      \<and> p \<noteq> z
      \<and> y \<noteq> z
      \<and> N \<subseteq> geotop_polyhedron L - {w}
      \<and> top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)
      \<and> p \<in> (S - {w}) \<inter> N
      \<and> y \<in> (T - {w}) \<inter> N"
    proof (intro conjI)
      show "S \<in> E" by (rule hS_E)
      show "T \<in> E" by (rule hT_E)
      show "U \<in> E" by (rule hU_E)
      show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
      show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
      show "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hU)
      show "S \<noteq> T" by (rule hST)
      show "S \<noteq> U" by (rule hSU)
      show "T \<noteq> U" by (rule hTU)
      show "(S - {w}) \<inter> (T - {w}) = {}" by (rule hST_disj)
      show "(S - {w}) \<inter> (U - {w}) = {}" by (rule hSU_disj)
      show "(T - {w}) \<inter> (U - {w}) = {}" by (rule hTU_disj)
      show "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hpS)
      show "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hyT)
      show "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hzU)
      show "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hp_can)
      show "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hy_can)
      show "z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hz_can)
      show "{p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hpyz_eq)
      show "p \<noteq> y" by (rule hpy)
      show "p \<noteq> z" by (rule hpz)
      show "y \<noteq> z" by (rule hyz)
      show "N \<subseteq> geotop_polyhedron L - {w}" by (rule hN_sub)
      show "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
        by (rule hN_conn)
      show "p \<in> (S - {w}) \<inter> N" by (rule hpSN)
      show "y \<in> (T - {w}) \<inter> N" by (rule hyTN)
    qed
    show ?thesis
      by (rule exI[where x=S], rule exI[where x=T],
          rule exI[where x=U], rule exI[where x=p],
          rule exI[where x=y], rule exI[where x=z],
          rule exI[where x=N], rule hbody)
  qed
  have hcanonical_pair_split_side_selected_three_edges:
      "\<exists>S T U p y z N. S \<in> E
        \<and> T \<in> E
        \<and> U \<in> E
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> {S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> S \<noteq> U
        \<and> T \<noteq> U
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> (S - {w}) \<inter> (U - {w}) = {}
        \<and> (T - {w}) \<inter> (U - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> {p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> p \<noteq> y
        \<and> p \<noteq> z
        \<and> y \<noteq> z
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> p \<in> (S - {w}) \<inter> N
        \<and> y \<in> (T - {w}) \<inter> N"
  proof -
    obtain S T U p y z N where hS_E: "S \<in> E"
      and hT_E: "T \<in> E"
      and hU_E: "U \<in> E"
      and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hU: "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and hSU: "S \<noteq> U"
      and hTU: "T \<noteq> U"
      and hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
      and hSU_disj: "(S - {w}) \<inter> (U - {w}) = {}"
      and hTU_disj: "(T - {w}) \<inter> (U - {w}) = {}"
      and hpS: "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      and hzU: "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r"
      and hp_can: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hy_can: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hz_can: "z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hpyz_eq: "{p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hpy: "p \<noteq> y"
      and hpz: "p \<noteq> z"
      and hyz: "y \<noteq> z"
      and hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
      and hN_conn: "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
      and hpSN: "p \<in> (S - {w}) \<inter> N"
      and hyTN: "y \<in> (T - {w}) \<inter> N"
      using hcanonical_pair_split_side_three_canonical_sphere_points
      by (elim exE conjE)
    have hSTU_eq: "{S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
    proof -
      have hsub: "{S, T, U} \<subseteq> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        using hS hT hU by (by100 simp)
      have hSTU_card: "card {S, T, U} = 3"
        using hST hSU hTU by (by100 simp)
      have he_card: "card {e\<^sub>1, e\<^sub>2, e\<^sub>3} = 3"
        using he\<^sub>12 he\<^sub>13 he\<^sub>23 by (by100 simp)
      show ?thesis
      proof (rule card_seteq)
        show "finite {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
          by (by100 simp)
        show "{S, T, U} \<subseteq> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
          by (rule hsub)
        show "card {e\<^sub>1, e\<^sub>2, e\<^sub>3} \<le> card {S, T, U}"
          using hSTU_card he_card by (by100 simp)
      qed
    qed
    have hbody: "S \<in> E
      \<and> T \<in> E
      \<and> U \<in> E
      \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> {S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> S \<noteq> T
      \<and> S \<noteq> U
      \<and> T \<noteq> U
      \<and> (S - {w}) \<inter> (T - {w}) = {}
      \<and> (S - {w}) \<inter> (U - {w}) = {}
      \<and> (T - {w}) \<inter> (U - {w}) = {}
      \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> {p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> p \<noteq> y
      \<and> p \<noteq> z
      \<and> y \<noteq> z
      \<and> N \<subseteq> geotop_polyhedron L - {w}
      \<and> top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)
      \<and> p \<in> (S - {w}) \<inter> N
      \<and> y \<in> (T - {w}) \<inter> N"
    proof (intro conjI)
      show "S \<in> E" by (rule hS_E)
      show "T \<in> E" by (rule hT_E)
      show "U \<in> E" by (rule hU_E)
      show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
      show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
      show "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hU)
      show "{S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hSTU_eq)
      show "S \<noteq> T" by (rule hST)
      show "S \<noteq> U" by (rule hSU)
      show "T \<noteq> U" by (rule hTU)
      show "(S - {w}) \<inter> (T - {w}) = {}" by (rule hST_disj)
      show "(S - {w}) \<inter> (U - {w}) = {}" by (rule hSU_disj)
      show "(T - {w}) \<inter> (U - {w}) = {}" by (rule hTU_disj)
      show "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hpS)
      show "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hyT)
      show "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hzU)
      show "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hp_can)
      show "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hy_can)
      show "z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hz_can)
      show "{p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hpyz_eq)
      show "p \<noteq> y" by (rule hpy)
      show "p \<noteq> z" by (rule hpz)
      show "y \<noteq> z" by (rule hyz)
      show "N \<subseteq> geotop_polyhedron L - {w}" by (rule hN_sub)
      show "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
        by (rule hN_conn)
      show "p \<in> (S - {w}) \<inter> N" by (rule hpSN)
      show "y \<in> (T - {w}) \<inter> N" by (rule hyTN)
    qed
    show ?thesis
      by (rule exI[where x=S], rule exI[where x=T],
          rule exI[where x=U], rule exI[where x=p],
          rule exI[where x=y], rule exI[where x=z],
          rule exI[where x=N], rule hbody)
  qed
  have hcanonical_pair_split_side_selected_three_edges_card:
      "\<exists>S T U p y z N. S \<in> E
        \<and> T \<in> E
        \<and> U \<in> E
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> {S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> S \<noteq> U
        \<and> T \<noteq> U
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> (S - {w}) \<inter> (U - {w}) = {}
        \<and> (T - {w}) \<inter> (U - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> {p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> card {p, y, z} = 3
        \<and> p \<noteq> y
        \<and> p \<noteq> z
        \<and> y \<noteq> z
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> p \<in> (S - {w}) \<inter> N
        \<and> y \<in> (T - {w}) \<inter> N"
  proof -
    obtain S T U p y z N where hS_E: "S \<in> E"
      and hT_E: "T \<in> E"
      and hU_E: "U \<in> E"
      and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hU: "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hSTU_eq: "{S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and hSU: "S \<noteq> U"
      and hTU: "T \<noteq> U"
      and hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
      and hSU_disj: "(S - {w}) \<inter> (U - {w}) = {}"
      and hTU_disj: "(T - {w}) \<inter> (U - {w}) = {}"
      and hpS: "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      and hzU: "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r"
      and hp_can: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hy_can: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hz_can: "z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hpyz_eq: "{p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hpy: "p \<noteq> y"
      and hpz: "p \<noteq> z"
      and hyz: "y \<noteq> z"
      and hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
      and hN_conn: "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
      and hpSN: "p \<in> (S - {w}) \<inter> N"
      and hyTN: "y \<in> (T - {w}) \<inter> N"
      using hcanonical_pair_split_side_selected_three_edges
      by (elim exE conjE)
    have hcard: "card {p, y, z} = 3"
      using hpy hpz hyz by (by100 simp)
    have hbody: "S \<in> E
        \<and> T \<in> E
        \<and> U \<in> E
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> {S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> S \<noteq> U
        \<and> T \<noteq> U
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> (S - {w}) \<inter> (U - {w}) = {}
        \<and> (T - {w}) \<inter> (U - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> {p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> card {p, y, z} = 3
        \<and> p \<noteq> y
        \<and> p \<noteq> z
        \<and> y \<noteq> z
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> p \<in> (S - {w}) \<inter> N
        \<and> y \<in> (T - {w}) \<inter> N"
    proof (intro conjI)
      show "S \<in> E" by (rule hS_E)
      show "T \<in> E" by (rule hT_E)
      show "U \<in> E" by (rule hU_E)
      show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
      show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
      show "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hU)
      show "{S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hSTU_eq)
      show "S \<noteq> T" by (rule hST)
      show "S \<noteq> U" by (rule hSU)
      show "T \<noteq> U" by (rule hTU)
      show "(S - {w}) \<inter> (T - {w}) = {}" by (rule hST_disj)
      show "(S - {w}) \<inter> (U - {w}) = {}" by (rule hSU_disj)
      show "(T - {w}) \<inter> (U - {w}) = {}" by (rule hTU_disj)
      show "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hpS)
      show "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hyT)
      show "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hzU)
      show "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hp_can)
      show "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hy_can)
      show "z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hz_can)
      show "{p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hpyz_eq)
      show "card {p, y, z} = 3" by (rule hcard)
      show "p \<noteq> y" by (rule hpy)
      show "p \<noteq> z" by (rule hpz)
      show "y \<noteq> z" by (rule hyz)
      show "N \<subseteq> geotop_polyhedron L - {w}" by (rule hN_sub)
      show "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
        by (rule hN_conn)
      show "p \<in> (S - {w}) \<inter> N" by (rule hpSN)
      show "y \<in> (T - {w}) \<inter> N" by (rule hyTN)
    qed
    show ?thesis
      by (rule exI[where x=S], rule exI[where x=T],
          rule exI[where x=U], rule exI[where x=p],
          rule exI[where x=y], rule exI[where x=z],
          rule exI[where x=N], rule hbody)
  qed
  have hcanonical_pair_split_side_selected_three_edges_same_component:
      "\<exists>S T U p y z. S \<in> E
        \<and> T \<in> E
        \<and> U \<in> E
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> {S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> S \<noteq> U
        \<and> T \<noteq> U
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> (S - {w}) \<inter> (U - {w}) = {}
        \<and> (T - {w}) \<inter> (U - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> {p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> p \<noteq> y
        \<and> p \<noteq> z
        \<and> y \<noteq> z
        \<and> top1_in_same_component_on (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w})) p y"
  proof -
    obtain S T U p y z N where hS_E: "S \<in> E"
      and hT_E: "T \<in> E"
      and hU_E: "U \<in> E"
      and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hU: "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hSTU_eq: "{S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and hSU: "S \<noteq> U"
      and hTU: "T \<noteq> U"
      and hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
      and hSU_disj: "(S - {w}) \<inter> (U - {w}) = {}"
      and hTU_disj: "(T - {w}) \<inter> (U - {w}) = {}"
      and hpS: "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      and hzU: "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r"
      and hp_can: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hy_can: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hz_can: "z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hpyz_eq: "{p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hpy: "p \<noteq> y"
      and hpz: "p \<noteq> z"
      and hyz: "y \<noteq> z"
      and hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
      and hN_conn: "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
      and hpSN: "p \<in> (S - {w}) \<inter> N"
      and hyTN: "y \<in> (T - {w}) \<inter> N"
      using hcanonical_pair_split_side_selected_three_edges
      by (elim exE conjE)
    have hN_subtop:
        "subspace_topology (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w})) N
          = subspace_topology UNIV geotop_euclidean_topology N"
      by (rule subspace_topology_trans[OF hN_sub])
    have hpN: "p \<in> N"
      using hpSN by (by100 blast)
    have hyN: "y \<in> N"
      using hyTN by (by100 blast)
    have hsame:
        "top1_in_same_component_on (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w})) p y"
      unfolding top1_in_same_component_on_def
    proof (rule exI[where x=N])
      show "N \<subseteq> geotop_polyhedron L - {w}
        \<and> p \<in> N
        \<and> y \<in> N
        \<and> top1_connected_on N
          (subspace_topology (geotop_polyhedron L - {w})
            (subspace_topology UNIV geotop_euclidean_topology
              (geotop_polyhedron L - {w})) N)"
      proof (intro conjI)
        show "N \<subseteq> geotop_polyhedron L - {w}" by (rule hN_sub)
        show "p \<in> N" by (rule hpN)
        show "y \<in> N" by (rule hyN)
        show "top1_connected_on N
          (subspace_topology (geotop_polyhedron L - {w})
            (subspace_topology UNIV geotop_euclidean_topology
              (geotop_polyhedron L - {w})) N)"
          unfolding hN_subtop by (rule hN_conn)
      qed
    qed
    have hbody: "S \<in> E
      \<and> T \<in> E
      \<and> U \<in> E
      \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> {S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}
      \<and> S \<noteq> T
      \<and> S \<noteq> U
      \<and> T \<noteq> U
      \<and> (S - {w}) \<inter> (T - {w}) = {}
      \<and> (S - {w}) \<inter> (U - {w}) = {}
      \<and> (T - {w}) \<inter> (U - {w}) = {}
      \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r
      \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> {p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}
      \<and> p \<noteq> y
      \<and> p \<noteq> z
      \<and> y \<noteq> z
      \<and> top1_in_same_component_on (geotop_polyhedron L - {w})
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron L - {w})) p y"
    proof (intro conjI)
      show "S \<in> E" by (rule hS_E)
      show "T \<in> E" by (rule hT_E)
      show "U \<in> E" by (rule hU_E)
      show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
      show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
      show "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hU)
      show "{S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hSTU_eq)
      show "S \<noteq> T" by (rule hST)
      show "S \<noteq> U" by (rule hSU)
      show "T \<noteq> U" by (rule hTU)
      show "(S - {w}) \<inter> (T - {w}) = {}" by (rule hST_disj)
      show "(S - {w}) \<inter> (U - {w}) = {}" by (rule hSU_disj)
      show "(T - {w}) \<inter> (U - {w}) = {}" by (rule hTU_disj)
      show "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hpS)
      show "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hyT)
      show "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hzU)
      show "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hp_can)
      show "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hy_can)
      show "z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hz_can)
      show "{p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hpyz_eq)
      show "p \<noteq> y" by (rule hpy)
      show "p \<noteq> z" by (rule hpz)
      show "y \<noteq> z" by (rule hyz)
      show "top1_in_same_component_on (geotop_polyhedron L - {w})
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron L - {w})) p y"
        by (rule hsame)
    qed
    show ?thesis
      by (rule exI[where x=S], rule exI[where x=T],
          rule exI[where x=U], rule exI[where x=p],
          rule exI[where x=y], rule exI[where x=z],
          rule hbody)
  qed
  have hcanonical_pair_split_side_three_card:
      "\<exists>S T U p y z. S \<in> E
        \<and> T \<in> E
        \<and> U \<in> E
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> {S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> S \<noteq> U
        \<and> T \<noteq> U
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> (S - {w}) \<inter> (U - {w}) = {}
        \<and> (T - {w}) \<inter> (U - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> {p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> card {p, y, z} = 3
        \<and> p \<noteq> y
        \<and> p \<noteq> z
        \<and> y \<noteq> z
        \<and> top1_in_same_component_on (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w})) p y"
  proof -
    obtain S T U p y z where hS_E: "S \<in> E"
      and hT_E: "T \<in> E"
      and hU_E: "U \<in> E"
      and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hU: "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hSTU_eq: "{S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hST: "S \<noteq> T"
      and hSU: "S \<noteq> U"
      and hTU: "T \<noteq> U"
      and hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
      and hSU_disj: "(S - {w}) \<inter> (U - {w}) = {}"
      and hTU_disj: "(T - {w}) \<inter> (U - {w}) = {}"
      and hpS: "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      and hzU: "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r"
      and hp_can: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hy_can: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hz_can: "z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hpyz_eq: "{p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      and hpy: "p \<noteq> y"
      and hpz: "p \<noteq> z"
      and hyz: "y \<noteq> z"
      and hsame: "top1_in_same_component_on (geotop_polyhedron L - {w})
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron L - {w})) p y"
      using hcanonical_pair_split_side_selected_three_edges_same_component
      by (elim exE conjE)
    have hcard: "card {p, y, z} = 3"
      using hpy hpz hyz by (by100 simp)
    have hbody: "S \<in> E
        \<and> T \<in> E
        \<and> U \<in> E
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> {S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> S \<noteq> U
        \<and> T \<noteq> U
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> (S - {w}) \<inter> (U - {w}) = {}
        \<and> (T - {w}) \<inter> (U - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> {p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> card {p, y, z} = 3
        \<and> p \<noteq> y
        \<and> p \<noteq> z
        \<and> y \<noteq> z
        \<and> top1_in_same_component_on (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w})) p y"
    proof (intro conjI)
      show "S \<in> E" by (rule hS_E)
      show "T \<in> E" by (rule hT_E)
      show "U \<in> E" by (rule hU_E)
      show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
      show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
      show "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hU)
      show "{S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hSTU_eq)
      show "S \<noteq> T" by (rule hST)
      show "S \<noteq> U" by (rule hSU)
      show "T \<noteq> U" by (rule hTU)
      show "(S - {w}) \<inter> (T - {w}) = {}" by (rule hST_disj)
      show "(S - {w}) \<inter> (U - {w}) = {}" by (rule hSU_disj)
      show "(T - {w}) \<inter> (U - {w}) = {}" by (rule hTU_disj)
      show "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hpS)
      show "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hyT)
      show "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hzU)
      show "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hp_can)
      show "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hy_can)
      show "z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hz_can)
      show "{p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hpyz_eq)
      show "card {p, y, z} = 3" by (rule hcard)
      show "p \<noteq> y" by (rule hpy)
      show "p \<noteq> z" by (rule hpz)
      show "y \<noteq> z" by (rule hyz)
      show "top1_in_same_component_on (geotop_polyhedron L - {w})
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron L - {w})) p y"
        by (rule hsame)
    qed
    show ?thesis
      by (rule exI[where x=S], rule exI[where x=T],
          rule exI[where x=U], rule exI[where x=p],
          rule exI[where x=y], rule exI[where x=z],
          rule hbody)
  qed
  have hno_local_component_meets_all_three_selected_edges:
      "\<And>C. C \<in> components (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))
        \<Longrightarrow> \<not> ((e\<^sub>1 - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
          \<and> (e\<^sub>2 - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
          \<and> (e\<^sub>3 - {w}) \<inter> ball w r \<inter> closure C \<noteq> {})"
  proof -
    fix C
    assume hC: "C \<in> components (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))"
    let ?T = "{S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}.
      (S - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}}"
    have hbound: "card ?T \<le> 2"
      using hradial_sector_bound hC by (by100 blast)
    have hcard_edges: "card {e\<^sub>1, e\<^sub>2, e\<^sub>3} = 3"
      using he\<^sub>12 he\<^sub>13 he\<^sub>23 by (by100 simp)
    show "\<not> ((e\<^sub>1 - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
          \<and> (e\<^sub>2 - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
          \<and> (e\<^sub>3 - {w}) \<inter> ball w r \<inter> closure C \<noteq> {})"
    proof
      assume hall: "(e\<^sub>1 - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
          \<and> (e\<^sub>2 - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
          \<and> (e\<^sub>3 - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
      have hT_eq: "?T = {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        using hall by (by100 blast)
      have "card ?T = 3"
        using hT_eq hcard_edges by (by100 simp)
      then show False
        using hbound by (by100 linarith)
    qed
  qed
  have hno_local_component_meets_selected_three_edges:
      "\<And>C S T U. C \<in> components (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))
        \<Longrightarrow> {S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<Longrightarrow> (S - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
        \<Longrightarrow> (T - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
        \<Longrightarrow> (U - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
        \<Longrightarrow> False"
  proof -
    fix C S T U
    assume hC: "C \<in> components (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))"
    assume hSTU: "{S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
    assume hS_touch: "(S - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
    assume hT_touch: "(T - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
    assume hU_touch: "(U - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
    have htouched_if_mem:
        "\<And>R. R \<in> {S, T, U}
          \<Longrightarrow> (R - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
    proof -
      fix R
      assume hR: "R \<in> {S, T, U}"
      have hcases: "R = S \<or> R = T \<or> R = U"
        using hR by (by100 simp)
      show "(R - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
        using hcases
      proof (elim disjE)
        assume hR_eq: "R = S"
        show "(R - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
          using hR_eq hS_touch by (by100 simp)
      next
        assume hR_eq: "R = T"
        show "(R - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
          using hR_eq hT_touch by (by100 simp)
      next
        assume hR_eq: "R = U"
        show "(R - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
          using hR_eq hU_touch by (by100 simp)
      qed
    qed
    have he\<^sub>1_mem: "e\<^sub>1 \<in> {S, T, U}"
      using hSTU by (by100 simp)
    have he\<^sub>2_mem: "e\<^sub>2 \<in> {S, T, U}"
      using hSTU by (by100 simp)
    have he\<^sub>3_mem: "e\<^sub>3 \<in> {S, T, U}"
      using hSTU by (by100 simp)
    have he\<^sub>1_touch: "(e\<^sub>1 - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
      by (rule htouched_if_mem[OF he\<^sub>1_mem])
    have he\<^sub>2_touch: "(e\<^sub>2 - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
      by (rule htouched_if_mem[OF he\<^sub>2_mem])
    have he\<^sub>3_touch: "(e\<^sub>3 - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
      by (rule htouched_if_mem[OF he\<^sub>3_mem])
    have hall: "(e\<^sub>1 - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
        \<and> (e\<^sub>2 - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
        \<and> (e\<^sub>3 - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
      using he\<^sub>1_touch he\<^sub>2_touch he\<^sub>3_touch by (by100 simp)
    show False
      using hno_local_component_meets_all_three_selected_edges[OF hC] hall
      by (by100 blast)
  qed
  have hlocal_component_meets_selected_three_edges_book_step:
      "\<exists>C S T U. C \<in> components (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))
        \<and> {S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> (S - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
        \<and> (T - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
        \<and> (U - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
    (**
      Remaining local-star bridge in Moise's branch-point argument.  The
      connected split-side package above gives three selected incident germs at
      \<open>w\<close>; using the small star ball and the carrier-sector cover, their
      punctured side must determine one local component of
      \<open>ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3)\<close> whose closure meets all three selected
      germs. **)
  proof -
    have hsplit_side_three_connected_card:
        "\<exists>S T U p y z N. S \<in> E
          \<and> T \<in> E
          \<and> U \<in> E
          \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> {S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<and> S \<noteq> T
          \<and> S \<noteq> U
          \<and> T \<noteq> U
          \<and> (S - {w}) \<inter> (T - {w}) = {}
          \<and> (S - {w}) \<inter> (U - {w}) = {}
          \<and> (T - {w}) \<inter> (U - {w}) = {}
          \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
          \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
          \<and> z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r
          \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<and> z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<and> {p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<and> card {p, y, z} = 3
          \<and> p \<noteq> y
          \<and> p \<noteq> z
          \<and> y \<noteq> z
          \<and> N \<subseteq> geotop_polyhedron L - {w}
          \<and> top1_connected_on N
            (subspace_topology UNIV geotop_euclidean_topology N)
          \<and> p \<in> (S - {w}) \<inter> N
          \<and> y \<in> (T - {w}) \<inter> N
          \<and> top1_in_same_component_on (geotop_polyhedron L - {w})
            (subspace_topology UNIV geotop_euclidean_topology
              (geotop_polyhedron L - {w})) p y"
    proof -
      obtain S T U p y z N where hS_E: "S \<in> E"
        and hT_E: "T \<in> E"
        and hU_E: "U \<in> E"
        and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        and hU: "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        and hSTU_eq: "{S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        and hST: "S \<noteq> T"
        and hSU: "S \<noteq> U"
        and hTU: "T \<noteq> U"
        and hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
        and hSU_disj: "(S - {w}) \<inter> (U - {w}) = {}"
        and hTU_disj: "(T - {w}) \<inter> (U - {w}) = {}"
        and hpS: "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
        and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
        and hzU: "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r"
        and hp_can: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
        and hy_can: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
        and hz_can: "z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
        and hpyz_eq: "{p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
        and hcard: "card {p, y, z} = 3"
        and hpy: "p \<noteq> y"
        and hpz: "p \<noteq> z"
        and hyz: "y \<noteq> z"
        and hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
        and hN_conn: "top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)"
        and hpSN: "p \<in> (S - {w}) \<inter> N"
        and hyTN: "y \<in> (T - {w}) \<inter> N"
        using hcanonical_pair_split_side_selected_three_edges_card
        by (elim exE conjE)
      have hN_subtop:
          "subspace_topology (geotop_polyhedron L - {w})
            (subspace_topology UNIV geotop_euclidean_topology
              (geotop_polyhedron L - {w})) N
            = subspace_topology UNIV geotop_euclidean_topology N"
        by (rule subspace_topology_trans[OF hN_sub])
      have hpN: "p \<in> N"
        using hpSN by (by100 blast)
      have hyN: "y \<in> N"
        using hyTN by (by100 blast)
      have hsame:
          "top1_in_same_component_on (geotop_polyhedron L - {w})
            (subspace_topology UNIV geotop_euclidean_topology
              (geotop_polyhedron L - {w})) p y"
        unfolding top1_in_same_component_on_def
      proof (rule exI[where x=N])
        show "N \<subseteq> geotop_polyhedron L - {w}
          \<and> p \<in> N
          \<and> y \<in> N
          \<and> top1_connected_on N
            (subspace_topology (geotop_polyhedron L - {w})
              (subspace_topology UNIV geotop_euclidean_topology
                (geotop_polyhedron L - {w})) N)"
        proof (intro conjI)
          show "N \<subseteq> geotop_polyhedron L - {w}" by (rule hN_sub)
          show "p \<in> N" by (rule hpN)
          show "y \<in> N" by (rule hyN)
          show "top1_connected_on N
            (subspace_topology (geotop_polyhedron L - {w})
              (subspace_topology UNIV geotop_euclidean_topology
                (geotop_polyhedron L - {w})) N)"
            unfolding hN_subtop by (rule hN_conn)
        qed
      qed
      have hbody: "S \<in> E
        \<and> T \<in> E
        \<and> U \<in> E
        \<and> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> {S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> S \<noteq> T
        \<and> S \<noteq> U
        \<and> T \<noteq> U
        \<and> (S - {w}) \<inter> (T - {w}) = {}
        \<and> (S - {w}) \<inter> (U - {w}) = {}
        \<and> (T - {w}) \<inter> (U - {w}) = {}
        \<and> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r
        \<and> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> {p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}
        \<and> card {p, y, z} = 3
        \<and> p \<noteq> y
        \<and> p \<noteq> z
        \<and> y \<noteq> z
        \<and> N \<subseteq> geotop_polyhedron L - {w}
        \<and> top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)
        \<and> p \<in> (S - {w}) \<inter> N
        \<and> y \<in> (T - {w}) \<inter> N
        \<and> top1_in_same_component_on (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w})) p y"
      proof (intro conjI)
        show "S \<in> E" by (rule hS_E)
        show "T \<in> E" by (rule hT_E)
        show "U \<in> E" by (rule hU_E)
        show "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hS)
        show "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hT)
        show "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hU)
        show "{S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hSTU_eq)
        show "S \<noteq> T" by (rule hST)
        show "S \<noteq> U" by (rule hSU)
        show "T \<noteq> U" by (rule hTU)
        show "(S - {w}) \<inter> (T - {w}) = {}" by (rule hST_disj)
        show "(S - {w}) \<inter> (U - {w}) = {}" by (rule hSU_disj)
        show "(T - {w}) \<inter> (U - {w}) = {}" by (rule hTU_disj)
        show "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hpS)
        show "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hyT)
        show "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r" by (rule hzU)
        show "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hp_can)
        show "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hy_can)
        show "z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hz_can)
        show "{p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}" by (rule hpyz_eq)
        show "card {p, y, z} = 3" by (rule hcard)
        show "p \<noteq> y" by (rule hpy)
        show "p \<noteq> z" by (rule hpz)
        show "y \<noteq> z" by (rule hyz)
        show "N \<subseteq> geotop_polyhedron L - {w}" by (rule hN_sub)
        show "top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)"
          by (rule hN_conn)
        show "p \<in> (S - {w}) \<inter> N" by (rule hpSN)
        show "y \<in> (T - {w}) \<inter> N" by (rule hyTN)
        show "top1_in_same_component_on (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w})) p y"
          by (rule hsame)
      qed
      show ?thesis
        by (rule exI[where x=S], rule exI[where x=T],
            rule exI[where x=U], rule exI[where x=p],
            rule exI[where x=y], rule exI[where x=z],
            rule exI[where x=N], rule hbody)
    qed
    have hselected_sphere_germ_closure:
        "\<And>S a. S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<Longrightarrow> a \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
          \<Longrightarrow> a \<in> closure ((S - {w}) \<inter> ball w r)"
    proof -
      fix S a
      assume hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      assume haS: "a \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      have hradial_closure:
          "\<And>q e x. q \<noteq> w
            \<Longrightarrow> r < dist w q
            \<Longrightarrow> e = closed_segment w q
            \<Longrightarrow> x = w + (r / dist w q) *\<^sub>R (q - w)
            \<Longrightarrow> x \<in> closure ((e - {w}) \<inter> ball w r)"
      proof -
        fix q e x
        assume hq_ne: "q \<noteq> w"
        assume hr_lt_q: "r < dist w q"
        assume he: "e = closed_segment w q"
        assume hx: "x = w + (r / dist w q) *\<^sub>R (q - w)"
        have hdist_q_pos: "0 < dist w q"
          using hq_ne by (by100 simp)
        show "x \<in> closure ((e - {w}) \<inter> ball w r)"
          unfolding closure_approachable
        proof (intro allI impI)
          fix \<epsilon> :: real
          assume h\<epsilon>: "0 < \<epsilon>"
          define d where "d = min (r / 2) (\<epsilon> / 2)"
          have hd_pos: "0 < d"
            unfolding d_def using hr_pos h\<epsilon> by (by100 simp)
          have hd_lt_r: "d < r"
            unfolding d_def using hr_pos h\<epsilon> by (by100 simp)
          have hd_lt_\<epsilon>: "d < \<epsilon>"
            unfolding d_def using hr_pos h\<epsilon> by (by100 simp)
          define t where "t = r - d"
          have ht_pos: "0 < t"
            unfolding t_def using hd_lt_r by (by100 simp)
          have ht_lt_r: "t < r"
            unfolding t_def using hd_pos by (by100 simp)
          have ht_le_q: "t \<le> dist w q"
            unfolding t_def using hr_lt_q hd_pos by (by100 simp)
          define u where "u = w + (t / dist w q) *\<^sub>R (q - w)"
          have hu_seg_sphere:
              "u \<in> (closed_segment w q - {w}) \<inter> sphere w t"
          proof -
            have hseg_sphere:
                "(closed_segment w q - {w}) \<inter> sphere w t = {u}"
              by (rule closed_segment_sphere_unique_from_center
                  [OF hq_ne ht_pos ht_le_q u_def])
            show ?thesis
              using hseg_sphere by (by100 simp)
          qed
          have hu_set: "u \<in> (e - {w}) \<inter> ball w r"
          proof -
            have hue: "u \<in> e - {w}"
              using hu_seg_sphere he by (by100 blast)
            have hudist: "dist w u = t"
              using hu_seg_sphere by (by100 simp)
            have huball: "u \<in> ball w r"
              using hudist ht_lt_r by (by100 simp)
            show ?thesis
              using hue huball by (by100 blast)
          qed
          have hux_vec:
              "u - x = ((t - r) / dist w q) *\<^sub>R (q - w)"
            unfolding u_def hx
            apply vector
            using hdist_q_pos
            by (simp add: field_simps)
          have hdist_ux: "dist u x = d"
          proof -
            have "dist u x = norm (u - x)"
              by (simp add: dist_norm)
            also have "\<dots> = norm (((t - r) / dist w q) *\<^sub>R (q - w))"
              using hux_vec by (by100 simp)
            also have "\<dots> = \<bar>(t - r) / dist w q\<bar> * norm (q - w)"
              by (by100 simp)
            also have "\<dots> = \<bar>t - r\<bar>"
              using hdist_q_pos by (simp add: dist_norm norm_minus_commute)
            also have "\<dots> = d"
              unfolding t_def using hd_pos by (by100 simp)
            finally show ?thesis .
          qed
          have hdist_eps: "dist u x < \<epsilon>"
            using hdist_ux hd_lt_\<epsilon> by (by100 simp)
          show "\<exists>y\<in>(e - {w}) \<inter> ball w r. dist y x < \<epsilon>"
            using hu_set hdist_eps by (by100 blast)
        qed
      qed
      have hcases: "S = e\<^sub>1 \<or> S = e\<^sub>2 \<or> S = e\<^sub>3"
        using hS by (by100 simp)
      show "a \<in> closure ((S - {w}) \<inter> ball w r)"
        using hcases
      proof (elim disjE)
        assume hS_eq: "S = e\<^sub>1"
        have ha_eq: "a = x\<^sub>1"
          using hS_eq haS he\<^sub>1_sphere_punctured_eq by (by100 simp)
        have hx_cl: "x\<^sub>1 \<in> closure ((e\<^sub>1 - {w}) \<inter> ball w r)"
          by (rule hradial_closure[OF hq\<^sub>1w hr_lt_q\<^sub>1 he\<^sub>1_seg x\<^sub>1_def])
        show "a \<in> closure ((S - {w}) \<inter> ball w r)"
          using ha_eq hS_eq hx_cl by (by100 simp)
      next
        assume hS_eq: "S = e\<^sub>2"
        have ha_eq: "a = x\<^sub>2"
          using hS_eq haS he\<^sub>2_sphere_punctured_eq by (by100 simp)
        have hx_cl: "x\<^sub>2 \<in> closure ((e\<^sub>2 - {w}) \<inter> ball w r)"
          by (rule hradial_closure[OF hq\<^sub>2w hr_lt_q\<^sub>2 he\<^sub>2_seg x\<^sub>2_def])
        show "a \<in> closure ((S - {w}) \<inter> ball w r)"
          using ha_eq hS_eq hx_cl by (by100 simp)
      next
        assume hS_eq: "S = e\<^sub>3"
        have ha_eq: "a = x\<^sub>3"
          using hS_eq haS he\<^sub>3_sphere_punctured_eq by (by100 simp)
        have hx_cl: "x\<^sub>3 \<in> closure ((e\<^sub>3 - {w}) \<inter> ball w r)"
          by (rule hradial_closure[OF hq\<^sub>3w hr_lt_q\<^sub>3 he\<^sub>3_seg x\<^sub>3_def])
        show "a \<in> closure ((S - {w}) \<inter> ball w r)"
          using ha_eq hS_eq hx_cl by (by100 simp)
      qed
    qed
    have hcomponent_from_split_side:
        "\<And>S T U p y z N. S \<in> E
          \<Longrightarrow> T \<in> E
          \<Longrightarrow> U \<in> E
          \<Longrightarrow> S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<Longrightarrow> T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<Longrightarrow> U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<Longrightarrow> {S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}
          \<Longrightarrow> S \<noteq> T
          \<Longrightarrow> S \<noteq> U
          \<Longrightarrow> T \<noteq> U
          \<Longrightarrow> (S - {w}) \<inter> (T - {w}) = {}
          \<Longrightarrow> (S - {w}) \<inter> (U - {w}) = {}
          \<Longrightarrow> (T - {w}) \<inter> (U - {w}) = {}
          \<Longrightarrow> p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r
          \<Longrightarrow> y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r
          \<Longrightarrow> z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r
          \<Longrightarrow> p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<Longrightarrow> y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<Longrightarrow> z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<Longrightarrow> {p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}
          \<Longrightarrow> card {p, y, z} = 3
          \<Longrightarrow> p \<noteq> y
          \<Longrightarrow> p \<noteq> z
          \<Longrightarrow> y \<noteq> z
          \<Longrightarrow> N \<subseteq> geotop_polyhedron L - {w}
          \<Longrightarrow> top1_connected_on N
            (subspace_topology UNIV geotop_euclidean_topology N)
          \<Longrightarrow> p \<in> (S - {w}) \<inter> N
          \<Longrightarrow> y \<in> (T - {w}) \<inter> N
          \<Longrightarrow> top1_in_same_component_on (geotop_polyhedron L - {w})
            (subspace_topology UNIV geotop_euclidean_topology
              (geotop_polyhedron L - {w})) p y
          \<Longrightarrow> \<exists>C. C \<in> components (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))
            \<and> (S - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
            \<and> (T - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
            \<and> (U - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
    proof -
      fix S T U p y z N
      assume hS_E: "S \<in> E"
      assume hT_E: "T \<in> E"
      assume hU_E: "U \<in> E"
      assume hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      assume hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      assume hU: "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      assume hSTU_eq: "{S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      assume hST: "S \<noteq> T"
      assume hSU: "S \<noteq> U"
      assume hTU: "T \<noteq> U"
      assume hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
      assume hSU_disj: "(S - {w}) \<inter> (U - {w}) = {}"
      assume hTU_disj: "(T - {w}) \<inter> (U - {w}) = {}"
      assume hpS: "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
      assume hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
      assume hzU: "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r"
      assume hp_can: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      assume hy_can: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      assume hz_can: "z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      assume hpyz_eq: "{p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
      assume hcard: "card {p, y, z} = 3"
      assume hpy: "p \<noteq> y"
      assume hpz: "p \<noteq> z"
      assume hyz: "y \<noteq> z"
      assume hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
      assume hN_conn: "top1_connected_on N
        (subspace_topology UNIV geotop_euclidean_topology N)"
      assume hpSN: "p \<in> (S - {w}) \<inter> N"
      assume hyTN: "y \<in> (T - {w}) \<inter> N"
      assume hsame: "top1_in_same_component_on (geotop_polyhedron L - {w})
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron L - {w})) p y"
      have hp_selected_germ_closure:
          "p \<in> closure ((S - {w}) \<inter> ball w r)"
        by (rule hselected_sphere_germ_closure[OF hS hpS])
      have hy_selected_germ_closure:
          "y \<in> closure ((T - {w}) \<inter> ball w r)"
        by (rule hselected_sphere_germ_closure[OF hT hyT])
      have hz_selected_germ_closure:
          "z \<in> closure ((U - {w}) \<inter> ball w r)"
        by (rule hselected_sphere_germ_closure[OF hU hzU])
      have hselected_union_eq:
          "S \<union> T \<union> U = e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3"
        using hSTU_eq by (by100 blast)
      have hlocal_open:
          "open (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))"
      proof -
        have hclosed: "closed (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3)"
          unfolding he\<^sub>1_seg he\<^sub>2_seg he\<^sub>3_seg
          by (intro closed_Un closed_segment)
        show ?thesis
          by (rule open_Diff[OF open_ball hclosed])
      qed
      have hlocal_open_selected:
          "open (ball w r - (S \<union> T \<union> U))"
        using hlocal_open hselected_union_eq by (by100 simp)
      have hcomponent_path_connected:
          "\<And>C. C \<in> components (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))
            \<Longrightarrow> path_connected C"
        by (rule component_of_open_path_connected[OF hlocal_open])
      have hselected_punctured_carrier_sector_cover:
          "ball w r \<inter> (geotop_polyhedron L - {w})
            \<subseteq> ((S - {w}) \<inter> ball w r)
              \<union> ((T - {w}) \<inter> ball w r)
              \<union> ((U - {w}) \<inter> ball w r)
              \<union> (ball w r - (S \<union> T \<union> U))"
        using hlocal_punctured_carrier_sector_cover hSTU_eq hselected_union_eq
        by (by100 blast)
      have hN_ball_sector_cover:
          "N \<inter> ball w r
            \<subseteq> ((S - {w}) \<inter> ball w r)
              \<union> ((T - {w}) \<inter> ball w r)
              \<union> ((U - {w}) \<inter> ball w r)
              \<union> (ball w r - (S \<union> T \<union> U))"
        using hN_sub hselected_punctured_carrier_sector_cover by (by100 blast)
      have hsplit_side_endpoint_local_branch_book_step: False
        (**
          Book local branch step.  The connected split-side arc gives two
          distinct selected incident germs from the same endpoint of the
          simple closed curve.  Since the carrier is finite and locally a
          1-complex, the SCC arc side is locally a single broken-line endpoint
          segment; the third selected incident germ makes this impossible. **)
        sorry
      show "\<exists>C. C \<in> components (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))
        \<and> (S - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
        \<and> (T - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
        \<and> (U - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
        using hsplit_side_endpoint_local_branch_book_step by (by100 blast)
    qed
    show ?thesis
    proof -
      obtain S T U p y z N where hS_E: "S \<in> E"
        and hT_E: "T \<in> E"
        and hU_E: "U \<in> E"
        and hS: "S \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        and hT: "T \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        and hU: "U \<in> {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        and hSTU: "{S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
        and hST: "S \<noteq> T"
        and hSU: "S \<noteq> U"
        and hTU: "T \<noteq> U"
        and hST_disj: "(S - {w}) \<inter> (T - {w}) = {}"
        and hSU_disj: "(S - {w}) \<inter> (U - {w}) = {}"
        and hTU_disj: "(T - {w}) \<inter> (U - {w}) = {}"
        and hpS: "p \<in> (S - {w, q\<^sub>1}) \<inter> sphere w r"
        and hyT: "y \<in> (T - {w, q\<^sub>1}) \<inter> sphere w r"
        and hzU: "z \<in> (U - {w, q\<^sub>1}) \<inter> sphere w r"
        and hp_can: "p \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
        and hy_can: "y \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
        and hz_can: "z \<in> {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
        and hpyz_eq: "{p, y, z} = {x\<^sub>1, x\<^sub>2, x\<^sub>3}"
        and hcard: "card {p, y, z} = 3"
        and hpy: "p \<noteq> y"
        and hpz: "p \<noteq> z"
        and hyz: "y \<noteq> z"
        and hN_sub: "N \<subseteq> geotop_polyhedron L - {w}"
        and hN_conn: "top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)"
        and hpSN: "p \<in> (S - {w}) \<inter> N"
        and hyTN: "y \<in> (T - {w}) \<inter> N"
        and hsame: "top1_in_same_component_on (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w})) p y"
        using hsplit_side_three_connected_card by (elim exE conjE)
      have hex_component:
          "\<exists>C. C \<in> components (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))
            \<and> (S - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
            \<and> (T - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
            \<and> (U - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
        by (rule hcomponent_from_split_side
            [OF hS_E hT_E hU_E hS hT hU hSTU hST hSU hTU
              hST_disj hSU_disj hTU_disj hpS hyT hzU hp_can hy_can hz_can
              hpyz_eq hcard hpy hpz hyz hN_sub hN_conn hpSN hyTN hsame])
      obtain C where hC:
          "C \<in> components (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))"
        and hS_touch: "(S - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
        and hT_touch: "(T - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
        and hU_touch: "(U - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
        using hex_component by (elim exE conjE)
      have hbody: "C \<in> components (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))
        \<and> {S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}
        \<and> (S - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
        \<and> (T - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}
        \<and> (U - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
      proof (intro conjI)
        show "C \<in> components (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))" by (rule hC)
        show "{S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}" by (rule hSTU)
        show "(S - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}" by (rule hS_touch)
        show "(T - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}" by (rule hT_touch)
        show "(U - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}" by (rule hU_touch)
      qed
      show ?thesis
        by (rule exI[where x=C], rule exI[where x=S],
            rule exI[where x=T], rule exI[where x=U], rule hbody)
    qed
  qed
  have harc_side_disjoint_germs_local_star_impossible: False
    (**
      Remaining finite local-star calculation, now localized to the
      split-side package already constructed above.  We have three selected
      incident edge germs at \<open>w\<close>, two connected through one punctured
      arc side, then split that arc side at one selected sphere point.  The
      book step is to use the small star ball, the carrier-sector cover, and
      the three-radial-sector bound to show the split side cannot account for
      all three incident germs without making \<open>w\<close> a local branch point of the
      simple closed curve. **)
  proof -
    obtain C S T U where hC:
        "C \<in> components (ball w r - (e\<^sub>1 \<union> e\<^sub>2 \<union> e\<^sub>3))"
      and hSTU: "{S, T, U} = {e\<^sub>1, e\<^sub>2, e\<^sub>3}"
      and hS_touch: "(S - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
      and hT_touch: "(T - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
      and hU_touch: "(U - {w}) \<inter> ball w r \<inter> closure C \<noteq> {}"
      using hlocal_component_meets_selected_three_edges_book_step
      by (elim exE conjE)
    show False
      by (rule hno_local_component_meets_selected_three_edges
          [OF hC hSTU hS_touch hT_touch hU_touch])
  qed
  have hsame_arc_side_two_germs_impossible: False
    using harc_side_disjoint_germs_local_star_impossible by (by100 blast)
  have hlocal_sector_cut_book:
      "\<not> top1_connected_on (geotop_polyhedron L - {w})
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron L - {w}))"
    (**
      Remaining local-sector book step: choose three distinct incident
      1-simplexes \<open>e\<^sub>1,e\<^sub>2,e\<^sub>3\<close>, take sufficiently small punctured subsegments
      in the three edge germs at \<open>w\<close>, and use the finite linear complex
      intersection property to show any carrier path joining two selected
      sectors must pass through \<open>w\<close>. **)
    using hsame_arc_side_two_germs_impossible by (by100 blast)
  show ?thesis
    by (rule hlocal_sector_cut_book)
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
    by (rule geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
        [OF hL_linear hL_fin hwL hSCC hbranch])
  show ?thesis
    by (rule hbranch_local_disconnect)
qed

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

lemma geotop_degree_two_vertex_two_distinct_incident_edges_prefix:
  fixes L :: "(real^2) set set" and w :: "real^2"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hwL: "{w} \<in> L"
  shows "\<exists>e\<^sub>1 e\<^sub>2.
      e\<^sub>1 \<in> L \<and> e\<^sub>2 \<in> L
      \<and> geotop_is_edge e\<^sub>1 \<and> geotop_is_edge e\<^sub>2
      \<and> w \<in> e\<^sub>1 \<and> w \<in> e\<^sub>2
      \<and> e\<^sub>1 \<noteq> e\<^sub>2
      \<and> {e\<in>L. geotop_is_edge e \<and> w \<in> e} = {e\<^sub>1, e\<^sub>2}"
proof -
  let ?E = "{e\<in>L. geotop_is_edge e \<and> w \<in> e}"
  have hcard: "card ?E = 2"
    using hdegree hwL by (by100 blast)
  have hex: "\<exists>e\<^sub>1 e\<^sub>2. ?E = {e\<^sub>1, e\<^sub>2} \<and> e\<^sub>1 \<noteq> e\<^sub>2"
    using hcard by (simp only: card_2_iff)
  obtain e\<^sub>1 e\<^sub>2 where hE: "?E = {e\<^sub>1, e\<^sub>2}" and hne: "e\<^sub>1 \<noteq> e\<^sub>2"
    using hex by (by100 blast)
  have he\<^sub>1: "e\<^sub>1 \<in> L \<and> geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1"
    using hE hne by (by100 blast)
  have he\<^sub>2: "e\<^sub>2 \<in> L \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2"
    using hE hne by (by100 blast)
  show ?thesis
    using hE hne he\<^sub>1 he\<^sub>2 by (by100 blast)
qed

lemma geotop_card_two_member_cases_prefix:
  fixes A :: "'a set"
  assumes hcard: "card A = 2"
  assumes ha: "a \<in> A"
  assumes hb: "b \<in> A"
  assumes hab: "a \<noteq> b"
  assumes hx: "x \<in> A"
  shows "x = a \<or> x = b"
proof -
  have hex: "\<exists>u v. A = {u, v} \<and> u \<noteq> v"
    using hcard card_2_iff[of A] by (by100 simp)
  obtain u v where hA: "A = {u, v}" and huv: "u \<noteq> v"
    using hex by (by100 blast)
  have hA_ab: "A = {a, b}"
    using hA ha hb hab by (by100 blast)
  show ?thesis
    using hA_ab hx by (by100 blast)
qed

lemma geotop_degree_two_vertex_unique_other_incident_edge_prefix:
  fixes L :: "(real^2) set set" and w :: "real^2"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hwL: "{w} \<in> L"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "\<exists>!e'. e' \<in> L \<and> geotop_is_edge e' \<and> w \<in> e' \<and> e' \<noteq> e"
proof -
  let ?E = "{d\<in>L. geotop_is_edge d \<and> w \<in> d}"
  obtain e\<^sub>1 e\<^sub>2 where hE: "?E = {e\<^sub>1, e\<^sub>2}" and hne: "e\<^sub>1 \<noteq> e\<^sub>2"
    using geotop_degree_two_vertex_two_distinct_incident_edges_prefix
      [OF hdegree hwL] by (by100 blast)
  have heE: "e \<in> ?E"
    using heL hedge hwe by (by100 simp)
  have he_cases: "e = e\<^sub>1 \<or> e = e\<^sub>2"
    using hE heE by (by100 blast)
  show ?thesis
  proof (rule disjE[OF he_cases])
    assume he_eq: "e = e\<^sub>1"
    have he\<^sub>2_prop: "e\<^sub>2 \<in> L \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2 \<and> e\<^sub>2 \<noteq> e"
      using hE hne he_eq by (by100 blast)
    show ?thesis
    proof (rule ex1I[of _ e\<^sub>2])
      show "e\<^sub>2 \<in> L \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2 \<and> e\<^sub>2 \<noteq> e"
        by (rule he\<^sub>2_prop)
    next
      fix x
      assume hx: "x \<in> L \<and> geotop_is_edge x \<and> w \<in> x \<and> x \<noteq> e"
      have hxE: "x \<in> ?E"
        using hx by (by100 simp)
      have hx_cases: "x = e\<^sub>1 \<or> x = e\<^sub>2"
        using hE hxE by (by100 blast)
      show "x = e\<^sub>2"
        using hx hx_cases he_eq by (by100 blast)
    qed
  next
    assume he_eq: "e = e\<^sub>2"
    have he\<^sub>1_prop: "e\<^sub>1 \<in> L \<and> geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1 \<and> e\<^sub>1 \<noteq> e"
      using hE hne he_eq by (by100 blast)
    show ?thesis
    proof (rule ex1I[of _ e\<^sub>1])
      show "e\<^sub>1 \<in> L \<and> geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1 \<and> e\<^sub>1 \<noteq> e"
        by (rule he\<^sub>1_prop)
    next
      fix x
      assume hx: "x \<in> L \<and> geotop_is_edge x \<and> w \<in> x \<and> x \<noteq> e"
      have hxE: "x \<in> ?E"
        using hx by (by100 simp)
      have hx_cases: "x = e\<^sub>1 \<or> x = e\<^sub>2"
        using hE hxE by (by100 blast)
      show "x = e\<^sub>1"
        using hx hx_cases he_eq by (by100 blast)
    qed
  qed
qed

lemma geotop_incident_edge_other_endpoint_unique_prefix:
  fixes L :: "(real^2) set set" and w :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hwL: "{w} \<in> L"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "\<exists>!q. q \<noteq> w \<and> e = closed_segment w q \<and> {q} \<in> L"
proof -
  have hex: "\<exists>q. q \<noteq> w \<and> e = closed_segment w q \<and> {q} \<in> L"
    by (rule geotop_incident_edge_other_endpoint_vertex_prefix
        [OF hL hwL heL hedge hwe])
  show ?thesis
    using hex
  proof (elim exE)
    fix q
    assume hq: "q \<noteq> w \<and> e = closed_segment w q \<and> {q} \<in> L"
    have hqw: "q \<noteq> w"
      using hq by (by100 blast)
    have heq: "e = closed_segment w q"
      using hq by (by100 blast)
    have hqL: "{q} \<in> L"
      using hq by (by100 blast)
    show ?thesis
    proof (rule ex1I[of _ q])
      show "q \<noteq> w \<and> e = closed_segment w q \<and> {q} \<in> L"
        by (intro conjI hqw heq hqL)
    next
      fix y
      assume hy: "y \<noteq> w \<and> e = closed_segment w y \<and> {y} \<in> L"
      have hyw: "y \<noteq> w"
        using hy by (by100 blast)
      have hey: "e = closed_segment w y"
        using hy by (by100 blast)
      have hseg_eq: "closed_segment w q = closed_segment w y"
        using heq hey by (by100 simp)
      have hpair_eq: "{w, q} = {w, y}"
        using hseg_eq closed_segment_eq[of w q w y] by (by100 simp)
      have hq_mem: "q \<in> {w, y}"
        using hpair_eq by (by100 blast)
      have hq_cases: "q = w \<or> q = y"
        using hq_mem by (by100 simp)
      show "y = q"
        using hq_cases hqw by (by100 blast)
    qed
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_prefix:
  fixes L :: "(real^2) set set" and w :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hwL: "{w} \<in> L"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "\<exists>q e'. q \<noteq> w
      \<and> e = closed_segment w q
      \<and> {q} \<in> L
      \<and> e' \<in> L
      \<and> geotop_is_edge e'
      \<and> q \<in> e'
      \<and> e' \<noteq> e
      \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e')"
proof -
  obtain q where hqw: "q \<noteq> w" and heq: "e = closed_segment w q" and hqL: "{q} \<in> L"
    using geotop_incident_edge_other_endpoint_vertex_prefix
      [OF hL hwL heL hedge hwe] by (by100 blast)
  have hqe: "q \<in> e"
    using heq by (by100 simp)
  have huniq_ex: "\<exists>!e'. e' \<in> L \<and> geotop_is_edge e' \<and> q \<in> e' \<and> e' \<noteq> e"
    by (rule geotop_degree_two_vertex_unique_other_incident_edge_prefix
        [OF hdegree hqL heL hedge hqe])
  obtain e' where he'_prop:
      "e' \<in> L \<and> geotop_is_edge e' \<and> q \<in> e' \<and> e' \<noteq> e"
      and he'_uniq_all:
      "\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e'"
    using huniq_ex unfolding Ex1_def by (by100 blast)
  have he'_uniq:
      "\<And>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<Longrightarrow> d = e'"
    using he'_uniq_all by (by100 blast)
  show ?thesis
  proof (intro exI conjI allI impI)
    show "q \<noteq> w" by (rule hqw)
    show "e = closed_segment w q" by (rule heq)
    show "{q} \<in> L" by (rule hqL)
    show "e' \<in> L" using he'_prop by (by100 blast)
    show "geotop_is_edge e'" using he'_prop by (by100 blast)
    show "q \<in> e'" using he'_prop by (by100 blast)
    show "e' \<noteq> e" using he'_prop by (by100 blast)
    fix d
    assume hd: "d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e"
    show "d = e'"
      by (rule he'_uniq[OF hd])
  qed
qed

lemma geotop_degree_two_vertex_incident_neighbor_prefix:
  fixes L :: "(real^2) set set" and w :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hwL: "{w} \<in> L"
  shows "\<exists>e q. e \<in> L
      \<and> geotop_is_edge e
      \<and> w \<in> e
      \<and> q \<noteq> w
      \<and> e = closed_segment w q
      \<and> {q} \<in> L"
proof -
  obtain e\<^sub>1 e\<^sub>2 where he\<^sub>1L: "e\<^sub>1 \<in> L"
      and he\<^sub>1edge: "geotop_is_edge e\<^sub>1"
      and hwe\<^sub>1: "w \<in> e\<^sub>1"
    using geotop_degree_two_vertex_two_distinct_incident_edges_prefix
      [OF hdegree hwL] by (by100 blast)
  have hex_q: "\<exists>q. q \<noteq> w \<and> e\<^sub>1 = closed_segment w q \<and> {q} \<in> L"
    by (rule geotop_incident_edge_other_endpoint_vertex_prefix
        [OF hL hwL he\<^sub>1L he\<^sub>1edge hwe\<^sub>1])
  obtain q where hqw: "q \<noteq> w"
      and he\<^sub>1q: "e\<^sub>1 = closed_segment w q"
      and hqL: "{q} \<in> L"
    using hex_q by (by100 blast)
  show ?thesis
    using he\<^sub>1L he\<^sub>1edge hwe\<^sub>1 hqw he\<^sub>1q hqL by (by100 blast)
qed

lemma geotop_degree_two_vertex_initial_oriented_edge_state_prefix:
  fixes L :: "(real^2) set set" and w :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hwL: "{w} \<in> L"
  shows "\<exists>s q. s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> fst s = w
      \<and> q \<noteq> w
      \<and> snd s = closed_segment w q
      \<and> {q} \<in> L"
proof -
  obtain e q where heL: "e \<in> L"
      and hedge: "geotop_is_edge e"
      and hwe: "w \<in> e"
      and hqw: "q \<noteq> w"
      and heq: "e = closed_segment w q"
      and hqL: "{q} \<in> L"
    using geotop_degree_two_vertex_incident_neighbor_prefix
      [OF hL hdegree hwL] by (by100 blast)
  have hstate: "(w, e) \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
    using hwL heL hedge hwe by (by100 simp)
  show ?thesis
  proof (intro exI conjI)
    show "(w, e) \<in>
        {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
      by (rule hstate)
    show "fst (w, e) = w"
      by (by100 simp)
    show "q \<noteq> w"
      by (rule hqw)
    show "snd (w, e) = closed_segment w q"
      using heq by (by100 simp)
    show "{q} \<in> L"
      by (rule hqL)
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_endpoint_prefix:
  fixes L :: "(real^2) set set" and w :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hwL: "{w} \<in> L"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "\<exists>q e' r. q \<noteq> w
      \<and> e = closed_segment w q
      \<and> {q} \<in> L
      \<and> e' \<in> L
      \<and> geotop_is_edge e'
      \<and> q \<in> e'
      \<and> e' \<noteq> e
      \<and> r \<noteq> q
      \<and> e' = closed_segment q r
      \<and> {r} \<in> L
      \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e')"
proof -
  have hex_succ: "\<exists>q e'. q \<noteq> w
      \<and> e = closed_segment w q
      \<and> {q} \<in> L
      \<and> e' \<in> L
      \<and> geotop_is_edge e'
      \<and> q \<in> e'
      \<and> e' \<noteq> e
      \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e')"
    by (rule geotop_degree_two_oriented_edge_successor_prefix
        [OF hL hdegree hwL heL hedge hwe])
  show ?thesis
    using hex_succ
  proof (elim exE)
    fix q e'
    assume hsucc: "q \<noteq> w
        \<and> e = closed_segment w q
        \<and> {q} \<in> L
        \<and> e' \<in> L
        \<and> geotop_is_edge e'
        \<and> q \<in> e'
        \<and> e' \<noteq> e
        \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e')"
    have hqw: "q \<noteq> w"
      using hsucc by (by100 blast)
    have heq: "e = closed_segment w q"
      using hsucc by (by100 blast)
    have hqL: "{q} \<in> L"
      using hsucc by (by100 blast)
    have he'L: "e' \<in> L"
      using hsucc by (by100 blast)
    have he'edge: "geotop_is_edge e'"
      using hsucc by (by100 blast)
    have hqe': "q \<in> e'"
      using hsucc by (by100 blast)
    have he'ne: "e' \<noteq> e"
      using hsucc by (by100 blast)
    have he'uniq:
        "\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e'"
      using hsucc by (by100 blast)
    have hex_r: "\<exists>r. r \<noteq> q \<and> e' = closed_segment q r \<and> {r} \<in> L"
      by (rule geotop_incident_edge_other_endpoint_vertex_prefix
          [OF hL hqL he'L he'edge hqe'])
    obtain r where hrq: "r \<noteq> q"
        and he'r: "e' = closed_segment q r"
        and hrL: "{r} \<in> L"
      using hex_r by (by100 blast)
    show ?thesis
    proof (intro exI conjI allI impI)
      show "q \<noteq> w" by (rule hqw)
      show "e = closed_segment w q" by (rule heq)
      show "{q} \<in> L" by (rule hqL)
      show "e' \<in> L" by (rule he'L)
      show "geotop_is_edge e'" by (rule he'edge)
      show "q \<in> e'" by (rule hqe')
      show "e' \<noteq> e" by (rule he'ne)
      show "r \<noteq> q" by (rule hrq)
      show "e' = closed_segment q r" by (rule he'r)
      show "{r} \<in> L" by (rule hrL)
      fix d
      assume hd: "d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e"
      show "d = e'"
        using he'uniq hd by (by100 blast)
    qed
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_nonbacktracking_prefix:
  fixes L :: "(real^2) set set" and w :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hwL: "{w} \<in> L"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "\<exists>q e' r. q \<noteq> w
      \<and> e = closed_segment w q
      \<and> {q} \<in> L
      \<and> e' \<in> L
      \<and> geotop_is_edge e'
      \<and> q \<in> e'
      \<and> e' \<noteq> e
      \<and> r \<noteq> q
      \<and> r \<noteq> w
      \<and> e' = closed_segment q r
      \<and> {r} \<in> L
      \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e')"
proof -
  have hex_succ: "\<exists>q e' r. q \<noteq> w
      \<and> e = closed_segment w q
      \<and> {q} \<in> L
      \<and> e' \<in> L
      \<and> geotop_is_edge e'
      \<and> q \<in> e'
      \<and> e' \<noteq> e
      \<and> r \<noteq> q
      \<and> e' = closed_segment q r
      \<and> {r} \<in> L
      \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e')"
    by (rule geotop_degree_two_oriented_edge_successor_endpoint_prefix
        [OF hL hdegree hwL heL hedge hwe])
  show ?thesis
    using hex_succ
  proof (elim exE)
    fix q e' r
    assume hsucc: "q \<noteq> w
        \<and> e = closed_segment w q
        \<and> {q} \<in> L
        \<and> e' \<in> L
        \<and> geotop_is_edge e'
        \<and> q \<in> e'
        \<and> e' \<noteq> e
        \<and> r \<noteq> q
        \<and> e' = closed_segment q r
        \<and> {r} \<in> L
        \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e')"
    have hqw: "q \<noteq> w"
      using hsucc by (by100 blast)
    have heq: "e = closed_segment w q"
      using hsucc by (by100 blast)
    have hqL: "{q} \<in> L"
      using hsucc by (by100 blast)
    have he'L: "e' \<in> L"
      using hsucc by (by100 blast)
    have he'edge: "geotop_is_edge e'"
      using hsucc by (by100 blast)
    have hqe': "q \<in> e'"
      using hsucc by (by100 blast)
    have he'ne: "e' \<noteq> e"
      using hsucc by (by100 blast)
    have hrq: "r \<noteq> q"
      using hsucc by (by100 blast)
    have he'r: "e' = closed_segment q r"
      using hsucc by (by100 blast)
    have hrL: "{r} \<in> L"
      using hsucc by (by100 blast)
    have he'uniq:
        "\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e'"
      using hsucc by (by100 blast)
    have hrw: "r \<noteq> w"
    proof
      assume hrw_eq: "r = w"
      have hseg_eq: "closed_segment q r = closed_segment w q"
        using hrw_eq closed_segment_commute[of q w] by (by100 simp)
      have "e' = e"
        using he'r heq hseg_eq by (by100 simp)
      show False
        using he'ne \<open>e' = e\<close> by (by100 blast)
    qed
    show ?thesis
    proof (intro exI conjI allI impI)
      show "q \<noteq> w" by (rule hqw)
      show "e = closed_segment w q" by (rule heq)
      show "{q} \<in> L" by (rule hqL)
      show "e' \<in> L" by (rule he'L)
      show "geotop_is_edge e'" by (rule he'edge)
      show "q \<in> e'" by (rule hqe')
      show "e' \<noteq> e" by (rule he'ne)
      show "r \<noteq> q" by (rule hrq)
      show "r \<noteq> w" by (rule hrw)
      show "e' = closed_segment q r" by (rule he'r)
      show "{r} \<in> L" by (rule hrL)
      fix d
      assume hd: "d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e"
      show "d = e'"
        using he'uniq hd by (by100 blast)
    qed
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_triple_unique_prefix:
  fixes L :: "(real^2) set set" and w :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hwL: "{w} \<in> L"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "\<exists>q e' r. q \<noteq> w
      \<and> e = closed_segment w q
      \<and> {q} \<in> L
      \<and> e' \<in> L
      \<and> geotop_is_edge e'
      \<and> q \<in> e'
      \<and> e' \<noteq> e
      \<and> r \<noteq> q
      \<and> r \<noteq> w
      \<and> e' = closed_segment q r
      \<and> {r} \<in> L
      \<and> (\<forall>q' e'' r'. q' \<noteq> w
          \<and> e = closed_segment w q'
          \<and> {q'} \<in> L
          \<and> e'' \<in> L
          \<and> geotop_is_edge e''
          \<and> q' \<in> e''
          \<and> e'' \<noteq> e
          \<and> r' \<noteq> q'
          \<and> r' \<noteq> w
          \<and> e'' = closed_segment q' r'
          \<and> {r'} \<in> L
          \<longrightarrow> q' = q \<and> e'' = e' \<and> r' = r)"
proof -
  have hex_succ: "\<exists>q e' r. q \<noteq> w
      \<and> e = closed_segment w q
      \<and> {q} \<in> L
      \<and> e' \<in> L
      \<and> geotop_is_edge e'
      \<and> q \<in> e'
      \<and> e' \<noteq> e
      \<and> r \<noteq> q
      \<and> r \<noteq> w
      \<and> e' = closed_segment q r
      \<and> {r} \<in> L
      \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e')"
    by (rule geotop_degree_two_oriented_edge_successor_nonbacktracking_prefix
        [OF hL hdegree hwL heL hedge hwe])
  show ?thesis
    using hex_succ
  proof (elim exE)
    fix q e' r
    assume hsucc: "q \<noteq> w
        \<and> e = closed_segment w q
        \<and> {q} \<in> L
        \<and> e' \<in> L
        \<and> geotop_is_edge e'
        \<and> q \<in> e'
        \<and> e' \<noteq> e
        \<and> r \<noteq> q
        \<and> r \<noteq> w
        \<and> e' = closed_segment q r
        \<and> {r} \<in> L
        \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e')"
    have hqw: "q \<noteq> w"
      using hsucc by (by100 blast)
    have heq: "e = closed_segment w q"
      using hsucc by (by100 blast)
    have hqL: "{q} \<in> L"
      using hsucc by (by100 blast)
    have he'L: "e' \<in> L"
      using hsucc by (by100 blast)
    have he'edge: "geotop_is_edge e'"
      using hsucc by (by100 blast)
    have hqe': "q \<in> e'"
      using hsucc by (by100 blast)
    have he'ne: "e' \<noteq> e"
      using hsucc by (by100 blast)
    have hrq: "r \<noteq> q"
      using hsucc by (by100 blast)
    have hrw: "r \<noteq> w"
      using hsucc by (by100 blast)
    have he'r: "e' = closed_segment q r"
      using hsucc by (by100 blast)
    have hrL: "{r} \<in> L"
      using hsucc by (by100 blast)
    have he'_uniq:
        "\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e'"
      using hsucc by (by100 blast)
    have hqe: "q \<in> e"
      using heq by (by100 simp)
    have hother_q_unique: "\<exists>!x. x \<noteq> w \<and> e = closed_segment w x \<and> {x} \<in> L"
      by (rule geotop_incident_edge_other_endpoint_unique_prefix
          [OF hL hwL heL hedge hwe])
    have hother_r_unique: "\<exists>!x. x \<noteq> q \<and> e' = closed_segment q x \<and> {x} \<in> L"
      by (rule geotop_incident_edge_other_endpoint_unique_prefix
          [OF hL hqL he'L he'edge hqe'])
    show ?thesis
    proof (intro exI conjI)
      show "q \<noteq> w" by (rule hqw)
      show "e = closed_segment w q" by (rule heq)
      show "{q} \<in> L" by (rule hqL)
      show "e' \<in> L" by (rule he'L)
      show "geotop_is_edge e'" by (rule he'edge)
      show "q \<in> e'" by (rule hqe')
      show "e' \<noteq> e" by (rule he'ne)
      show "r \<noteq> q" by (rule hrq)
      show "r \<noteq> w" by (rule hrw)
      show "e' = closed_segment q r" by (rule he'r)
      show "{r} \<in> L" by (rule hrL)
      show "\<forall>q' e'' r'. q' \<noteq> w
          \<and> e = closed_segment w q'
          \<and> {q'} \<in> L
          \<and> e'' \<in> L
          \<and> geotop_is_edge e''
          \<and> q' \<in> e''
          \<and> e'' \<noteq> e
          \<and> r' \<noteq> q'
          \<and> r' \<noteq> w
          \<and> e'' = closed_segment q' r'
          \<and> {r'} \<in> L
          \<longrightarrow> q' = q \<and> e'' = e' \<and> r' = r"
      proof (intro allI impI)
        fix q' e'' r'
        assume hcand: "q' \<noteq> w
            \<and> e = closed_segment w q'
            \<and> {q'} \<in> L
            \<and> e'' \<in> L
            \<and> geotop_is_edge e''
            \<and> q' \<in> e''
            \<and> e'' \<noteq> e
            \<and> r' \<noteq> q'
            \<and> r' \<noteq> w
            \<and> e'' = closed_segment q' r'
            \<and> {r'} \<in> L"
        have hq'w: "q' \<noteq> w"
          using hcand by (by100 blast)
        have heq': "e = closed_segment w q'"
          using hcand by (by100 blast)
        have hq'L: "{q'} \<in> L"
          using hcand by (by100 blast)
        have he''L: "e'' \<in> L"
          using hcand by (by100 blast)
        have he''edge: "geotop_is_edge e''"
          using hcand by (by100 blast)
        have hq'e'': "q' \<in> e''"
          using hcand by (by100 blast)
        have he''ne: "e'' \<noteq> e"
          using hcand by (by100 blast)
        have hr'q': "r' \<noteq> q'"
          using hcand by (by100 blast)
        have he''r': "e'' = closed_segment q' r'"
          using hcand by (by100 blast)
        have hr'L: "{r'} \<in> L"
          using hcand by (by100 blast)
        have hq'_eq: "q' = q"
          using hother_q_unique hqw heq hqL hq'w heq' hq'L
          unfolding Ex1_def by (by100 blast)
        have hq_e'': "q \<in> e''"
          using hq'e'' hq'_eq by (by100 simp)
        have he''_eq: "e'' = e'"
          using he'_uniq he''L he''edge hq_e'' he''ne by (by100 blast)
        have hr'q: "r' \<noteq> q"
          using hr'q' hq'_eq by (by100 simp)
        have he'r': "e' = closed_segment q r'"
          using he''r' hq'_eq he''_eq by (by100 simp)
        have hr'_eq: "r' = r"
          using hother_r_unique hrq he'r hrL hr'q he'r' hr'L
          unfolding Ex1_def by (by100 blast)
        show "q' = q \<and> e'' = e' \<and> r' = r"
          using hq'_eq he''_eq hr'_eq by (by100 blast)
      qed
    qed
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_state_prefix:
  fixes L :: "(real^2) set set" and w :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hwL: "{w} \<in> L"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "\<exists>q e'. (q, e') \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> q \<noteq> w
      \<and> e = closed_segment w q
      \<and> e' \<noteq> e
      \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e')"
proof -
  have hex: "\<exists>q e'. q \<noteq> w
      \<and> e = closed_segment w q
      \<and> {q} \<in> L
      \<and> e' \<in> L
      \<and> geotop_is_edge e'
      \<and> q \<in> e'
      \<and> e' \<noteq> e
      \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e')"
    by (rule geotop_degree_two_oriented_edge_successor_prefix
        [OF hL hdegree hwL heL hedge hwe])
  show ?thesis
    using hex by (by100 blast)
qed

lemma geotop_degree_two_oriented_edge_successor_state_unique_prefix:
  fixes L :: "(real^2) set set" and w :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hwL: "{w} \<in> L"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  assumes hsucc1: "(q\<^sub>1, e\<^sub>1) \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> q\<^sub>1 \<noteq> w
      \<and> e = closed_segment w q\<^sub>1
      \<and> e\<^sub>1 \<noteq> e
      \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q\<^sub>1 \<in> d \<and> d \<noteq> e \<longrightarrow> d = e\<^sub>1)"
  assumes hsucc2: "(q\<^sub>2, e\<^sub>2) \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> q\<^sub>2 \<noteq> w
      \<and> e = closed_segment w q\<^sub>2
      \<and> e\<^sub>2 \<noteq> e
      \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q\<^sub>2 \<in> d \<and> d \<noteq> e \<longrightarrow> d = e\<^sub>2)"
  shows "q\<^sub>1 = q\<^sub>2 \<and> e\<^sub>1 = e\<^sub>2"
proof -
  have hq1w: "q\<^sub>1 \<noteq> w"
    using hsucc1 by (by100 blast)
  have heq1: "e = closed_segment w q\<^sub>1"
    using hsucc1 by (by100 blast)
  have hq1L: "{q\<^sub>1} \<in> L"
    using hsucc1 by (by100 blast)
  have hq2w: "q\<^sub>2 \<noteq> w"
    using hsucc2 by (by100 blast)
  have heq2: "e = closed_segment w q\<^sub>2"
    using hsucc2 by (by100 blast)
  have hq2L: "{q\<^sub>2} \<in> L"
    using hsucc2 by (by100 blast)
  have hother_unique: "\<exists>!x. x \<noteq> w \<and> e = closed_segment w x \<and> {x} \<in> L"
    by (rule geotop_incident_edge_other_endpoint_unique_prefix
        [OF hL hwL heL hedge hwe])
  have hq2_eq_q1: "q\<^sub>2 = q\<^sub>1"
    using hother_unique hq1w heq1 hq1L hq2w heq2 hq2L
    unfolding Ex1_def by (by100 blast)
  have he2L: "e\<^sub>2 \<in> L"
    using hsucc2 by (by100 blast)
  have he2edge: "geotop_is_edge e\<^sub>2"
    using hsucc2 by (by100 blast)
  have hq2e2: "q\<^sub>2 \<in> e\<^sub>2"
    using hsucc2 by (by100 blast)
  have he2ne: "e\<^sub>2 \<noteq> e"
    using hsucc2 by (by100 blast)
  have hq1e2: "q\<^sub>1 \<in> e\<^sub>2"
    using hq2e2 hq2_eq_q1 by (by100 simp)
  have huniq1: "\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q\<^sub>1 \<in> d \<and> d \<noteq> e \<longrightarrow> d = e\<^sub>1"
    using hsucc1 by (by100 blast)
  have he2_eq_e1: "e\<^sub>2 = e\<^sub>1"
    using huniq1 he2L he2edge hq1e2 he2ne by (by100 blast)
  show ?thesis
    using hq2_eq_q1 he2_eq_e1 by (by100 blast)
qed

definition geotop_oriented_edge_successor_state
  where "geotop_oriented_edge_successor_state (L::(real^2) set set) s t \<longleftrightarrow>
    {fst s} \<in> L
    \<and> snd s \<in> L
    \<and> geotop_is_edge (snd s)
    \<and> fst s \<in> snd s
    \<and> t \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
    \<and> fst t \<noteq> fst s
    \<and> snd s = closed_segment (fst s) (fst t)
    \<and> snd t \<noteq> snd s
    \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> fst t \<in> d \<and> d \<noteq> snd s
      \<longrightarrow> d = snd t)"

definition geotop_oriented_edge_successor
  where "geotop_oriented_edge_successor (L::(real^2) set set) s =
    (THE t. t \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> geotop_oriented_edge_successor_state L s t)"

lemma geotop_degree_two_oriented_edge_successor_relation_total_unique_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  shows "\<exists>!t. t \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> geotop_oriented_edge_successor_state L s t"
proof -
  obtain w e where hs_eq: "s = (w, e)"
    by (cases s) (by100 blast)
  have hwL: "{w} \<in> L"
    using hs hs_eq by (by100 blast)
  have heL: "e \<in> L"
    using hs hs_eq by (by100 blast)
  have hedge: "geotop_is_edge e"
    using hs hs_eq by (by100 blast)
  have hwe: "w \<in> e"
    using hs hs_eq by (by100 blast)
  have hex: "\<exists>q e'. (q, e') \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> q \<noteq> w
      \<and> e = closed_segment w q
      \<and> e' \<noteq> e
      \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e')"
    by (rule geotop_degree_two_oriented_edge_successor_state_prefix
        [OF hL hdegree hwL heL hedge hwe])
  show ?thesis
  proof (rule ex_ex1I)
    show "\<exists>t. t \<in>
        {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
        \<and> geotop_oriented_edge_successor_state L s t"
    proof -
      from hex obtain q e' where hsucc: "(q, e') \<in>
          {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
          \<and> q \<noteq> w
          \<and> e = closed_segment w q
          \<and> e' \<noteq> e
          \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e \<longrightarrow> d = e')"
        by (elim exE)
      have hstate: "(q, e') \<in>
          {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
        using hsucc by (by100 blast)
      have hrel: "geotop_oriented_edge_successor_state L s (q, e')"
        using hwL heL hedge hwe hsucc hs_eq
        unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
      show ?thesis
        using hstate hrel by (by100 blast)
    qed
  next
    fix t\<^sub>1 t\<^sub>2
    assume ht1: "t\<^sub>1 \<in>
        {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
        \<and> geotop_oriented_edge_successor_state L s t\<^sub>1"
    assume ht2: "t\<^sub>2 \<in>
        {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
        \<and> geotop_oriented_edge_successor_state L s t\<^sub>2"
    obtain q\<^sub>1 e\<^sub>1 where ht1_eq: "t\<^sub>1 = (q\<^sub>1, e\<^sub>1)"
      by (cases t\<^sub>1) (by100 blast)
    obtain q\<^sub>2 e\<^sub>2 where ht2_eq: "t\<^sub>2 = (q\<^sub>2, e\<^sub>2)"
      by (cases t\<^sub>2) (by100 blast)
    have hsucc1: "(q\<^sub>1, e\<^sub>1) \<in>
        {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
        \<and> q\<^sub>1 \<noteq> w
        \<and> e = closed_segment w q\<^sub>1
        \<and> e\<^sub>1 \<noteq> e
        \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q\<^sub>1 \<in> d \<and> d \<noteq> e \<longrightarrow> d = e\<^sub>1)"
      using ht1 hs_eq ht1_eq
      unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
    have hsucc2: "(q\<^sub>2, e\<^sub>2) \<in>
        {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
        \<and> q\<^sub>2 \<noteq> w
        \<and> e = closed_segment w q\<^sub>2
        \<and> e\<^sub>2 \<noteq> e
        \<and> (\<forall>d. d \<in> L \<and> geotop_is_edge d \<and> q\<^sub>2 \<in> d \<and> d \<noteq> e \<longrightarrow> d = e\<^sub>2)"
      using ht2 hs_eq ht2_eq
      unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
    have heq: "q\<^sub>1 = q\<^sub>2 \<and> e\<^sub>1 = e\<^sub>2"
      by (rule geotop_degree_two_oriented_edge_successor_state_unique_prefix
          [OF hL hdegree hwL heL hedge hwe hsucc1 hsucc2])
    show "t\<^sub>1 = t\<^sub>2"
      using ht1_eq ht2_eq heq by (by100 blast)
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_fun_step_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  shows "geotop_oriented_edge_successor L s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> geotop_oriented_edge_successor_state L s
          (geotop_oriented_edge_successor L s)"
proof -
  have hex1: "\<exists>!t. t \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> geotop_oriented_edge_successor_state L s t"
    by (rule geotop_degree_two_oriented_edge_successor_relation_total_unique_prefix
        [OF hL hdegree hs])
  show ?thesis
    unfolding geotop_oriented_edge_successor_def
    using hex1 by (rule theI')
qed

lemma geotop_degree_two_oriented_edge_successor_step_incident_edge_cases_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hinc: "fst (geotop_oriented_edge_successor L s) \<in> e"
  shows "e = snd s \<or> e = snd (geotop_oriented_edge_successor L s)"
proof -
  have hstep: "geotop_oriented_edge_successor L s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> geotop_oriented_edge_successor_state L s
          (geotop_oriented_edge_successor L s)"
    by (rule geotop_degree_two_oriented_edge_successor_fun_step_prefix
        [OF hL hdegree hs])
  have hrel: "geotop_oriented_edge_successor_state L s
      (geotop_oriented_edge_successor L s)"
    by (rule conjunct2[OF hstep])
  show ?thesis
  proof (cases "e = snd s")
    case True
    show ?thesis
      using True by (by100 blast)
  next
    case False
    have huniq: "\<forall>d. d \<in> L \<and> geotop_is_edge d
        \<and> fst (geotop_oriented_edge_successor L s) \<in> d
        \<and> d \<noteq> snd s
        \<longrightarrow> d = snd (geotop_oriented_edge_successor L s)"
      using hrel unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
    have "e = snd (geotop_oriented_edge_successor L s)"
      using huniq heL hedge hinc False by (by100 blast)
    show ?thesis
      using \<open>e = snd (geotop_oriented_edge_successor L s)\<close> by (by100 blast)
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_state_predecessor_unique_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hsucc1: "geotop_oriented_edge_successor_state L s\<^sub>1 t"
  assumes hsucc2: "geotop_oriented_edge_successor_state L s\<^sub>2 t"
  shows "s\<^sub>1 = s\<^sub>2"
proof -
  obtain w\<^sub>1 e\<^sub>1 where hs1_eq: "s\<^sub>1 = (w\<^sub>1, e\<^sub>1)"
    by (cases s\<^sub>1) (by100 blast)
  obtain w\<^sub>2 e\<^sub>2 where hs2_eq: "s\<^sub>2 = (w\<^sub>2, e\<^sub>2)"
    by (cases s\<^sub>2) (by100 blast)
  obtain q e' where ht_eq: "t = (q, e')"
    by (cases t) (by100 blast)
  have hqL: "{q} \<in> L"
    using hsucc1 hs1_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have he'L: "e' \<in> L"
    using hsucc1 hs1_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have he'edge: "geotop_is_edge e'"
    using hsucc1 hs1_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have hqe': "q \<in> e'"
    using hsucc1 hs1_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have hw1L: "{w\<^sub>1} \<in> L"
    using hsucc1 hs1_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have he1L: "e\<^sub>1 \<in> L"
    using hsucc1 hs1_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have he1edge: "geotop_is_edge e\<^sub>1"
    using hsucc1 hs1_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have hqw1: "q \<noteq> w\<^sub>1"
    using hsucc1 hs1_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have hw1q: "w\<^sub>1 \<noteq> q"
    using hqw1 by (by100 simp)
  have he1_seg: "e\<^sub>1 = closed_segment w\<^sub>1 q"
    using hsucc1 hs1_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have he'_ne_e1: "e' \<noteq> e\<^sub>1"
    using hsucc1 hs1_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have he1_ne_e': "e\<^sub>1 \<noteq> e'"
    using he'_ne_e1 by (by100 simp)
  have hw2L: "{w\<^sub>2} \<in> L"
    using hsucc2 hs2_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have he2L: "e\<^sub>2 \<in> L"
    using hsucc2 hs2_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have he2edge: "geotop_is_edge e\<^sub>2"
    using hsucc2 hs2_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have hqw2: "q \<noteq> w\<^sub>2"
    using hsucc2 hs2_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have hw2q: "w\<^sub>2 \<noteq> q"
    using hqw2 by (by100 simp)
  have he2_seg: "e\<^sub>2 = closed_segment w\<^sub>2 q"
    using hsucc2 hs2_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have he'_ne_e2: "e' \<noteq> e\<^sub>2"
    using hsucc2 hs2_eq ht_eq
    unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have he2_ne_e': "e\<^sub>2 \<noteq> e'"
    using he'_ne_e2 by (by100 simp)
  have hqe1: "q \<in> e\<^sub>1"
    using he1_seg by (by100 simp)
  have hqe2: "q \<in> e\<^sub>2"
    using he2_seg by (by100 simp)
  have hother_edge_unique:
      "\<exists>!d. d \<in> L \<and> geotop_is_edge d \<and> q \<in> d \<and> d \<noteq> e'"
    by (rule geotop_degree_two_vertex_unique_other_incident_edge_prefix
        [OF hdegree hqL he'L he'edge hqe'])
  have he1_prop:
      "e\<^sub>1 \<in> L \<and> geotop_is_edge e\<^sub>1 \<and> q \<in> e\<^sub>1 \<and> e\<^sub>1 \<noteq> e'"
    by (intro conjI he1L he1edge hqe1 he1_ne_e')
  have he2_prop:
      "e\<^sub>2 \<in> L \<and> geotop_is_edge e\<^sub>2 \<and> q \<in> e\<^sub>2 \<and> e\<^sub>2 \<noteq> e'"
    by (intro conjI he2L he2edge hqe2 he2_ne_e')
  obtain e\<^sub>0 where he0_prop:
      "e\<^sub>0 \<in> L \<and> geotop_is_edge e\<^sub>0 \<and> q \<in> e\<^sub>0 \<and> e\<^sub>0 \<noteq> e'"
    and he0_uniq: "\<forall>y. y \<in> L \<and> geotop_is_edge y \<and> q \<in> y \<and> y \<noteq> e' \<longrightarrow> y = e\<^sub>0"
    using hother_edge_unique unfolding Ex1_def by (by100 blast)
  have he1_eq_e0: "e\<^sub>1 = e\<^sub>0"
    using he0_uniq he1_prop by (by100 blast)
  have he2_eq_e0: "e\<^sub>2 = e\<^sub>0"
    using he0_uniq he2_prop by (by100 blast)
  have he2_eq_e1: "e\<^sub>2 = e\<^sub>1"
    using he1_eq_e0 he2_eq_e0 by (by100 simp)
  have he1_qw1: "e\<^sub>1 = closed_segment q w\<^sub>1"
    using he1_seg closed_segment_commute[of w\<^sub>1 q] by (by100 simp)
  have he1_qw2: "e\<^sub>1 = closed_segment q w\<^sub>2"
    using he2_seg he2_eq_e1 closed_segment_commute[of w\<^sub>2 q] by (by100 simp)
  have hendpoint_unique:
      "\<exists>!x. x \<noteq> q \<and> e\<^sub>1 = closed_segment q x \<and> {x} \<in> L"
    by (rule geotop_incident_edge_other_endpoint_unique_prefix
        [OF hL hqL he1L he1edge hqe1])
  obtain w\<^sub>0 where hw0_prop:
      "w\<^sub>0 \<noteq> q \<and> e\<^sub>1 = closed_segment q w\<^sub>0 \<and> {w\<^sub>0} \<in> L"
    and hw0_uniq: "\<forall>y. y \<noteq> q \<and> e\<^sub>1 = closed_segment q y \<and> {y} \<in> L
      \<longrightarrow> y = w\<^sub>0"
    using hendpoint_unique unfolding Ex1_def by (by100 blast)
  have hw1_eq_w0: "w\<^sub>1 = w\<^sub>0"
    using hw0_uniq hw1q he1_qw1 hw1L by (by100 blast)
  have hw2_eq_w0: "w\<^sub>2 = w\<^sub>0"
    using hw0_uniq hw2q he1_qw2 hw2L by (by100 blast)
  have hw2_eq_w1: "w\<^sub>2 = w\<^sub>1"
    using hw1_eq_w0 hw2_eq_w0 by (by100 simp)
  show ?thesis
    using hs1_eq hs2_eq hw2_eq_w1 he2_eq_e1 by (by100 blast)
qed

lemma geotop_degree_two_oriented_edge_successor_fun_inj_on_states_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  shows "inj_on (geotop_oriented_edge_successor L)
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
proof (rule inj_onI)
  fix s\<^sub>1 s\<^sub>2
  assume hs1: "s\<^sub>1 \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assume hs2: "s\<^sub>2 \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assume heq: "geotop_oriented_edge_successor L s\<^sub>1 =
      geotop_oriented_edge_successor L s\<^sub>2"
  have hstep1: "geotop_oriented_edge_successor L s\<^sub>1 \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> geotop_oriented_edge_successor_state L s\<^sub>1
          (geotop_oriented_edge_successor L s\<^sub>1)"
    by (rule geotop_degree_two_oriented_edge_successor_fun_step_prefix
        [OF hL hdegree hs1])
  have hstep2: "geotop_oriented_edge_successor L s\<^sub>2 \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> geotop_oriented_edge_successor_state L s\<^sub>2
          (geotop_oriented_edge_successor L s\<^sub>2)"
    by (rule geotop_degree_two_oriented_edge_successor_fun_step_prefix
        [OF hL hdegree hs2])
  have hsucc1: "geotop_oriented_edge_successor_state L s\<^sub>1
      (geotop_oriented_edge_successor L s\<^sub>1)"
    by (rule conjunct2[OF hstep1])
  have hsucc2: "geotop_oriented_edge_successor_state L s\<^sub>2
      (geotop_oriented_edge_successor L s\<^sub>1)"
    using conjunct2[OF hstep2] heq by (by100 simp)
  show "s\<^sub>1 = s\<^sub>2"
    by (rule geotop_degree_two_oriented_edge_successor_state_predecessor_unique_prefix
        [OF hL hdegree hsucc1 hsucc2])
qed

lemma geotop_degree_two_oriented_edge_successor_funpow_state_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  shows "(geotop_oriented_edge_successor L ^^ n) s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
proof (induct n)
  case 0
  show ?case
    using hs by (by100 simp)
next
  case (Suc n)
  have hstep: "geotop_oriented_edge_successor L
      ((geotop_oriented_edge_successor L ^^ n) s) \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> geotop_oriented_edge_successor_state L
          ((geotop_oriented_edge_successor L ^^ n) s)
          (geotop_oriented_edge_successor L
            ((geotop_oriented_edge_successor L ^^ n) s))"
    by (rule geotop_degree_two_oriented_edge_successor_fun_step_prefix
        [OF hL hdegree Suc.hyps])
  show ?case
    using hstep by (by100 simp)
qed

lemma geotop_finite_funpow_repeat_prefix:
  fixes A :: "'a set" and f :: "'a \<Rightarrow> 'a"
  assumes hfin: "finite A"
  assumes hx: "x \<in> A"
  assumes hclosed: "\<forall>y\<in>A. f y \<in> A"
  shows "\<exists>m n. m < n \<and> n \<le> Suc (card A) \<and> (f ^^ m) x = (f ^^ n) x"
proof -
  have hiter: "\<And>i. (f ^^ i) x \<in> A"
  proof -
    fix i
    show "(f ^^ i) x \<in> A"
    proof (induct i)
      case 0
      show ?case
        using hx by (by100 simp)
    next
      case (Suc i)
      show ?case
        using hclosed Suc.hyps by (by100 simp)
    qed
  qed
  have himage_sub: "(\<lambda>i. (f ^^ i) x) ` {0..card A} \<subseteq> A"
    using hiter by (by100 blast)
  have hcard_image_le: "card ((\<lambda>i. (f ^^ i) x) ` {0..card A}) \<le> card A"
    by (rule card_mono[OF hfin himage_sub])
  have hcard_dom_gt:
      "card {0..card A} > card ((\<lambda>i. (f ^^ i) x) ` {0..card A})"
    using hcard_image_le by (by100 simp)
  have hnot_inj: "\<not> inj_on (\<lambda>i. (f ^^ i) x) {0..card A}"
    by (rule pigeonhole[OF hcard_dom_gt])
  obtain i j where hi: "i \<in> {0..card A}"
    and hj: "j \<in> {0..card A}"
    and hij_eq: "(f ^^ i) x = (f ^^ j) x"
    and hij_ne: "i \<noteq> j"
    using hnot_inj unfolding inj_on_def by (by100 blast)
  show ?thesis
  proof (cases "i < j")
    case True
    have "j \<le> Suc (card A)"
      using hj by (by100 simp)
    show ?thesis
    proof (intro exI conjI)
      show "i < j" by (rule True)
      show "j \<le> Suc (card A)" by (rule \<open>j \<le> Suc (card A)\<close>)
      show "(f ^^ i) x = (f ^^ j) x" by (rule hij_eq)
    qed
  next
    case False
    have hji: "j < i"
      using False hij_ne by (by100 simp)
    have "i \<le> Suc (card A)"
      using hi by (by100 simp)
    show ?thesis
    proof (intro exI conjI)
      show "j < i" by (rule hji)
      show "i \<le> Suc (card A)" by (rule \<open>i \<le> Suc (card A)\<close>)
      show "(f ^^ j) x = (f ^^ i) x"
        using hij_eq by (by100 simp)
    qed
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_funpow_repeat_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  shows "\<exists>m n. m < n
      \<and> n \<le> Suc (card
        {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d})
      \<and> (geotop_oriented_edge_successor L ^^ m) s =
        (geotop_oriented_edge_successor L ^^ n) s"
proof -
  let ?A = "{(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  have hA_fin: "finite ?A"
    by (rule geotop_finite_linear_graph_oriented_edge_states_finite_graph_prefix
        [OF hL hfin])
  have hclosed: "\<forall>t\<in>?A. geotop_oriented_edge_successor L t \<in> ?A"
  proof
    fix t
    assume ht: "t \<in> ?A"
    have hstep: "geotop_oriented_edge_successor L t \<in> ?A
        \<and> geotop_oriented_edge_successor_state L t
            (geotop_oriented_edge_successor L t)"
	      by (rule geotop_degree_two_oriented_edge_successor_fun_step_prefix
	          [OF hL hdegree ht])
	    show "geotop_oriented_edge_successor L t \<in> ?A"
	      by (rule conjunct1[OF hstep])
	  qed
  show ?thesis
    by (rule geotop_finite_funpow_repeat_prefix
        [OF hA_fin hs hclosed])
qed

lemma geotop_funpow_closed_prefix:
  fixes A :: "'a set" and f :: "'a \<Rightarrow> 'a"
  assumes hx: "x \<in> A"
  assumes hclosed: "\<forall>y\<in>A. f y \<in> A"
  shows "(f ^^ n) x \<in> A"
proof (induct n)
  case 0
  show ?case
    using hx by (by100 simp)
next
  case (Suc n)
  show ?case
    using hclosed Suc.hyps by (by100 simp)
qed

lemma geotop_funpow_inj_on_closed_prefix:
  fixes A :: "'a set" and f :: "'a \<Rightarrow> 'a"
  assumes hinj: "inj_on f A"
  assumes hclosed: "\<forall>y\<in>A. f y \<in> A"
  shows "inj_on (f ^^ n) A"
proof (induct n)
  case 0
  show ?case
    by (by100 simp)
next
  case (Suc n)
  show ?case
  proof (rule inj_onI)
    fix x y
    assume hx: "x \<in> A"
    assume hy: "y \<in> A"
    assume heq: "(f ^^ Suc n) x = (f ^^ Suc n) y"
    have hx_n: "(f ^^ n) x \<in> A"
      by (rule geotop_funpow_closed_prefix[OF hx hclosed])
    have hy_n: "(f ^^ n) y \<in> A"
      by (rule geotop_funpow_closed_prefix[OF hy hclosed])
    have hf_eq: "f ((f ^^ n) x) = f ((f ^^ n) y)"
      using heq by (by100 simp)
    have hn_eq: "(f ^^ n) x = (f ^^ n) y"
      using inj_onD[OF hinj hf_eq hx_n hy_n] by (by100 simp)
    show "x = y"
      by (rule inj_onD[OF Suc.hyps hn_eq hx hy])
  qed
qed

lemma geotop_finite_inj_closed_funpow_period_prefix:
  fixes A :: "'a set" and f :: "'a \<Rightarrow> 'a"
  assumes hfin: "finite A"
  assumes hx: "x \<in> A"
  assumes hclosed: "\<forall>y\<in>A. f y \<in> A"
  assumes hinj: "inj_on f A"
  shows "\<exists>n. 0 < n \<and> n \<le> Suc (card A) \<and> (f ^^ n) x = x"
proof -
  obtain m n where hmn: "m < n"
    and hn_le: "n \<le> Suc (card A)"
    and hrepeat: "(f ^^ m) x = (f ^^ n) x"
    using geotop_finite_funpow_repeat_prefix[OF hfin hx hclosed] by (by100 blast)
  have hn_decomp: "n = m + (n - m)"
    using hmn by (by100 simp)
  have hclosed_diff: "(f ^^ (n - m)) x \<in> A"
    by (rule geotop_funpow_closed_prefix[OF hx hclosed])
  have hmap_eq: "(f ^^ m) x = (f ^^ m) ((f ^^ (n - m)) x)"
    using hrepeat hn_decomp funpow_add[of m "n - m" f] by (by100 simp)
  have hinj_m: "inj_on (f ^^ m) A"
    by (rule geotop_funpow_inj_on_closed_prefix[OF hinj hclosed])
  have hreturn: "x = (f ^^ (n - m)) x"
    by (rule inj_onD[OF hinj_m hmap_eq hx hclosed_diff])
  have hpos: "0 < n - m"
    using hmn by (by100 simp)
  have hle: "n - m \<le> Suc (card A)"
    using hn_le by (by100 simp)
  show ?thesis
  proof (intro exI conjI)
    show "0 < n - m" by (rule hpos)
    show "n - m \<le> Suc (card A)" by (rule hle)
    show "(f ^^ (n - m)) x = x"
      using hreturn by (by100 simp)
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_funpow_period_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  shows "\<exists>n. 0 < n
      \<and> n \<le> Suc (card
        {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d})
      \<and> (geotop_oriented_edge_successor L ^^ n) s = s"
proof -
  let ?A = "{(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  have hA_fin: "finite ?A"
    by (rule geotop_finite_linear_graph_oriented_edge_states_finite_graph_prefix
        [OF hL hfin])
  have hclosed: "\<forall>t\<in>?A. geotop_oriented_edge_successor L t \<in> ?A"
  proof
    fix t
    assume ht: "t \<in> ?A"
    have hstep: "geotop_oriented_edge_successor L t \<in> ?A
        \<and> geotop_oriented_edge_successor_state L t
            (geotop_oriented_edge_successor L t)"
      by (rule geotop_degree_two_oriented_edge_successor_fun_step_prefix
          [OF hL hdegree ht])
    show "geotop_oriented_edge_successor L t \<in> ?A"
      by (rule conjunct1[OF hstep])
  qed
  have hinj: "inj_on (geotop_oriented_edge_successor L) ?A"
    by (rule geotop_degree_two_oriented_edge_successor_fun_inj_on_states_prefix
        [OF hL hdegree])
  show ?thesis
    by (rule geotop_finite_inj_closed_funpow_period_prefix
        [OF hA_fin hs hclosed hinj])
qed

lemma geotop_degree_two_oriented_edge_successor_closed_orbit_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  shows "\<exists>n. 0 < n
      \<and> n \<le> Suc (card
        {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d})
      \<and> (geotop_oriented_edge_successor L ^^ n) s = s
      \<and> (\<forall>k\<le>n. (geotop_oriented_edge_successor L ^^ k) s \<in>
        {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d})"
proof -
  let ?A = "{(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  obtain n where hn_pos: "0 < n"
    and hn_le: "n \<le> Suc (card ?A)"
    and hn_return: "(geotop_oriented_edge_successor L ^^ n) s = s"
    using geotop_degree_two_oriented_edge_successor_funpow_period_prefix
      [OF hL hfin hdegree hs] by (by100 blast)
  have hstates: "\<forall>k\<le>n. (geotop_oriented_edge_successor L ^^ k) s \<in> ?A"
  proof (intro allI impI)
    fix k
    assume hk: "k \<le> n"
    show "(geotop_oriented_edge_successor L ^^ k) s \<in> ?A"
      by (rule geotop_degree_two_oriented_edge_successor_funpow_state_prefix
          [OF hL hdegree hs])
  qed
  show ?thesis
  proof (intro exI conjI)
    show "0 < n" by (rule hn_pos)
    show "n \<le> Suc (card ?A)" by (rule hn_le)
    show "(geotop_oriented_edge_successor L ^^ n) s = s" by (rule hn_return)
    show "\<forall>k\<le>n. (geotop_oriented_edge_successor L ^^ k) s \<in> ?A"
      by (rule hstates)
  qed
qed

lemma geotop_finite_inj_closed_funpow_least_period_prefix:
  fixes A :: "'a set" and f :: "'a \<Rightarrow> 'a"
  assumes hfin: "finite A"
  assumes hx: "x \<in> A"
  assumes hclosed: "\<forall>y\<in>A. f y \<in> A"
  assumes hinj: "inj_on f A"
  shows "\<exists>p. 0 < p \<and> p \<le> Suc (card A) \<and> (f ^^ p) x = x
      \<and> (\<forall>k. 0 < k \<and> k < p \<longrightarrow> (f ^^ k) x \<noteq> x)"
proof -
  let ?P = "\<lambda>p. 0 < p \<and> p \<le> Suc (card A) \<and> (f ^^ p) x = x"
  have hex: "\<exists>p. ?P p"
    by (rule geotop_finite_inj_closed_funpow_period_prefix
        [OF hfin hx hclosed hinj])
  define p where "p = (LEAST n. ?P n)"
  have hpP: "?P p"
    unfolding p_def by (rule LeastI_ex[OF hex])
  have hp_pos: "0 < p"
    using hpP by (by100 blast)
  have hp_le: "p \<le> Suc (card A)"
    using hpP by (by100 blast)
  have hp_return: "(f ^^ p) x = x"
    using hpP by (by100 blast)
  have hminimal: "\<forall>k. 0 < k \<and> k < p \<longrightarrow> (f ^^ k) x \<noteq> x"
  proof (intro allI impI)
    fix k
    assume hk: "0 < k \<and> k < p"
    have hk_pos: "0 < k"
      using hk by (by100 blast)
    have hk_less: "k < p"
      using hk by (by100 blast)
    show "(f ^^ k) x \<noteq> x"
    proof
      assume hk_return: "(f ^^ k) x = x"
      have hk_le: "k \<le> Suc (card A)"
        using hk_less hp_le by (by100 linarith)
      have "?P k"
        using hk_pos hk_le hk_return by (by100 blast)
      moreover have hk_less_least: "k < (LEAST n. ?P n)"
        using hk_less unfolding p_def by (by100 simp)
      moreover have "\<not> ?P k"
        by (rule not_less_Least[OF hk_less_least])
      ultimately show False
        by (by100 blast)
    qed
  qed
  show ?thesis
  proof (intro exI conjI)
    show "0 < p" by (rule hp_pos)
    show "p \<le> Suc (card A)" by (rule hp_le)
    show "(f ^^ p) x = x" by (rule hp_return)
    show "\<forall>k. 0 < k \<and> k < p \<longrightarrow> (f ^^ k) x \<noteq> x"
      by (rule hminimal)
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_least_period_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  shows "\<exists>p. 0 < p
      \<and> p \<le> Suc (card
        {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d})
      \<and> (geotop_oriented_edge_successor L ^^ p) s = s
      \<and> (\<forall>k. 0 < k \<and> k < p \<longrightarrow>
        (geotop_oriented_edge_successor L ^^ k) s \<noteq> s)"
proof -
  let ?A = "{(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  have hA_fin: "finite ?A"
    by (rule geotop_finite_linear_graph_oriented_edge_states_finite_graph_prefix
        [OF hL hfin])
  have hclosed: "\<forall>t\<in>?A. geotop_oriented_edge_successor L t \<in> ?A"
  proof
    fix t
    assume ht: "t \<in> ?A"
    have hstep: "geotop_oriented_edge_successor L t \<in> ?A
        \<and> geotop_oriented_edge_successor_state L t
            (geotop_oriented_edge_successor L t)"
      by (rule geotop_degree_two_oriented_edge_successor_fun_step_prefix
          [OF hL hdegree ht])
    show "geotop_oriented_edge_successor L t \<in> ?A"
      by (rule conjunct1[OF hstep])
  qed
  have hinj: "inj_on (geotop_oriented_edge_successor L) ?A"
    by (rule geotop_degree_two_oriented_edge_successor_fun_inj_on_states_prefix
        [OF hL hdegree])
  show ?thesis
    by (rule geotop_finite_inj_closed_funpow_least_period_prefix
        [OF hA_fin hs hclosed hinj])
qed

lemma geotop_finite_inj_closed_funpow_least_period_orbit_inj_prefix:
  fixes A :: "'a set" and f :: "'a \<Rightarrow> 'a"
  assumes hx: "x \<in> A"
  assumes hclosed: "\<forall>y\<in>A. f y \<in> A"
  assumes hinj: "inj_on f A"
  assumes hp_pos: "0 < p"
  assumes hminimal: "\<forall>k. 0 < k \<and> k < p \<longrightarrow> (f ^^ k) x \<noteq> x"
  shows "inj_on (\<lambda>k. (f ^^ k) x) {0..<p}"
proof (rule inj_onI)
  fix i j
  assume hi: "i \<in> {0..<p}"
  assume hj: "j \<in> {0..<p}"
  assume heq: "(f ^^ i) x = (f ^^ j) x"
  have hi_lt: "i < p"
    using hi by (by100 simp)
  have hj_lt: "j < p"
    using hj by (by100 simp)
  show "i = j"
  proof (cases i j rule: linorder_cases)
    case less
    have hj_decomp: "j = i + (j - i)"
      using less by (by100 simp)
    have hdiff_pos: "0 < j - i"
      using less by (by100 simp)
    have hdiff_lt: "j - i < p"
      using hj_lt by (by100 linarith)
    have hdiff_state: "(f ^^ (j - i)) x \<in> A"
      by (rule geotop_funpow_closed_prefix[OF hx hclosed])
    have hmap_eq: "(f ^^ i) x = (f ^^ i) ((f ^^ (j - i)) x)"
      using heq hj_decomp funpow_add[of i "j - i" f] by (by100 simp)
    have hinj_i: "inj_on (f ^^ i) A"
      by (rule geotop_funpow_inj_on_closed_prefix[OF hinj hclosed])
    have hreturn: "x = (f ^^ (j - i)) x"
      by (rule inj_onD[OF hinj_i hmap_eq hx hdiff_state])
    have hreturn_sym: "(f ^^ (j - i)) x = x"
      using hreturn by (by100 simp)
    have "(f ^^ (j - i)) x \<noteq> x"
      using hminimal hdiff_pos hdiff_lt by (by100 blast)
    have False
      using \<open>(f ^^ (j - i)) x \<noteq> x\<close> hreturn_sym by (by100 blast)
    thus ?thesis
      by (by100 blast)
  next
    case equal
    show ?thesis
      by (rule equal)
  next
    case greater
    have hi_decomp: "i = j + (i - j)"
      using greater by (by100 simp)
    have hdiff_pos: "0 < i - j"
      using greater by (by100 simp)
    have hdiff_lt: "i - j < p"
      using hi_lt by (by100 linarith)
    have hdiff_state: "(f ^^ (i - j)) x \<in> A"
      by (rule geotop_funpow_closed_prefix[OF hx hclosed])
    have hmap_eq: "(f ^^ j) x = (f ^^ j) ((f ^^ (i - j)) x)"
      using heq hi_decomp funpow_add[of j "i - j" f] by (by100 simp)
    have hinj_j: "inj_on (f ^^ j) A"
      by (rule geotop_funpow_inj_on_closed_prefix[OF hinj hclosed])
    have hreturn: "x = (f ^^ (i - j)) x"
      by (rule inj_onD[OF hinj_j hmap_eq hx hdiff_state])
    have hreturn_sym: "(f ^^ (i - j)) x = x"
      using hreturn by (by100 simp)
    have "(f ^^ (i - j)) x \<noteq> x"
      using hminimal hdiff_pos hdiff_lt by (by100 blast)
    have False
      using \<open>(f ^^ (i - j)) x \<noteq> x\<close> hreturn_sym by (by100 blast)
    thus ?thesis
      by (by100 blast)
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_least_period_orbit_inj_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hminimal: "\<forall>k. 0 < k \<and> k < p \<longrightarrow>
      (geotop_oriented_edge_successor L ^^ k) s \<noteq> s"
  shows "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
proof -
  let ?A = "{(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  have hclosed: "\<forall>t\<in>?A. geotop_oriented_edge_successor L t \<in> ?A"
  proof
    fix t
    assume ht: "t \<in> ?A"
    have hstep: "geotop_oriented_edge_successor L t \<in> ?A
        \<and> geotop_oriented_edge_successor_state L t
            (geotop_oriented_edge_successor L t)"
      by (rule geotop_degree_two_oriented_edge_successor_fun_step_prefix
          [OF hL hdegree ht])
    show "geotop_oriented_edge_successor L t \<in> ?A"
      by (rule conjunct1[OF hstep])
  qed
  have hinj: "inj_on (geotop_oriented_edge_successor L) ?A"
    by (rule geotop_degree_two_oriented_edge_successor_fun_inj_on_states_prefix
        [OF hL hdegree])
  show ?thesis
    by (rule geotop_finite_inj_closed_funpow_least_period_orbit_inj_prefix
        [OF hs hclosed hinj hp_pos hminimal])
qed

lemma geotop_funpow_period_orbit_successor_image_prefix:
  fixes f :: "'a \<Rightarrow> 'a"
  assumes hp_pos: "0 < p"
  assumes hreturn: "(f ^^ p) x = x"
  shows "f ` ((\<lambda>k. (f ^^ k) x) ` {0..<p}) =
      ((\<lambda>k. (f ^^ k) x) ` {0..<p})"
proof
  show "f ` ((\<lambda>k. (f ^^ k) x) ` {0..<p}) \<subseteq>
      ((\<lambda>k. (f ^^ k) x) ` {0..<p})"
  proof
    fix y
    assume hy: "y \<in> f ` ((\<lambda>k. (f ^^ k) x) ` {0..<p})"
    obtain k where hk: "k \<in> {0..<p}"
      and hy_eq: "y = f ((f ^^ k) x)"
      using hy by (by100 blast)
    have hk_lt: "k < p"
      using hk by (by100 simp)
    show "y \<in> ((\<lambda>k. (f ^^ k) x) ` {0..<p})"
    proof (cases "Suc k < p")
      case True
      have hSuc_mem: "Suc k \<in> {0..<p}"
        using True by (by100 simp)
      have hy_Suc: "y = (f ^^ Suc k) x"
        using hy_eq by (by100 simp)
      show ?thesis
        using hSuc_mem hy_Suc by (by100 blast)
    next
      case False
      have hSuc_eq: "Suc k = p"
        using False hk_lt by (by100 simp)
      have hy_Suc: "y = (f ^^ Suc k) x"
        using hy_eq by (by100 simp)
      have hy_x: "y = x"
        using hy_Suc hSuc_eq hreturn by (by100 simp)
      have hzero_mem: "0 \<in> {0..<p}"
        using hp_pos by (by100 simp)
      show ?thesis
      proof (rule image_eqI[where x = 0])
        show "y = (f ^^ 0) x"
          using hy_x by (by100 simp)
        show "0 \<in> {0..<p}"
          by (rule hzero_mem)
      qed
    qed
  qed
  show "((\<lambda>k. (f ^^ k) x) ` {0..<p}) \<subseteq>
      f ` ((\<lambda>k. (f ^^ k) x) ` {0..<p})"
  proof
    fix y
    assume hy: "y \<in> ((\<lambda>k. (f ^^ k) x) ` {0..<p})"
    obtain k where hk: "k \<in> {0..<p}" and hy_eq: "y = (f ^^ k) x"
      using hy by (by100 blast)
    show "y \<in> f ` ((\<lambda>k. (f ^^ k) x) ` {0..<p})"
    proof (cases k)
      case 0
      define j where "j = p - 1"
      have hj_mem: "j \<in> {0..<p}"
        unfolding j_def using hp_pos by (by100 simp)
      have hp_eq: "p = Suc j"
        unfolding j_def using hp_pos by (by100 simp)
      have hy_img: "y = f ((f ^^ j) x)"
        using hy_eq 0 hreturn hp_eq by (by100 simp)
      show ?thesis
        using hj_mem hy_img by (by100 blast)
    next
      case (Suc j)
      have hj_mem: "j \<in> {0..<p}"
        using hk Suc by (by100 simp)
      have hy_img: "y = f ((f ^^ j) x)"
        using hy_eq Suc by (by100 simp)
      show ?thesis
        using hj_mem hy_img by (by100 blast)
    qed
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_period_orbit_image_prefix:
  fixes L :: "(real^2) set set"
  assumes hp_pos: "0 < p"
  assumes hreturn: "(geotop_oriented_edge_successor L ^^ p) s = s"
  shows "geotop_oriented_edge_successor L `
      ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) =
      ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p})"
  by (rule geotop_funpow_period_orbit_successor_image_prefix
      [OF hp_pos hreturn])

lemma geotop_funpow_least_period_orbit_card_prefix:
  fixes A :: "'a set" and f :: "'a \<Rightarrow> 'a"
  assumes hx: "x \<in> A"
  assumes hclosed: "\<forall>y\<in>A. f y \<in> A"
  assumes hinj: "inj_on f A"
  assumes hp_pos: "0 < p"
  assumes hminimal: "\<forall>k. 0 < k \<and> k < p \<longrightarrow> (f ^^ k) x \<noteq> x"
  shows "card ((\<lambda>k. (f ^^ k) x) ` {0..<p}) = p"
proof -
  have hinj_orbit: "inj_on (\<lambda>k. (f ^^ k) x) {0..<p}"
    by (rule geotop_finite_inj_closed_funpow_least_period_orbit_inj_prefix
        [OF hx hclosed hinj hp_pos hminimal])
  have hcard_image:
      "card ((\<lambda>k. (f ^^ k) x) ` {0..<p}) = card {0..<p}"
    by (rule card_image[OF hinj_orbit])
  show ?thesis
    using hcard_image by (by100 simp)
qed

lemma geotop_degree_two_oriented_edge_successor_least_period_orbit_card_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hminimal: "\<forall>k. 0 < k \<and> k < p \<longrightarrow>
      (geotop_oriented_edge_successor L ^^ k) s \<noteq> s"
  shows "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
proof -
  let ?A = "{(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  have hclosed: "\<forall>t\<in>?A. geotop_oriented_edge_successor L t \<in> ?A"
  proof
    fix t
    assume ht: "t \<in> ?A"
    have hstep: "geotop_oriented_edge_successor L t \<in> ?A
        \<and> geotop_oriented_edge_successor_state L t
            (geotop_oriented_edge_successor L t)"
      by (rule geotop_degree_two_oriented_edge_successor_fun_step_prefix
          [OF hL hdegree ht])
    show "geotop_oriented_edge_successor L t \<in> ?A"
      by (rule conjunct1[OF hstep])
  qed
  have hinj: "inj_on (geotop_oriented_edge_successor L) ?A"
    by (rule geotop_degree_two_oriented_edge_successor_fun_inj_on_states_prefix
        [OF hL hdegree])
  show ?thesis
    by (rule geotop_funpow_least_period_orbit_card_prefix
        [OF hs hclosed hinj hp_pos hminimal])
qed

lemma geotop_degree_two_oriented_edge_successor_funpow_edge_between_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  shows "snd ((geotop_oriented_edge_successor L ^^ k) s) =
      closed_segment (fst ((geotop_oriented_edge_successor L ^^ k) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))"
proof -
  let ?s\<^sub>k = "(geotop_oriented_edge_successor L ^^ k) s"
  have hsk_state: "?s\<^sub>k \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
    by (rule geotop_degree_two_oriented_edge_successor_funpow_state_prefix
        [OF hL hdegree hs])
  have hstep: "geotop_oriented_edge_successor L ?s\<^sub>k \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> geotop_oriented_edge_successor_state L ?s\<^sub>k
          (geotop_oriented_edge_successor L ?s\<^sub>k)"
    by (rule geotop_degree_two_oriented_edge_successor_fun_step_prefix
        [OF hL hdegree hsk_state])
  have hrel: "geotop_oriented_edge_successor_state L ?s\<^sub>k
      (geotop_oriented_edge_successor L ?s\<^sub>k)"
    by (rule conjunct2[OF hstep])
  have hseg: "snd ?s\<^sub>k =
      closed_segment (fst ?s\<^sub>k) (fst (geotop_oriented_edge_successor L ?s\<^sub>k))"
    using hrel unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  show ?thesis
    using hseg by (by100 simp)
qed

lemma geotop_degree_two_oriented_edge_successor_funpow_next_vertex_distinct_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  shows "fst ((geotop_oriented_edge_successor L ^^ Suc k) s) \<noteq>
      fst ((geotop_oriented_edge_successor L ^^ k) s)"
proof -
  let ?s\<^sub>k = "(geotop_oriented_edge_successor L ^^ k) s"
  have hsk_state: "?s\<^sub>k \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
    by (rule geotop_degree_two_oriented_edge_successor_funpow_state_prefix
        [OF hL hdegree hs])
  have hstep: "geotop_oriented_edge_successor L ?s\<^sub>k \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> geotop_oriented_edge_successor_state L ?s\<^sub>k
          (geotop_oriented_edge_successor L ?s\<^sub>k)"
    by (rule geotop_degree_two_oriented_edge_successor_fun_step_prefix
        [OF hL hdegree hsk_state])
  have hrel: "geotop_oriented_edge_successor_state L ?s\<^sub>k
      (geotop_oriented_edge_successor L ?s\<^sub>k)"
    by (rule conjunct2[OF hstep])
  have hneq: "fst (geotop_oriented_edge_successor L ?s\<^sub>k) \<noteq> fst ?s\<^sub>k"
    using hrel unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  show ?thesis
    using hneq by (by100 simp)
qed

lemma geotop_degree_two_oriented_edge_successor_first_step_endpoint_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hq_ne: "q \<noteq> fst s"
  assumes hseg: "snd s = closed_segment (fst s) q"
  shows "fst (geotop_oriented_edge_successor L s) = q"
proof -
  have hstep: "geotop_oriented_edge_successor L s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> geotop_oriented_edge_successor_state L s
          (geotop_oriented_edge_successor L s)"
    by (rule geotop_degree_two_oriented_edge_successor_fun_step_prefix
        [OF hL hdegree hs])
  have hrel: "geotop_oriented_edge_successor_state L s
      (geotop_oriented_edge_successor L s)"
    by (rule conjunct2[OF hstep])
  have hsucc_seg: "snd s =
      closed_segment (fst s) (fst (geotop_oriented_edge_successor L s))"
    using hrel unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have hsucc_ne: "fst (geotop_oriented_edge_successor L s) \<noteq> fst s"
    using hrel unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have hseg_eq: "closed_segment (fst s) (fst (geotop_oriented_edge_successor L s)) =
      closed_segment (fst s) q"
    using hsucc_seg hseg by (by100 simp)
  have hpair_eq: "{fst s, fst (geotop_oriented_edge_successor L s)} = {fst s, q}"
    using hseg_eq closed_segment_eq
      [of "fst s" "fst (geotop_oriented_edge_successor L s)" "fst s" q]
    by (by100 simp)
  have "fst (geotop_oriented_edge_successor L s) \<in> {fst s, q}"
    using hpair_eq by (by100 blast)
  thus ?thesis
    using hsucc_ne by (by100 blast)
qed

lemma geotop_degree_two_oriented_edge_successor_funpow_vertex_in_graph_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  shows "{fst ((geotop_oriented_edge_successor L ^^ k) s)} \<in> L"
proof -
  have hstate: "(geotop_oriented_edge_successor L ^^ k) s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
    by (rule geotop_degree_two_oriented_edge_successor_funpow_state_prefix
        [OF hL hdegree hs])
  obtain v d where hvd: "(geotop_oriented_edge_successor L ^^ k) s = (v, d)"
    by (cases "(geotop_oriented_edge_successor L ^^ k) s") (by100 blast)
  have "{v} \<in> L"
    using hstate hvd by (by100 simp)
  show ?thesis
    using \<open>{v} \<in> L\<close> hvd by (by100 simp)
qed

lemma geotop_degree_two_oriented_edge_successor_funpow_edge_in_graph_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  shows "snd ((geotop_oriented_edge_successor L ^^ k) s) \<in> L
      \<and> geotop_is_edge (snd ((geotop_oriented_edge_successor L ^^ k) s))
      \<and> fst ((geotop_oriented_edge_successor L ^^ k) s)
          \<in> snd ((geotop_oriented_edge_successor L ^^ k) s)"
proof -
  have hstate: "(geotop_oriented_edge_successor L ^^ k) s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
    by (rule geotop_degree_two_oriented_edge_successor_funpow_state_prefix
        [OF hL hdegree hs])
  obtain v d where hvd: "(geotop_oriented_edge_successor L ^^ k) s = (v, d)"
    by (cases "(geotop_oriented_edge_successor L ^^ k) s") (by100 blast)
  have "d \<in> L \<and> geotop_is_edge d \<and> v \<in> d"
    using hstate hvd by (by100 simp)
  show ?thesis
    using \<open>d \<in> L \<and> geotop_is_edge d \<and> v \<in> d\<close> hvd by (by100 simp)
qed

lemma geotop_degree_two_oriented_edge_successor_consecutive_vertices_edge_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  shows "closed_segment (fst ((geotop_oriented_edge_successor L ^^ k) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc k) s)) \<in> L
      \<and> geotop_is_edge
        (closed_segment (fst ((geotop_oriented_edge_successor L ^^ k) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc k) s)))"
proof -
  have hseg: "snd ((geotop_oriented_edge_successor L ^^ k) s) =
      closed_segment (fst ((geotop_oriented_edge_successor L ^^ k) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))"
    by (rule geotop_degree_two_oriented_edge_successor_funpow_edge_between_prefix
        [OF hL hdegree hs])
  have hedge_data: "snd ((geotop_oriented_edge_successor L ^^ k) s) \<in> L
      \<and> geotop_is_edge (snd ((geotop_oriented_edge_successor L ^^ k) s))
      \<and> fst ((geotop_oriented_edge_successor L ^^ k) s)
          \<in> snd ((geotop_oriented_edge_successor L ^^ k) s)"
    by (rule geotop_degree_two_oriented_edge_successor_funpow_edge_in_graph_prefix
        [OF hL hdegree hs])
  show ?thesis
    using hseg hedge_data by (by100 simp)
qed

lemma geotop_degree_two_oriented_edge_successor_funpow_noninitial_vertex_incident_edge_cases_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hk_pos: "0 < k"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hinc: "fst ((geotop_oriented_edge_successor L ^^ k) s) \<in> e"
  shows "e = closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ (k - 1)) s))
        (fst ((geotop_oriented_edge_successor L ^^ k) s))
      \<or> e = closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ k) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))"
proof -
  let ?s\<^sub>p = "(geotop_oriented_edge_successor L ^^ (k - 1)) s"
  have hSuc_pred: "Suc (k - 1) = k"
    using hk_pos by (by100 simp)
  have hp_state: "?s\<^sub>p \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
    by (rule geotop_degree_two_oriented_edge_successor_funpow_state_prefix
        [OF hL hdegree hs])
  have hsucc_pred: "geotop_oriented_edge_successor L ?s\<^sub>p =
      (geotop_oriented_edge_successor L ^^ k) s"
    using hSuc_pred
      funpow.simps(2)[of "k - 1" "geotop_oriented_edge_successor L"]
    by (by100 simp)
  have hinc_step: "fst (geotop_oriented_edge_successor L ?s\<^sub>p) \<in> e"
    using hinc hsucc_pred by (by100 simp)
  have hcases: "e = snd ?s\<^sub>p \<or>
      e = snd (geotop_oriented_edge_successor L ?s\<^sub>p)"
    by (rule geotop_degree_two_oriented_edge_successor_step_incident_edge_cases_prefix
        [OF hL hdegree hp_state heL hedge hinc_step])
  have hincoming: "snd ?s\<^sub>p =
      closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ (k - 1)) s))
        (fst ((geotop_oriented_edge_successor L ^^ k) s))"
  proof -
    have hseg: "snd ?s\<^sub>p =
        closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ (k - 1)) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc (k - 1)) s))"
      by (rule geotop_degree_two_oriented_edge_successor_funpow_edge_between_prefix
          [OF hL hdegree hs])
    show ?thesis
      using hseg hSuc_pred by (by100 simp)
  qed
  have houtgoing: "snd (geotop_oriented_edge_successor L ?s\<^sub>p) =
      closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ k) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))"
  proof -
    have hseg: "snd ((geotop_oriented_edge_successor L ^^ k) s) =
        closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ k) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))"
      by (rule geotop_degree_two_oriented_edge_successor_funpow_edge_between_prefix
          [OF hL hdegree hs])
    show ?thesis
      using hseg hsucc_pred by (by100 simp)
  qed
  show ?thesis
    using hcases hincoming houtgoing by (by100 blast)
qed

lemma geotop_degree_two_oriented_edge_successor_period_closing_edge_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  shows "closed_segment (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
        (fst s) \<in> L
      \<and> geotop_is_edge
        (closed_segment (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
          (fst s))"
proof -
  have hSuc_pred: "Suc (p - 1) = p"
    using hp_pos by (by100 simp)
  have hedge: "closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc (p - 1)) s)) \<in> L
      \<and> geotop_is_edge
        (closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc (p - 1)) s)))"
    by (rule geotop_degree_two_oriented_edge_successor_consecutive_vertices_edge_prefix
        [OF hL hdegree hs])
  have hvertex_close: "fst ((geotop_oriented_edge_successor L ^^ Suc (p - 1)) s) =
      fst s"
    using hSuc_pred hp_closed by (by100 simp)
  show ?thesis
    using hedge hvertex_close by (by100 simp)
qed

lemma geotop_degree_two_oriented_edge_successor_period_initial_vertex_incident_edge_cases_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hinc: "fst s \<in> e"
  shows "e = closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
        (fst s)
      \<or> e = closed_segment
        (fst s)
        (fst ((geotop_oriented_edge_successor L ^^ Suc 0) s))"
proof -
  let ?s\<^sub>p = "(geotop_oriented_edge_successor L ^^ (p - 1)) s"
  have hSuc_pred: "Suc (p - 1) = p"
    using hp_pos by (by100 simp)
  have hp_state: "?s\<^sub>p \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
    by (rule geotop_degree_two_oriented_edge_successor_funpow_state_prefix
        [OF hL hdegree hs])
  have hsucc_to_p: "geotop_oriented_edge_successor L ?s\<^sub>p =
      (geotop_oriented_edge_successor L ^^ p) s"
    using hSuc_pred
      funpow.simps(2)[of "p - 1" "geotop_oriented_edge_successor L"]
    by (by100 simp)
  have hsucc_pred: "geotop_oriented_edge_successor L ?s\<^sub>p = s"
    using hsucc_to_p hp_closed by (by100 simp)
  have hinc_step: "fst (geotop_oriented_edge_successor L ?s\<^sub>p) \<in> e"
    using hinc hsucc_pred by (by100 simp)
  have hcases: "e = snd ?s\<^sub>p \<or>
      e = snd (geotop_oriented_edge_successor L ?s\<^sub>p)"
    by (rule geotop_degree_two_oriented_edge_successor_step_incident_edge_cases_prefix
        [OF hL hdegree hp_state heL hedge hinc_step])
  have hincoming: "snd ?s\<^sub>p =
      closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
        (fst s)"
  proof -
    have hseg: "snd ?s\<^sub>p =
        closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc (p - 1)) s))"
      by (rule geotop_degree_two_oriented_edge_successor_funpow_edge_between_prefix
          [OF hL hdegree hs])
    have hclose: "fst ((geotop_oriented_edge_successor L ^^ Suc (p - 1)) s) =
        fst s"
      using hSuc_pred hp_closed by (by100 simp)
    show ?thesis
      using hseg hclose by (by100 simp)
  qed
  have houtgoing: "snd (geotop_oriented_edge_successor L ?s\<^sub>p) =
      closed_segment
        (fst s)
        (fst ((geotop_oriented_edge_successor L ^^ Suc 0) s))"
  proof -
    have hseg0: "snd ((geotop_oriented_edge_successor L ^^ 0) s) =
        closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ 0) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc 0) s))"
      by (rule geotop_degree_two_oriented_edge_successor_funpow_edge_between_prefix
          [where k=0, OF hL hdegree hs])
    have hseg: "snd s =
        closed_segment
          (fst s)
          (fst ((geotop_oriented_edge_successor L ^^ Suc 0) s))"
      using hseg0 by (by100 simp)
    show ?thesis
      using hseg hsucc_pred by (by100 simp)
  qed
  show ?thesis
    using hcases hincoming houtgoing by (by100 blast)
qed

lemma geotop_degree_two_oriented_edge_successor_period_vertex_incident_edge_cases_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes hk_lt: "k < p"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hinc: "fst ((geotop_oriented_edge_successor L ^^ k) s) \<in> e"
  shows "e = closed_segment
        (fst ((geotop_oriented_edge_successor L ^^
          (if k = 0 then p - 1 else k - 1)) s))
        (fst ((geotop_oriented_edge_successor L ^^ k) s))
      \<or> e = closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ k) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))"
proof (cases "k = 0")
  case True
  have hinc0: "fst s \<in> e"
    using hinc True by (by100 simp)
  have hcases: "e = closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
        (fst s)
      \<or> e = closed_segment
        (fst s)
        (fst ((geotop_oriented_edge_successor L ^^ Suc 0) s))"
    by (rule geotop_degree_two_oriented_edge_successor_period_initial_vertex_incident_edge_cases_prefix
        [OF hL hdegree hs hp_pos hp_closed heL hedge hinc0])
  show ?thesis
    using hcases True by (by100 simp)
next
  case False
  have hk_pos: "0 < k"
    using False by (by100 simp)
  have hcases: "e = closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ (k - 1)) s))
        (fst ((geotop_oriented_edge_successor L ^^ k) s))
      \<or> e = closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ k) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))"
    by (rule geotop_degree_two_oriented_edge_successor_funpow_noninitial_vertex_incident_edge_cases_prefix
        [OF hL hdegree hs hk_pos heL hedge hinc])
  show ?thesis
    using hcases False by (by100 simp)
qed

lemma geotop_degree_two_oriented_edge_successor_period_incident_edge_in_edge_orbit_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes hk_lt: "k < p"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hinc: "fst ((geotop_oriented_edge_successor L ^^ k) s) \<in> e"
  shows "e \<in> (\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p}"
proof -
  let ?edge_at = "\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))"
  have hcases: "e = closed_segment
        (fst ((geotop_oriented_edge_successor L ^^
          (if k = 0 then p - 1 else k - 1)) s))
        (fst ((geotop_oriented_edge_successor L ^^ k) s))
      \<or> e = closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ k) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))"
    by (rule geotop_degree_two_oriented_edge_successor_period_vertex_incident_edge_cases_prefix
        [OF hL hdegree hs hp_pos hp_closed hk_lt heL hedge hinc])
  show ?thesis
  proof (cases "e = closed_segment
        (fst ((geotop_oriented_edge_successor L ^^
          (if k = 0 then p - 1 else k - 1)) s))
        (fst ((geotop_oriented_edge_successor L ^^ k) s))")
    case True
    let ?j = "if k = 0 then p - 1 else k - 1"
    have hj_lt: "?j < p"
    proof (cases "k = 0")
      case True
      show ?thesis
        using True hp_pos by (by100 simp)
    next
      case False
      show ?thesis
        using False hk_lt by (by100 simp)
    qed
    have hnext: "fst ((geotop_oriented_edge_successor L ^^ Suc ?j) s) =
        fst ((geotop_oriented_edge_successor L ^^ k) s)"
    proof (cases "k = 0")
      case True
      have hSuc: "Suc (p - 1) = p"
        using hp_pos by (by100 simp)
      show ?thesis
        using True hSuc hp_closed by (by100 simp)
    next
      case False
      have hk_pos: "0 < k"
        using False by (by100 simp)
      have hSuc: "Suc (k - 1) = k"
        using hk_pos by (by100 simp)
      show ?thesis
        using False hSuc by (by100 simp)
    qed
    have heq: "e = ?edge_at ?j"
      using True hnext by (by100 simp)
    have hj_mem: "?j \<in> {0..<p}"
      using hj_lt by (by100 simp)
    show ?thesis
      using heq hj_mem by (by100 blast)
  next
    case False
    have heq: "e = ?edge_at k"
      using hcases False by (by100 blast)
    have hk_mem: "k \<in> {0..<p}"
      using hk_lt by (by100 simp)
    show ?thesis
      using heq hk_mem by (by100 blast)
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_period_vertex_orbit_incident_edge_in_edge_orbit_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes hv: "v \<in> (\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hinc: "v \<in> e"
  shows "e \<in> (\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p}"
proof -
  obtain k where hk_mem: "k \<in> {0..<p}"
    and hv_eq: "v = fst ((geotop_oriented_edge_successor L ^^ k) s)"
    using hv by (by100 blast)
  have hk_lt: "k < p"
    using hk_mem by (by100 simp)
  have hinc_k: "fst ((geotop_oriented_edge_successor L ^^ k) s) \<in> e"
    using hinc hv_eq by (by100 simp)
  show ?thesis
    by (rule geotop_degree_two_oriented_edge_successor_period_incident_edge_in_edge_orbit_prefix
        [OF hL hdegree hs hp_pos hp_closed hk_lt heL hedge hinc_k])
qed

lemma geotop_degree_two_oriented_edge_successor_period_edge_endpoints_in_vertex_orbit_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes hj_lt: "j < p"
  shows "fst ((geotop_oriented_edge_successor L ^^ j) s)
        \<in> (\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}
      \<and> fst ((geotop_oriented_edge_successor L ^^ Suc j) s)
        \<in> (\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}"
proof -
  let ?V = "(\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}"
  have hleft: "fst ((geotop_oriented_edge_successor L ^^ j) s) \<in> ?V"
  proof -
    have hj_mem: "j \<in> {0..<p}"
      using hj_lt by (by100 simp)
    show ?thesis
    proof (rule image_eqI[where x=j])
      show "fst ((geotop_oriented_edge_successor L ^^ j) s) =
          fst ((geotop_oriented_edge_successor L ^^ j) s)"
        by (by100 simp)
      show "j \<in> {0..<p}"
        by (rule hj_mem)
    qed
  qed
  have hright: "fst ((geotop_oriented_edge_successor L ^^ Suc j) s) \<in> ?V"
  proof (cases "Suc j < p")
    case True
    have hSuc_mem: "Suc j \<in> {0..<p}"
      using True by (by100 simp)
    show ?thesis
    proof (rule image_eqI[where x="Suc j"])
      show "fst ((geotop_oriented_edge_successor L ^^ Suc j) s) =
          fst ((geotop_oriented_edge_successor L ^^ Suc j) s)"
        by (by100 simp)
      show "Suc j \<in> {0..<p}"
        by (rule hSuc_mem)
    qed
  next
    case False
    have hSuc_eq: "Suc j = p"
      using hj_lt False by (by100 linarith)
    have hclose: "fst ((geotop_oriented_edge_successor L ^^ Suc j) s) = fst s"
      using hSuc_eq hp_closed by (by100 simp)
    have hzero: "0 \<in> {0..<p}"
      using hp_pos by (by100 simp)
    show ?thesis
    proof (rule image_eqI[where x=0])
      show "fst ((geotop_oriented_edge_successor L ^^ Suc j) s) =
          fst ((geotop_oriented_edge_successor L ^^ 0) s)"
        using hclose by (by100 simp)
      show "0 \<in> {0..<p}"
        by (rule hzero)
    qed
  qed
  show ?thesis
    using hleft hright by (by100 blast)
qed

lemma geotop_closed_segment_face_endpoint_or_self_prefix:
  fixes a b :: "real^2"
  assumes hab: "a \<noteq> b"
  assumes hface: "geotop_is_face F (closed_segment a b)"
  shows "F = {a} \<or> F = {b} \<or> F = closed_segment a b"
proof -
  have hsegV: "geotop_simplex_vertices (closed_segment a b) {a, b}"
    by (rule geotop_closed_segment_simplex_vertices[OF hab])
  obtain V W where hFV: "geotop_simplex_vertices (closed_segment a b) V"
      and hW_ne: "W \<noteq> {}"
      and hW_sub: "W \<subseteq> V"
      and hF_eq: "F = geotop_convex_hull W"
      and hFW: "geotop_simplex_vertices F W"
    by (rule geotop_face_witness_simplex_vertices_prefix[OF hface])
  have hV_eq: "V = {a, b}"
    by (rule geotop_simplex_vertices_unique[OF hFV hsegV])
  have hW_sub_ab: "W \<subseteq> {a, b}"
    using hW_sub hV_eq by (by100 simp)
  have hW_cases: "W = {a} \<or> W = {b} \<or> W = {a, b}"
    using hW_ne hW_sub_ab by (by100 blast)
  show ?thesis
  proof (rule disjE[OF hW_cases])
    assume hW: "W = {a}"
    have "F = {a}"
      using hF_eq hW geotop_convex_hull_eq_HOL[of "{a}"] by (by100 simp)
    thus ?thesis by (by100 blast)
  next
    assume hW_cases': "W = {b} \<or> W = {a, b}"
    show ?thesis
    proof (rule disjE[OF hW_cases'])
      assume hW: "W = {b}"
      have "F = {b}"
        using hF_eq hW geotop_convex_hull_eq_HOL[of "{b}"] by (by100 simp)
      thus ?thesis by (by100 blast)
    next
      assume hW: "W = {a, b}"
      have "F = closed_segment a b"
        using hF_eq hW geotop_convex_hull_eq_HOL[of "{a, b}"]
          segment_convex_hull[of a b]
        by (by100 simp)
      thus ?thesis by (by100 blast)
    qed
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_period_edge_face_in_cycle_subcomplex_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes hj_lt: "j < p"
  assumes hface: "geotop_is_face F
      (closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s)))"
  shows "F \<in> ((\<lambda>v. {v}) `
        ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
      \<union> ((\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p})"
proof -
  let ?v = "\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)"
  let ?V = "?v ` {0..<p}"
  let ?e = "\<lambda>j. closed_segment (?v j) (?v (Suc j))"
  let ?E = "?e ` {0..<p}"
  have hneq: "?v j \<noteq> ?v (Suc j)"
  proof -
    have hneq_sym: "?v (Suc j) \<noteq> ?v j"
      by (rule geotop_degree_two_oriented_edge_successor_funpow_next_vertex_distinct_prefix
          [OF hL hdegree hs])
    show ?thesis
      by (rule not_sym[OF hneq_sym])
  qed
  have hface_cases: "F = {?v j} \<or> F = {?v (Suc j)} \<or> F = ?e j"
    by (rule geotop_closed_segment_face_endpoint_or_self_prefix[OF hneq hface])
  have hendpoints: "?v j \<in> ?V \<and> ?v (Suc j) \<in> ?V"
    by (rule geotop_degree_two_oriented_edge_successor_period_edge_endpoints_in_vertex_orbit_prefix
        [OF hL hdegree hs hp_pos hp_closed hj_lt])
  have hj_mem: "j \<in> {0..<p}"
    using hj_lt by (by100 simp)
  show ?thesis
  proof (rule disjE[OF hface_cases])
    assume hF: "F = {?v j}"
    have "F \<in> ((\<lambda>v. {v}) ` ?V)"
    proof (rule image_eqI[where x = "?v j"])
      show "F = {?v j}"
        by (rule hF)
      show "?v j \<in> ?V"
        using hendpoints by (by100 blast)
    qed
    thus ?thesis by (by100 blast)
  next
    assume hcases: "F = {?v (Suc j)} \<or> F = ?e j"
    show ?thesis
    proof (rule disjE[OF hcases])
      assume hF: "F = {?v (Suc j)}"
      have "F \<in> ((\<lambda>v. {v}) ` ?V)"
      proof (rule image_eqI[where x = "?v (Suc j)"])
        show "F = {?v (Suc j)}"
          by (rule hF)
        show "?v (Suc j) \<in> ?V"
          using hendpoints by (by100 blast)
      qed
      thus ?thesis by (by100 blast)
    next
      assume hF: "F = ?e j"
      have "F \<in> ?E"
      proof (rule image_eqI[where x = j])
        show "F = ?e j"
          by (rule hF)
        show "j \<in> {0..<p}"
          by (rule hj_mem)
      qed
      thus ?thesis by (by100 blast)
    qed
  qed
qed

lemma geotop_singleton_face_eq_prefix:
  fixes v :: "real^2"
  assumes hface: "geotop_is_face F {v}"
  shows "F = {v}"
proof -
  obtain V W where hFV: "geotop_simplex_vertices {v} V"
      and hW_ne: "W \<noteq> {}"
      and hW_sub: "W \<subseteq> V"
      and hF_eq: "F = geotop_convex_hull W"
      and hFW: "geotop_simplex_vertices F W"
    by (rule geotop_face_witness_simplex_vertices_prefix[OF hface])
  have hV_eq: "V = {v}"
    by (rule geotop_singleton_simplex_vertices[OF hFV])
  have hW_eq: "W = {v}"
    using hW_ne hW_sub hV_eq by (by100 blast)
  show ?thesis
    using hF_eq hW_eq geotop_convex_hull_eq_HOL[of "{v}"] by (by100 simp)
qed

lemma geotop_degree_two_oriented_edge_successor_period_cycle_subcomplex_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  shows "geotop_is_complex
      (((\<lambda>v. {v}) `
        ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
      \<union> ((\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p}))
    \<and> (((\<lambda>v. {v}) `
        ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
      \<union> ((\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p}))
      \<subseteq> L"
proof -
  let ?v = "\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)"
  let ?V = "?v ` {0..<p}"
  let ?SV = "(\<lambda>v. {v}) ` ?V"
  let ?e = "\<lambda>j. closed_segment (?v j) (?v (Suc j))"
  let ?E = "?e ` {0..<p}"
  let ?K = "?SV \<union> ?E"
  have hcomplexL: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have hV_fin: "finite ?V"
    by (by100 simp)
  have hSV_fin: "finite ?SV"
    using hV_fin by (by100 simp)
  have hE_fin: "finite ?E"
    by (by100 simp)
  have hK_fin: "finite ?K"
    using hSV_fin hE_fin by (by100 simp)
  have hV_sub: "?V \<subseteq> {v. {v} \<in> L}"
  proof
    fix x
    assume hxV: "x \<in> ?V"
    obtain k where hk_mem: "k \<in> {0..<p}" and hx_eq: "x = ?v k"
      using hxV by (by100 blast)
    have "{?v k} \<in> L"
      by (rule geotop_degree_two_oriented_edge_successor_funpow_vertex_in_graph_prefix
          [OF hL hdegree hs])
    show "x \<in> {v. {v} \<in> L}"
      using hx_eq \<open>{?v k} \<in> L\<close> by (by100 simp)
  qed
  have hE_sub: "?E \<subseteq> {e\<in>L. geotop_is_edge e}"
  proof
    fix e
    assume heE: "e \<in> ?E"
    obtain j where hj_mem: "j \<in> {0..<p}" and he_eq: "e = ?e j"
      using heE by (by100 blast)
    have hedge_data: "?e j \<in> L \<and> geotop_is_edge (?e j)"
      by (rule geotop_degree_two_oriented_edge_successor_consecutive_vertices_edge_prefix
          [OF hL hdegree hs])
    show "e \<in> {e \<in> L. geotop_is_edge e}"
      using he_eq hedge_data by (by100 simp)
  qed
  have hK_sub: "?K \<subseteq> L"
  proof
    fix x
    assume hx: "x \<in> ?K"
    show "x \<in> L"
    proof (rule UnE[OF hx])
      assume hxSV: "x \<in> ?SV"
      obtain v where hvV: "v \<in> ?V" and hx_eq: "x = {v}"
        using hxSV by (by100 blast)
      have "{v} \<in> L"
        using hV_sub hvV by (by100 blast)
      show "x \<in> L"
        using hx_eq \<open>{v} \<in> L\<close> by (by100 simp)
    next
      assume hxE: "x \<in> ?E"
      have "x \<in> {e \<in> L. geotop_is_edge e}"
        using hE_sub hxE by (by100 blast)
      thus "x \<in> L"
        by (by100 simp)
    qed
  qed
  have hsimplex: "\<forall>\<sigma>\<in>?K. geotop_is_simplex \<sigma>"
  proof
    fix \<sigma>
    assume h\<sigma>K: "\<sigma> \<in> ?K"
    show "geotop_is_simplex \<sigma>"
    proof (rule UnE[OF h\<sigma>K])
      assume h\<sigma>SV: "\<sigma> \<in> ?SV"
      obtain v where h\<sigma>eq: "\<sigma> = {v}"
        using h\<sigma>SV by (by100 blast)
      have hdim: "geotop_simplex_dim {v} 0"
        by (rule geotop_singleton_is_simplex)
      have "geotop_is_simplex {v}"
        by (rule geotop_simplex_dim_imp_is_simplex[OF hdim])
      show "geotop_is_simplex \<sigma>"
        using h\<sigma>eq \<open>geotop_is_simplex {v}\<close> by (by100 simp)
    next
      assume h\<sigma>E: "\<sigma> \<in> ?E"
      have "\<sigma> \<in> {e \<in> L. geotop_is_edge e}"
        using hE_sub h\<sigma>E by (by100 blast)
      hence hedge: "geotop_is_edge \<sigma>"
        by (by100 simp)
      have hdim: "geotop_simplex_dim \<sigma> 1"
        using hedge unfolding geotop_is_edge_def by (by100 simp)
      show "geotop_is_simplex \<sigma>"
        by (rule geotop_simplex_dim_imp_is_simplex[OF hdim])
    qed
  qed
  have hfaces: "\<forall>\<sigma>\<in>?K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> ?K"
  proof (intro ballI allI impI)
    fix \<sigma> \<tau>
    assume h\<sigma>K: "\<sigma> \<in> ?K"
    assume hface: "geotop_is_face \<tau> \<sigma>"
    show "\<tau> \<in> ?K"
    proof (rule UnE[OF h\<sigma>K])
      assume h\<sigma>SV: "\<sigma> \<in> ?SV"
      obtain v where hvV: "v \<in> ?V" and h\<sigma>eq: "\<sigma> = {v}"
        using h\<sigma>SV by (by100 blast)
      have h\<tau>eq: "\<tau> = {v}"
        using hface h\<sigma>eq geotop_singleton_face_eq_prefix by (by100 blast)
      have "{v} \<in> ?SV"
        using hvV by (by100 blast)
      show "\<tau> \<in> ?K"
        using h\<tau>eq \<open>{v} \<in> ?SV\<close> by (by100 blast)
    next
      assume h\<sigma>E: "\<sigma> \<in> ?E"
      obtain j where hj_mem: "j \<in> {0..<p}" and h\<sigma>eq: "\<sigma> = ?e j"
        using h\<sigma>E by (by100 blast)
      have hj_lt: "j < p"
        using hj_mem by (by100 simp)
      have hface_j: "geotop_is_face \<tau> (?e j)"
        using hface h\<sigma>eq by (by100 simp)
      show "\<tau> \<in> ?K"
        by (rule geotop_degree_two_oriented_edge_successor_period_edge_face_in_cycle_subcomplex_prefix
            [OF hL hdegree hs hp_pos hp_closed hj_lt hface_j])
    qed
  qed
  have hinter:
      "\<forall>\<sigma>\<in>?K. \<forall>\<tau>\<in>?K. \<sigma> \<inter> \<tau> \<noteq> {}
        \<longrightarrow> geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma>
          \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
  proof (intro ballI impI)
    fix \<sigma> \<tau>
    assume h\<sigma>K: "\<sigma> \<in> ?K"
    assume h\<tau>K: "\<tau> \<in> ?K"
    assume hne: "\<sigma> \<inter> \<tau> \<noteq> {}"
    have h\<sigma>L: "\<sigma> \<in> L"
      using hK_sub h\<sigma>K by (by100 blast)
    have h\<tau>L: "\<tau> \<in> L"
      using hK_sub h\<tau>K by (by100 blast)
    have hL_inter: "\<forall>\<sigma>\<in>L. \<forall>\<tau>\<in>L. \<sigma> \<inter> \<tau> \<noteq> {}
        \<longrightarrow> geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma>
          \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
      by (rule geotop_is_complex_intersection[OF hcomplexL])
    show "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma>
        \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
      using hL_inter h\<sigma>L h\<tau>L hne by (by100 blast)
  qed
  have hlocfin: "\<forall>\<sigma>\<in>?K. \<exists>U. open U \<and> \<sigma> \<subseteq> U
      \<and> finite {\<tau>\<in>?K. \<tau> \<inter> U \<noteq> {}}"
  proof
    fix \<sigma>
    assume h\<sigma>K: "\<sigma> \<in> ?K"
    show "\<exists>U. open U \<and> \<sigma> \<subseteq> U
        \<and> finite {\<tau>\<in>?K. \<tau> \<inter> U \<noteq> {}}"
    proof (rule exI[where x = "UNIV"])
      show "open UNIV \<and> \<sigma> \<subseteq> UNIV
          \<and> finite {\<tau> \<in> ?K. \<tau> \<inter> UNIV \<noteq> {}}"
        using hK_fin by (by100 simp)
    qed
  qed
  have hK_complex: "geotop_is_complex ?K"
    unfolding geotop_is_complex_def
    using hsimplex hfaces hinter hlocfin by (by100 blast)
  show ?thesis
    using hK_complex hK_sub by (by100 blast)
qed

lemma geotop_degree_two_oriented_edge_successor_period_nonorbit_edge_avoids_vertex_orbit_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hnot: "e \<notin> ((\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p})"
  shows "e \<inter> ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}) = {}"
proof (rule ccontr)
  let ?V = "(\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}"
  let ?E = "(\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p}"
  assume hne: "e \<inter> ?V \<noteq> {}"
  obtain v where hv_e: "v \<in> e" and hvV: "v \<in> ?V"
    using hne by (by100 blast)
  have "e \<in> ?E"
    by (rule geotop_degree_two_oriented_edge_successor_period_vertex_orbit_incident_edge_in_edge_orbit_prefix
        [OF hL hdegree hs hp_pos hp_closed hvV heL hedge hv_e])
  show False
    using hnot \<open>e \<in> ?E\<close> by (by100 blast)
qed

lemma geotop_degree_two_oriented_edge_successor_period_closed_segment_edge_orbit_subset_edges_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  shows "(\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` I
      \<subseteq> {e\<in>L. geotop_is_edge e}"
proof
  fix e
  assume he: "e \<in> (\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` I"
  obtain j where hjI: "j \<in> I"
    and heq: "e = closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))"
    using he by (by100 blast)
  have hedge_data: "closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s)) \<in> L
      \<and> geotop_is_edge
        (closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ j) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc j) s)))"
    by (rule geotop_degree_two_oriented_edge_successor_consecutive_vertices_edge_prefix
        [OF hL hdegree hs])
  show "e \<in> {e \<in> L. geotop_is_edge e}"
    using heq hedge_data by (by100 simp)
qed

lemma geotop_degree_two_oriented_edge_successor_vertex_orbit_subset_vertices_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  shows "(\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` I
      \<subseteq> {v. {v} \<in> L}"
proof
  fix x
  assume hx: "x \<in> (\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` I"
  obtain k where hkI: "k \<in> I"
    and hx_eq: "x = fst ((geotop_oriented_edge_successor L ^^ k) s)"
    using hx by (by100 blast)
  have "{fst ((geotop_oriented_edge_successor L ^^ k) s)} \<in> L"
    by (rule geotop_degree_two_oriented_edge_successor_funpow_vertex_in_graph_prefix
        [OF hL hdegree hs])
  show "x \<in> {v. {v} \<in> L}"
    using hx_eq \<open>{fst ((geotop_oriented_edge_successor L ^^ k) s)} \<in> L\<close>
    by (by100 simp)
qed

lemma geotop_degree_two_oriented_edge_successor_edge_orbit_subset_edges_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  shows "(\<lambda>k. snd ((geotop_oriented_edge_successor L ^^ k) s)) ` I
      \<subseteq> {e\<in>L. geotop_is_edge e}"
proof
  fix x
  assume hx: "x \<in> (\<lambda>k. snd ((geotop_oriented_edge_successor L ^^ k) s)) ` I"
  obtain k where hkI: "k \<in> I"
    and hx_eq: "x = snd ((geotop_oriented_edge_successor L ^^ k) s)"
    using hx by (by100 blast)
  have hedge_data: "snd ((geotop_oriented_edge_successor L ^^ k) s) \<in> L
      \<and> geotop_is_edge (snd ((geotop_oriented_edge_successor L ^^ k) s))
      \<and> fst ((geotop_oriented_edge_successor L ^^ k) s)
          \<in> snd ((geotop_oriented_edge_successor L ^^ k) s)"
    by (rule geotop_degree_two_oriented_edge_successor_funpow_edge_in_graph_prefix
        [OF hL hdegree hs])
  show "x \<in> {e\<in>L. geotop_is_edge e}"
    using hx_eq hedge_data by (by100 simp)
qed

lemma geotop_degree_two_vertex_successor_least_period_orbit_package_prefix:
  fixes L :: "(real^2) set set" and w :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hwL: "{w} \<in> L"
  shows "\<exists>s q p. s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> fst s = w
      \<and> q \<noteq> w
      \<and> snd s = closed_segment w q
      \<and> {q} \<in> L
      \<and> 0 < p
      \<and> p \<le> Suc (card
          {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d})
      \<and> (geotop_oriented_edge_successor L ^^ p) s = s
      \<and> (\<forall>k. 0 < k \<and> k < p \<longrightarrow>
          (geotop_oriented_edge_successor L ^^ k) s \<noteq> s)
      \<and> inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}
      \<and> card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
proof -
  let ?S = "{(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  obtain s q where hs: "s \<in> ?S"
      and hfst: "fst s = w"
      and hqw: "q \<noteq> w"
      and hsnd: "snd s = closed_segment w q"
      and hqL: "{q} \<in> L"
    using geotop_degree_two_vertex_initial_oriented_edge_state_prefix
      [OF hL hdegree hwL] by (by100 blast)
  obtain p where hp_pos: "0 < p"
      and hp_le: "p \<le> Suc (card ?S)"
      and hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
      and hp_min: "\<forall>k. 0 < k \<and> k < p \<longrightarrow>
          (geotop_oriented_edge_successor L ^^ k) s \<noteq> s"
    using geotop_degree_two_oriented_edge_successor_least_period_prefix
      [OF hL hfin hdegree hs] by (by100 blast)
  have hinj: "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
    by (rule geotop_degree_two_oriented_edge_successor_least_period_orbit_inj_prefix
        [OF hL hdegree hs hp_pos hp_min])
  have hcard: "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
    by (rule geotop_degree_two_oriented_edge_successor_least_period_orbit_card_prefix
        [OF hL hdegree hs hp_pos hp_min])
  show ?thesis
  proof (intro exI conjI)
    show "s \<in> ?S" by (rule hs)
    show "fst s = w" by (rule hfst)
    show "q \<noteq> w" by (rule hqw)
    show "snd s = closed_segment w q" by (rule hsnd)
    show "{q} \<in> L" by (rule hqL)
    show "0 < p" by (rule hp_pos)
    show "p \<le> Suc (card ?S)" by (rule hp_le)
    show "(geotop_oriented_edge_successor L ^^ p) s = s" by (rule hp_closed)
    show "\<forall>k. 0 < k \<and> k < p \<longrightarrow>
        (geotop_oriented_edge_successor L ^^ k) s \<noteq> s"
      by (rule hp_min)
    show "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
      by (rule hinj)
    show "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
      by (rule hcard)
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_initial_neighbor_before_period_prefix:
  fixes L :: "(real^2) set set" and w q :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hfst: "fst s = w"
  assumes hq_ne: "q \<noteq> w"
  assumes hsnd: "snd s = closed_segment w q"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  shows "fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q
      \<and> 1 < p"
proof -
  have hq_ne_s: "q \<noteq> fst s"
    using hq_ne hfst by (by100 simp)
  have hsnd_s: "snd s = closed_segment (fst s) q"
    using hsnd hfst by (by100 simp)
  have hfirst: "fst (geotop_oriented_edge_successor L s) = q"
    by (rule geotop_degree_two_oriented_edge_successor_first_step_endpoint_prefix
        [OF hL hdegree hs hq_ne_s hsnd_s])
  have hfirst_funpow: "fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q"
    using hfirst by (by100 simp)
  have hp_gt1: "1 < p"
  proof (rule ccontr)
    assume hnot: "\<not> 1 < p"
    have hp_eq: "p = 1"
      using hp_pos hnot by (by100 linarith)
    have "geotop_oriented_edge_successor L s = s"
      using hp_closed hp_eq by (by100 simp)
    hence "fst (geotop_oriented_edge_successor L s) = fst s"
      by (by100 simp)
    hence "q = w"
      using hfirst hfst by (by100 simp)
    thus False
      using hq_ne by (by100 blast)
  qed
  show ?thesis
    using hfirst_funpow hp_gt1 by (by100 blast)
qed

lemma geotop_degree_two_vertex_successor_started_least_period_orbit_package_prefix:
  fixes L :: "(real^2) set set" and w :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hwL: "{w} \<in> L"
  shows "\<exists>s q p. s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> fst s = w
      \<and> q \<noteq> w
      \<and> snd s = closed_segment w q
      \<and> {q} \<in> L
      \<and> 1 < p
      \<and> fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q
      \<and> p \<le> Suc (card
          {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d})
      \<and> (geotop_oriented_edge_successor L ^^ p) s = s
      \<and> (\<forall>k. 0 < k \<and> k < p \<longrightarrow>
          (geotop_oriented_edge_successor L ^^ k) s \<noteq> s)
      \<and> inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}
      \<and> card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
proof -
  let ?S = "{(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  have hpackage: "\<exists>s q p. s \<in> ?S
      \<and> fst s = w
      \<and> q \<noteq> w
      \<and> snd s = closed_segment w q
      \<and> {q} \<in> L
      \<and> 0 < p
      \<and> p \<le> Suc (card ?S)
      \<and> (geotop_oriented_edge_successor L ^^ p) s = s
      \<and> (\<forall>k. 0 < k \<and> k < p \<longrightarrow>
          (geotop_oriented_edge_successor L ^^ k) s \<noteq> s)
      \<and> inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}
      \<and> card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
    by (rule geotop_degree_two_vertex_successor_least_period_orbit_package_prefix
        [OF hL hfin hdegree hwL])
  obtain s q p where hpkg: "s \<in> ?S
      \<and> fst s = w
      \<and> q \<noteq> w
      \<and> snd s = closed_segment w q
      \<and> {q} \<in> L
      \<and> 0 < p
      \<and> p \<le> Suc (card ?S)
      \<and> (geotop_oriented_edge_successor L ^^ p) s = s
      \<and> (\<forall>k. 0 < k \<and> k < p \<longrightarrow>
          (geotop_oriented_edge_successor L ^^ k) s \<noteq> s)
      \<and> inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}
      \<and> card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
    using hpackage by (elim exE)
  have hs: "s \<in> ?S"
    using hpkg by (by100 simp)
  have hfst: "fst s = w"
    using hpkg by (by100 simp)
  have hq_ne: "q \<noteq> w"
    using hpkg by (by100 simp)
  have hsnd: "snd s = closed_segment w q"
    using hpkg by (by100 simp)
  have hqL: "{q} \<in> L"
    using hpkg by (by100 simp)
  have hp_pos: "0 < p"
    using hpkg by (by100 simp)
  have hp_le: "p \<le> Suc (card ?S)"
    using hpkg by (by100 simp)
  have hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
    using hpkg by (by100 simp)
  have hp_min: "\<forall>k. 0 < k \<and> k < p \<longrightarrow>
      (geotop_oriented_edge_successor L ^^ k) s \<noteq> s"
    using hpkg by (by100 simp)
  have hinj: "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
    using hpkg by (by100 simp)
  have hcard: "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
    using hpkg by (by100 simp)
  have hstart: "fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q
      \<and> 1 < p"
    by (rule geotop_degree_two_oriented_edge_successor_initial_neighbor_before_period_prefix
        [OF hL hdegree hs hfst hq_ne hsnd hp_pos hp_closed])
  show ?thesis
  proof (intro exI conjI)
    show "s \<in> ?S" by (rule hs)
    show "fst s = w" by (rule hfst)
    show "q \<noteq> w" by (rule hq_ne)
    show "snd s = closed_segment w q" by (rule hsnd)
    show "{q} \<in> L" by (rule hqL)
    show "1 < p" using hstart by (by100 blast)
    show "fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q"
      using hstart by (by100 blast)
    show "p \<le> Suc (card ?S)" by (rule hp_le)
    show "(geotop_oriented_edge_successor L ^^ p) s = s" by (rule hp_closed)
    show "\<forall>k. 0 < k \<and> k < p \<longrightarrow>
        (geotop_oriented_edge_successor L ^^ k) s \<noteq> s"
      by (rule hp_min)
    show "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
      by (rule hinj)
    show "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
      by (rule hcard)
  qed
qed

lemma geotop_degree_two_vertex_successor_started_cycle_edge_package_prefix:
  fixes L :: "(real^2) set set" and w :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hwL: "{w} \<in> L"
  shows "\<exists>s q p. s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> fst s = w
      \<and> q \<noteq> w
      \<and> snd s = closed_segment w q
      \<and> {q} \<in> L
      \<and> 1 < p
      \<and> fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q
      \<and> (geotop_oriented_edge_successor L ^^ p) s = s
      \<and> (\<forall>k. 0 < k \<and> k < p \<longrightarrow>
          (geotop_oriented_edge_successor L ^^ k) s \<noteq> s)
      \<and> inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}
      \<and> card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p
      \<and> closed_segment (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
          (fst s) \<in> L
      \<and> geotop_is_edge
          (closed_segment (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
            (fst s))"
proof -
  let ?S = "{(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  have hstarted: "\<exists>s q p. s \<in> ?S
      \<and> fst s = w
      \<and> q \<noteq> w
      \<and> snd s = closed_segment w q
      \<and> {q} \<in> L
      \<and> 1 < p
      \<and> fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q
      \<and> p \<le> Suc (card ?S)
      \<and> (geotop_oriented_edge_successor L ^^ p) s = s
      \<and> (\<forall>k. 0 < k \<and> k < p \<longrightarrow>
          (geotop_oriented_edge_successor L ^^ k) s \<noteq> s)
      \<and> inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}
      \<and> card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
    by (rule geotop_degree_two_vertex_successor_started_least_period_orbit_package_prefix
        [OF hL hfin hdegree hwL])
  obtain s q p where hpkg: "s \<in> ?S
      \<and> fst s = w
      \<and> q \<noteq> w
      \<and> snd s = closed_segment w q
      \<and> {q} \<in> L
      \<and> 1 < p
      \<and> fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q
      \<and> p \<le> Suc (card ?S)
      \<and> (geotop_oriented_edge_successor L ^^ p) s = s
      \<and> (\<forall>k. 0 < k \<and> k < p \<longrightarrow>
          (geotop_oriented_edge_successor L ^^ k) s \<noteq> s)
      \<and> inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}
      \<and> card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
    using hstarted by (elim exE)
  have hs: "s \<in> ?S"
    using hpkg by (by100 simp)
  have hfst: "fst s = w"
    using hpkg by (by100 simp)
  have hq_ne: "q \<noteq> w"
    using hpkg by (by100 simp)
  have hsnd: "snd s = closed_segment w q"
    using hpkg by (by100 simp)
  have hqL: "{q} \<in> L"
    using hpkg by (by100 simp)
  have hp_gt1: "1 < p"
    using hpkg by (by100 simp)
  have hfirst: "fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q"
    using hpkg by (by100 simp)
  have hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
    using hpkg by (by100 simp)
  have hp_min: "\<forall>k. 0 < k \<and> k < p \<longrightarrow>
      (geotop_oriented_edge_successor L ^^ k) s \<noteq> s"
    using hpkg by (by100 simp)
  have hinj: "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
    using hpkg by (by100 simp)
  have hcard: "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
    using hpkg by (by100 simp)
  have hp_pos: "0 < p"
    using hp_gt1 by (by100 linarith)
  have hclosing: "closed_segment (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
        (fst s) \<in> L
      \<and> geotop_is_edge
        (closed_segment (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
          (fst s))"
    by (rule geotop_degree_two_oriented_edge_successor_period_closing_edge_prefix
        [OF hL hdegree hs hp_pos hp_closed])
  show ?thesis
  proof (intro exI conjI)
    show "s \<in> ?S" by (rule hs)
    show "fst s = w" by (rule hfst)
    show "q \<noteq> w" by (rule hq_ne)
    show "snd s = closed_segment w q" by (rule hsnd)
    show "{q} \<in> L" by (rule hqL)
    show "1 < p" by (rule hp_gt1)
    show "fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q"
      by (rule hfirst)
    show "(geotop_oriented_edge_successor L ^^ p) s = s"
      by (rule hp_closed)
    show "\<forall>k. 0 < k \<and> k < p \<longrightarrow>
        (geotop_oriented_edge_successor L ^^ k) s \<noteq> s"
      by (rule hp_min)
    show "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
      by (rule hinj)
    show "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
      by (rule hcard)
    show "closed_segment (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
        (fst s) \<in> L"
      using hclosing by (by100 blast)
    show "geotop_is_edge
        (closed_segment (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
          (fst s))"
      using hclosing by (by100 blast)
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_finite_total_function_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  shows "finite {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> (\<forall>s \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}.
        \<exists>!t. t \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
          \<and> geotop_oriented_edge_successor_state L s t)"
proof -
  have hstate_fin: "finite {(v, d). {v} \<in> L \<and> d \<in> L
      \<and> geotop_is_edge d \<and> v \<in> d}"
    by (rule geotop_finite_linear_graph_oriented_edge_states_finite_graph_prefix
        [OF hL hfin])
  have htotal: "\<forall>s \<in> {(v, d). {v} \<in> L \<and> d \<in> L
      \<and> geotop_is_edge d \<and> v \<in> d}.
      \<exists>!t. t \<in> {(v, d). {v} \<in> L \<and> d \<in> L
        \<and> geotop_is_edge d \<and> v \<in> d}
        \<and> geotop_oriented_edge_successor_state L s t"
  proof
    fix s
    assume hs: "s \<in> {(v, d). {v} \<in> L \<and> d \<in> L
        \<and> geotop_is_edge d \<and> v \<in> d}"
    show "\<exists>!t. t \<in> {(v, d). {v} \<in> L \<and> d \<in> L
        \<and> geotop_is_edge d \<and> v \<in> d}
        \<and> geotop_oriented_edge_successor_state L s t"
      by (rule geotop_degree_two_oriented_edge_successor_relation_total_unique_prefix
          [OF hL hdegree hs])
  qed
  show ?thesis
    using hstate_fin htotal by (by100 blast)
qed

end
