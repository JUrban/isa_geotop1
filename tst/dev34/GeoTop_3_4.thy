theory GeoTop_3_4
  imports "GeoTop34CoreDirty.GeoTop_3_4_Core"
begin

lemma geotop_standard_2simplex_exists_dev34:
  shows "\<exists>\<sigma> :: (real^2) set. geotop_simplex_dim \<sigma> 2"
proof -
  let ?V = "insert (0::real^2) Basis"
  have hfin: "finite ?V"
    by (by100 simp)
  have hne: "?V \<noteq> {}"
    by (by100 simp)
  have h0: "(0::real^2) \<notin> Basis"
    by (by100 simp)
  have hdep_image:
      "\<not> dependent ((\<lambda>x::real^2. - (0::real^2) + x) ` Basis)"
    using independent_Basis by (by100 simp)
  have hai: "\<not> affine_dependent ?V"
    using affine_dependent_iff_dependent[OF h0] hdep_image by (by100 simp)
  have hvertices: "geotop_simplex_vertices (geotop_convex_hull ?V) ?V"
    by (rule geotop_AI_finite_ne_is_simplex_vertices[OF hfin hne hai])
  have hcard_basis: "card (Basis :: (real^2) set) = 2"
    by (by100 simp)
  have hcard: "card ?V = 2 + 1"
    using h0 hcard_basis by (by100 simp)
  obtain m n where hfin': "finite ?V"
    and hcard_n: "card ?V = n + 1"
    and hn_le_m: "n \<le> m"
    and hgp: "geotop_general_position ?V m"
    and hhull: "geotop_convex_hull ?V = geotop_convex_hull ?V"
    using hvertices unfolding geotop_simplex_vertices_def by (by100 blast)
  have hn: "n = 2"
    using hcard hcard_n by (by100 linarith)
  have h2_le_m: "2 \<le> m"
    using hn hn_le_m by (by100 simp)
  have hdim: "geotop_simplex_dim (geotop_convex_hull ?V) 2"
    unfolding geotop_simplex_dim_def
  proof (intro exI conjI)
    show "finite ?V"
      by (rule hfin')
    show "card ?V = 2 + 1"
      by (rule hcard)
    show "2 \<le> m"
      by (rule h2_le_m)
    show "geotop_general_position ?V m"
      by (rule hgp)
    show "geotop_convex_hull ?V = geotop_convex_hull ?V"
      by (rule hhull)
  qed
  show ?thesis
    using hdim by (by100 blast)
qed

lemma geotop_isomorphism_refl_id_dev34:
  fixes K :: "'a::real_normed_vector set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_isomorphism K K id"
proof -
  have hbij: "bij_betw id (geotop_complex_vertices K) (geotop_complex_vertices K)"
    by (by100 simp)
  have hcond: "\<forall>V. V \<subseteq> geotop_complex_vertices K \<longrightarrow>
      (geotop_convex_hull V \<in> K \<longleftrightarrow> geotop_convex_hull (id ` V) \<in> K)"
    by (by100 simp)
  show ?thesis
    unfolding geotop_isomorphism_def using hbij hcond by (by100 blast)
qed

lemma geotop_subdivision_source_is_complex_dev34:
  fixes K K' :: "'a::real_normed_vector set set"
  assumes hsub: "geotop_is_subdivision K' K"
  shows "geotop_is_complex K'"
  using hsub unfolding geotop_is_subdivision_def by (by100 blast)

lemma geotop_comb_boundary_subset_complex_dev34:
  fixes K :: "'a::real_normed_vector set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_comb_boundary K n \<subseteq> K"
  (**
    The combinatorial boundary consists of selected \((n-1)\)-simplexes of
    \<open>K\<close> and their faces; face closure of a complex keeps all of them inside
    \<open>K\<close>. **)
proof
  fix \<rho>
  assume h\<rho>: "\<rho> \<in> geotop_comb_boundary K n"
  let ?S = "{\<tau> \<in> K. geotop_simplex_dim \<tau> (n - 1) \<and>
      card {\<sigma> \<in> K. geotop_simplex_dim \<sigma> n \<and> geotop_is_face \<tau> \<sigma>} = 1}"
  have hface_closed: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    using hK unfolding geotop_is_complex_def by (elim conjE) assumption
  have h\<rho>_cases: "\<rho> \<in> ?S \<union> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
    using h\<rho> unfolding geotop_comb_boundary_def by (by100 simp)
  show "\<rho> \<in> K"
  proof (rule UnE[OF h\<rho>_cases])
    assume "\<rho> \<in> ?S"
    show "\<rho> \<in> K"
      using \<open>\<rho> \<in> ?S\<close> by (by100 blast)
  next
    assume "\<rho> \<in> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
    then obtain \<tau> where h\<tau>S: "\<tau> \<in> ?S" and h\<rho>\<tau>: "geotop_is_face \<rho> \<tau>"
      by (by100 blast)
    have h\<tau>K: "\<tau> \<in> K"
      using h\<tau>S by (by100 blast)
    show "\<rho> \<in> K"
      using hface_closed h\<tau>K h\<rho>\<tau> by (by100 blast)
  qed
qed

lemma geotop_2simplex_comb_boundary_member_proper_face_dev34:
  fixes \<sigma> \<rho> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes h\<rho>:
    "\<rho> \<in> geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
  shows "geotop_is_face \<rho> \<sigma> \<and> \<rho> \<noteq> \<sigma>"
  (**
    In the face complex of a 2-simplex, every simplex of the combinatorial
    boundary is a proper face of the top 2-simplex. **)
proof -
  let ?K = "{\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
  let ?S = "{\<tau> \<in> ?K. geotop_simplex_dim \<tau> (2 - 1) \<and>
      card {\<theta> \<in> ?K. geotop_simplex_dim \<theta> 2 \<and> geotop_is_face \<tau> \<theta>} = 1}"
  have h\<rho>_cases: "\<rho> \<in> ?S \<union> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
    using h\<rho> unfolding geotop_comb_boundary_def by (by100 simp)
  have hS_proper: "\<forall>\<tau>\<in>?S. geotop_is_face \<tau> \<sigma> \<and> \<tau> \<noteq> \<sigma>"
  proof
    fix \<tau>
    assume h\<tau>S: "\<tau> \<in> ?S"
    have h\<tau>K: "\<tau> \<in> ?K"
      using h\<tau>S by (by100 blast)
    have h\<tau>dim1: "geotop_simplex_dim \<tau> 1"
      using h\<tau>S by (by100 simp)
    have h\<tau>ne\<sigma>: "\<tau> \<noteq> \<sigma>"
    proof
      assume h\<tau>eq: "\<tau> = \<sigma>"
      have h\<tau>dim2: "geotop_simplex_dim \<tau> 2"
        using h\<sigma> h\<tau>eq by (by100 simp)
      have h12: "(1::nat) = 2"
        by (rule geotop_simplex_dim_unique[OF h\<tau>dim1 h\<tau>dim2])
      show False
        using h12 by (by100 simp)
    qed
    have h\<tau>\<sigma>: "geotop_is_face \<tau> \<sigma>"
      using h\<tau>K h\<tau>ne\<sigma> by (by100 blast)
    show "geotop_is_face \<tau> \<sigma> \<and> \<tau> \<noteq> \<sigma>"
      using h\<tau>\<sigma> h\<tau>ne\<sigma> by (by100 blast)
  qed
  show ?thesis
  proof (rule UnE[OF h\<rho>_cases])
    assume h\<rho>S: "\<rho> \<in> ?S"
    show ?thesis
      using hS_proper h\<rho>S by (by100 blast)
  next
    assume "\<rho> \<in> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
    then obtain \<tau> where h\<tau>S: "\<tau> \<in> ?S" and h\<rho>\<tau>: "geotop_is_face \<rho> \<tau>"
      by (by100 blast)
    have h\<tau>\<sigma>: "geotop_is_face \<tau> \<sigma>"
      using hS_proper h\<tau>S by (by100 blast)
    have h\<tau>ne\<sigma>: "\<tau> \<noteq> \<sigma>"
      using hS_proper h\<tau>S by (by100 blast)
    have h\<rho>\<sigma>: "geotop_is_face \<rho> \<sigma>"
      by (rule geotop_is_face_trans[OF h\<rho>\<tau> h\<tau>\<sigma>])
    have h\<rho>ne\<sigma>: "\<rho> \<noteq> \<sigma>"
    proof
      assume h\<rho>eq: "\<rho> = \<sigma>"
      have h\<sigma>sub\<tau>: "\<sigma> \<subseteq> \<tau>"
        using geotop_is_face_imp_subset[OF h\<rho>\<tau>] h\<rho>eq by (by100 simp)
      have h\<tau>sub\<sigma>: "\<tau> \<subseteq> \<sigma>"
        by (rule geotop_is_face_imp_subset[OF h\<tau>\<sigma>])
      have "\<tau> = \<sigma>"
        using h\<sigma>sub\<tau> h\<tau>sub\<sigma> by (by100 blast)
      show False
        using h\<tau>ne\<sigma> \<open>\<tau> = \<sigma>\<close> by (by100 blast)
    qed
    show ?thesis
      using h\<rho>\<sigma> h\<rho>ne\<sigma> by (by100 blast)
  qed
qed

lemma geotop_2simplex_face_complex_edge_unique_top_2face_dev34:
  fixes \<sigma> e :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hedge: "geotop_simplex_dim e 1"
  assumes hface: "geotop_is_face e \<sigma>"
  shows "card {\<theta> \<in> {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}.
      geotop_simplex_dim \<theta> 2 \<and> geotop_is_face e \<theta>} = 1"
proof -
  let ?K = "{\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
  let ?S = "{\<theta> \<in> ?K. geotop_simplex_dim \<theta> 2 \<and> geotop_is_face e \<theta>}"
  have h\<sigma>S: "\<sigma> \<in> ?S"
    using h\<sigma> hface by (by100 simp)
  have hSsub: "?S \<subseteq> {\<sigma>}"
  proof
    fix \<theta>
    assume h\<theta>S: "\<theta> \<in> ?S"
    have h\<theta>K: "\<theta> \<in> ?K"
      using h\<theta>S by (by100 blast)
    have h\<theta>dim: "geotop_simplex_dim \<theta> 2"
      using h\<theta>S by (by100 blast)
    have hcase: "geotop_is_face \<theta> \<sigma> \<or> \<theta> = \<sigma>"
      using h\<theta>K by (by100 blast)
    show "\<theta> \<in> {\<sigma>}"
    proof (rule disjE[OF hcase])
      assume h\<theta>face: "geotop_is_face \<theta> \<sigma>"
      have h\<sigma>simplex: "geotop_is_simplex \<sigma>"
        by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>])
      have h\<sigma>conv: "convex \<sigma>"
        by (rule GeoTopBase0.geotop_simplex_is_convex[OF h\<sigma>simplex])
      have h\<theta>HOL: "\<theta> face_of \<sigma>"
        by (rule geotop_is_face_imp_HOL_face_of_R2[OF h\<theta>face])
      have h\<sigma>hyper: "geotop_hyperplane_dim (affine hull \<sigma>) 2"
        by (rule geotop_simplex_dim_imp_hyperplane_dim[OF h\<sigma>])
      have h\<theta>hyper: "geotop_hyperplane_dim (affine hull \<theta>) 2"
        by (rule geotop_simplex_dim_imp_hyperplane_dim[OF h\<theta>dim])
      have h\<sigma>aff: "aff_dim \<sigma> = 2"
        using geotop_hyperplane_dim_imp_affine_aff_dim[OF h\<sigma>hyper]
        by (by100 simp)
      have h\<theta>aff: "aff_dim \<theta> = 2"
        using geotop_hyperplane_dim_imp_affine_aff_dim[OF h\<theta>hyper]
        by (by100 simp)
      have "\<theta> = \<sigma>"
      proof (rule ccontr)
        assume hne: "\<theta> \<noteq> \<sigma>"
        have "aff_dim \<theta> < aff_dim \<sigma>"
          by (rule face_of_aff_dim_lt[OF h\<sigma>conv h\<theta>HOL hne])
        show False
          using \<open>aff_dim \<theta> < aff_dim \<sigma>\<close> h\<sigma>aff h\<theta>aff by (by100 simp)
      qed
      show "\<theta> \<in> {\<sigma>}"
        using \<open>\<theta> = \<sigma>\<close> by (by100 simp)
    next
      assume "\<theta> = \<sigma>"
      show "\<theta> \<in> {\<sigma>}"
        using \<open>\<theta> = \<sigma>\<close> by (by100 simp)
    qed
  qed
  have "?S = {\<sigma>}"
    using h\<sigma>S hSsub by (by100 blast)
  show ?thesis
    using \<open>?S = {\<sigma>}\<close> by (by100 simp)
qed

lemma geotop_2simplex_edge_face_in_comb_boundary_dev34:
  fixes \<sigma> e :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hedge: "geotop_simplex_dim e 1"
  assumes hface: "geotop_is_face e \<sigma>"
  shows "e \<in> geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
proof -
  let ?K = "{\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
  let ?S = "{\<tau> \<in> ?K. geotop_simplex_dim \<tau> (2 - 1) \<and>
      card {\<theta> \<in> ?K. geotop_simplex_dim \<theta> 2 \<and> geotop_is_face \<tau> \<theta>} = 1}"
  have heK: "e \<in> ?K"
    using hface by (by100 simp)
  have hcard:
      "card {\<theta> \<in> ?K. geotop_simplex_dim \<theta> 2 \<and> geotop_is_face e \<theta>} = 1"
    by (rule geotop_2simplex_face_complex_edge_unique_top_2face_dev34
        [OF h\<sigma> hedge hface])
  have "e \<in> ?S"
    using heK hedge hcard by (by100 simp)
  show ?thesis
    unfolding geotop_comb_boundary_def Let_def using \<open>e \<in> ?S\<close> by (by100 blast)
qed

lemma geotop_2simplex_vertex_face_in_comb_boundary_dev34:
  fixes \<sigma> vface :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hvface: "geotop_simplex_dim vface 0"
  assumes hface: "geotop_is_face vface \<sigma>"
  shows "vface \<in> geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and hv_eq: "vface = geotop_convex_hull W"
    and hvW: "geotop_simplex_vertices vface W"
    by (rule geotop_face_witness_simplex_vertices[OF hface])
  obtain V2 m where hV2_fin: "finite V2"
    and hV2_card: "card V2 = 2 + 1"
    and h2_le_m: "2 \<le> m"
    and hgp_V2: "geotop_general_position V2 m"
    and h\<sigma>_eq_V2: "\<sigma> = geotop_convex_hull V2"
    using h\<sigma> unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V2: "geotop_simplex_vertices \<sigma> V2"
    unfolding geotop_simplex_vertices_def
    using hV2_fin hV2_card h2_le_m hgp_V2 h\<sigma>_eq_V2 by (by100 blast)
  have hV_eq: "V = V2"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>V2])
  obtain W0 m0 where hW0_fin: "finite W0"
    and hW0_card: "card W0 = 0 + 1"
    and h0_le_m0: "0 \<le> m0"
    and hgp_W0: "geotop_general_position W0 m0"
    and hv_eq_W0: "vface = geotop_convex_hull W0"
    using hvface unfolding geotop_simplex_dim_def by (by100 blast)
  have hvW0: "geotop_simplex_vertices vface W0"
    unfolding geotop_simplex_vertices_def
    using hW0_fin hW0_card h0_le_m0 hgp_W0 hv_eq_W0 by (by100 blast)
  have hW_eq: "W = W0"
    by (rule geotop_simplex_vertices_unique[OF hvW hvW0])
  have hW_card: "card W = 1"
    using hW_eq hW0_card by (by100 simp)
  have hW_fin: "finite W"
    using hW_eq hW0_fin by (by100 simp)
  have hV2_not_sub_W: "\<not> V2 \<subseteq> W"
  proof
    assume hsub: "V2 \<subseteq> W"
    have "card V2 \<le> card W"
      by (rule card_mono[OF hW_fin hsub])
    show False
      using \<open>card V2 \<le> card W\<close> hV2_card hW_card by (by100 simp)
  qed
  obtain u where huV2: "u \<in> V2" and huW: "u \<notin> W"
    using hV2_not_sub_W by (by100 blast)
  let ?X = "insert u W"
  define e where "e = geotop_convex_hull ?X"
  have hW_sub_V2: "W \<subseteq> V2"
    using hW_sub hV_eq by (by100 simp)
  have hX_sub: "?X \<subseteq> V2"
    using hW_sub_V2 huV2 by (by100 blast)
  have hX_ne: "?X \<noteq> {}"
    by (by100 simp)
  have hX_fin: "finite ?X"
    using hW_fin by (by100 simp)
  have hX_card: "card ?X = 1 + 1"
    using hW_fin hW_card huW by (by100 simp)
  have h1_le_m: "1 \<le> m"
    using h2_le_m by (by100 simp)
  have hgp_X: "geotop_general_position ?X m"
    by (rule geotop_general_position_subset[OF hgp_V2 hX_sub])
  have heV: "geotop_simplex_vertices e ?X"
    unfolding geotop_simplex_vertices_def e_def
    using hX_fin hX_card h1_le_m hgp_X by (by100 blast)
  have heface: "geotop_is_face e \<sigma>"
    unfolding e_def
    by (rule geotop_is_face_of_subset[OF h\<sigma>V2 hX_ne hX_sub])
  have hedim: "geotop_simplex_dim e 1"
    unfolding geotop_simplex_dim_def e_def
    using hX_fin hX_card h1_le_m hgp_X by (by100 blast)
  have hv_face_e: "geotop_is_face vface e"
  proof -
    have hW_sub_X: "W \<subseteq> ?X"
      by (by100 blast)
    show ?thesis
      unfolding geotop_is_face_def using heV hW_ne hW_sub_X hv_eq by (by100 blast)
  qed
  let ?K = "{\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
  let ?S = "{\<tau> \<in> ?K. geotop_simplex_dim \<tau> (2 - 1) \<and>
      card {\<theta> \<in> ?K. geotop_simplex_dim \<theta> 2 \<and> geotop_is_face \<tau> \<theta>} = 1}"
  have heK: "e \<in> ?K"
    using heface by (by100 simp)
  have hcard:
      "card {\<theta> \<in> ?K. geotop_simplex_dim \<theta> 2 \<and> geotop_is_face e \<theta>} = 1"
    by (rule geotop_2simplex_face_complex_edge_unique_top_2face_dev34
        [OF h\<sigma> hedim heface])
  have heS: "e \<in> ?S"
    using heK hedim hcard by (by100 simp)
  show ?thesis
    unfolding geotop_comb_boundary_def Let_def
    using heS hv_face_e by (by100 blast)
qed

lemma geotop_2simplex_proper_face_in_comb_boundary_dev34:
  fixes \<sigma> \<rho> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hface: "geotop_is_face \<rho> \<sigma>"
  assumes hne: "\<rho> \<noteq> \<sigma>"
  shows "\<rho> \<in> geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and h\<rho>_eq: "\<rho> = geotop_convex_hull W"
    and h\<rho>W: "geotop_simplex_vertices \<rho> W"
    by (rule geotop_face_witness_simplex_vertices[OF hface])
  obtain V2 m where hV2_fin: "finite V2"
    and hV2_card: "card V2 = 2 + 1"
    and h2_le_m: "2 \<le> m"
    and hgp_V2: "geotop_general_position V2 m"
    and h\<sigma>_eq_V2: "\<sigma> = geotop_convex_hull V2"
    using h\<sigma> unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V2: "geotop_simplex_vertices \<sigma> V2"
    unfolding geotop_simplex_vertices_def
    using hV2_fin hV2_card h2_le_m hgp_V2 h\<sigma>_eq_V2 by (by100 blast)
  have hV_eq: "V = V2"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>V2])
  have hW_sub_V2: "W \<subseteq> V2"
    using hW_sub hV_eq by (by100 simp)
  have hW_fin: "finite W"
    by (rule finite_subset[OF hW_sub_V2 hV2_fin])
  have hW_card_pos: "0 < card W"
    using hW_fin hW_ne card_gt_0_iff by (by100 blast)
  have hW_card_le3: "card W \<le> 3"
    using card_mono[OF hV2_fin hW_sub_V2] hV2_card by (by100 simp)
  have hW_card_ne3: "card W \<noteq> 3"
  proof
    assume hW_card3: "card W = 3"
    have hW_eq_V2: "W = V2"
      by (rule card_subset_eq[OF hV2_fin hW_sub_V2])
        (use hW_card3 hV2_card in \<open>by100 simp\<close>)
    have "\<rho> = \<sigma>"
      using h\<rho>_eq h\<sigma>_eq_V2 hW_eq_V2 by (by100 simp)
    show False
      using hne \<open>\<rho> = \<sigma>\<close> by (by100 blast)
  qed
  have hW_card_cases: "card W = 1 \<or> card W = 2"
    using hW_card_pos hW_card_le3 hW_card_ne3 by (by100 linarith)
  show ?thesis
  proof (rule disjE[OF hW_card_cases])
    assume hW_card1: "card W = 1"
    have h\<rho>dim0: "geotop_simplex_dim \<rho> 0"
    proof -
      obtain m' n' where hWfin': "finite W"
        and hWcard': "card W = n' + 1"
        and hn'm': "n' \<le> m'"
        and hgpW': "geotop_general_position W m'"
        and h\<rho>eq': "\<rho> = geotop_convex_hull W"
        using h\<rho>W unfolding geotop_simplex_vertices_def by (by100 blast)
      have "n' = 0"
        using hW_card1 hWcard' by (by100 linarith)
      show ?thesis
        unfolding geotop_simplex_dim_def
        using hWfin' hWcard' hn'm' hgpW' h\<rho>eq' \<open>n' = 0\<close> by (by100 blast)
    qed
    show ?thesis
      by (rule geotop_2simplex_vertex_face_in_comb_boundary_dev34
          [OF h\<sigma> h\<rho>dim0 hface])
  next
    assume hW_card2: "card W = 2"
    have h\<rho>dim1: "geotop_simplex_dim \<rho> 1"
    proof -
      obtain m' n' where hWfin': "finite W"
        and hWcard': "card W = n' + 1"
        and hn'm': "n' \<le> m'"
        and hgpW': "geotop_general_position W m'"
        and h\<rho>eq': "\<rho> = geotop_convex_hull W"
        using h\<rho>W unfolding geotop_simplex_vertices_def by (by100 blast)
      have "n' = 1"
        using hW_card2 hWcard' by (by100 linarith)
      show ?thesis
        unfolding geotop_simplex_dim_def
        using hWfin' hWcard' hn'm' hgpW' h\<rho>eq' \<open>n' = 1\<close> by (by100 blast)
    qed
    show ?thesis
      by (rule geotop_2simplex_edge_face_in_comb_boundary_dev34
          [OF h\<sigma> h\<rho>dim1 hface])
  qed
qed

lemma geotop_2simplex_comb_boundary_finite_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  shows "finite (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
proof -
  let ?K = "{\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
  have hK_complex: "geotop_is_complex ?K"
    by (rule geotop_simplex_dim_face_complex_is_complex_R2[OF h\<sigma>])
  have hbd_sub: "geotop_comb_boundary ?K 2 \<subseteq> ?K"
    by (rule geotop_comb_boundary_subset_complex_dev34[OF hK_complex])
  have hK_finite: "finite ?K"
    by (rule geotop_simplex_dim_face_complex_finite_R2[OF h\<sigma>])
  show ?thesis
    by (rule finite_subset[OF hbd_sub hK_finite])
qed

lemma geotop_2simplex_comb_boundary_is_complex_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  shows "geotop_is_complex
    (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
proof -
  let ?K = "{\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
  let ?B = "geotop_comb_boundary ?K 2"
  have hK_complex: "geotop_is_complex ?K"
    by (rule geotop_simplex_dim_face_complex_is_complex_R2[OF h\<sigma>])
  have hB_sub_K: "?B \<subseteq> ?K"
    by (rule geotop_comb_boundary_subset_complex_dev34[OF hK_complex])
  have hB_fin: "finite ?B"
    by (rule geotop_2simplex_comb_boundary_finite_dev34[OF h\<sigma>])
  have hK_simplexes: "\<forall>\<tau>\<in>?K. geotop_is_simplex \<tau>"
    using conjunct1[OF hK_complex[unfolded geotop_is_complex_def]] .
  have hsimplexes: "\<forall>\<tau>\<in>?B. geotop_is_simplex \<tau>"
  proof
    fix \<tau>
    assume h\<tau>B: "\<tau> \<in> ?B"
    have h\<tau>K: "\<tau> \<in> ?K"
      using hB_sub_K h\<tau>B by (by100 blast)
    show "geotop_is_simplex \<tau>"
      using hK_simplexes h\<tau>K by (by100 blast)
  qed
  have hface_closed: "\<forall>\<tau>\<in>?B. \<forall>\<rho>. geotop_is_face \<rho> \<tau> \<longrightarrow> \<rho> \<in> ?B"
  proof (intro ballI allI impI)
    fix \<tau> \<rho>
    assume h\<tau>B: "\<tau> \<in> ?B"
    assume h\<rho>\<tau>: "geotop_is_face \<rho> \<tau>"
    have h\<tau>proper: "geotop_is_face \<tau> \<sigma> \<and> \<tau> \<noteq> \<sigma>"
      by (rule geotop_2simplex_comb_boundary_member_proper_face_dev34
          [OF h\<sigma> h\<tau>B])
    have h\<tau>\<sigma>: "geotop_is_face \<tau> \<sigma>"
      using h\<tau>proper by (by100 blast)
    have h\<tau>ne\<sigma>: "\<tau> \<noteq> \<sigma>"
      using h\<tau>proper by (by100 blast)
    have h\<rho>\<sigma>: "geotop_is_face \<rho> \<sigma>"
      by (rule geotop_is_face_trans[OF h\<rho>\<tau> h\<tau>\<sigma>])
    have h\<rho>ne\<sigma>: "\<rho> \<noteq> \<sigma>"
    proof
      assume h\<rho>eq: "\<rho> = \<sigma>"
      have h\<sigma>sub\<tau>: "\<sigma> \<subseteq> \<tau>"
        using geotop_is_face_imp_subset[OF h\<rho>\<tau>] h\<rho>eq by (by100 simp)
      have h\<tau>sub\<sigma>: "\<tau> \<subseteq> \<sigma>"
        by (rule geotop_is_face_imp_subset[OF h\<tau>\<sigma>])
      have "\<tau> = \<sigma>"
        using h\<sigma>sub\<tau> h\<tau>sub\<sigma> by (by100 blast)
      show False
        using h\<tau>ne\<sigma> \<open>\<tau> = \<sigma>\<close> by (by100 blast)
    qed
    show "\<rho> \<in> ?B"
      by (rule geotop_2simplex_proper_face_in_comb_boundary_dev34
          [OF h\<sigma> h\<rho>\<sigma> h\<rho>ne\<sigma>])
  qed
  have hintersections:
      "\<forall>\<tau>\<in>?B. \<forall>\<rho>\<in>?B. \<tau> \<inter> \<rho> \<noteq> {} \<longrightarrow>
        geotop_is_face (\<tau> \<inter> \<rho>) \<tau> \<and> geotop_is_face (\<tau> \<inter> \<rho>) \<rho>"
  proof (intro ballI impI)
    fix \<tau> \<rho>
    assume h\<tau>B: "\<tau> \<in> ?B"
    assume h\<rho>B: "\<rho> \<in> ?B"
    assume hmeet: "\<tau> \<inter> \<rho> \<noteq> {}"
    have hK_inter:
        "\<forall>\<alpha>\<in>?K. \<forall>\<beta>\<in>?K. \<alpha> \<inter> \<beta> \<noteq> {} \<longrightarrow>
          geotop_is_face (\<alpha> \<inter> \<beta>) \<alpha> \<and> geotop_is_face (\<alpha> \<inter> \<beta>) \<beta>"
      using conjunct1[OF conjunct2[OF conjunct2[
        OF hK_complex[unfolded geotop_is_complex_def]]]] .
    have h\<tau>K: "\<tau> \<in> ?K"
      using hB_sub_K h\<tau>B by (by100 blast)
    have h\<rho>K: "\<rho> \<in> ?K"
      using hB_sub_K h\<rho>B by (by100 blast)
    show "geotop_is_face (\<tau> \<inter> \<rho>) \<tau> \<and> geotop_is_face (\<tau> \<inter> \<rho>) \<rho>"
      using hK_inter h\<tau>K h\<rho>K hmeet by (by100 blast)
  qed
  have hlocfin:
      "\<forall>\<tau>\<in>?B. \<exists>U. open U \<and> \<tau> \<subseteq> U
        \<and> finite {\<rho>\<in>?B. \<rho> \<inter> U \<noteq> {}}"
  proof
    fix \<tau>
    assume h\<tau>B: "\<tau> \<in> ?B"
    have hopen: "open (UNIV :: (real^2) set)"
      by (by100 simp)
    have hsub: "\<tau> \<subseteq> (UNIV :: (real^2) set)"
      by (by100 simp)
    have hfin: "finite {\<rho>\<in>?B. \<rho> \<inter> (UNIV :: (real^2) set) \<noteq> {}}"
      using hB_fin by (by100 simp)
    show "\<exists>U. open U \<and> \<tau> \<subseteq> U \<and> finite {\<rho>\<in>?B. \<rho> \<inter> U \<noteq> {}}"
      using hopen hsub hfin by (by100 blast)
  qed
  show ?thesis
    unfolding geotop_is_complex_def
    using hsimplexes hface_closed hintersections hlocfin by (by100 blast)
qed

lemma geotop_degree_two_oriented_edge_successor_period_gt_two_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hdegree_two:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs:
    "s \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_gt1: "1 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  shows "2 < p"
  (**
    Degree-two successor cycles have at least three oriented edge states.  A
    two-step return would make the second successor state traverse the same
    closed segment in the reverse direction, while the successor-state
    definition requires consecutive edge simplexes to be distinct. **)
proof (rule ccontr)
  assume hnot: "\<not> 2 < p"
  have hp_eq2: "p = 2"
    using hp_gt1 hnot by (by100 linarith)
  let ?succ = "geotop_oriented_edge_successor L"
  let ?t = "?succ s"
  have hstep0:
      "?t \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> geotop_oriented_edge_successor_state L s ?t"
    by (rule geotop_degree_two_oriented_edge_successor_fun_step_prefix
        [OF hL_linear hdegree_two hs])
  have ht_state:
      "?t \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
    by (rule conjunct1[OF hstep0])
  have hrel0: "geotop_oriented_edge_successor_state L s ?t"
    using hstep0 by (by100 blast)
  have hstep1:
      "?succ ?t \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> geotop_oriented_edge_successor_state L ?t (?succ ?t)"
    by (rule geotop_degree_two_oriented_edge_successor_fun_step_prefix
        [OF hL_linear hdegree_two ht_state])
  have hclosed2: "(?succ ^^ 2) s = s"
    using hp_closed hp_eq2 by (by100 simp)
  have htwo: "(2::nat) = Suc (Suc 0)"
    by (by100 simp)
  have hfunpow2: "(?succ ^^ 2) s = ?succ (?succ s)"
    by (subst htwo, simp only: funpow.simps comp_apply id_apply)
  have hsucc2: "?succ ?t = s"
    using hclosed2 hfunpow2 by (by100 simp)
  have hrel1: "geotop_oriented_edge_successor_state L ?t s"
    using hstep1 hsucc2 by (by100 simp)
  have hs_edge: "snd s = closed_segment (fst s) (fst ?t)"
    using hrel0 unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have ht_edge: "snd ?t = closed_segment (fst ?t) (fst s)"
    using hrel1 unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have hedges_ne: "snd s \<noteq> snd ?t"
    using hrel1 unfolding geotop_oriented_edge_successor_state_def by (by100 simp)
  have hedges_eq: "snd ?t = snd s"
    using hs_edge ht_edge closed_segment_commute[of "fst ?t" "fst s"] by (by100 simp)
  show False
    using hedges_ne hedges_eq by (by100 blast)
qed

lemma geotop_successor_cycle_state_edge_image_eq_closed_segments_dev34:
  fixes L :: "(real^2) set set"
  assumes hedge_image:
    "((\<lambda>k. snd ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}) = E"
  assumes hstate_edge_eq:
    "\<And>k. snd ((geotop_oriented_edge_successor L ^^ k) s)
      = closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ k) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))"
  shows "((\<lambda>k. closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ k) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))) ` {0..<p}) = E"
proof -
  have himage:
      "((\<lambda>k. closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ k) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))) ` {0..<p})
      = ((\<lambda>k. snd ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p})"
  proof (rule image_cong)
    show "{0..<p} = {0..<p}"
      by (rule HOL.refl)
    fix k
    assume "k \<in> {0..<p}"
    show "closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ k) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))
        = snd ((geotop_oriented_edge_successor L ^^ k) s)"
      using hstate_edge_eq[of k] by (by100 simp)
  qed
  show ?thesis
    using himage hedge_image by (by100 simp)
qed

lemma geotop_successor_cycle_listing_vertex_edge_decomp_dev34:
  fixes L :: "(real^2) set set"
  assumes hvertex_image:
    "((\<lambda>k. v k) ` {0..<p}) = geotop_complex_vertices L"
  assumes hedge_segments:
    "((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})
      = {e\<in>L. geotop_is_edge e}"
  assumes hL_decomp:
    "L = ((\<lambda>v. {v}) ` geotop_complex_vertices L) \<union>
      {e\<in>L. geotop_is_edge e}"
  shows "L =
    ((\<lambda>x. {x}) ` ((\<lambda>k. v k) ` {0..<p}))
    \<union> ((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})"
  using hvertex_image hedge_segments hL_decomp by (by100 simp)

lemma geotop_face_dim_le_dev34:
  fixes \<tau> \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> n"
  assumes hface: "geotop_is_face \<tau> \<sigma>"
  shows "\<exists>k. k \<le> n \<and> geotop_simplex_dim \<tau> k"
  (**
    Face-dimension monotonicity used by the Figure 4.10 boundary model:
    the combinatorial boundary contains \((n-1)\)-faces and their faces, so
    the second layer is still at most \((n-1)\)-dimensional. **)
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and h\<tau>_eq: "\<tau> = geotop_convex_hull W"
    and h\<tau>W: "geotop_simplex_vertices \<tau> W"
    by (rule geotop_face_witness_simplex_vertices[OF hface])
  obtain Vn m where hVn_fin: "finite Vn"
    and hVn_card: "card Vn = n + 1"
    and hn_le_m: "n \<le> m"
    and hgp_Vn: "geotop_general_position Vn m"
    and h\<sigma>_eq_Vn: "\<sigma> = geotop_convex_hull Vn"
    using h\<sigma> unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>Vn: "geotop_simplex_vertices \<sigma> Vn"
    unfolding geotop_simplex_vertices_def
    using hVn_fin hVn_card hn_le_m hgp_Vn h\<sigma>_eq_Vn by (by100 blast)
  have hV_eq: "V = Vn"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>Vn])
  have hW_sub_Vn: "W \<subseteq> Vn"
    using hW_sub hV_eq by (by100 simp)
  obtain m' k where hW_fin: "finite W"
    and hW_card: "card W = k + 1"
    and hk_le_m': "k \<le> m'"
    and hgp_W: "geotop_general_position W m'"
    and h\<tau>_eq_W: "\<tau> = geotop_convex_hull W"
    using h\<tau>W unfolding geotop_simplex_vertices_def by (by100 blast)
  have hcard_le: "card W \<le> card Vn"
    by (rule card_mono[OF hVn_fin hW_sub_Vn])
  have hk_le_n: "k \<le> n"
    using hcard_le hW_card hVn_card by (by100 linarith)
  have h\<tau>dim: "geotop_simplex_dim \<tau> k"
    unfolding geotop_simplex_dim_def
    using hW_fin hW_card hk_le_m' hgp_W h\<tau>_eq_W by (by100 blast)
  show ?thesis
    using hk_le_n h\<tau>dim by (by100 blast)
qed

lemma geotop_2simplex_comb_boundary_is_1dim_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  shows "geotop_complex_is_1dim
    (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  (**
    The frontier complex of a 2-simplex is a finite 1-complex: it consists
    of boundary edges and their vertex faces. **)
proof -
  let ?K = "{\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
  let ?S = "{\<tau> \<in> ?K. geotop_simplex_dim \<tau> (2 - 1) \<and>
      card {\<theta> \<in> ?K. geotop_simplex_dim \<theta> 2 \<and> geotop_is_face \<tau> \<theta>} = 1}"
  show ?thesis
    unfolding geotop_complex_is_1dim_def
  proof
    fix \<rho>
    assume h\<rho>B: "\<rho> \<in> geotop_comb_boundary ?K 2"
    have h\<rho>cases: "\<rho> \<in> ?S \<union> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
      using h\<rho>B unfolding geotop_comb_boundary_def Let_def by (by100 simp)
    show "\<exists>n::nat. n \<le> 1 \<and> geotop_simplex_dim \<rho> n"
    proof (rule UnE[OF h\<rho>cases])
      assume h\<rho>S: "\<rho> \<in> ?S"
      have h\<rho>dim1: "geotop_simplex_dim \<rho> 1"
        using h\<rho>S by (by100 simp)
      show ?thesis
      proof (intro exI conjI)
        show "(1::nat) \<le> 1"
          by (by100 simp)
        show "geotop_simplex_dim \<rho> 1"
          by (rule h\<rho>dim1)
      qed
    next
      assume "\<rho> \<in> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
      then obtain \<tau> where h\<tau>S: "\<tau> \<in> ?S" and h\<rho>\<tau>: "geotop_is_face \<rho> \<tau>"
        by (by100 blast)
      have h\<tau>dim: "geotop_simplex_dim \<tau> 1"
        using h\<tau>S by (by100 simp)
      obtain k where hk_le: "k \<le> 1" and h\<rho>dim: "geotop_simplex_dim \<rho> k"
        using geotop_face_dim_le_dev34[OF h\<tau>dim h\<rho>\<tau>] by (by100 blast)
      show ?thesis
        using hk_le h\<rho>dim by (by100 blast)
    qed
  qed
qed

lemma geotop_finite_polyhedron_points_as_vertices_dev34:
  fixes K :: "'a::euclidean_space set set" and S :: "'a set"
  assumes hK_complex: "geotop_is_complex K"
  assumes hK_1dim: "geotop_complex_is_1dim K"
  assumes hK_finite: "finite K"
  assumes hS_finite: "finite S"
  assumes hS_poly: "S \<subseteq> geotop_polyhedron K"
  shows "\<exists>K'. geotop_is_complex K'
      \<and> geotop_complex_is_1dim K'
      \<and> finite K'
      \<and> geotop_polyhedron K' = geotop_polyhedron K
      \<and> (\<forall>x\<in>S. {x} \<in> K')
      \<and> (\<forall>v. {v} \<in> K \<longrightarrow> {v} \<in> K')"
  (**
    Iterated finite-point subdivision helper for the boundary-realization
    packages.  It keeps the carrier fixed while making a prescribed finite
    subset of the carrier into vertices, and it records survival of the old
    vertices for the next subdivision step. **)
proof -
  have hinduct:
    "\<And>S. finite S \<Longrightarrow> S \<subseteq> geotop_polyhedron K \<Longrightarrow>
      \<exists>K'. geotop_is_complex K'
        \<and> geotop_complex_is_1dim K'
        \<and> finite K'
        \<and> geotop_polyhedron K' = geotop_polyhedron K
        \<and> (\<forall>x\<in>S. {x} \<in> K')
        \<and> (\<forall>v. {v} \<in> K \<longrightarrow> {v} \<in> K')"
  proof -
    fix S :: "'a set"
    assume hS_fin: "finite S"
    show "S \<subseteq> geotop_polyhedron K \<Longrightarrow>
      \<exists>K'. geotop_is_complex K'
        \<and> geotop_complex_is_1dim K'
        \<and> finite K'
        \<and> geotop_polyhedron K' = geotop_polyhedron K
        \<and> (\<forall>x\<in>S. {x} \<in> K')
        \<and> (\<forall>v. {v} \<in> K \<longrightarrow> {v} \<in> K')"
      using hS_fin
    proof (induction S rule: finite_induct)
      case empty
      have hS_vertices: "\<forall>x\<in>{}. {x} \<in> K"
        by (by100 simp)
      have hold_vertices: "\<forall>v. {v} \<in> K \<longrightarrow> {v} \<in> K"
        by (by100 simp)
      show ?case
        using hK_complex hK_1dim hK_finite hS_vertices hold_vertices
        by (by100 blast)
    next
      case (insert x S)
      have hS_poly: "S \<subseteq> geotop_polyhedron K"
        using insert.prems by (by100 blast)
      have hx_poly: "x \<in> geotop_polyhedron K"
        using insert.prems by (by100 blast)
      obtain K0 where hK0_complex: "geotop_is_complex K0"
        and hK0_1dim: "geotop_complex_is_1dim K0"
        and hK0_finite: "finite K0"
        and hK0_poly: "geotop_polyhedron K0 = geotop_polyhedron K"
        and hS_vertices: "\<forall>y\<in>S. {y} \<in> K0"
        and hold_vertices0: "\<forall>v. {v} \<in> K \<longrightarrow> {v} \<in> K0"
        using insert.IH[OF hS_poly] by (by100 blast)
      have hx_poly0: "x \<in> geotop_polyhedron K0"
        using hx_poly hK0_poly by (by100 simp)
      obtain K1 where hK1_complex: "geotop_is_complex K1"
        and hK1_1dim: "geotop_complex_is_1dim K1"
        and hK1_poly0: "geotop_polyhedron K1 = geotop_polyhedron K0"
        and hx_vertex: "{x} \<in> K1"
        and hvertices_preserved: "\<forall>v. {v} \<in> K0 \<longrightarrow> {v} \<in> K1"
        and hfinite_imp: "finite K0 \<longrightarrow> finite K1"
        using geotop_complex_subdivide_at[OF hK0_complex hK0_1dim hx_poly0]
        by (by100 blast)
      have hK1_finite: "finite K1"
        using hfinite_imp hK0_finite by (by100 blast)
      have hK1_poly: "geotop_polyhedron K1 = geotop_polyhedron K"
        using hK1_poly0 hK0_poly by (by100 simp)
      have hS_vertices1: "\<forall>y\<in>S. {y} \<in> K1"
        using hS_vertices hvertices_preserved by (by100 blast)
      have hinsert_vertices: "\<forall>y\<in>insert x S. {y} \<in> K1"
        using hx_vertex hS_vertices1 by (by100 blast)
      have hold_vertices1: "\<forall>v. {v} \<in> K \<longrightarrow> {v} \<in> K1"
        using hold_vertices0 hvertices_preserved by (by100 blast)
      show ?case
        using hK1_complex hK1_1dim hK1_finite hK1_poly
          hinsert_vertices hold_vertices1
        by (by100 blast)
    qed
  qed
  show ?thesis
    by (rule hinduct[OF hS_finite hS_poly])
qed

lemma geotop_2simplex_boundary_finite_points_as_vertices_dev34:
  fixes \<sigma> :: "(real^2) set" and S :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hS_finite: "finite S"
  assumes hS_poly:
    "S \<subseteq> geotop_polyhedron
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  shows "\<exists>F. geotop_is_complex F
      \<and> geotop_complex_is_1dim F
      \<and> finite F
      \<and> geotop_polyhedron F =
        geotop_polyhedron
          (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> (\<forall>x\<in>S. {x} \<in> F)
      \<and> (\<forall>v.
        {v} \<in> geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2
        \<longrightarrow> {v} \<in> F)"
  (**
    Moise Fig. 4.10 boundary-edge subdivision helper.  Any finite set of
    prescribed points on the frontier complex of a 2-simplex can be made into
    vertices of a finite 1-complex with the same boundary carrier. **)
proof -
  let ?B = "geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
  have hB_complex: "geotop_is_complex ?B"
    by (rule geotop_2simplex_comb_boundary_is_complex_dev34[OF h\<sigma>])
  have hB_1dim: "geotop_complex_is_1dim ?B"
    by (rule geotop_2simplex_comb_boundary_is_1dim_dev34[OF h\<sigma>])
  have hB_finite: "finite ?B"
    by (rule geotop_2simplex_comb_boundary_finite_dev34[OF h\<sigma>])
  obtain F where hF:
      "geotop_is_complex F
      \<and> geotop_complex_is_1dim F
      \<and> finite F
      \<and> geotop_polyhedron F = geotop_polyhedron ?B
      \<and> (\<forall>x\<in>S. {x} \<in> F)
      \<and> (\<forall>v. {v} \<in> ?B \<longrightarrow> {v} \<in> F)"
    using geotop_finite_polyhedron_points_as_vertices_dev34
      [OF hB_complex hB_1dim hB_finite hS_finite hS_poly]
    by (by100 blast)
  show ?thesis
    using hF by (by100 blast)
qed

lemma geotop_2simplex_boundary_finite_points_subdivision_vertices_dev34:
  fixes \<sigma> :: "(real^2) set" and S :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hS_finite: "finite S"
  assumes hS_poly:
    "S \<subseteq> geotop_polyhedron
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  shows "\<exists>F. geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> finite F
      \<and> (\<forall>x\<in>S. {x} \<in> F)"
  (**
    Strengthened Fig. 4.10 edge-subdivision helper.  After making the
    prescribed boundary points vertices in a same-carrier 1-complex, take a
    common subdivision with the original boundary complex; singleton parent
    simplexes force the prescribed points to remain vertices. **)
proof -
  let ?B = "geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
  obtain K\<^sub>0 where hK\<^sub>0_complex: "geotop_is_complex K\<^sub>0"
      and hK\<^sub>0_1dim: "geotop_complex_is_1dim K\<^sub>0"
      and hK\<^sub>0_finite: "finite K\<^sub>0"
      and hK\<^sub>0_poly: "geotop_polyhedron K\<^sub>0 = geotop_polyhedron ?B"
      and hS_vertices_K\<^sub>0: "\<forall>x\<in>S. {x} \<in> K\<^sub>0"
      and hold_vertices:
        "\<forall>v. {v} \<in> ?B \<longrightarrow> {v} \<in> K\<^sub>0"
    using geotop_2simplex_boundary_finite_points_as_vertices_dev34
      [OF h\<sigma> hS_finite hS_poly]
    by (by100 blast)
  have hB_complex: "geotop_is_complex ?B"
    by (rule geotop_2simplex_comb_boundary_is_complex_dev34[OF h\<sigma>])
  have hB_finite: "finite ?B"
    by (rule geotop_2simplex_comb_boundary_finite_dev34[OF h\<sigma>])
  have hpoly_eq: "geotop_polyhedron ?B = geotop_polyhedron K\<^sub>0"
    using hK\<^sub>0_poly by (by100 simp)
  obtain F where hF_B: "geotop_is_subdivision F ?B"
      and hF_K\<^sub>0: "geotop_is_subdivision F K\<^sub>0"
    using geotop_common_subdivision_finite
      [OF hB_complex hK\<^sub>0_complex hB_finite hK\<^sub>0_finite hpoly_eq]
    by (by100 blast)
  have hF_finite: "finite F"
    by (rule geotop_subdivision_of_finite_is_finite[OF hB_finite hF_B])
  have hF_complex: "geotop_is_complex F"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hF_B])
  have hS_vertices_F: "\<forall>x\<in>S. {x} \<in> F"
  proof
    fix x
    assume hxS: "x \<in> S"
    have hxK\<^sub>0: "{x} \<in> K\<^sub>0"
      using hS_vertices_K\<^sub>0 hxS by (by100 blast)
    have hcover:
        "{x} = \<Union>{\<rho>\<in>F. \<rho> \<subseteq> {x}}"
      by (rule geotop_subdivision_covers_simplex
          [OF hK\<^sub>0_complex hF_complex hK\<^sub>0_finite hF_finite hF_K\<^sub>0 hxK\<^sub>0])
    have hx_union: "x \<in> \<Union>{\<rho>\<in>F. \<rho> \<subseteq> {x}}"
      using hcover by (by100 simp)
    obtain \<rho> where h\<rho>F: "\<rho> \<in> F"
        and h\<rho>sub: "\<rho> \<subseteq> {x}"
        and hx\<rho>: "x \<in> \<rho>"
      using hx_union by (by100 blast)
    have h\<rho>eq: "\<rho> = {x}"
      using h\<rho>sub hx\<rho> by (by100 blast)
    show "{x} \<in> F"
      using h\<rho>F h\<rho>eq by (by100 simp)
  qed
  show ?thesis
    using hF_B hF_finite hS_vertices_F by (by100 blast)
qed

lemma geotop_2simplex_boundary_finite_points_subdivision_preserves_vertices_dev34:
  fixes \<sigma> :: "(real^2) set" and S :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hS_finite: "finite S"
  assumes hS_poly:
    "S \<subseteq> geotop_polyhedron
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  shows "\<exists>F. geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> finite F
      \<and> (\<forall>x\<in>S. {x} \<in> F)
      \<and> (\<forall>v.
        {v} \<in> geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2
        \<longrightarrow> {v} \<in> F)"
  (**
    Fig. 4.10 boundary-subdivision helper with endpoint preservation: the
    final common subdivision keeps both the newly prescribed boundary points and
    the original vertices of the 2-simplex boundary as vertices. **)
proof -
  let ?B = "geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
  obtain K\<^sub>0 where hK\<^sub>0_complex: "geotop_is_complex K\<^sub>0"
      and hK\<^sub>0_1dim: "geotop_complex_is_1dim K\<^sub>0"
      and hK\<^sub>0_finite: "finite K\<^sub>0"
      and hK\<^sub>0_poly: "geotop_polyhedron K\<^sub>0 = geotop_polyhedron ?B"
      and hS_vertices_K\<^sub>0: "\<forall>x\<in>S. {x} \<in> K\<^sub>0"
      and hold_vertices_K\<^sub>0:
        "\<forall>v. {v} \<in> ?B \<longrightarrow> {v} \<in> K\<^sub>0"
    using geotop_2simplex_boundary_finite_points_as_vertices_dev34
      [OF h\<sigma> hS_finite hS_poly]
    by (by100 blast)
  have hB_complex: "geotop_is_complex ?B"
    by (rule geotop_2simplex_comb_boundary_is_complex_dev34[OF h\<sigma>])
  have hB_finite: "finite ?B"
    by (rule geotop_2simplex_comb_boundary_finite_dev34[OF h\<sigma>])
  have hpoly_eq: "geotop_polyhedron ?B = geotop_polyhedron K\<^sub>0"
    using hK\<^sub>0_poly by (by100 simp)
  obtain F where hF_B: "geotop_is_subdivision F ?B"
      and hF_K\<^sub>0: "geotop_is_subdivision F K\<^sub>0"
    using geotop_common_subdivision_finite
      [OF hB_complex hK\<^sub>0_complex hB_finite hK\<^sub>0_finite hpoly_eq]
    by (by100 blast)
  have hF_finite: "finite F"
    by (rule geotop_subdivision_of_finite_is_finite[OF hB_finite hF_B])
  have hF_complex: "geotop_is_complex F"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hF_B])
  have hsingleton_survives: "\<And>x. {x} \<in> K\<^sub>0 \<Longrightarrow> {x} \<in> F"
  proof -
    fix x
    assume hxK\<^sub>0: "{x} \<in> K\<^sub>0"
    have hcover:
        "{x} = \<Union>{\<rho>\<in>F. \<rho> \<subseteq> {x}}"
      by (rule geotop_subdivision_covers_simplex
          [OF hK\<^sub>0_complex hF_complex hK\<^sub>0_finite hF_finite hF_K\<^sub>0 hxK\<^sub>0])
    have hx_union: "x \<in> \<Union>{\<rho>\<in>F. \<rho> \<subseteq> {x}}"
      using hcover by (by100 simp)
    obtain \<rho> where h\<rho>F: "\<rho> \<in> F"
        and h\<rho>sub: "\<rho> \<subseteq> {x}"
        and hx\<rho>: "x \<in> \<rho>"
      using hx_union by (by100 blast)
    have h\<rho>eq: "\<rho> = {x}"
      using h\<rho>sub hx\<rho> by (by100 blast)
    show "{x} \<in> F"
      using h\<rho>F h\<rho>eq by (by100 simp)
  qed
  have hS_vertices_F: "\<forall>x\<in>S. {x} \<in> F"
    using hS_vertices_K\<^sub>0 hsingleton_survives by (by100 blast)
  have hold_vertices_F: "\<forall>v. {v} \<in> ?B \<longrightarrow> {v} \<in> F"
    using hold_vertices_K\<^sub>0 hsingleton_survives by (by100 blast)
  show ?thesis
    using hF_B hF_finite hS_vertices_F hold_vertices_F by (by100 blast)
qed

lemma geotop_cyclic_listing_isomorphism_from_matching_cases_dev34:
  fixes L F :: "(real^2) set set" and v u :: "nat \<Rightarrow> real^2"
    and \<psi> :: "real^2 \<Rightarrow> real^2"
  assumes hsource_vertices:
    "((\<lambda>k. v k) ` {0..<p}) = geotop_complex_vertices L"
  assumes htarget_vertices:
    "((\<lambda>k. u k) ` {0..<p}) = geotop_complex_vertices F"
  assumes hsource_closed: "v p = v 0"
  assumes htarget_closed: "u p = u 0"
  assumes h\<psi>bij: "bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)"
  assumes h\<psi>idx: "\<forall>k\<in>{0..<p}. \<psi> (v k) = u k"
  assumes hsource_cases:
    "\<And>W. W \<subseteq> geotop_complex_vertices L
      \<Longrightarrow> geotop_convex_hull W \<in> L
      \<Longrightarrow> (\<exists>x\<in>((\<lambda>k. v k) ` {0..<p}). W = {x})
        \<or> (\<exists>k\<in>{0..<p}. W = {v k, v (Suc k)})"
  assumes hsource_single:
    "\<And>x. x \<in> ((\<lambda>k. v k) ` {0..<p})
      \<Longrightarrow> geotop_convex_hull {x} \<in> L"
  assumes hsource_edge:
    "\<And>k. k \<in> {0..<p}
      \<Longrightarrow> geotop_convex_hull {v k, v (Suc k)} \<in> L"
  assumes htarget_cases:
    "\<And>W. W \<subseteq> geotop_complex_vertices F
      \<Longrightarrow> geotop_convex_hull W \<in> F
      \<Longrightarrow> (\<exists>x\<in>((\<lambda>k. u k) ` {0..<p}). W = {x})
        \<or> (\<exists>k\<in>{0..<p}. W = {u k, u (Suc k)})"
  assumes htarget_single:
    "\<And>x. x \<in> ((\<lambda>k. u k) ` {0..<p})
      \<Longrightarrow> geotop_convex_hull {x} \<in> F"
  assumes htarget_edge:
    "\<And>k. k \<in> {0..<p}
      \<Longrightarrow> geotop_convex_hull {u k, u (Suc k)} \<in> F"
  shows "geotop_isomorphism L F \<psi>"
  (**
    Fig. 4.10 bookkeeping lemma.  After both cyclic complexes have been reduced
    to singleton/adjacent-edge hull cases and the listed vertices are matched by
    a vertex bijection, the simplicial isomorphism condition follows by
    transferring those two cases in both directions. **)
proof -
  let ?VL = "geotop_complex_vertices L"
  let ?VF = "geotop_complex_vertices F"
  let ?VI = "((\<lambda>k. v k) ` {0..<p})"
  let ?UI = "((\<lambda>k. u k) ` {0..<p})"
  have h\<psi>inj: "inj_on \<psi> ?VL"
    using h\<psi>bij by (rule bij_betw_imp_inj_on)
  have hp_pos_if_idx: "\<And>k. k \<in> {0..<p} \<Longrightarrow> 0 < p"
    by (by100 simp)
  have hsource_suc_in_image:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow> v (Suc k) \<in> ?VI"
  proof -
    fix k
    assume hk: "k \<in> {0..<p}"
    show "v (Suc k) \<in> ?VI"
    proof (cases "Suc k < p")
      case True
      hence "Suc k \<in> {0..<p}"
        by (by100 simp)
      thus ?thesis
        by (by100 blast)
    next
      case False
      have hSuc_eq: "Suc k = p"
        using hk False by (by100 simp)
      have "0 \<in> {0..<p}"
        using hp_pos_if_idx[OF hk] by (by100 simp)
      hence "v 0 \<in> ?VI"
        by (by100 blast)
      thus ?thesis
        using hSuc_eq hsource_closed by (by100 simp)
    qed
  qed
  have htarget_suc_in_image:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow> u (Suc k) \<in> ?UI"
  proof -
    fix k
    assume hk: "k \<in> {0..<p}"
    show "u (Suc k) \<in> ?UI"
    proof (cases "Suc k < p")
      case True
      hence "Suc k \<in> {0..<p}"
        by (by100 simp)
      thus ?thesis
        by (by100 blast)
    next
      case False
      have hSuc_eq: "Suc k = p"
        using hk False by (by100 simp)
      have "0 \<in> {0..<p}"
        using hp_pos_if_idx[OF hk] by (by100 simp)
      hence "u 0 \<in> ?UI"
        by (by100 blast)
      thus ?thesis
        using hSuc_eq htarget_closed by (by100 simp)
    qed
  qed
  have h\<psi>_suc:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow> \<psi> (v (Suc k)) = u (Suc k)"
  proof -
    fix k
    assume hk: "k \<in> {0..<p}"
    show "\<psi> (v (Suc k)) = u (Suc k)"
    proof (cases "Suc k < p")
      case True
      hence "Suc k \<in> {0..<p}"
        by (by100 simp)
      thus ?thesis
        using h\<psi>idx by (by100 blast)
    next
      case False
      have hSuc_eq: "Suc k = p"
        using hk False by (by100 simp)
      have h0: "0 \<in> {0..<p}"
        using hp_pos_if_idx[OF hk] by (by100 simp)
      have "\<psi> (v 0) = u 0"
        using h\<psi>idx h0 by (by100 blast)
      thus ?thesis
        using hSuc_eq hsource_closed htarget_closed by (by100 simp)
    qed
  qed
  have hforward:
      "\<And>W. W \<subseteq> ?VL \<Longrightarrow> geotop_convex_hull W \<in> L
        \<Longrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F"
  proof -
    fix W
    assume hWsub: "W \<subseteq> ?VL"
    assume hWL: "geotop_convex_hull W \<in> L"
    have hcases:
        "(\<exists>x\<in>?VI. W = {x})
        \<or> (\<exists>k\<in>{0..<p}. W = {v k, v (Suc k)})"
      by (rule hsource_cases[OF hWsub hWL])
    show "geotop_convex_hull (\<psi> ` W) \<in> F"
    proof (rule disjE[OF hcases])
      assume hsingle: "\<exists>x\<in>?VI. W = {x}"
      then obtain x where hxI: "x \<in> ?VI" and hW: "W = {x}"
        by (by100 blast)
      have hxVL: "x \<in> ?VL"
        using hxI hsource_vertices by (by100 simp)
      have h\<psi>xVF: "\<psi> x \<in> ?VF"
        using h\<psi>bij hxVL unfolding bij_betw_def by (by100 blast)
      have h\<psi>xI: "\<psi> x \<in> ?UI"
        using h\<psi>xVF htarget_vertices by (by100 simp)
      have himage: "\<psi> ` W = {\<psi> x}"
        using hW by (by100 simp)
      show ?thesis
        using htarget_single[OF h\<psi>xI] himage by (by100 simp)
    next
      assume hedge: "\<exists>k\<in>{0..<p}. W = {v k, v (Suc k)}"
      then obtain k where hk: "k \<in> {0..<p}"
          and hW: "W = {v k, v (Suc k)}"
        by (by100 blast)
      have h\<psi>k: "\<psi> (v k) = u k"
        using h\<psi>idx hk by (by100 blast)
      have h\<psi>Sk: "\<psi> (v (Suc k)) = u (Suc k)"
        by (rule h\<psi>_suc[OF hk])
      have himage: "\<psi> ` W = {u k, u (Suc k)}"
        using hW h\<psi>k h\<psi>Sk by (by100 simp)
      show ?thesis
        using htarget_edge[OF hk] himage by (by100 simp)
    qed
  qed
  have hreverse:
      "\<And>W. W \<subseteq> ?VL \<Longrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F
        \<Longrightarrow> geotop_convex_hull W \<in> L"
  proof -
    fix W
    assume hWsub: "W \<subseteq> ?VL"
    assume himageF: "geotop_convex_hull (\<psi> ` W) \<in> F"
    have himage_sub: "\<psi> ` W \<subseteq> ?VF"
      using h\<psi>bij hWsub unfolding bij_betw_def by (by100 blast)
    have hcases:
        "(\<exists>y\<in>?UI. \<psi> ` W = {y})
        \<or> (\<exists>k\<in>{0..<p}. \<psi> ` W = {u k, u (Suc k)})"
      by (rule htarget_cases[OF himage_sub himageF])
    show "geotop_convex_hull W \<in> L"
    proof (rule disjE[OF hcases])
      assume hsingle: "\<exists>y\<in>?UI. \<psi> ` W = {y}"
      then obtain y where hyI: "y \<in> ?UI" and himage: "\<psi> ` W = {y}"
        by (by100 blast)
      obtain x where hxW: "x \<in> W" and h\<psi>x: "\<psi> x = y"
        using himage by (by100 blast)
      have hxVL: "x \<in> ?VL"
        using hWsub hxW by (by100 blast)
      have hW_sub_x: "W \<subseteq> {x}"
      proof
        fix z
        assume hzW: "z \<in> W"
        have hzVL: "z \<in> ?VL"
          using hWsub hzW by (by100 blast)
        have "\<psi> z = y"
          using himage hzW by (by100 blast)
        hence "\<psi> z = \<psi> x"
          using h\<psi>x by (by100 simp)
        hence "z = x"
          by (rule inj_onD[OF h\<psi>inj _ hzVL hxVL])
        thus "z \<in> {x}"
          by (by100 simp)
      qed
      have hW_eq: "W = {x}"
        using hW_sub_x hxW by (by100 blast)
      have hxI: "x \<in> ?VI"
        using hxVL hsource_vertices by (by100 simp)
      show ?thesis
        using hsource_single[OF hxI] hW_eq by (by100 simp)
    next
      assume hedge: "\<exists>k\<in>{0..<p}. \<psi> ` W = {u k, u (Suc k)}"
      then obtain k where hk: "k \<in> {0..<p}"
          and himage: "\<psi> ` W = {u k, u (Suc k)}"
        by (by100 blast)
      have hvkI: "v k \<in> ?VI"
        using hk by (by100 blast)
      have hvSkI: "v (Suc k) \<in> ?VI"
        by (rule hsource_suc_in_image[OF hk])
      have hvkVL: "v k \<in> ?VL"
        using hvkI hsource_vertices by (by100 simp)
      have hvSkVL: "v (Suc k) \<in> ?VL"
        using hvSkI hsource_vertices by (by100 simp)
      have h\<psi>k: "\<psi> (v k) = u k"
        using h\<psi>idx hk by (by100 blast)
      have h\<psi>Sk: "\<psi> (v (Suc k)) = u (Suc k)"
        by (rule h\<psi>_suc[OF hk])
      have hW_nonempty: "W \<noteq> {}"
        using himage by (by100 blast)
      obtain x where hxW: "x \<in> W"
        using hW_nonempty by (by100 blast)
      have hW_sub_pair: "W \<subseteq> {v k, v (Suc k)}"
      proof
        fix z
        assume hzW: "z \<in> W"
        have hzVL: "z \<in> ?VL"
          using hWsub hzW by (by100 blast)
        have h\<psi>z_cases: "\<psi> z = u k \<or> \<psi> z = u (Suc k)"
          using himage hzW by (by100 blast)
        show "z \<in> {v k, v (Suc k)}"
        proof (rule disjE[OF h\<psi>z_cases])
          assume "\<psi> z = u k"
          hence "\<psi> z = \<psi> (v k)"
            using h\<psi>k by (by100 simp)
          hence "z = v k"
            by (rule inj_onD[OF h\<psi>inj _ hzVL hvkVL])
          thus ?thesis
            by (by100 simp)
        next
          assume "\<psi> z = u (Suc k)"
          hence "\<psi> z = \<psi> (v (Suc k))"
            using h\<psi>Sk by (by100 simp)
          hence "z = v (Suc k)"
            by (rule inj_onD[OF h\<psi>inj _ hzVL hvSkVL])
          thus ?thesis
            by (by100 simp)
        qed
      qed
      have hW_cases:
          "W = {v k} \<or> W = {v (Suc k)}
          \<or> W = {v k, v (Suc k)}"
        using hW_sub_pair hxW by (by100 blast)
      show ?thesis
      proof (rule disjE[OF hW_cases])
        assume hW: "W = {v k}"
        show ?thesis
          using hsource_single[OF hvkI] hW by (by100 simp)
      next
        assume htail:
            "W = {v (Suc k)} \<or> W = {v k, v (Suc k)}"
        show ?thesis
        proof (rule disjE[OF htail])
          assume hW: "W = {v (Suc k)}"
          show ?thesis
            using hsource_single[OF hvSkI] hW by (by100 simp)
        next
          assume hW: "W = {v k, v (Suc k)}"
          show ?thesis
            using hsource_edge[OF hk] hW by (by100 simp)
        qed
      qed
    qed
  qed
  have hcond:
      "\<forall>W. W \<subseteq> ?VL \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F)"
    using hforward hreverse by (by100 blast)
  show ?thesis
    unfolding geotop_isomorphism_def using h\<psi>bij hcond by (by100 blast)
qed

definition geotop_standard_boundary_cycle_listing_data_dev34 ::
  "(real^2) set \<Rightarrow> nat \<Rightarrow> (real^2) set set \<Rightarrow> (nat \<Rightarrow> real^2) \<Rightarrow> bool"
where
  "geotop_standard_boundary_cycle_listing_data_dev34 \<sigma> p F u \<longleftrightarrow>
    geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
    \<and> u p = u 0
    \<and> ((\<lambda>k. u k) ` {0..<p}) = geotop_complex_vertices F
    \<and> F =
      ((\<lambda>x. {x}) ` ((\<lambda>k. u k) ` {0..<p}))
      \<union> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
    \<and> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
      = {e\<in>F. geotop_is_edge e}
    \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices F
      \<longrightarrow> geotop_convex_hull W \<in> F
      \<longrightarrow> ((\<exists>x\<in>((\<lambda>k. u k) ` {0..<p}). W = {x})
        \<or> (\<exists>k\<in>{0..<p}. W = {u k, u (Suc k)})))
    \<and> (\<forall>x\<in>((\<lambda>k. u k) ` {0..<p}). geotop_convex_hull {x} \<in> F)
    \<and> (\<forall>k\<in>{0..<p}. geotop_convex_hull {u k, u (Suc k)} \<in> F)"

lemma geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34:
  fixes L :: "(real^2) set set" and v :: "nat \<Rightarrow> real^2"
    and \<sigma> :: "(real^2) set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hdegree_two:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hp_gt2: "2 < p"
  assumes hsource_vertices:
    "((\<lambda>k. v k) ` {0..<p}) = geotop_complex_vertices L"
  assumes hsource_closed: "v p = v 0"
  assumes hsource_listing_decomp:
    "L =
      ((\<lambda>x. {x}) ` ((\<lambda>k. v k) ` {0..<p}))
      \<union> ((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})"
  assumes hsource_edge_segments:
    "((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})
      = {e\<in>L. geotop_is_edge e}"
  assumes hsource_cases:
    "\<And>W. W \<subseteq> geotop_complex_vertices L
      \<Longrightarrow> geotop_convex_hull W \<in> L
      \<Longrightarrow> (\<exists>x\<in>((\<lambda>k. v k) ` {0..<p}). W = {x})
        \<or> (\<exists>k\<in>{0..<p}. W = {v k, v (Suc k)})"
  assumes hsource_single:
    "\<And>x. x \<in> ((\<lambda>k. v k) ` {0..<p})
      \<Longrightarrow> geotop_convex_hull {x} \<in> L"
  assumes hsource_edge:
    "\<And>k. k \<in> {0..<p}
      \<Longrightarrow> geotop_convex_hull {v k, v (Suc k)} \<in> L"
  assumes hsource_adjacent_distinct:
    "\<And>k. k \<in> {0..<p} \<Longrightarrow> v k \<noteq> v (Suc k)"
  shows "\<exists>F u \<psi>.
      geotop_standard_boundary_cycle_listing_data_dev34 \<sigma> p F u
      \<and> bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)
      \<and> (\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)"
  (**
    Moise Fig. 4.10 target realization in source normal form.  The remaining
    geometric construction is to put a cyclic subdivision on the boundary of a
    standard 2-simplex with exactly the quotient cyclic incidence of the source
    listing, allowing repeated indices in the given parametrization. **)
proof -
  let ?V = "((\<lambda>k. v k) ` {0..<p})"
  let ?E = "((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})"
  let ?B = "geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
  have hidx_finite: "finite {0..<p}"
    by (by100 simp)
  have hsource_vertices_finite: "finite (geotop_complex_vertices L)"
    using hsource_vertices hidx_finite by (by100 simp)
  have hp_pos: "0 < p"
    using hp_gt2 by (by100 linarith)
  have hsource_vertices_nonempty: "geotop_complex_vertices L \<noteq> {}"
  proof -
    have "0 \<in> {0..<p}"
      using hp_pos by (by100 simp)
    hence "v 0 \<in> ?V"
      by (by100 blast)
    thus ?thesis
      using hsource_vertices by (by100 blast)
  qed
  have hsource_edges_eq:
      "?E = {e\<in>L. geotop_is_edge e}"
    by (rule hsource_edge_segments)
  have hsource_listed_edges_finite: "finite ?E"
    by (rule finite_imageI[OF hidx_finite])
  have hsource_graph_edges_finite:
      "finite {e\<in>L. geotop_is_edge e}"
    using hsource_edges_eq hsource_listed_edges_finite by (by100 simp)
  have hsource_edges_card_le_p:
      "card {e\<in>L. geotop_is_edge e} \<le> p"
    using hsource_edges_eq card_image_le[OF hidx_finite,
      of "\<lambda>k. closed_segment (v k) (v (Suc k))"] by (by100 simp)
  have hsource_listed_edge_in_L:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow> closed_segment (v k) (v (Suc k)) \<in> L"
    using hsource_edges_eq by (by100 blast)
  have hsource_listed_edge_is_edge:
      "\<And>k. k \<in> {0..<p}
        \<Longrightarrow> geotop_is_edge (closed_segment (v k) (v (Suc k)))"
    using hsource_edges_eq by (by100 blast)
  have hsource_listed_edges_nonempty: "?E \<noteq> {}"
    using hp_pos by (by100 blast)
  have hsource_graph_edges_nonempty:
      "{e\<in>L. geotop_is_edge e} \<noteq> {}"
    using hsource_edges_eq hsource_listed_edges_nonempty by (by100 simp)
  have hsource_edges_card_pos:
      "0 < card {e\<in>L. geotop_is_edge e}"
    using hsource_graph_edges_finite hsource_graph_edges_nonempty by (by100 simp)
  have hB_complex:
      "geotop_is_complex ?B"
    by (rule geotop_2simplex_comb_boundary_is_complex_dev34[OF h\<sigma>])
  have hB_finite:
      "finite ?B"
    by (rule geotop_2simplex_comb_boundary_finite_dev34[OF h\<sigma>])
  have hB_edges_finite:
      "finite {e\<in>?B. geotop_is_edge e}"
    using hB_finite by (by100 simp)
  have hB_vertices_finite:
      "finite (geotop_complex_vertices ?B)"
    by (rule geotop_finite_complex_vertices_finite_dev34[OF hB_complex hB_finite])
  have hB_vertices_poly:
      "geotop_complex_vertices ?B \<subseteq> geotop_polyhedron ?B"
  proof
    fix x
    assume hx: "x \<in> geotop_complex_vertices ?B"
    have hx_single: "{x} \<in> ?B"
      using geotop_complex_vertices_eq_0_simplexes[OF hB_complex] hx by (by100 blast)
    show "x \<in> geotop_polyhedron ?B"
      unfolding geotop_polyhedron_def using hx_single by (by100 blast)
  qed
  have htarget_seed_subdivision:
      "\<exists>F. geotop_is_subdivision F ?B
        \<and> finite F
        \<and> (\<forall>x\<in>geotop_complex_vertices ?B. {x} \<in> F)
        \<and> (\<forall>v. {v} \<in> ?B \<longrightarrow> {v} \<in> F)"
    using geotop_2simplex_boundary_finite_points_subdivision_preserves_vertices_dev34
      [OF h\<sigma> hB_vertices_finite hB_vertices_poly]
    by (by100 blast)
  obtain F\<^sub>0 where hF\<^sub>0_sub: "geotop_is_subdivision F\<^sub>0 ?B"
      and hF\<^sub>0_finite: "finite F\<^sub>0"
      and hB_vertices_in_F\<^sub>0:
        "\<forall>x\<in>geotop_complex_vertices ?B. {x} \<in> F\<^sub>0"
      and hB_old_vertices_in_F\<^sub>0:
        "\<forall>v. {v} \<in> ?B \<longrightarrow> {v} \<in> F\<^sub>0"
    using htarget_seed_subdivision by (by100 blast)
  have hF\<^sub>0_complex: "geotop_is_complex F\<^sub>0"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hF\<^sub>0_sub])
  have hF\<^sub>0_vertices_finite:
      "finite (geotop_complex_vertices F\<^sub>0)"
    by (rule geotop_finite_complex_vertices_finite_dev34[OF hF\<^sub>0_complex hF\<^sub>0_finite])
  have hF\<^sub>0_edges_finite:
      "finite {e\<in>F\<^sub>0. geotop_is_edge e}"
    using hF\<^sub>0_finite by (by100 simp)
  show ?thesis
    sorry
qed

lemma geotop_standard_boundary_cycle_listing_data_with_source_bijection_dev34:
  fixes L :: "(real^2) set set" and v :: "nat \<Rightarrow> real^2"
    and \<sigma> :: "(real^2) set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hdegree_two:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hp_gt2: "2 < p"
  assumes hL_listing_decomp:
    "L =
      ((\<lambda>x. {x}) ` ((\<lambda>k. v k) ` {0..<p}))
      \<union> ((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})"
  assumes hedge_segments:
    "((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})
      = {e\<in>L. geotop_is_edge e}"
  assumes hvertices:
    "((\<lambda>k. v k) ` {0..<p}) = geotop_complex_vertices L"
  assumes hclosed_vertex: "v p = v 0"
  shows "\<exists>F u \<psi>.
      geotop_standard_boundary_cycle_listing_data_dev34 \<sigma> p F u
      \<and> bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)
      \<and> (\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)"
  (**
    Moise Fig. 4.10 source-to-target package: after constructing a cyclic
    subdivision of the standard boundary, choose the simplicial vertex bijection
    by matching the source and target cyclic listings position by position. **)
proof -
  let ?V = "((\<lambda>k. v k) ` {0..<p})"
  let ?E = "((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})"
  let ?B = "geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL_linear])
  have hL_1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_dev34[OF hL_linear])
  have hidx_finite: "finite {0..<p}"
    by (by100 simp)
  have hsource_vertices_finite: "finite (geotop_complex_vertices L)"
    using hvertices hidx_finite by (by100 simp)
  have hp_pos: "0 < p"
    using hp_gt2 by (by100 linarith)
  have hsource_vertices_nonempty: "geotop_complex_vertices L \<noteq> {}"
  proof -
    have "0 \<in> {0..<p}"
      using hp_pos by (by100 simp)
    hence "v 0 \<in> ?V"
      by (by100 blast)
    thus ?thesis
      using hvertices by (by100 blast)
  qed
  have hsource_singletons_subset_L: "((\<lambda>x. {x}) ` ?V) \<subseteq> L"
    using hL_listing_decomp by (by100 blast)
  have hsource_index_vertex:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow> v k \<in> geotop_complex_vertices L"
    using hvertices by (by100 blast)
  have hsource_closed_vertex_in_vertices:
      "v p \<in> geotop_complex_vertices L"
  proof -
    have "0 \<in> {0..<p}"
      using hp_pos by (by100 simp)
    hence "v 0 \<in> geotop_complex_vertices L"
      using hsource_index_vertex by (by100 blast)
    thus ?thesis
      using hclosed_vertex by (by100 simp)
  qed
  have hsource_singleton_image_finite: "finite ((\<lambda>x. {x}) ` ?V)"
    by (rule finite_imageI[OF finite_imageI[OF hidx_finite]])
  have hsource_vertex_singleton:
      "\<And>x. x \<in> geotop_complex_vertices L \<Longrightarrow> {x} \<in> L"
  proof -
    fix x
    assume hx: "x \<in> geotop_complex_vertices L"
    have "x \<in> ?V"
      using hx hvertices by (by100 blast)
    thus "{x} \<in> L"
      using hsource_singletons_subset_L by (by100 blast)
  qed
  have hL_nonempty: "L \<noteq> {}"
  proof -
    obtain x where hx: "x \<in> geotop_complex_vertices L"
      using hsource_vertices_nonempty by (by100 blast)
    have "{x} \<in> L"
      by (rule hsource_vertex_singleton[OF hx])
    thus ?thesis
      by (by100 blast)
  qed
  have hsource_edges_eq: "?E = {e\<in>L. geotop_is_edge e}"
    by (rule hedge_segments)
  have hsource_listed_edges_finite: "finite ?E"
    by (rule finite_imageI[OF hidx_finite])
  have hsource_edge_set_finite: "finite {e\<in>L. geotop_is_edge e}"
    using hsource_edges_eq hsource_listed_edges_finite by (by100 simp)
  have hsource_vertex_edge_decomp:
      "L =
        ((\<lambda>x. {x}) ` geotop_complex_vertices L)
        \<union> {e\<in>L. geotop_is_edge e}"
    using hL_listing_decomp hvertices hsource_edges_eq by (by100 simp)
  have hsource_member_cases:
      "\<And>\<tau>. \<tau> \<in> L \<Longrightarrow>
        \<tau> \<in> ((\<lambda>x. {x}) ` ?V) \<or> \<tau> \<in> ?E"
    using hL_listing_decomp by (by100 blast)
  have hsource_edge_listed_cases:
      "\<And>\<tau>. \<tau> \<in> L \<Longrightarrow> geotop_is_edge \<tau> \<Longrightarrow>
        \<exists>k\<in>{0..<p}. \<tau> = closed_segment (v k) (v (Suc k))"
    using hsource_edges_eq by (by100 blast)
  have hsource_edge_members:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        closed_segment (v k) (v (Suc k)) \<in> L
        \<and> geotop_is_edge (closed_segment (v k) (v (Suc k)))"
  proof -
    fix k
    assume hk: "k \<in> {0..<p}"
    have "closed_segment (v k) (v (Suc k)) \<in> ?E"
      using hk by (by100 blast)
    hence "closed_segment (v k) (v (Suc k)) \<in> {e\<in>L. geotop_is_edge e}"
      using hsource_edges_eq by (by100 simp)
    thus "closed_segment (v k) (v (Suc k)) \<in> L
        \<and> geotop_is_edge (closed_segment (v k) (v (Suc k)))"
      by (by100 blast)
  qed
  have hsource_edge_endpoints_distinct:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow> v k \<noteq> v (Suc k)"
  proof
    fix k
    assume hk: "k \<in> {0..<p}"
    assume heq: "v k = v (Suc k)"
    have hedge: "geotop_is_edge (closed_segment (v k) (v (Suc k)))"
      using hsource_edge_members[OF hk] by (by100 blast)
    have hdim0: "geotop_simplex_dim {v k} 0"
      by (rule geotop_singleton_is_simplex)
    have hdim1: "geotop_simplex_dim {v k} 1"
      using hedge heq unfolding geotop_is_edge_def by (by100 simp)
    have "0 = (1::nat)"
      by (rule geotop_simplex_dim_unique[OF hdim0 hdim1])
    thus False
      by (by100 linarith)
  qed
  have hsource_singleton_not_edge:
      "\<And>(x :: real^2). \<not> geotop_is_edge {x}"
  proof
    fix x :: "real^2"
    assume hedge: "geotop_is_edge {x}"
    have hdim0: "geotop_simplex_dim {x} 0"
      by (rule geotop_singleton_is_simplex[where P=x])
    have hdim1: "geotop_simplex_dim {x} 1"
      using hedge unfolding geotop_is_edge_def by (by100 simp)
    have "0 = (1::nat)"
      by (rule geotop_simplex_dim_unique[OF hdim0 hdim1])
    thus False
      by (by100 linarith)
  qed
  have hsource_nonedge_singleton_cases:
      "\<And>\<tau>. \<tau> \<in> L \<Longrightarrow> \<not> geotop_is_edge \<tau> \<Longrightarrow>
        \<exists>x\<in>?V. \<tau> = {x}"
    using hsource_member_cases hsource_edge_members hsource_singleton_not_edge
    by (by100 blast)
  have hsource_edge_simplex_vertices:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        geotop_simplex_vertices (closed_segment (v k) (v (Suc k)))
          {v k, v (Suc k)}"
    by (rule geotop_closed_segment_simplex_vertices[OF hsource_edge_endpoints_distinct])
  have hsource_edge_endpoints_vertices:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        v k \<in> geotop_complex_vertices L
        \<and> v (Suc k) \<in> geotop_complex_vertices L"
    using hsource_edge_members hsource_edge_simplex_vertices
    unfolding geotop_complex_vertices_def by (by100 blast)
  have hsource_successor_vertex_in_image:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow> v (Suc k) \<in> ?V"
    using hsource_edge_endpoints_vertices hvertices by (by100 blast)
  have hsource_singleton_convex_hull_in_L:
      "\<And>x. x \<in> geotop_complex_vertices L \<Longrightarrow>
        geotop_convex_hull {x} \<in> L"
  proof -
    fix x
    assume hx: "x \<in> geotop_complex_vertices L"
    have hxL: "{x} \<in> L"
      by (rule hsource_vertex_singleton[OF hx])
    have hhull: "geotop_convex_hull {x} = {x}"
      using geotop_convex_hull_eq_HOL[of "{x}"] by (by100 simp)
    show "geotop_convex_hull {x} \<in> L"
      using hxL hhull by (by100 simp)
  qed
  have hsource_edge_convex_hull_eq:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        geotop_convex_hull {v k, v (Suc k)}
          = closed_segment (v k) (v (Suc k))"
    using hsource_edge_simplex_vertices
    unfolding geotop_simplex_vertices_def by (by100 blast)
  have hsource_edge_convex_hull_in_L:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        geotop_convex_hull {v k, v (Suc k)} \<in> L"
    using hsource_edge_convex_hull_eq hsource_edge_members by (by100 simp)
  have hsource_convex_hull_nonedge_singleton_cases:
      "\<And>W. W \<noteq> {} \<Longrightarrow> geotop_convex_hull W \<in> L
        \<Longrightarrow> \<not> geotop_is_edge (geotop_convex_hull W)
        \<Longrightarrow> \<exists>x\<in>?V. W = {x}"
  proof -
    fix W :: "(real^2) set"
    assume hW_ne: "W \<noteq> {}"
    assume hWhull_L: "geotop_convex_hull W \<in> L"
    assume hnot_edge: "\<not> geotop_is_edge (geotop_convex_hull W)"
    obtain x where hxV: "x \<in> ?V" and hWhull_eq: "geotop_convex_hull W = {x}"
      using hsource_nonedge_singleton_cases[OF hWhull_L hnot_edge] by (by100 blast)
    have hW_sub_x: "W \<subseteq> {x}"
    proof
      fix y
      assume hyW: "y \<in> W"
      have hy_hull: "y \<in> geotop_convex_hull W"
        using geotop_convex_hull_contains_V hyW by (by100 blast)
      show "y \<in> {x}"
        using hy_hull hWhull_eq by (by100 simp)
    qed
    have hxW: "x \<in> W"
    proof -
      obtain y where hyW: "y \<in> W"
        using hW_ne by (by100 blast)
      have hy_single: "y \<in> {x}"
        using hW_sub_x hyW by (by100 blast)
      have hyx: "y = x"
        using hy_single by (by100 simp)
      show ?thesis
        using hyW hyx by (by100 simp)
    qed
    show "\<exists>x\<in>?V. W = {x}"
      using hxV hW_sub_x hxW by (by100 blast)
  qed
  have hsource_convex_hull_edge_listed_cases:
      "\<And>W. geotop_convex_hull W \<in> L
        \<Longrightarrow> geotop_is_edge (geotop_convex_hull W)
        \<Longrightarrow> \<exists>k\<in>{0..<p}.
          geotop_convex_hull W = closed_segment (v k) (v (Suc k))"
    using hsource_edge_listed_cases by (by100 blast)
  have hsource_convex_hull_member_cases:
      "\<And>W. W \<noteq> {} \<Longrightarrow> geotop_convex_hull W \<in> L
        \<Longrightarrow> (\<exists>x\<in>?V. W = {x})
          \<or> (\<exists>k\<in>{0..<p}.
              geotop_convex_hull W = closed_segment (v k) (v (Suc k)))"
    using hsource_convex_hull_nonedge_singleton_cases
      hsource_convex_hull_edge_listed_cases
    by (by100 blast)
  have hsource_listed_edge_complex_vertex_endpoint_cases:
      "\<And>x k. x \<in> ?V \<Longrightarrow> k \<in> {0..<p}
        \<Longrightarrow> x \<in> closed_segment (v k) (v (Suc k))
        \<Longrightarrow> x = v k \<or> x = v (Suc k)"
  proof -
    fix x k
    assume hxV: "x \<in> ?V"
    assume hk: "k \<in> {0..<p}"
    assume hxseg: "x \<in> closed_segment (v k) (v (Suc k))"
    have hxL: "{x} \<in> L"
      using hxV hvertices hsource_vertex_singleton by (by100 blast)
    have hsegL: "closed_segment (v k) (v (Suc k)) \<in> L"
      using hsource_edge_members[OF hk] by (by100 blast)
    have hmeet: "{x} \<inter> closed_segment (v k) (v (Suc k)) \<noteq> {}"
      using hxseg by (by100 blast)
    have hface_pair:
        "geotop_is_face ({x} \<inter> closed_segment (v k) (v (Suc k))) {x}
        \<and> geotop_is_face ({x} \<inter> closed_segment (v k) (v (Suc k)))
             (closed_segment (v k) (v (Suc k)))"
      using geotop_is_complex_intersection[OF hL_complex] hxL hsegL hmeet
      by (by100 blast)
    have hface_single:
        "geotop_is_face {x} (closed_segment (v k) (v (Suc k)))"
      using hface_pair hxseg by (by100 simp)
    have hface_cases:
        "{x} = {v k}
        \<or> {x} = {v (Suc k)}
        \<or> {x} = closed_segment (v k) (v (Suc k))"
      using geotop_segment_face_cases_dev34
        [OF hface_single hsource_edge_endpoints_distinct[OF hk]]
      by (by100 blast)
    show "x = v k \<or> x = v (Suc k)"
    proof (rule disjE[OF hface_cases])
      assume "{x} = {v k}"
      thus ?thesis
        by (by100 simp)
    next
      assume htail: "{x} = {v (Suc k)}
        \<or> {x} = closed_segment (v k) (v (Suc k))"
      show ?thesis
      proof (rule disjE[OF htail])
        assume "{x} = {v (Suc k)}"
        thus ?thesis
          by (by100 simp)
      next
        assume hself: "{x} = closed_segment (v k) (v (Suc k))"
        have hedge: "geotop_is_edge (closed_segment (v k) (v (Suc k)))"
          using hsource_edge_members[OF hk] by (by100 blast)
        have "geotop_is_edge {x}"
          using hedge hself by (by100 simp)
        thus ?thesis
          using hsource_singleton_not_edge by (by100 blast)
      qed
    qed
  qed
  have hsource_convex_hull_listed_edge_vertex_subset:
      "\<And>W k. W \<subseteq> geotop_complex_vertices L
        \<Longrightarrow> k \<in> {0..<p}
        \<Longrightarrow> geotop_convex_hull W = closed_segment (v k) (v (Suc k))
        \<Longrightarrow> W \<subseteq> {v k, v (Suc k)}"
  proof
    fix W k x
    assume hWsub: "W \<subseteq> geotop_complex_vertices L"
    assume hk: "k \<in> {0..<p}"
    assume hWhull:
        "geotop_convex_hull W = closed_segment (v k) (v (Suc k))"
    assume hxW: "x \<in> W"
    have hxV: "x \<in> ?V"
      using hWsub hxW hvertices by (by100 blast)
    have hx_hull: "x \<in> geotop_convex_hull W"
      using geotop_convex_hull_contains_V hxW by (by100 blast)
    have hx_seg: "x \<in> closed_segment (v k) (v (Suc k))"
      using hx_hull hWhull by (by100 simp)
    show "x \<in> {v k, v (Suc k)}"
      using hsource_listed_edge_complex_vertex_endpoint_cases[OF hxV hk hx_seg]
      by (by100 blast)
  qed
  have hsource_convex_hull_nonempty_pair_if_listed_edge:
      "\<And>W k. W \<noteq> {}
        \<Longrightarrow> W \<subseteq> geotop_complex_vertices L
        \<Longrightarrow> k \<in> {0..<p}
        \<Longrightarrow> geotop_convex_hull W = closed_segment (v k) (v (Suc k))
        \<Longrightarrow> W = {v k, v (Suc k)}"
  proof -
    fix W :: "(real^2) set" and k
    assume hW_ne: "W \<noteq> {}"
    assume hWsub: "W \<subseteq> geotop_complex_vertices L"
    assume hk: "k \<in> {0..<p}"
    assume hWhull:
        "geotop_convex_hull W = closed_segment (v k) (v (Suc k))"
    have hW_pair_sub: "W \<subseteq> {v k, v (Suc k)}"
      by (rule hsource_convex_hull_listed_edge_vertex_subset[OF hWsub hk hWhull])
    have hvk_in_W: "v k \<in> W"
    proof (rule ccontr)
      assume hvk_not: "v k \<notin> W"
      have hW_sub_suc: "W \<subseteq> {v (Suc k)}"
        using hW_pair_sub hvk_not by (by100 blast)
      have hHOL_sub: "convex hull W \<subseteq> convex hull {v (Suc k)}"
        by (rule hull_mono[OF hW_sub_suc])
      have hgeo_sub:
          "geotop_convex_hull W \<subseteq> geotop_convex_hull {v (Suc k)}"
        using hHOL_sub geotop_convex_hull_eq_HOL[of W]
          geotop_convex_hull_eq_HOL[of "{v (Suc k)}"] by (by100 simp)
      have hvk_seg: "v k \<in> closed_segment (v k) (v (Suc k))"
        by (by100 simp)
      have "v k \<in> geotop_convex_hull {v (Suc k)}"
        using hgeo_sub hWhull hvk_seg by (by100 blast)
      hence "v k = v (Suc k)"
        using geotop_convex_hull_eq_HOL[of "{v (Suc k)}"] by (by100 simp)
      thus False
        using hsource_edge_endpoints_distinct[OF hk] by (by100 blast)
    qed
    have hvsuc_in_W: "v (Suc k) \<in> W"
    proof (rule ccontr)
      assume hvsuc_not: "v (Suc k) \<notin> W"
      have hW_sub_k: "W \<subseteq> {v k}"
        using hW_pair_sub hvsuc_not by (by100 blast)
      have hHOL_sub: "convex hull W \<subseteq> convex hull {v k}"
        by (rule hull_mono[OF hW_sub_k])
      have hgeo_sub:
          "geotop_convex_hull W \<subseteq> geotop_convex_hull {v k}"
        using hHOL_sub geotop_convex_hull_eq_HOL[of W]
          geotop_convex_hull_eq_HOL[of "{v k}"] by (by100 simp)
      have hvsuc_seg: "v (Suc k) \<in> closed_segment (v k) (v (Suc k))"
        by (by100 simp)
      have "v (Suc k) \<in> geotop_convex_hull {v k}"
        using hgeo_sub hWhull hvsuc_seg by (by100 blast)
      hence "v (Suc k) = v k"
        using geotop_convex_hull_eq_HOL[of "{v k}"] by (by100 simp)
      hence "v k = v (Suc k)"
        by (by100 simp)
      thus False
        using hsource_edge_endpoints_distinct[OF hk] by (by100 blast)
    qed
    show "W = {v k, v (Suc k)}"
      using hW_pair_sub hvk_in_W hvsuc_in_W by (by100 blast)
  qed
  have hsource_cyclic_listing_convex_hull_in_L_cases:
      "\<And>W. W \<noteq> {} \<Longrightarrow> W \<subseteq> geotop_complex_vertices L
        \<Longrightarrow> geotop_convex_hull W \<in> L
        \<Longrightarrow> (\<exists>x\<in>?V. W = {x})
          \<or> (\<exists>k\<in>{0..<p}. W = {v k, v (Suc k)})"
  proof -
    fix W :: "(real^2) set"
    assume hW_ne: "W \<noteq> {}"
    assume hWsub: "W \<subseteq> geotop_complex_vertices L"
    assume hWhull_L: "geotop_convex_hull W \<in> L"
    have hcases:
        "(\<exists>x\<in>?V. W = {x})
        \<or> (\<exists>k\<in>{0..<p}.
            geotop_convex_hull W = closed_segment (v k) (v (Suc k)))"
      by (rule hsource_convex_hull_member_cases[OF hW_ne hWhull_L])
    show "(\<exists>x\<in>?V. W = {x})
        \<or> (\<exists>k\<in>{0..<p}. W = {v k, v (Suc k)})"
    proof (rule disjE[OF hcases])
      assume hsingle: "\<exists>x\<in>?V. W = {x}"
      show ?thesis
        using hsingle by (by100 blast)
    next
      assume hedge:
          "\<exists>k\<in>{0..<p}.
            geotop_convex_hull W = closed_segment (v k) (v (Suc k))"
      obtain k where hk: "k \<in> {0..<p}"
          and hWhull:
            "geotop_convex_hull W = closed_segment (v k) (v (Suc k))"
        using hedge by (by100 blast)
      have hW_pair: "W = {v k, v (Suc k)}"
        by (rule hsource_convex_hull_nonempty_pair_if_listed_edge
            [OF hW_ne hWsub hk hWhull])
      show ?thesis
        using hk hW_pair by (by100 blast)
    qed
  qed
  have hsource_empty_not_edge:
      "\<not> geotop_is_edge ({} :: (real^2) set)"
  proof
    assume hedge: "geotop_is_edge ({} :: (real^2) set)"
    have hdim: "geotop_simplex_dim ({} :: (real^2) set) 1"
      using hedge unfolding geotop_is_edge_def by (by100 blast)
    have hsimplex: "geotop_is_simplex ({} :: (real^2) set)"
      by (rule geotop_simplex_dim_imp_is_simplex[OF hdim])
    show False
      using geotop_is_simplex_nonempty[OF hsimplex] by (by100 simp)
  qed
  have hsource_convex_hull_empty_notin_L:
      "geotop_convex_hull ({} :: (real^2) set) \<notin> L"
  proof
    assume hempty_hull_L: "geotop_convex_hull ({} :: (real^2) set) \<in> L"
    have hhullempty: "geotop_convex_hull ({} :: (real^2) set) = {}"
      using geotop_convex_hull_eq_HOL[of "({} :: (real^2) set)"]
      by (by100 simp)
    have hempty_L: "({} :: (real^2) set) \<in> L"
      using hempty_hull_L hhullempty by (by100 simp)
    have hcases: "({} :: (real^2) set) \<in> ((\<lambda>x. {x}) ` ?V)
        \<or> ({} :: (real^2) set) \<in> ?E"
      using hsource_member_cases[OF hempty_L] by (by100 blast)
    have hnot_singleton_image:
        "({} :: (real^2) set) \<notin> ((\<lambda>x. {x}) ` ?V)"
      by (by100 blast)
    show False
      using hcases hnot_singleton_image hsource_edge_members hsource_empty_not_edge
      by (by100 blast)
  qed
  have hsource_cyclic_listing_convex_hull_in_L_cases_all:
      "\<And>W. W \<subseteq> geotop_complex_vertices L
        \<Longrightarrow> geotop_convex_hull W \<in> L
        \<Longrightarrow> (\<exists>x\<in>?V. W = {x})
          \<or> (\<exists>k\<in>{0..<p}. W = {v k, v (Suc k)})"
  proof -
    fix W
    assume hWsub: "W \<subseteq> geotop_complex_vertices L"
    assume hWhull_L: "geotop_convex_hull W \<in> L"
    show "(\<exists>x\<in>?V. W = {x})
        \<or> (\<exists>k\<in>{0..<p}. W = {v k, v (Suc k)})"
    proof (cases "W = {}")
      case True
      show ?thesis
        using hWhull_L hsource_convex_hull_empty_notin_L True by (by100 simp)
    next
      case False
      show ?thesis
        by (rule hsource_cyclic_listing_convex_hull_in_L_cases
            [OF False hWsub hWhull_L])
    qed
  qed
  have hB_complex:
      "geotop_is_complex ?B"
    by (rule geotop_2simplex_comb_boundary_is_complex_dev34[OF h\<sigma>])
  have hB_finite:
      "finite ?B"
    by (rule geotop_2simplex_comb_boundary_finite_dev34[OF h\<sigma>])
  have hB_vertices_finite:
      "finite (geotop_complex_vertices ?B)"
    by (rule geotop_finite_complex_vertices_finite_dev34[OF hB_complex hB_finite])
  have hB_vertices_poly:
      "geotop_complex_vertices ?B \<subseteq> geotop_polyhedron ?B"
  proof
    fix x
    assume hx: "x \<in> geotop_complex_vertices ?B"
    have hx_single: "{x} \<in> ?B"
      using geotop_complex_vertices_eq_0_simplexes[OF hB_complex] hx by (by100 blast)
    show "x \<in> geotop_polyhedron ?B"
      unfolding geotop_polyhedron_def using hx_single by (by100 blast)
  qed
  have htarget_seed_subdivision:
      "\<exists>F. geotop_is_subdivision F ?B
        \<and> finite F
        \<and> (\<forall>x\<in>geotop_complex_vertices ?B. {x} \<in> F)
        \<and> (\<forall>v. {v} \<in> ?B \<longrightarrow> {v} \<in> F)"
    using geotop_2simplex_boundary_finite_points_subdivision_preserves_vertices_dev34
      [OF h\<sigma> hB_vertices_finite hB_vertices_poly]
    by (by100 blast)
  obtain F\<^sub>0 where hF\<^sub>0_sub: "geotop_is_subdivision F\<^sub>0 ?B"
      and hF\<^sub>0_finite: "finite F\<^sub>0"
      and hB_vertices_in_F\<^sub>0:
        "\<forall>x\<in>geotop_complex_vertices ?B. {x} \<in> F\<^sub>0"
      and hB_old_vertices_in_F\<^sub>0:
        "\<forall>v. {v} \<in> ?B \<longrightarrow> {v} \<in> F\<^sub>0"
    using htarget_seed_subdivision by (by100 blast)
  have hF\<^sub>0_complex: "geotop_is_complex F\<^sub>0"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hF\<^sub>0_sub])
  have hF\<^sub>0_vertices_finite:
      "finite (geotop_complex_vertices F\<^sub>0)"
    by (rule geotop_finite_complex_vertices_finite_dev34[OF hF\<^sub>0_complex hF\<^sub>0_finite])
  have hsource_singleton_convex_hull_in_L_image:
      "\<And>x. x \<in> ?V \<Longrightarrow> geotop_convex_hull {x} \<in> L"
    using hsource_singleton_convex_hull_in_L hvertices by (by100 blast)
  show ?thesis
    by (rule geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34
        [OF hL_linear hL_finite hdegree_two h\<sigma> hp_gt2 hvertices hclosed_vertex
          hL_listing_decomp hedge_segments
          hsource_cyclic_listing_convex_hull_in_L_cases_all
          hsource_singleton_convex_hull_in_L_image
          hsource_edge_convex_hull_in_L
          hsource_edge_endpoints_distinct])
qed

lemma geotop_standard_2simplex_boundary_cyclic_target_data_dev34:
  fixes L :: "(real^2) set set" and v :: "nat \<Rightarrow> real^2"
    and \<sigma> :: "(real^2) set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hdegree_two:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hp_gt2: "2 < p"
  assumes hL_listing_decomp:
    "L =
      ((\<lambda>x. {x}) ` ((\<lambda>k. v k) ` {0..<p}))
      \<union> ((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})"
  assumes hedge_segments:
    "((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})
      = {e\<in>L. geotop_is_edge e}"
  assumes hvertices:
    "((\<lambda>k. v k) ` {0..<p}) = geotop_complex_vertices L"
  assumes hclosed_vertex: "v p = v 0"
  shows "\<exists>F u \<psi>.
      geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> u p = u 0
      \<and> ((\<lambda>k. u k) ` {0..<p}) = geotop_complex_vertices F
      \<and> F =
        ((\<lambda>x. {x}) ` ((\<lambda>k. u k) ` {0..<p}))
        \<union> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
      \<and> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
        = {e\<in>F. geotop_is_edge e}
      \<and> bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)
      \<and> (\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices F
        \<longrightarrow> geotop_convex_hull W \<in> F
        \<longrightarrow> ((\<exists>x\<in>((\<lambda>k. u k) ` {0..<p}). W = {x})
          \<or> (\<exists>k\<in>{0..<p}. W = {u k, u (Suc k)})))
      \<and> (\<forall>x\<in>((\<lambda>k. u k) ` {0..<p}). geotop_convex_hull {x} \<in> F)
      \<and> (\<forall>k\<in>{0..<p}. geotop_convex_hull {u k, u (Suc k)} \<in> F)"
  (**
    Moise Fig. 4.10 target construction: subdivide the boundary of the given
    2-simplex into a cyclic 1-complex matching the already listed source cycle,
    then define the vertex bijection by corresponding cyclic positions. **)
proof -
  obtain F u \<psi> where htarget:
      "geotop_standard_boundary_cycle_listing_data_dev34 \<sigma> p F u"
      and h\<psi>bij:
      "bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)"
      and h\<psi>idx:
      "\<forall>k\<in>{0..<p}. \<psi> (v k) = u k"
    using geotop_standard_boundary_cycle_listing_data_with_source_bijection_dev34
      [OF hL_linear hL_finite hdegree_two h\<sigma> hp_gt2 hL_listing_decomp
        hedge_segments hvertices hclosed_vertex]
    by (by100 blast)
  show ?thesis
    using htarget h\<psi>bij h\<psi>idx
    unfolding geotop_standard_boundary_cycle_listing_data_dev34_def
    by (by100 blast)
qed

lemma geotop_cyclic_listing_standard_boundary_cycle_target_model_dev34:
  fixes L :: "(real^2) set set" and v :: "nat \<Rightarrow> real^2"
    and \<sigma> :: "(real^2) set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hdegree_two:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hp_gt2: "2 < p"
  assumes hL_listing_decomp:
    "L =
      ((\<lambda>x. {x}) ` ((\<lambda>k. v k) ` {0..<p}))
      \<union> ((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})"
  assumes hedge_segments:
    "((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})
      = {e\<in>L. geotop_is_edge e}"
  assumes hvertices:
    "((\<lambda>k. v k) ` {0..<p}) = geotop_complex_vertices L"
  assumes hclosed_vertex: "v p = v 0"
  assumes hsource_cases:
    "\<And>W. W \<subseteq> geotop_complex_vertices L
      \<Longrightarrow> geotop_convex_hull W \<in> L
      \<Longrightarrow> (\<exists>x\<in>((\<lambda>k. v k) ` {0..<p}). W = {x})
        \<or> (\<exists>k\<in>{0..<p}. W = {v k, v (Suc k)})"
  shows "(\<exists>F \<psi>.
      geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> geotop_isomorphism L F \<psi>)
    \<and> (\<exists>F u \<psi>.
      geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> u p = u 0
      \<and> ((\<lambda>k. u k) ` {0..<p}) = geotop_complex_vertices F
      \<and> F =
        ((\<lambda>x. {x}) ` ((\<lambda>k. u k) ` {0..<p}))
        \<union> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
      \<and> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
        = {e\<in>F. geotop_is_edge e}
      \<and> bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)
      \<and> (\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)
      \<and> geotop_isomorphism L F \<psi>)"
  (**
    Precise Moise Fig. 4.10 target package.  The source graph is already in
    cyclic singleton/adjacent-edge normal form; the remaining book step is to
    build the matching cyclic subdivision of the frontier of a standard
    2-simplex and define the vertex map by the two cyclic parametrizations.
    Injectivity of the index parametrization belongs to the upstream orbit
    package when the graph cycle is known to be listed without repeats. **)
proof -
  let ?B = "geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
  let ?VI = "((\<lambda>k. v k) ` {0..<p})"
  have hsource_single:
      "\<And>x. x \<in> ?VI \<Longrightarrow> geotop_convex_hull {x} \<in> L"
  proof -
    fix x
    assume hx: "x \<in> ?VI"
    have hxL: "{x} \<in> L"
      using hx hL_listing_decomp by (by100 blast)
    have hhull: "geotop_convex_hull {x} = {x}"
      using geotop_convex_hull_eq_HOL[of "{x}"] by (by100 simp)
    show "geotop_convex_hull {x} \<in> L"
      using hxL hhull by (by100 simp)
  qed
  have hlisted_edge_members:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        closed_segment (v k) (v (Suc k)) \<in> L
        \<and> geotop_is_edge (closed_segment (v k) (v (Suc k)))"
  proof -
    fix k
    assume hk: "k \<in> {0..<p}"
    have "closed_segment (v k) (v (Suc k))
        \<in> ((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})"
      using hk by (by100 blast)
    hence "closed_segment (v k) (v (Suc k)) \<in> {e\<in>L. geotop_is_edge e}"
      using hedge_segments by (by100 simp)
    thus "closed_segment (v k) (v (Suc k)) \<in> L
        \<and> geotop_is_edge (closed_segment (v k) (v (Suc k)))"
      by (by100 blast)
  qed
  have hlisted_edge_endpoints_distinct:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow> v k \<noteq> v (Suc k)"
  proof
    fix k
    assume hk: "k \<in> {0..<p}"
    assume heq: "v k = v (Suc k)"
    have hedge: "geotop_is_edge (closed_segment (v k) (v (Suc k)))"
      using hlisted_edge_members[OF hk] by (by100 blast)
    have hdim0: "geotop_simplex_dim {v k} 0"
      by (rule geotop_singleton_is_simplex)
    have hdim1: "geotop_simplex_dim {v k} 1"
      using hedge heq unfolding geotop_is_edge_def by (by100 simp)
    have "0 = (1::nat)"
      by (rule geotop_simplex_dim_unique[OF hdim0 hdim1])
    thus False
      by (by100 linarith)
  qed
  have hlisted_edge_simplex_vertices:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        geotop_simplex_vertices (closed_segment (v k) (v (Suc k)))
          {v k, v (Suc k)}"
    by (rule geotop_closed_segment_simplex_vertices[OF hlisted_edge_endpoints_distinct])
  have hlisted_edge_convex_hull_eq:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        geotop_convex_hull {v k, v (Suc k)}
          = closed_segment (v k) (v (Suc k))"
    using hlisted_edge_simplex_vertices
    unfolding geotop_simplex_vertices_def by (by100 blast)
  have hsource_edge:
      "\<And>k. k \<in> {0..<p}
        \<Longrightarrow> geotop_convex_hull {v k, v (Suc k)} \<in> L"
    using hlisted_edge_convex_hull_eq hlisted_edge_members by (by100 simp)
  let ?target_data = "\<lambda>F u \<psi>.
        geotop_is_subdivision F ?B
        \<and> u p = u 0
        \<and> ((\<lambda>k. u k) ` {0..<p}) = geotop_complex_vertices F
        \<and> F =
          ((\<lambda>x. {x}) ` ((\<lambda>k. u k) ` {0..<p}))
          \<union> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
        \<and> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
          = {e\<in>F. geotop_is_edge e}
        \<and> bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)
        \<and> (\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)
        \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices F
          \<longrightarrow> geotop_convex_hull W \<in> F
          \<longrightarrow> ((\<exists>x\<in>((\<lambda>k. u k) ` {0..<p}). W = {x})
            \<or> (\<exists>k\<in>{0..<p}. W = {u k, u (Suc k)})))
        \<and> (\<forall>x\<in>((\<lambda>k. u k) ` {0..<p}). geotop_convex_hull {x} \<in> F)
        \<and> (\<forall>k\<in>{0..<p}. geotop_convex_hull {u k, u (Suc k)} \<in> F)"
  have htarget_boundary_cycle_data:
      "\<exists>F u \<psi>. ?target_data F u \<psi>"
    by (rule geotop_standard_2simplex_boundary_cyclic_target_data_dev34
        [OF hL_linear hL_finite hdegree_two h\<sigma> hp_gt2 hL_listing_decomp
          hedge_segments hvertices hclosed_vertex])
  obtain F u \<psi> where htarget_data: "?target_data F u \<psi>"
    using htarget_boundary_cycle_data by (elim exE)
  have hF_sub: "geotop_is_subdivision F ?B"
    by (rule conjunct1[OF htarget_data])
  have htarget_data1:
      "u p = u 0
        \<and> ((\<lambda>k. u k) ` {0..<p}) = geotop_complex_vertices F
        \<and> F =
          ((\<lambda>x. {x}) ` ((\<lambda>k. u k) ` {0..<p}))
          \<union> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
        \<and> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
          = {e\<in>F. geotop_is_edge e}
        \<and> bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)
        \<and> (\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)
        \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices F
          \<longrightarrow> geotop_convex_hull W \<in> F
          \<longrightarrow> ((\<exists>x\<in>((\<lambda>k. u k) ` {0..<p}). W = {x})
            \<or> (\<exists>k\<in>{0..<p}. W = {u k, u (Suc k)})))
        \<and> (\<forall>x\<in>((\<lambda>k. u k) ` {0..<p}). geotop_convex_hull {x} \<in> F)
        \<and> (\<forall>k\<in>{0..<p}. geotop_convex_hull {u k, u (Suc k)} \<in> F)"
    by (rule conjunct2[OF htarget_data])
  have hu_closed: "u p = u 0"
    by (rule conjunct1[OF htarget_data1])
  have htarget_data2:
      "((\<lambda>k. u k) ` {0..<p}) = geotop_complex_vertices F
        \<and> F =
          ((\<lambda>x. {x}) ` ((\<lambda>k. u k) ` {0..<p}))
          \<union> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
        \<and> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
          = {e\<in>F. geotop_is_edge e}
        \<and> bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)
        \<and> (\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)
        \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices F
          \<longrightarrow> geotop_convex_hull W \<in> F
          \<longrightarrow> ((\<exists>x\<in>((\<lambda>k. u k) ` {0..<p}). W = {x})
            \<or> (\<exists>k\<in>{0..<p}. W = {u k, u (Suc k)})))
        \<and> (\<forall>x\<in>((\<lambda>k. u k) ` {0..<p}). geotop_convex_hull {x} \<in> F)
        \<and> (\<forall>k\<in>{0..<p}. geotop_convex_hull {u k, u (Suc k)} \<in> F)"
    by (rule conjunct2[OF htarget_data1])
  have htarget_vertices:
      "((\<lambda>k. u k) ` {0..<p}) = geotop_complex_vertices F"
    by (rule conjunct1[OF htarget_data2])
  have htarget_data3:
      "F =
        ((\<lambda>x. {x}) ` ((\<lambda>k. u k) ` {0..<p}))
        \<union> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
        \<and> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
          = {e\<in>F. geotop_is_edge e}
        \<and> bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)
        \<and> (\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)
        \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices F
          \<longrightarrow> geotop_convex_hull W \<in> F
          \<longrightarrow> ((\<exists>x\<in>((\<lambda>k. u k) ` {0..<p}). W = {x})
            \<or> (\<exists>k\<in>{0..<p}. W = {u k, u (Suc k)})))
        \<and> (\<forall>x\<in>((\<lambda>k. u k) ` {0..<p}). geotop_convex_hull {x} \<in> F)
        \<and> (\<forall>k\<in>{0..<p}. geotop_convex_hull {u k, u (Suc k)} \<in> F)"
    by (rule conjunct2[OF htarget_data2])
  have hF_decomp:
      "F =
        ((\<lambda>x. {x}) ` ((\<lambda>k. u k) ` {0..<p}))
        \<union> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})"
    by (rule conjunct1[OF htarget_data3])
  have htarget_data4:
      "((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
          = {e\<in>F. geotop_is_edge e}
        \<and> bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)
        \<and> (\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)
        \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices F
          \<longrightarrow> geotop_convex_hull W \<in> F
          \<longrightarrow> ((\<exists>x\<in>((\<lambda>k. u k) ` {0..<p}). W = {x})
            \<or> (\<exists>k\<in>{0..<p}. W = {u k, u (Suc k)})))
        \<and> (\<forall>x\<in>((\<lambda>k. u k) ` {0..<p}). geotop_convex_hull {x} \<in> F)
        \<and> (\<forall>k\<in>{0..<p}. geotop_convex_hull {u k, u (Suc k)} \<in> F)"
    by (rule conjunct2[OF htarget_data3])
  have htarget_edges:
      "((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
        = {e\<in>F. geotop_is_edge e}"
    by (rule conjunct1[OF htarget_data4])
  have htarget_data5:
      "bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)
        \<and> (\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)
        \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices F
          \<longrightarrow> geotop_convex_hull W \<in> F
          \<longrightarrow> ((\<exists>x\<in>((\<lambda>k. u k) ` {0..<p}). W = {x})
            \<or> (\<exists>k\<in>{0..<p}. W = {u k, u (Suc k)})))
        \<and> (\<forall>x\<in>((\<lambda>k. u k) ` {0..<p}). geotop_convex_hull {x} \<in> F)
        \<and> (\<forall>k\<in>{0..<p}. geotop_convex_hull {u k, u (Suc k)} \<in> F)"
    by (rule conjunct2[OF htarget_data4])
  have h\<psi>bij: "bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)"
    by (rule conjunct1[OF htarget_data5])
  have htarget_data6:
      "(\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)
        \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices F
          \<longrightarrow> geotop_convex_hull W \<in> F
          \<longrightarrow> ((\<exists>x\<in>((\<lambda>k. u k) ` {0..<p}). W = {x})
            \<or> (\<exists>k\<in>{0..<p}. W = {u k, u (Suc k)})))
        \<and> (\<forall>x\<in>((\<lambda>k. u k) ` {0..<p}). geotop_convex_hull {x} \<in> F)
        \<and> (\<forall>k\<in>{0..<p}. geotop_convex_hull {u k, u (Suc k)} \<in> F)"
    by (rule conjunct2[OF htarget_data5])
  have h\<psi>idx: "\<forall>k\<in>{0..<p}. \<psi> (v k) = u k"
    by (rule conjunct1[OF htarget_data6])
  have htarget_data7:
      "(\<forall>W. W \<subseteq> geotop_complex_vertices F
          \<longrightarrow> geotop_convex_hull W \<in> F
          \<longrightarrow> ((\<exists>x\<in>((\<lambda>k. u k) ` {0..<p}). W = {x})
            \<or> (\<exists>k\<in>{0..<p}. W = {u k, u (Suc k)})))
        \<and> (\<forall>x\<in>((\<lambda>k. u k) ` {0..<p}). geotop_convex_hull {x} \<in> F)
        \<and> (\<forall>k\<in>{0..<p}. geotop_convex_hull {u k, u (Suc k)} \<in> F)"
    by (rule conjunct2[OF htarget_data6])
  have htarget_cases:
      "\<forall>W. W \<subseteq> geotop_complex_vertices F
        \<longrightarrow> geotop_convex_hull W \<in> F
        \<longrightarrow> ((\<exists>x\<in>((\<lambda>k. u k) ` {0..<p}). W = {x})
          \<or> (\<exists>k\<in>{0..<p}. W = {u k, u (Suc k)}))"
    by (rule conjunct1[OF htarget_data7])
  have htarget_data8:
      "(\<forall>x\<in>((\<lambda>k. u k) ` {0..<p}). geotop_convex_hull {x} \<in> F)
        \<and> (\<forall>k\<in>{0..<p}. geotop_convex_hull {u k, u (Suc k)} \<in> F)"
    by (rule conjunct2[OF htarget_data7])
  have htarget_single:
      "\<forall>x\<in>((\<lambda>k. u k) ` {0..<p}). geotop_convex_hull {x} \<in> F"
    by (rule conjunct1[OF htarget_data8])
  have htarget_edge:
      "\<forall>k\<in>{0..<p}. geotop_convex_hull {u k, u (Suc k)} \<in> F"
    by (rule conjunct2[OF htarget_data8])
  have hLF_iso: "geotop_isomorphism L F \<psi>"
  proof (rule geotop_cyclic_listing_isomorphism_from_matching_cases_dev34
      [OF hvertices htarget_vertices hclosed_vertex hu_closed h\<psi>bij h\<psi>idx
        hsource_cases hsource_single hsource_edge])
    fix W
    assume "W \<subseteq> geotop_complex_vertices F"
      and "geotop_convex_hull W \<in> F"
    thus "(\<exists>x\<in>((\<lambda>k. u k) ` {0..<p}). W = {x})
      \<or> (\<exists>k\<in>{0..<p}. W = {u k, u (Suc k)})"
      using htarget_cases by (by100 blast)
  next
    fix x
    assume "x \<in> ((\<lambda>k. u k) ` {0..<p})"
    thus "geotop_convex_hull {x} \<in> F"
      using htarget_single by (by100 blast)
  next
    fix k
    assume "k \<in> {0..<p}"
    thus "geotop_convex_hull {u k, u (Suc k)} \<in> F"
      using htarget_edge by (by100 blast)
  qed
  show ?thesis
  proof
    show "\<exists>F \<psi>. geotop_is_subdivision F ?B \<and> geotop_isomorphism L F \<psi>"
    proof (rule exI[where x=F])
      show "\<exists>\<psi>. geotop_is_subdivision F ?B \<and> geotop_isomorphism L F \<psi>"
      proof (rule exI[where x=\<psi>])
        show "geotop_is_subdivision F ?B \<and> geotop_isomorphism L F \<psi>"
        proof
          show "geotop_is_subdivision F ?B"
            by (rule hF_sub)
          show "geotop_isomorphism L F \<psi>"
            by (rule hLF_iso)
        qed
      qed
    qed
    show "\<exists>F u \<psi>.
        geotop_is_subdivision F ?B
        \<and> u p = u 0
        \<and> ((\<lambda>k. u k) ` {0..<p}) = geotop_complex_vertices F
        \<and> F =
          ((\<lambda>x. {x}) ` ((\<lambda>k. u k) ` {0..<p}))
          \<union> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
        \<and> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
          = {e\<in>F. geotop_is_edge e}
        \<and> bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)
        \<and> (\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)
        \<and> geotop_isomorphism L F \<psi>"
    proof (rule exI[where x=F])
      show "\<exists>u \<psi>.
        geotop_is_subdivision F ?B
        \<and> u p = u 0
        \<and> ((\<lambda>k. u k) ` {0..<p}) = geotop_complex_vertices F
        \<and> F =
          ((\<lambda>x. {x}) ` ((\<lambda>k. u k) ` {0..<p}))
          \<union> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
        \<and> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
          = {e\<in>F. geotop_is_edge e}
        \<and> bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)
        \<and> (\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)
        \<and> geotop_isomorphism L F \<psi>"
      proof (rule exI[where x=u])
        show "\<exists>\<psi>.
          geotop_is_subdivision F ?B
          \<and> u p = u 0
          \<and> ((\<lambda>k. u k) ` {0..<p}) = geotop_complex_vertices F
          \<and> F =
            ((\<lambda>x. {x}) ` ((\<lambda>k. u k) ` {0..<p}))
            \<union> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
          \<and> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
            = {e\<in>F. geotop_is_edge e}
          \<and> bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)
          \<and> (\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)
          \<and> geotop_isomorphism L F \<psi>"
        proof (rule exI[where x=\<psi>])
          show "geotop_is_subdivision F ?B
            \<and> u p = u 0
            \<and> ((\<lambda>k. u k) ` {0..<p}) = geotop_complex_vertices F
            \<and> F =
              ((\<lambda>x. {x}) ` ((\<lambda>k. u k) ` {0..<p}))
              \<union> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
            \<and> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
              = {e\<in>F. geotop_is_edge e}
            \<and> bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)
            \<and> (\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)
            \<and> geotop_isomorphism L F \<psi>"
          proof (intro conjI)
            show "geotop_is_subdivision F ?B"
              by (rule hF_sub)
            show "u p = u 0"
              by (rule hu_closed)
            show "((\<lambda>k. u k) ` {0..<p}) = geotop_complex_vertices F"
              by (rule htarget_vertices)
            show "F =
              ((\<lambda>x. {x}) ` ((\<lambda>k. u k) ` {0..<p}))
              \<union> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})"
              by (rule hF_decomp)
            show "((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
              = {e \<in> F. geotop_is_edge e}"
              by (rule htarget_edges)
            show "bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)"
              by (rule h\<psi>bij)
            show "\<forall>k\<in>{0..<p}. \<psi> (v k) = u k"
              by (rule h\<psi>idx)
            show "geotop_isomorphism L F \<psi>"
              by (rule hLF_iso)
          qed
        qed
      qed
    qed
  qed
qed

lemma geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34:
  fixes L :: "(real^2) set set" and v :: "nat \<Rightarrow> real^2"
    and \<sigma> :: "(real^2) set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hdegree_two:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hp_gt2: "2 < p"
  assumes hL_listing_decomp:
    "L =
      ((\<lambda>x. {x}) ` ((\<lambda>k. v k) ` {0..<p}))
      \<union> ((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})"
  assumes hedge_segments:
    "((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})
      = {e\<in>L. geotop_is_edge e}"
  assumes hvertices:
    "((\<lambda>k. v k) ` {0..<p}) = geotop_complex_vertices L"
  assumes hclosed_vertex: "v p = v 0"
  shows "\<exists>F \<psi>.
      geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> geotop_isomorphism L F \<psi>"
  (**
    Moise Fig. 4.10, boundary-cycle construction package.  After the finite
    graph has been put in cyclic order, subdivide the three boundary edges of
    one 2-simplex so that the resulting frontier complex has the same edge
    set cardinality and cyclic incidence as \<open>L\<close>, then send listed vertices of
    \<open>L\<close> to the corresponding boundary subdivision vertices. **)
proof -
  let ?V = "(\<lambda>k. v k) ` {0..<p}"
  let ?E = "(\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p}"
  let ?B = "geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL_linear])
  have hL_1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_dev34[OF hL_linear])
  have hidx_fin: "finite {0..<p}"
    by (by100 simp)
  have hV_fin: "finite ?V"
    by (rule finite_imageI[OF hidx_fin])
  have hE_fin: "finite ?E"
    by (rule finite_imageI[OF hidx_fin])
  have hV_eq_complex_vertices: "?V = geotop_complex_vertices L"
    by (rule hvertices)
  have hp_pos: "0 < p"
    using hp_gt2 by (by100 linarith)
  have hV_singletons_subset_L: "((\<lambda>x. {x}) ` ?V) \<subseteq> L"
    using hL_listing_decomp by (by100 blast)
  have hE_eq_edges: "?E = {e\<in>L. geotop_is_edge e}"
    by (rule hedge_segments)
  have hE_subset_L: "?E \<subseteq> L"
    using hE_eq_edges by (by100 blast)
  have hE_edges: "\<And>e. e \<in> ?E \<Longrightarrow> geotop_is_edge e"
    using hE_eq_edges by (by100 blast)
  have hlisted_edge_members:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        closed_segment (v k) (v (Suc k)) \<in> L
        \<and> geotop_is_edge (closed_segment (v k) (v (Suc k)))"
  proof -
    fix k
    assume hk: "k \<in> {0..<p}"
    have hsegE: "closed_segment (v k) (v (Suc k)) \<in> ?E"
      using hk by (by100 blast)
    show "closed_segment (v k) (v (Suc k)) \<in> L
        \<and> geotop_is_edge (closed_segment (v k) (v (Suc k)))"
      using hsegE hE_subset_L hE_edges by (by100 blast)
  qed
  have hlisted_edge_dim:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        geotop_simplex_dim (closed_segment (v k) (v (Suc k))) 1"
    using hlisted_edge_members unfolding geotop_is_edge_def by (by100 blast)
  have hlisted_edge_endpoints_distinct:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow> v k \<noteq> v (Suc k)"
  proof
    fix k
    assume hk: "k \<in> {0..<p}"
    assume heq: "v k = v (Suc k)"
    have hedge: "geotop_is_edge (closed_segment (v k) (v (Suc k)))"
      using hlisted_edge_members[OF hk] by (by100 blast)
    have hdim0: "geotop_simplex_dim {v k} 0"
      by (rule geotop_singleton_is_simplex)
    have hdim1: "geotop_simplex_dim {v k} 1"
      using hedge heq unfolding geotop_is_edge_def by (by100 simp)
    have "0 = (1::nat)"
      by (rule geotop_simplex_dim_unique[OF hdim0 hdim1])
    thus False
      by (by100 linarith)
  qed
  have hV_nonempty: "?V \<noteq> {}"
  proof -
    have "0 \<in> {0..<p}"
      using hp_pos by (by100 simp)
    hence "v 0 \<in> ?V"
      by (by100 blast)
    thus ?thesis
      by (by100 blast)
  qed
  have hL_member_cases:
      "\<And>\<tau>. \<tau> \<in> L \<Longrightarrow> \<tau> \<in> ((\<lambda>x. {x}) ` ?V) \<or> \<tau> \<in> ?E"
    using hL_listing_decomp by (by100 blast)
  have hsingleton_not_edge: "\<And>(x :: real^2). \<not> geotop_is_edge {x}"
  proof
    fix x :: "real^2"
    assume hedge: "geotop_is_edge {x}"
    have hdim0: "geotop_simplex_dim {x} 0"
      by (rule geotop_singleton_is_simplex[where P=x])
    have hdim1: "geotop_simplex_dim {x} 1"
      using hedge unfolding geotop_is_edge_def by (by100 simp)
    have "0 = (1::nat)"
      by (rule geotop_simplex_dim_unique[OF hdim0 hdim1])
    thus False
      by (by100 linarith)
  qed
  have hE_not_singleton_image:
      "\<And>e. e \<in> ?E \<Longrightarrow> e \<notin> ((\<lambda>x. {x}) ` ?V)"
  proof
    fix e
    assume heE: "e \<in> ?E"
    assume he_single: "e \<in> ((\<lambda>x. {x}) ` ?V)"
    obtain x where heq: "e = {x}"
      using he_single by (by100 blast)
    have "geotop_is_edge {x}"
      using hE_edges[OF heE] heq by (by100 simp)
    thus False
      using hsingleton_not_edge by (by100 blast)
  qed
  have hvertex_edge_parts_disjoint:
      "((\<lambda>x. {x}) ` ?V) \<inter> ?E = {}"
  proof
    show "((\<lambda>x. {x}) ` ?V) \<inter> ?E \<subseteq> {}"
    proof
      fix e
      assume he: "e \<in> ((\<lambda>x. {x}) ` ?V) \<inter> ?E"
      have heE: "e \<in> ?E"
        using he by (by100 simp)
      have he_single: "e \<in> ((\<lambda>x. {x}) ` ?V)"
        using he by (by100 simp)
      show "e \<in> {}"
        using hE_not_singleton_image[OF heE] he_single by (by100 blast)
    qed
    show "{} \<subseteq> ((\<lambda>x. {x}) ` ?V) \<inter> ?E"
      by (by100 simp)
  qed
  have hvertex_singletons_in_L:
      "\<And>x. x \<in> ?V \<Longrightarrow> {x} \<in> L"
    using hV_singletons_subset_L by (by100 blast)
  have hlisted_edge_simplex_vertices:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        geotop_simplex_vertices (closed_segment (v k) (v (Suc k)))
          {v k, v (Suc k)}"
    by (rule geotop_closed_segment_simplex_vertices[OF hlisted_edge_endpoints_distinct])
  have hlisted_edge_endpoints_complex_vertices:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        v k \<in> geotop_complex_vertices L
        \<and> v (Suc k) \<in> geotop_complex_vertices L"
    using hlisted_edge_members hlisted_edge_simplex_vertices
    unfolding geotop_complex_vertices_def by (by100 blast)
  have hlisted_edge_endpoint_singletons_in_L:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow> {v k} \<in> L \<and> {v (Suc k)} \<in> L"
    using hlisted_edge_endpoints_complex_vertices hL_complex
      geotop_complex_vertices_eq_0_simplexes by (by100 blast)
  have hlisted_successor_vertices_in_V:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow> v (Suc k) \<in> ?V"
    using hlisted_edge_endpoints_complex_vertices hV_eq_complex_vertices
    by (by100 blast)
  have hlast_successor_vertex_in_V: "v p \<in> ?V"
    using hlisted_successor_vertices_in_V[of "p - 1"] hp_gt2 by (by100 simp)
  have hclosing_listed_edge_members:
      "closed_segment (v (p - 1)) (v p) \<in> L
      \<and> geotop_is_edge (closed_segment (v (p - 1)) (v p))"
    using hlisted_edge_members[of "p - 1"] hp_gt2 by (by100 simp)
  obtain k\<^sub>p where hk\<^sub>p: "k\<^sub>p \<in> {0..<p}"
      and hvp_eq: "v p = v k\<^sub>p"
    using hlast_successor_vertex_in_V by (by100 blast)
  have hsingleton_convex_hull_in_L:
      "\<And>x. x \<in> ?V \<Longrightarrow> geotop_convex_hull {x} \<in> L"
  proof -
    fix x
    assume hx: "x \<in> ?V"
    have hxL: "{x} \<in> L"
      by (rule hvertex_singletons_in_L[OF hx])
    have hhull: "geotop_convex_hull {x} = {x}"
      using geotop_convex_hull_eq_HOL[of "{x}"] by (by100 simp)
    show "geotop_convex_hull {x} \<in> L"
      using hxL hhull by (by100 simp)
  qed
  have hlisted_edge_convex_hull_eq:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        geotop_convex_hull {v k, v (Suc k)}
          = closed_segment (v k) (v (Suc k))"
    using hlisted_edge_simplex_vertices
    unfolding geotop_simplex_vertices_def by (by100 blast)
  have hlisted_edge_convex_hull_in_L:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        geotop_convex_hull {v k, v (Suc k)} \<in> L"
    using hlisted_edge_convex_hull_eq hlisted_edge_members by (by100 simp)
  have hL_edge_listed_cases:
      "\<And>\<tau>. \<tau> \<in> L \<Longrightarrow> geotop_is_edge \<tau> \<Longrightarrow>
        \<exists>k\<in>{0..<p}. \<tau> = closed_segment (v k) (v (Suc k))"
    using hE_eq_edges by (by100 blast)
  have hL_nonedge_singleton_cases:
      "\<And>\<tau>. \<tau> \<in> L \<Longrightarrow> \<not> geotop_is_edge \<tau> \<Longrightarrow>
        \<exists>x\<in>?V. \<tau> = {x}"
    using hL_member_cases hE_edges by (by100 blast)
  have hL_nonedge_eq_singletons:
      "{\<tau>\<in>L. \<not> geotop_is_edge \<tau>} = ((\<lambda>x. {x}) ` ?V)"
    using hL_nonedge_singleton_cases hvertex_singletons_in_L hsingleton_not_edge
    by (by100 blast)
  have hconvex_hull_nonedge_singleton_cases:
      "\<And>W. W \<noteq> {} \<Longrightarrow> geotop_convex_hull W \<in> L
        \<Longrightarrow> \<not> geotop_is_edge (geotop_convex_hull W)
        \<Longrightarrow> \<exists>x\<in>?V. W = {x}"
  proof -
    fix W :: "(real^2) set"
    assume hW_ne: "W \<noteq> {}"
    assume hWhull_L: "geotop_convex_hull W \<in> L"
    assume hnot_edge: "\<not> geotop_is_edge (geotop_convex_hull W)"
    obtain x where hxV: "x \<in> ?V" and hWhull_eq: "geotop_convex_hull W = {x}"
      using hL_nonedge_singleton_cases[OF hWhull_L hnot_edge] by (by100 blast)
    have hW_sub_x: "W \<subseteq> {x}"
    proof
      fix y
      assume hyW: "y \<in> W"
      have hy_hull: "y \<in> geotop_convex_hull W"
        using geotop_convex_hull_contains_V hyW by (by100 blast)
      show "y \<in> {x}"
        using hy_hull hWhull_eq by (by100 simp)
    qed
    have hxW: "x \<in> W"
    proof -
      obtain y where hyW: "y \<in> W"
        using hW_ne by (by100 blast)
      have hy_single: "y \<in> {x}"
        using hW_sub_x hyW by (by100 blast)
      have hyx: "y = x"
        using hy_single by (by100 simp)
      show ?thesis
        using hyW hyx by (by100 simp)
    qed
    have hW_eq: "W = {x}"
      using hW_sub_x hxW by (by100 blast)
    show "\<exists>x\<in>?V. W = {x}"
      using hxV hW_eq by (by100 blast)
  qed
  have hconvex_hull_edge_listed_cases:
      "\<And>W. geotop_convex_hull W \<in> L
        \<Longrightarrow> geotop_is_edge (geotop_convex_hull W)
        \<Longrightarrow> \<exists>k\<in>{0..<p}.
          geotop_convex_hull W = closed_segment (v k) (v (Suc k))"
    using hL_edge_listed_cases by (by100 blast)
  have hconvex_hull_member_cases:
      "\<And>W. W \<noteq> {} \<Longrightarrow> geotop_convex_hull W \<in> L
        \<Longrightarrow> (\<exists>x\<in>?V. W = {x})
          \<or> (\<exists>k\<in>{0..<p}.
              geotop_convex_hull W = closed_segment (v k) (v (Suc k)))"
    using hconvex_hull_nonedge_singleton_cases hconvex_hull_edge_listed_cases
    by (by100 blast)
  have hlisted_edge_complex_vertex_endpoint_cases:
      "\<And>x k. x \<in> ?V \<Longrightarrow> k \<in> {0..<p}
        \<Longrightarrow> x \<in> closed_segment (v k) (v (Suc k))
        \<Longrightarrow> x = v k \<or> x = v (Suc k)"
  proof -
    fix x k
    assume hxV: "x \<in> ?V"
    assume hk: "k \<in> {0..<p}"
    assume hxseg: "x \<in> closed_segment (v k) (v (Suc k))"
    have hxL: "{x} \<in> L"
      by (rule hvertex_singletons_in_L[OF hxV])
    have hsegL: "closed_segment (v k) (v (Suc k)) \<in> L"
      using hlisted_edge_members[OF hk] by (by100 blast)
    have hmeet: "{x} \<inter> closed_segment (v k) (v (Suc k)) \<noteq> {}"
      using hxseg by (by100 blast)
    have hface_pair:
        "geotop_is_face ({x} \<inter> closed_segment (v k) (v (Suc k))) {x}
        \<and> geotop_is_face ({x} \<inter> closed_segment (v k) (v (Suc k)))
             (closed_segment (v k) (v (Suc k)))"
      using geotop_is_complex_intersection[OF hL_complex] hxL hsegL hmeet
      by (by100 blast)
    have hface_single:
        "geotop_is_face {x} (closed_segment (v k) (v (Suc k)))"
      using hface_pair hxseg by (by100 simp)
    have hface_cases:
        "{x} = {v k}
        \<or> {x} = {v (Suc k)}
        \<or> {x} = closed_segment (v k) (v (Suc k))"
      using geotop_segment_face_cases_dev34
        [OF hface_single hlisted_edge_endpoints_distinct[OF hk]]
      by (by100 blast)
    show "x = v k \<or> x = v (Suc k)"
    proof (rule disjE[OF hface_cases])
      assume "{x} = {v k}"
      thus ?thesis
        by (by100 simp)
    next
      assume htail: "{x} = {v (Suc k)}
        \<or> {x} = closed_segment (v k) (v (Suc k))"
      show ?thesis
      proof (rule disjE[OF htail])
        assume "{x} = {v (Suc k)}"
        thus ?thesis
          by (by100 simp)
      next
        assume hself: "{x} = closed_segment (v k) (v (Suc k))"
        have hedge: "geotop_is_edge (closed_segment (v k) (v (Suc k)))"
          using hlisted_edge_members[OF hk] by (by100 blast)
        have "geotop_is_edge {x}"
          using hedge hself by (by100 simp)
        thus ?thesis
          using hsingleton_not_edge by (by100 blast)
      qed
    qed
  qed
  have hconvex_hull_listed_edge_vertex_subset:
      "\<And>W k. W \<subseteq> geotop_complex_vertices L
        \<Longrightarrow> k \<in> {0..<p}
        \<Longrightarrow> geotop_convex_hull W = closed_segment (v k) (v (Suc k))
        \<Longrightarrow> W \<subseteq> {v k, v (Suc k)}"
  proof
    fix W k x
    assume hWsub: "W \<subseteq> geotop_complex_vertices L"
    assume hk: "k \<in> {0..<p}"
    assume hWhull:
        "geotop_convex_hull W = closed_segment (v k) (v (Suc k))"
    assume hxW: "x \<in> W"
    have hxV: "x \<in> ?V"
      using hWsub hxW hV_eq_complex_vertices by (by100 blast)
    have hx_hull: "x \<in> geotop_convex_hull W"
      using geotop_convex_hull_contains_V hxW by (by100 blast)
    have hx_seg: "x \<in> closed_segment (v k) (v (Suc k))"
      using hx_hull hWhull by (by100 simp)
    show "x \<in> {v k, v (Suc k)}"
      using hlisted_edge_complex_vertex_endpoint_cases[OF hxV hk hx_seg]
      by (by100 blast)
  qed
  have hconvex_hull_nonempty_pair_if_listed_edge:
      "\<And>W k. W \<noteq> {}
        \<Longrightarrow> W \<subseteq> geotop_complex_vertices L
        \<Longrightarrow> k \<in> {0..<p}
        \<Longrightarrow> geotop_convex_hull W = closed_segment (v k) (v (Suc k))
        \<Longrightarrow> W = {v k, v (Suc k)}"
  proof -
    fix W :: "(real^2) set" and k
    assume hW_ne: "W \<noteq> {}"
    assume hWsub: "W \<subseteq> geotop_complex_vertices L"
    assume hk: "k \<in> {0..<p}"
    assume hWhull:
        "geotop_convex_hull W = closed_segment (v k) (v (Suc k))"
    have hW_pair_sub: "W \<subseteq> {v k, v (Suc k)}"
      by (rule hconvex_hull_listed_edge_vertex_subset[OF hWsub hk hWhull])
    have hvk_in_W: "v k \<in> W"
    proof (rule ccontr)
      assume hvk_not: "v k \<notin> W"
      have hW_sub_suc: "W \<subseteq> {v (Suc k)}"
        using hW_pair_sub hvk_not by (by100 blast)
      have hHOL_sub: "convex hull W \<subseteq> convex hull {v (Suc k)}"
        by (rule hull_mono[OF hW_sub_suc])
      have hgeo_sub:
          "geotop_convex_hull W \<subseteq> geotop_convex_hull {v (Suc k)}"
        using hHOL_sub geotop_convex_hull_eq_HOL[of W]
          geotop_convex_hull_eq_HOL[of "{v (Suc k)}"] by (by100 simp)
      have hvk_seg: "v k \<in> closed_segment (v k) (v (Suc k))"
        by (by100 simp)
      have "v k \<in> geotop_convex_hull {v (Suc k)}"
        using hgeo_sub hWhull hvk_seg by (by100 blast)
      hence "v k = v (Suc k)"
        using geotop_convex_hull_eq_HOL[of "{v (Suc k)}"] by (by100 simp)
      thus False
        using hlisted_edge_endpoints_distinct[OF hk] by (by100 blast)
    qed
    have hvsuc_in_W: "v (Suc k) \<in> W"
    proof (rule ccontr)
      assume hvsuc_not: "v (Suc k) \<notin> W"
      have hW_sub_k: "W \<subseteq> {v k}"
        using hW_pair_sub hvsuc_not by (by100 blast)
      have hHOL_sub: "convex hull W \<subseteq> convex hull {v k}"
        by (rule hull_mono[OF hW_sub_k])
      have hgeo_sub:
          "geotop_convex_hull W \<subseteq> geotop_convex_hull {v k}"
        using hHOL_sub geotop_convex_hull_eq_HOL[of W]
          geotop_convex_hull_eq_HOL[of "{v k}"] by (by100 simp)
      have hvsuc_seg: "v (Suc k) \<in> closed_segment (v k) (v (Suc k))"
        by (by100 simp)
      have "v (Suc k) \<in> geotop_convex_hull {v k}"
        using hgeo_sub hWhull hvsuc_seg by (by100 blast)
      hence "v (Suc k) = v k"
        using geotop_convex_hull_eq_HOL[of "{v k}"] by (by100 simp)
      hence "v k = v (Suc k)"
        by (by100 simp)
      thus False
        using hlisted_edge_endpoints_distinct[OF hk] by (by100 blast)
    qed
    show "W = {v k, v (Suc k)}"
      using hW_pair_sub hvk_in_W hvsuc_in_W by (by100 blast)
  qed
  have hcyclic_listing_convex_hull_in_L_cases:
      "\<And>W. W \<noteq> {} \<Longrightarrow> W \<subseteq> geotop_complex_vertices L
        \<Longrightarrow> geotop_convex_hull W \<in> L
        \<Longrightarrow> (\<exists>x\<in>?V. W = {x})
          \<or> (\<exists>k\<in>{0..<p}. W = {v k, v (Suc k)})"
  proof -
    fix W :: "(real^2) set"
    assume hW_ne: "W \<noteq> {}"
    assume hWsub: "W \<subseteq> geotop_complex_vertices L"
    assume hWhull_L: "geotop_convex_hull W \<in> L"
    have hcases:
        "(\<exists>x\<in>?V. W = {x})
        \<or> (\<exists>k\<in>{0..<p}.
            geotop_convex_hull W = closed_segment (v k) (v (Suc k)))"
      by (rule hconvex_hull_member_cases[OF hW_ne hWhull_L])
    show "(\<exists>x\<in>?V. W = {x})
        \<or> (\<exists>k\<in>{0..<p}. W = {v k, v (Suc k)})"
    proof (rule disjE[OF hcases])
      assume hsingle: "\<exists>x\<in>?V. W = {x}"
      show ?thesis
        using hsingle by (by100 blast)
    next
      assume hedge:
          "\<exists>k\<in>{0..<p}.
            geotop_convex_hull W = closed_segment (v k) (v (Suc k))"
      obtain k where hk: "k \<in> {0..<p}"
          and hWhull:
            "geotop_convex_hull W = closed_segment (v k) (v (Suc k))"
        using hedge by (by100 blast)
      have hW_pair: "W = {v k, v (Suc k)}"
        by (rule hconvex_hull_nonempty_pair_if_listed_edge
            [OF hW_ne hWsub hk hWhull])
      show ?thesis
        using hk hW_pair by (by100 blast)
    qed
  qed
  have hempty_not_edge: "\<not> geotop_is_edge ({} :: (real^2) set)"
  proof
    assume hedge: "geotop_is_edge ({} :: (real^2) set)"
    have hdim: "geotop_simplex_dim ({} :: (real^2) set) 1"
      using hedge unfolding geotop_is_edge_def by (by100 blast)
    have hsimplex: "geotop_is_simplex ({} :: (real^2) set)"
      by (rule geotop_simplex_dim_imp_is_simplex[OF hdim])
    show False
      using geotop_is_simplex_nonempty[OF hsimplex] by (by100 simp)
  qed
  have hconvex_hull_empty_notin_L:
      "geotop_convex_hull ({} :: (real^2) set) \<notin> L"
  proof
    assume hempty_hull_L: "geotop_convex_hull ({} :: (real^2) set) \<in> L"
    have hhullempty: "geotop_convex_hull ({} :: (real^2) set) = {}"
      using geotop_convex_hull_eq_HOL[of "({} :: (real^2) set)"]
      by (by100 simp)
    have hempty_L: "({} :: (real^2) set) \<in> L"
      using hempty_hull_L hhullempty by (by100 simp)
    have hcases: "({} :: (real^2) set) \<in> ((\<lambda>x. {x}) ` ?V)
        \<or> ({} :: (real^2) set) \<in> ?E"
      using hL_member_cases[OF hempty_L] by (by100 blast)
    have hnot_singleton_image:
        "({} :: (real^2) set) \<notin> ((\<lambda>x. {x}) ` ?V)"
      by (by100 blast)
    show False
      using hcases hnot_singleton_image hE_edges hempty_not_edge by (by100 blast)
  qed
  have hcyclic_listing_convex_hull_in_L_cases_all:
      "\<And>W. W \<subseteq> geotop_complex_vertices L
        \<Longrightarrow> geotop_convex_hull W \<in> L
        \<Longrightarrow> (\<exists>x\<in>?V. W = {x})
          \<or> (\<exists>k\<in>{0..<p}. W = {v k, v (Suc k)})"
  proof -
    fix W
    assume hWsub: "W \<subseteq> geotop_complex_vertices L"
    assume hWhull_L: "geotop_convex_hull W \<in> L"
    show "(\<exists>x\<in>?V. W = {x})
        \<or> (\<exists>k\<in>{0..<p}. W = {v k, v (Suc k)})"
    proof (cases "W = {}")
      case True
      show ?thesis
        using hWhull_L hconvex_hull_empty_notin_L True by (by100 simp)
    next
      case False
      show ?thesis
        by (rule hcyclic_listing_convex_hull_in_L_cases[OF False hWsub hWhull_L])
    qed
  qed
  have hB_complex:
      "geotop_is_complex ?B"
    by (rule geotop_2simplex_comb_boundary_is_complex_dev34[OF h\<sigma>])
  have hB_finite:
      "finite ?B"
    by (rule geotop_2simplex_comb_boundary_finite_dev34[OF h\<sigma>])
  have hB_vertices_finite:
      "finite (geotop_complex_vertices ?B)"
    by (rule geotop_finite_complex_vertices_finite_dev34[OF hB_complex hB_finite])
  have hB_vertices_poly:
      "geotop_complex_vertices ?B \<subseteq> geotop_polyhedron ?B"
  proof
    fix x
    assume hx: "x \<in> geotop_complex_vertices ?B"
    have hx_single: "{x} \<in> ?B"
      using geotop_complex_vertices_eq_0_simplexes[OF hB_complex] hx by (by100 blast)
    show "x \<in> geotop_polyhedron ?B"
      unfolding geotop_polyhedron_def using hx_single by (by100 blast)
  qed
  have hboundary_vertices_preserving_subdivision:
      "\<exists>F. geotop_is_subdivision F ?B
        \<and> finite F
        \<and> (\<forall>x\<in>geotop_complex_vertices ?B. {x} \<in> F)
        \<and> (\<forall>v. {v} \<in> ?B \<longrightarrow> {v} \<in> F)"
    using geotop_2simplex_boundary_finite_points_subdivision_preserves_vertices_dev34
      [OF h\<sigma> hB_vertices_finite hB_vertices_poly]
    by (by100 blast)
  obtain F\<^sub>0 where hF\<^sub>0_sub: "geotop_is_subdivision F\<^sub>0 ?B"
      and hF\<^sub>0_finite: "finite F\<^sub>0"
      and hB_vertices_in_F\<^sub>0:
        "\<forall>x\<in>geotop_complex_vertices ?B. {x} \<in> F\<^sub>0"
      and hB_old_vertices_in_F\<^sub>0:
        "\<forall>v. {v} \<in> ?B \<longrightarrow> {v} \<in> F\<^sub>0"
    using hboundary_vertices_preserving_subdivision by (by100 blast)
  have hF\<^sub>0_complex: "geotop_is_complex F\<^sub>0"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hF\<^sub>0_sub])
  have hF\<^sub>0_vertices_finite:
      "finite (geotop_complex_vertices F\<^sub>0)"
    by (rule geotop_finite_complex_vertices_finite_dev34[OF hF\<^sub>0_complex hF\<^sub>0_finite])
  have htarget_cycle_model:
      "(\<exists>F \<psi>. geotop_is_subdivision F ?B \<and> geotop_isomorphism L F \<psi>)
      \<and> (\<exists>F u \<psi>.
        geotop_is_subdivision F ?B
        \<and> u p = u 0
        \<and> ((\<lambda>k. u k) ` {0..<p}) = geotop_complex_vertices F
        \<and> F =
          ((\<lambda>x. {x}) ` ((\<lambda>k. u k) ` {0..<p}))
          \<union> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
        \<and> ((\<lambda>k. closed_segment (u k) (u (Suc k))) ` {0..<p})
          = {e\<in>F. geotop_is_edge e}
        \<and> bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)
        \<and> (\<forall>k\<in>{0..<p}. \<psi> (v k) = u k)
        \<and> geotop_isomorphism L F \<psi>)"
    by (rule geotop_cyclic_listing_standard_boundary_cycle_target_model_dev34
        [OF hL_linear hL_finite hdegree_two h\<sigma> hp_gt2 hL_listing_decomp
          hedge_segments hvertices hclosed_vertex
          hcyclic_listing_convex_hull_in_L_cases_all])
  have hstandard_boundary_cycle_subdivision_model:
      "\<exists>F \<psi>. geotop_is_subdivision F ?B \<and> geotop_isomorphism L F \<psi>"
    by (rule conjunct1[OF htarget_cycle_model])
  show ?thesis
    by (rule hstandard_boundary_cycle_subdivision_model)
qed

lemma geotop_cyclic_vertex_listing_standard_boundary_subdivision_model_dev34:
  fixes L :: "(real^2) set set" and v :: "nat \<Rightarrow> real^2"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hdegree_two:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hp_gt2: "2 < p"
  assumes hL_listing_decomp:
    "L =
      ((\<lambda>x. {x}) ` ((\<lambda>k. v k) ` {0..<p}))
      \<union> ((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})"
  assumes hedge_segments:
    "((\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p})
      = {e\<in>L. geotop_is_edge e}"
  assumes hclosed_vertex: "v p = v 0"
  shows "\<exists>(\<sigma> :: (real^2) set) F \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> geotop_isomorphism L F \<psi>"
  (**
    Moise Figure 4.10 boundary-realization construction after the finite graph
    has already been replaced by an abstract cyclic vertex listing.  Build a
    subdivision of the frontier of a standard 2-simplex with the same cyclic
    vertices and edges, then send each listed vertex of \<open>L\<close> to the
    corresponding subdivision vertex. **)
proof -
  let ?V = "(\<lambda>k. v k) ` {0..<p}"
  let ?E = "(\<lambda>k. closed_segment (v k) (v (Suc k))) ` {0..<p}"
  have hp_pos: "0 < p"
    using hp_gt2 by (by100 linarith)
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL_linear])
  have hL_1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_dev34[OF hL_linear])
  have hidx_fin: "finite {0..<p}"
    by (by100 simp)
  have hV_fin: "finite ?V"
    by (rule finite_imageI[OF hidx_fin])
  have hE_fin: "finite ?E"
    by (rule finite_imageI[OF hidx_fin])
  have hV_singletons_subset_L: "((\<lambda>x. {x}) ` ?V) \<subseteq> L"
    using hL_listing_decomp by (by100 blast)
  have hV_subset_complex_vertices: "?V \<subseteq> geotop_complex_vertices L"
  proof
    fix x
    assume hx: "x \<in> ?V"
    have "{x} \<in> ((\<lambda>x. {x}) ` ?V)"
      using hx by (by100 blast)
    hence "{x} \<in> L"
      using hV_singletons_subset_L by (by100 blast)
    thus "x \<in> geotop_complex_vertices L"
      using geotop_complex_vertices_eq_0_simplexes[OF hL_complex] by (by100 simp)
  qed
  have hV_nonempty: "?V \<noteq> {}"
  proof -
    have "0 \<in> {0..<p}"
      using hp_pos by (by100 simp)
    hence "v 0 \<in> ?V"
      by (by100 blast)
    thus ?thesis
      by (by100 blast)
  qed
  have hV_eq_complex_vertices: "?V = geotop_complex_vertices L"
  proof
    show "?V \<subseteq> geotop_complex_vertices L"
      by (rule hV_subset_complex_vertices)
    show "geotop_complex_vertices L \<subseteq> ?V"
    proof
      fix x
      assume hx: "x \<in> geotop_complex_vertices L"
      have hx_singleton: "{x} \<in> L"
        using hx geotop_complex_vertices_eq_0_simplexes[OF hL_complex]
        by (by100 simp)
      have hx_cases:
          "{x} \<in> ((\<lambda>x. {x}) ` ?V) \<or> {x} \<in> ?E"
        using hx_singleton hL_listing_decomp by (by100 blast)
      show "x \<in> ?V"
      proof (rule disjE[OF hx_cases])
        assume "{x} \<in> ((\<lambda>x. {x}) ` ?V)"
        thus ?thesis
          by (by100 blast)
      next
        assume hxE: "{x} \<in> ?E"
        obtain k where hk: "k \<in> {0..<p}"
          and hxseg: "{x} = closed_segment (v k) (v (Suc k))"
          using hxE by (by100 blast)
        have hvk_seg: "v k \<in> closed_segment (v k) (v (Suc k))"
          by (by100 simp)
        have hvk_singleton: "v k \<in> {x}"
          using hxseg hvk_seg by (by100 simp)
        have hx_eq: "x = v k"
          using hvk_singleton by (by100 simp)
        show ?thesis
          using hk hx_eq by (by100 blast)
      qed
    qed
  qed
  have hE_eq_edges: "?E = {e\<in>L. geotop_is_edge e}"
    by (rule hedge_segments)
  have hE_subset_L: "?E \<subseteq> L"
    using hE_eq_edges by (by100 blast)
  have hE_edges: "\<And>e. e \<in> ?E \<Longrightarrow> geotop_is_edge e"
    using hE_eq_edges by (by100 blast)
  have hlisted_edge_members:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        closed_segment (v k) (v (Suc k)) \<in> L
        \<and> geotop_is_edge (closed_segment (v k) (v (Suc k)))"
  proof -
    fix k
    assume hk: "k \<in> {0..<p}"
    have hsegE: "closed_segment (v k) (v (Suc k)) \<in> ?E"
      using hk by (by100 blast)
    show "closed_segment (v k) (v (Suc k)) \<in> L
        \<and> geotop_is_edge (closed_segment (v k) (v (Suc k)))"
      using hsegE hE_subset_L hE_edges by (by100 blast)
  qed
  have hlisted_edge_dim:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow>
        geotop_simplex_dim (closed_segment (v k) (v (Suc k))) 1"
    using hlisted_edge_members unfolding geotop_is_edge_def by (by100 blast)
  have hlisted_edge_endpoints_distinct:
      "\<And>k. k \<in> {0..<p} \<Longrightarrow> v k \<noteq> v (Suc k)"
  proof
    fix k
    assume hk: "k \<in> {0..<p}"
    assume heq: "v k = v (Suc k)"
    have hedge: "geotop_is_edge (closed_segment (v k) (v (Suc k)))"
      using hlisted_edge_members[OF hk] by (by100 blast)
    have hdim0: "geotop_simplex_dim {v k} 0"
      by (rule geotop_singleton_is_simplex)
    have hdim1: "geotop_simplex_dim {v k} 1"
      using hedge heq unfolding geotop_is_edge_def by (by100 simp)
    have "0 = (1::nat)"
      by (rule geotop_simplex_dim_unique[OF hdim0 hdim1])
    thus False
      by (by100 linarith)
  qed
  have hsingleton_not_edge: "\<And>(x :: real^2). \<not> geotop_is_edge {x}"
  proof
    fix x :: "real^2"
    assume hedge: "geotop_is_edge {x}"
    have hdim0: "geotop_simplex_dim {x} 0"
      by (rule geotop_singleton_is_simplex[where P=x])
    have hdim1: "geotop_simplex_dim {x} 1"
      using hedge unfolding geotop_is_edge_def by (by100 simp)
    have "0 = (1::nat)"
      by (rule geotop_simplex_dim_unique[OF hdim0 hdim1])
    thus False
      by (by100 linarith)
  qed
  have hE_not_singleton_image:
      "\<And>e. e \<in> ?E \<Longrightarrow> e \<notin> ((\<lambda>x. {x}) ` ?V)"
  proof
    fix e
    assume heE: "e \<in> ?E"
    assume he_single: "e \<in> ((\<lambda>x. {x}) ` ?V)"
    obtain x where heq: "e = {x}"
      using he_single by (by100 blast)
    have "geotop_is_edge {x}"
      using hE_edges[OF heE] heq by (by100 simp)
    thus False
      using hsingleton_not_edge by (by100 blast)
  qed
  have hvertex_edge_parts_disjoint:
      "((\<lambda>x. {x}) ` ?V) \<inter> ?E = {}"
  proof
    show "((\<lambda>x. {x}) ` ?V) \<inter> ?E \<subseteq> {}"
    proof
      fix e
      assume he: "e \<in> ((\<lambda>x. {x}) ` ?V) \<inter> ?E"
      have heE: "e \<in> ?E"
        using he by (by100 simp)
      have he_single: "e \<in> ((\<lambda>x. {x}) ` ?V)"
        using he by (by100 simp)
      show "e \<in> {}"
        using hE_not_singleton_image[OF heE] he_single by (by100 blast)
    qed
    show "{} \<subseteq> ((\<lambda>x. {x}) ` ?V) \<inter> ?E"
      by (by100 simp)
  qed
  have hboundary_cycle_model:
      "\<exists>(\<sigma> :: (real^2) set) F \<psi>.
        geotop_simplex_dim \<sigma> 2
        \<and> geotop_is_subdivision F
          (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
        \<and> geotop_isomorphism L F \<psi>"
    (**
      Remaining geometric construction: subdivide the three sides of a standard
      2-simplex into a cyclic 1-complex with vertex set corresponding to
      \<open>?V\<close> and edge set corresponding to \<open>?E\<close>, then use the resulting
      ordered vertex bijection as the simplicial isomorphism. **)
  proof -
    obtain \<sigma> :: "(real^2) set" where h\<sigma>: "geotop_simplex_dim \<sigma> 2"
      using geotop_standard_2simplex_exists_dev34 by (by100 blast)
    let ?B = "geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
    have hB_1dim: "geotop_complex_is_1dim ?B"
      by (rule geotop_2simplex_comb_boundary_is_1dim_dev34[OF h\<sigma>])
    have hstandard_cycle_subdivision_model:
        "\<exists>F \<psi>. geotop_is_subdivision F ?B \<and> geotop_isomorphism L F \<psi>"
      (**
        Remaining Figure 4.10 standard-boundary construction: subdivide the
        three boundary edges of \<open>\<sigma>\<close> into a finite cyclic 1-complex whose
        vertex and edge incidence matches the disjoint cyclic listing
        \<open>((\<lambda>x. {x}) ` ?V, ?E)\<close>; then define \<open>\<psi>\<close> by the cyclic vertex
        correspondence and verify the hull-membership clauses of
        \<open>geotop_isomorphism\<close>. **)
      by (rule geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34
          [OF hL_linear hL_finite hdegree_two h\<sigma> hp_gt2 hL_listing_decomp
            hedge_segments hV_eq_complex_vertices hclosed_vertex])
    show ?thesis
      using h\<sigma> hstandard_cycle_subdivision_model by (by100 blast)
  qed
  show ?thesis
    by (rule hboundary_cycle_model)
qed

lemma geotop_cyclic_successor_listing_standard_boundary_subdivision_model_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hdegree_two:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs:
    "s \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_gt2: "2 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes hinj: "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
  assumes hcard:
    "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
  assumes hstate_edge_eq:
    "\<And>k. snd ((geotop_oriented_edge_successor L ^^ k) s)
      = closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ k) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))"
  assumes hedge_image:
    "((\<lambda>k. snd ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p})
      = {e\<in>L. geotop_is_edge e}"
  assumes hL_listing_decomp:
    "L =
      ((\<lambda>x. {x}) `
        ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
      \<union> ((\<lambda>k. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ k) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))) ` {0..<p})"
  shows "\<exists>(\<sigma> :: (real^2) set) F \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> geotop_isomorphism L F \<psi>"
  (**
    Moise Figure 4.10 standard-boundary realization package.  Use the indexed
    cyclic successor listing to subdivide the frontier of a standard 2-simplex
    with matching cyclic vertices and edges, then map the listed graph vertices
    to the corresponding boundary subdivision vertices. **)
proof -
  let ?v = "\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)"
  have hclosed_vertex: "?v p = ?v 0"
    using hp_closed by (by100 simp)
  have hedge_segments:
      "((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<p})
        = {e\<in>L. geotop_is_edge e}"
    by (rule geotop_successor_cycle_state_edge_image_eq_closed_segments_dev34
        [OF hedge_image hstate_edge_eq])
  show ?thesis
    by (rule geotop_cyclic_vertex_listing_standard_boundary_subdivision_model_dev34
        [OF hL_linear hL_finite hdegree_two hp_gt2 hL_listing_decomp
          hedge_segments hclosed_vertex])
qed

lemma geotop_successor_cycle_listing_realizes_standard_triangle_boundary_subdivision_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hdegree_two:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs:
    "s \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_gt2: "2 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes hinj: "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
  assumes hcard:
    "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
  assumes hvertex_image:
    "((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p})
      = geotop_complex_vertices L"
  assumes hedge_image:
    "((\<lambda>k. snd ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p})
      = {e\<in>L. geotop_is_edge e}"
  assumes hL_decomp:
    "L = ((\<lambda>v. {v}) ` geotop_complex_vertices L) \<union>
      {e\<in>L. geotop_is_edge e}"
  assumes hstate_edge_eq:
    "\<And>k. snd ((geotop_oriented_edge_successor L ^^ k) s)
      = closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ k) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))"
  shows "\<exists>(\<sigma> :: (real^2) set) F \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> geotop_isomorphism L F \<psi>"
  (**
    Moise Figure 4.10, standard boundary model package.  Starting only from
    the cyclic successor listing of the original finite graph, subdivide the
    frontier of one standard 2-simplex into a cyclic chain with the same
    number of vertices and edges, then map the listed graph vertices to the
    listed boundary vertices to obtain the simplicial isomorphism. **)
proof -
  let ?v = "\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)"
  have hedge_segments:
      "((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<p})
        = {e\<in>L. geotop_is_edge e}"
    by (rule geotop_successor_cycle_state_edge_image_eq_closed_segments_dev34
        [OF hedge_image hstate_edge_eq])
  have hL_listing_decomp:
      "L =
        ((\<lambda>x. {x}) ` (?v ` {0..<p}))
        \<union> ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<p})"
    by (rule geotop_successor_cycle_listing_vertex_edge_decomp_dev34
        [OF hvertex_image hedge_segments hL_decomp])
  show ?thesis
    by (rule geotop_cyclic_successor_listing_standard_boundary_subdivision_model_dev34
        [OF hL_linear hL_finite hdegree_two hs hp_gt2 hp_closed hinj hcard
            hstate_edge_eq hedge_image hL_listing_decomp])
qed

lemma geotop_successor_cycle_period_gt_two_realizes_boundary_subdivision_model_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hdegree_two:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs:
    "s \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_gt2: "2 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes hinj: "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
  assumes hcard:
    "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
  assumes hL_cycle:
    "L =
      (((\<lambda>v. {v}) `
        ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
      \<union> ((\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p}))"
  shows "\<exists>(\<sigma> :: (real^2) set) F \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> geotop_isomorphism L F \<psi>"
  (**
    Pure Figure 4.10 boundary realization step after the graph-order package:
    use the cyclic list of at least three vertices to subdivide the three sides
    of a 2-simplex, preserving cyclic adjacency, and define the simplicial
    isomorphism by the ordered vertex correspondence. **)
proof -
  let ?v = "\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)"
  let ?E = "((\<lambda>j. closed_segment (?v j) (?v (Suc j))) ` {0..<p})"
  let ?V = "(?v ` {0..<p})"
  have hp_pos: "0 < p"
    using hp_gt2 by (by100 linarith)
  have hidx_fin: "finite {0..<p}"
    by (by100 simp)
  have hV_fin: "finite ?V"
    by (rule finite_imageI[OF hidx_fin])
  have hE_fin: "finite ?E"
    by (rule finite_imageI[OF hidx_fin])
  have hcycle_subcomplex:
      "geotop_is_complex (((\<lambda>v. {v}) ` ?V) \<union> ?E)
        \<and> (((\<lambda>v. {v}) ` ?V) \<union> ?E) \<subseteq> L"
    by (rule geotop_degree_two_oriented_edge_successor_period_cycle_subcomplex_prefix
        [OF hL_linear hdegree_two hs hp_pos hp_closed])
  have hcycle_union_eq_L:
      "(((\<lambda>v. {v}) ` ?V) \<union> ?E) = L"
    using hL_cycle by (by100 simp)
  have hcycle_union_is_complex:
      "geotop_is_complex (((\<lambda>v. {v}) ` ?V) \<union> ?E)"
    using hcycle_subcomplex by (by100 blast)
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL_linear])
  have hsuccessor_states:
      "\<And>k. (geotop_oriented_edge_successor L ^^ k) s
        \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
    by (rule geotop_degree_two_oriented_edge_successor_funpow_state_prefix
        [OF hL_linear hdegree_two hs])
  have hconsecutive_edges:
      "\<And>k. closed_segment (?v k) (?v (Suc k)) \<in> L
        \<and> geotop_is_edge (closed_segment (?v k) (?v (Suc k)))"
    by (rule geotop_degree_two_oriented_edge_successor_consecutive_vertices_edge_prefix
        [OF hL_linear hdegree_two hs])
  have hconsecutive_vertices_distinct:
      "\<And>k. ?v (Suc k) \<noteq> ?v k"
    by (rule geotop_degree_two_oriented_edge_successor_funpow_next_vertex_distinct_prefix
        [OF hL_linear hdegree_two hs])
  have hvertex_singletons:
      "\<And>k. k < p \<Longrightarrow> {?v k} \<in> L"
  proof -
    fix k
    assume hk: "k < p"
    have hk_mem: "k \<in> {0..<p}"
      using hk by (by100 simp)
    have "{?v k} \<in> ((\<lambda>v. {v}) ` ?V)"
      using hk_mem by (by100 blast)
    thus "{?v k} \<in> L"
      using hL_cycle by (by100 blast)
  qed
  have hvertices_in_complex_vertices:
      "\<And>k. k < p \<Longrightarrow> ?v k \<in> geotop_complex_vertices L"
  proof -
    fix k
    assume hk: "k < p"
    have "{?v k} \<in> L"
      by (rule hvertex_singletons[OF hk])
    thus "?v k \<in> geotop_complex_vertices L"
      using geotop_complex_vertices_eq_0_simplexes[OF hL_complex] by (by100 simp)
  qed
  have hclosed_vertex: "?v p = ?v 0"
    using hp_closed by (by100 simp)
  have hnext_in_V: "\<And>k. k < p \<Longrightarrow> ?v (Suc k) \<in> ?V"
  proof -
    fix k
    assume hk: "k < p"
    show "?v (Suc k) \<in> ?V"
    proof (cases "Suc k < p")
      case True
      have "Suc k \<in> {0..<p}"
        using True by (by100 simp)
      thus ?thesis
        by (by100 blast)
    next
      case False
      have hSuc_eq: "Suc k = p"
        using hk False by (by100 linarith)
      have "0 \<in> {0..<p}"
        using hp_pos by (by100 simp)
      hence "?v 0 \<in> ?V"
        by (by100 blast)
      thus ?thesis
        using hSuc_eq hclosed_vertex by (by100 simp)
    qed
  qed
  have hV_subset_complex_vertices: "?V \<subseteq> geotop_complex_vertices L"
  proof
    fix x
    assume hx: "x \<in> ?V"
    obtain k where hk: "k \<in> {0..<p}" and hxk: "x = ?v k"
      using hx by (by100 blast)
    have hk_lt: "k < p"
      using hk by (by100 simp)
    show "x \<in> geotop_complex_vertices L"
      using hvertices_in_complex_vertices[OF hk_lt] hxk by (by100 simp)
  qed
  have hedge_members:
      "\<And>k. k < p \<Longrightarrow> closed_segment (?v k) (?v (Suc k)) \<in> L"
  proof -
    fix k
    assume hk: "k < p"
    have hk_mem: "k \<in> {0..<p}"
      using hk by (by100 simp)
    have "closed_segment (?v k) (?v (Suc k)) \<in> ?E"
      using hk_mem by (by100 blast)
    thus "closed_segment (?v k) (?v (Suc k)) \<in> L"
      using hL_cycle by (by100 blast)
  qed
  have hcomplex_vertices_subset_cycle: "geotop_complex_vertices L \<subseteq> ?V"
  proof
    fix x
    assume hx: "x \<in> geotop_complex_vertices L"
    have hx_singleton: "{x} \<in> L"
      using hx geotop_complex_vertices_eq_0_simplexes[OF hL_complex] by (by100 simp)
    have hx_cases:
        "{x} \<in> ((\<lambda>v. {v}) ` ?V) \<or> {x} \<in> ?E"
      using hx_singleton hL_cycle by (by100 blast)
    show "x \<in> ?V"
    proof (rule disjE[OF hx_cases])
      assume "{x} \<in> ((\<lambda>v. {v}) ` ?V)"
      thus ?thesis
        by (by100 blast)
    next
      assume hxE: "{x} \<in> ?E"
      obtain k where hk: "k \<in> {0..<p}"
        and hxseg: "{x} = closed_segment (?v k) (?v (Suc k))"
        using hxE by (by100 blast)
      have hk_lt: "k < p"
        using hk by (by100 simp)
      have hvk_seg: "?v k \<in> closed_segment (?v k) (?v (Suc k))"
        by (by100 simp)
      have hvk_singleton: "?v k \<in> {x}"
        using hxseg hvk_seg by (by100 simp)
      have hx_eq: "x = ?v k"
        using hvk_singleton by (by100 simp)
      show ?thesis
        using hk hx_eq by (by100 blast)
    qed
  qed
  have hcomplex_vertices_cycle: "geotop_complex_vertices L = ?V"
    using hcomplex_vertices_subset_cycle hV_subset_complex_vertices by (by100 blast)
  have hcomplex_vertices_finite: "finite (geotop_complex_vertices L)"
    using hcomplex_vertices_cycle hV_fin by (by100 simp)
  have hcomplex_vertices_nonempty: "geotop_complex_vertices L \<noteq> {}"
  proof -
    have "0 \<in> {0..<p}"
      using hp_pos by (by100 simp)
    hence "?v 0 \<in> ?V"
      by (by100 blast)
    thus ?thesis
      using hcomplex_vertices_cycle by (by100 blast)
  qed
  have hL_cycle_vertices:
      "L =
        (((\<lambda>v. {v}) ` geotop_complex_vertices L) \<union> ?E)"
    using hL_cycle hcomplex_vertices_cycle by (by100 simp)
  have hE_subset_L: "?E \<subseteq> L"
  proof
    fix e
    assume he: "e \<in> ?E"
    obtain k where hk: "k \<in> {0..<p}"
      and heq: "e = closed_segment (?v k) (?v (Suc k))"
      using he by (by100 blast)
    have "closed_segment (?v k) (?v (Suc k)) \<in> L"
      using hconsecutive_edges[of k] by (by100 blast)
    thus "e \<in> L"
      using heq by (by100 simp)
  qed
  have hE_edges:
      "\<And>e. e \<in> ?E \<Longrightarrow> geotop_is_edge e"
  proof -
    fix e
    assume he: "e \<in> ?E"
    obtain k where hk: "k \<in> {0..<p}"
      and heq: "e = closed_segment (?v k) (?v (Suc k))"
      using he by (by100 blast)
    have "geotop_is_edge (closed_segment (?v k) (?v (Suc k)))"
      using hconsecutive_edges[of k] by (by100 blast)
    thus "geotop_is_edge e"
      using heq by (by100 simp)
  qed
  have hvertex_singletons_subset_L:
      "((\<lambda>v. {v}) ` geotop_complex_vertices L) \<subseteq> L"
  proof
    fix A
    assume hA: "A \<in> ((\<lambda>v. {v}) ` geotop_complex_vertices L)"
    obtain v where hv: "v \<in> geotop_complex_vertices L" and hAeq: "A = {v}"
      using hA by (by100 blast)
    have "{v} \<in> L"
      using hv geotop_complex_vertices_eq_0_simplexes[OF hL_complex] by (by100 simp)
    thus "A \<in> L"
      using hAeq by (by100 simp)
  qed
  have hedge_endpoints_in_vertices:
      "\<And>k. k < p \<Longrightarrow>
        ?v k \<in> geotop_complex_vertices L
        \<and> ?v (Suc k) \<in> geotop_complex_vertices L"
  proof -
    fix k
    assume hk: "k < p"
    have hvk: "?v k \<in> geotop_complex_vertices L"
      by (rule hvertices_in_complex_vertices[OF hk])
    have hvsuc: "?v (Suc k) \<in> ?V"
      by (rule hnext_in_V[OF hk])
    have "?v (Suc k) \<in> geotop_complex_vertices L"
      using hvsuc hV_subset_complex_vertices by (by100 blast)
    thus "?v k \<in> geotop_complex_vertices L
        \<and> ?v (Suc k) \<in> geotop_complex_vertices L"
      using hvk by (by100 blast)
  qed
  have hL_edges_subset_E: "{e\<in>L. geotop_is_edge e} \<subseteq> ?E"
  proof
    fix d
    assume hd: "d \<in> {e\<in>L. geotop_is_edge e}"
    have hdL: "d \<in> L"
      using hd by (by100 simp)
    have hd_edge: "geotop_is_edge d"
      using hd by (by100 simp)
    have hd_cases:
        "d \<in> ((\<lambda>v. {v}) ` geotop_complex_vertices L) \<or> d \<in> ?E"
      using hL_cycle_vertices hdL by (by100 blast)
    show "d \<in> ?E"
    proof (rule disjE[OF hd_cases])
      assume "d \<in> ((\<lambda>v. {v}) ` geotop_complex_vertices L)"
      then obtain v where hd_singleton: "d = {v}"
        by (by100 blast)
      have "\<not> geotop_is_edge {v}"
        by (rule geotop_singleton_not_edge_prefix)
      thus "d \<in> ?E"
        using hd_edge hd_singleton by (by100 blast)
    next
      assume "d \<in> ?E"
      thus "d \<in> ?E" .
    qed
  qed
  have hE_eq_edges: "?E = {e\<in>L. geotop_is_edge e}"
  proof
    show "?E \<subseteq> {e\<in>L. geotop_is_edge e}"
      using hE_subset_L hE_edges by (by100 blast)
    show "{e\<in>L. geotop_is_edge e} \<subseteq> ?E"
      by (rule hL_edges_subset_E)
  qed
  have hL_vertex_edge_decomp:
      "L = ((\<lambda>v. {v}) ` geotop_complex_vertices L) \<union>
        {e\<in>L. geotop_is_edge e}"
    using hL_cycle_vertices hE_eq_edges by (by100 simp)
  have hL_edge_set_finite: "finite {e\<in>L. geotop_is_edge e}"
    using hE_fin hE_eq_edges by (by100 simp)
  have hL_singleton_image_finite:
      "finite ((\<lambda>v. {v}) ` geotop_complex_vertices L)"
    by (rule finite_imageI[OF hcomplex_vertices_finite])
  have hstate_edge_eq:
      "\<And>k. snd ((geotop_oriented_edge_successor L ^^ k) s)
        = closed_segment (?v k) (?v (Suc k))"
    by (rule geotop_degree_two_oriented_edge_successor_funpow_edge_between_prefix
        [OF hL_linear hdegree_two hs])
  have hstate_edge_image_eq_E:
      "((\<lambda>k. snd ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}) = ?E"
  proof
    show "((\<lambda>k. snd ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}) \<subseteq> ?E"
    proof
      fix e
      assume he: "e \<in> ((\<lambda>k. snd ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p})"
      obtain k where hk: "k \<in> {0..<p}"
        and heq: "e = snd ((geotop_oriented_edge_successor L ^^ k) s)"
        using he by (by100 blast)
      have "e = closed_segment (?v k) (?v (Suc k))"
        using heq hstate_edge_eq[of k] by (by100 simp)
      thus "e \<in> ?E"
        using hk by (by100 blast)
    qed
    show "?E \<subseteq> ((\<lambda>k. snd ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p})"
    proof
      fix e
      assume he: "e \<in> ?E"
      obtain k where hk: "k \<in> {0..<p}"
        and heq: "e = closed_segment (?v k) (?v (Suc k))"
        using he by (by100 blast)
      have "e = snd ((geotop_oriented_edge_successor L ^^ k) s)"
        using heq hstate_edge_eq[of k] by (by100 simp)
      thus "e \<in> ((\<lambda>k. snd ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p})"
        using hk by (by100 blast)
    qed
  qed
  have hstate_vertex_image_eq_vertices:
      "((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p})
        = geotop_complex_vertices L"
    using hcomplex_vertices_cycle by (by100 simp)
  have hstate_edge_image_eq_edges:
      "((\<lambda>k. snd ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p})
        = {e\<in>L. geotop_is_edge e}"
    using hstate_edge_image_eq_E hE_eq_edges by (by100 simp)
  show ?thesis
    by (rule geotop_successor_cycle_listing_realizes_standard_triangle_boundary_subdivision_dev34
        [OF hL_linear hL_finite hdegree_two hs hp_gt2 hp_closed hinj hcard
          hstate_vertex_image_eq_vertices hstate_edge_image_eq_edges
          hL_vertex_edge_decomp hstate_edge_eq])
qed

lemma geotop_successor_cycle_realizes_boundary_subdivision_model_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hdegree_two:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs:
    "s \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_gt1: "1 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes hinj: "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
  assumes hcard:
    "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
  assumes hL_cycle:
    "L =
      (((\<lambda>v. {v}) `
        ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
      \<union> ((\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p}))"
  shows "\<exists>(\<sigma> :: (real^2) set) F \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> geotop_isomorphism L F \<psi>"
  (**
    Moise Figure 4.10, boundary-realization half.  Given a finite cyclic
    successor listing of the graph, subdivide the three boundary edges of a
    2-simplex into one cyclic 1-complex with the same ordered vertices and
    edges, then define the simplicial isomorphism by the corresponding cyclic
    vertex order. **)
proof -
  have hp_gt2: "2 < p"
    by (rule geotop_degree_two_oriented_edge_successor_period_gt_two_dev34
        [OF hL_linear hdegree_two hs hp_gt1 hp_closed])
  show ?thesis
    by (rule geotop_successor_cycle_period_gt_two_realizes_boundary_subdivision_model_dev34
        [OF hL_linear hL_finite hdegree_two hs hp_gt2 hp_closed hinj hcard hL_cycle])
qed

lemma geotop_finite_connected_degree_two_linear_graph_cycle_orbit_package_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hL_nonempty: "L \<noteq> {}"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree_two:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  shows "\<exists>w s q p. {w} \<in> L
      \<and> s \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> fst s = w
      \<and> q \<noteq> w
      \<and> snd s = closed_segment w q
      \<and> {q} \<in> L
      \<and> 1 < p
      \<and> 2 < p
      \<and> fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q
      \<and> (geotop_oriented_edge_successor L ^^ p) s = s
      \<and> (\<forall>k. 0 < k \<and> k < p \<longrightarrow>
          (geotop_oriented_edge_successor L ^^ k) s \<noteq> s)
      \<and> inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}
      \<and> card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p
      \<and> closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s) \<in> L
      \<and> geotop_is_edge
          (closed_segment
            (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s))
      \<and> L =
        (((\<lambda>v. {v}) `
          ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
        \<union> ((\<lambda>j. closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ j) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p}))"
  (**
    Fig. 4.10 cycle-order package, separated from the geometric boundary
    subdivision construction: choose a starting vertex and one oriented
    incident edge, follow the degree-two successor once around the graph, and
    use connectedness to show that this closed orbit exhausts L. **)
proof -
  have hpolygon: "geotop_is_polygon (geotop_polyhedron L)"
    by (rule geotop_finite_connected_degree_two_linear_graph_polygon_dev34
        [OF hL_linear hL_finite hL_nonempty hconn hdegree_two])
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL_linear])
  have hpoly_scc:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology (geotop_polyhedron L)"
    by (rule geotop_polygon_top1_simple_closed_curve_prefix[OF hpolygon])
  have hpoly_ne: "geotop_polyhedron L \<noteq> {}"
    by (rule simple_closed_curve_nonempty[OF hpoly_scc])
  obtain w where hwL: "{w} \<in> L"
    using geotop_nonempty_polyhedron_has_complex_vertex[OF hL_complex hpoly_ne]
    by (by100 blast)
  obtain s q p where hs:
      "s \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
    and hfst: "fst s = w"
    and hq_ne: "q \<noteq> w"
    and hsnd: "snd s = closed_segment w q"
    and hqL: "{q} \<in> L"
    and hp_gt1: "1 < p"
    and hfirst_q: "fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q"
    and hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
    and hp_min:
      "\<forall>k. 0 < k \<and> k < p \<longrightarrow>
        (geotop_oriented_edge_successor L ^^ k) s \<noteq> s"
    and hinj: "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
    and hcard:
      "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
    and hclosing_L:
      "closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s) \<in> L"
    and hclosing_edge:
      "geotop_is_edge
        (closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s))"
    using geotop_degree_two_vertex_successor_started_cycle_edge_package_prefix
        [OF hL_linear hL_finite hdegree_two hwL]
    by (elim exE conjE)
  have hp_pos: "0 < p"
    using hp_gt1 by (by100 linarith)
  have hp_gt2: "2 < p"
    by (rule geotop_degree_two_oriented_edge_successor_period_gt_two_dev34
        [OF hL_linear hdegree_two hs hp_gt1 hp_closed])
  have hL_cycle:
      "L =
        (((\<lambda>v. {v}) `
          ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
        \<union> ((\<lambda>j. closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ j) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p}))"
    by (rule geotop_degree_two_oriented_edge_successor_period_cycle_exhausts_connected_graph_prefix
        [OF hL_linear hL_finite hconn hdegree_two hs hp_pos hp_closed])
  show ?thesis
  proof (intro exI conjI)
    show "{w} \<in> L" by (rule hwL)
    show "s \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
      by (rule hs)
    show "fst s = w" by (rule hfst)
    show "q \<noteq> w" by (rule hq_ne)
    show "snd s = closed_segment w q" by (rule hsnd)
    show "{q} \<in> L" by (rule hqL)
    show "1 < p" by (rule hp_gt1)
    show "2 < p" by (rule hp_gt2)
    show "fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q"
      by (rule hfirst_q)
    show "(geotop_oriented_edge_successor L ^^ p) s = s"
      by (rule hp_closed)
    show "\<forall>k. 0 < k \<and> k < p \<longrightarrow>
        (geotop_oriented_edge_successor L ^^ k) s \<noteq> s"
      by (rule hp_min)
    show "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
      by (rule hinj)
    show "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
      by (rule hcard)
    show "closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s) \<in> L"
      by (rule hclosing_L)
    show "geotop_is_edge
        (closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s))"
      by (rule hclosing_edge)
    show "L =
        (((\<lambda>v. {v}) `
          ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
        \<union> ((\<lambda>j. closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ j) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p}))"
      by (rule hL_cycle)
  qed
qed

lemma geotop_finite_connected_degree_two_linear_graph_boundary_subdivision_model_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hL_nonempty: "L \<noteq> {}"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree_two:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  shows "\<exists>(\<sigma> :: (real^2) set) F \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> geotop_isomorphism L F \<psi>"
  (**
    Remaining Fig. 4.10 ordered-cycle realization: enumerate the oriented
    successor orbit once around the finite connected degree-two linear graph,
    build the corresponding subdivision of the frontier of a 2-simplex, and
    map vertices/edges in cyclic order to obtain a simplicial isomorphism. **)
proof -
  have hcycle_orbit_package:
      "\<exists>w s q p. {w} \<in> L
        \<and> s \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
        \<and> fst s = w
        \<and> q \<noteq> w
        \<and> snd s = closed_segment w q
        \<and> {q} \<in> L
        \<and> 1 < p
        \<and> 2 < p
        \<and> fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q
        \<and> (geotop_oriented_edge_successor L ^^ p) s = s
        \<and> (\<forall>k. 0 < k \<and> k < p \<longrightarrow>
            (geotop_oriented_edge_successor L ^^ k) s \<noteq> s)
        \<and> inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}
        \<and> card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p
        \<and> closed_segment
            (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s) \<in> L
        \<and> geotop_is_edge
            (closed_segment
              (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s))
        \<and> L =
          (((\<lambda>v. {v}) `
            ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
          \<union> ((\<lambda>j. closed_segment
            (fst ((geotop_oriented_edge_successor L ^^ j) s))
            (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p}))"
    by (rule geotop_finite_connected_degree_two_linear_graph_cycle_orbit_package_dev34
        [OF hL_linear hL_finite hL_nonempty hconn hdegree_two])
  obtain w s q p where hwL: "{w} \<in> L"
    and hs: "s \<in> {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
    and hfst: "fst s = w"
    and hq_ne: "q \<noteq> w"
    and hsnd: "snd s = closed_segment w q"
    and hqL: "{q} \<in> L"
    and hp_gt1: "1 < p"
    and hp_gt2: "2 < p"
    and hfirst_q: "fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q"
    and hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
    and hp_min:
      "\<forall>k. 0 < k \<and> k < p \<longrightarrow>
        (geotop_oriented_edge_successor L ^^ k) s \<noteq> s"
    and hinj: "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
    and hcard:
      "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
    and hclosing_L:
      "closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s) \<in> L"
    and hclosing_edge:
      "geotop_is_edge
        (closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s))"
    and hL_cycle:
      "L =
        (((\<lambda>v. {v}) `
          ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
        \<union> ((\<lambda>j. closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ j) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p}))"
    using hcycle_orbit_package by (elim exE conjE)
  have hordered_cycle_model:
      "\<exists>(\<sigma> :: (real^2) set) F \<psi>.
        geotop_simplex_dim \<sigma> 2
        \<and> geotop_is_subdivision F
          (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
        \<and> geotop_isomorphism L F \<psi>"
    by (rule geotop_successor_cycle_realizes_boundary_subdivision_model_dev34
        [OF hL_linear hL_finite hdegree_two hs hp_gt1 hp_closed hinj hcard hL_cycle])
  show ?thesis
    by (rule hordered_cycle_model)
qed

lemma geotop_connected_nonisolated_finite_linear_graph_boundary_cycle_model_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron L)"
  shows "\<exists>(\<sigma> :: (real^2) set) F \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> geotop_isomorphism L F \<psi>"
  (**
    Core Fig. 4.10 cycle realization.  The finite linear graph whose carrier
    is a polygon has a cyclic edge order; place that ordered cycle as a
    subdivision of the frontier of a 2-simplex. **)
proof -
  have hconnected_nonisolated:
      "geotop_complex_connected L
      \<and> (\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e))"
    by (rule geotop_finite_linear_graph_polygon_connected_nonisolated_dev34
        [OF hL_linear hL_finite hpolygon])
  have hconn: "geotop_complex_connected L"
    using hconnected_nonisolated by (by100 blast)
  have hdegree_two:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
    by (rule geotop_polygon_finite_linear_graph_vertices_degree_two_prefix
        [OF hL_linear hL_finite hconn hpolygon])
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL_linear])
  have hpoly_scc:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology (geotop_polyhedron L)"
    by (rule geotop_polygon_top1_simple_closed_curve_prefix[OF hpolygon])
  have hpoly_ne: "geotop_polyhedron L \<noteq> {}"
    by (rule simple_closed_curve_nonempty[OF hpoly_scc])
  obtain w where hwL: "{w} \<in> L"
    using geotop_nonempty_polyhedron_has_complex_vertex[OF hL_complex hpoly_ne]
    by (by100 blast)
  have hL_nonempty: "L \<noteq> {}"
    using hwL by (by100 blast)
  show ?thesis
    by (rule geotop_finite_connected_degree_two_linear_graph_boundary_subdivision_model_dev34
        [OF hL_linear hL_finite hL_nonempty hconn hdegree_two])
qed

lemma geotop_fig410_boundary_subdivision_model_from_finite_linear_graph_polygon_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron L)"
  shows "\<exists>(\<sigma> :: (real^2) set) F \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> geotop_isomorphism L F \<psi>"
  (**
    Fig. 4.10, book step 1 in graph-only form.  Enumerate the finite linear
    graph as the ordered edge-cycle of a polygon; subdivide the whole frontier
    of a 2-simplex with the same ordered vertex/edge data; map each link vertex
    to the corresponding boundary subdivision vertex. **)
proof -
  (**
    Remaining Fig. 4.10 graph step: recover the cyclic edge order and realize
    that abstract cycle as a subdivision of the frontier of a 2-simplex. **)
  show ?thesis
    by (rule geotop_connected_nonisolated_finite_linear_graph_boundary_cycle_model_dev34
        [OF hL_linear hL_finite hpolygon])
qed

lemma geotop_fig410_boundary_subdivision_model_from_finite_linear_link_polygon_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  assumes hlink_finite: "finite (geotop_link K v)"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
  shows "\<exists>(\<sigma> :: (real^2) set) F \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> geotop_isomorphism (geotop_link K v) F \<psi>"
  (**
    Fig. 4.10, book step 1.  A finite linear polygonal link is enumerated as an
    edge-cycle and matched to a subdivision of the frontier of a 2-simplex. **)
proof -
  show ?thesis
    by (rule geotop_fig410_boundary_subdivision_model_from_finite_linear_graph_polygon_dev34
        [OF hlink_linear hlink_finite hpolygon])
qed

lemma geotop_complex_vertices_subset_polyhedron_dev34:
  fixes K :: "'a::real_normed_vector set set"
  shows "geotop_complex_vertices K \<subseteq> geotop_polyhedron K"
proof
  fix v
  assume hv: "v \<in> geotop_complex_vertices K"
  obtain \<tau> V where h\<tau>K: "\<tau> \<in> K"
    and hV: "geotop_simplex_vertices \<tau> V"
    and hvV: "v \<in> V"
    using hv unfolding geotop_complex_vertices_def by (by100 blast)
  have h\<tau>_hull: "\<tau> = geotop_convex_hull V"
    using hV unfolding geotop_simplex_vertices_def by (by100 blast)
  have hV_hull: "V \<subseteq> geotop_convex_hull V"
    by (rule geotop_convex_hull_contains_V)
  have hV\<tau>: "V \<subseteq> \<tau>"
    using h\<tau>_hull hV_hull by (by100 simp)
  have "v \<in> \<tau>"
    using hV\<tau> hvV by (by100 blast)
  show "v \<in> geotop_polyhedron K"
    unfolding geotop_polyhedron_def using h\<tau>K \<open>v \<in> \<tau>\<close> by (by100 blast)
qed

lemma geotop_2simplex_HOL_interior_nonempty_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  shows "interior \<sigma> \<noteq> {}"
  (**
    Fig. 4.10 interior-vertex step: a 2-simplex in the plane has a nonempty
    ordinary interior, so the construction may choose its new cone vertex
    there. **)
proof -
  have hsimplex: "geotop_is_simplex \<sigma>"
    by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>])
  have hrel_nonempty: "rel_interior \<sigma> \<noteq> {}"
    by (rule geotop_simplex_rel_interior_nonempty[OF hsimplex])
  have hhyper: "geotop_hyperplane_dim (affine hull \<sigma>) 2"
    by (rule geotop_simplex_dim_imp_hyperplane_dim[OF h\<sigma>])
  have hdim\<sigma>: "aff_dim \<sigma> = 2"
    using geotop_hyperplane_dim_imp_affine_aff_dim[OF hhyper] by (by100 simp)
  have hdim_UNIV: "aff_dim \<sigma> = int (DIM(real^2))"
    using hdim\<sigma> by (by100 simp)
  have hrel_eq_int: "rel_interior \<sigma> = interior \<sigma>"
    by (rule interior_rel_interior[OF hdim_UNIV])
  show ?thesis
    using hrel_nonempty hrel_eq_int by (by100 simp)
qed

lemma geotop_2simplex_face_complex_polyhedron_eq_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  shows "geotop_polyhedron {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} = \<sigma>"
proof
  show "geotop_polyhedron {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} \<subseteq> \<sigma>"
  proof
    fix x
    assume hx: "x \<in> geotop_polyhedron {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    obtain \<tau> where h\<tau>: "\<tau> \<in> {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
      and hx\<tau>: "x \<in> \<tau>"
      using hx unfolding geotop_polyhedron_def by (by100 blast)
    have hcase: "geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>"
      using h\<tau> by (by100 simp)
    show "x \<in> \<sigma>"
    proof (rule disjE[OF hcase])
      assume hface: "geotop_is_face \<tau> \<sigma>"
      have "\<tau> \<subseteq> \<sigma>"
        by (rule geotop_is_face_imp_subset[OF hface])
      show ?thesis
        using \<open>\<tau> \<subseteq> \<sigma>\<close> hx\<tau> by (by100 blast)
    next
      assume "\<tau> = \<sigma>"
      show ?thesis
        using \<open>\<tau> = \<sigma>\<close> hx\<tau> by (by100 simp)
    qed
  qed
  show "\<sigma> \<subseteq> geotop_polyhedron {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
  proof
    fix x
    assume hx: "x \<in> \<sigma>"
    have h\<sigma>K: "\<sigma> \<in> {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
      by (by100 simp)
    show "x \<in> geotop_polyhedron {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
      unfolding geotop_polyhedron_def using h\<sigma>K hx by (by100 blast)
  qed
qed

lemma geotop_subdivision_vertices_subset_original_polyhedron_dev34:
  fixes K K' :: "'a::real_normed_vector set set"
  assumes hsub: "geotop_is_subdivision K' K"
  shows "geotop_complex_vertices K' \<subseteq> geotop_polyhedron K"
  (**
    A vertex of a subdivision lies in the same carrier as the original
    complex.  This is the carrier half of the Fig. 4.10 claim that the new
    interior cone point is not an old boundary-subdivision vertex. **)
proof -
  have hvertices: "geotop_complex_vertices K' \<subseteq> geotop_polyhedron K'"
    by (rule geotop_complex_vertices_subset_polyhedron_dev34)
  have hpoly: "geotop_polyhedron K' = geotop_polyhedron K"
    using hsub unfolding geotop_is_subdivision_def by (by100 blast)
  show ?thesis
    using hvertices hpoly by (by100 simp)
qed

lemma geotop_subdivision_target_is_complex_dev34:
  fixes K K' :: "'a::real_normed_vector set set"
  assumes hsub: "geotop_is_subdivision K' K"
  shows "geotop_is_complex K"
  using hsub unfolding geotop_is_subdivision_def by (by100 blast)

lemma geotop_subdivision_polyhedron_eq_dev34:
  fixes K K' :: "'a::real_normed_vector set set"
  assumes hsub: "geotop_is_subdivision K' K"
  shows "geotop_polyhedron K' = geotop_polyhedron K"
  using hsub unfolding geotop_is_subdivision_def by (by100 blast)

lemma geotop_2simplex_face_complex_subdivision_HOL_interior_point_dev34:
  fixes L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hsubdiv:
    "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
  shows "c \<in> interior (geotop_polyhedron L')"
  (**
    Target-side part of Fig. 4.10: a subdivision of the full face complex has
    the same polyhedron as the 2-simplex, so an interior cone point remains an
    ordinary interior point of the fan polyhedron. **)
proof -
  have hpoly_sub:
      "geotop_polyhedron L' =
        geotop_polyhedron {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    by (rule geotop_subdivision_polyhedron_eq_dev34[OF hsubdiv])
  have hpoly_face:
      "geotop_polyhedron {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} = \<sigma>"
    by (rule geotop_2simplex_face_complex_polyhedron_eq_dev34[OF h\<sigma>])
  have hpoly: "geotop_polyhedron L' = \<sigma>"
    using hpoly_sub hpoly_face by (by100 simp)
  show ?thesis
    using hc hpoly by (by100 simp)
qed

lemma geotop_2simplex_rel_frontier_subset_comb_boundary_polyhedron_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  shows "rel_frontier \<sigma> \<subseteq>
    geotop_polyhedron
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
proof
  fix x
  assume hx: "x \<in> rel_frontier \<sigma>"
  obtain V m where hV_fin: "finite V"
    and hV_card: "card V = 2 + 1"
    and h2_le_m: "2 \<le> m"
    and hgp_V: "geotop_general_position V m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma> unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>_HOL: "\<sigma> = convex hull V"
    using h\<sigma>_eq geotop_convex_hull_eq_HOL[of V] by (by100 simp)
  have h\<sigma>polytope: "polytope \<sigma>"
    unfolding polytope_def using hV_fin h\<sigma>_HOL by (by100 blast)
  have h\<sigma>polyhedron: "polyhedron \<sigma>"
    by (rule polytope_imp_polyhedron[OF h\<sigma>polytope])
  obtain F where hF_face: "F face_of \<sigma>"
    and hF_ne: "F \<noteq> \<sigma>"
    and hxF: "x \<in> F"
    using hx rel_frontier_of_polyhedron_alt[OF h\<sigma>polyhedron]
    by (by100 blast)
  have hF_nonempty: "F \<noteq> {}"
    using hxF by (by100 blast)
  have h\<sigma>simplex: "geotop_is_simplex \<sigma>"
    by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>])
  have hF_geotop: "geotop_is_face F \<sigma>"
    by (rule geotop_HOL_face_of_simplex_imp_geotop_is_face_R2
        [OF h\<sigma>simplex hF_face hF_nonempty])
  have hF_boundary:
      "F \<in> geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
    by (rule geotop_2simplex_proper_face_in_comb_boundary_dev34
        [OF h\<sigma> hF_geotop hF_ne])
  show "x \<in>
    geotop_polyhedron
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
    unfolding geotop_polyhedron_def using hF_boundary hxF by (by100 blast)
qed

lemma geotop_2simplex_comb_boundary_polyhedron_disjoint_HOL_interior_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  shows
    "geotop_polyhedron
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<inter> interior \<sigma> = {}"
  (**
    The combinatorial boundary of a 2-simplex is made of proper faces, and
    proper faces are disjoint from the simplex relative interior; in the plane,
    that relative interior is the ordinary interior. **)
proof (rule equals0I)
  fix x
  assume hx:
    "x \<in> geotop_polyhedron
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<inter> interior \<sigma>"
  have hx_int: "x \<in> interior \<sigma>"
    using hx by (by100 blast)
  obtain \<rho> where h\<rho>:
      "\<rho> \<in> geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
    and hx\<rho>: "x \<in> \<rho>"
    using hx unfolding geotop_polyhedron_def by (by100 blast)
  have hproper: "geotop_is_face \<rho> \<sigma> \<and> \<rho> \<noteq> \<sigma>"
    by (rule geotop_2simplex_comb_boundary_member_proper_face_dev34[OF h\<sigma> h\<rho>])
  have hface: "geotop_is_face \<rho> \<sigma>"
    using hproper by (by100 blast)
  have hne: "\<rho> \<noteq> \<sigma>"
    using hproper by (by100 blast)
  have hface_HOL: "\<rho> face_of \<sigma>"
    by (rule geotop_is_face_imp_HOL_face_of_R2[OF hface])
  have hhyper: "geotop_hyperplane_dim (affine hull \<sigma>) 2"
    by (rule geotop_simplex_dim_imp_hyperplane_dim[OF h\<sigma>])
  have hdim\<sigma>: "aff_dim \<sigma> = 2"
    using geotop_hyperplane_dim_imp_affine_aff_dim[OF hhyper] by (by100 simp)
  have hdim_UNIV: "aff_dim \<sigma> = int (DIM(real^2))"
    using hdim\<sigma> by (by100 simp)
  have hrel_eq_int: "rel_interior \<sigma> = interior \<sigma>"
    by (rule interior_rel_interior[OF hdim_UNIV])
  have hx_rel: "x \<in> rel_interior \<sigma>"
    using hx_int hrel_eq_int by (by100 simp)
  have hdisj: "\<rho> \<inter> rel_interior \<sigma> = {}"
    by (rule face_of_disjoint_rel_interior[OF hface_HOL hne])
  show False
    using hdisj hx\<rho> hx_rel by (by100 blast)
qed

lemma geotop_2simplex_comb_boundary_self_subdivision_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  shows "geotop_is_subdivision
    (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
    (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
proof -
  have hcomplex:
      "geotop_is_complex
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
    by (rule geotop_2simplex_comb_boundary_is_complex_dev34[OF h\<sigma>])
  show ?thesis
    by (rule geotop_is_subdivision_refl[OF hcomplex])
qed

lemma geotop_standard_2simplex_boundary_self_subdivision_model_dev34:
  shows "\<exists>(\<sigma> :: (real^2) set) F.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
proof -
  obtain \<sigma> :: "(real^2) set" where h\<sigma>: "geotop_simplex_dim \<sigma> 2"
    using geotop_standard_2simplex_exists_dev34 by (by100 blast)
  let ?F = "geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
  have hsub:
      "geotop_is_subdivision ?F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
    by (rule geotop_2simplex_comb_boundary_self_subdivision_dev34[OF h\<sigma>])
  show ?thesis
    using h\<sigma> hsub by (by100 blast)
qed

lemma geotop_standard_2simplex_boundary_self_isomorphism_model_dev34:
  shows "\<exists>(\<sigma> :: (real^2) set) F \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> geotop_isomorphism F F \<psi>"
proof -
  obtain \<sigma> :: "(real^2) set" and F where h\<sigma>: "geotop_simplex_dim \<sigma> 2"
    and hsub:
      "geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
    using geotop_standard_2simplex_boundary_self_subdivision_model_dev34
    by (by100 blast)
  have hF_complex: "geotop_is_complex F"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hsub])
  have hiso: "geotop_isomorphism F F id"
    by (rule geotop_isomorphism_refl_id_dev34[OF hF_complex])
  show ?thesis
    using h\<sigma> hsub hiso by (by100 blast)
qed

lemma geotop_boundary_subdivision_is_complex_dev34:
  fixes F :: "(real^2) set set"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  shows "geotop_is_complex F"
  by (rule geotop_subdivision_source_is_complex_dev34[OF hsub])

lemma geotop_boundary_subdivision_polyhedron_eq_dev34:
  fixes F :: "(real^2) set set"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  shows
    "geotop_polyhedron F =
      geotop_polyhedron
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  by (rule geotop_subdivision_polyhedron_eq_dev34[OF hsub])

lemma geotop_boundary_subdivision_finite_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  shows "finite F"
proof -
  have hbd_fin:
    "finite (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
    by (rule geotop_2simplex_comb_boundary_finite_dev34[OF h\<sigma>])
  show ?thesis
    by (rule geotop_subdivision_of_finite_is_finite[OF hbd_fin hsub])
qed

lemma geotop_boundary_subdivision_vertices_disjoint_HOL_interior_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  shows "geotop_complex_vertices F \<inter> interior \<sigma> = {}"
  (**
    A subdivision of the boundary has the same carrier as the boundary; since
    the boundary carrier misses the 2-simplex interior, its vertices do too. **)
proof (rule equals0I)
  fix x
  assume hx: "x \<in> geotop_complex_vertices F \<inter> interior \<sigma>"
  have hxV: "x \<in> geotop_complex_vertices F"
    using hx by (by100 blast)
  have hx_int: "x \<in> interior \<sigma>"
    using hx by (by100 blast)
  have hV_sub:
    "geotop_complex_vertices F \<subseteq>
      geotop_polyhedron
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
    by (rule geotop_subdivision_vertices_subset_original_polyhedron_dev34[OF hsub])
  have hx_boundary:
    "x \<in> geotop_polyhedron
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
    using hV_sub hxV by (by100 blast)
  have hdisj:
    "geotop_polyhedron
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<inter> interior \<sigma> = {}"
    by (rule geotop_2simplex_comb_boundary_polyhedron_disjoint_HOL_interior_dev34[OF h\<sigma>])
  show False
    using hdisj hx_boundary hx_int by (by100 blast)
qed

lemma geotop_boundary_subdivision_polyhedron_disjoint_HOL_interior_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  shows "geotop_polyhedron F \<inter> interior \<sigma> = {}"
proof -
  have hpoly:
    "geotop_polyhedron F =
      geotop_polyhedron
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
    by (rule geotop_boundary_subdivision_polyhedron_eq_dev34[OF hsub])
  have hbd_disj:
    "geotop_polyhedron
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<inter> interior \<sigma> = {}"
    by (rule geotop_2simplex_comb_boundary_polyhedron_disjoint_HOL_interior_dev34
        [OF h\<sigma>])
  show ?thesis
    using hpoly hbd_disj by (by100 simp)
qed

lemma geotop_boundary_subdivision_radial_cover_2simplex_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  shows "\<forall>x\<in>\<sigma>. x = c \<or>
    (\<exists>y\<in>geotop_polyhedron F. x \<in> closed_segment c y)"
proof (intro ballI)
  fix x
  assume hx\<sigma>: "x \<in> \<sigma>"
  show "x = c \<or> (\<exists>y\<in>geotop_polyhedron F. x \<in> closed_segment c y)"
  proof (cases "x = c")
    case True
    show ?thesis
      using True by (by100 blast)
  next
    case hx_ne_c: False
    have h\<sigma>simplex: "geotop_is_simplex \<sigma>"
      by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>])
    have h\<sigma>conv: "convex \<sigma>"
      by (rule GeoTopBase0.geotop_simplex_is_convex[OF h\<sigma>simplex])
    have h\<sigma>compact: "compact \<sigma>"
      by (rule geotop_is_simplex_compact[OF h\<sigma>simplex])
    have h\<sigma>bdd: "bounded \<sigma>"
      using h\<sigma>compact compact_imp_bounded by (by100 blast)
    have hhyper: "geotop_hyperplane_dim (affine hull \<sigma>) 2"
      by (rule geotop_simplex_dim_imp_hyperplane_dim[OF h\<sigma>])
    have hdim\<sigma>: "aff_dim \<sigma> = 2"
      using geotop_hyperplane_dim_imp_affine_aff_dim[OF hhyper] by (by100 simp)
    have hdim_UNIV: "aff_dim \<sigma> = int (DIM(real^2))"
      using hdim\<sigma> by (by100 simp)
    have hrel_eq_int: "rel_interior \<sigma> = interior \<sigma>"
      by (rule interior_rel_interior[OF hdim_UNIV])
    have hc_rel: "c \<in> rel_interior \<sigma>"
      using hc hrel_eq_int by (by100 simp)
    have hnot_sing: "\<not> (c = x \<and> \<sigma> = {c})"
      using hx_ne_c by (by100 blast)
    obtain y where hy_front: "y \<in> rel_frontier \<sigma>"
      and hx_seg: "x \<in> closed_segment c y"
      using segment_to_rel_frontier[OF h\<sigma>conv h\<sigma>bdd hc_rel hx\<sigma> hnot_sing]
      by (by100 metis)
    have hy_boundary:
        "y \<in> geotop_polyhedron
          (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
      using geotop_2simplex_rel_frontier_subset_comb_boundary_polyhedron_dev34
        [OF h\<sigma>] hy_front by (by100 blast)
    have hpoly_eq:
        "geotop_polyhedron F =
          geotop_polyhedron
            (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
      by (rule geotop_boundary_subdivision_polyhedron_eq_dev34[OF hsub])
    have hyF: "y \<in> geotop_polyhedron F"
      using hy_boundary hpoly_eq by (by100 simp)
    show ?thesis
      using hyF hx_seg by (by100 blast)
  qed
qed

lemma geotop_boundary_subdivision_interior_point_notin_polyhedron_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  shows "c \<notin> geotop_polyhedron F"
proof
  assume hcF: "c \<in> geotop_polyhedron F"
  have hdisj: "geotop_polyhedron F \<inter> interior \<sigma> = {}"
    by (rule geotop_boundary_subdivision_polyhedron_disjoint_HOL_interior_dev34
        [OF h\<sigma> hsub])
  show False
    using hdisj hcF hc by (by100 blast)
qed

lemma geotop_boundary_subdivision_simplex_misses_interior_point_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hA: "A \<in> F"
  shows "c \<notin> A"
proof
  assume hcA: "c \<in> A"
  have hc_not_poly: "c \<notin> geotop_polyhedron F"
    by (rule geotop_boundary_subdivision_interior_point_notin_polyhedron_dev34
        [OF h\<sigma> hsub hc])
  have hc_poly: "c \<in> geotop_polyhedron F"
    using hA hcA unfolding geotop_polyhedron_def by (by100 blast)
  show False
    using hc_not_poly hc_poly by (by100 blast)
qed

lemma geotop_boundary_subdivision_hull_simplex_misses_interior_point_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hA: "geotop_convex_hull A \<in> F"
  shows "c \<notin> geotop_convex_hull A"
  by (rule geotop_boundary_subdivision_simplex_misses_interior_point_dev34
      [OF h\<sigma> hsub hc hA])

lemma geotop_boundary_subdivision_simplex_affine_hull_misses_interior_point_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hA: "A \<in> F"
  shows "c \<notin> affine hull A"
proof
  assume hc_aff_A: "c \<in> affine hull A"
  let ?B = "geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
  have href: "geotop_refines F ?B"
    using hsub unfolding geotop_is_subdivision_def by (by100 blast)
  obtain \<rho> where h\<rho>B: "\<rho> \<in> ?B" and hA\<rho>: "A \<subseteq> \<rho>"
    using href hA unfolding geotop_refines_def by (by100 blast)
  have hproper: "geotop_is_face \<rho> \<sigma> \<and> \<rho> \<noteq> \<sigma>"
    by (rule geotop_2simplex_comb_boundary_member_proper_face_dev34
        [OF h\<sigma> h\<rho>B])
  have hface: "geotop_is_face \<rho> \<sigma>"
    using hproper by (by100 blast)
  have hne: "\<rho> \<noteq> \<sigma>"
    using hproper by (by100 blast)
  have hface_HOL: "\<rho> face_of \<sigma>"
    by (rule geotop_is_face_imp_HOL_face_of_R2[OF hface])
  have h\<sigma>simplex: "geotop_is_simplex \<sigma>"
    by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>])
  have h\<sigma>conv: "convex \<sigma>"
    by (rule GeoTopBase0.geotop_simplex_is_convex[OF h\<sigma>simplex])
  have hhyper: "geotop_hyperplane_dim (affine hull \<sigma>) 2"
    by (rule geotop_simplex_dim_imp_hyperplane_dim[OF h\<sigma>])
  have hdim\<sigma>: "aff_dim \<sigma> = 2"
    using geotop_hyperplane_dim_imp_affine_aff_dim[OF hhyper] by (by100 simp)
  have hdim_UNIV: "aff_dim \<sigma> = int (DIM(real^2))"
    using hdim\<sigma> by (by100 simp)
  have hrel_eq_int: "rel_interior \<sigma> = interior \<sigma>"
    by (rule interior_rel_interior[OF hdim_UNIV])
  have hc_rel: "c \<in> rel_interior \<sigma>"
    using hc hrel_eq_int by (by100 simp)
  have hdisj: "affine hull \<rho> \<inter> rel_interior \<sigma> = {}"
    by (rule affine_hull_face_of_disjoint_rel_interior
        [OF h\<sigma>conv hface_HOL hne])
  have hAff_sub: "affine hull A \<subseteq> affine hull \<rho>"
    by (rule hull_mono[OF hA\<rho>])
  have "c \<in> affine hull \<rho>"
    using hAff_sub hc_aff_A by (by100 blast)
  show False
    using hdisj \<open>c \<in> affine hull \<rho>\<close> hc_rel by (by100 blast)
qed

lemma geotop_convex_hull_insert_contains_insert_point_dev34:
  fixes A :: "(real^2) set"
  shows "c \<in> geotop_convex_hull (insert c A)"
proof -
  have hc_set: "c \<in> insert c A"
    by (by100 simp)
  have hsub: "insert c A \<subseteq> geotop_convex_hull (insert c A)"
    unfolding geotop_convex_hull_eq_HOL by (rule hull_subset)
  show ?thesis
    using hsub hc_set by (by100 blast)
qed

lemma geotop_boundary_subdivision_old_hull_ne_cone_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hA: "geotop_convex_hull A \<in> F"
  assumes hB: "B \<in> F"
  shows "geotop_convex_hull A \<noteq> geotop_convex_hull (insert c B)"
proof
  assume heq: "geotop_convex_hull A = geotop_convex_hull (insert c B)"
  have hc_not_old: "c \<notin> geotop_convex_hull A"
    by (rule geotop_boundary_subdivision_hull_simplex_misses_interior_point_dev34
        [OF h\<sigma> hsub hc hA])
  have hc_cone: "c \<in> geotop_convex_hull (insert c B)"
    by (rule geotop_convex_hull_insert_contains_insert_point_dev34)
  have "c \<in> geotop_convex_hull A"
    using heq hc_cone by (by100 simp)
  show False
    using hc_not_old \<open>c \<in> geotop_convex_hull A\<close> by (by100 blast)
qed

lemma geotop_old_vertices_hull_ne_new_singleton_dev34:
  fixes F :: "(real^2) set set"
  fixes A :: "(real^2) set"
  assumes hcF: "c \<notin> geotop_complex_vertices F"
  assumes hA: "A \<subseteq> geotop_complex_vertices F"
  shows "geotop_convex_hull A \<noteq> geotop_convex_hull {c}"
proof
  assume heq: "geotop_convex_hull A = geotop_convex_hull {c}"
  have hsing: "geotop_convex_hull {c} = {c}"
    using geotop_convex_hull_eq_HOL[of "{c}"] by (by100 simp)
  show False
  proof (cases "A = {}")
    case True
    have "geotop_convex_hull A = {}"
      using True geotop_convex_hull_eq_HOL[of A] by (by100 simp)
    then show False
      using heq hsing by (by100 simp)
  next
    case False
    obtain a where ha: "a \<in> A"
      using False by (by100 blast)
    have hsub: "A \<subseteq> geotop_convex_hull A"
      unfolding geotop_convex_hull_eq_HOL by (rule hull_subset)
    have ha_hull: "a \<in> geotop_convex_hull A"
      using hsub ha by (by100 blast)
    have hac: "a = c"
      using heq hsing ha_hull by (by100 blast)
    have "a \<in> geotop_complex_vertices F"
      using hA ha by (by100 blast)
    then show False
      using hcF hac by (by100 blast)
  qed
qed

lemma geotop_boundary_subdivision_cone_hull_ne_new_singleton_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hA: "A \<in> F"
  assumes hAne: "A \<noteq> {}"
  shows "geotop_convex_hull (insert c A) \<noteq> geotop_convex_hull {c}"
proof
  assume heq: "geotop_convex_hull (insert c A) = geotop_convex_hull {c}"
  obtain a where ha: "a \<in> A"
    using hAne by (by100 blast)
  have hc_not_A: "c \<notin> A"
    by (rule geotop_boundary_subdivision_simplex_misses_interior_point_dev34
        [OF h\<sigma> hsub hc hA])
  have hsing: "geotop_convex_hull {c} = {c}"
    using geotop_convex_hull_eq_HOL[of "{c}"] by (by100 simp)
  have hsub_hull: "insert c A \<subseteq> geotop_convex_hull (insert c A)"
    unfolding geotop_convex_hull_eq_HOL by (rule hull_subset)
  have ha_hull: "a \<in> geotop_convex_hull (insert c A)"
    using hsub_hull ha by (by100 blast)
  have "a = c"
    using heq hsing ha_hull by (by100 blast)
  show False
    using hc_not_A ha \<open>a = c\<close> by (by100 blast)
qed

lemma geotop_boundary_subdivision_simplex_subset_2simplex_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hA: "A \<in> F"
  shows "A \<subseteq> \<sigma>"
proof -
  have href:
      "geotop_refines F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
    using hsub unfolding geotop_is_subdivision_def by (by100 blast)
  obtain \<rho> where h\<rho>:
      "\<rho> \<in> geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2"
    and hA\<rho>: "A \<subseteq> \<rho>"
    using href hA unfolding geotop_refines_def by (by100 blast)
  have hproper: "geotop_is_face \<rho> \<sigma> \<and> \<rho> \<noteq> \<sigma>"
    by (rule geotop_2simplex_comb_boundary_member_proper_face_dev34[OF h\<sigma> h\<rho>])
  have h\<rho>sub: "\<rho> \<subseteq> \<sigma>"
    by (rule geotop_is_face_imp_subset[OF conjunct1[OF hproper]])
  show ?thesis
    using hA\<rho> h\<rho>sub by (by100 blast)
qed

lemma geotop_boundary_subdivision_cone_hull_subset_2simplex_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hA: "A \<in> F"
  shows "geotop_convex_hull (insert c A) \<subseteq> \<sigma>"
proof -
  have hA\<sigma>: "A \<subseteq> \<sigma>"
    by (rule geotop_boundary_subdivision_simplex_subset_2simplex_dev34
        [OF h\<sigma> hsub hA])
  have hc\<sigma>: "c \<in> \<sigma>"
    using hc interior_subset by (by100 blast)
  have hinsert: "insert c A \<subseteq> \<sigma>"
    using hA\<sigma> hc\<sigma> by (by100 blast)
  have h\<sigma>simplex: "geotop_is_simplex \<sigma>"
    by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>])
  have hHOL: "convex hull (insert c A) \<subseteq> \<sigma>"
    by (rule GeoTopBase0.geotop_finite_subset_simplex_hull_subset
        [OF h\<sigma>simplex hinsert])
  show ?thesis
    using hHOL geotop_convex_hull_eq_HOL[of "insert c A"] by (by100 simp)
qed

lemma geotop_boundary_cone_definition_refines_2simplex_face_complex_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "geotop_refines L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
  unfolding geotop_refines_def
proof
  fix \<tau>
  assume h\<tau>L: "\<tau> \<in> L'"
  have htarget: "\<sigma> \<in> {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    by (by100 simp)
  show "\<exists>\<rho>\<in>{\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}. \<tau> \<subseteq> \<rho>"
  proof (cases "\<tau> = geotop_convex_hull {c}")
    case True
    have hsing: "geotop_convex_hull {c} = {c}"
      using geotop_convex_hull_eq_HOL[of "{c}"] by (by100 simp)
    have hc\<sigma>: "c \<in> \<sigma>"
      using hc interior_subset by (by100 blast)
    have h\<tau>singleton: "\<tau> = {c}"
      using True hsing by (by100 simp)
    have "\<tau> \<subseteq> \<sigma>"
      using h\<tau>singleton hc\<sigma> by (by100 blast)
    show ?thesis
      using htarget \<open>\<tau> \<subseteq> \<sigma>\<close> by (by100 blast)
  next
    case False
    have hcases:
      "\<tau> \<in> F
        \<or> (\<exists>A. A \<in> F \<and> A \<noteq> {} \<and> \<tau> = geotop_convex_hull (insert c A))"
      using hL h\<tau>L False by (by100 blast)
    from hcases show ?thesis
    proof
      assume h\<tau>F: "\<tau> \<in> F"
      have "\<tau> \<subseteq> \<sigma>"
        by (rule geotop_boundary_subdivision_simplex_subset_2simplex_dev34
            [OF h\<sigma> hsub h\<tau>F])
      show ?thesis
        using htarget \<open>\<tau> \<subseteq> \<sigma>\<close> by (by100 blast)
    next
      assume "\<exists>A. A \<in> F \<and> A \<noteq> {} \<and> \<tau> = geotop_convex_hull (insert c A)"
      then obtain A where hAF: "A \<in> F"
        and h\<tau>eq: "\<tau> = geotop_convex_hull (insert c A)"
        by (by100 blast)
      have hcone_sub: "geotop_convex_hull (insert c A) \<subseteq> \<sigma>"
        by (rule geotop_boundary_subdivision_cone_hull_subset_2simplex_dev34
            [OF h\<sigma> hsub hc hAF])
      have "\<tau> \<subseteq> \<sigma>"
        using h\<tau>eq hcone_sub by (by100 simp)
      show ?thesis
        using htarget \<open>\<tau> \<subseteq> \<sigma>\<close> by (by100 blast)
    qed
  qed
qed

lemma geotop_boundary_cone_definition_members_subset_2simplex_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  assumes h\<tau>: "\<tau> \<in> L'"
  shows "\<tau> \<subseteq> \<sigma>"
proof -
  have href: "geotop_refines L' {\<rho>. geotop_is_face \<rho> \<sigma> \<or> \<rho> = \<sigma>}"
    by (rule geotop_boundary_cone_definition_refines_2simplex_face_complex_dev34
        [OF h\<sigma> hsub hc hL])
  have href_unfold:
      "\<forall>g\<in>L'. \<exists>h\<in>{\<rho>. geotop_is_face \<rho> \<sigma> \<or> \<rho> = \<sigma>}. g \<subseteq> h"
    using href unfolding geotop_refines_def by (by100 simp)
  obtain \<rho> where h\<rho>: "\<rho> \<in> {\<rho>. geotop_is_face \<rho> \<sigma> \<or> \<rho> = \<sigma>}"
    and h\<tau>\<rho>: "\<tau> \<subseteq> \<rho>"
    using href_unfold h\<tau> by (by100 fast)
  have h\<rho>\<sigma>: "\<rho> \<subseteq> \<sigma>"
  proof -
    have "geotop_is_face \<rho> \<sigma> \<or> \<rho> = \<sigma>"
      using h\<rho> by (by100 simp)
    thus ?thesis
    proof
      assume hface: "geotop_is_face \<rho> \<sigma>"
      show ?thesis
        by (rule geotop_is_face_imp_subset[OF hface])
    next
      assume "\<rho> = \<sigma>"
      show ?thesis
        using \<open>\<rho> = \<sigma>\<close> by (by100 simp)
    qed
  qed
  show ?thesis
    using h\<tau>\<rho> h\<rho>\<sigma> by (by100 blast)
qed

lemma geotop_boundary_cone_definition_polyhedron_subset_2simplex_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "geotop_polyhedron L' \<subseteq> \<sigma>"
proof
  fix x
  assume hx: "x \<in> geotop_polyhedron L'"
  obtain \<tau> where h\<tau>L: "\<tau> \<in> L'" and hx\<tau>: "x \<in> \<tau>"
    using hx unfolding geotop_polyhedron_def by (by100 blast)
  have h\<tau>sub: "\<tau> \<subseteq> \<sigma>"
    by (rule geotop_boundary_cone_definition_members_subset_2simplex_dev34
        [OF h\<sigma> hsub hc hL h\<tau>L])
  show "x \<in> \<sigma>"
    using h\<tau>sub hx\<tau> by (by100 blast)
qed

lemma geotop_boundary_cone_definition_old_polyhedron_subset_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "geotop_polyhedron F \<subseteq> geotop_polyhedron L'"
proof
  fix x
  assume hx: "x \<in> geotop_polyhedron F"
  obtain A where hAF: "A \<in> F" and hxA: "x \<in> A"
    using hx unfolding geotop_polyhedron_def by (by100 blast)
  have hAL: "A \<in> L'"
    using hL hAF by (by100 simp)
  show "x \<in> geotop_polyhedron L'"
    unfolding geotop_polyhedron_def using hAL hxA by (by100 blast)
qed

lemma geotop_boundary_cone_definition_cone_point_in_polyhedron_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "c \<in> geotop_polyhedron L'"
proof -
  have hcL: "geotop_convex_hull {c} \<in> L'"
    using hL by (by100 simp)
  have hsing: "geotop_convex_hull {c} = {c}"
    using geotop_convex_hull_eq_HOL[of "{c}"] by (by100 simp)
  show ?thesis
    unfolding geotop_polyhedron_def using hcL hsing by (by100 blast)
qed

lemma geotop_boundary_cone_definition_segment_to_old_polyhedron_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  assumes hy: "y \<in> geotop_polyhedron F"
  assumes ht0: "0 \<le> t"
  assumes ht1: "t \<le> 1"
  shows "(1 - t) *\<^sub>R c + t *\<^sub>R y \<in> geotop_polyhedron L'"
proof -
  obtain A where hAF: "A \<in> F" and hyA: "y \<in> A"
    using hy unfolding geotop_polyhedron_def by (by100 blast)
  have hAne: "A \<noteq> {}"
    using hyA by (by100 blast)
  have hconeL: "geotop_convex_hull (insert c A) \<in> L'"
    using hL hAF hAne by (by100 blast)
  have hc_hull: "c \<in> geotop_convex_hull (insert c A)"
  proof -
    have "c \<in> insert c A"
      by (by100 simp)
    moreover have "insert c A \<subseteq> geotop_convex_hull (insert c A)"
      unfolding geotop_convex_hull_eq_HOL by (rule hull_subset)
    ultimately show ?thesis
      by (by100 blast)
  qed
  have hy_hull: "y \<in> geotop_convex_hull (insert c A)"
  proof -
    have "y \<in> insert c A"
      using hyA by (by100 blast)
    moreover have "insert c A \<subseteq> geotop_convex_hull (insert c A)"
      unfolding geotop_convex_hull_eq_HOL by (rule hull_subset)
    ultimately show ?thesis
      by (by100 blast)
  qed
  have hconv: "convex (geotop_convex_hull (insert c A))"
    unfolding geotop_convex_hull_eq_HOL by (rule convex_convex_hull)
  have h1mt: "0 \<le> 1 - t"
    using ht1 by (by100 simp)
  have hsum: "(1 - t) + t = 1"
    by (by100 simp)
  have hpoint:
      "(1 - t) *\<^sub>R c + t *\<^sub>R y
        \<in> geotop_convex_hull (insert c A)"
    by (rule convexD[OF hconv hc_hull hy_hull h1mt ht0 hsum])
  show ?thesis
    unfolding geotop_polyhedron_def using hconeL hpoint by (by100 blast)
qed

lemma geotop_boundary_cone_definition_closed_segment_to_old_polyhedron_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  assumes hy: "y \<in> geotop_polyhedron F"
  shows "closed_segment c y \<subseteq> geotop_polyhedron L'"
proof
  fix x
  assume hx: "x \<in> closed_segment c y"
  obtain t where ht0: "0 \<le> t" and ht1: "t \<le> 1"
    and hx_eq: "x = (1 - t) *\<^sub>R c + t *\<^sub>R y"
    using hx unfolding closed_segment_def by (by100 blast)
  have "(1 - t) *\<^sub>R c + t *\<^sub>R y \<in> geotop_polyhedron L'"
    by (rule geotop_boundary_cone_definition_segment_to_old_polyhedron_dev34
        [OF hL hy ht0 ht1])
  show "x \<in> geotop_polyhedron L'"
    using hx_eq \<open>(1 - t) *\<^sub>R c + t *\<^sub>R y \<in> geotop_polyhedron L'\<close>
    by (by100 simp)
qed

lemma geotop_boundary_cone_definition_polyhedron_contains_radial_cover_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  assumes hcover:
    "\<forall>x\<in>\<sigma>. x = c \<or>
      (\<exists>y\<in>geotop_polyhedron F. x \<in> closed_segment c y)"
  shows "\<sigma> \<subseteq> geotop_polyhedron L'"
proof
  fix x
  assume hx: "x \<in> \<sigma>"
  have hcase:
      "x = c \<or> (\<exists>y\<in>geotop_polyhedron F. x \<in> closed_segment c y)"
    using hcover hx by (by100 blast)
  show "x \<in> geotop_polyhedron L'"
  proof (rule disjE[OF hcase])
    assume "x = c"
    have "c \<in> geotop_polyhedron L'"
      by (rule geotop_boundary_cone_definition_cone_point_in_polyhedron_dev34
          [OF hL])
    thus ?thesis
      using \<open>x = c\<close> by (by100 simp)
  next
    assume "\<exists>y\<in>geotop_polyhedron F. x \<in> closed_segment c y"
    then obtain y where hy: "y \<in> geotop_polyhedron F"
      and hxseg: "x \<in> closed_segment c y"
      by (by100 blast)
    have hseg_sub: "closed_segment c y \<subseteq> geotop_polyhedron L'"
      by (rule geotop_boundary_cone_definition_closed_segment_to_old_polyhedron_dev34
          [OF hL hy])
    show ?thesis
      using hseg_sub hxseg by (by100 blast)
  qed
qed

lemma geotop_boundary_cone_definition_polyhedron_eq_2simplex_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "geotop_polyhedron L' = \<sigma>"
proof
  show "geotop_polyhedron L' \<subseteq> \<sigma>"
    by (rule geotop_boundary_cone_definition_polyhedron_subset_2simplex_dev34
        [OF h\<sigma> hsub hc hL])
  have hcover:
      "\<forall>x\<in>\<sigma>. x = c \<or>
        (\<exists>y\<in>geotop_polyhedron F. x \<in> closed_segment c y)"
    by (rule geotop_boundary_subdivision_radial_cover_2simplex_dev34
        [OF h\<sigma> hsub hc])
  show "\<sigma> \<subseteq> geotop_polyhedron L'"
    by (rule geotop_boundary_cone_definition_polyhedron_contains_radial_cover_dev34
        [OF hL hcover])
qed

lemma geotop_boundary_cone_definition_finite_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "finite L'"
proof -
  have hF_fin: "finite F"
    by (rule geotop_boundary_subdivision_finite_dev34[OF h\<sigma> hsub])
  have hcones_sub:
      "{geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}}
        \<subseteq> (\<lambda>A. geotop_convex_hull (insert c A)) ` F"
    by (by100 blast)
  have hcones_fin:
      "finite {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}}"
    by (rule finite_subset[OF hcones_sub]) (use hF_fin in \<open>by100 simp\<close>)
  show ?thesis
    using hL hF_fin hcones_fin by (by100 simp)
qed

lemma geotop_boundary_cone_definition_local_finite_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "\<forall>\<tau>\<in>L'. \<exists>U. open U \<and> \<tau> \<subseteq> U
      \<and> finite {\<rho> \<in> L'. \<rho> \<inter> U \<noteq> {}}"
proof
  fix \<tau>
  assume h\<tau>L: "\<tau> \<in> L'"
  have hL_fin: "finite L'"
    by (rule geotop_boundary_cone_definition_finite_dev34[OF h\<sigma> hsub hL])
  have hmeet_sub: "{\<rho> \<in> L'. \<rho> \<inter> UNIV \<noteq> {}} \<subseteq> L'"
    by (by100 blast)
  have hmeet_fin: "finite {\<rho> \<in> L'. \<rho> \<inter> UNIV \<noteq> {}}"
    by (rule finite_subset[OF hmeet_sub hL_fin])
  show "\<exists>U. open U \<and> \<tau> \<subseteq> U \<and> finite {\<rho> \<in> L'. \<rho> \<inter> U \<noteq> {}}"
    using hmeet_fin by (intro exI[of _ UNIV]) (by100 simp)
qed

lemma geotop_boundary_cone_definition_target_complex_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  shows "geotop_is_complex {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
  by (rule geotop_simplex_dim_face_complex_is_complex_R2[OF h\<sigma>])

lemma geotop_boundary_cone_definition_polyhedron_eq_target_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "geotop_polyhedron L' =
      geotop_polyhedron {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
proof -
  have hL_poly: "geotop_polyhedron L' = \<sigma>"
    by (rule geotop_boundary_cone_definition_polyhedron_eq_2simplex_dev34
        [OF h\<sigma> hsub hc hL])
  have htarget_poly:
      "geotop_polyhedron {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} = \<sigma>"
    by (rule geotop_2simplex_face_complex_polyhedron_eq_dev34[OF h\<sigma>])
  show ?thesis
    using hL_poly htarget_poly by (by100 simp)
qed

lemma geotop_boundary_subdivision_simplex_subset_rel_frontier_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hA: "A \<in> F"
  shows "A \<subseteq> rel_frontier \<sigma>"
proof
  fix x
  assume hxA: "x \<in> A"
  have hA_sub: "A \<subseteq> \<sigma>"
    by (rule geotop_boundary_subdivision_simplex_subset_2simplex_dev34
        [OF h\<sigma> hsub hA])
  have hx\<sigma>: "x \<in> \<sigma>"
    using hA_sub hxA by (by100 blast)
  have hdisj: "geotop_polyhedron F \<inter> interior \<sigma> = {}"
    by (rule geotop_boundary_subdivision_polyhedron_disjoint_HOL_interior_dev34
        [OF h\<sigma> hsub])
  have hxFpoly: "x \<in> geotop_polyhedron F"
    unfolding geotop_polyhedron_def using hA hxA by (by100 blast)
  have hx_not_int: "x \<notin> interior \<sigma>"
    using hdisj hxFpoly by (by100 blast)
  have hhyper: "geotop_hyperplane_dim (affine hull \<sigma>) 2"
    by (rule geotop_simplex_dim_imp_hyperplane_dim[OF h\<sigma>])
  have hdim\<sigma>: "aff_dim \<sigma> = 2"
    using geotop_hyperplane_dim_imp_affine_aff_dim[OF hhyper] by (by100 simp)
  have hdim_UNIV: "aff_dim \<sigma> = int (DIM(real^2))"
    using hdim\<sigma> by (by100 simp)
  have hrel_eq_int: "rel_interior \<sigma> = interior \<sigma>"
    by (rule interior_rel_interior[OF hdim_UNIV])
  have hx_closure: "x \<in> closure \<sigma>"
    using hx\<sigma> closure_subset by (by100 blast)
  show "x \<in> rel_frontier \<sigma>"
    unfolding rel_frontier_def
    using hx_closure hx_not_int hrel_eq_int by (by100 simp)
qed

lemma geotop_boundary_subdivision_cone_inter_eq_cone_inter_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hA: "A \<in> F"
  assumes hB: "B \<in> F"
  shows "geotop_convex_hull (insert c A) \<inter> geotop_convex_hull (insert c B)
      = geotop_convex_hull (insert c (A \<inter> B))"
proof -
  have hF_complex: "geotop_is_complex F"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hsub])
  have hF_simplexes: "\<forall>\<rho>\<in>F. geotop_is_simplex \<rho>"
    by (rule geotop_is_complex_simplex[OF hF_complex])
  have hA_simplex: "geotop_is_simplex A"
    using hF_simplexes hA by (by100 blast)
  have hB_simplex: "geotop_is_simplex B"
    using hF_simplexes hB by (by100 blast)
  have h\<sigma>simplex: "geotop_is_simplex \<sigma>"
    by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>])
  have h\<sigma>conv: "convex \<sigma>"
    using GeoTopBase0.geotop_simplex_is_convex[OF h\<sigma>simplex]
    unfolding geotop_convex_iff_HOL_convex .
  have hA_conv: "convex A"
    using GeoTopBase0.geotop_simplex_is_convex[OF hA_simplex]
    unfolding geotop_convex_iff_HOL_convex .
  have hB_conv: "convex B"
    using GeoTopBase0.geotop_simplex_is_convex[OF hB_simplex]
    unfolding geotop_convex_iff_HOL_convex .
  have hA_rel: "A \<subseteq> rel_frontier \<sigma>"
    by (rule geotop_boundary_subdivision_simplex_subset_rel_frontier_dev34
        [OF h\<sigma> hsub hA])
  have hB_rel: "B \<subseteq> rel_frontier \<sigma>"
    by (rule geotop_boundary_subdivision_simplex_subset_rel_frontier_dev34
        [OF h\<sigma> hsub hB])
  have hhyper: "geotop_hyperplane_dim (affine hull \<sigma>) 2"
    by (rule geotop_simplex_dim_imp_hyperplane_dim[OF h\<sigma>])
  have hdim\<sigma>: "aff_dim \<sigma> = 2"
    using geotop_hyperplane_dim_imp_affine_aff_dim[OF hhyper] by (by100 simp)
  have hdim_UNIV: "aff_dim \<sigma> = int (DIM(real^2))"
    using hdim\<sigma> by (by100 simp)
  have hrel_eq_int: "rel_interior \<sigma> = interior \<sigma>"
    by (rule interior_rel_interior[OF hdim_UNIV])
  have hc_rel: "c \<in> rel_interior \<sigma>"
    using hc hrel_eq_int by (by100 simp)
  have hHOL:
      "convex hull (insert c A) \<inter> convex hull (insert c B)
        = convex hull (insert c (A \<inter> B))"
    by (rule convex_hull_insert_Int_eq
        [OF hc_rel hA_rel hB_rel h\<sigma>conv hA_conv hB_conv])
  show ?thesis
    using hHOL geotop_convex_hull_eq_HOL[of "insert c A"]
      geotop_convex_hull_eq_HOL[of "insert c B"]
      geotop_convex_hull_eq_HOL[of "insert c (A \<inter> B)"]
    by (by100 simp)
qed

lemma geotop_boundary_subdivision_old_inter_cone_eq_old_inter_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hA: "A \<in> F"
  assumes hB: "B \<in> F"
  shows "A \<inter> geotop_convex_hull (insert c B) = A \<inter> B"
proof -
  have hF_complex: "geotop_is_complex F"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hsub])
  have hF_simplexes: "\<forall>\<rho>\<in>F. geotop_is_simplex \<rho>"
    by (rule geotop_is_complex_simplex[OF hF_complex])
  have hB_simplex: "geotop_is_simplex B"
    using hF_simplexes hB by (by100 blast)
  have h\<sigma>simplex: "geotop_is_simplex \<sigma>"
    by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>])
  have h\<sigma>conv: "convex \<sigma>"
    using GeoTopBase0.geotop_simplex_is_convex[OF h\<sigma>simplex]
    unfolding geotop_convex_iff_HOL_convex .
  have hB_conv: "convex B"
    using GeoTopBase0.geotop_simplex_is_convex[OF hB_simplex]
    unfolding geotop_convex_iff_HOL_convex .
  have hB_sub: "B \<subseteq> \<sigma>"
    by (rule geotop_boundary_subdivision_simplex_subset_2simplex_dev34
        [OF h\<sigma> hsub hB])
  have hA_rel: "A \<subseteq> rel_frontier \<sigma>"
    by (rule geotop_boundary_subdivision_simplex_subset_rel_frontier_dev34
        [OF h\<sigma> hsub hA])
  have hA_disj: "disjnt A (rel_interior \<sigma>)"
    using hA_rel unfolding rel_frontier_def disjnt_def by (by100 blast)
  have hhyper: "geotop_hyperplane_dim (affine hull \<sigma>) 2"
    by (rule geotop_simplex_dim_imp_hyperplane_dim[OF h\<sigma>])
  have hdim\<sigma>: "aff_dim \<sigma> = 2"
    using geotop_hyperplane_dim_imp_affine_aff_dim[OF hhyper] by (by100 simp)
  have hdim_UNIV: "aff_dim \<sigma> = int (DIM(real^2))"
    using hdim\<sigma> by (by100 simp)
  have hrel_eq_int: "rel_interior \<sigma> = interior \<sigma>"
    by (rule interior_rel_interior[OF hdim_UNIV])
  have hc_rel: "c \<in> rel_interior \<sigma>"
    using hc hrel_eq_int by (by100 simp)
  have hHOL:
      "A \<inter> convex hull (insert c B) = A \<inter> convex hull B"
    by (rule Int_convex_hull_insert_rel_exterior
        [OF h\<sigma>conv hB_sub hc_rel hA_disj])
  have hB_hull: "convex hull B = B"
    using hB_conv convex_hull_eq[of B] by (by100 simp)
  show ?thesis
    using hHOL hB_hull geotop_convex_hull_eq_HOL[of "insert c B"]
    by (by100 simp)
qed

lemma geotop_boundary_subdivision_old_face_is_face_of_cone_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hB: "B \<in> F"
  assumes hface: "geotop_is_face D B"
  shows "geotop_is_face D (geotop_convex_hull (insert c B))"
proof -
  obtain V W where hBV: "geotop_simplex_vertices B V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and hD_eq: "D = geotop_convex_hull W"
    and hDW: "geotop_simplex_vertices D W"
    by (rule geotop_face_witness_simplex_vertices[OF hface])
  have hB_eq: "B = geotop_convex_hull V"
    using hBV unfolding geotop_simplex_vertices_def by (by100 blast)
  have hV_ai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF hBV])
  have hc_not_aff_B: "c \<notin> affine hull B"
    by (rule geotop_boundary_subdivision_simplex_affine_hull_misses_interior_point_dev34
        [OF h\<sigma> hsub hc hB])
  have hAff_B: "affine hull B = affine hull V"
    using hB_eq geotop_convex_hull_eq_HOL[of V] affine_hull_convex_hull[of V]
    by (by100 simp)
  have hc_not_aff_V: "c \<notin> affine hull V"
    using hc_not_aff_B hAff_B by (by100 simp)
  have hV_fin: "finite V"
    using hBV unfolding geotop_simplex_vertices_def by (by100 blast)
  have hinsert_ai: "\<not> affine_dependent (insert c V)"
    by (rule affine_independent_insert[OF hV_ai hc_not_aff_V])
  have hinsert_fin: "finite (insert c V)"
    using hV_fin by (by100 simp)
  have hinsert_ne: "insert c V \<noteq> {}"
    by (by100 simp)
  have hconeV:
      "geotop_simplex_vertices (geotop_convex_hull (insert c V)) (insert c V)"
    by (rule geotop_AI_finite_ne_is_simplex_vertices
        [OF hinsert_fin hinsert_ne hinsert_ai])
  have hcone_eq:
      "geotop_convex_hull (insert c B) =
        geotop_convex_hull (insert c V)"
  proof -
    have "geotop_convex_hull (insert c B) =
        geotop_convex_hull (insert c (geotop_convex_hull V))"
      using hB_eq by (by100 simp)
    also have "... = geotop_convex_hull (insert c V)"
    proof -
      have hHOL:
          "convex hull (insert c V) =
            convex hull (insert c (convex hull V))"
        by (rule hull_insert)
      show ?thesis
        using hHOL geotop_convex_hull_eq_HOL[of "insert c V"]
          geotop_convex_hull_eq_HOL[of "insert c (geotop_convex_hull V)"]
          geotop_convex_hull_eq_HOL[of V]
        by (by100 simp)
    qed
    finally show ?thesis .
  qed
  have hconeV_B:
      "geotop_simplex_vertices (geotop_convex_hull (insert c B)) (insert c V)"
    using hconeV hcone_eq by (by100 simp)
  have hW_sub_cone: "W \<subseteq> insert c V"
    using hW_sub by (by100 blast)
  show ?thesis
    unfolding geotop_is_face_def
    using hconeV_B hW_ne hW_sub_cone hD_eq by (by100 blast)
qed

lemma geotop_boundary_subdivision_new_singleton_is_face_of_cone_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hB: "B \<in> F"
  shows "geotop_is_face (geotop_convex_hull {c})
    (geotop_convex_hull (insert c B))"
proof -
  have hF_complex: "geotop_is_complex F"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hsub])
  have hF_simplexes: "\<forall>\<rho>\<in>F. geotop_is_simplex \<rho>"
    by (rule geotop_is_complex_simplex[OF hF_complex])
  have hB_simplex: "geotop_is_simplex B"
    using hF_simplexes hB by (by100 blast)
  obtain V where hBV: "geotop_simplex_vertices B V"
    using hB_simplex unfolding geotop_is_simplex_def geotop_simplex_vertices_def
    by (by100 blast)
  have hB_eq: "B = geotop_convex_hull V"
    using hBV unfolding geotop_simplex_vertices_def by (by100 blast)
  have hV_ai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF hBV])
  have hc_not_aff_B: "c \<notin> affine hull B"
    by (rule geotop_boundary_subdivision_simplex_affine_hull_misses_interior_point_dev34
        [OF h\<sigma> hsub hc hB])
  have hAff_B: "affine hull B = affine hull V"
    using hB_eq geotop_convex_hull_eq_HOL[of V] affine_hull_convex_hull[of V]
    by (by100 simp)
  have hc_not_aff_V: "c \<notin> affine hull V"
    using hc_not_aff_B hAff_B by (by100 simp)
  have hV_fin: "finite V"
    using hBV unfolding geotop_simplex_vertices_def by (by100 blast)
  have hinsert_ai: "\<not> affine_dependent (insert c V)"
    by (rule affine_independent_insert[OF hV_ai hc_not_aff_V])
  have hinsert_fin: "finite (insert c V)"
    using hV_fin by (by100 simp)
  have hinsert_ne: "insert c V \<noteq> {}"
    by (by100 simp)
  have hconeV:
      "geotop_simplex_vertices (geotop_convex_hull (insert c V)) (insert c V)"
    by (rule geotop_AI_finite_ne_is_simplex_vertices
        [OF hinsert_fin hinsert_ne hinsert_ai])
  have hcone_eq:
      "geotop_convex_hull (insert c B) =
        geotop_convex_hull (insert c V)"
  proof -
    have "geotop_convex_hull (insert c B) =
        geotop_convex_hull (insert c (geotop_convex_hull V))"
      using hB_eq by (by100 simp)
    also have "... = geotop_convex_hull (insert c V)"
    proof -
      have hHOL:
          "convex hull (insert c V) =
            convex hull (insert c (convex hull V))"
        by (rule hull_insert)
      show ?thesis
        using hHOL geotop_convex_hull_eq_HOL[of "insert c V"]
          geotop_convex_hull_eq_HOL[of "insert c (geotop_convex_hull V)"]
          geotop_convex_hull_eq_HOL[of V]
        by (by100 simp)
    qed
    finally show ?thesis .
  qed
  have hconeV_B:
      "geotop_simplex_vertices (geotop_convex_hull (insert c B)) (insert c V)"
    using hconeV hcone_eq by (by100 simp)
  have hsingleton_sub: "{c} \<subseteq> insert c V"
    by (by100 blast)
  show ?thesis
    unfolding geotop_is_face_def
    using hconeV_B hsingleton_sub by (intro exI[of _ "insert c V"] exI[of _ "{c}"])
      (by100 simp)
qed

lemma geotop_boundary_subdivision_cone_face_is_face_of_cone_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hB: "B \<in> F"
  assumes hface: "geotop_is_face D B"
  shows "geotop_is_face (geotop_convex_hull (insert c D))
    (geotop_convex_hull (insert c B))"
proof -
  obtain V W where hBV: "geotop_simplex_vertices B V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and hD_eq: "D = geotop_convex_hull W"
    and hDW: "geotop_simplex_vertices D W"
    by (rule geotop_face_witness_simplex_vertices[OF hface])
  have hB_eq: "B = geotop_convex_hull V"
    using hBV unfolding geotop_simplex_vertices_def by (by100 blast)
  have hV_ai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF hBV])
  have hc_not_aff_B: "c \<notin> affine hull B"
    by (rule geotop_boundary_subdivision_simplex_affine_hull_misses_interior_point_dev34
        [OF h\<sigma> hsub hc hB])
  have hAff_B: "affine hull B = affine hull V"
    using hB_eq geotop_convex_hull_eq_HOL[of V] affine_hull_convex_hull[of V]
    by (by100 simp)
  have hc_not_aff_V: "c \<notin> affine hull V"
    using hc_not_aff_B hAff_B by (by100 simp)
  have hV_fin: "finite V"
    using hBV unfolding geotop_simplex_vertices_def by (by100 blast)
  have hinsert_ai: "\<not> affine_dependent (insert c V)"
    by (rule affine_independent_insert[OF hV_ai hc_not_aff_V])
  have hinsert_fin: "finite (insert c V)"
    using hV_fin by (by100 simp)
  have hinsert_ne: "insert c V \<noteq> {}"
    by (by100 simp)
  have hconeV:
      "geotop_simplex_vertices (geotop_convex_hull (insert c V)) (insert c V)"
    by (rule geotop_AI_finite_ne_is_simplex_vertices
        [OF hinsert_fin hinsert_ne hinsert_ai])
  have hcone_eq:
      "geotop_convex_hull (insert c B) =
        geotop_convex_hull (insert c V)"
  proof -
    have "geotop_convex_hull (insert c B) =
        geotop_convex_hull (insert c (geotop_convex_hull V))"
      using hB_eq by (by100 simp)
    also have "... = geotop_convex_hull (insert c V)"
    proof -
      have hHOL:
          "convex hull (insert c V) =
            convex hull (insert c (convex hull V))"
        by (rule hull_insert)
      show ?thesis
        using hHOL geotop_convex_hull_eq_HOL[of "insert c V"]
          geotop_convex_hull_eq_HOL[of "insert c (geotop_convex_hull V)"]
          geotop_convex_hull_eq_HOL[of V]
        by (by100 simp)
    qed
    finally show ?thesis .
  qed
  have hconeV_B:
      "geotop_simplex_vertices (geotop_convex_hull (insert c B)) (insert c V)"
    using hconeV hcone_eq by (by100 simp)
  have hW_sub_cone: "insert c W \<subseteq> insert c V"
    using hW_sub by (by100 blast)
  have htarget_eq:
      "geotop_convex_hull (insert c D) = geotop_convex_hull (insert c W)"
  proof -
    have "geotop_convex_hull (insert c D) =
        geotop_convex_hull (insert c (geotop_convex_hull W))"
      using hD_eq by (by100 simp)
    also have "... = geotop_convex_hull (insert c W)"
    proof -
      have hHOL:
          "convex hull (insert c W) =
            convex hull (insert c (convex hull W))"
        by (rule hull_insert)
      show ?thesis
        using hHOL geotop_convex_hull_eq_HOL[of "insert c W"]
          geotop_convex_hull_eq_HOL[of "insert c (geotop_convex_hull W)"]
          geotop_convex_hull_eq_HOL[of W]
        by (by100 simp)
    qed
    finally show ?thesis .
  qed
  show ?thesis
    unfolding geotop_is_face_def
    using hconeV_B hW_sub_cone htarget_eq
    by (intro exI[of _ "insert c V"] exI[of _ "insert c W"]) (by100 simp)
qed

lemma geotop_boundary_cone_definition_subdivision_obligations_except_source_complex_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "geotop_is_complex {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_refines L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_polyhedron L' =
        geotop_polyhedron {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
proof -
  have htarget_complex:
      "geotop_is_complex {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    by (rule geotop_boundary_cone_definition_target_complex_dev34[OF h\<sigma>])
  have href:
      "geotop_refines L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    by (rule geotop_boundary_cone_definition_refines_2simplex_face_complex_dev34
        [OF h\<sigma> hsub hc hL])
  have hpoly:
      "geotop_polyhedron L' =
        geotop_polyhedron {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    by (rule geotop_boundary_cone_definition_polyhedron_eq_target_dev34
        [OF h\<sigma> hsub hc hL])
  show ?thesis
    using htarget_complex href hpoly by (by100 blast)
qed

lemma geotop_boundary_subdivision_new_interior_vertex_exists_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  shows "\<exists>c. c \<in> interior \<sigma> \<and> c \<notin> geotop_complex_vertices F"
  (**
    Figure 4.10's new vertex: choose any point in the nonempty interior of
    the 2-simplex; by the boundary-subdivision disjointness lemma it is not
    an old boundary vertex. **)
proof -
  have hint_nonempty: "interior \<sigma> \<noteq> {}"
    by (rule geotop_2simplex_HOL_interior_nonempty_dev34[OF h\<sigma>])
  obtain c where hc_int: "c \<in> interior \<sigma>"
    using hint_nonempty by (by100 blast)
  have hdisj: "geotop_complex_vertices F \<inter> interior \<sigma> = {}"
    by (rule geotop_boundary_subdivision_vertices_disjoint_HOL_interior_dev34
        [OF h\<sigma> hsub])
  have hc_new: "c \<notin> geotop_complex_vertices F"
    using hdisj hc_int by (by100 blast)
  show ?thesis
    using hc_int hc_new by (by100 blast)
qed

lemma geotop_boundary_cone_definition_contains_new_vertex_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "geotop_convex_hull {c} \<in> L'"
  using hL by (by100 simp)

lemma geotop_boundary_cone_definition_contains_old_simplex_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  assumes hA: "A \<in> F"
  shows "A \<in> L'"
  using hL hA by (by100 simp)

lemma geotop_boundary_cone_definition_contains_cone_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  assumes hA: "A \<in> F"
  assumes hAne: "A \<noteq> {}"
  shows "geotop_convex_hull (insert c A) \<in> L'"
  using hL hA hAne by (by100 blast)

lemma geotop_boundary_cone_definition_member_cases_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  assumes h\<tau>: "\<tau> \<in> L'"
  shows "\<tau> = geotop_convex_hull {c}
      \<or> \<tau> \<in> F
      \<or> (\<exists>A. A \<in> F \<and> A \<noteq> {} \<and> \<tau> = geotop_convex_hull (insert c A))"
  using hL h\<tau> by (by100 blast)

lemma geotop_boundary_cone_definition_member_cases_without_new_singleton_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  assumes h\<tau>: "\<tau> \<in> L'"
  assumes hnot: "\<tau> \<noteq> geotop_convex_hull {c}"
  shows "\<tau> \<in> F
      \<or> (\<exists>A. A \<in> F \<and> A \<noteq> {} \<and> \<tau> = geotop_convex_hull (insert c A))"
  using geotop_boundary_cone_definition_member_cases_dev34[OF hL h\<tau>] hnot
  by (by100 blast)

lemma geotop_boundary_cone_definition_new_vertex_in_vertices_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "c \<in> geotop_complex_vertices L'"
proof -
  have hmem: "geotop_convex_hull {c} \<in> L'"
    by (rule geotop_boundary_cone_definition_contains_new_vertex_dev34[OF hL])
  have hch: "geotop_convex_hull {c} = {c}"
    using geotop_convex_hull_eq_HOL[of "{c}"] by (by100 simp)
  have hsv: "geotop_simplex_vertices (geotop_convex_hull {c}) {c}"
    using geotop_simplex_vertices_singleton[of c] hch by (by100 simp)
  show ?thesis
    unfolding geotop_complex_vertices_def using hmem hsv by (by100 blast)
qed

lemma geotop_boundary_cone_definition_old_vertices_subset_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "geotop_complex_vertices F \<subseteq> geotop_complex_vertices L'"
proof
  fix v
  assume hv: "v \<in> geotop_complex_vertices F"
  obtain \<sigma> V where h\<sigma>F: "\<sigma> \<in> F"
    and hV: "geotop_simplex_vertices \<sigma> V"
    and hvV: "v \<in> V"
    using hv unfolding geotop_complex_vertices_def by (by100 blast)
  have h\<sigma>L: "\<sigma> \<in> L'"
    by (rule geotop_boundary_cone_definition_contains_old_simplex_dev34[OF hL h\<sigma>F])
  show "v \<in> geotop_complex_vertices L'"
    unfolding geotop_complex_vertices_def using h\<sigma>L hV hvV by (by100 blast)
qed

lemma geotop_boundary_cone_definition_vertices_contains_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "insert c (geotop_complex_vertices F) \<subseteq> geotop_complex_vertices L'"
proof -
  have hc: "c \<in> geotop_complex_vertices L'"
    by (rule geotop_boundary_cone_definition_new_vertex_in_vertices_dev34[OF hL])
  have hFsub: "geotop_complex_vertices F \<subseteq> geotop_complex_vertices L'"
    by (rule geotop_boundary_cone_definition_old_vertices_subset_dev34[OF hL])
  show ?thesis
    using hc hFsub by (by100 blast)
qed

lemma geotop_boundary_cone_definition_old_hull_imp_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  assumes hA: "geotop_convex_hull A \<in> F"
  shows "geotop_convex_hull A \<in> L'"
  by (rule geotop_boundary_cone_definition_contains_old_simplex_dev34[OF hL hA])

lemma geotop_convex_hull_insert_geotop_convex_hull_eq_dev34:
  fixes A :: "(real^2) set"
  shows "geotop_convex_hull (insert c (geotop_convex_hull A))
      = geotop_convex_hull (insert c A)"
proof -
  have hHOL:
      "convex hull (insert c A) = convex hull (insert c (convex hull A))"
    by (rule hull_insert)
  show ?thesis
    using hHOL unfolding geotop_convex_hull_eq_HOL by (by100 simp)
qed

lemma geotop_boundary_subdivision_cone_over_simplex_is_simplex_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hA: "A \<in> F"
  shows "geotop_is_simplex (geotop_convex_hull (insert c A))"
proof -
  have hF_complex: "geotop_is_complex F"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hsub])
  have hF_simplexes: "\<forall>\<tau>\<in>F. geotop_is_simplex \<tau>"
    by (rule conjunct1[OF hF_complex[unfolded geotop_is_complex_def]])
  have hA_simplex: "geotop_is_simplex A"
    using hF_simplexes hA by (by100 blast)
  obtain V m n where hV_fin: "finite V"
    and hV_card: "card V = n + 1"
    and hn_le_m: "n \<le> m"
    and hV_gp: "geotop_general_position V m"
    and hA_eq: "A = geotop_convex_hull V"
    using hA_simplex unfolding geotop_is_simplex_def by (by100 blast)
  have hAV: "geotop_simplex_vertices A V"
    unfolding geotop_simplex_vertices_def
    using hV_fin hV_card hn_le_m hV_gp hA_eq by (by100 blast)
  have hV_ai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF hAV])
  have hc_not_aff_A: "c \<notin> affine hull A"
    by (rule geotop_boundary_subdivision_simplex_affine_hull_misses_interior_point_dev34
        [OF h\<sigma> hsub hc hA])
  have hAff_A: "affine hull A = affine hull V"
    using hA_eq geotop_convex_hull_eq_HOL[of V] affine_hull_convex_hull[of V]
    by (by100 simp)
  have hc_not_aff_V: "c \<notin> affine hull V"
    using hc_not_aff_A hAff_A by (by100 simp)
  have hinsert_ai: "\<not> affine_dependent (insert c V)"
    by (rule affine_independent_insert[OF hV_ai hc_not_aff_V])
  have hinsert_fin: "finite (insert c V)"
    using hV_fin by (by100 simp)
  have hinsert_ne: "insert c V \<noteq> {}"
    by (by100 simp)
  have hconeV:
      "geotop_simplex_vertices (geotop_convex_hull (insert c V)) (insert c V)"
    by (rule geotop_AI_finite_ne_is_simplex_vertices
        [OF hinsert_fin hinsert_ne hinsert_ai])
  have hcone_eq:
      "geotop_convex_hull (insert c A) =
        geotop_convex_hull (insert c V)"
  proof -
    have "geotop_convex_hull (insert c A) =
        geotop_convex_hull (insert c (geotop_convex_hull V))"
      using hA_eq by (by100 simp)
    also have "... = geotop_convex_hull (insert c V)"
      by (rule geotop_convex_hull_insert_geotop_convex_hull_eq_dev34)
    finally show ?thesis .
  qed
  show ?thesis
  proof -
    obtain m' n' where hcone_fin: "finite (insert c V)"
      and hcone_card: "card (insert c V) = n' + 1"
      and hcone_le: "n' \<le> m'"
      and hcone_gp: "geotop_general_position (insert c V) m'"
      and hcone_hull:
        "geotop_convex_hull (insert c V) = geotop_convex_hull (insert c V)"
      using hconeV unfolding geotop_simplex_vertices_def by (by100 blast)
    show ?thesis
      unfolding geotop_is_simplex_def
      using hcone_fin hcone_card hcone_le hcone_gp hcone_eq
      by (intro exI[of _ "insert c V"] exI[of _ m'] exI[of _ n'])
        (by100 simp)
  qed
qed

lemma geotop_boundary_subdivision_cone_simplex_vertices_subset_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hA: "A \<in> F"
  assumes hW:
    "geotop_simplex_vertices (geotop_convex_hull (insert c A)) W"
  shows "W \<subseteq> insert c (geotop_complex_vertices F)"
proof -
  have hF_complex: "geotop_is_complex F"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hsub])
  have hF_simplexes: "\<forall>\<tau>\<in>F. geotop_is_simplex \<tau>"
    by (rule conjunct1[OF hF_complex[unfolded geotop_is_complex_def]])
  have hA_simplex: "geotop_is_simplex A"
    using hF_simplexes hA by (by100 blast)
  obtain V m n where hV_fin: "finite V"
    and hV_card: "card V = n + 1"
    and hn_le_m: "n \<le> m"
    and hV_gp: "geotop_general_position V m"
    and hA_eq: "A = geotop_convex_hull V"
    using hA_simplex unfolding geotop_is_simplex_def by (by100 blast)
  have hAV: "geotop_simplex_vertices A V"
    unfolding geotop_simplex_vertices_def
    using hV_fin hV_card hn_le_m hV_gp hA_eq by (by100 blast)
  have hV_vertices: "V \<subseteq> geotop_complex_vertices F"
    unfolding geotop_complex_vertices_def using hA hAV by (by100 blast)
  have hV_ai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF hAV])
  have hc_not_aff_A: "c \<notin> affine hull A"
    by (rule geotop_boundary_subdivision_simplex_affine_hull_misses_interior_point_dev34
        [OF h\<sigma> hsub hc hA])
  have hAff_A: "affine hull A = affine hull V"
    using hA_eq geotop_convex_hull_eq_HOL[of V] affine_hull_convex_hull[of V]
    by (by100 simp)
  have hc_not_aff_V: "c \<notin> affine hull V"
    using hc_not_aff_A hAff_A by (by100 simp)
  have hinsert_ai: "\<not> affine_dependent (insert c V)"
    by (rule affine_independent_insert[OF hV_ai hc_not_aff_V])
  have hinsert_fin: "finite (insert c V)"
    using hV_fin by (by100 simp)
  have hinsert_ne: "insert c V \<noteq> {}"
    by (by100 simp)
  have hconeV:
      "geotop_simplex_vertices (geotop_convex_hull (insert c V)) (insert c V)"
    by (rule geotop_AI_finite_ne_is_simplex_vertices
        [OF hinsert_fin hinsert_ne hinsert_ai])
  have hcone_eq:
      "geotop_convex_hull (insert c A) =
        geotop_convex_hull (insert c V)"
  proof -
    have "geotop_convex_hull (insert c A) =
        geotop_convex_hull (insert c (geotop_convex_hull V))"
      using hA_eq by (by100 simp)
    also have "... = geotop_convex_hull (insert c V)"
      by (rule geotop_convex_hull_insert_geotop_convex_hull_eq_dev34)
    finally show ?thesis .
  qed
  have hconeA:
      "geotop_simplex_vertices (geotop_convex_hull (insert c A)) (insert c V)"
    using hcone_eq hconeV by (by100 simp)
  have hW_eq: "W = insert c V"
    by (rule geotop_simplex_vertices_unique[OF hW hconeA])
  show ?thesis
    using hW_eq hV_vertices by (by100 blast)
qed

lemma geotop_boundary_cone_definition_vertices_subset_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "geotop_complex_vertices L' \<subseteq> insert c (geotop_complex_vertices F)"
proof
  fix v
  assume hv: "v \<in> geotop_complex_vertices L'"
  obtain \<tau> V where h\<tau>L: "\<tau> \<in> L'"
    and h\<tau>V: "geotop_simplex_vertices \<tau> V"
    and hvV: "v \<in> V"
    using hv unfolding geotop_complex_vertices_def by (by100 blast)
  have hcases:
      "\<tau> = geotop_convex_hull {c}
      \<or> \<tau> \<in> F
      \<or> (\<exists>A. A \<in> F \<and> A \<noteq> {} \<and> \<tau> = geotop_convex_hull (insert c A))"
    by (rule geotop_boundary_cone_definition_member_cases_dev34[OF hL h\<tau>L])
  show "v \<in> insert c (geotop_complex_vertices F)"
  proof (cases "\<tau> = geotop_convex_hull {c}")
    case True
    have hsingleton: "geotop_convex_hull {c} = {c}"
      using geotop_convex_hull_eq_HOL[of "{c}"] by (by100 simp)
    have hV_singleton: "geotop_simplex_vertices {c} V"
      using h\<tau>V True hsingleton by (by100 simp)
    have hV_eq: "V = {c}"
      by (rule geotop_singleton_simplex_vertices[OF hV_singleton])
    show ?thesis
      using hvV hV_eq by (by100 simp)
  next
    case hnot_new: False
    have hrest:
        "\<tau> \<in> F
        \<or> (\<exists>A. A \<in> F \<and> A \<noteq> {} \<and> \<tau> = geotop_convex_hull (insert c A))"
      using hcases hnot_new by (by100 blast)
    show ?thesis
    proof (cases "\<tau> \<in> F")
      case True
      have "v \<in> geotop_complex_vertices F"
        unfolding geotop_complex_vertices_def using True h\<tau>V hvV by (by100 blast)
      then show ?thesis
        by (by100 simp)
    next
      case False
      obtain A where hAF: "A \<in> F"
        and hAne: "A \<noteq> {}"
        and h\<tau>eq: "\<tau> = geotop_convex_hull (insert c A)"
        using hrest False by (by100 blast)
      have hconeV:
          "geotop_simplex_vertices (geotop_convex_hull (insert c A)) V"
        using h\<tau>V h\<tau>eq by (by100 simp)
      have hVsub: "V \<subseteq> insert c (geotop_complex_vertices F)"
        by (rule geotop_boundary_subdivision_cone_simplex_vertices_subset_dev34
            [OF h\<sigma> hsub hc hAF hconeV])
      show ?thesis
        using hVsub hvV by (by100 blast)
    qed
  qed
qed

lemma geotop_boundary_cone_definition_vertices_eq_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "geotop_complex_vertices L' = insert c (geotop_complex_vertices F)"
proof -
  have hsup: "insert c (geotop_complex_vertices F) \<subseteq> geotop_complex_vertices L'"
    by (rule geotop_boundary_cone_definition_vertices_contains_dev34[OF hL])
  have hsubL: "geotop_complex_vertices L' \<subseteq> insert c (geotop_complex_vertices F)"
    by (rule geotop_boundary_cone_definition_vertices_subset_dev34
        [OF h\<sigma> hsub hc hL])
  show ?thesis
    by (rule subset_antisym[OF hsubL hsup])
qed

lemma geotop_boundary_subdivision_cone_point_in_simplex_vertices_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hA: "A \<in> F"
  assumes hW:
    "geotop_simplex_vertices (geotop_convex_hull (insert c A)) W"
  shows "c \<in> W"
proof -
  have hF_complex: "geotop_is_complex F"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hsub])
  have hF_simplexes: "\<forall>\<tau>\<in>F. geotop_is_simplex \<tau>"
    by (rule conjunct1[OF hF_complex[unfolded geotop_is_complex_def]])
  have hA_simplex: "geotop_is_simplex A"
    using hF_simplexes hA by (by100 blast)
  obtain V m n where hV_fin: "finite V"
    and hV_card: "card V = n + 1"
    and hn_le_m: "n \<le> m"
    and hV_gp: "geotop_general_position V m"
    and hA_eq: "A = geotop_convex_hull V"
    using hA_simplex unfolding geotop_is_simplex_def by (by100 blast)
  have hAV: "geotop_simplex_vertices A V"
    unfolding geotop_simplex_vertices_def
    using hV_fin hV_card hn_le_m hV_gp hA_eq by (by100 blast)
  have hV_ai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF hAV])
  have hc_not_aff_A: "c \<notin> affine hull A"
    by (rule geotop_boundary_subdivision_simplex_affine_hull_misses_interior_point_dev34
        [OF h\<sigma> hsub hc hA])
  have hAff_A: "affine hull A = affine hull V"
    using hA_eq geotop_convex_hull_eq_HOL[of V] affine_hull_convex_hull[of V]
    by (by100 simp)
  have hc_not_aff_V: "c \<notin> affine hull V"
    using hc_not_aff_A hAff_A by (by100 simp)
  have hinsert_ai: "\<not> affine_dependent (insert c V)"
    by (rule affine_independent_insert[OF hV_ai hc_not_aff_V])
  have hinsert_fin: "finite (insert c V)"
    using hV_fin by (by100 simp)
  have hinsert_ne: "insert c V \<noteq> {}"
    by (by100 simp)
  have hconeV:
      "geotop_simplex_vertices (geotop_convex_hull (insert c V)) (insert c V)"
    by (rule geotop_AI_finite_ne_is_simplex_vertices
        [OF hinsert_fin hinsert_ne hinsert_ai])
  have hcone_eq:
      "geotop_convex_hull (insert c A) =
        geotop_convex_hull (insert c V)"
  proof -
    have "geotop_convex_hull (insert c A) =
        geotop_convex_hull (insert c (geotop_convex_hull V))"
      using hA_eq by (by100 simp)
    also have "... = geotop_convex_hull (insert c V)"
      by (rule geotop_convex_hull_insert_geotop_convex_hull_eq_dev34)
    finally show ?thesis .
  qed
  have hconeA:
      "geotop_simplex_vertices (geotop_convex_hull (insert c A)) (insert c V)"
    using hcone_eq hconeV by (by100 simp)
  have hW_eq: "W = insert c V"
    by (rule geotop_simplex_vertices_unique[OF hW hconeA])
  show ?thesis
    using hW_eq by (by100 simp)
qed

lemma geotop_boundary_subdivision_cone_simplex_vertices_base_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hA: "A \<in> F"
  assumes hW:
    "geotop_simplex_vertices (geotop_convex_hull (insert c A)) W"
  shows "\<exists>V. geotop_simplex_vertices A V \<and> W = insert c V"
proof -
  have hF_complex: "geotop_is_complex F"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hsub])
  have hF_simplexes: "\<forall>\<tau>\<in>F. geotop_is_simplex \<tau>"
    by (rule conjunct1[OF hF_complex[unfolded geotop_is_complex_def]])
  have hA_simplex: "geotop_is_simplex A"
    using hF_simplexes hA by (by100 blast)
  obtain V m n where hV_fin: "finite V"
    and hV_card: "card V = n + 1"
    and hn_le_m: "n \<le> m"
    and hV_gp: "geotop_general_position V m"
    and hA_eq: "A = geotop_convex_hull V"
    using hA_simplex unfolding geotop_is_simplex_def by (by100 blast)
  have hAV: "geotop_simplex_vertices A V"
    unfolding geotop_simplex_vertices_def
    using hV_fin hV_card hn_le_m hV_gp hA_eq by (by100 blast)
  have hV_ai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF hAV])
  have hc_not_aff_A: "c \<notin> affine hull A"
    by (rule geotop_boundary_subdivision_simplex_affine_hull_misses_interior_point_dev34
        [OF h\<sigma> hsub hc hA])
  have hAff_A: "affine hull A = affine hull V"
    using hA_eq geotop_convex_hull_eq_HOL[of V] affine_hull_convex_hull[of V]
    by (by100 simp)
  have hc_not_aff_V: "c \<notin> affine hull V"
    using hc_not_aff_A hAff_A by (by100 simp)
  have hinsert_ai: "\<not> affine_dependent (insert c V)"
    by (rule affine_independent_insert[OF hV_ai hc_not_aff_V])
  have hinsert_fin: "finite (insert c V)"
    using hV_fin by (by100 simp)
  have hinsert_ne: "insert c V \<noteq> {}"
    by (by100 simp)
  have hconeV:
      "geotop_simplex_vertices (geotop_convex_hull (insert c V)) (insert c V)"
    by (rule geotop_AI_finite_ne_is_simplex_vertices
        [OF hinsert_fin hinsert_ne hinsert_ai])
  have hcone_eq:
      "geotop_convex_hull (insert c A) =
        geotop_convex_hull (insert c V)"
  proof -
    have "geotop_convex_hull (insert c A) =
        geotop_convex_hull (insert c (geotop_convex_hull V))"
      using hA_eq by (by100 simp)
    also have "... = geotop_convex_hull (insert c V)"
      by (rule geotop_convex_hull_insert_geotop_convex_hull_eq_dev34)
    finally show ?thesis .
  qed
  have hconeA:
      "geotop_simplex_vertices (geotop_convex_hull (insert c A)) (insert c V)"
    using hcone_eq hconeV by (by100 simp)
  have hW_eq: "W = insert c V"
    by (rule geotop_simplex_vertices_unique[OF hW hconeA])
  show ?thesis
    using hAV hW_eq by (by100 blast)
qed

lemma geotop_boundary_cone_definition_members_are_simplexes_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "\<forall>\<tau>\<in>L'. geotop_is_simplex \<tau>"
proof
  fix \<tau>
  assume h\<tau>: "\<tau> \<in> L'"
  have hcases:
      "\<tau> = geotop_convex_hull {c}
      \<or> \<tau> \<in> F
      \<or> (\<exists>A. A \<in> F \<and> A \<noteq> {} \<and> \<tau> = geotop_convex_hull (insert c A))"
    by (rule geotop_boundary_cone_definition_member_cases_dev34[OF hL h\<tau>])
  have hF_complex: "geotop_is_complex F"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hsub])
  have hF_simplexes: "\<forall>\<rho>\<in>F. geotop_is_simplex \<rho>"
    by (rule geotop_is_complex_simplex[OF hF_complex])
  show "geotop_is_simplex \<tau>"
  proof (cases "\<tau> = geotop_convex_hull {c}")
    case True
    have hch: "geotop_convex_hull {c} = {c}"
      using geotop_convex_hull_eq_HOL[of "{c}"] by (by100 simp)
    have "geotop_is_simplex {c}"
      by (rule geotop_simplex_dim_imp_is_simplex[OF geotop_singleton_is_simplex])
    then show ?thesis
      using True hch by (by100 simp)
  next
    case hnot_singleton: False
    have htail:
        "\<tau> \<in> F
        \<or> (\<exists>A. A \<in> F \<and> A \<noteq> {} \<and> \<tau> = geotop_convex_hull (insert c A))"
      using hcases hnot_singleton by (by100 blast)
    show ?thesis
    proof (cases "\<tau> \<in> F")
      case True
      show ?thesis
        using hF_simplexes True by (by100 blast)
    next
      case False
      obtain A where hA: "A \<in> F"
        and hAne: "A \<noteq> {}"
        and h\<tau>_eq: "\<tau> = geotop_convex_hull (insert c A)"
        using htail False by (by100 blast)
      have "geotop_is_simplex (geotop_convex_hull (insert c A))"
        by (rule geotop_boundary_subdivision_cone_over_simplex_is_simplex_dev34
            [OF h\<sigma> hsub hc hA])
      then show ?thesis
        using h\<tau>_eq by (by100 simp)
    qed
  qed
qed

lemma geotop_boundary_cone_definition_old_face_in_L_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  assumes hA: "A \<in> F"
  assumes hface: "geotop_is_face \<tau> A"
  shows "\<tau> \<in> L'"
proof -
  have hF_complex: "geotop_is_complex F"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hsub])
  have hF_faces: "\<forall>\<rho>\<in>F. \<forall>\<eta>. geotop_is_face \<eta> \<rho> \<longrightarrow> \<eta> \<in> F"
    by (rule geotop_is_complex_face_closed[OF hF_complex])
  have h\<tau>F: "\<tau> \<in> F"
    using hF_faces hA hface by (by100 blast)
  show ?thesis
    by (rule geotop_boundary_cone_definition_contains_old_simplex_dev34[OF hL h\<tau>F])
qed

lemma geotop_boundary_cone_definition_cone_face_in_L_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  assumes hA: "A \<in> F"
  assumes hface: "geotop_is_face \<tau> (geotop_convex_hull (insert c A))"
  shows "\<tau> \<in> L'"
proof -
  have hF_complex: "geotop_is_complex F"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hsub])
  have hF_simplexes: "\<forall>\<rho>\<in>F. geotop_is_simplex \<rho>"
    by (rule geotop_is_complex_simplex[OF hF_complex])
  have hF_faces: "\<forall>\<rho>\<in>F. \<forall>\<eta>. geotop_is_face \<eta> \<rho> \<longrightarrow> \<eta> \<in> F"
    by (rule geotop_is_complex_face_closed[OF hF_complex])
  have hA_simplex: "geotop_is_simplex A"
    using hF_simplexes hA by (by100 blast)
  obtain V m n where hV_fin: "finite V"
    and hV_card: "card V = n + 1"
    and hn_le_m: "n \<le> m"
    and hV_gp: "geotop_general_position V m"
    and hA_eq: "A = geotop_convex_hull V"
    using hA_simplex unfolding geotop_is_simplex_def by (by100 blast)
  have hAV: "geotop_simplex_vertices A V"
    unfolding geotop_simplex_vertices_def
    using hV_fin hV_card hn_le_m hV_gp hA_eq by (by100 blast)
  have hV_ai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF hAV])
  have hc_not_aff_A: "c \<notin> affine hull A"
    by (rule geotop_boundary_subdivision_simplex_affine_hull_misses_interior_point_dev34
        [OF h\<sigma> hsub hc hA])
  have hAff_A: "affine hull A = affine hull V"
    using hA_eq geotop_convex_hull_eq_HOL[of V] affine_hull_convex_hull[of V]
    by (by100 simp)
  have hc_not_aff_V: "c \<notin> affine hull V"
    using hc_not_aff_A hAff_A by (by100 simp)
  have hc_not_V: "c \<notin> V"
  proof
    assume "c \<in> V"
    have "V \<subseteq> affine hull V"
      by (rule hull_subset)
    hence "c \<in> affine hull V"
      using \<open>c \<in> V\<close> by (by100 blast)
    show False
      using hc_not_aff_V \<open>c \<in> affine hull V\<close> by (by100 blast)
  qed
  have hinsert_ai: "\<not> affine_dependent (insert c V)"
    by (rule affine_independent_insert[OF hV_ai hc_not_aff_V])
  have hinsert_fin: "finite (insert c V)"
    using hV_fin by (by100 simp)
  have hinsert_ne: "insert c V \<noteq> {}"
    by (by100 simp)
  have hconeV:
      "geotop_simplex_vertices (geotop_convex_hull (insert c V)) (insert c V)"
    by (rule geotop_AI_finite_ne_is_simplex_vertices
        [OF hinsert_fin hinsert_ne hinsert_ai])
  have hcone_eq:
      "geotop_convex_hull (insert c A) =
        geotop_convex_hull (insert c V)"
  proof -
    have "geotop_convex_hull (insert c A) =
        geotop_convex_hull (insert c (geotop_convex_hull V))"
      using hA_eq by (by100 simp)
    also have "... = geotop_convex_hull (insert c V)"
      by (rule geotop_convex_hull_insert_geotop_convex_hull_eq_dev34)
    finally show ?thesis .
  qed
  obtain U W where hU:
      "geotop_simplex_vertices (geotop_convex_hull (insert c A)) U"
    and hW_ne: "W \<noteq> {}"
    and hW_sub_U: "W \<subseteq> U"
    and h\<tau>_eq: "\<tau> = geotop_convex_hull W"
    and h\<tau>W: "geotop_simplex_vertices \<tau> W"
    by (rule geotop_face_witness_simplex_vertices[OF hface])
  have hconeV_A:
      "geotop_simplex_vertices (geotop_convex_hull (insert c A)) (insert c V)"
    using hconeV hcone_eq by (by100 simp)
  have hU_eq: "U = insert c V"
    by (rule geotop_simplex_vertices_unique[OF hU hconeV_A])
  have hW_sub: "W \<subseteq> insert c V"
    using hW_sub_U hU_eq by (by100 simp)
  show ?thesis
  proof (cases "c \<in> W")
    case True
    show ?thesis
    proof (cases "W - {c} = {}")
      case True
      have hW_eq: "W = {c}"
        using \<open>c \<in> W\<close> True by (by100 blast)
      have h\<tau>_singleton: "\<tau> = geotop_convex_hull {c}"
        using h\<tau>_eq hW_eq by (by100 simp)
      have "geotop_convex_hull {c} \<in> L'"
        by (rule geotop_boundary_cone_definition_contains_new_vertex_dev34[OF hL])
      show ?thesis
        using h\<tau>_singleton \<open>geotop_convex_hull {c} \<in> L'\<close> by (by100 simp)
    next
      case hWbase_ne: False
      let ?B = "geotop_convex_hull (W - {c})"
      have hWbase_sub_V: "W - {c} \<subseteq> V"
        using hW_sub hc_not_V by (by100 blast)
      have hB_face_A: "geotop_is_face ?B A"
        by (rule geotop_is_face_of_subset[OF hAV hWbase_ne hWbase_sub_V])
      have hBF: "?B \<in> F"
        using hF_faces hA hB_face_A by (by100 blast)
      have hB_ne: "?B \<noteq> {}"
      proof -
        obtain b where hb: "b \<in> W - {c}"
          using hWbase_ne by (by100 blast)
        have hsub: "W - {c} \<subseteq> ?B"
          unfolding geotop_convex_hull_eq_HOL by (rule hull_subset)
        have "b \<in> ?B"
          using hb hsub by (by100 blast)
        show ?thesis
          using \<open>b \<in> ?B\<close> by (by100 blast)
      qed
      have hW_eq: "W = insert c (W - {c})"
        using \<open>c \<in> W\<close> by (by100 blast)
      have h\<tau>_cone:
          "\<tau> = geotop_convex_hull (insert c ?B)"
      proof -
        have "\<tau> = geotop_convex_hull (insert c (W - {c}))"
          using h\<tau>_eq hW_eq by (by100 simp)
        also have "... = geotop_convex_hull (insert c ?B)"
          using geotop_convex_hull_insert_geotop_convex_hull_eq_dev34
            [of c "W - {c}"] by (by100 simp)
        finally show ?thesis .
      qed
      have "geotop_convex_hull (insert c ?B) \<in> L'"
        by (rule geotop_boundary_cone_definition_contains_cone_dev34
            [OF hL hBF hB_ne])
      show ?thesis
        using h\<tau>_cone \<open>geotop_convex_hull (insert c ?B) \<in> L'\<close> by (by100 simp)
    qed
  next
    case False
    have hW_sub_V: "W \<subseteq> V"
      using hW_sub False by (by100 blast)
    have hface_A: "geotop_is_face \<tau> A"
      unfolding geotop_is_face_def
      using hAV hW_ne hW_sub_V h\<tau>_eq by (by100 blast)
    show ?thesis
      by (rule geotop_boundary_cone_definition_old_face_in_L_dev34
          [OF hsub hL hA hface_A])
  qed
qed

lemma geotop_boundary_cone_definition_face_closed_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "\<forall>\<tau>\<in>L'. \<forall>\<eta>. geotop_is_face \<eta> \<tau> \<longrightarrow> \<eta> \<in> L'"
proof
  fix \<tau>
  assume h\<tau>L: "\<tau> \<in> L'"
  show "\<forall>\<eta>. geotop_is_face \<eta> \<tau> \<longrightarrow> \<eta> \<in> L'"
  proof (intro allI impI)
    fix \<eta>
    assume hface: "geotop_is_face \<eta> \<tau>"
    have hcases:
        "\<tau> = geotop_convex_hull {c}
        \<or> \<tau> \<in> F
        \<or> (\<exists>A. A \<in> F \<and> A \<noteq> {} \<and> \<tau> = geotop_convex_hull (insert c A))"
      by (rule geotop_boundary_cone_definition_member_cases_dev34[OF hL h\<tau>L])
    show "\<eta> \<in> L'"
    proof (cases "\<tau> = geotop_convex_hull {c}")
      case True
      have hch: "geotop_convex_hull {c} = {c}"
        using geotop_convex_hull_eq_HOL[of "{c}"] by (by100 simp)
      have h\<tau>singleton: "\<tau> = {c}"
        using True hch by (by100 simp)
      obtain V W where hV: "geotop_simplex_vertices \<tau> V"
        and hW_ne: "W \<noteq> {}"
        and hW_sub: "W \<subseteq> V"
        and h\<eta>_eq: "\<eta> = geotop_convex_hull W"
        using hface unfolding geotop_is_face_def by (by100 blast)
      have h\<tau>V_singleton: "geotop_simplex_vertices \<tau> {c}"
        using geotop_simplex_vertices_singleton[of c] h\<tau>singleton by (by100 simp)
      have hV_eq: "V = {c}"
        by (rule geotop_simplex_vertices_unique[OF hV h\<tau>V_singleton])
      have hW_eq: "W = {c}"
        using hW_ne hW_sub hV_eq by (by100 blast)
      have h\<eta>_singleton: "\<eta> = geotop_convex_hull {c}"
        using h\<eta>_eq hW_eq by (by100 simp)
      have "geotop_convex_hull {c} \<in> L'"
        by (rule geotop_boundary_cone_definition_contains_new_vertex_dev34[OF hL])
      show ?thesis
        using h\<eta>_singleton \<open>geotop_convex_hull {c} \<in> L'\<close> by (by100 simp)
    next
      case hnot_singleton: False
      have htail:
          "\<tau> \<in> F
          \<or> (\<exists>A. A \<in> F \<and> A \<noteq> {} \<and> \<tau> = geotop_convex_hull (insert c A))"
        using hcases hnot_singleton by (by100 blast)
      show ?thesis
      proof (cases "\<tau> \<in> F")
        case True
        show ?thesis
          by (rule geotop_boundary_cone_definition_old_face_in_L_dev34
              [OF hsub hL True hface])
      next
        case False
        obtain A where hA: "A \<in> F"
          and hAne: "A \<noteq> {}"
          and h\<tau>_eq: "\<tau> = geotop_convex_hull (insert c A)"
          using htail False by (by100 blast)
        have hface_cone: "geotop_is_face \<eta> (geotop_convex_hull (insert c A))"
          using hface h\<tau>_eq by (by100 simp)
        show ?thesis
          by (rule geotop_boundary_cone_definition_cone_face_in_L_dev34
              [OF h\<sigma> hsub hc hL hA hface_cone])
      qed
    qed
  qed
qed

lemma geotop_boundary_cone_definition_intersections_are_faces_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "\<forall>\<tau>\<in>L'. \<forall>\<eta>\<in>L'. \<tau> \<inter> \<eta> \<noteq> {}
    \<longrightarrow> geotop_is_face (\<tau> \<inter> \<eta>) \<tau>
      \<and> geotop_is_face (\<tau> \<inter> \<eta>) \<eta>"
proof
  fix \<tau>
  assume h\<tau>L: "\<tau> \<in> L'"
  show "\<forall>\<eta>\<in>L'. \<tau> \<inter> \<eta> \<noteq> {}
    \<longrightarrow> geotop_is_face (\<tau> \<inter> \<eta>) \<tau>
      \<and> geotop_is_face (\<tau> \<inter> \<eta>) \<eta>"
  proof
    fix \<eta>
    assume h\<eta>L: "\<eta> \<in> L'"
    show "\<tau> \<inter> \<eta> \<noteq> {}
      \<longrightarrow> geotop_is_face (\<tau> \<inter> \<eta>) \<tau>
        \<and> geotop_is_face (\<tau> \<inter> \<eta>) \<eta>"
    proof
      assume hI_ne: "\<tau> \<inter> \<eta> \<noteq> {}"
      have hF_complex: "geotop_is_complex F"
        by (rule geotop_subdivision_source_is_complex_dev34[OF hsub])
      have hF_inter:
          "\<forall>A\<in>F. \<forall>B\<in>F. A \<inter> B \<noteq> {}
            \<longrightarrow> geotop_is_face (A \<inter> B) A
              \<and> geotop_is_face (A \<inter> B) B"
        by (rule geotop_is_complex_intersection[OF hF_complex])
      have hsing: "geotop_convex_hull {c} = {c}"
        using geotop_convex_hull_eq_HOL[of "{c}"] by (by100 simp)
      have h\<tau>cases:
          "\<tau> = geotop_convex_hull {c}
          \<or> \<tau> \<in> F
          \<or> (\<exists>A. A \<in> F \<and> A \<noteq> {} \<and> \<tau> = geotop_convex_hull (insert c A))"
        by (rule geotop_boundary_cone_definition_member_cases_dev34[OF hL h\<tau>L])
      show "geotop_is_face (\<tau> \<inter> \<eta>) \<tau>
        \<and> geotop_is_face (\<tau> \<inter> \<eta>) \<eta>"
      proof (cases "\<tau> = geotop_convex_hull {c}")
        case h\<tau>single: True
        have h\<tau>simplex: "geotop_is_simplex \<tau>"
          using geotop_boundary_cone_definition_members_are_simplexes_dev34
            [OF h\<sigma> hsub hc hL] h\<tau>L by (by100 blast)
        have h\<eta>cases:
            "\<eta> = geotop_convex_hull {c}
            \<or> \<eta> \<in> F
            \<or> (\<exists>B. B \<in> F \<and> B \<noteq> {} \<and> \<eta> = geotop_convex_hull (insert c B))"
          by (rule geotop_boundary_cone_definition_member_cases_dev34[OF hL h\<eta>L])
        show ?thesis
        proof (cases "\<eta> = geotop_convex_hull {c}")
          case h\<eta>single: True
          have hI_eq: "\<tau> \<inter> \<eta> = \<tau>"
            using h\<eta>single h\<tau>single by (by100 simp)
          have hface: "geotop_is_face \<tau> \<tau>"
            by (rule geotop_is_face_refl_of_simplex[OF h\<tau>simplex])
          show ?thesis
            using hI_eq hface h\<eta>single h\<tau>single by (by100 simp)
        next
          case h\<eta>not_single: False
          have h\<eta>tail:
              "\<eta> \<in> F
              \<or> (\<exists>B. B \<in> F \<and> B \<noteq> {} \<and> \<eta> = geotop_convex_hull (insert c B))"
            using h\<eta>cases h\<eta>not_single by (by100 blast)
          show ?thesis
          proof (cases "\<eta> \<in> F")
            case h\<eta>F: True
            obtain x where hx: "x \<in> \<tau> \<inter> \<eta>"
              using hI_ne by (by100 blast)
            have hx_c: "x = c"
              using hx h\<tau>single hsing by (by100 blast)
            have "c \<in> \<eta>"
              using hx hx_c by (by100 blast)
            have "c \<notin> \<eta>"
              by (rule geotop_boundary_subdivision_simplex_misses_interior_point_dev34
                  [OF h\<sigma> hsub hc h\<eta>F])
            show ?thesis
              using \<open>c \<in> \<eta>\<close> \<open>c \<notin> \<eta>\<close> by (by100 blast)
          next
            case h\<eta>not_F: False
            obtain B where hB: "B \<in> F"
              and hBne: "B \<noteq> {}"
              and h\<eta>eq: "\<eta> = geotop_convex_hull (insert c B)"
              using h\<eta>tail h\<eta>not_F by (by100 blast)
            have hc_cone: "c \<in> geotop_convex_hull (insert c B)"
              by (rule geotop_convex_hull_insert_contains_insert_point_dev34)
            have hsingle_sub_cone:
                "geotop_convex_hull {c} \<subseteq> geotop_convex_hull (insert c B)"
            proof
              fix x
              assume hx: "x \<in> geotop_convex_hull {c}"
              have "x = c"
                using hx hsing by (by100 simp)
              show "x \<in> geotop_convex_hull (insert c B)"
                using \<open>x = c\<close> hc_cone by (by100 simp)
            qed
            have hI_eq: "\<tau> \<inter> \<eta> = geotop_convex_hull {c}"
              using h\<tau>single h\<eta>eq hsingle_sub_cone by (by100 blast)
            have hface_\<tau>: "geotop_is_face (geotop_convex_hull {c}) \<tau>"
              using h\<tau>single geotop_is_face_refl_of_simplex[OF h\<tau>simplex]
              by (by100 simp)
            have hface_\<eta>:
                "geotop_is_face (geotop_convex_hull {c}) \<eta>"
              using h\<eta>eq
                geotop_boundary_subdivision_new_singleton_is_face_of_cone_dev34
                  [OF h\<sigma> hsub hc hB]
              by (by100 simp)
            show ?thesis
              using hI_eq hface_\<tau> hface_\<eta> by (by100 simp)
          qed
        qed
      next
        case h\<tau>not_single: False
        have h\<tau>tail:
            "\<tau> \<in> F
            \<or> (\<exists>A. A \<in> F \<and> A \<noteq> {} \<and> \<tau> = geotop_convex_hull (insert c A))"
          using h\<tau>cases h\<tau>not_single by (by100 blast)
        show ?thesis
        proof (cases "\<tau> \<in> F")
          case h\<tau>F: True
          have h\<eta>cases:
              "\<eta> = geotop_convex_hull {c}
              \<or> \<eta> \<in> F
              \<or> (\<exists>B. B \<in> F \<and> B \<noteq> {} \<and> \<eta> = geotop_convex_hull (insert c B))"
            by (rule geotop_boundary_cone_definition_member_cases_dev34[OF hL h\<eta>L])
          show ?thesis
          proof (cases "\<eta> = geotop_convex_hull {c}")
            case h\<eta>single: True
            obtain x where hx: "x \<in> \<tau> \<inter> \<eta>"
              using hI_ne by (by100 blast)
            have hx_c: "x = c"
              using hx h\<eta>single hsing by (by100 blast)
            have "c \<in> \<tau>"
              using hx hx_c by (by100 blast)
            have "c \<notin> \<tau>"
              by (rule geotop_boundary_subdivision_simplex_misses_interior_point_dev34
                  [OF h\<sigma> hsub hc h\<tau>F])
            show ?thesis
              using \<open>c \<in> \<tau>\<close> \<open>c \<notin> \<tau>\<close> by (by100 blast)
          next
            case h\<eta>not_single: False
            have h\<eta>tail:
                "\<eta> \<in> F
                \<or> (\<exists>B. B \<in> F \<and> B \<noteq> {} \<and> \<eta> = geotop_convex_hull (insert c B))"
              using h\<eta>cases h\<eta>not_single by (by100 blast)
            show ?thesis
            proof (cases "\<eta> \<in> F")
              case h\<eta>F: True
              show ?thesis
                using hF_inter h\<tau>F h\<eta>F hI_ne by (by100 blast)
            next
              case h\<eta>not_F: False
              obtain B where hB: "B \<in> F"
                and hBne: "B \<noteq> {}"
                and h\<eta>eq: "\<eta> = geotop_convex_hull (insert c B)"
                using h\<eta>tail h\<eta>not_F by (by100 blast)
              have hI_eq: "\<tau> \<inter> \<eta> = \<tau> \<inter> B"
                using geotop_boundary_subdivision_old_inter_cone_eq_old_inter_dev34
                  [OF h\<sigma> hsub hc h\<tau>F hB] h\<eta>eq by (by100 simp)
              have hold_ne: "\<tau> \<inter> B \<noteq> {}"
                using hI_ne hI_eq by (by100 simp)
              have hfaces_old:
                  "geotop_is_face (\<tau> \<inter> B) \<tau>
                    \<and> geotop_is_face (\<tau> \<inter> B) B"
                using hF_inter h\<tau>F hB hold_ne by (by100 blast)
              have hface_\<tau>: "geotop_is_face (\<tau> \<inter> B) \<tau>"
                using hfaces_old by (by100 blast)
              have hface_B: "geotop_is_face (\<tau> \<inter> B) B"
                using hfaces_old by (by100 blast)
              have hface_\<eta>: "geotop_is_face (\<tau> \<inter> B) \<eta>"
                using h\<eta>eq
                  geotop_boundary_subdivision_old_face_is_face_of_cone_dev34
                    [OF h\<sigma> hsub hc hB hface_B]
                by (by100 simp)
              show ?thesis
                using hI_eq hface_\<tau> hface_\<eta> by (by100 simp)
            qed
          qed
        next
          case h\<tau>not_F: False
          obtain A where hA: "A \<in> F"
            and hAne: "A \<noteq> {}"
            and h\<tau>eq: "\<tau> = geotop_convex_hull (insert c A)"
            using h\<tau>tail h\<tau>not_F by (by100 blast)
          have h\<eta>cases:
              "\<eta> = geotop_convex_hull {c}
              \<or> \<eta> \<in> F
              \<or> (\<exists>B. B \<in> F \<and> B \<noteq> {} \<and> \<eta> = geotop_convex_hull (insert c B))"
            by (rule geotop_boundary_cone_definition_member_cases_dev34[OF hL h\<eta>L])
          show ?thesis
          proof (cases "\<eta> = geotop_convex_hull {c}")
            case h\<eta>single: True
            have hc_cone: "c \<in> geotop_convex_hull (insert c A)"
              by (rule geotop_convex_hull_insert_contains_insert_point_dev34)
            have hsingle_sub_cone:
                "geotop_convex_hull {c} \<subseteq> geotop_convex_hull (insert c A)"
            proof
              fix x
              assume hx: "x \<in> geotop_convex_hull {c}"
              have "x = c"
                using hx hsing by (by100 simp)
              show "x \<in> geotop_convex_hull (insert c A)"
                using \<open>x = c\<close> hc_cone by (by100 simp)
            qed
            have hI_eq: "\<tau> \<inter> \<eta> = geotop_convex_hull {c}"
              using h\<tau>eq h\<eta>single hsingle_sub_cone by (by100 blast)
            have hface_\<tau>: "geotop_is_face (geotop_convex_hull {c}) \<tau>"
              using h\<tau>eq
                geotop_boundary_subdivision_new_singleton_is_face_of_cone_dev34
                  [OF h\<sigma> hsub hc hA]
              by (by100 simp)
            have h\<eta>simplex: "geotop_is_simplex \<eta>"
              using geotop_boundary_cone_definition_members_are_simplexes_dev34
                [OF h\<sigma> hsub hc hL] h\<eta>L by (by100 blast)
            have hface_\<eta>: "geotop_is_face (geotop_convex_hull {c}) \<eta>"
              using h\<eta>single geotop_is_face_refl_of_simplex[OF h\<eta>simplex]
              by (by100 simp)
            show ?thesis
              using hI_eq hface_\<tau> hface_\<eta> by (by100 simp)
          next
            case h\<eta>not_single: False
            have h\<eta>tail:
                "\<eta> \<in> F
                \<or> (\<exists>B. B \<in> F \<and> B \<noteq> {} \<and> \<eta> = geotop_convex_hull (insert c B))"
              using h\<eta>cases h\<eta>not_single by (by100 blast)
            show ?thesis
            proof (cases "\<eta> \<in> F")
              case h\<eta>F: True
              have hI_eq: "\<tau> \<inter> \<eta> = A \<inter> \<eta>"
              proof -
                have "\<eta> \<inter> \<tau> = \<eta> \<inter> A"
                  using geotop_boundary_subdivision_old_inter_cone_eq_old_inter_dev34
                    [OF h\<sigma> hsub hc h\<eta>F hA] h\<tau>eq by (by100 simp)
                thus ?thesis by (by100 blast)
              qed
              have hold_ne: "A \<inter> \<eta> \<noteq> {}"
                using hI_ne hI_eq by (by100 simp)
              have hfaces_old:
                  "geotop_is_face (A \<inter> \<eta>) A
                    \<and> geotop_is_face (A \<inter> \<eta>) \<eta>"
                using hF_inter hA h\<eta>F hold_ne by (by100 blast)
              have hface_A: "geotop_is_face (A \<inter> \<eta>) A"
                using hfaces_old by (by100 blast)
              have hface_\<eta>: "geotop_is_face (A \<inter> \<eta>) \<eta>"
                using hfaces_old by (by100 blast)
              have hface_\<tau>: "geotop_is_face (A \<inter> \<eta>) \<tau>"
                using h\<tau>eq
                  geotop_boundary_subdivision_old_face_is_face_of_cone_dev34
                    [OF h\<sigma> hsub hc hA hface_A]
                by (by100 simp)
              show ?thesis
                using hI_eq hface_\<tau> hface_\<eta> by (by100 simp)
            next
              case h\<eta>not_F: False
              obtain B where hB: "B \<in> F"
                and hBne: "B \<noteq> {}"
                and h\<eta>eq: "\<eta> = geotop_convex_hull (insert c B)"
                using h\<eta>tail h\<eta>not_F by (by100 blast)
              have hI_eq:
                  "\<tau> \<inter> \<eta> = geotop_convex_hull (insert c (A \<inter> B))"
                using h\<tau>eq h\<eta>eq
                  geotop_boundary_subdivision_cone_inter_eq_cone_inter_dev34
                    [OF h\<sigma> hsub hc hA hB]
                by (by100 simp)
              show ?thesis
              proof (cases "A \<inter> B = {}")
                case hAB_empty: True
                have hI_single: "\<tau> \<inter> \<eta> = geotop_convex_hull {c}"
                  using hI_eq hAB_empty by (by100 simp)
                have hface_\<tau>:
                    "geotop_is_face (geotop_convex_hull {c}) \<tau>"
                  using h\<tau>eq
                    geotop_boundary_subdivision_new_singleton_is_face_of_cone_dev34
                      [OF h\<sigma> hsub hc hA]
                  by (by100 simp)
                have hface_\<eta>:
                    "geotop_is_face (geotop_convex_hull {c}) \<eta>"
                  using h\<eta>eq
                    geotop_boundary_subdivision_new_singleton_is_face_of_cone_dev34
                      [OF h\<sigma> hsub hc hB]
                  by (by100 simp)
                show ?thesis
                  using hI_single hface_\<tau> hface_\<eta> by (by100 simp)
              next
                case hAB_ne: False
                have hfaces_old:
                    "geotop_is_face (A \<inter> B) A
                      \<and> geotop_is_face (A \<inter> B) B"
                  using hF_inter hA hB hAB_ne by (by100 blast)
                have hface_A: "geotop_is_face (A \<inter> B) A"
                  using hfaces_old by (by100 blast)
                have hface_B: "geotop_is_face (A \<inter> B) B"
                  using hfaces_old by (by100 blast)
                have hface_\<tau>:
                    "geotop_is_face
                      (geotop_convex_hull (insert c (A \<inter> B))) \<tau>"
                  using h\<tau>eq
                    geotop_boundary_subdivision_cone_face_is_face_of_cone_dev34
                      [OF h\<sigma> hsub hc hA hface_A]
                  by (by100 simp)
                have hface_\<eta>:
                    "geotop_is_face
                      (geotop_convex_hull (insert c (A \<inter> B))) \<eta>"
                  using h\<eta>eq
                    geotop_boundary_subdivision_cone_face_is_face_of_cone_dev34
                      [OF h\<sigma> hsub hc hB hface_B]
                  by (by100 simp)
                show ?thesis
                  using hI_eq hface_\<tau> hface_\<eta> by (by100 simp)
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma geotop_boundary_cone_definition_source_complex_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "geotop_is_complex L'"
proof -
  have hsimplexes: "\<forall>\<tau>\<in>L'. geotop_is_simplex \<tau>"
    by (rule geotop_boundary_cone_definition_members_are_simplexes_dev34
        [OF h\<sigma> hsub hc hL])
  have hfaces: "\<forall>\<tau>\<in>L'. \<forall>\<eta>. geotop_is_face \<eta> \<tau> \<longrightarrow> \<eta> \<in> L'"
    by (rule geotop_boundary_cone_definition_face_closed_dev34
        [OF h\<sigma> hsub hc hL])
  have hintersections:
      "\<forall>\<tau>\<in>L'. \<forall>\<eta>\<in>L'. \<tau> \<inter> \<eta> \<noteq> {}
        \<longrightarrow> geotop_is_face (\<tau> \<inter> \<eta>) \<tau>
          \<and> geotop_is_face (\<tau> \<inter> \<eta>) \<eta>"
    by (rule geotop_boundary_cone_definition_intersections_are_faces_dev34
        [OF h\<sigma> hsub hc hL])
  have hlocal:
      "\<forall>\<tau>\<in>L'. \<exists>U. open U \<and> \<tau> \<subseteq> U
        \<and> finite {\<rho> \<in> L'. \<rho> \<inter> U \<noteq> {}}"
    by (rule geotop_boundary_cone_definition_local_finite_dev34
        [OF h\<sigma> hsub hL])
  show ?thesis
    unfolding geotop_is_complex_def
    using hsimplexes hfaces hintersections hlocal by (by100 blast)
qed

lemma geotop_boundary_cone_definition_is_subdivision_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  shows "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
proof -
  have hsource: "geotop_is_complex L'"
    by (rule geotop_boundary_cone_definition_source_complex_dev34
        [OF h\<sigma> hsub hc hL])
  have hrest:
      "geotop_is_complex {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_refines L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_polyhedron L'
        = geotop_polyhedron {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    by (rule geotop_boundary_cone_definition_subdivision_obligations_except_source_complex_dev34
        [OF h\<sigma> hsub hc hL])
  show ?thesis
    unfolding geotop_is_subdivision_def
    using hsource hrest by (by100 blast)
qed

lemma geotop_boundary_cone_definition_old_hull_iff_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hc_new: "c \<notin> geotop_complex_vertices F"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  assumes hAsub: "A \<subseteq> geotop_complex_vertices F"
  shows "geotop_convex_hull A \<in> F \<longleftrightarrow> geotop_convex_hull A \<in> L'"
proof
  assume hAF: "geotop_convex_hull A \<in> F"
  show "geotop_convex_hull A \<in> L'"
    by (rule geotop_boundary_cone_definition_old_hull_imp_dev34[OF hL hAF])
next
  assume hAL: "geotop_convex_hull A \<in> L'"
  have hL_complex: "geotop_is_complex L'"
    by (rule geotop_boundary_cone_definition_source_complex_dev34
        [OF h\<sigma> hsub hc hL])
  have hF_complex: "geotop_is_complex F"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hsub])
  have hF_finite: "finite F"
    by (rule geotop_boundary_subdivision_finite_dev34[OF h\<sigma> hsub])
  have hF_vertices_finite: "finite (geotop_complex_vertices F)"
    by (rule geotop_finite_complex_vertices_finite_dev34
        [OF hF_complex hF_finite])
  have hA_finite: "finite A"
    by (rule finite_subset[OF hAsub hF_vertices_finite])
  have hA_ne: "A \<noteq> {}"
  proof
    assume hA_empty: "A = {}"
    have hconv_empty: "geotop_convex_hull A = {}"
      using hA_empty geotop_convex_hull_eq_HOL[of A] convex_hull_empty
      by (by100 simp)
    have "geotop_convex_hull A \<noteq> {}"
      by (rule geotop_complex_simplex_nonempty[OF hL_complex hAL])
    show False
      using hconv_empty \<open>geotop_convex_hull A \<noteq> {}\<close> by (by100 blast)
  qed
  have hA_L_vertices: "A \<subseteq> geotop_complex_vertices L'"
  proof -
    have hF_vertices_L: "geotop_complex_vertices F \<subseteq> geotop_complex_vertices L'"
      by (rule geotop_boundary_cone_definition_old_vertices_subset_dev34[OF hL])
    show ?thesis
      using hAsub hF_vertices_L by (by100 blast)
  qed
  have hA_sv: "geotop_simplex_vertices (geotop_convex_hull A) A"
    by (rule geotop_V_subK_convhullK_is_simplex_vertices
        [OF hL_complex hA_finite hA_ne hA_L_vertices hAL])
  have hcases:
      "geotop_convex_hull A = geotop_convex_hull {c}
      \<or> geotop_convex_hull A \<in> F
      \<or> (\<exists>B. B \<in> F \<and> B \<noteq> {}
          \<and> geotop_convex_hull A = geotop_convex_hull (insert c B))"
    by (rule geotop_boundary_cone_definition_member_cases_dev34[OF hL hAL])
  show "geotop_convex_hull A \<in> F"
  proof (cases "geotop_convex_hull A = geotop_convex_hull {c}")
    case True
    have "geotop_convex_hull A \<noteq> geotop_convex_hull {c}"
      by (rule geotop_old_vertices_hull_ne_new_singleton_dev34
          [OF hc_new hAsub])
    then show ?thesis
      using True by (by100 blast)
  next
    case hnot_new: False
    have hrest:
        "geotop_convex_hull A \<in> F
        \<or> (\<exists>B. B \<in> F \<and> B \<noteq> {}
            \<and> geotop_convex_hull A = geotop_convex_hull (insert c B))"
      using hcases hnot_new by (by100 blast)
    show ?thesis
    proof (cases "geotop_convex_hull A \<in> F")
      case True
      show ?thesis
        using True .
    next
      case False
      obtain B where hBF: "B \<in> F"
        and hBne: "B \<noteq> {}"
        and hAeqB: "geotop_convex_hull A = geotop_convex_hull (insert c B)"
        using hrest False by (by100 blast)
      have hcone_sv:
          "geotop_simplex_vertices (geotop_convex_hull (insert c B)) A"
        using hA_sv hAeqB by (by100 simp)
      have hcA: "c \<in> A"
        by (rule geotop_boundary_subdivision_cone_point_in_simplex_vertices_dev34
            [OF h\<sigma> hsub hc hBF hcone_sv])
      have "c \<in> geotop_complex_vertices F"
        using hAsub hcA by (by100 blast)
      then show ?thesis
        using hc_new by (by100 blast)
    qed
  qed
qed

lemma geotop_boundary_cone_definition_cone_hull_iff_dev34:
  fixes F L' :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hsub:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hc: "c \<in> interior \<sigma>"
  assumes hc_new: "c \<notin> geotop_complex_vertices F"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  assumes hA_fin: "finite A"
  assumes hA_ne: "A \<noteq> {}"
  assumes hAsub: "A \<subseteq> geotop_complex_vertices F"
  shows "geotop_convex_hull A \<in> F
      \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'"
proof
  assume hAF: "geotop_convex_hull A \<in> F"
  show "geotop_convex_hull (insert c A) \<in> L'"
  proof -
    have hbase_ne: "geotop_convex_hull A \<noteq> {}"
    proof -
      obtain a where ha: "a \<in> A"
        using hA_ne by (by100 blast)
      have hsub_A: "A \<subseteq> geotop_convex_hull A"
        unfolding geotop_convex_hull_eq_HOL by (rule hull_subset)
      have "a \<in> geotop_convex_hull A"
        using hsub_A ha by (by100 blast)
      show ?thesis
        using \<open>a \<in> geotop_convex_hull A\<close> by (by100 blast)
    qed
    have hcone:
        "geotop_convex_hull (insert c (geotop_convex_hull A)) \<in> L'"
      by (rule geotop_boundary_cone_definition_contains_cone_dev34
          [OF hL hAF hbase_ne])
    have heq:
        "geotop_convex_hull (insert c (geotop_convex_hull A))
          = geotop_convex_hull (insert c A)"
      by (rule geotop_convex_hull_insert_geotop_convex_hull_eq_dev34)
    show ?thesis
      using hcone heq by (by100 simp)
  qed
next
  assume hconeL: "geotop_convex_hull (insert c A) \<in> L'"
  have hL_complex: "geotop_is_complex L'"
    by (rule geotop_boundary_cone_definition_source_complex_dev34
        [OF h\<sigma> hsub hc hL])
  have hcL: "c \<in> geotop_complex_vertices L'"
    by (rule geotop_boundary_cone_definition_new_vertex_in_vertices_dev34[OF hL])
  have hF_vertices_L: "geotop_complex_vertices F \<subseteq> geotop_complex_vertices L'"
    by (rule geotop_boundary_cone_definition_old_vertices_subset_dev34[OF hL])
  have hA_L_vertices: "A \<subseteq> geotop_complex_vertices L'"
    using hAsub hF_vertices_L by (by100 blast)
  have hinsert_sub:
      "insert c A \<subseteq> geotop_complex_vertices L'"
    using hcL hA_L_vertices by (by100 blast)
  have hinsert_fin: "finite (insert c A)"
    using hA_fin by (by100 simp)
  have hinsert_ne: "insert c A \<noteq> {}"
    by (by100 simp)
  have hconeA_sv:
      "geotop_simplex_vertices
        (geotop_convex_hull (insert c A)) (insert c A)"
    by (rule geotop_V_subK_convhullK_is_simplex_vertices
        [OF hL_complex hinsert_fin hinsert_ne hinsert_sub hconeL])
  have hcases:
      "geotop_convex_hull (insert c A) = geotop_convex_hull {c}
      \<or> geotop_convex_hull (insert c A) \<in> F
      \<or> (\<exists>B. B \<in> F \<and> B \<noteq> {}
          \<and> geotop_convex_hull (insert c A)
            = geotop_convex_hull (insert c B))"
    by (rule geotop_boundary_cone_definition_member_cases_dev34[OF hL hconeL])
  show "geotop_convex_hull A \<in> F"
  proof (cases "geotop_convex_hull (insert c A) = geotop_convex_hull {c}")
    case hnew: True
    obtain a where ha: "a \<in> A"
      using hA_ne by (by100 blast)
    have ha_old: "a \<in> geotop_complex_vertices F"
      using hAsub ha by (by100 blast)
    have hac: "a \<noteq> c"
      using hc_new ha_old by (by100 blast)
    have hsub_hull:
        "insert c A \<subseteq> geotop_convex_hull (insert c A)"
      unfolding geotop_convex_hull_eq_HOL by (rule hull_subset)
    have ha_cone: "a \<in> geotop_convex_hull (insert c A)"
      using hsub_hull ha by (by100 blast)
    have hsing: "geotop_convex_hull {c} = {c}"
      using geotop_convex_hull_eq_HOL[of "{c}"] by (by100 simp)
    have "a = c"
      using hnew hsing ha_cone by (by100 blast)
    then show ?thesis
      using hac by (by100 blast)
  next
    case hnot_new: False
    have hrest:
        "geotop_convex_hull (insert c A) \<in> F
        \<or> (\<exists>B. B \<in> F \<and> B \<noteq> {}
            \<and> geotop_convex_hull (insert c A)
              = geotop_convex_hull (insert c B))"
      using hcases hnot_new by (by100 blast)
    show ?thesis
    proof (cases "geotop_convex_hull (insert c A) \<in> F")
      case hconeF: True
      have hc_cone: "c \<in> geotop_convex_hull (insert c A)"
        by (rule geotop_convex_hull_insert_contains_insert_point_dev34)
      have hc_not_cone: "c \<notin> geotop_convex_hull (insert c A)"
        by (rule geotop_boundary_subdivision_simplex_misses_interior_point_dev34
            [OF h\<sigma> hsub hc hconeF])
      then show ?thesis
        using hc_cone by (by100 blast)
    next
      case hnot_old: False
      obtain B where hBF: "B \<in> F"
        and hBne: "B \<noteq> {}"
        and hcone_eq:
          "geotop_convex_hull (insert c A)
            = geotop_convex_hull (insert c B)"
        using hrest hnot_old by (by100 blast)
      have hconeB_sv:
          "geotop_simplex_vertices
            (geotop_convex_hull (insert c B)) (insert c A)"
        using hconeA_sv hcone_eq by (by100 simp)
      obtain V where hBV: "geotop_simplex_vertices B V"
        and hinsert_eq: "insert c A = insert c V"
        using geotop_boundary_subdivision_cone_simplex_vertices_base_dev34
          [OF h\<sigma> hsub hc hBF hconeB_sv]
        by (by100 blast)
      have hc_not_A: "c \<notin> A"
      proof
        assume hcA: "c \<in> A"
        have "c \<in> geotop_complex_vertices F"
          using hAsub hcA by (by100 blast)
        then show False
          using hc_new by (by100 blast)
      qed
      have hV_vertices: "V \<subseteq> geotop_complex_vertices F"
        unfolding geotop_complex_vertices_def using hBF hBV by (by100 blast)
      have hc_not_V: "c \<notin> V"
      proof
        assume hcV: "c \<in> V"
        have "c \<in> geotop_complex_vertices F"
          using hV_vertices hcV by (by100 blast)
        then show False
          using hc_new by (by100 blast)
      qed
      have hA_eq_V: "A = V"
      proof
        show "A \<subseteq> V"
        proof
          fix x
          assume hx: "x \<in> A"
          have "x \<in> insert c V"
            using hinsert_eq hx by (by100 blast)
          show "x \<in> V"
            using \<open>x \<in> insert c V\<close> hc_not_A hx by (by100 blast)
        qed
        show "V \<subseteq> A"
        proof
          fix x
          assume hx: "x \<in> V"
          have "x \<in> insert c A"
            using hinsert_eq hx by (by100 blast)
          show "x \<in> A"
            using \<open>x \<in> insert c A\<close> hc_not_V hx by (by100 blast)
        qed
      qed
      have hB_eq: "B = geotop_convex_hull V"
        using hBV unfolding geotop_simplex_vertices_def by (by100 blast)
      have "geotop_convex_hull A = B"
        using hA_eq_V hB_eq by (by100 simp)
      then show ?thesis
        using hBF by (by100 simp)
    qed
  qed
qed

lemma geotop_boundary_cone_definition_cone_hull_imp_dev34:
  fixes F L' :: "(real^2) set set"
  assumes hL:
    "L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  assumes hA: "geotop_convex_hull A \<in> F"
  assumes hAne: "A \<noteq> {}"
  shows "geotop_convex_hull (insert c A) \<in> L'"
proof -
  have hbase_ne: "geotop_convex_hull A \<noteq> {}"
  proof -
    obtain a where ha: "a \<in> A"
      using hAne by (by100 blast)
    have hsub: "A \<subseteq> geotop_convex_hull A"
      unfolding geotop_convex_hull_eq_HOL by (rule hull_subset)
    have "a \<in> geotop_convex_hull A"
      using hsub ha by (by100 blast)
    show ?thesis
      using \<open>a \<in> geotop_convex_hull A\<close> by (by100 blast)
  qed
  have hcone:
      "geotop_convex_hull (insert c (geotop_convex_hull A)) \<in> L'"
    by (rule geotop_boundary_cone_definition_contains_cone_dev34
        [OF hL hA hbase_ne])
  have heq:
      "geotop_convex_hull (insert c (geotop_convex_hull A))
        = geotop_convex_hull (insert c A)"
    by (rule geotop_convex_hull_insert_geotop_convex_hull_eq_dev34)
  show ?thesis
    using hcone heq by (by100 simp)
qed

lemma geotop_fig410_explicit_cone_basic_data_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hboundary:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  shows "\<exists>L' c.
      c \<in> interior \<sigma>
      \<and> c \<notin> geotop_complex_vertices F
      \<and> L' =
        insert (geotop_convex_hull {c})
          (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> insert c (geotop_complex_vertices F) \<subseteq> geotop_complex_vertices L'"
proof -
  obtain c where hc_int: "c \<in> interior \<sigma>"
    and hc_new: "c \<notin> geotop_complex_vertices F"
    using geotop_boundary_subdivision_new_interior_vertex_exists_dev34
      [OF h\<sigma> hboundary]
    by (by100 blast)
  let ?L' =
    "insert (geotop_convex_hull {c})
      (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
  have hL_def:
    "?L' =
      insert (geotop_convex_hull {c})
        (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
    by (by100 simp)
  have hc_simplex: "geotop_convex_hull {c} \<in> ?L'"
    by (rule geotop_boundary_cone_definition_contains_new_vertex_dev34[OF hL_def])
  have hvertices_contains:
      "insert c (geotop_complex_vertices F) \<subseteq> geotop_complex_vertices ?L'"
    by (rule geotop_boundary_cone_definition_vertices_contains_dev34[OF hL_def])
  show ?thesis
    using hc_int hc_new hL_def hc_simplex hvertices_contains
    by (intro exI[of _ ?L'] exI[of _ c]) (intro conjI; assumption)
qed

lemma geotop_fig410_explicit_cone_forward_memberships_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hboundary:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  shows "\<exists>L' c.
      c \<in> interior \<sigma>
      \<and> c \<notin> geotop_complex_vertices F
      \<and> L' =
        insert (geotop_convex_hull {c})
          (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> insert c (geotop_complex_vertices F) \<subseteq> geotop_complex_vertices L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        geotop_convex_hull A \<in> F \<longrightarrow> geotop_convex_hull A \<in> L')
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        geotop_convex_hull A \<in> F \<longrightarrow>
        geotop_convex_hull (insert c A) \<in> L')"
proof -
  obtain L' c where hbasic:
      "c \<in> interior \<sigma>
      \<and> c \<notin> geotop_complex_vertices F
      \<and> L' =
        insert (geotop_convex_hull {c})
          (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> insert c (geotop_complex_vertices F) \<subseteq> geotop_complex_vertices L'"
    using geotop_fig410_explicit_cone_basic_data_dev34[OF h\<sigma> hboundary]
    by (by100 blast)
  have hc_int: "c \<in> interior \<sigma>"
    using hbasic by (by100 blast)
  have hc_new: "c \<notin> geotop_complex_vertices F"
    using hbasic by (by100 blast)
  have hL:
      "L' =
        insert (geotop_convex_hull {c})
          (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
    using hbasic by (by100 blast)
  have hc_simplex: "geotop_convex_hull {c} \<in> L'"
    using hbasic by (by100 blast)
  have hvertices_contains:
      "insert c (geotop_complex_vertices F) \<subseteq> geotop_complex_vertices L'"
    using hbasic by (by100 blast)
  have hold:
      "\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        geotop_convex_hull A \<in> F \<longrightarrow> geotop_convex_hull A \<in> L'"
  proof (intro allI impI)
    fix A :: "(real^2) set"
    assume "A \<subseteq> geotop_complex_vertices F"
    assume hA: "geotop_convex_hull A \<in> F"
    show "geotop_convex_hull A \<in> L'"
      by (rule geotop_boundary_cone_definition_old_hull_imp_dev34[OF hL hA])
  qed
  have hcone:
      "\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        geotop_convex_hull A \<in> F \<longrightarrow>
        geotop_convex_hull (insert c A) \<in> L'"
  proof (intro allI impI)
    fix A :: "(real^2) set"
    assume "finite A"
    assume hAne: "A \<noteq> {}"
    assume "A \<subseteq> geotop_complex_vertices F"
    assume hA: "geotop_convex_hull A \<in> F"
    show "geotop_convex_hull (insert c A) \<in> L'"
      by (rule geotop_boundary_cone_definition_cone_hull_imp_dev34
          [OF hL hA hAne])
  qed
  show ?thesis
    using hc_int hc_new hL hc_simplex hvertices_contains hold hcone
    by (intro exI[of _ L'] exI[of _ c]) (intro conjI; assumption)
qed

lemma geotop_fig410_explicit_cone_over_boundary_subdivision_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hboundary:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  shows "\<exists>L' c.
      c \<in> interior \<sigma>
      \<and> c \<notin> geotop_complex_vertices F
      \<and> L' =
        insert (geotop_convex_hull {c})
          (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
  (**
    Book construction underlying Fig. 4.10 step 2.  Pick a point \<open>c\<close> in the
    interior of the 2-simplex, hence in no boundary edge, and take the complex
    consisting of the subdivided frontier \<open>F\<close>, the new vertex \<open>{c}\<close>, and the
    cones from \<open>c\<close> over every nonempty simplex of \<open>F\<close>. **)
proof -
  obtain L' c where hdata:
      "c \<in> interior \<sigma>
      \<and> c \<notin> geotop_complex_vertices F
      \<and> L' =
        insert (geotop_convex_hull {c})
          (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> insert c (geotop_complex_vertices F) \<subseteq> geotop_complex_vertices L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        geotop_convex_hull A \<in> F \<longrightarrow> geotop_convex_hull A \<in> L')
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        geotop_convex_hull A \<in> F \<longrightarrow>
        geotop_convex_hull (insert c A) \<in> L')"
    using geotop_fig410_explicit_cone_forward_memberships_dev34
      [OF h\<sigma> hboundary]
    by (elim exE) assumption
  have hc: "c \<in> interior \<sigma>"
    using hdata by (by100 blast)
  have hc_new: "c \<notin> geotop_complex_vertices F"
    using hdata by (by100 blast)
  have hL:
      "L' =
        insert (geotop_convex_hull {c})
          (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})"
    using hdata by (by100 blast)
  have hc_simplex: "geotop_convex_hull {c} \<in> L'"
    using hdata by (by100 blast)
  have hsubdiv:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    by (rule geotop_boundary_cone_definition_is_subdivision_dev34
        [OF h\<sigma> hboundary hc hL])
  have hvertices:
      "geotop_complex_vertices L' = insert c (geotop_complex_vertices F)"
    by (rule geotop_boundary_cone_definition_vertices_eq_dev34
        [OF h\<sigma> hboundary hc hL])
  have hold:
      "\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L')"
  proof (intro allI impI)
    fix A :: "(real^2) set"
    assume hAsub: "A \<subseteq> geotop_complex_vertices F"
    show "geotop_convex_hull A \<in> F
        \<longleftrightarrow> geotop_convex_hull A \<in> L'"
      by (rule geotop_boundary_cone_definition_old_hull_iff_dev34
          [OF h\<sigma> hboundary hc hc_new hL hAsub])
  qed
  have hcone:
      "\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L')"
  proof (intro allI impI)
    fix A :: "(real^2) set"
    assume hA_fin: "finite A"
    assume hA_ne: "A \<noteq> {}"
    assume hAsub: "A \<subseteq> geotop_complex_vertices F"
    show "geotop_convex_hull A \<in> F
        \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'"
      by (rule geotop_boundary_cone_definition_cone_hull_iff_dev34
          [OF h\<sigma> hboundary hc hc_new hL hA_fin hA_ne hAsub])
  qed
  show ?thesis
    using hc hc_new hL hsubdiv hvertices hc_simplex hold hcone
    by (intro exI[of _ L'] exI[of _ c]) (intro conjI; assumption)
qed

lemma geotop_fig410_cone_over_boundary_subdivision_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hboundary:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  shows "\<exists>L' c.
      geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
  (**
    Pure geometric part of Moise Fig. 4.10, step 2.  Choose a new point inside
    the 2-simplex, keep the subdivided frontier complex \<open>F\<close>, and add exactly
    the cones from the new point over the nonempty simplexes of \<open>F\<close>.  This
    gives a subdivision of the full 2-simplex face complex whose old simplexes
    are precisely \<open>F\<close> and whose new simplexes are precisely those cones. **)
proof -
  obtain L' c where hcone:
      "c \<in> interior \<sigma>
      \<and> c \<notin> geotop_complex_vertices F
      \<and> L' =
        insert (geotop_convex_hull {c})
          (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using geotop_fig410_explicit_cone_over_boundary_subdivision_dev34
      [OF h\<sigma> hboundary]
    by (elim exE) assumption
  have hc_int: "c \<in> interior \<sigma>"
    using hcone by (rule conjunct1)
  have hcone1:
      "c \<notin> geotop_complex_vertices F
      \<and> L' =
        insert (geotop_convex_hull {c})
          (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using hcone by (rule conjunct2)
  have hcF: "c \<notin> geotop_complex_vertices F"
    using hcone1 by (rule conjunct1)
  have hcone2:
      "L' =
        insert (geotop_convex_hull {c})
          (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using hcone1 by (rule conjunct2)
  have hcone3:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using hcone2 by (rule conjunct2)
  have hsubdiv:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    using hcone3 by (rule conjunct1)
  have hcone4:
      "geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using hcone3 by (rule conjunct2)
  have hvertices:
      "geotop_complex_vertices L' = insert c (geotop_complex_vertices F)"
    using hcone4 by (rule conjunct1)
  have hcone5:
      "geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using hcone4 by (rule conjunct2)
  have hc_simplex: "geotop_convex_hull {c} \<in> L'"
    using hcone5 by (rule conjunct1)
  have hcone6:
      "(\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using hcone5 by (rule conjunct2)
  have hboundary_membership:
      "\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L')"
    using hcone6 by (rule conjunct1)
  have hcone_membership:
      "\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L')"
    using hcone6 by (rule conjunct2)
  show ?thesis
    using hsubdiv hcF hvertices hc_simplex hboundary_membership hcone_membership
    by (intro exI[of _ L'] exI[of _ c]) (intro conjI; assumption)
qed

lemma geotop_fig410_cone_over_boundary_subdivision_with_interior_dev34:
  fixes F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hboundary:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  shows "\<exists>L' c.
      c \<in> interior \<sigma>
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
  (**
    Same Fig. 4.10 cone step as above, but keep the book's chosen cone vertex
    explicitly in the ordinary interior of the target 2-simplex. **)
proof -
  obtain L' c where hcone:
      "c \<in> interior \<sigma>
      \<and> c \<notin> geotop_complex_vertices F
      \<and> L' =
        insert (geotop_convex_hull {c})
          (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using geotop_fig410_explicit_cone_over_boundary_subdivision_dev34
      [OF h\<sigma> hboundary]
    by (elim exE) assumption
  have hc_int: "c \<in> interior \<sigma>"
    using hcone by (rule conjunct1)
  have hcone1:
      "c \<notin> geotop_complex_vertices F
      \<and> L' =
        insert (geotop_convex_hull {c})
          (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using hcone by (rule conjunct2)
  have hcF: "c \<notin> geotop_complex_vertices F"
    using hcone1 by (rule conjunct1)
  have hcone2:
      "L' =
        insert (geotop_convex_hull {c})
          (F \<union> {geotop_convex_hull (insert c A) | A. A \<in> F \<and> A \<noteq> {}})
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using hcone1 by (rule conjunct2)
  have hcone3:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using hcone2 by (rule conjunct2)
  have hsubdiv:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    using hcone3 by (rule conjunct1)
  have hcone4:
      "geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using hcone3 by (rule conjunct2)
  have hvertices:
      "geotop_complex_vertices L' = insert c (geotop_complex_vertices F)"
    using hcone4 by (rule conjunct1)
  have hcone5:
      "geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using hcone4 by (rule conjunct2)
  have hc_simplex: "geotop_convex_hull {c} \<in> L'"
    using hcone5 by (rule conjunct1)
  have hcone6:
      "(\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using hcone5 by (rule conjunct2)
  have hboundary_target:
      "\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L')"
    using hcone6 by (rule conjunct1)
  have hcone_target:
      "\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L')"
    using hcone6 by (rule conjunct2)
  show ?thesis
    using hc_int hsubdiv hcF hvertices hc_simplex hboundary_target hcone_target
    by (intro exI[of _ L'] exI[of _ c]) (intro conjI; assumption)
qed

lemma geotop_fig410_cone_fan_from_boundary_subdivision_and_isomorphism_dev34:
  fixes L F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hboundary:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hiso: "geotop_isomorphism L F \<psi>"
  shows "\<exists>L' c.
      geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Fig. 4.10, book step 2 in graph-only form.  Choose a new point inside the
    2-simplex and cone every nonempty boundary subdivision simplex to it,
    leaving the old boundary subdivision as the frontier.  The simplicial
    isomorphism from \<open>L\<close> to \<open>F\<close> translates the cone-simplex condition back
    to the original edge-chain or edge-cycle. **)
proof -
  obtain L' c where hcone:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using geotop_fig410_cone_over_boundary_subdivision_dev34
      [OF h\<sigma> hboundary]
    by (elim exE) assumption
  have hsubdiv:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    using hcone by (by100 blast)
  have hcF: "c \<notin> geotop_complex_vertices F"
    using hcone by (by100 blast)
  have hvertices:
      "geotop_complex_vertices L' = insert c (geotop_complex_vertices F)"
    using hcone by (by100 blast)
  have hc_simplex: "geotop_convex_hull {c} \<in> L'"
    using hcone by (by100 blast)
  have h\<psi>_bij:
      "bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)"
    using hiso unfolding geotop_isomorphism_def by (by100 blast)
  have h\<psi>_image:
      "\<psi> ` geotop_complex_vertices L = geotop_complex_vertices F"
    using h\<psi>_bij unfolding bij_betw_def by (by100 blast)
  have h\<psi>_vertices:
      "\<forall>W. W \<subseteq> geotop_complex_vertices L
        \<longrightarrow> \<psi> ` W \<subseteq> geotop_complex_vertices F"
    using h\<psi>_image by (by100 blast)
  have hcone_boundary:
      "\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L')"
    using hcone by (by100 blast)
  have hboundary_target:
      "\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
  proof (intro allI impI)
    fix W :: "(real^2) set"
    assume hWsub: "W \<subseteq> geotop_complex_vertices L"
    have h\<psi>Wsub: "\<psi> ` W \<subseteq> geotop_complex_vertices F"
      using h\<psi>_vertices hWsub by (by100 blast)
    show "geotop_convex_hull (\<psi> ` W) \<in> F
      \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'"
      using hcone_boundary h\<psi>Wsub by (by100 blast)
  qed
  have hiso_simplex:
      "\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F)"
    using hiso unfolding geotop_isomorphism_def by (by100 blast)
  have hcone_target:
      "\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L')"
  proof (intro allI impI)
    fix W :: "(real^2) set"
    assume hWfin: "finite W"
    assume hWne: "W \<noteq> {}"
    assume hWsub: "W \<subseteq> geotop_complex_vertices L"
    have h\<psi>Wsub: "\<psi> ` W \<subseteq> geotop_complex_vertices F"
      using h\<psi>_vertices hWsub by (by100 blast)
    have h\<psi>Wfin: "finite (\<psi> ` W)"
      using hWfin by (by100 simp)
    have h\<psi>Wne: "\<psi> ` W \<noteq> {}"
      using hWne by (by100 blast)
    have hF_cone:
        "geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'"
      using hcone h\<psi>Wfin h\<psi>Wne h\<psi>Wsub by (by100 blast)
    have hL_F:
        "geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F"
      using hiso_simplex hWsub by (by100 blast)
    show "geotop_convex_hull W \<in> L
      \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'"
      using hL_F hF_cone by (by100 blast)
  qed
  show ?thesis
    apply (rule_tac x=L' in exI)
    apply (rule_tac x=c in exI)
    using hsubdiv hcF hvertices hc_simplex hboundary_target hcone_target
    by (by100 blast)
qed

lemma geotop_fig410_fan_target_from_boundary_subdivision_and_isomorphism_dev34:
  fixes L F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hboundary:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hiso: "geotop_isomorphism L F \<psi>"
  shows "\<exists>(T :: (real^2) set set) L' B c.
      T = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' T
      \<and> bij_betw \<psi> (geotop_complex_vertices L) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Boundary-subdivision-to-fan packaging for Fig. 4.10.  Once an edge-chain
    or edge-cycle has been realized as a subdivision of the boundary of a
    2-simplex, the cone wrapper supplies the target fan and the simplicial
    isomorphism translates membership back to the original graph. **)
proof -
  obtain L' c where hcone:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
    using geotop_fig410_cone_fan_from_boundary_subdivision_and_isomorphism_dev34
        [OF h\<sigma> hboundary hiso]
    by (elim exE) assumption
  have hsubdiv:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    using hcone by (by100 blast)
  have hcF: "c \<notin> geotop_complex_vertices F"
    using hcone by (by100 blast)
  have hvertices:
      "geotop_complex_vertices L' = insert c (geotop_complex_vertices F)"
    using hcone by (by100 blast)
  have hc_simplex: "geotop_convex_hull {c} \<in> L'"
    using hcone by (by100 blast)
  have h\<psi>_bij:
      "bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)"
    using hiso unfolding geotop_isomorphism_def by (by100 blast)
  have hiso_simplex:
      "\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F)"
    using hiso unfolding geotop_isomorphism_def by (by100 blast)
  have hboundary_target:
      "\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
  proof (intro allI impI)
    fix W :: "(real^2) set"
    assume hW: "W \<subseteq> geotop_complex_vertices L"
    have hLF:
        "geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F"
      using hiso_simplex hW by (by100 blast)
    have hFL':
        "geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'"
      using hcone hW by (by100 blast)
    show "geotop_convex_hull W \<in> L
        \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'"
      using hLF hFL' by (by100 blast)
  qed
  have hcone_target:
      "\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L')"
    using hcone by (by100 blast)
  show ?thesis
    apply (rule_tac x="{\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}" in exI)
    apply (rule_tac x=L' in exI)
    apply (rule_tac x="geotop_complex_vertices F" in exI)
    apply (rule_tac x=c in exI)
  using h\<sigma> hsubdiv h\<psi>_bij hcF hvertices hc_simplex
        hboundary_target hcone_target
    by (by100 blast)
qed

lemma geotop_standard_boundary_self_fan_target_dev34:
  shows "\<exists>(T :: (real^2) set set) (\<sigma> :: (real^2) set) F L' B c \<psi>.
      T = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> geotop_isomorphism F F \<psi>
      \<and> geotop_is_subdivision L' T
      \<and> bij_betw \<psi> (geotop_complex_vertices F) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull W \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull W \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
proof -
  obtain \<sigma> :: "(real^2) set" and F \<psi> where h\<sigma>: "geotop_simplex_dim \<sigma> 2"
    and hsub:
      "geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
    and hiso: "geotop_isomorphism F F \<psi>"
    using geotop_standard_2simplex_boundary_self_isomorphism_model_dev34
    by (by100 blast)
  have hfan_ex:
      "\<exists>(T :: (real^2) set set) L' B c.
      T = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' T
      \<and> bij_betw \<psi> (geotop_complex_vertices F) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull W \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull W \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
    by (rule geotop_fig410_fan_target_from_boundary_subdivision_and_isomorphism_dev34
        [OF h\<sigma> hsub hiso])
  obtain T L' B c where hfan:
      "T = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' T
      \<and> bij_betw \<psi> (geotop_complex_vertices F) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull W \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull W \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
    using hfan_ex by (elim exE) assumption
  show ?thesis
  proof (rule_tac x=T in exI, rule_tac x=\<sigma> in exI,
      rule_tac x=F in exI, rule_tac x=L' in exI,
      rule_tac x=B in exI, rule_tac x=c in exI,
      rule_tac x=\<psi> in exI)
    show "T = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} \<and>
      geotop_simplex_dim \<sigma> 2 \<and>
      geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2) \<and>
      geotop_isomorphism F F \<psi> \<and>
      geotop_is_subdivision L' T \<and>
      bij_betw \<psi> (geotop_complex_vertices F) B \<and>
      c \<notin> B \<and>
      geotop_complex_vertices L' = insert c B \<and>
      geotop_convex_hull {c} \<in> L' \<and>
      (\<forall>W. W \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull W \<in> F \<longleftrightarrow>
          geotop_convex_hull (\<psi> ` W) \<in> L')) \<and>
      (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull W \<in> F \<longleftrightarrow>
          geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
      using h\<sigma> hsub hiso hfan by (by100 blast)
  qed
qed

lemma geotop_fig410_cone_fan_from_boundary_subdivision_and_isomorphism_with_interior_dev34:
  fixes L F :: "(real^2) set set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hboundary:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hiso: "geotop_isomorphism L F \<psi>"
  shows "\<exists>L' c.
      c \<in> interior \<sigma>
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Fig. 4.10 graph-only cone wrapper with the interior cone vertex retained
    through the simplicial isomorphism from the old link to the boundary
    subdivision. **)
proof -
  obtain L' c where hcone:
      "c \<in> interior \<sigma>
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L'))
      \<and> (\<forall>A. finite A \<longrightarrow> A \<noteq> {} \<longrightarrow>
        A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c A) \<in> L'))"
    using geotop_fig410_cone_over_boundary_subdivision_with_interior_dev34
      [OF h\<sigma> hboundary]
    by (elim exE) assumption
  have hc_int: "c \<in> interior \<sigma>"
    using hcone by (by100 blast)
  have hsubdiv:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    using hcone by (by100 blast)
  have hcF: "c \<notin> geotop_complex_vertices F"
    using hcone by (by100 blast)
  have hvertices:
      "geotop_complex_vertices L' = insert c (geotop_complex_vertices F)"
    using hcone by (by100 blast)
  have hc_simplex: "geotop_convex_hull {c} \<in> L'"
    using hcone by (by100 blast)
  have h\<psi>_bij:
      "bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices F)"
    using hiso unfolding geotop_isomorphism_def by (by100 blast)
  have h\<psi>_image:
      "\<psi> ` geotop_complex_vertices L = geotop_complex_vertices F"
    using h\<psi>_bij unfolding bij_betw_def by (by100 blast)
  have h\<psi>_vertices:
      "\<forall>W. W \<subseteq> geotop_complex_vertices L
        \<longrightarrow> \<psi> ` W \<subseteq> geotop_complex_vertices F"
    using h\<psi>_image by (by100 blast)
  have hcone_boundary:
      "\<forall>A. A \<subseteq> geotop_complex_vertices F \<longrightarrow>
        (geotop_convex_hull A \<in> F
          \<longleftrightarrow> geotop_convex_hull A \<in> L')"
    using hcone by (by100 blast)
  have hboundary_target:
      "\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
  proof (intro allI impI)
    fix W :: "(real^2) set"
    assume hWsub: "W \<subseteq> geotop_complex_vertices L"
    have h\<psi>Wsub: "\<psi> ` W \<subseteq> geotop_complex_vertices F"
      using h\<psi>_vertices hWsub by (by100 blast)
    show "geotop_convex_hull (\<psi> ` W) \<in> F
      \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'"
      using hcone_boundary h\<psi>Wsub by (by100 blast)
  qed
  have hiso_simplex:
      "\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F)"
    using hiso unfolding geotop_isomorphism_def by (by100 blast)
  have hcone_target:
      "\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L')"
  proof (intro allI impI)
    fix W :: "(real^2) set"
    assume hWfin: "finite W"
    assume hWne: "W \<noteq> {}"
    assume hWsub: "W \<subseteq> geotop_complex_vertices L"
    have h\<psi>Wsub: "\<psi> ` W \<subseteq> geotop_complex_vertices F"
      using h\<psi>_vertices hWsub by (by100 blast)
    have h\<psi>Wfin: "finite (\<psi> ` W)"
      using hWfin by (by100 simp)
    have h\<psi>Wne: "\<psi> ` W \<noteq> {}"
      using hWne by (by100 blast)
    have hF_cone:
        "geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'"
      using hcone h\<psi>Wfin h\<psi>Wne h\<psi>Wsub by (by100 blast)
    have hL_F:
        "geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F"
      using hiso_simplex hWsub by (by100 blast)
    show "geotop_convex_hull W \<in> L
      \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'"
      using hL_F hF_cone by (by100 blast)
  qed
  show ?thesis
    apply (rule_tac x=L' in exI)
    apply (rule_tac x=c in exI)
    using hc_int hsubdiv hcF hvertices hc_simplex hboundary_target hcone_target
    by (by100 simp)
qed

lemma geotop_fig410_cone_fan_from_boundary_subdivision_model_dev34:
  fixes K F :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hboundary:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hiso: "geotop_isomorphism (geotop_link K v) F \<psi>"
  shows "\<exists>L' c.
      geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Fig. 4.10, book step 2.  Add one new vertex in the interior of the
    2-simplex and cone the subdivided frontier to it; the old boundary
    simplexes remain boundary simplexes and each nonempty link simplex gives
    exactly one cone simplex. **)
proof -
  show ?thesis
    by (rule geotop_fig410_cone_fan_from_boundary_subdivision_and_isomorphism_dev34
        [OF h\<sigma> hboundary hiso])
qed

lemma geotop_fig410_cone_fan_from_boundary_subdivision_model_with_interior_dev34:
  fixes K F :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hboundary:
    "geotop_is_subdivision F
      (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
  assumes hiso: "geotop_isomorphism (geotop_link K v) F \<psi>"
  shows "\<exists>L' c.
      c \<in> interior \<sigma>
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Vertex-link specialization of the Fig. 4.10 cone wrapper, retaining the
    interior location of the new fan vertex. **)
proof -
  show ?thesis
    by (rule geotop_fig410_cone_fan_from_boundary_subdivision_and_isomorphism_with_interior_dev34
        [OF h\<sigma> hboundary hiso])
qed

lemma geotop_standard_boundary_cone_fan_with_link_isomorphism_from_finite_linear_link_polygon_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  assumes hlink_finite: "finite (geotop_link K v)"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
  shows "\<exists>(\<sigma> :: (real^2) set) F L' c \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_isomorphism (geotop_link K v) F \<psi>
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Moise Fig. 4.10 boundary model in intrinsic simplicial language.  The
    finite polygonal link is matched by a simplicial isomorphism to a
    subdivision \<open>F\<close> of the frontier of a 2-simplex; coning \<open>F\<close> from the new
    vertex \<open>c\<close> gives the full fan subdivision \<open>L'\<close>. **)
proof -
  obtain \<sigma> :: "(real^2) set" and F \<psi>
    where hboundary:
      "geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> geotop_isomorphism (geotop_link K v) F \<psi>"
    using geotop_fig410_boundary_subdivision_model_from_finite_linear_link_polygon_dev34
      [OF hK hv hlink_linear hlink_finite hpolygon]
    by (by100 blast)
  have h\<sigma>: "geotop_simplex_dim \<sigma> 2"
    using hboundary by (by100 blast)
  have hboundary_sub:
      "geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
    using hboundary by (by100 blast)
  have hiso: "geotop_isomorphism (geotop_link K v) F \<psi>"
    using hboundary by (by100 blast)
  have hcone_ex:
      "\<exists>L' c.
      geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
    by (rule geotop_fig410_cone_fan_from_boundary_subdivision_model_dev34
        [OF hK hv h\<sigma> hboundary_sub hiso])
  obtain L' c where hcone:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
    using hcone_ex by (elim exE) assumption
  have hsubdiv:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    using hcone by (by100 blast)
  have hcF: "c \<notin> geotop_complex_vertices F"
    using hcone by (by100 blast)
  have hvertices:
      "geotop_complex_vertices L' = insert c (geotop_complex_vertices F)"
    using hcone by (by100 blast)
  have hc_simplex: "geotop_convex_hull {c} \<in> L'"
    using hcone by (by100 blast)
  have hboundary_in_fan:
      "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
    using hcone by (by100 blast)
  have hcone_target:
      "\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L')"
    using hcone by (by100 blast)
  show ?thesis
    apply (rule_tac x=\<sigma> in exI)
    apply (rule_tac x=F in exI)
    apply (rule_tac x=L' in exI)
    apply (rule_tac x=c in exI)
    apply (rule_tac x=\<psi> in exI)
    using h\<sigma> hsubdiv hiso hcF hvertices hc_simplex hboundary_in_fan
      hcone_target
    by (by100 blast)
qed

lemma geotop_standard_boundary_cone_fan_with_link_isomorphism_from_finite_linear_link_polygon_with_interior_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  assumes hlink_finite: "finite (geotop_link K v)"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
  shows "\<exists>(\<sigma> :: (real^2) set) F L' c \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> c \<in> interior \<sigma>
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_isomorphism (geotop_link K v) F \<psi>
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Finite polygonal-link form of Fig. 4.10 with the target fan vertex kept
    in the ordinary interior of the chosen 2-simplex. **)
proof -
  obtain \<sigma> :: "(real^2) set" and F \<psi>
    where hboundary:
      "geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)
      \<and> geotop_isomorphism (geotop_link K v) F \<psi>"
    using geotop_fig410_boundary_subdivision_model_from_finite_linear_link_polygon_dev34
      [OF hK hv hlink_linear hlink_finite hpolygon]
    by (by100 blast)
  have h\<sigma>: "geotop_simplex_dim \<sigma> 2"
    using hboundary by (by100 blast)
  have hboundary_sub:
      "geotop_is_subdivision F
        (geotop_comb_boundary {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} 2)"
    using hboundary by (by100 blast)
  have hiso: "geotop_isomorphism (geotop_link K v) F \<psi>"
    using hboundary by (by100 blast)
  have hcone_ex:
      "\<exists>L' c.
      c \<in> interior \<sigma>
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
    by (rule geotop_fig410_cone_fan_from_boundary_subdivision_model_with_interior_dev34
        [OF hK hv h\<sigma> hboundary_sub hiso])
  obtain L' c where hcone:
      "c \<in> interior \<sigma>
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
    using hcone_ex by (elim exE) assumption
  show ?thesis
    apply (rule_tac x=\<sigma> in exI)
    apply (rule_tac x=F in exI)
    apply (rule_tac x=L' in exI)
    apply (rule_tac x=c in exI)
    apply (rule_tac x=\<psi> in exI)
    using h\<sigma> hiso hcone
    by (by100 simp)
qed

lemma geotop_standard_boundary_cone_model_from_finite_linear_link_polygon_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  assumes hlink_finite: "finite (geotop_link K v)"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
  shows "\<exists>(\<sigma> :: (real^2) set) F L' B c \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F))
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Moise Fig. 4.10, split at the book's two construction steps.  First
    subdivide the frontier of a 2-simplex to a boundary complex \<open>F\<close> whose
    ordered vertices/edges are simplicially isomorphic to the finite link.
    Then add the new non-frontier vertex \<open>c\<close> and cone \<open>F\<close> to obtain the
    full subdivided 2-simplex complex \<open>L'\<close>. **)
proof -
  obtain \<sigma> :: "(real^2) set" and F L' c \<psi>
    where hmodel:
      "geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_isomorphism (geotop_link K v) F \<psi>
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
    using geotop_standard_boundary_cone_fan_with_link_isomorphism_from_finite_linear_link_polygon_dev34
      [OF hK hv hlink_linear hlink_finite hpolygon]
    by (elim exE) assumption
  have hdim: "geotop_simplex_dim \<sigma> 2"
    using hmodel by (by100 simp)
  have hsubdiv:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    using hmodel by (by100 simp)
  have hiso: "geotop_isomorphism (geotop_link K v) F \<psi>"
    using hmodel by (by100 simp)
  have h\<psi>: "bij_betw \<psi> (geotop_complex_vertices (geotop_link K v))
      (geotop_complex_vertices F)"
    using hiso unfolding geotop_isomorphism_def by (by100 blast)
  have hcB: "c \<notin> geotop_complex_vertices F"
    using hmodel by (by100 simp)
  have hL_vertices:
      "geotop_complex_vertices L' = insert c (geotop_complex_vertices F)"
    using hmodel by (by100 simp)
  have hcone_vertex_target: "geotop_convex_hull {c} \<in> L'"
    using hmodel by (by100 simp)
  have hboundary_target:
      "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F)"
    using hiso unfolding geotop_isomorphism_def by (by100 blast)
  have hboundary_in_fan:
      "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
    using hmodel by (by100 simp)
  have hcone_target:
      "\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L')"
    using hmodel by (by100 simp)
  show ?thesis
    apply (rule_tac x=\<sigma> in exI)
    apply (rule_tac x=F in exI)
    apply (rule_tac x=L' in exI)
    apply (rule_tac x="geotop_complex_vertices F" in exI)
    apply (rule_tac x=c in exI)
    apply (rule_tac x=\<psi> in exI)
    using hdim hsubdiv h\<psi> hcB hL_vertices hcone_vertex_target
      hboundary_target hboundary_in_fan hcone_target
    by (by100 blast)
qed

lemma geotop_standard_boundary_cone_model_from_finite_linear_link_polygon_with_interior_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  assumes hlink_finite: "finite (geotop_link K v)"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
  shows "\<exists>(\<sigma> :: (real^2) set) F L' B c \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> c \<in> interior \<sigma>
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F))
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Boundary-cone model with the new fan vertex explicitly retained in the
    interior of the target 2-simplex. **)
proof -
  obtain \<sigma> :: "(real^2) set" and F L' c \<psi>
    where hmodel:
      "geotop_simplex_dim \<sigma> 2
      \<and> c \<in> interior \<sigma>
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_isomorphism (geotop_link K v) F \<psi>
      \<and> c \<notin> geotop_complex_vertices F
      \<and> geotop_complex_vertices L' = insert c (geotop_complex_vertices F)
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
    using geotop_standard_boundary_cone_fan_with_link_isomorphism_from_finite_linear_link_polygon_with_interior_dev34
      [OF hK hv hlink_linear hlink_finite hpolygon]
    by (elim exE) assumption
  have hdim: "geotop_simplex_dim \<sigma> 2"
    using hmodel by (by100 simp)
  have hc_int: "c \<in> interior \<sigma>"
    using hmodel by (by100 simp)
  have hsubdiv:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    using hmodel by (by100 simp)
  have hiso: "geotop_isomorphism (geotop_link K v) F \<psi>"
    using hmodel by (by100 simp)
  have h\<psi>: "bij_betw \<psi> (geotop_complex_vertices (geotop_link K v))
      (geotop_complex_vertices F)"
    using hiso unfolding geotop_isomorphism_def by (by100 blast)
  have hcB: "c \<notin> geotop_complex_vertices F"
    using hmodel by (by100 simp)
  have hL_vertices:
      "geotop_complex_vertices L' = insert c (geotop_complex_vertices F)"
    using hmodel by (by100 simp)
  have hcone_vertex_target: "geotop_convex_hull {c} \<in> L'"
    using hmodel by (by100 simp)
  have hboundary_target:
      "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F)"
    using hiso unfolding geotop_isomorphism_def by (by100 blast)
  have hboundary_in_fan:
      "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
    using hmodel by (by100 simp)
  have hcone_target:
      "\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L')"
    using hmodel by (by100 simp)
  show ?thesis
    apply (rule_tac x=\<sigma> in exI)
    apply (rule_tac x=F in exI)
    apply (rule_tac x=L' in exI)
    apply (rule_tac x="geotop_complex_vertices F" in exI)
    apply (rule_tac x=c in exI)
    apply (rule_tac x=\<psi> in exI)
    using hdim hc_int hsubdiv h\<psi> hcB hL_vertices hcone_vertex_target
      hboundary_target hboundary_in_fan hcone_target
    by (by100 simp)
qed


lemma geotop_standard_fan_target_from_finite_linear_link_polygon_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  assumes hlink_finite: "finite (geotop_link K v)"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
  shows "\<exists>(\<sigma> :: (real^2) set) L' B c \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Moise Fig. 4.10 construction obligation.  From the finite polygonal link,
    use the cyclic order to subdivide the frontier of a 2-simplex with matching
    edge data; then add one non-frontier vertex and
    cone the subdivided frontier to it.  The map \<open>\<psi>\<close> is the induced
    order-preserving vertex bijection from the old link to the subdivided
    frontier. **)
proof -
  obtain \<sigma> :: "(real^2) set" and F L' B c \<psi>
    where hmodel:
      "geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F))
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
    using geotop_standard_boundary_cone_model_from_finite_linear_link_polygon_dev34
      [OF hK hv hlink_linear hlink_finite hpolygon]
    by (elim exE) assumption
  have hdim: "geotop_simplex_dim \<sigma> 2"
    using hmodel by (by100 simp)
  have hsubdiv:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    using hmodel by (by100 simp)
  have h\<psi>: "bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B"
    using hmodel by (by100 simp)
  have hcB: "c \<notin> B"
    using hmodel by (by100 simp)
  have hL_vertices: "geotop_complex_vertices L' = insert c B"
    using hmodel by (by100 simp)
  have hcone_vertex_target: "geotop_convex_hull {c} \<in> L'"
    using hmodel by (by100 simp)
  have hboundary_target:
      "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F)"
    using hmodel by (by100 simp)
  have hboundary_in_fan:
      "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
    using hmodel by (by100 simp)
  have hcone_target:
      "\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L')"
    using hmodel by (by100 simp)
  have hlink_target:
      "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
  proof (intro allI impI)
    fix W
    assume hW: "W \<subseteq> geotop_complex_vertices (geotop_link K v)"
    have hWF:
        "geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F"
      using hboundary_target hW by (by100 blast)
    have hFL:
        "geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'"
      using hboundary_in_fan hW by (by100 blast)
    show "geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'"
      using hWF hFL by (by100 blast)
  qed
  show ?thesis
    using hdim hsubdiv h\<psi> hcB hL_vertices hcone_vertex_target
      hlink_target hcone_target by (by100 blast)
qed

lemma geotop_standard_fan_target_from_finite_linear_link_polygon_with_interior_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  assumes hlink_finite: "finite (geotop_link K v)"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
  shows "\<exists>(\<sigma> :: (real^2) set) L' B c \<psi>.
      geotop_simplex_dim \<sigma> 2
      \<and> c \<in> interior \<sigma>
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Fig. 4.10 fan target data with the intermediate boundary complex removed,
    retaining that the cone vertex is an ordinary interior point of the target
    2-simplex. **)
proof -
  obtain \<sigma> :: "(real^2) set" and F L' B c \<psi>
    where hmodel:
      "geotop_simplex_dim \<sigma> 2
      \<and> c \<in> interior \<sigma>
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F))
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
    using geotop_standard_boundary_cone_model_from_finite_linear_link_polygon_with_interior_dev34
      [OF hK hv hlink_linear hlink_finite hpolygon]
    by (elim exE) assumption
  have hdim: "geotop_simplex_dim \<sigma> 2"
    using hmodel by (by100 simp)
  have hc_int: "c \<in> interior \<sigma>"
    using hmodel by (by100 simp)
  have hsubdiv:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    using hmodel by (by100 simp)
  have h\<psi>: "bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B"
    using hmodel by (by100 simp)
  have hcB: "c \<notin> B"
    using hmodel by (by100 simp)
  have hL_vertices: "geotop_complex_vertices L' = insert c B"
    using hmodel by (by100 simp)
  have hcone_vertex_target: "geotop_convex_hull {c} \<in> L'"
    using hmodel by (by100 simp)
  have hboundary_target:
      "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F)"
    using hmodel by (by100 simp)
  have hboundary_in_fan:
      "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
    using hmodel by (by100 simp)
  have hcone_target:
      "\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L')"
    using hmodel by (by100 simp)
  have hlink_target:
      "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
  proof (intro allI impI)
    fix W
    assume hW: "W \<subseteq> geotop_complex_vertices (geotop_link K v)"
    have hWF:
        "geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> F"
      using hboundary_target hW by (by100 blast)
    have hFL:
        "geotop_convex_hull (\<psi> ` W) \<in> F
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'"
      using hboundary_in_fan hW by (by100 blast)
    show "geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'"
      using hWF hFL by (by100 blast)
  qed
  show ?thesis
    apply (rule_tac x=\<sigma> in exI)
    apply (rule_tac x=L' in exI)
    apply (rule_tac x=B in exI)
    apply (rule_tac x=c in exI)
    apply (rule_tac x=\<psi> in exI)
    using hdim hc_int hsubdiv h\<psi> hcB hL_vertices hcone_vertex_target
      hlink_target hcone_target by (by100 simp)
qed

lemma geotop_vertex_star_standard_fan_isomorphism_from_finite_linear_link_polygon_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  assumes hlink_finite: "finite (geotop_link K v)"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
  shows "\<exists>(\<sigma> :: (real^2) set) L' \<phi>.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_isomorphism (geotop_star K v) L' \<phi>"
  (**
    Moise Fig. 4.10 with the simplicial bijection made explicit.  The missing
    combinatorial content is to enumerate the finite polygonal link as an
    edge-cycle, subdivide \<open>Fr \<sigma>\<close> with the same ordered
    edge data, and define \<open>\<phi>\<close> on vertices by the corresponding order-preserving
    match, with \<open>v\<close> sent to the new cone vertex. **)
proof -
  obtain \<sigma> :: "(real^2) set" and L' B c \<psi>
    where htarget:
      "geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
    using geotop_standard_fan_target_from_finite_linear_link_polygon_dev34
      [OF hK hv hlink_linear hlink_finite hpolygon]
    by (elim exE) assumption
  have hstar_vertices_finite:
      "finite (geotop_complex_vertices (geotop_star K v))"
    using geotop_fig410_link_and_star_vertices_finite_dev34
      [OF hK hv hlink_finite]
    by (by100 blast)
  define \<phi> where "\<phi> x = (if x = v then c else \<psi> x)" for x
  have hdim: "geotop_simplex_dim \<sigma> 2"
    using htarget by (by100 simp)
  have hsubdiv:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    using htarget by (by100 simp)
  have h\<psi>: "bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B"
    using htarget by (by100 simp)
  have hcB: "c \<notin> B"
    using htarget by (by100 simp)
  have hL_vertices: "geotop_complex_vertices L' = insert c B"
    using htarget by (by100 simp)
  have hcone_vertex_target: "geotop_convex_hull {c} \<in> L'"
    using htarget by (by100 simp)
  have hlink_target:
      "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
    using htarget by (by100 simp)
  have hcone_target:
      "\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L')"
    using htarget by (by100 simp)
  have hiso_raw:
      "geotop_isomorphism (geotop_star K v) L'
        (\<lambda>x. if x = v then c else \<psi> x)"
    by (rule_tac geotop_star_fan_isomorphism_from_link_and_cone_target_cases_dev34
        [OF hK hv h\<psi> hcB hL_vertices hstar_vertices_finite
          hlink_target hcone_vertex_target hcone_target])
  have h\<phi>_eq: "\<phi> = (\<lambda>x. if x = v then c else \<psi> x)"
    using \<phi>_def by (by100 blast)
  have hiso: "geotop_isomorphism (geotop_star K v) L' \<phi>"
    using hiso_raw h\<phi>_eq by (by100 simp)
  show ?thesis
    using hdim hsubdiv hiso by (by100 blast)
qed


lemma geotop_vertex_star_standard_fan_model_from_finite_linear_link_polygon_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  assumes hlink_finite: "finite (geotop_link K v)"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
  shows "\<exists>(\<sigma> :: (real^2) set) L'.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_isomorphic (geotop_star K v) L'"
  (**
    Moise Fig. 4.10, isolated in the exact form used below.  Subdivide the
    frontier of a 2-simplex so its edge-cycle has the same combinatorial
    order as the finite polygonal link, add one interior vertex, and cone that
    subdivided frontier to the new vertex.  The simplicial bijection sends
    \<open>v\<close> to the new cone vertex and sends the link vertices, in cyclic
    order, to the subdivided frontier vertices. **)
proof -
  obtain \<sigma> :: "(real^2) set" and L' \<phi>
    where hfan:
      "geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_isomorphism (geotop_star K v) L' \<phi>"
    using geotop_vertex_star_standard_fan_isomorphism_from_finite_linear_link_polygon_dev34
      [OF hK hv hlink_linear hlink_finite hpolygon]
    by (by100 blast)
  show ?thesis
    unfolding geotop_isomorphic_def using hfan by (by100 blast)
qed

lemma geotop_finite_linear_graph_broken_line_connected_endpoint_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hbroken: "geotop_is_broken_line (geotop_polyhedron L)"
  shows "geotop_complex_connected L
      \<and> (\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w)"
  (**
    Broken-line chain prerequisite for the boundary-vertex Fig. 4.10 case:
    the carrier is an arc, hence connected, and one of the arc endpoints is a
    graph endpoint of the finite linear complex. **)
proof -
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL_linear])
  have harc_geo: "geotop_is_arc (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    using hbroken unfolding geotop_is_broken_line_def by (by100 blast)
  obtain \<gamma> :: "real \<Rightarrow> real^2"
    where h\<gamma>_arc: "arc \<gamma>"
      and h\<gamma>_img: "path_image \<gamma> = geotop_polyhedron L"
    using geotop_is_arc_imp_HOL_arc[OF harc_geo] by (by100 blast)
  have hpoly_conn_HOL: "connected (geotop_polyhedron L)"
    using connected_arc_image[OF h\<gamma>_arc] h\<gamma>_img by (by100 simp)
  have hpoly_conn: "top1_connected_on (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    using hpoly_conn_HOL top1_connected_on_geotop_iff_connected by (by100 blast)
  have hpath: "top1_path_connected_on (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    by (rule iffD2[OF Theorem_GT_1_12(2)[OF hL_complex] hpoly_conn])
  have hconn: "geotop_complex_connected L"
    by (rule iffD2[OF Theorem_GT_1_12(1)[OF hL_complex] hpath])
  have hend: "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
    by (rule geotop_broken_line_polyhedron_finite_linear_graph_has_endpoint_dev34
        [OF hL_linear hL_finite hbroken])
  show ?thesis
    using hconn hend by (by100 blast)
qed

definition geotop_linear_graph_endpoint_chain_listing_dev34 ::
  "(real^2) set set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) list \<Rightarrow> bool"
where
  "geotop_linear_graph_endpoint_chain_listing_dev34 L w q vs \<longleftrightarrow>
    2 \<le> length vs
    \<and> vs ! 0 = w
    \<and> vs ! 1 = q
    \<and> distinct vs
    \<and> set vs = geotop_complex_vertices L
    \<and> (\<forall>v \<in> set vs. {v} \<in> L)
    \<and> (\<forall>i < length vs - 1.
      closed_segment (vs ! i) (vs ! Suc i) \<in> L
      \<and> geotop_is_edge (closed_segment (vs ! i) (vs ! Suc i)))
    \<and> {e \<in> L. geotop_is_edge e}
      = ((\<lambda>i. closed_segment (vs ! i) (vs ! Suc i)) ` {0..<length vs - 1})"

lemma geotop_endpoint_chain_listing_length_ge2_dev34:
  assumes hlist: "geotop_linear_graph_endpoint_chain_listing_dev34 L w q vs"
  shows "2 \<le> length vs"
  using hlist unfolding geotop_linear_graph_endpoint_chain_listing_dev34_def
  by (by100 blast)

lemma geotop_endpoint_chain_listing_vertices_eq_dev34:
  assumes hlist: "geotop_linear_graph_endpoint_chain_listing_dev34 L w q vs"
  shows "set vs = geotop_complex_vertices L"
  using hlist unfolding geotop_linear_graph_endpoint_chain_listing_dev34_def
  by (by100 blast)

lemma geotop_endpoint_chain_listing_first_vertices_dev34:
  assumes hlist: "geotop_linear_graph_endpoint_chain_listing_dev34 L w q vs"
  shows "vs ! 0 = w \<and> vs ! 1 = q"
  using hlist unfolding geotop_linear_graph_endpoint_chain_listing_dev34_def
  by (by100 blast)

lemma geotop_endpoint_chain_listing_edge_set_eq_dev34:
  assumes hlist: "geotop_linear_graph_endpoint_chain_listing_dev34 L w q vs"
  shows "{e \<in> L. geotop_is_edge e}
      = ((\<lambda>i. closed_segment (vs ! i) (vs ! Suc i)) ` {0..<length vs - 1})"
  using hlist unfolding geotop_linear_graph_endpoint_chain_listing_dev34_def
  by (by100 blast)

lemma geotop_endpoint_chain_listing_first_edge_dev34:
  assumes hlist: "geotop_linear_graph_endpoint_chain_listing_dev34 L w q vs"
  shows "closed_segment w q \<in> L \<and> geotop_is_edge (closed_segment w q)"
proof -
  have hlen: "2 \<le> length vs"
    by (rule geotop_endpoint_chain_listing_length_ge2_dev34[OF hlist])
  have h0_lt: "0 < length vs - 1"
    using hlen by (by100 linarith)
  have hstep:
      "closed_segment (vs ! 0) (vs ! Suc 0) \<in> L
      \<and> geotop_is_edge (closed_segment (vs ! 0) (vs ! Suc 0))"
    using hlist h0_lt unfolding geotop_linear_graph_endpoint_chain_listing_dev34_def
    by (by100 blast)
  have hfirst: "vs ! 0 = w \<and> vs ! 1 = q"
    by (rule geotop_endpoint_chain_listing_first_vertices_dev34[OF hlist])
  show ?thesis
    using hstep hfirst by (by100 simp)
qed

lemma geotop_endpoint_chain_listing_two_vertex_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hendpoint: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes he_edge: "geotop_is_edge e"
  assumes hw_e: "w \<in> e"
  assumes hq_ne: "q \<noteq> w"
  assumes he_seg: "e = closed_segment w q"
  assumes hqL: "{q} \<in> L"
  assumes hq_card: "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 1"
  shows "geotop_linear_graph_endpoint_chain_listing_dev34 L w q [w, q]"
  (**
    Endpoint-chain base case in the book induction.  If the first neighbor
    \<open>q\<close> is also the other degree-one endpoint, connectedness forces the
    linear graph to consist only of \<open>{w}\<close>, \<open>{q}\<close>, and the edge
    \<open>closed_segment w q\<close>, so the two-vertex list is the whole chain. **)
proof -
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL_linear])
  have hwL: "{w} \<in> L"
    using geotop_graph_endpoint_singleton_and_card_one_dev34
        [OF hL_linear hendpoint]
    by (by100 blast)
  have hexhaust: "L - {{w}, {q}, e} = {}"
    by (rule geotop_two_degree_one_endpoint_edge_connected_exhausts_dev34
        [OF hL_linear hL_finite hconn hendpoint hqL hq_card
          heL he_edge hw_e hq_ne he_seg])
  have hL_sub: "L \<subseteq> {{w}, {q}, e}"
    using hexhaust by (by100 blast)
  have hvertices_subset: "geotop_complex_vertices L \<subseteq> {w, q}"
  proof
    fix x
    assume hx: "x \<in> geotop_complex_vertices L"
    have hxL: "{x} \<in> L"
      using hx geotop_complex_vertices_eq_0_simplexes[OF hL_complex]
      by (by100 simp)
    have hcase: "{x} = {w} \<or> {x} = {q} \<or> {x} = e"
      using hL_sub hxL by (by100 blast)
    show "x \<in> {w, q}"
    proof (rule disjE[OF hcase])
      assume "{x} = {w}"
      thus ?thesis by (by100 simp)
    next
      assume hrest: "{x} = {q} \<or> {x} = e"
      show ?thesis
      proof (rule disjE[OF hrest])
        assume "{x} = {q}"
        thus ?thesis by (by100 simp)
      next
        assume hx_e: "{x} = e"
        have "geotop_is_edge {x}"
          using he_edge hx_e by (by100 simp)
        moreover have "\<not> geotop_is_edge {x}"
          by (rule geotop_singleton_not_edge_prefix)
        ultimately show ?thesis
          by (by100 blast)
      qed
    qed
  qed
  have hvertices_supset: "{w, q} \<subseteq> geotop_complex_vertices L"
  proof
    fix x
    assume hx: "x \<in> {w, q}"
    have "{x} \<in> L"
      using hx hwL hqL by (by100 blast)
    thus "x \<in> geotop_complex_vertices L"
      using geotop_complex_vertices_eq_0_simplexes[OF hL_complex]
      by (by100 simp)
  qed
  have hvertices_eq: "set [w, q] = geotop_complex_vertices L"
    using hvertices_subset hvertices_supset by (by100 simp)
  have hedge_set_eq: "{d \<in> L. geotop_is_edge d} = {e}"
  proof
    show "{d \<in> L. geotop_is_edge d} \<subseteq> {e}"
    proof
      fix d
      assume hd: "d \<in> {d \<in> L. geotop_is_edge d}"
      have hdL: "d \<in> L"
        using hd by (by100 simp)
      have hdedge: "geotop_is_edge d"
        using hd by (by100 simp)
      have hcase: "d = {w} \<or> d = {q} \<or> d = e"
        using hL_sub hdL by (by100 blast)
      show "d \<in> {e}"
      proof (rule disjE[OF hcase])
        assume hdw: "d = {w}"
        have "\<not> geotop_is_edge {w}"
          by (rule geotop_singleton_not_edge_prefix)
        thus ?thesis
          using hdedge hdw by (by100 blast)
      next
        assume hrest: "d = {q} \<or> d = e"
        show ?thesis
        proof (rule disjE[OF hrest])
          assume hdq: "d = {q}"
          have "\<not> geotop_is_edge {q}"
            by (rule geotop_singleton_not_edge_prefix)
          thus ?thesis
            using hdedge hdq by (by100 blast)
        next
          assume "d = e"
          thus ?thesis by (by100 simp)
        qed
      qed
    qed
  next
    show "{e} \<subseteq> {d \<in> L. geotop_is_edge d}"
      using heL he_edge by (by100 simp)
  qed
  have hedge_image:
      "{d \<in> L. geotop_is_edge d}
        = ((\<lambda>i. closed_segment ([w, q] ! i) ([w, q] ! Suc i))
            ` {0..<length [w, q] - 1})"
    using hedge_set_eq he_seg by (by100 simp)
  have hsteps: "\<forall>i < length [w, q] - 1.
      closed_segment ([w, q] ! i) ([w, q] ! Suc i) \<in> L
      \<and> geotop_is_edge (closed_segment ([w, q] ! i) ([w, q] ! Suc i))"
    using heL he_edge he_seg by (by100 simp)
  have hvertex_singletons: "\<forall>v \<in> set [w, q]. {v} \<in> L"
    using hwL hqL by (by100 simp)
  show ?thesis
    unfolding geotop_linear_graph_endpoint_chain_listing_dev34_def
    using hq_ne hvertices_eq hvertex_singletons hsteps hedge_image
    by (by100 simp)
qed

lemma geotop_delete_leaf_complex_vertices_eq_insert_endpoint_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hendpoint: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes he_edge: "geotop_is_edge e"
  assumes hw_e: "w \<in> e"
  shows "geotop_complex_vertices L =
    insert w (geotop_complex_vertices (L - {{w}, e}))"
proof -
  let ?R = "L - {{w}, e}"
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL_linear])
  have hR_complex: "geotop_is_complex ?R"
    by (rule geotop_graph_endpoint_delete_leaf_complex_dev34
        [OF hL_linear hL_finite hendpoint heL he_edge hw_e])
  have hwL: "{w} \<in> L"
    using geotop_graph_endpoint_singleton_and_card_one_dev34
        [OF hL_linear hendpoint]
    by (by100 blast)
  show ?thesis
  proof (rule equalityI)
    show "geotop_complex_vertices L
        \<subseteq> insert w (geotop_complex_vertices ?R)"
    proof
      fix x
      assume hx: "x \<in> geotop_complex_vertices L"
      have hxL: "{x} \<in> L"
        using hx geotop_complex_vertices_eq_0_simplexes[OF hL_complex]
        by (by100 simp)
      show "x \<in> insert w (geotop_complex_vertices ?R)"
      proof (cases "x = w")
        case True
        thus ?thesis by (by100 simp)
      next
        case False
        have hx_ne_w: "{x} \<noteq> {w}"
          using False by (by100 simp)
        have hx_ne_e: "{x} \<noteq> e"
        proof
          assume hx_e: "{x} = e"
          have "geotop_is_edge {x}"
            using he_edge hx_e by (by100 simp)
          moreover have "\<not> geotop_is_edge {x}"
            by (rule geotop_singleton_not_edge_prefix)
          ultimately show False
            by (by100 blast)
        qed
        have "{x} \<in> ?R"
          using hxL hx_ne_w hx_ne_e by (by100 blast)
        thus ?thesis
          using geotop_complex_vertices_eq_0_simplexes[OF hR_complex]
          by (by100 simp)
      qed
    qed
  next
    show "insert w (geotop_complex_vertices ?R)
        \<subseteq> geotop_complex_vertices L"
    proof
      fix x
      assume hx: "x \<in> insert w (geotop_complex_vertices ?R)"
      show "x \<in> geotop_complex_vertices L"
      proof (cases "x = w")
        case True
        thus ?thesis
          using hwL geotop_complex_vertices_eq_0_simplexes[OF hL_complex]
          by (by100 simp)
      next
        case False
        have hxR: "x \<in> geotop_complex_vertices ?R"
          using hx False by (by100 simp)
        have "{x} \<in> ?R"
          using hxR geotop_complex_vertices_eq_0_simplexes[OF hR_complex]
          by (by100 simp)
        hence "{x} \<in> L"
          by (by100 blast)
        thus ?thesis
          using geotop_complex_vertices_eq_0_simplexes[OF hL_complex]
          by (by100 simp)
      qed
    qed
  qed
qed

lemma geotop_delete_leaf_edge_set_eq_insert_deleted_edge_dev34:
  fixes L :: "(real^2) set set"
  assumes heL: "e \<in> L"
  assumes he_edge: "geotop_is_edge e"
  shows "{d \<in> L. geotop_is_edge d}
    = insert e {d \<in> L - {{w}, e}. geotop_is_edge d}"
proof (rule equalityI)
  show "{d \<in> L. geotop_is_edge d}
      \<subseteq> insert e {d \<in> L - {{w}, e}. geotop_is_edge d}"
  proof
    fix d
    assume hd: "d \<in> {d \<in> L. geotop_is_edge d}"
    have hdL: "d \<in> L"
      using hd by (by100 simp)
    have hd_edge: "geotop_is_edge d"
      using hd by (by100 simp)
    show "d \<in> insert e {d \<in> L - {{w}, e}. geotop_is_edge d}"
    proof (cases "d = e")
      case True
      thus ?thesis by (by100 simp)
    next
      case False
      have hd_ne_singleton: "d \<noteq> {w}"
      proof
        assume hdw: "d = {w}"
        have "\<not> geotop_is_edge {w}"
          by (rule geotop_singleton_not_edge_prefix)
        thus False
          using hd_edge hdw by (by100 blast)
      qed
      have "d \<in> L - {{w}, e}"
        using hdL hd_ne_singleton False by (by100 blast)
      thus ?thesis
        using hd_edge by (by100 blast)
    qed
  qed
next
  show "insert e {d \<in> L - {{w}, e}. geotop_is_edge d}
      \<subseteq> {d \<in> L. geotop_is_edge d}"
  proof
    fix d
    assume hd: "d \<in> insert e {d \<in> L - {{w}, e}. geotop_is_edge d}"
    show "d \<in> {d \<in> L. geotop_is_edge d}"
    proof (cases "d = e")
      case True
      thus ?thesis
        using heL he_edge by (by100 simp)
    next
      case False
      thus ?thesis
        using hd by (by100 blast)
    qed
  qed
qed

lemma geotop_chain_edge_image_cons_dev34:
  fixes vs :: "(real^2) list"
  assumes hlen: "2 \<le> length vs"
  shows "((\<lambda>i. closed_segment ((w # vs) ! i) ((w # vs) ! Suc i))
      ` {0..<length (w # vs) - 1})
    = insert (closed_segment w (vs ! 0))
        ((\<lambda>i. closed_segment (vs ! i) (vs ! Suc i))
          ` {0..<length vs - 1})"
proof (rule equalityI)
  show "((\<lambda>i. closed_segment ((w # vs) ! i) ((w # vs) ! Suc i))
      ` {0..<length (w # vs) - 1})
    \<subseteq> insert (closed_segment w (vs ! 0))
        ((\<lambda>i. closed_segment (vs ! i) (vs ! Suc i))
          ` {0..<length vs - 1})"
  proof
    fix a
    assume ha: "a \<in> ((\<lambda>i. closed_segment ((w # vs) ! i) ((w # vs) ! Suc i))
      ` {0..<length (w # vs) - 1})"
    obtain i where hi: "i \<in> {0..<length (w # vs) - 1}"
      and ha_eq: "a = closed_segment ((w # vs) ! i) ((w # vs) ! Suc i)"
      using ha by (by100 blast)
    have hi_lt: "i < length vs"
      using hi by (by100 simp)
    show "a \<in> insert (closed_segment w (vs ! 0))
        ((\<lambda>i. closed_segment (vs ! i) (vs ! Suc i))
          ` {0..<length vs - 1})"
    proof (cases i)
      case 0
      thus ?thesis
        using ha_eq by (by100 simp)
    next
      case (Suc j)
      have hj_lt: "j < length vs - 1"
        using Suc hi_lt by (by100 linarith)
      have "a = closed_segment (vs ! j) (vs ! Suc j)"
        using ha_eq Suc by (by100 simp)
      moreover have "j \<in> {0..<length vs - 1}"
        using hj_lt by (by100 simp)
      ultimately show ?thesis
        by (by100 blast)
    qed
  qed
next
  show "insert (closed_segment w (vs ! 0))
      ((\<lambda>i. closed_segment (vs ! i) (vs ! Suc i))
        ` {0..<length vs - 1})
    \<subseteq> ((\<lambda>i. closed_segment ((w # vs) ! i) ((w # vs) ! Suc i))
      ` {0..<length (w # vs) - 1})"
  proof
    fix a
    assume ha: "a \<in> insert (closed_segment w (vs ! 0))
      ((\<lambda>i. closed_segment (vs ! i) (vs ! Suc i))
        ` {0..<length vs - 1})"
    show "a \<in> ((\<lambda>i. closed_segment ((w # vs) ! i) ((w # vs) ! Suc i))
      ` {0..<length (w # vs) - 1})"
    proof (rule insertE[OF ha])
      assume ha_first: "a = closed_segment w (vs ! 0)"
      have hvs_nonempty: "vs \<noteq> []"
      proof
        assume hnil: "vs = []"
        have "length vs = 0"
          using hnil by (by100 simp)
        thus False
          using hlen by (by100 linarith)
      qed
      have "0 \<in> {0..<length (w # vs) - 1}"
        using hvs_nonempty by (by100 simp)
      show ?thesis
      proof (rule image_eqI[where x = 0])
        show "a = closed_segment ((w # vs) ! 0) ((w # vs) ! Suc 0)"
          using ha_first by (by100 simp)
        show "0 \<in> {0..<length (w # vs) - 1}"
          by (rule \<open>0 \<in> {0..<length (w # vs) - 1}\<close>)
      qed
    next
      assume ha_rest: "a \<in> ((\<lambda>i. closed_segment (vs ! i) (vs ! Suc i))
        ` {0..<length vs - 1})"
      obtain j where hj: "j \<in> {0..<length vs - 1}"
        and ha_eq: "a = closed_segment (vs ! j) (vs ! Suc j)"
        using ha_rest by (by100 blast)
      have hSuc_range: "Suc j \<in> {0..<length (w # vs) - 1}"
        using hj by (by100 simp)
      have "a = closed_segment ((w # vs) ! Suc j) ((w # vs) ! Suc (Suc j))"
        using ha_eq by (by100 simp)
      thus ?thesis
        using hSuc_range by (by100 blast)
    qed
  qed
qed

lemma geotop_endpoint_chain_listing_cons_delete_leaf_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hendpoint: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes he_edge: "geotop_is_edge e"
  assumes hw_e: "w \<in> e"
  assumes hq_ne: "q \<noteq> w"
  assumes he_seg: "e = closed_segment w q"
  assumes hlistR:
    "geotop_linear_graph_endpoint_chain_listing_dev34 (L - {{w}, e}) q r vs"
  shows "geotop_linear_graph_endpoint_chain_listing_dev34 L w q (w # vs)"
proof -
  let ?R = "L - {{w}, e}"
  have hlenR: "2 \<le> length vs"
    by (rule geotop_endpoint_chain_listing_length_ge2_dev34[OF hlistR])
  have hfirstR: "vs ! 0 = q \<and> vs ! 1 = r"
    by (rule geotop_endpoint_chain_listing_first_vertices_dev34[OF hlistR])
  have hverticesR: "set vs = geotop_complex_vertices ?R"
    by (rule geotop_endpoint_chain_listing_vertices_eq_dev34[OF hlistR])
  have hstepsR: "\<forall>i < length vs - 1.
      closed_segment (vs ! i) (vs ! Suc i) \<in> ?R
      \<and> geotop_is_edge (closed_segment (vs ! i) (vs ! Suc i))"
    using hlistR unfolding geotop_linear_graph_endpoint_chain_listing_dev34_def
    by (by100 blast)
  have hedgeR: "{d \<in> ?R. geotop_is_edge d}
      = ((\<lambda>i. closed_segment (vs ! i) (vs ! Suc i))
          ` {0..<length vs - 1})"
    by (rule geotop_endpoint_chain_listing_edge_set_eq_dev34[OF hlistR])
  have hverticesL: "geotop_complex_vertices L =
      insert w (geotop_complex_vertices ?R)"
    by (rule geotop_delete_leaf_complex_vertices_eq_insert_endpoint_dev34
        [OF hL_linear hL_finite hendpoint heL he_edge hw_e])
  have hR_complex: "geotop_is_complex ?R"
    by (rule geotop_graph_endpoint_delete_leaf_complex_dev34
        [OF hL_linear hL_finite hendpoint heL he_edge hw_e])
  have hw_not_R_vertices: "w \<notin> geotop_complex_vertices ?R"
  proof -
    have hw_not_poly: "w \<notin> geotop_polyhedron ?R"
      by (rule geotop_graph_endpoint_not_in_delete_leaf_polyhedron_dev34
          [OF hL_linear hL_finite hendpoint heL he_edge hw_e])
    have hvertices_poly: "geotop_complex_vertices ?R \<subseteq> geotop_polyhedron ?R"
      by (rule geotop_complex_vertices_subset_polyhedron_dev34)
    show ?thesis
      using hw_not_poly hvertices_poly by (by100 blast)
  qed
  have hdistinct_cons: "distinct (w # vs)"
  proof -
    have hdistinctR: "distinct vs"
      using hlistR unfolding geotop_linear_graph_endpoint_chain_listing_dev34_def
      by (by100 blast)
    have "w \<notin> set vs"
      using hverticesR hw_not_R_vertices by (by100 simp)
    thus ?thesis
      using hdistinctR by (by100 simp)
  qed
  have hvertices_cons: "set (w # vs) = geotop_complex_vertices L"
    using hverticesR hverticesL by (by100 simp)
  have hvertex_singletons: "\<forall>v \<in> set (w # vs). {v} \<in> L"
  proof -
    have hwL: "{w} \<in> L"
      using geotop_graph_endpoint_singleton_and_card_one_dev34
          [OF hL_linear hendpoint]
      by (by100 blast)
    have hsingleR: "\<forall>v \<in> set vs. {v} \<in> ?R"
    proof
      fix v
      assume hv: "v \<in> set vs"
      have "v \<in> geotop_complex_vertices ?R"
        using hverticesR hv by (by100 simp)
      thus "{v} \<in> ?R"
        using geotop_complex_vertices_eq_0_simplexes[OF hR_complex]
        by (by100 simp)
    qed
    show ?thesis
    proof
      fix v
      assume hv: "v \<in> set (w # vs)"
      have hcase: "v = w \<or> v \<in> set vs"
        using hv by (by100 simp)
      show "{v} \<in> L"
      proof (rule disjE[OF hcase])
        assume "v = w"
        thus ?thesis
          using hwL by (by100 simp)
      next
        assume hv_vs: "v \<in> set vs"
        have "{v} \<in> ?R"
          using hsingleR hv_vs by (by100 simp)
        thus ?thesis
          by (by100 simp)
      qed
    qed
  qed
  have hsteps_cons: "\<forall>i < length (w # vs) - 1.
      closed_segment ((w # vs) ! i) ((w # vs) ! Suc i) \<in> L
      \<and> geotop_is_edge (closed_segment ((w # vs) ! i) ((w # vs) ! Suc i))"
  proof (intro allI impI)
    fix i
    assume hi: "i < length (w # vs) - 1"
    show "closed_segment ((w # vs) ! i) ((w # vs) ! Suc i) \<in> L
      \<and> geotop_is_edge (closed_segment ((w # vs) ! i) ((w # vs) ! Suc i))"
    proof (cases i)
      case 0
      have "closed_segment ((w # vs) ! i) ((w # vs) ! Suc i) = e"
        using 0 hfirstR he_seg by (by100 simp)
      thus ?thesis
        using heL he_edge by (by100 simp)
    next
      case (Suc j)
      have hj_lt: "j < length vs - 1"
        using Suc hi by (by100 simp)
      have hstep_j: "closed_segment (vs ! j) (vs ! Suc j) \<in> ?R
        \<and> geotop_is_edge (closed_segment (vs ! j) (vs ! Suc j))"
        using hstepsR hj_lt by (by100 blast)
      have hi_pos: "((w # vs) ! i) = vs ! j"
        using Suc by (by100 simp)
      have hi_next: "((w # vs) ! Suc i) = vs ! Suc j"
        using Suc by (by100 simp)
      thus ?thesis
        using hstep_j hi_pos by (by100 simp)
    qed
  qed
  have hedge_image_cons:
      "((\<lambda>i. closed_segment ((w # vs) ! i) ((w # vs) ! Suc i))
          ` {0..<length (w # vs) - 1})
      = insert e ((\<lambda>i. closed_segment (vs ! i) (vs ! Suc i))
          ` {0..<length vs - 1})"
  proof -
    have himage:
        "((\<lambda>i. closed_segment ((w # vs) ! i) ((w # vs) ! Suc i))
            ` {0..<length (w # vs) - 1})
        = insert (closed_segment w (vs ! 0))
            ((\<lambda>i. closed_segment (vs ! i) (vs ! Suc i))
              ` {0..<length vs - 1})"
      by (rule geotop_chain_edge_image_cons_dev34[OF hlenR])
    have "closed_segment w (vs ! 0) = e"
      using hfirstR he_seg by (by100 simp)
    thus ?thesis
      using himage by (by100 simp)
  qed
  have hedge_set_cons: "{d \<in> L. geotop_is_edge d}
      = ((\<lambda>i. closed_segment ((w # vs) ! i) ((w # vs) ! Suc i))
          ` {0..<length (w # vs) - 1})"
  proof -
    have hdelete: "{d \<in> L. geotop_is_edge d}
        = insert e {d \<in> ?R. geotop_is_edge d}"
      by (rule geotop_delete_leaf_edge_set_eq_insert_deleted_edge_dev34
          [OF heL he_edge])
    show ?thesis
      using hdelete hedgeR hedge_image_cons by (by100 simp)
  qed
  show ?thesis
    unfolding geotop_linear_graph_endpoint_chain_listing_dev34_def
    using hlenR hfirstR hdistinct_cons hvertices_cons hvertex_singletons
      hsteps_cons hedge_set_cons
    by (by100 simp)
qed

lemma geotop_finite_connected_degree_one_or_two_endpoint_chain_listing_from_first_neighbor_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree12: "\<forall>x. {x} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> x \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> x \<in> e} = 2"
  assumes hendpoint: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes he_edge: "geotop_is_edge e"
  assumes hw_e: "w \<in> e"
  assumes hq_ne: "q \<noteq> w"
  assumes he_seg: "e = closed_segment w q"
  assumes hqL: "{q} \<in> L"
  shows "\<exists>vs. geotop_linear_graph_endpoint_chain_listing_dev34 L w q vs"
  using hL_finite hL_linear hconn hdegree12 hendpoint heL he_edge hw_e
    hq_ne he_seg hqL
proof (induction L arbitrary: w e q rule: finite_psubset_induct)
  case (psubset L)
  show ?case
  proof -
    have hfinL: "finite L"
      by (rule psubset.hyps)
    have hL: "geotop_is_linear_graph L"
      by (rule psubset.prems(1))
    have hconnL: "geotop_complex_connected L"
      by (rule psubset.prems(2))
    have hdegreeL: "\<forall>x. {x} \<in> L \<longrightarrow>
        card {d\<in>L. geotop_is_edge d \<and> x \<in> d} = 1 \<or>
        card {d\<in>L. geotop_is_edge d \<and> x \<in> d} = 2"
      by (rule psubset.prems(3))
    have hend: "geotop_graph_endpoint L w"
      by (rule psubset.prems(4))
    have heL': "e \<in> L"
      by (rule psubset.prems(5))
    have hedge: "geotop_is_edge e"
      by (rule psubset.prems(6))
    have hwe: "w \<in> e"
      by (rule psubset.prems(7))
    have hqw: "q \<noteq> w"
      by (rule psubset.prems(8))
    have heq: "e = closed_segment w q"
      by (rule psubset.prems(9))
    have hqL': "{q} \<in> L"
      by (rule psubset.prems(10))
    have hqcard_cases:
        "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 1 \<or>
         card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 2"
      using hdegreeL hqL' by (by100 blast)
    show ?thesis
    proof (rule disjE[OF hqcard_cases])
      assume hqcard1: "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 1"
      show ?thesis
      proof
        show "geotop_linear_graph_endpoint_chain_listing_dev34 L w q [w, q]"
          by (rule geotop_endpoint_chain_listing_two_vertex_dev34
              [OF hL hfinL hconnL hend heL' hedge hwe hqw heq hqL' hqcard1])
      qed
    next
      assume hqcard2: "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 2"
      let ?R = "L - {{w}, e}"
      have hqe: "q \<in> e"
        using heq by (by100 simp)
      have hqR: "{q} \<in> ?R"
      proof -
        have hq_ne_w_singleton: "{q} \<noteq> {w}"
          using hqw by (by100 blast)
        have hq_ne_e: "{q} \<noteq> e"
        proof
          assume hqe_single: "{q} = e"
          have "w \<in> {q}"
            using hwe hqe_single by (by100 simp)
          hence "w = q"
            by (by100 simp)
          thus False
            using hqw by (by100 blast)
        qed
        show ?thesis
          using hqL' hq_ne_w_singleton hq_ne_e by (by100 simp)
      qed
      have hR_psubset: "?R \<subset> L"
        using heL' by (by100 blast)
      have hR_linear: "geotop_is_linear_graph ?R"
        by (rule geotop_graph_endpoint_delete_leaf_linear_graph_dev34
            [OF hL hfinL hend heL' hedge hwe])
      have hR_conn: "geotop_complex_connected ?R"
        by (rule geotop_graph_endpoint_delete_leaf_connected_dev34
            [OF hL hfinL hconnL hend heL' hedge hwe hqL' hqw heq])
      have hR_degree12: "\<forall>x. {x} \<in> ?R \<longrightarrow>
          card {l\<in>?R. geotop_is_edge l \<and> x \<in> l} = 1 \<or>
          card {l\<in>?R. geotop_is_edge l \<and> x \<in> l} = 2"
        by (rule geotop_graph_endpoint_delete_leaf_degree_one_or_two_dev34
            [OF hL hfinL hend heL' hedge hwe hqL' hqw heq hdegreeL hqcard2])
      have hR_endpoint: "geotop_graph_endpoint ?R q"
        by (rule geotop_graph_endpoint_delete_leaf_neighbor_endpoint_dev34
            [OF hL hfinL hend heL' hedge hwe hqL' hqw hqe hqcard2])
      have hfinR: "finite ?R"
        using hfinL by (by100 simp)
      have hneighborR: "\<exists>e' r. e' \<in> ?R \<and> geotop_is_edge e' \<and> q \<in> e'
          \<and> r \<noteq> q \<and> e' = closed_segment q r \<and> {r} \<in> ?R"
        by (rule geotop_graph_endpoint_unique_segment_neighbor_dev34
            [OF hR_linear hfinR hR_endpoint])
      obtain e' r where hneighborR_pack:
          "e' \<in> ?R \<and> geotop_is_edge e' \<and> q \<in> e'
          \<and> r \<noteq> q \<and> e' = closed_segment q r \<and> {r} \<in> ?R"
        using hneighborR
        by (elim exE)
      have heR: "e' \<in> ?R"
        using hneighborR_pack by (by100 simp)
      have he'_edge: "geotop_is_edge e'"
        using hneighborR_pack by (by100 simp)
      have hq_e': "q \<in> e'"
        using hneighborR_pack by (by100 simp)
      have hr_ne: "r \<noteq> q"
        using hneighborR_pack by (by100 simp)
      have he'_seg: "e' = closed_segment q r"
        using hneighborR_pack by (by100 simp)
      have hrR: "{r} \<in> ?R"
        using hneighborR_pack by (by100 simp)
      obtain vs where hlistR:
        "geotop_linear_graph_endpoint_chain_listing_dev34 ?R q r vs"
      proof -
        have hex: "\<exists>vs. geotop_linear_graph_endpoint_chain_listing_dev34 ?R q r vs"
        proof (rule psubset.IH[where B = ?R and w = q and e = e' and q = r])
          show "?R \<subset> L" by (rule hR_psubset)
          show "geotop_is_linear_graph ?R" by (rule hR_linear)
          show "geotop_complex_connected ?R" by (rule hR_conn)
          show "\<forall>x. {x} \<in> ?R \<longrightarrow>
              card {d \<in> ?R. geotop_is_edge d \<and> x \<in> d} = 1 \<or>
              card {d \<in> ?R. geotop_is_edge d \<and> x \<in> d} = 2"
            by (rule hR_degree12)
          show "geotop_graph_endpoint ?R q" by (rule hR_endpoint)
          show "e' \<in> ?R" by (rule heR)
          show "geotop_is_edge e'" by (rule he'_edge)
          show "q \<in> e'" by (rule hq_e')
          show "r \<noteq> q" by (rule hr_ne)
          show "e' = closed_segment q r" by (rule he'_seg)
          show "{r} \<in> ?R" by (rule hrR)
        qed
        then obtain vs where
          "geotop_linear_graph_endpoint_chain_listing_dev34 ?R q r vs"
          by (by100 blast)
        thus ?thesis
          by (rule that)
      qed
      have hlistL: "geotop_linear_graph_endpoint_chain_listing_dev34 L w q (w # vs)"
        by (rule geotop_endpoint_chain_listing_cons_delete_leaf_dev34
            [OF hL hfinL hend heL' hedge hwe hqw heq hlistR])
      show ?thesis
        using hlistL by (by100 blast)
    qed
  qed
qed

lemma geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34:
  fixes L :: "(real^2) set set"
  fixes \<gamma> :: "real \<Rightarrow> real^2"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hbroken: "geotop_is_broken_line (geotop_polyhedron L)"
  assumes hconn: "geotop_complex_connected L"
  assumes hvertices_finite: "finite (geotop_complex_vertices L)"
  assumes hendpoint: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes he_edge: "geotop_is_edge e"
  assumes hw_e: "w \<in> e"
  assumes hq_ne: "q \<noteq> w"
  assumes he_seg: "e = closed_segment w q"
  assumes hqL: "{q} \<in> L"
  assumes h\<gamma>_arc: "arc \<gamma>"
  assumes h\<gamma>_img: "path_image \<gamma> = geotop_polyhedron L"
  assumes h\<gamma>_start: "pathstart \<gamma> = w"
  assumes hfirst_edge_path_image: "closed_segment w q \<subseteq> path_image \<gamma>"
  assumes h\<gamma>_endpoints:
    "geotop_arc_endpoints (geotop_polyhedron L) {w, pathfinish \<gamma>}"
  assumes hfinishL: "{pathfinish \<gamma>} \<in> L"
  assumes hfinish_endpoint: "geotop_graph_endpoint L (pathfinish \<gamma>)"
  assumes hfirst_edge_exhausts_if_finish:
    "q = pathfinish \<gamma> \<Longrightarrow> geotop_polyhedron L = e"
  assumes hq_not_endpoint_if_not_finish:
    "q \<noteq> pathfinish \<gamma> \<Longrightarrow> \<not> geotop_graph_endpoint L q"
  shows "\<exists>(T :: (real^2) set set) (\<sigma> :: (real^2) set) L' B c \<psi>.
      T = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' T
      \<and> bij_betw \<psi> (geotop_complex_vertices L) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Book construction isolated from the endpoint hygiene above: the oriented
    finite broken-line chain starting at \<open>w\<close> and entering the first edge
    \<open>closed_segment w q\<close> is placed on a subdivided boundary arc of a
    2-simplex, and the adjacent boundary vertex is used as the fan vertex. **)
proof -
  have hchain_listing_base_if_finish:
      "q = pathfinish \<gamma> \<Longrightarrow>
        geotop_linear_graph_endpoint_chain_listing_dev34 L w q [w, q]"
  proof -
    assume hq_finish: "q = pathfinish \<gamma>"
    have hq_endpoint: "geotop_graph_endpoint L q"
      using hfinish_endpoint hq_finish by (by100 simp)
    have hq_card: "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 1"
      using geotop_graph_endpoint_singleton_and_card_one_dev34
          [OF hL_linear hq_endpoint]
      by (by100 blast)
    show ?thesis
      by (rule geotop_endpoint_chain_listing_two_vertex_dev34
          [OF hL_linear hL_finite hconn hendpoint heL he_edge hw_e hq_ne
            he_seg hqL hq_card])
  qed
  have hchain_listing_if_degree_one_or_two:
      "(\<forall>x. {x} \<in> L \<longrightarrow>
          card {l\<in>L. geotop_is_edge l \<and> x \<in> l} = 1 \<or>
          card {l\<in>L. geotop_is_edge l \<and> x \<in> l} = 2)
      \<Longrightarrow> \<exists>vs. geotop_linear_graph_endpoint_chain_listing_dev34 L w q vs"
  proof -
    assume hdegree12: "\<forall>x. {x} \<in> L \<longrightarrow>
        card {l\<in>L. geotop_is_edge l \<and> x \<in> l} = 1 \<or>
        card {l\<in>L. geotop_is_edge l \<and> x \<in> l} = 2"
    show ?thesis
      by (rule geotop_finite_connected_degree_one_or_two_endpoint_chain_listing_from_first_neighbor_dev34
          [OF hL_linear hL_finite hconn hdegree12 hendpoint heL he_edge
            hw_e hq_ne he_seg hqL])
  qed
  have hchain_boundary_arc_fan_target:
      "\<exists>vs (T :: (real^2) set set) (\<sigma> :: (real^2) set) L' B c \<psi>.
        geotop_linear_graph_endpoint_chain_listing_dev34 L w q vs
        \<and> T = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
        \<and> geotop_simplex_dim \<sigma> 2
        \<and> geotop_is_subdivision L' T
        \<and> bij_betw \<psi> (geotop_complex_vertices L) B
        \<and> c \<notin> B
        \<and> geotop_complex_vertices L' = insert c B
        \<and> geotop_convex_hull {c} \<in> L'
        \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
          (geotop_convex_hull W \<in> L
            \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
        \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
          W \<subseteq> geotop_complex_vertices L \<longrightarrow>
          (geotop_convex_hull W \<in> L
            \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
    (**
      Remaining boundary-arc realization package from Moise Fig. 4.10:
      use the broken-line arc order, with the first edge oriented from \<open>w\<close>
      to \<open>q\<close>, to obtain an endpoint chain listing; realize the listed chain
      as the base arc of a fan subdividing a 2-simplex, with \<open>c\<close> the adjacent
      boundary vertex.  This is the path analogue of the cyclic boundary
      subdivision model, not an isomorphism with the whole boundary cycle. **)
    sorry
  show ?thesis
  proof -
    from hchain_boundary_arc_fan_target show ?thesis
    proof (elim exE conjE)
      fix vs :: "(real^2) list"
        and T :: "(real^2) set set"
        and \<sigma> :: "(real^2) set"
        and L' :: "(real^2) set set"
        and B :: "(real^2) set"
        and c :: "real^2"
        and \<psi> :: "real^2 \<Rightarrow> real^2"
      assume hlist: "geotop_linear_graph_endpoint_chain_listing_dev34 L w q vs"
      assume hT: "T = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
      assume h\<sigma>: "geotop_simplex_dim \<sigma> 2"
      assume hsub: "geotop_is_subdivision L' T"
      assume hbij: "bij_betw \<psi> (geotop_complex_vertices L) B"
      assume hcB: "c \<notin> B"
      assume hvertices: "geotop_complex_vertices L' = insert c B"
      assume hc_simplex: "geotop_convex_hull {c} \<in> L'"
      assume hboundary_target:
        "\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
          (geotop_convex_hull W \<in> L
            \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
      assume hcone_target:
        "\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
          W \<subseteq> geotop_complex_vertices L \<longrightarrow>
          (geotop_convex_hull W \<in> L
            \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L')"
    show ?thesis
      apply (rule exI[where x=T])
      apply (rule exI[where x=\<sigma>])
      apply (rule exI[where x=L'])
      apply (rule exI[where x=B])
      apply (rule exI[where x=c])
      apply (rule exI[where x=\<psi>])
      using hT h\<sigma> hsub hbij hcB hvertices hc_simplex
        hboundary_target hcone_target
      by (intro conjI)
    qed
  qed
qed

lemma geotop_endpoint_first_neighbor_chain_boundary_arc_fan_target_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hbroken: "geotop_is_broken_line (geotop_polyhedron L)"
  assumes hconn: "geotop_complex_connected L"
  assumes hvertices_finite: "finite (geotop_complex_vertices L)"
  assumes hendpoint: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes he_edge: "geotop_is_edge e"
  assumes hw_e: "w \<in> e"
  assumes hq_ne: "q \<noteq> w"
  assumes he_seg: "e = closed_segment w q"
  assumes hqL: "{q} \<in> L"
  shows "\<exists>(T :: (real^2) set set) (\<sigma> :: (real^2) set) L' B c \<psi>.
      T = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' T
      \<and> bij_betw \<psi> (geotop_complex_vertices L) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Moise Fig. 4.10 endpoint-chain package after choosing the first edge:
    enumerate the finite connected broken-line graph from endpoint \<open>w\<close> through
    its first neighbor \<open>q\<close>, realize the ordered chain as a subdivision of one
    boundary arc of a standard 2-simplex, choose the adjacent boundary vertex
    \<open>c\<close>, and cone the arc subdivision from \<open>c\<close>. **)
proof -
  have hB_arc: "geotop_is_arc (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    using hbroken unfolding geotop_is_broken_line_def by (by100 blast)
  obtain E where hE: "geotop_arc_endpoints (geotop_polyhedron L) E"
    using geotop_is_arc_has_arc_endpoints_dev34[OF hB_arc] by (by100 blast)
  have hpoly_refl: "geotop_polyhedron L = geotop_polyhedron L"
    by (rule HOL.refl)
  have hwE: "w \<in> E"
    by (rule geotop_broken_line_graph_endpoint_in_arc_endpoints_prefix
        [OF hL_linear hL_finite hpoly_refl hbroken hE hendpoint])
  obtain \<gamma> :: "real \<Rightarrow> real^2"
    where h\<gamma>_arc: "arc \<gamma>"
      and h\<gamma>_img: "path_image \<gamma> = geotop_polyhedron L"
      and hE_eq: "E = {pathstart \<gamma>, pathfinish \<gamma>}"
    using arc_endpoints_imp_arc_HOL[OF hE] by (by100 blast)
  define \<gamma>w where "\<gamma>w = (if pathstart \<gamma> = w then \<gamma> else reversepath \<gamma>)"
  have h\<gamma>w_arc: "arc \<gamma>w"
  proof (cases "pathstart \<gamma> = w")
    case True
    show ?thesis
      unfolding \<gamma>w_def using True h\<gamma>_arc by (by100 simp)
  next
    case False
    have "arc (reversepath \<gamma>)"
      by (rule arc_reversepath[OF h\<gamma>_arc])
    thus ?thesis
      unfolding \<gamma>w_def using False by (by100 simp)
  qed
  have h\<gamma>w_img: "path_image \<gamma>w = geotop_polyhedron L"
    unfolding \<gamma>w_def using h\<gamma>_img path_image_reversepath by (by100 simp)
  have h\<gamma>w_start: "pathstart \<gamma>w = w"
  proof (cases "pathstart \<gamma> = w")
    case True
    show ?thesis
      unfolding \<gamma>w_def using True by (by100 simp)
  next
    case False
    have "w = pathfinish \<gamma>"
      using hwE hE_eq False by (by100 blast)
    thus ?thesis
      unfolding \<gamma>w_def using False by (simp add: pathstart_reversepath)
  qed
  have hq_e: "q \<in> e"
  proof -
    have "q \<in> closed_segment w q"
      by (by100 simp)
    thus ?thesis
      using he_seg by (by100 simp)
  qed
  have he_subset_poly: "e \<subseteq> geotop_polyhedron L"
    using heL unfolding geotop_polyhedron_def by (by100 blast)
  have hq_poly: "q \<in> geotop_polyhedron L"
    using hq_e he_subset_poly by (by100 blast)
  have hq_path_image: "q \<in> path_image \<gamma>w"
    using hq_poly h\<gamma>w_img by (by100 simp)
  have hfirst_edge_path_image: "closed_segment w q \<subseteq> path_image \<gamma>w"
    using he_seg he_subset_poly h\<gamma>w_img by (by100 simp)
  have h\<gamma>w_finish_ne_w: "pathfinish \<gamma>w \<noteq> w"
  proof -
    have "pathfinish \<gamma>w \<noteq> pathstart \<gamma>w"
      by (rule arc_distinct_ends[OF h\<gamma>w_arc])
    thus ?thesis
      using h\<gamma>w_start by (by100 simp)
  qed
  have h\<gamma>w_finish_path_image: "pathfinish \<gamma>w \<in> path_image \<gamma>w"
    unfolding path_image_def pathfinish_def by (by100 simp)
  have h\<gamma>w_endpoints:
      "geotop_arc_endpoints (geotop_polyhedron L) {w, pathfinish \<gamma>w}"
  proof -
    have "geotop_arc_endpoints (path_image \<gamma>w)
        {pathstart \<gamma>w, pathfinish \<gamma>w}"
      by (rule geotop_HOL_arc_imp_geotop_arc_endpoints_prefix[OF h\<gamma>w_arc])
    thus ?thesis
      using h\<gamma>w_start h\<gamma>w_img by (by100 simp)
  qed
  have h\<gamma>w_finish_poly: "pathfinish \<gamma>w \<in> geotop_polyhedron L"
    using h\<gamma>w_finish_path_image h\<gamma>w_img by (by100 simp)
  have h\<gamma>w_finish_endpoint_mem: "pathfinish \<gamma>w \<in> {w, pathfinish \<gamma>w}"
    by (by100 simp)
  have h\<gamma>w_finishL: "{pathfinish \<gamma>w} \<in> L"
    by (rule geotop_broken_line_endpoint_in_finite_linear_graph_vertex_dev34
        [OF hL_linear hL_finite hpoly_refl hbroken h\<gamma>w_endpoints
          h\<gamma>w_finish_endpoint_mem])
  have h\<gamma>w_finish_card_one:
      "card {e\<in>L. geotop_is_edge e \<and> pathfinish \<gamma>w \<in> e} = 1"
    by (rule geotop_broken_line_endpoint_vertex_incident_edge_card_one_dev34
        [OF hL_linear hL_finite hpoly_refl hbroken h\<gamma>w_endpoints
          h\<gamma>w_finish_endpoint_mem h\<gamma>w_finishL])
  have h\<gamma>w_finish_endpoint: "geotop_graph_endpoint L (pathfinish \<gamma>w)"
    by (rule geotop_degree_one_vertex_graph_endpoint_dev34
        [OF hL_linear h\<gamma>w_finishL h\<gamma>w_finish_card_one])
  have hfirst_edge_exhausts_if_finish:
      "q = pathfinish \<gamma>w \<Longrightarrow> geotop_polyhedron L = e"
  proof -
    assume hq_finish: "q = pathfinish \<gamma>w"
    have hq_card_one: "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 1"
      using h\<gamma>w_finish_card_one hq_finish by (by100 simp)
    show ?thesis
      by (rule geotop_two_degree_one_endpoint_edge_connected_polyhedron_eq_dev34
          [OF hL_linear hL_finite hconn hendpoint hqL hq_card_one
            heL he_edge hw_e hq_ne he_seg])
  qed
  have hq_arc_interior_if_not_finish:
      "q \<noteq> pathfinish \<gamma>w \<Longrightarrow>
        q \<in> geotop_arc_interior (geotop_polyhedron L) {w, pathfinish \<gamma>w}"
    using hq_poly hq_ne unfolding geotop_arc_interior_def by (by100 blast)
  have hL_complex_local: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL_linear])
  have hL_1dim_local: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_dev34[OF hL_linear])
  have hq_card_ge2_if_not_finish:
      "q \<noteq> pathfinish \<gamma>w \<Longrightarrow>
        card {l\<in>L. geotop_is_edge l \<and> q \<in> l} \<ge> 2"
  proof -
    assume hq_not_finish: "q \<noteq> pathfinish \<gamma>w"
    have hq_int: "q \<in> geotop_arc_interior
        (geotop_polyhedron L) {w, pathfinish \<gamma>w}"
      by (rule hq_arc_interior_if_not_finish[OF hq_not_finish])
    have hraw:
        "card {\<sigma> \<in> L. q \<in> \<sigma> \<and> geotop_simplex_dim \<sigma> 1} \<ge> 2"
      by (rule broken_line_internal_vertex_card_edges_ge2
          [OF hL_complex_local hpoly_refl hL_1dim_local hB_arc
            h\<gamma>w_endpoints hqL hq_int])
    have "{\<sigma> \<in> L. q \<in> \<sigma> \<and> geotop_simplex_dim \<sigma> 1}
        = {l\<in>L. geotop_is_edge l \<and> q \<in> l}"
      unfolding geotop_is_edge_def by (by100 blast)
    thus ?thesis
      using hraw by (by100 simp)
  qed
  have hq_not_endpoint_if_not_finish:
      "q \<noteq> pathfinish \<gamma>w \<Longrightarrow> \<not> geotop_graph_endpoint L q"
  proof
    assume hq_not_finish: "q \<noteq> pathfinish \<gamma>w"
    assume hq_endpoint: "geotop_graph_endpoint L q"
    have hq_card_one:
        "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 1"
      using geotop_graph_endpoint_singleton_and_card_one_dev34
          [OF hL_linear hq_endpoint]
      by (by100 blast)
    have hq_card_ge2:
        "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} \<ge> 2"
      by (rule hq_card_ge2_if_not_finish[OF hq_not_finish])
    show False
      using hq_card_one hq_card_ge2 by (by100 simp)
  qed
  show ?thesis
    by (rule geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
        [OF hL_linear hL_finite hbroken hconn hvertices_finite hendpoint
          heL he_edge hw_e hq_ne he_seg hqL h\<gamma>w_arc h\<gamma>w_img
          h\<gamma>w_start hfirst_edge_path_image h\<gamma>w_endpoints h\<gamma>w_finishL
          h\<gamma>w_finish_endpoint hfirst_edge_exhausts_if_finish
          hq_not_endpoint_if_not_finish])
qed

lemma geotop_endpoint_degree_one_chain_boundary_arc_fan_target_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hbroken: "geotop_is_broken_line (geotop_polyhedron L)"
  assumes hconn: "geotop_complex_connected L"
  assumes hvertices_finite: "finite (geotop_complex_vertices L)"
  assumes hwL: "{w} \<in> L"
  assumes hcard_one: "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1"
  shows "\<exists>(T :: (real^2) set set) (\<sigma> :: (real^2) set) L' B c \<psi>.
      T = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' T
      \<and> bij_betw \<psi> (geotop_complex_vertices L) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Core boundary-arc fan target.  With the finite vertex set and the chosen
    degree-one endpoint made explicit, the broken-line carrier gives the
    ordered edge-chain from \<open>w\<close>.  Realize it as a subdivided boundary arc of
    a standard 2-simplex before coning from the adjacent boundary vertex. **)
proof -
  have hendpoint: "geotop_graph_endpoint L w"
    by (rule geotop_degree_one_vertex_graph_endpoint_dev34[OF hL_linear hwL hcard_one])
  obtain e q where heL: "e \<in> L"
      and he_edge: "geotop_is_edge e"
      and hw_e: "w \<in> e"
      and hq_ne: "q \<noteq> w"
      and he_seg: "e = closed_segment w q"
      and hqL: "{q} \<in> L"
    using geotop_graph_endpoint_unique_segment_neighbor_dev34[OF hL_linear hL_finite hendpoint]
    by (by100 blast)
  show ?thesis
    by (rule geotop_endpoint_first_neighbor_chain_boundary_arc_fan_target_dev34
        [OF hL_linear hL_finite hbroken hconn hvertices_finite hendpoint
          heL he_edge hw_e hq_ne he_seg hqL])
qed

lemma geotop_endpoint_finite_linear_graph_boundary_vertex_fan_target_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hbroken: "geotop_is_broken_line (geotop_polyhedron L)"
  assumes hconn: "geotop_complex_connected L"
  assumes hwL: "{w} \<in> L"
  assumes hend: "geotop_graph_endpoint L w"
  shows "\<exists>(T :: (real^2) set set) (\<sigma> :: (real^2) set) L' B c \<psi>.
      T = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' T
      \<and> bij_betw \<psi> (geotop_complex_vertices L) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Endpoint-specific Moise Fig. 4.10 boundary-vertex graph step.  Enumerate
    the finite connected linear graph as an edge-chain starting at \<open>w\<close>,
    place that ordered chain on a subdivided boundary arc of a 2-simplex, and
    cone the arc from the adjacent boundary vertex. **)
proof -
  have hvertices_finite: "finite (geotop_complex_vertices L)"
    by (rule geotop_finite_linear_graph_vertices_finite_dev34[OF hL_linear hL_finite])
  have hendpoint_data:
      "{w} \<in> L \<and> card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1"
  proof (rule geotop_graph_endpoint_singleton_and_card_one_dev34
      [where L = L and w = w])
    show "geotop_is_linear_graph L" by (rule hL_linear)
    show "geotop_graph_endpoint L w" by (rule hend)
  qed
  have hcard_one: "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1"
    using hendpoint_data by (by100 blast)
  show ?thesis
  proof (rule geotop_endpoint_degree_one_chain_boundary_arc_fan_target_dev34
      [where L = L and w = w])
    show "geotop_is_linear_graph L" by (rule hL_linear)
    show "finite L" by (rule hL_finite)
    show "geotop_is_broken_line (geotop_polyhedron L)" by (rule hbroken)
    show "geotop_complex_connected L" by (rule hconn)
    show "finite (geotop_complex_vertices L)" by (rule hvertices_finite)
    show "{w} \<in> L" by (rule hwL)
    show "card {e \<in> L. geotop_is_edge e \<and> w \<in> e} = 1" by (rule hcard_one)
  qed
qed

lemma geotop_connected_endpoint_finite_linear_graph_boundary_vertex_fan_target_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hbroken: "geotop_is_broken_line (geotop_polyhedron L)"
  assumes hconn: "geotop_complex_connected L"
  assumes hend: "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
  shows "\<exists>(T :: (real^2) set set) (\<sigma> :: (real^2) set) L' B c \<psi>.
      T = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' T
      \<and> bij_betw \<psi> (geotop_complex_vertices L) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Moise Fig. 4.10 boundary-vertex graph step.  Starting with the connected
    finite linear edge-chain and a graph endpoint, enumerate the chain from
    that endpoint, place it on a subdivided boundary arc of a 2-simplex, and
    take the corresponding boundary endpoint as the fan vertex. **)
proof -
  obtain w where hwL: "{w} \<in> L"
    and hw_endpoint: "geotop_graph_endpoint L w"
    using hend by (by100 blast)
  show ?thesis
  proof (rule geotop_endpoint_finite_linear_graph_boundary_vertex_fan_target_dev34
      [where L = L and w = w])
    show "geotop_is_linear_graph L" by (rule hL_linear)
    show "finite L" by (rule hL_finite)
    show "geotop_is_broken_line (geotop_polyhedron L)" by (rule hbroken)
    show "geotop_complex_connected L" by (rule hconn)
    show "{w} \<in> L" by (rule hwL)
    show "geotop_graph_endpoint L w" by (rule hw_endpoint)
  qed
qed

lemma geotop_standard_boundary_vertex_fan_target_from_finite_linear_graph_broken_line_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hbroken: "geotop_is_broken_line (geotop_polyhedron L)"
  shows "\<exists>(T :: (real^2) set set) (\<sigma> :: (real^2) set) L' B c \<psi>.
      T = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' T
      \<and> bij_betw \<psi> (geotop_complex_vertices L) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices L \<longrightarrow>
        (geotop_convex_hull W \<in> L
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Graph-only boundary-vertex version of Moise Fig. 4.10.  A finite linear
    graph whose carrier is a broken line is enumerated as an edge-chain and
    placed on a subdivided boundary arc of a 2-simplex; the matching boundary
    endpoint is then used as the fan vertex. **)
proof -
  have hchain0:
      "geotop_complex_connected L
      \<and> (\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w)"
    by (rule geotop_finite_linear_graph_broken_line_connected_endpoint_dev34
        [OF hL_linear hL_finite hbroken])
  (**
    Remaining boundary-vertex Fig. 4.10 graph step: recover the ordered
    edge-chain from the connected finite linear graph with a graph endpoint,
    realize that abstract chain as a subdivided boundary arc of a 2-simplex,
    and choose the matching boundary endpoint as the fan vertex. **)
  have hconn: "geotop_complex_connected L"
    using hchain0 by (by100 blast)
  have hend: "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
    using hchain0 by (by100 blast)
  show ?thesis
  proof (rule geotop_connected_endpoint_finite_linear_graph_boundary_vertex_fan_target_dev34
      [where L = L])
    show "geotop_is_linear_graph L" by (rule hL_linear)
    show "finite L" by (rule hL_finite)
    show "geotop_is_broken_line (geotop_polyhedron L)" by (rule hbroken)
    show "geotop_complex_connected L" by (rule hconn)
    show "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w" by (rule hend)
  qed
qed

lemma geotop_standard_boundary_vertex_fan_target_from_finite_linear_link_broken_line_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  assumes hlink_finite: "finite (geotop_link K v)"
  assumes hbroken: "geotop_is_broken_line (geotop_polyhedron (geotop_link K v))"
  shows "\<exists>(L :: (real^2) set set) (\<sigma> :: (real^2) set) L' B c \<psi>.
      L = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' L
      \<and> bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
  (**
    Boundary-vertex analogue of the Fig. 4.10 target construction.  Enumerate
    the finite broken-line link as an edge-chain, place it on a subdivided
    boundary arc of a 2-simplex, choose the cone vertex as the corresponding
    boundary endpoint, and cone that arc inside the target triangle. **)
proof -
  show ?thesis
    by (rule geotop_standard_boundary_vertex_fan_target_from_finite_linear_graph_broken_line_dev34
        [OF hlink_linear hlink_finite hbroken])
qed

lemma geotop_vertex_star_fan_model_from_finite_linear_link_broken_line_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  assumes hlink_finite: "finite (geotop_link K v)"
  assumes hbroken: "geotop_is_broken_line (geotop_polyhedron (geotop_link K v))"
  shows "\<exists>(L :: (real^2) set set) (\<sigma> :: (real^2) set) K' L'.
      L = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision K' (geotop_star K v)
      \<and> geotop_is_subdivision L' L
      \<and> geotop_isomorphic K' L'"
  (**
    Boundary-vertex analogue of Moise Fig. 4.10.  Enumerate the finite
    broken-line link as an ordered edge-chain, place that chain as a subdivided
    boundary arc of a 2-simplex, and cone it from the corresponding boundary
    vertex of the target triangle.  The resulting fan is a subdivision of a
    2-simplex and is simplicially isomorphic to the vertex star. **)
proof -
  obtain L\<^sub>T :: "(real^2) set set" and \<sigma> :: "(real^2) set" and L' B c \<psi>
    where htarget:
      "L\<^sub>T = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' L\<^sub>T
      \<and> bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
    using geotop_standard_boundary_vertex_fan_target_from_finite_linear_link_broken_line_dev34
      [OF hK hv hlink_linear hlink_finite hbroken]
    by (elim exE) assumption
  have hL_def: "L\<^sub>T = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    using htarget by (by100 simp)
  have hdim: "geotop_simplex_dim \<sigma> 2"
    using htarget by (by100 simp)
  have hsubdiv: "geotop_is_subdivision L' L\<^sub>T"
    using htarget by (by100 simp)
  have h\<psi>: "bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B"
    using htarget by (by100 simp)
  have hcB: "c \<notin> B"
    using htarget by (by100 simp)
  have hL_vertices: "geotop_complex_vertices L' = insert c B"
    using htarget by (by100 simp)
  have hcone_vertex_target: "geotop_convex_hull {c} \<in> L'"
    using htarget by (by100 simp)
  have hlink_target:
      "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
    using htarget by (by100 simp)
  have hcone_target:
      "\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L')"
    using htarget by (by100 simp)
  have hstar_vertices_finite:
      "finite (geotop_complex_vertices (geotop_star K v))"
    using geotop_fig410_link_and_star_vertices_finite_dev34
      [OF hK hv hlink_finite]
    by (by100 blast)
  define \<phi> where "\<phi> x = (if x = v then c else \<psi> x)" for x
  have hiso_raw:
      "geotop_isomorphism (geotop_star K v) L'
        (\<lambda>x. if x = v then c else \<psi> x)"
    by (rule_tac geotop_star_fan_isomorphism_from_link_and_cone_target_cases_dev34
        [OF hK hv h\<psi> hcB hL_vertices hstar_vertices_finite
          hlink_target hcone_vertex_target hcone_target])
  have h\<phi>_eq: "\<phi> = (\<lambda>x. if x = v then c else \<psi> x)"
    using \<phi>_def by (by100 blast)
  have hiso: "geotop_isomorphism (geotop_star K v) L' \<phi>"
    using hiso_raw h\<phi>_eq by (by100 simp)
  have hisomorphic: "geotop_isomorphic (geotop_star K v) L'"
    unfolding geotop_isomorphic_def using hiso by (by100 blast)
  have hstar_complex: "geotop_is_complex (geotop_star K v)"
    by (rule geotop_star_is_complex[OF hK])
  have hstar_sub: "geotop_is_subdivision (geotop_star K v) (geotop_star K v)"
    by (rule geotop_is_subdivision_refl[OF hstar_complex])
  show ?thesis
    apply (rule_tac x=L\<^sub>T in exI)
    apply (rule_tac x=\<sigma> in exI)
    apply (rule_tac x="geotop_star K v" in exI)
    apply (rule_tac x=L' in exI)
    using hL_def hdim hstar_sub hsubdiv hisomorphic
    by (by100 blast)
qed

lemma geotop_vertex_star_fan_model_from_finite_linear_link_line_or_polygon_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  assumes hlink_finite: "finite (geotop_link K v)"
  assumes hshape:
    "geotop_is_broken_line (geotop_polyhedron (geotop_link K v))
      \<or> geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
  shows "\<exists>(L :: (real^2) set set) (\<sigma> :: (real^2) set) K' L'.
      L = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision K' (geotop_star K v)
      \<and> geotop_is_subdivision L' L
      \<and> geotop_isomorphic K' L'"
  (**
    Case split matching the book: polygonal links use the full-boundary
    Figure 4.10 fan; broken-line links use the boundary-vertex fan obtained by
    coning a subdivided boundary arc of a 2-simplex. **)
proof (cases "geotop_is_broken_line (geotop_polyhedron (geotop_link K v))")
  case True
  show ?thesis
    by (rule geotop_vertex_star_fan_model_from_finite_linear_link_broken_line_dev34
        [OF hK hv hlink_linear hlink_finite True])
next
  case False
  have hpolygon: "geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
    using hshape False by (by100 blast)
  obtain \<sigma> :: "(real^2) set" and L'
    where hfan:
      "geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_isomorphic (geotop_star K v) L'"
    using geotop_vertex_star_standard_fan_model_from_finite_linear_link_polygon_dev34
      [OF hK hv hlink_linear hlink_finite hpolygon]
    by (by100 blast)
  have hstar_complex: "geotop_is_complex (geotop_star K v)"
    by (rule geotop_star_is_complex[OF hK])
  have hstar_sub: "geotop_is_subdivision (geotop_star K v) (geotop_star K v)"
    by (rule geotop_is_subdivision_refl[OF hstar_complex])
  show ?thesis
    using hfan hstar_sub by (intro exI[of _ "{\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"]) (by100 blast)
qed

lemma geotop_vertex_star_fan_model_from_link_complex_line_or_polygon_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink:
    "geotop_is_complex (geotop_link K v)
      \<and> geotop_complex_is_1dim (geotop_link K v)
      \<and> finite (geotop_link K v)
      \<and> (geotop_is_broken_line (geotop_polyhedron (geotop_link K v))
          \<or> geotop_is_polygon (geotop_polyhedron (geotop_link K v)))"
  shows "\<exists>(L :: (real^2) set set) (\<sigma> :: (real^2) set) K' L'.
      L = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision K' (geotop_star K v)
      \<and> geotop_is_subdivision L' L
      \<and> geotop_isomorphic K' L'"
proof -
  have hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  proof -
    have hlink_complex: "geotop_is_complex (geotop_link K v)"
      using hlink by (by100 blast)
    have hlink_1dim: "geotop_complex_is_1dim (geotop_link K v)"
      using hlink by (by100 blast)
    show ?thesis
      by (rule geotop_complex_1dim_imp_linear_graph_dev34[OF hlink_complex hlink_1dim])
  qed
  have hlink_finite: "finite (geotop_link K v)"
    using hlink by (by100 blast)
  have hshape:
    "geotop_is_broken_line (geotop_polyhedron (geotop_link K v))
      \<or> geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
    using hlink by (by100 blast)
  show ?thesis
    by (rule geotop_vertex_star_fan_model_from_finite_linear_link_line_or_polygon_dev34
        [OF hK hv hlink_linear hlink_finite hshape])
qed

lemma geotop_vertex_star_cone_equiv_from_link_complex_line_or_polygon_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink:
    "geotop_is_complex (geotop_link K v)
      \<and> geotop_complex_is_1dim (geotop_link K v)
      \<and> finite (geotop_link K v)
      \<and> (geotop_is_broken_line (geotop_polyhedron (geotop_link K v))
          \<or> geotop_is_polygon (geotop_polyhedron (geotop_link K v)))"
  shows "\<exists>(L :: (real^2) set set) (\<sigma> :: (real^2) set).
        L = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
        \<and> geotop_simplex_dim \<sigma> 2
        \<and> geotop_comb_equiv (geotop_star K v) L"
proof -
  have hmodel_ex:
    "\<exists>(L :: (real^2) set set) (\<sigma> :: (real^2) set) K' L'.
      L = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision K' (geotop_star K v)
      \<and> geotop_is_subdivision L' L
      \<and> geotop_isomorphic K' L'"
    by (rule geotop_vertex_star_fan_model_from_link_complex_line_or_polygon_dev34
        [OF hK hv hlink])
  obtain L :: "(real^2) set set" and \<sigma> :: "(real^2) set" and K' L'
    where hmodel:
      "L = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision K' (geotop_star K v)
      \<and> geotop_is_subdivision L' L
      \<and> geotop_isomorphic K' L'"
    using hmodel_ex by (elim exE)
  have hL_eq: "L = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    using hmodel by (by100 simp)
  have h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    using hmodel by (by100 simp)
  have hK'_sub: "geotop_is_subdivision K' (geotop_star K v)"
    using hmodel by (by100 simp)
  have hL'_sub: "geotop_is_subdivision L' L"
    using hmodel by (by100 simp)
  have h_iso: "geotop_isomorphic K' L'"
    using hmodel by (by100 simp)
  have hstar_finite: "finite (geotop_star K v)"
    by (rule geotop_star_finite_at_complex_vertex[OF hK hv])
  have hL_finite: "finite L"
  proof -
    have h\<sigma>simplex: "geotop_is_simplex \<sigma>"
      by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>2])
    have "finite {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
      by (rule geotop_simplex_face_complex_finite_R2[OF h\<sigma>simplex])
    thus ?thesis
      using hL_eq by (by100 simp)
  qed
  have hcomb: "geotop_comb_equiv (geotop_star K v) L"
    unfolding geotop_comb_equiv_def
    using hstar_finite hL_finite hK'_sub hL'_sub h_iso by (by100 blast)
  show ?thesis
    using hL_eq h\<sigma>2 hcomb by (by100 blast)
qed

lemma geotop_vertex_star_cone_equiv_from_link_line_or_polygon_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hshape:
    "geotop_is_broken_line (\<Union>(geotop_link K v))
      \<or> geotop_is_polygon (\<Union>(geotop_link K v))"
  shows "\<exists>(L :: (real^2) set set) (\<sigma> :: (real^2) set).
        L = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
        \<and> geotop_simplex_dim \<sigma> 2
        \<and> geotop_comb_equiv (geotop_star K v) L"
proof -
  have hlink:
    "geotop_is_complex (geotop_link K v)
      \<and> geotop_complex_is_1dim (geotop_link K v)
      \<and> finite (geotop_link K v)
      \<and> (geotop_is_broken_line (geotop_polyhedron (geotop_link K v))
          \<or> geotop_is_polygon (geotop_polyhedron (geotop_link K v)))"
    by (rule geotop_link_finite_1dim_line_or_polygon_dev34[OF hK hv hshape])
  show ?thesis
    by (rule geotop_vertex_star_cone_equiv_from_link_complex_line_or_polygon_dev34
        [OF hK hv hlink])
qed

lemma geotop_vertex_star_comb_2cell_from_link_line_or_polygon_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hshape:
    "geotop_is_broken_line (\<Union>(geotop_link K v))
      \<or> geotop_is_polygon (\<Union>(geotop_link K v))"
  shows "geotop_comb_n_cell (geotop_star K v) 2"
proof -
  have hstar_complex: "geotop_is_complex (geotop_star K v)"
    by (rule geotop_star_is_complex[OF hK])
  have hstar_finite: "finite (geotop_star K v)"
    by (rule geotop_star_finite_at_complex_vertex[OF hK hv])
  have hcone_equiv:
    "\<exists>(L :: (real^2) set set) (\<sigma> :: (real^2) set).
        L = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
        \<and> geotop_simplex_dim \<sigma> 2
        \<and> geotop_comb_equiv (geotop_star K v) L"
    by (rule geotop_vertex_star_cone_equiv_from_link_line_or_polygon_dev34
        [OF hK hv hshape])
  show ?thesis
    unfolding geotop_comb_n_cell_def using hstar_complex hcone_equiv by (by100 blast)
qed

lemma geotop_openin_norm_polyhedron_contains_relative_ball_dev34:
  fixes M U :: "(real^2) set" and p :: "real^2"
  assumes hUopen: "openin_on M
      (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U"
  assumes hpU: "p \<in> U"
  shows "\<exists>r>0. M \<inter> ball p r \<subseteq> U"
proof -
  let ?TM = "top1_metric_topology_on M (\<lambda>x y. norm (x - y))"
  have hUmem: "U \<in> ?TM"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hTM_eq: "?TM = subspace_topology UNIV geotop_euclidean_topology M"
    by (rule top1_norm_metric_topology_on_eq_geotop_subspace_R2_dev34)
  have hUsubspace: "U \<in> subspace_topology UNIV geotop_euclidean_topology M"
    using hUmem hTM_eq by (by100 simp)
  obtain W where hWtop: "W \<in> geotop_euclidean_topology"
      and hUeq: "U = M \<inter> W"
    using hUsubspace unfolding subspace_topology_def by (by100 blast)
  have hpW: "p \<in> W"
    using hpU hUeq by (by100 blast)
  have hWopen: "open W"
    using hWtop unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  obtain r where hr_pos: "0 < r" and hball: "ball p r \<subseteq> W"
    using hWopen hpW openE by (by100 blast)
  show ?thesis
    using hr_pos hball hUeq by (intro exI[of _ r]) (by100 blast)
qed

lemma geotop_polyhedron_2_manifold_geo_chart_at_dev34:
  fixes K :: "(real^2) set set" and p :: "real^2"
  assumes hM: "geotop_n_manifold_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes hpM: "p \<in> geotop_polyhedron K"
  shows "\<exists>U f. openin_on (geotop_polyhedron K)
        (top1_metric_topology_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y))) U
      \<and> p \<in> U
      \<and> top1_homeomorphism_on U
        (subspace_topology UNIV geotop_euclidean_topology U)
        (UNIV::(real^2) set) geotop_euclidean_topology f"
proof -
  let ?M = "geotop_polyhedron K"
  let ?d = "\<lambda>x y. norm (x - y)"
  let ?TM = "top1_metric_topology_on ?M ?d"
  obtain U f where hUopen: "openin_on ?M ?TM U"
    and hpU: "p \<in> U"
    and hhomeo_metric: "top1_homeomorphism_on U (subspace_topology ?M ?TM U)
        (UNIV::(real^2) set) geotop_euclidean_topology f"
    using hM hpM unfolding geotop_n_manifold_on_def by (by100 blast)
  have hUsubM: "U \<subseteq> ?M"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hTM_eq: "?TM = subspace_topology UNIV geotop_euclidean_topology ?M"
    by (rule top1_norm_metric_topology_on_eq_geotop_subspace_R2_dev34)
  have hsource_eq: "subspace_topology ?M ?TM U =
      subspace_topology UNIV geotop_euclidean_topology U"
  proof -
    have htrans: "subspace_topology ?M
        (subspace_topology UNIV geotop_euclidean_topology ?M) U =
      subspace_topology UNIV geotop_euclidean_topology U"
      by (rule subspace_topology_trans[OF hUsubM])
    show ?thesis
      using hTM_eq htrans by (by100 simp)
  qed
  have hhomeo_geo: "top1_homeomorphism_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
    using hhomeo_metric hsource_eq by (by100 simp)
  show ?thesis
    using hUopen hpU hhomeo_geo by (by100 blast)
qed

lemma geotop_manifold_interior_geo_chart_at_dev34:
  fixes M :: "(real^2) set" and p :: "real^2"
  assumes hpint: "p \<in> geotop_manifold_interior M (\<lambda>x y. norm (x - y))"
  shows "\<exists>U f. openin_on M
        (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U
      \<and> p \<in> U
      \<and> top1_homeomorphism_on U
        (subspace_topology UNIV geotop_euclidean_topology U)
        (UNIV::(real^2) set) geotop_euclidean_topology f"
proof -
  let ?d = "\<lambda>x y. norm (x - y)"
  let ?TM = "top1_metric_topology_on M ?d"
  obtain U f where hUopen: "openin_on M ?TM U"
    and hpU: "p \<in> U"
    and hhomeo_metric: "top1_homeomorphism_on U
        (subspace_topology M ?TM U)
        (UNIV::(real^2) set) geotop_euclidean_topology f"
    using hpint unfolding geotop_manifold_interior_def by (by100 blast)
  have hUsubM: "U \<subseteq> M"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hTM_eq: "?TM = subspace_topology UNIV geotop_euclidean_topology M"
    by (rule top1_norm_metric_topology_on_eq_geotop_subspace_R2_dev34)
  have hsource_eq: "subspace_topology M ?TM U =
      subspace_topology UNIV geotop_euclidean_topology U"
  proof -
    have htrans: "subspace_topology M
        (subspace_topology UNIV geotop_euclidean_topology M) U =
      subspace_topology UNIV geotop_euclidean_topology U"
      by (rule subspace_topology_trans[OF hUsubM])
    show ?thesis
      using hTM_eq htrans by (by100 simp)
  qed
  have hhomeo_geo: "top1_homeomorphism_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
    using hhomeo_metric hsource_eq by (by100 simp)
  show ?thesis
    using hUopen hpU hhomeo_geo by (by100 blast)
qed

lemma top1_homeomorphism_on_subspace_image_dev34:
  assumes hhomeo: "top1_homeomorphism_on X TX Y TY f"
  assumes hA: "A \<subseteq> X"
  shows "top1_homeomorphism_on A (subspace_topology X TX A)
      (f ` A) (subspace_topology Y TY (f ` A)) f"
proof -
  have hTX: "is_topology_on X TX"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hTY: "is_topology_on Y TY"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hbij: "bij_betw f X Y"
    by (rule top1_homeomorphism_on_imp_bij[OF hhomeo])
  have hmapX: "f ` X = Y"
    using hbij unfolding bij_betw_def by (by100 blast)
  have hImg_subY: "f ` A \<subseteq> Y"
    using hA hmapX by (by100 blast)
  have hinjX: "inj_on f X"
    using hbij by (rule bij_betw_imp_inj_on)
  have hinjA: "inj_on f A"
    by (rule inj_on_subset[OF hinjX hA])
  have htopA: "is_topology_on A (subspace_topology X TX A)"
    by (rule subspace_topology_is_topology_on[OF hTX hA])
  have htopImg: "is_topology_on (f ` A) (subspace_topology Y TY (f ` A))"
    by (rule subspace_topology_is_topology_on[OF hTY hImg_subY])
  have hbijA: "bij_betw f A (f ` A)"
    unfolding bij_betw_def using hinjA by (by100 blast)
  have hcont_f: "top1_continuous_map_on X TX Y TY f"
    by (rule top1_homeomorphism_on_imp_cont1[OF hhomeo])
  have hcont_A: "top1_continuous_map_on A (subspace_topology X TX A)
      (f ` A) (subspace_topology Y TY (f ` A)) f"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>A. f x \<in> f ` A"
      by (by100 blast)
    show "\<forall>V\<in>subspace_topology Y TY (f ` A).
        {x \<in> A. f x \<in> V} \<in> subspace_topology X TX A"
    proof
      fix V
      assume hV: "V \<in> subspace_topology Y TY (f ` A)"
      obtain W where hW: "W \<in> TY" and hVeq: "V = f ` A \<inter> W"
        using hV unfolding subspace_topology_def by (by100 blast)
      have hpreX: "{x \<in> X. f x \<in> W} \<in> TX"
        using hcont_f hW unfolding top1_continuous_map_on_def by (by100 blast)
      have hpre_eq: "{x \<in> A. f x \<in> V} = A \<inter> {x \<in> X. f x \<in> W}"
        using hA hVeq by (by100 blast)
      show "{x \<in> A. f x \<in> V} \<in> subspace_topology X TX A"
        unfolding hpre_eq subspace_topology_def using hpreX by (by100 blast)
    qed
  qed
  have hcont_inv: "top1_continuous_map_on Y TY X TX (inv_into X f)"
    by (rule top1_homeomorphism_on_imp_cont2[OF hhomeo])
  have hcont_inv_A: "top1_continuous_map_on (f ` A)
      (subspace_topology Y TY (f ` A)) A (subspace_topology X TX A)
      (inv_into A f)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>y\<in>f ` A. inv_into A f y \<in> A"
      using hinjA by (by100 simp)
    show "\<forall>V\<in>subspace_topology X TX A.
        {y \<in> f ` A. inv_into A f y \<in> V} \<in>
        subspace_topology Y TY (f ` A)"
    proof
      fix V
      assume hV: "V \<in> subspace_topology X TX A"
      obtain W where hW: "W \<in> TX" and hVeq: "V = A \<inter> W"
        using hV unfolding subspace_topology_def by (by100 blast)
      have hpreY: "{y \<in> Y. inv_into X f y \<in> W} \<in> TY"
        using hcont_inv hW unfolding top1_continuous_map_on_def by (by100 blast)
      have hpre_eq:
        "{y \<in> f ` A. inv_into A f y \<in> V} =
         (f ` A) \<inter> {y \<in> Y. inv_into X f y \<in> W}"
      proof
        show "{y \<in> f ` A. inv_into A f y \<in> V} \<subseteq>
            (f ` A) \<inter> {y \<in> Y. inv_into X f y \<in> W}"
        proof
          fix y
          assume hy: "y \<in> {y \<in> f ` A. inv_into A f y \<in> V}"
          obtain a where haA: "a \<in> A" and hyfa: "y = f a"
            using hy by (by100 blast)
          have haX: "a \<in> X"
            using hA haA by (by100 blast)
          have hinvA: "inv_into A f y = a"
            using hinjA haA hyfa by (by100 simp)
          have hinvX: "inv_into X f y = a"
            using hinjX haX hyfa by (by100 simp)
          have haW: "a \<in> W"
            using hy hVeq hinvA by (by100 blast)
          have hyY: "y \<in> Y"
            using hImg_subY hy by (by100 blast)
          show "y \<in> (f ` A) \<inter> {y \<in> Y. inv_into X f y \<in> W}"
            using hy hyY hinvX haW by (by100 blast)
        qed
      next
        show "(f ` A) \<inter> {y \<in> Y. inv_into X f y \<in> W} \<subseteq>
            {y \<in> f ` A. inv_into A f y \<in> V}"
        proof
          fix y
          assume hy: "y \<in> (f ` A) \<inter> {y \<in> Y. inv_into X f y \<in> W}"
          obtain a where haA: "a \<in> A" and hyfa: "y = f a"
            using hy by (by100 blast)
          have haX: "a \<in> X"
            using hA haA by (by100 blast)
          have hinvA: "inv_into A f y = a"
            using hinjA haA hyfa by (by100 simp)
          have hinvX: "inv_into X f y = a"
            using hinjX haX hyfa by (by100 simp)
          have haW: "a \<in> W"
            using hy hinvX by (by100 blast)
          have hinvA_V: "inv_into A f y \<in> V"
            using hVeq hinvA haA haW by (by100 blast)
          show "y \<in> {y \<in> f ` A. inv_into A f y \<in> V}"
            using hy hinvA_V by (by100 blast)
        qed
      qed
      show "{y \<in> f ` A. inv_into A f y \<in> V} \<in>
          subspace_topology Y TY (f ` A)"
        unfolding hpre_eq subspace_topology_def using hpreY by (by100 blast)
    qed
  qed
  show ?thesis
    unfolding top1_homeomorphism_on_def
    using htopA htopImg hbijA hcont_A hcont_inv_A by (by100 blast)
qed

lemma geotop_plane_chart_domain_connected_dev34:
  fixes U :: "(real^2) set"
  assumes hhomeo: "top1_homeomorphism_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
  shows "top1_connected_on U
      (subspace_topology UNIV geotop_euclidean_topology U)"
proof -
  let ?TU = "subspace_topology UNIV geotop_euclidean_topology U"
  have htop_UNIV: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
    unfolding geotop_euclidean_topology_eq_open_sets
    by (rule top1_open_sets_is_topology_on_UNIV)
  have htop_U: "is_topology_on U ?TU"
    by (rule subspace_topology_is_topology_on[OF htop_UNIV subset_UNIV])
  have hcont_inv: "top1_continuous_map_on (UNIV::(real^2) set)
      geotop_euclidean_topology U ?TU (inv_into U f)"
    by (rule top1_homeomorphism_on_imp_cont2[OF hhomeo])
  have hUNIV_sub_eq:
      "subspace_topology UNIV geotop_euclidean_topology (UNIV::(real^2) set)
       = geotop_euclidean_topology"
    by (rule subspace_topology_self_carrier) (by100 simp)
  have hconn_UNIV: "top1_connected_on (UNIV::(real^2) set)
      geotop_euclidean_topology"
  proof -
    have "connected (UNIV::(real^2) set)"
      by (rule connected_UNIV)
    hence "top1_connected_on (UNIV::(real^2) set)
        (subspace_topology UNIV geotop_euclidean_topology (UNIV::(real^2) set))"
      using top1_connected_on_geotop_iff_connected[of "UNIV::(real^2) set"]
      by (by100 simp)
    thus ?thesis
      using hUNIV_sub_eq by (by100 simp)
  qed
  have hconn_UNIV_sub: "top1_connected_on (UNIV::(real^2) set)
      (subspace_topology UNIV geotop_euclidean_topology (UNIV::(real^2) set))"
    using hconn_UNIV hUNIV_sub_eq by (by100 simp)
  have hbij: "bij_betw f U (UNIV::(real^2) set)"
    by (rule top1_homeomorphism_on_imp_bij[OF hhomeo])
  have hinj: "inj_on f U"
    using hbij by (rule bij_betw_imp_inj_on)
  have hsurj: "f ` U = (UNIV::(real^2) set)"
    using hbij unfolding bij_betw_def by (by100 blast)
  have himage_eq: "(inv_into U f) ` (UNIV::(real^2) set) = U"
  proof
    show "(inv_into U f) ` (UNIV::(real^2) set) \<subseteq> U"
    proof
      fix y
      assume hy: "y \<in> (inv_into U f) ` (UNIV::(real^2) set)"
      obtain z where hz: "z \<in> (UNIV::(real^2) set)"
        and hyz: "y = inv_into U f z"
        using hy by (by100 blast)
      have hz_img: "z \<in> f ` U"
        using hsurj hz by (by100 simp)
      obtain u where huU: "u \<in> U" and hfuz: "f u = z"
        using hz_img by (by100 blast)
      have "y = u"
        using hyz inv_into_f_eq[OF hinj huU hfuz] by (by100 simp)
      thus "y \<in> U"
        using huU by (by100 simp)
    qed
  next
    show "U \<subseteq> (inv_into U f) ` (UNIV::(real^2) set)"
    proof
      fix y
      assume hyU: "y \<in> U"
      have hy_inv: "y = inv_into U f (f y)"
        using bij_betw_inv_into_left[OF hbij hyU] by (by100 simp)
      show "y \<in> (inv_into U f) ` (UNIV::(real^2) set)"
        using image_eqI[of y "inv_into U f" "f y" "UNIV::(real^2) set"] hy_inv
        by (by100 blast)
    qed
  qed
  have hconn_U_self: "top1_connected_on U (subspace_topology U ?TU U)"
    by (rule Theorem_GT_1_8
        [OF htop_UNIV htop_U hcont_inv subset_UNIV himage_eq hconn_UNIV_sub])
  have hTU_sub: "\<forall>V\<in>?TU. V \<subseteq> U"
    unfolding subspace_topology_def by (by100 blast)
  have hU_self_eq: "subspace_topology U ?TU U = ?TU"
    by (rule subspace_topology_self_carrier[OF hTU_sub])
  show ?thesis
    using hconn_U_self hU_self_eq by (by100 simp)
qed

lemma geotop_homeomorphism_image_arc_dev34:
  fixes A U :: "(real^2) set"
  assumes hhomeo: "top1_homeomorphism_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
  assumes hAsub: "A \<subseteq> U"
  assumes hAarc: "geotop_is_arc A
      (subspace_topology UNIV geotop_euclidean_topology A)"
  shows "geotop_is_arc (f ` A)
      (subspace_topology UNIV geotop_euclidean_topology (f ` A))"
proof -
  obtain \<gamma> :: "real \<Rightarrow> real^2" where h\<gamma>arc: "arc \<gamma>"
    and h\<gamma>img: "path_image \<gamma> = A"
    using geotop_is_arc_imp_HOL_arc[OF hAarc] by (by100 blast)
  have hcont_top1: "top1_continuous_map_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
    by (rule top1_homeomorphism_on_imp_cont1[OF hhomeo])
  have hUNIV_eq: "subspace_topology UNIV geotop_euclidean_topology (UNIV::(real^2) set)
      = geotop_euclidean_topology"
    by (rule subspace_topology_self_carrier) (by100 simp)
  have hcont_sub: "top1_continuous_map_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set)
      (subspace_topology UNIV geotop_euclidean_topology (UNIV::(real^2) set)) f"
    using hcont_top1 hUNIV_eq by (by100 simp)
  have hcontU: "continuous_on U f"
    by (rule top1_continuous_map_on_geotop_imp_continuous_on[OF hcont_sub])
  have hcontA: "continuous_on A f"
    by (rule continuous_on_subset[OF hcontU hAsub])
  have hcont_img: "continuous_on (path_image \<gamma>) f"
    using hcontA h\<gamma>img by (by100 simp)
  have hbij: "bij_betw f U (UNIV::(real^2) set)"
    by (rule top1_homeomorphism_on_imp_bij[OF hhomeo])
  have hinjU: "inj_on f U"
    using hbij by (rule bij_betw_imp_inj_on)
  have hinjA: "inj_on f A"
    by (rule inj_on_subset[OF hinjU hAsub])
  have hinj_img: "inj_on f (path_image \<gamma>)"
    using hinjA h\<gamma>img by (by100 simp)
  have hsimple: "simple_path (f \<circ> \<gamma>)"
    by (rule simple_path_continuous_image
        [OF arc_imp_simple_path[OF h\<gamma>arc] hcont_img hinj_img])
  have hends: "pathfinish (f \<circ> \<gamma>) \<noteq> pathstart (f \<circ> \<gamma>)"
  proof
    assume heq: "pathfinish (f \<circ> \<gamma>) = pathstart (f \<circ> \<gamma>)"
    have h\<gamma>0: "\<gamma> 0 \<in> path_image \<gamma>"
      unfolding path_image_def by (by100 simp)
    have h\<gamma>1: "\<gamma> 1 \<in> path_image \<gamma>"
      unfolding path_image_def by (by100 simp)
    have h\<gamma>0A: "\<gamma> 0 \<in> A"
      using h\<gamma>0 h\<gamma>img by (by100 simp)
    have h\<gamma>1A: "\<gamma> 1 \<in> A"
      using h\<gamma>1 h\<gamma>img by (by100 simp)
    have hf_eq: "f (\<gamma> 1) = f (\<gamma> 0)"
      using heq unfolding pathfinish_def pathstart_def by (by100 simp)
    have "\<gamma> 1 = \<gamma> 0"
      by (rule inj_onD[OF hinjA hf_eq h\<gamma>1A h\<gamma>0A])
    have "pathfinish \<gamma> = pathstart \<gamma>"
      using \<open>\<gamma> 1 = \<gamma> 0\<close> unfolding pathfinish_def pathstart_def by (by100 simp)
    thus False
      using arc_distinct_ends[OF h\<gamma>arc] by (by100 blast)
  qed
  have hfg_arc: "arc (f \<circ> \<gamma>)"
    using hsimple hends unfolding arc_simple_path by (by100 blast)
  have hfg_img: "path_image (f \<circ> \<gamma>) = f ` A"
    using h\<gamma>img path_image_compose[of f \<gamma>] by (by100 simp)
  have "geotop_is_arc (path_image (f \<circ> \<gamma>))
      (subspace_topology UNIV geotop_euclidean_topology (path_image (f \<circ> \<gamma>)))"
    by (rule geotop_HOL_arc_imp_geotop_is_arc[OF hfg_arc])
  thus ?thesis
    using hfg_img by (by100 simp)
qed

lemma geotop_homeomorphism_image_1sphere_dev34:
  fixes J U :: "(real^2) set"
  assumes hhomeo: "top1_homeomorphism_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
  assumes hJsub: "J \<subseteq> U"
  assumes hJsphere: "geotop_is_n_sphere J
      (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "geotop_is_n_sphere (f ` J)
      (subspace_topology UNIV geotop_euclidean_topology (f ` J)) 1"
proof -
  obtain g where hg: "top1_homeomorphism_on J
      (subspace_topology UNIV geotop_euclidean_topology J)
      (geotop_std_sphere::(real^2) set)
      (subspace_topology UNIV geotop_euclidean_topology geotop_std_sphere) g"
    using hJsphere unfolding geotop_is_n_sphere_def by (by100 blast)
  have hsource_eq:
    "subspace_topology U
        (subspace_topology UNIV geotop_euclidean_topology U) J =
     subspace_topology UNIV geotop_euclidean_topology J"
    by (rule subspace_topology_trans[OF hJsub])
  have hres: "top1_homeomorphism_on J
      (subspace_topology U (subspace_topology UNIV geotop_euclidean_topology U) J)
      (f ` J) (subspace_topology UNIV geotop_euclidean_topology (f ` J)) f"
    by (rule top1_homeomorphism_on_subspace_image_dev34[OF hhomeo hJsub])
  have hres_geo: "top1_homeomorphism_on J
      (subspace_topology UNIV geotop_euclidean_topology J)
      (f ` J) (subspace_topology UNIV geotop_euclidean_topology (f ` J)) f"
    using hres hsource_eq by (by100 simp)
  have hres_sym: "top1_homeomorphism_on (f ` J)
      (subspace_topology UNIV geotop_euclidean_topology (f ` J))
      J (subspace_topology UNIV geotop_euclidean_topology J) (inv_into J f)"
    by (rule top1_homeomorphism_on_sym[OF hres_geo])
  have hcomp: "top1_homeomorphism_on (f ` J)
      (subspace_topology UNIV geotop_euclidean_topology (f ` J))
      (geotop_std_sphere::(real^2) set)
      (subspace_topology UNIV geotop_euclidean_topology geotop_std_sphere)
      (g \<circ> inv_into J f)"
    by (rule top1_homeomorphism_on_comp[OF hres_sym hg])
  have htop_img: "is_topology_on (f ` J)
      (subspace_topology UNIV geotop_euclidean_topology (f ` J))"
    using hcomp unfolding top1_homeomorphism_on_def by (by100 blast)
  show ?thesis
    unfolding geotop_is_n_sphere_def
    using htop_img hcomp by (by100 blast)
qed

lemma geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34:
  fixes K :: "(real^2) set set" and e \<sigma> U :: "(real^2) set"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>face: "geotop_is_face e \<sigma>"
  assumes hr: "0 < r"
  assumes hlocal_poly_eq_\<sigma>:
    "ball p r \<inter> geotop_polyhedron K = ball p r \<inter> \<sigma>"
  assumes hballU: "geotop_polyhedron K \<inter> ball p r \<subseteq> U"
  assumes hUsubM: "U \<subseteq> geotop_polyhedron K"
  shows "\<exists>A. A = sphere p r \<inter> \<sigma>
      \<and> geotop_is_arc A
          (subspace_topology UNIV geotop_euclidean_topology A)
      \<and> \<not> top1_connected_on (U - A)
          (subspace_topology UNIV geotop_euclidean_topology (U - A))"
  (**
    Moise Lemma 3 crosscut form.  In the one-sided local model, take the full
    small spherical crosscut \<open>A = sphere p r \<inter> \<sigma>\<close>.  The proof should use the
    first radius-crossing argument: any carrier path from the inner cap to the
    outer side first meets \<open>sphere p r\<close> while still in the local ball, hence by
    the local equality it meets \<open>A\<close>. **)
  sorry

lemma geotop_edge_one_side_simplex_local_semicircle_radius_separates_domain_dev34:
  fixes K :: "(real^2) set set" and e \<sigma> U :: "(real^2) set"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>face: "geotop_is_face e \<sigma>"
  assumes hs: "0 < s"
  assumes hlocal_poly_eq_\<sigma>:
    "ball p s \<inter> geotop_polyhedron K = ball p s \<inter> \<sigma>"
  assumes hballU_s: "geotop_polyhedron K \<inter> ball p s \<subseteq> U"
  assumes hUsubM: "U \<subseteq> geotop_polyhedron K"
  shows "\<exists>r A. 0 < r \<and> r < s
      \<and> A \<subseteq> sphere p r \<inter> \<sigma>
      \<and> geotop_is_arc A
          (subspace_topology UNIV geotop_euclidean_topology A)
      \<and> \<not> top1_connected_on (U - A)
          (subspace_topology UNIV geotop_euclidean_topology (U - A))"
  (**
    Radius-explicit form of Moise Lemma 3.  Choose the semicircle in the
    unique incident 2-simplex with center \<open>p\<close> and radius strictly smaller
    than the local chart radius \<open>s\<close>; that semicircle is the separating arc. **)
proof -
  define r where "r = s / 2"
  have hr_pos: "0 < r"
    using hs unfolding r_def by (by100 simp)
  have hrs: "r < s"
    using hs unfolding r_def by (by100 simp)
  have hlocal_eq_r:
    "ball p r \<inter> geotop_polyhedron K = ball p r \<inter> \<sigma>"
  proof
    show "ball p r \<inter> geotop_polyhedron K \<subseteq> ball p r \<inter> \<sigma>"
    proof
      fix x
      assume hx: "x \<in> ball p r \<inter> geotop_polyhedron K"
      have hx_ball_s: "x \<in> ball p s"
        using hx hrs by (by100 simp)
      have hx_ball_poly_s: "x \<in> ball p s \<inter> geotop_polyhedron K"
        using hx hx_ball_s by (by100 blast)
      have hx_ball_sigma_s: "x \<in> ball p s \<inter> \<sigma>"
        using hlocal_poly_eq_\<sigma> hx_ball_poly_s by (by100 blast)
      show "x \<in> ball p r \<inter> \<sigma>"
        using hx hx_ball_sigma_s by (by100 blast)
    qed
    show "ball p r \<inter> \<sigma> \<subseteq> ball p r \<inter> geotop_polyhedron K"
    proof
      fix x
      assume hx: "x \<in> ball p r \<inter> \<sigma>"
      have hx_ball_s: "x \<in> ball p s"
        using hx hrs by (by100 simp)
      have hx_ball_sigma_s: "x \<in> ball p s \<inter> \<sigma>"
        using hx hx_ball_s by (by100 blast)
      have hx_ball_poly_s: "x \<in> ball p s \<inter> geotop_polyhedron K"
        using hlocal_poly_eq_\<sigma> hx_ball_sigma_s by (by100 blast)
      show "x \<in> ball p r \<inter> geotop_polyhedron K"
        using hx hx_ball_poly_s by (by100 blast)
    qed
  qed
  have hballU_r: "geotop_polyhedron K \<inter> ball p r \<subseteq> U"
  proof
    fix x
    assume hx: "x \<in> geotop_polyhedron K \<inter> ball p r"
    have hx_ball_s: "x \<in> ball p s"
      using hx hrs by (by100 simp)
    have hx_poly_ball_s: "x \<in> geotop_polyhedron K \<inter> ball p s"
      using hx hx_ball_s by (by100 blast)
    show "x \<in> U"
      using hballU_s hx_poly_ball_s by (by100 blast)
  qed
  have hsphere_sigma_subset_U: "sphere p r \<inter> \<sigma> \<subseteq> U"
  proof
    fix x
    assume hx: "x \<in> sphere p r \<inter> \<sigma>"
    have hx_ball_s: "x \<in> ball p s"
      using hx hrs by (by100 simp)
    have hx_ball_sigma_s: "x \<in> ball p s \<inter> \<sigma>"
      using hx hx_ball_s by (by100 blast)
    have hx_ball_poly_s: "x \<in> ball p s \<inter> geotop_polyhedron K"
      using hlocal_poly_eq_\<sigma> hx_ball_sigma_s by (by100 blast)
    have hx_poly_ball_s: "x \<in> geotop_polyhedron K \<inter> ball p s"
      using hx_ball_poly_s by (by100 blast)
    show "x \<in> U"
      using hballU_s hx_poly_ball_s by (by100 blast)
  qed
  have hp_\<sigma>: "p \<in> \<sigma>"
  proof -
    have hp_e: "p \<in> e"
      using hp rel_interior_subset by (by100 blast)
    have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
      by (rule geotop_is_face_imp_subset[OF h\<sigma>face])
    show ?thesis
      using hp_e he_sub_\<sigma> by (by100 blast)
  qed
  have hsemicircle_book:
    "\<exists>A. A \<subseteq> sphere p r \<inter> \<sigma>
      \<and> geotop_is_arc A
          (subspace_topology UNIV geotop_euclidean_topology A)
      \<and> \<not> top1_connected_on (U - A)
          (subspace_topology UNIV geotop_euclidean_topology (U - A))"
  proof -
    obtain A where hA: "A = sphere p r \<inter> \<sigma>"
      and hA_arc: "geotop_is_arc A
          (subspace_topology UNIV geotop_euclidean_topology A)"
      and hA_sep: "\<not> top1_connected_on (U - A)
          (subspace_topology UNIV geotop_euclidean_topology (U - A))"
      using geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34
          [OF hedge hp h\<sigma>2 h\<sigma>face hr_pos hlocal_eq_r hballU_r hUsubM]
      by (by100 blast)
    show ?thesis
      using hA hA_arc hA_sep by (by100 blast)
  qed
  show ?thesis
    using hr_pos hrs hsemicircle_book by (by100 blast)
qed

lemma geotop_edge_one_side_simplex_local_semicircle_separates_domain_dev34:
  fixes K :: "(real^2) set set" and e \<sigma> U :: "(real^2) set"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>face: "geotop_is_face e \<sigma>"
  assumes hs: "0 < s"
  assumes hlocal_poly_eq_\<sigma>:
    "ball p s \<inter> geotop_polyhedron K = ball p s \<inter> \<sigma>"
  assumes hballU_s: "geotop_polyhedron K \<inter> ball p s \<subseteq> U"
  assumes hUsubM: "U \<subseteq> geotop_polyhedron K"
  shows "\<exists>A. A \<subseteq> U
      \<and> geotop_is_arc A
          (subspace_topology UNIV geotop_euclidean_topology A)
      \<and> \<not> top1_connected_on (U - A)
          (subspace_topology UNIV geotop_euclidean_topology (U - A))"
  (**
    Moise Lemma 3 local geometry isolated after the carrier analysis:
    a sufficiently small neighborhood of the edge-interior point in the
    polyhedron is exactly the one-sided half-neighborhood supplied by the
    unique incident 2-simplex.  Choose a small semicircle in that simplex,
    centered at \<open>p\<close>; it lies in \<open>U\<close>, is an arc, and separates \<open>U\<close>. **)
proof -
  obtain r A where hr_pos: "0 < r" and hrs: "r < s"
    and hA_sphere: "A \<subseteq> sphere p r \<inter> \<sigma>"
    and hAarc: "geotop_is_arc A
        (subspace_topology UNIV geotop_euclidean_topology A)"
    and hAsep: "\<not> top1_connected_on (U - A)
        (subspace_topology UNIV geotop_euclidean_topology (U - A))"
    using geotop_edge_one_side_simplex_local_semicircle_radius_separates_domain_dev34
      [OF hedge hp h\<sigma>2 h\<sigma>face hs hlocal_poly_eq_\<sigma> hballU_s hUsubM]
    by (by100 blast)
  have hA_small: "A \<subseteq> ball p s \<inter> \<sigma>"
  proof
    fix x
    assume hxA: "x \<in> A"
    have hx_sphere_sigma: "x \<in> sphere p r \<inter> \<sigma>"
      using hA_sphere hxA by (by100 blast)
    have hx_sphere: "x \<in> sphere p r"
      using hx_sphere_sigma by (by100 blast)
    have hx_sigma: "x \<in> \<sigma>"
      using hx_sphere_sigma by (by100 blast)
    have hx_ball: "x \<in> ball p s"
      using hx_sphere hrs by (by100 simp)
    show "x \<in> ball p s \<inter> \<sigma>"
      using hx_ball hx_sigma by (by100 blast)
  qed
  have hAsubU: "A \<subseteq> U"
  proof
    fix x
    assume hxA: "x \<in> A"
    have hx_ball_sigma: "x \<in> ball p s \<inter> \<sigma>"
      using hA_small hxA by (by100 blast)
    have hx_ball_poly: "x \<in> ball p s \<inter> geotop_polyhedron K"
      using hx_ball_sigma hlocal_poly_eq_\<sigma>[symmetric] by (by100 simp)
    have hx_poly_ball: "x \<in> geotop_polyhedron K \<inter> ball p s"
      using hx_ball_poly by (by100 blast)
    show "x \<in> U"
      using hballU_s hx_poly_ball by (by100 blast)
  qed
  show ?thesis
    using hAsubU hAarc hAsep by (by100 blast)
qed

lemma geotop_unique_incident_2simplex_small_semicircle_domain_separates_chart_dev34:
  fixes K :: "(real^2) set set" and e U A :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hunique:
    "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  assumes hlocal_ball: "\<exists>r>0. geotop_polyhedron K \<inter> ball p r \<subseteq> U"
  assumes hUsubM: "U \<subseteq> geotop_polyhedron K"
  shows "\<exists>A. A \<subseteq> U
      \<and> geotop_is_arc A
          (subspace_topology UNIV geotop_euclidean_topology A)
      \<and> \<not> top1_connected_on (U - A)
          (subspace_topology UNIV geotop_euclidean_topology (U - A))"
  (**
    Moise Lemma 3 local picture: with only one 2-simplex incident to the edge,
    choose a sufficiently small semicircle in that simplex, centered at the
    edge-interior point.  The local-ball assumption keeps the semicircle inside
    the chart domain \<open>U\<close>; since \<open>U\<close> is a subspace neighborhood in \<open>|K|\<close>,
    the semicircle separates the half-neighborhood in \<open>U\<close>. **)
proof -
  have hp_e: "p \<in> e"
    using hp rel_interior_subset by (by100 blast)
  obtain rU where hrU: "0 < rU"
    and hballU: "geotop_polyhedron K \<inter> ball p rU \<subseteq> U"
    using hlocal_ball by (by100 blast)
  obtain rK F \<sigma> where hrK: "0 < rK"
    and hFfin: "finite F"
    and hFsub: "F \<subseteq> K"
    and heF: "e \<in> F"
    and h\<sigma>F: "\<sigma> \<in> F"
    and h\<sigma>K: "\<sigma> \<in> K"
    and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and h\<sigma>face: "geotop_is_face e \<sigma>"
    and hfaces: "{\<tau>\<in>K. geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>} = {\<sigma>}"
    and hcover: "ball p rK \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
    by (rule geotop_complex_unique_edge_face_point_finite_local_cover_dev34
        [OF hK heK hp_e hunique])
  define r where "r = min rU rK"
  have hr: "0 < r"
    using hrU hrK unfolding r_def by (by100 simp)
  have hballU_r: "geotop_polyhedron K \<inter> ball p r \<subseteq> U"
  proof -
    have hball_sub: "ball p r \<subseteq> ball p rU"
      unfolding r_def by (by100 auto)
    have "geotop_polyhedron K \<inter> ball p r
        \<subseteq> geotop_polyhedron K \<inter> ball p rU"
      using hball_sub by (by100 blast)
    thus ?thesis
      using hballU by (by100 blast)
  qed
  have hcover_r: "ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
  proof -
    have hball_sub: "ball p r \<subseteq> ball p rK"
      unfolding r_def by (by100 auto)
    have "ball p r \<inter> geotop_polyhedron K
        \<subseteq> ball p rK \<inter> geotop_polyhedron K"
      using hball_sub by (by100 blast)
    thus ?thesis
      using hcover by (by100 blast)
  qed
  have hp_unionF: "p \<in> \<Union>F"
    using heF hp_e by (by100 blast)
  obtain \<delta> where h\<delta>: "0 < \<delta>"
    and hisolate: "ball p \<delta> \<inter> \<Union>F \<subseteq> \<Union>{\<tau>\<in>F. p \<in> \<tau>}"
    using geotop_complex_finite_subcomplex_local_point_carriers_dev34
      [OF hK hFfin hFsub hp_unionF]
    by (by100 blast)
  define s where "s = min r \<delta>"
  have hs: "0 < s"
    using hr h\<delta> unfolding s_def by (by100 simp)
  have hballU_s: "geotop_polyhedron K \<inter> ball p s \<subseteq> U"
  proof -
    have hball_sub: "ball p s \<subseteq> ball p r"
      unfolding s_def by (by100 auto)
    have "geotop_polyhedron K \<inter> ball p s
        \<subseteq> geotop_polyhedron K \<inter> ball p r"
      using hball_sub by (by100 blast)
    thus ?thesis
      using hballU_r by (by100 blast)
  qed
  have hcover_s: "ball p s \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
  proof -
    have hball_sub: "ball p s \<subseteq> ball p r"
      unfolding s_def by (by100 auto)
    have "ball p s \<inter> geotop_polyhedron K
        \<subseteq> ball p r \<inter> geotop_polyhedron K"
      using hball_sub by (by100 blast)
    thus ?thesis
      using hcover_r by (by100 blast)
  qed
  have hpoint_carriers_s:
    "ball p s \<inter> geotop_polyhedron K \<subseteq> \<Union>{\<tau>\<in>F. p \<in> \<tau>}"
  proof
    fix x
    assume hx: "x \<in> ball p s \<inter> geotop_polyhedron K"
    have hxF: "x \<in> \<Union>F"
      using hcover_s hx by (by100 blast)
    have hball_sub: "ball p s \<subseteq> ball p \<delta>"
      unfolding s_def by (by100 auto)
    have hx\<delta>: "x \<in> ball p \<delta>"
      using hx hball_sub by (by100 blast)
    have "x \<in> ball p \<delta> \<inter> \<Union>F"
      using hxF hx\<delta> by (by100 blast)
    thus "x \<in> \<Union>{\<tau>\<in>F. p \<in> \<tau>}"
      using hisolate by (by100 blast)
  qed
  have hpoint_carriers_subset_\<sigma>: "\<Union>{\<tau>\<in>F. p \<in> \<tau>} \<subseteq> \<sigma>"
    by (rule geotop_complex_unique_edge_face_point_carrier_union_subset_unique_face_dev34
        [OF hK heK hedge hp h\<sigma>K h\<sigma>2 h\<sigma>face hfaces hFsub])
  have hlocal_poly_\<sigma>: "ball p s \<inter> geotop_polyhedron K \<subseteq> \<sigma>"
    using hpoint_carriers_s hpoint_carriers_subset_\<sigma> by (by100 blast)
  have h\<sigma>subM: "\<sigma> \<subseteq> geotop_polyhedron K"
    using h\<sigma>K unfolding geotop_polyhedron_def by (by100 blast)
  have hlocal_poly_eq_\<sigma>:
    "ball p s \<inter> geotop_polyhedron K = ball p s \<inter> \<sigma>"
  proof
    show "ball p s \<inter> geotop_polyhedron K \<subseteq> ball p s \<inter> \<sigma>"
      using hlocal_poly_\<sigma> by (by100 blast)
  next
    show "ball p s \<inter> \<sigma> \<subseteq> ball p s \<inter> geotop_polyhedron K"
      using h\<sigma>subM by (by100 blast)
  qed
  (**
    Remaining Moise Lemma 3 geometry: choose the small semicircle in the unique
    incident 2-simplex \<open>\<sigma>\<close>, use the finite carrier cover \<open>F\<close> and the shrunken
    radius \<open>s\<close> to keep it inside \<open>U\<close>, and prove that its complement in
    \<open>U\<close> separates. **)
  show ?thesis
    by (rule geotop_edge_one_side_simplex_local_semicircle_separates_domain_dev34
        [OF hedge hp h\<sigma>2 h\<sigma>face hs hlocal_poly_eq_\<sigma> hballU_s hUsubM])
qed

lemma geotop_unique_incident_2simplex_small_semicircle_separates_chart_dev34:
  fixes K :: "(real^2) set set" and e U A :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hunique:
    "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  assumes hlocal_ball: "\<exists>r>0. geotop_polyhedron K \<inter> ball p r \<subseteq> U"
  assumes hUsubM: "U \<subseteq> geotop_polyhedron K"
  assumes hhomeo: "top1_homeomorphism_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
  shows "\<exists>A. A \<subseteq> U
      \<and> geotop_is_arc (f ` A)
          (subspace_topology UNIV geotop_euclidean_topology (f ` A))
      \<and> \<not> top1_connected_on (U - A)
          (subspace_topology UNIV geotop_euclidean_topology (U - A))"
proof -
  obtain A where hAsub: "A \<subseteq> U"
    and hAarc: "geotop_is_arc A
          (subspace_topology UNIV geotop_euclidean_topology A)"
    and hAsep: "\<not> top1_connected_on (U - A)
          (subspace_topology UNIV geotop_euclidean_topology (U - A))"
    using geotop_unique_incident_2simplex_small_semicircle_domain_separates_chart_dev34
      [OF hK heK hedge hp hunique hlocal_ball hUsubM]
    by (by100 blast)
  have hAimg: "geotop_is_arc (f ` A)
      (subspace_topology UNIV geotop_euclidean_topology (f ` A))"
    by (rule geotop_homeomorphism_image_arc_dev34[OF hhomeo hAsub hAarc])
  show ?thesis
    using hAsub hAimg hAsep by (by100 blast)
qed

lemma geotop_2simplex_face_containing_edge_eq_edge_or_simplex_dev34:
  fixes F e \<sigma> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes hF\<sigma>: "geotop_is_face F \<sigma>"
  assumes hedge: "geotop_is_edge e"
  assumes heF: "e \<subseteq> F"
  shows "F = e \<or> F = \<sigma>"
  (**
    In a 2-simplex the face lattice has no proper face strictly between an
    edge and the full simplex.  This is the combinatorial part of the
    two-triangle local edge model. **)
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and he_eq: "e = geotop_convex_hull W"
    and heW: "geotop_simplex_vertices e W"
    and hW_card: "card W = 2"
    by (rule geotop_edge_face_witness_card_two[OF hedge he\<sigma>])
  obtain V\<^sub>F W\<^sub>F where h\<sigma>VF: "geotop_simplex_vertices \<sigma> V\<^sub>F"
    and hWF_ne: "W\<^sub>F \<noteq> {}"
    and hWF_sub: "W\<^sub>F \<subseteq> V\<^sub>F"
    and hF_eq: "F = geotop_convex_hull W\<^sub>F"
    and hFWF: "geotop_simplex_vertices F W\<^sub>F"
    by (rule geotop_face_witness_simplex_vertices[OF hF\<sigma>])
  have hVF_eq: "V\<^sub>F = V"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>VF h\<sigma>V])
  have hWF_sub_V: "W\<^sub>F \<subseteq> V"
    using hWF_sub hVF_eq by (by100 simp)
  have hW_sub_WF: "W \<subseteq> W\<^sub>F"
  proof
    fix x
    assume hxW: "x \<in> W"
    have hxV: "x \<in> V"
      using hxW hW_sub by (by100 blast)
    have hx_e: "x \<in> e"
    proof -
      have "x \<in> convex hull W"
        using hxW hull_inc[of x W] by (by100 simp)
      hence "x \<in> geotop_convex_hull W"
        using geotop_convex_hull_eq_HOL[of W] by (by100 simp)
      thus ?thesis
        using he_eq by (by100 simp)
    qed
    have hxF: "x \<in> F"
      using hx_e heF by (by100 blast)
    show "x \<in> W\<^sub>F"
    proof (rule ccontr)
      assume hx_not_WF: "\<not> x \<in> W\<^sub>F"
      have hWF_sub_no_x: "W\<^sub>F \<subseteq> V - {x}"
        using hWF_sub_V hx_not_WF by (by100 blast)
      have hx_not_hull: "x \<notin> geotop_convex_hull W\<^sub>F"
        by (rule geotop_simplex_vertex_notin_hull_of_other_vertices
            [OF h\<sigma>V hxV hWF_sub_no_x])
      have "x \<in> geotop_convex_hull W\<^sub>F"
        using hxF hF_eq by (by100 simp)
      thus False
        using hx_not_hull by (by100 blast)
    qed
  qed
  have hV_card: "card V = 3"
  proof -
    obtain V2 m where hV2_fin: "finite V2"
      and hV2_card: "card V2 = 2 + 1"
      and h2_le_m: "2 \<le> m"
      and hgp_V2: "geotop_general_position V2 m"
      and h\<sigma>_eq_V2: "\<sigma> = geotop_convex_hull V2"
      using h\<sigma>2 unfolding geotop_simplex_dim_def by (by100 blast)
    have h\<sigma>V2: "geotop_simplex_vertices \<sigma> V2"
      unfolding geotop_simplex_vertices_def
      using hV2_fin hV2_card h2_le_m hgp_V2 h\<sigma>_eq_V2 by (by100 blast)
    have hV_eq: "V = V2"
      by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>V2])
    show ?thesis
      using hV_eq hV2_card by (by100 simp)
  qed
  have hV_fin: "finite V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hWF_cases: "W\<^sub>F = W \<or> W\<^sub>F = V"
  proof (cases "W\<^sub>F = W")
    case True
    show ?thesis
      using True by (by100 blast)
  next
    case False
    have hWF_fin: "finite W\<^sub>F"
      using hFWF unfolding geotop_simplex_vertices_def by (by100 blast)
    have hW_psub_WF: "W \<subset> W\<^sub>F"
      using hW_sub_WF False by (by100 blast)
    have hW_card_lt: "card W < card W\<^sub>F"
      by (rule psubset_card_mono[OF hWF_fin hW_psub_WF])
    have hWF_le_V: "card W\<^sub>F \<le> card V"
      by (rule card_mono[OF hV_fin hWF_sub_V])
    have hWF_card: "card W\<^sub>F = card V"
      using hW_card hW_card_lt hWF_le_V hV_card by (by100 arith)
    have hWF_eq_V: "W\<^sub>F = V"
    proof (rule card_seteq[OF hV_fin hWF_sub_V])
      show "card V \<le> card W\<^sub>F"
        using hWF_card by (by100 simp)
    qed
    show ?thesis
      using hWF_eq_V by (by100 blast)
  qed
  show ?thesis
  proof -
    have h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
      using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
    from hWF_cases show ?thesis
    proof
      assume hWF_eq_W: "W\<^sub>F = W"
      have "F = e"
        using hWF_eq_W hF_eq he_eq by (by100 simp)
      show ?thesis
        using \<open>F = e\<close> by (by100 blast)
    next
      assume hWF_eq_V: "W\<^sub>F = V"
      have "F = \<sigma>"
        using hWF_eq_V hF_eq h\<sigma>_eq by (by100 simp)
      show ?thesis
        using \<open>F = \<sigma>\<close> by (by100 blast)
    qed
  qed
qed

lemma geotop_complex_two_2simplex_shared_edge_inter_eq_edge_dev34:
  fixes K :: "(real^2) set set"
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  assumes hedge: "geotop_is_edge e"
  shows "\<sigma> \<inter> \<tau> = e"
  (**
    In a complex, two distinct 2-simplexes sharing the edge \<open>e\<close> intersect
    exactly in \<open>e\<close>.  The complex intersection is a face of each simplex, and
    the previous face-containment lemma rules out a larger common face. **)
proof -
  let ?I = "\<sigma> \<inter> \<tau>"
  have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
    by (rule geotop_is_face_imp_subset[OF he\<sigma>])
  have he_sub_\<tau>: "e \<subseteq> \<tau>"
    by (rule geotop_is_face_imp_subset[OF he\<tau>])
  have he_nonempty: "e \<noteq> {}"
  proof -
    have he_dim: "geotop_simplex_dim e 1"
      using hedge unfolding geotop_is_edge_def by (by100 simp)
    have he_simplex: "geotop_is_simplex e"
      by (rule geotop_simplex_dim_imp_is_simplex[OF he_dim])
    show ?thesis
      by (rule geotop_simplex_nonempty[OF he_simplex])
  qed
  have he_sub_I: "e \<subseteq> ?I"
    using he_sub_\<sigma> he_sub_\<tau> by (by100 blast)
  have hI_nonempty: "?I \<noteq> {}"
    using he_nonempty he_sub_I by (by100 blast)
  have hI_face_\<sigma>: "geotop_is_face ?I \<sigma>"
    using geotop_is_complex_intersection[OF hK] h\<sigma>K h\<tau>K hI_nonempty
    by (by100 blast)
  have hI_face_\<tau>: "geotop_is_face ?I \<tau>"
    using geotop_is_complex_intersection[OF hK] h\<sigma>K h\<tau>K hI_nonempty
    by (by100 blast)
  have hcase_\<sigma>: "?I = e \<or> ?I = \<sigma>"
    by (rule geotop_2simplex_face_containing_edge_eq_edge_or_simplex_dev34
        [OF h\<sigma>2 he\<sigma> hI_face_\<sigma> hedge he_sub_I])
  have hcase_\<tau>: "?I = e \<or> ?I = \<tau>"
    by (rule geotop_2simplex_face_containing_edge_eq_edge_or_simplex_dev34
        [OF h\<tau>2 he\<tau> hI_face_\<tau> hedge he_sub_I])
  show ?thesis
  proof (rule ccontr)
    assume hnot: "\<not> ?thesis"
    have hI_eq_\<sigma>: "?I = \<sigma>"
      using hcase_\<sigma> hnot by (by100 blast)
    have hI_eq_\<tau>: "?I = \<tau>"
      using hcase_\<tau> hnot by (by100 blast)
    have "\<sigma> = \<tau>"
      using hI_eq_\<sigma> hI_eq_\<tau> by (by100 simp)
    thus False
      using h\<sigma>\<tau> by (by100 blast)
  qed
qed

lemma geotop_2simplex_opposite_vertex_notin_edge_affine_hull_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hc: "c \<notin> {a, b}"
  shows "c \<notin> affine hull {a, b}"
  (**
    In the shared-edge picture, the vertex opposite the edge is not on the
    affine line of that edge. **)
proof -
  have hcV: "c \<in> {a, b, c}"
    by (by100 simp)
  have hsub: "{a, b} \<subseteq> {a, b, c} - {c}"
    using hc by (by100 blast)
  show ?thesis
    by (rule geotop_simplex_vertex_notin_affine_hull_of_other_vertices_dev34
        [OF h\<sigma>V hcV hsub])
qed

lemma geotop_two_2simplex_shared_edge_vertices_obtain_dev34:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  assumes hedge: "geotop_is_edge e"
  obtains a b c d where
    "a \<noteq> b"
    "c \<notin> {a, b}"
    "d \<notin> {a, b}"
    "c \<noteq> d"
    "e = geotop_convex_hull {a, b}"
    "geotop_simplex_vertices \<sigma> {a, b, c}"
    "geotop_simplex_vertices \<tau> {a, b, d}"
  (**
    Shared-edge vertex form for the two-triangle local model: the common edge
    has two vertices \<open>a,b\<close>, and the two distinct 2-simplexes have distinct
    third vertices \<open>c\<close> and \<open>d\<close>. **)
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and he_eq_W: "e = geotop_convex_hull W"
    and heW: "geotop_simplex_vertices e W"
    and hW_card: "card W = 2"
    by (rule geotop_edge_face_witness_card_two[OF hedge he\<sigma>])
  have hW_fin: "finite W"
    using heW unfolding geotop_simplex_vertices_def by (by100 blast)
  obtain a b where hW_eq: "W = {a, b}" and hab: "a \<noteq> b"
    using hW_card card_2_iff by (by100 metis)
  have he_eq_ab: "e = geotop_convex_hull {a, b}"
    using he_eq_W hW_eq by (by100 simp)
  have hV_card: "card V = 3"
  proof -
    obtain V2 m where hV2_fin: "finite V2"
      and hV2_card: "card V2 = 2 + 1"
      and h2_le_m: "2 \<le> m"
      and hgp_V2: "geotop_general_position V2 m"
      and h\<sigma>_eq_V2: "\<sigma> = geotop_convex_hull V2"
      using h\<sigma>2 unfolding geotop_simplex_dim_def by (by100 blast)
    have h\<sigma>V2: "geotop_simplex_vertices \<sigma> V2"
      unfolding geotop_simplex_vertices_def
      using hV2_fin hV2_card h2_le_m hgp_V2 h\<sigma>_eq_V2 by (by100 blast)
    have hV_eq: "V = V2"
      by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>V2])
    show ?thesis
      using hV_eq hV2_card by (by100 simp)
  qed
  have hV_fin: "finite V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  obtain c where hcV: "c \<in> V" and hc_not_W: "c \<notin> W"
  proof -
    have "W \<noteq> V"
    proof
      assume hWV: "W = V"
      show False
        using hW_card hV_card hWV by (by100 arith)
    qed
    then obtain c where "c \<in> V" and "c \<notin> W"
      using hW_sub by (by100 blast)
    thus ?thesis
      by (rule that)
  qed
  have hc_not_ab: "c \<notin> {a, b}"
    using hc_not_W hW_eq by (by100 simp)
  have h\<sigma>V_ab: "geotop_simplex_vertices \<sigma> {a, b, c}"
  proof -
    have haV: "a \<in> V"
      using hW_eq hW_sub by (by100 blast)
    have hbV: "b \<in> V"
      using hW_eq hW_sub by (by100 blast)
    have hac: "a \<noteq> c"
      using hc_not_ab by (by100 blast)
    have hbc: "b \<noteq> c"
      using hc_not_ab by (by100 blast)
    have hV_eq: "V = {a, b, c}"
      by (rule geotop_2simplex_vertices_three_eq_dev34
          [OF h\<sigma>2 h\<sigma>V haV hbV hcV hab hac hbc])
    show ?thesis
      using h\<sigma>V hV_eq by (by100 simp)
  qed
  obtain V\<^sub>\<tau> W\<^sub>\<tau> where h\<tau>V: "geotop_simplex_vertices \<tau> V\<^sub>\<tau>"
    and hW\<tau>_ne: "W\<^sub>\<tau> \<noteq> {}"
    and hW\<tau>_sub: "W\<^sub>\<tau> \<subseteq> V\<^sub>\<tau>"
    and he_eq_W\<tau>: "e = geotop_convex_hull W\<^sub>\<tau>"
    and heW\<tau>: "geotop_simplex_vertices e W\<^sub>\<tau>"
    and hW\<tau>_card: "card W\<^sub>\<tau> = 2"
    by (rule geotop_edge_face_witness_card_two[OF hedge he\<tau>])
  have hW\<tau>_eq: "W\<^sub>\<tau> = W"
    by (rule geotop_simplex_vertices_unique[OF heW\<tau> heW])
  have hW_sub_V\<tau>: "W \<subseteq> V\<^sub>\<tau>"
    using hW\<tau>_sub hW\<tau>_eq by (by100 simp)
  have hV\<tau>_card: "card V\<^sub>\<tau> = 3"
  proof -
    obtain V2 m where hV2_fin: "finite V2"
      and hV2_card: "card V2 = 2 + 1"
      and h2_le_m: "2 \<le> m"
      and hgp_V2: "geotop_general_position V2 m"
      and h\<tau>_eq_V2: "\<tau> = geotop_convex_hull V2"
      using h\<tau>2 unfolding geotop_simplex_dim_def by (by100 blast)
    have h\<tau>V2: "geotop_simplex_vertices \<tau> V2"
      unfolding geotop_simplex_vertices_def
      using hV2_fin hV2_card h2_le_m hgp_V2 h\<tau>_eq_V2 by (by100 blast)
    have hV_eq: "V\<^sub>\<tau> = V2"
      by (rule geotop_simplex_vertices_unique[OF h\<tau>V h\<tau>V2])
    show ?thesis
      using hV_eq hV2_card by (by100 simp)
  qed
  have hV\<tau>_fin: "finite V\<^sub>\<tau>"
    using h\<tau>V unfolding geotop_simplex_vertices_def by (by100 blast)
  obtain d where hdV: "d \<in> V\<^sub>\<tau>" and hd_not_W: "d \<notin> W"
  proof -
    have "W \<noteq> V\<^sub>\<tau>"
    proof
      assume hWV: "W = V\<^sub>\<tau>"
      show False
        using hW_card hV\<tau>_card hWV by (by100 arith)
    qed
    then obtain d where "d \<in> V\<^sub>\<tau>" and "d \<notin> W"
      using hW_sub_V\<tau> by (by100 blast)
    thus ?thesis
      by (rule that)
  qed
  have hd_not_ab: "d \<notin> {a, b}"
    using hd_not_W hW_eq by (by100 simp)
  have h\<tau>V_ab: "geotop_simplex_vertices \<tau> {a, b, d}"
  proof -
    have haV: "a \<in> V\<^sub>\<tau>"
      using hW_eq hW_sub_V\<tau> by (by100 blast)
    have hbV: "b \<in> V\<^sub>\<tau>"
      using hW_eq hW_sub_V\<tau> by (by100 blast)
    have had: "a \<noteq> d"
      using hd_not_ab by (by100 blast)
    have hbd: "b \<noteq> d"
      using hd_not_ab by (by100 blast)
    have hV_eq: "V\<^sub>\<tau> = {a, b, d}"
      by (rule geotop_2simplex_vertices_three_eq_dev34
          [OF h\<tau>2 h\<tau>V haV hbV hdV hab had hbd])
    show ?thesis
      using h\<tau>V hV_eq by (by100 simp)
  qed
  have hcd: "c \<noteq> d"
  proof
    assume hcd_eq: "c = d"
    have h\<sigma>_eq: "\<sigma> = geotop_convex_hull {a, b, c}"
      using h\<sigma>V_ab unfolding geotop_simplex_vertices_def by (by100 blast)
    have h\<tau>_eq: "\<tau> = geotop_convex_hull {a, b, d}"
      using h\<tau>V_ab unfolding geotop_simplex_vertices_def by (by100 blast)
    have "\<sigma> = \<tau>"
      using h\<sigma>_eq h\<tau>_eq hcd_eq by (by100 simp)
    thus False
      using h\<sigma>\<tau> by (by100 blast)
  qed
  show ?thesis
    by (rule that[OF hab hc_not_ab hd_not_ab hcd he_eq_ab h\<sigma>V_ab h\<tau>V_ab])
qed

lemma geotop_two_2simplex_shared_edge_vertices_affine_obtain_dev34:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  assumes hedge: "geotop_is_edge e"
  obtains a b c d where
    "a \<noteq> b"
    "c \<notin> {a, b}"
    "d \<notin> {a, b}"
    "c \<noteq> d"
    "e = geotop_convex_hull {a, b}"
    "geotop_simplex_vertices \<sigma> {a, b, c}"
    "geotop_simplex_vertices \<tau> {a, b, d}"
    "c \<notin> affine hull {a, b}"
    "d \<notin> affine hull {a, b}"
  (**
    The same shared-edge vertex form, with the two opposite vertices certified
    off the affine line of the common edge. **)
proof -
  obtain a b c d where hab: "a \<noteq> b"
    and hc_not_ab: "c \<notin> {a, b}"
    and hd_not_ab: "d \<notin> {a, b}"
    and hcd: "c \<noteq> d"
    and he_eq: "e = geotop_convex_hull {a, b}"
    and h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
    and h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
    by (rule geotop_two_2simplex_shared_edge_vertices_obtain_dev34
        [OF h\<sigma>2 h\<tau>2 h\<sigma>\<tau> he\<sigma> he\<tau> hedge])
  have hc_aff: "c \<notin> affine hull {a, b}"
    by (rule geotop_2simplex_opposite_vertex_notin_edge_affine_hull_dev34
        [OF h\<sigma>V hc_not_ab])
  have hd_aff: "d \<notin> affine hull {a, b}"
    by (rule geotop_2simplex_opposite_vertex_notin_edge_affine_hull_dev34
        [OF h\<tau>V hd_not_ab])
  show ?thesis
    by (rule that[OF hab hc_not_ab hd_not_ab hcd he_eq h\<sigma>V h\<tau>V hc_aff hd_aff])
qed

lemma geotop_edge_vertices_affine_hull_normal_form_dev34:
  fixes e :: "(real^2) set"
  assumes hedge: "geotop_is_edge e"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  shows "\<exists>n d. n \<noteq> 0 \<and> affine hull {a, b} = {x. n \<bullet> x = d}"
  (**
    The affine hull of the shared edge is a genuine line in the plane, written
    in normal form for the subsequent half-plane argument. **)
proof -
  have he1: "geotop_simplex_dim e 1"
    using hedge unfolding geotop_is_edge_def by (by100 simp)
  have hhyper: "geotop_hyperplane_dim (affine hull e) 1"
    by (rule geotop_simplex_dim_imp_hyperplane_dim[OF he1])
  obtain n d where hn: "n \<noteq> 0"
    and hline_e: "affine hull e = {x. n \<bullet> x = d}"
    using geotop_hyperplane_dim_1_R2_normal_form[OF hhyper] by (by100 blast)
  have he_HOL: "e = convex hull {a, b}"
    using he_eq geotop_convex_hull_eq_HOL by (by100 simp)
  have haff_eq: "affine hull e = affine hull {a, b}"
    using he_HOL affine_hull_convex_hull[of "{a, b}"] by (by100 simp)
  have hline_ab: "affine hull {a, b} = {x. n \<bullet> x = d}"
    using haff_eq hline_e by (by100 simp)
  show ?thesis
    using hn hline_ab by (by100 blast)
qed

lemma geotop_two_2simplex_shared_edge_vertices_normal_obtain_dev34:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  assumes hedge: "geotop_is_edge e"
  obtains a b c d n r where
    "a \<noteq> b"
    "c \<notin> {a, b}"
    "d \<notin> {a, b}"
    "c \<noteq> d"
    "e = geotop_convex_hull {a, b}"
    "geotop_simplex_vertices \<sigma> {a, b, c}"
    "geotop_simplex_vertices \<tau> {a, b, d}"
    "n \<noteq> 0"
    "affine hull {a, b} = {x. n \<bullet> x = r}"
    "n \<bullet> c \<noteq> r"
    "n \<bullet> d \<noteq> r"
  (**
    Normal-coordinate version of the shared-edge picture: the two opposite
    vertices are strictly off the line through the common edge. **)
proof -
  obtain a b c d where hab: "a \<noteq> b"
    and hc_not_ab: "c \<notin> {a, b}"
    and hd_not_ab: "d \<notin> {a, b}"
    and hcd: "c \<noteq> d"
    and he_eq: "e = geotop_convex_hull {a, b}"
    and h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
    and h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
    and hc_aff: "c \<notin> affine hull {a, b}"
    and hd_aff: "d \<notin> affine hull {a, b}"
    by (rule geotop_two_2simplex_shared_edge_vertices_affine_obtain_dev34
        [OF h\<sigma>2 h\<tau>2 h\<sigma>\<tau> he\<sigma> he\<tau> hedge])
  obtain n r where hn: "n \<noteq> 0"
    and hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
    using geotop_edge_vertices_affine_hull_normal_form_dev34[OF hedge he_eq]
    by (by100 blast)
  have hc_ne: "n \<bullet> c \<noteq> r"
  proof
    assume hc_eq: "n \<bullet> c = r"
    have "c \<in> affine hull {a, b}"
      using hline hc_eq by (by100 simp)
    thus False
      using hc_aff by (by100 blast)
  qed
  have hd_ne: "n \<bullet> d \<noteq> r"
  proof
    assume hd_eq: "n \<bullet> d = r"
    have "d \<in> affine hull {a, b}"
      using hline hd_eq by (by100 simp)
    thus False
      using hd_aff by (by100 blast)
  qed
  show ?thesis
    by (rule that[OF hab hc_not_ab hd_not_ab hcd he_eq h\<sigma>V h\<tau>V
          hn hline hc_ne hd_ne])
qed

lemma geotop_2simplex_vertices_HOL_interior_explicit_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  shows "interior \<sigma> =
    {v. \<exists>x y z. 0 < x \<and> 0 < y \<and> 0 < z \<and> x + y + z = 1
      \<and> x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = v}"
  (**
    HOL positive-barycentric description of the interior of a nondegenerate
    2-simplex, specialized to the vertex triples used in the shared-edge
    local model. **)
proof -
  have h\<sigma>_geo: "\<sigma> = geotop_convex_hull {a, b, c}"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have h\<sigma>_HOL: "\<sigma> = convex hull {a, b, c}"
    using h\<sigma>_geo geotop_convex_hull_eq_HOL[of "{a, b, c}"] by (by100 simp)
  have h_ai: "\<not> affine_dependent {a, b, c}"
    by (rule geotop_general_position_imp_aff_indep[OF h\<sigma>V])
  have hac: "a \<noteq> c"
    using hc_not_ab by (by100 blast)
  have hbc: "b \<noteq> c"
    using hc_not_ab by (by100 blast)
  have hcol_eq:
    "collinear {a, b, c} =
      (a = b \<or> a = c \<or> b = c \<or> affine_dependent {a, b, c})"
    by (rule collinear_3_eq_affine_dependent)
  have hnoncol: "\<not> collinear {a, b, c}"
    using h_ai hab hac hbc hcol_eq by (by100 simp)
  have hdim: "DIM(real^2) = 2"
    by (by100 simp)
  have hinter:
    "interior (convex hull {a, b, c}) =
      {v. \<exists>x y z. 0 < x \<and> 0 < y \<and> 0 < z \<and> x + y + z = 1
        \<and> x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = v}"
    by (rule interior_convex_hull_3_minimal[OF hnoncol hdim])
  show ?thesis
    using h\<sigma>_HOL hinter by (by100 simp)
qed

lemma geotop_2simplex_positive_bary_in_HOL_interior_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hx: "0 < x"
  assumes hy: "0 < y"
  assumes hz: "0 < z"
  assumes hsum: "x + y + z = 1"
  assumes hp: "p = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
  shows "p \<in> interior \<sigma>"
  (**
    Direct membership form of the positive-barycentric interior
    characterization. **)
proof -
  have hinter:
    "interior \<sigma> =
      {v. \<exists>x y z. 0 < x \<and> 0 < y \<and> 0 < z \<and> x + y + z = 1
        \<and> x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = v}"
    by (rule geotop_2simplex_vertices_HOL_interior_explicit_dev34
        [OF hab hc_not_ab h\<sigma>V])
  have "p \<in>
      {v. \<exists>x y z. 0 < x \<and> 0 < y \<and> 0 < z \<and> x + y + z = 1
        \<and> x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = v}"
    using hx hy hz hsum hp by (by100 blast)
  thus ?thesis
    using hinter by (by100 simp)
qed

lemma geotop_2simplex_HOL_interior_positive_side_of_edge_line_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c > r"
  assumes hp: "p \<in> interior \<sigma>"
  shows "n \<bullet> p > r"
  (**
    Positive-side half-plane form of the triangle interior: interior points of
    the triangle lie on the same strict side of the edge line as the opposite
    vertex. **)
proof -
  have ha_aff: "a \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have hb_aff: "b \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have ha_line: "n \<bullet> a = r"
    using hline ha_aff by (by100 simp)
  have hb_line: "n \<bullet> b = r"
    using hline hb_aff by (by100 simp)
  have hinter:
    "interior \<sigma> =
      {v. \<exists>x y z. 0 < x \<and> 0 < y \<and> 0 < z \<and> x + y + z = 1
        \<and> x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = v}"
    by (rule geotop_2simplex_vertices_HOL_interior_explicit_dev34
        [OF hab hc_not_ab h\<sigma>V])
  obtain x y z where hx: "0 < x"
    and hy: "0 < y"
    and hz: "0 < z"
    and hsum: "x + y + z = 1"
    and hp_eq: "x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = p"
    using hp hinter by (by100 blast)
  have hp_eq': "p = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
    using hp_eq by (by100 simp)
  have hp_dot: "n \<bullet> p = x * r + y * r + z * (n \<bullet> c)"
  proof -
    have "n \<bullet> p = n \<bullet> (x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c)"
      using hp_eq' by (by100 simp)
    also have "\<dots> = n \<bullet> (x *\<^sub>R a) + n \<bullet> (y *\<^sub>R b) + n \<bullet> (z *\<^sub>R c)"
      by (simp add: inner_add_right)
    also have "\<dots> = x * (n \<bullet> a) + y * (n \<bullet> b) + z * (n \<bullet> c)"
      by (simp add: inner_scaleR_right)
    also have "\<dots> = x * r + y * r + z * (n \<bullet> c)"
      using ha_line hb_line by (by100 simp)
    finally show ?thesis .
  qed
  have hsum_r: "x * r + y * r + z * r = r"
  proof -
    have "r * (x + y + z) = r"
      using hsum by (by100 simp)
    thus ?thesis
      by (simp add: algebra_simps)
  qed
  have "n \<bullet> p - r = z * (n \<bullet> c - r)"
  proof -
    have "n \<bullet> p - r =
        (x * r + y * r + z * (n \<bullet> c)) - (x * r + y * r + z * r)"
      using hp_dot hsum_r by (by100 linarith)
    also have "\<dots> = z * (n \<bullet> c - r)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  moreover have "0 < n \<bullet> c - r"
    using hc_side by (by100 linarith)
  hence "0 < z * (n \<bullet> c - r)"
    by (rule mult_pos_pos[OF hz])
  ultimately have "0 < n \<bullet> p - r"
    by (by100 linarith)
  thus ?thesis
    by (by100 linarith)
qed

lemma geotop_2simplex_HOL_interior_negative_side_of_edge_line_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c < r"
  assumes hp: "p \<in> interior \<sigma>"
  shows "n \<bullet> p < r"
  (**
    Negative-side half-plane form of the triangle interior, symmetric to the
    positive-side version. **)
proof -
  have ha_aff: "a \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have hb_aff: "b \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have ha_line: "n \<bullet> a = r"
    using hline ha_aff by (by100 simp)
  have hb_line: "n \<bullet> b = r"
    using hline hb_aff by (by100 simp)
  have hinter:
    "interior \<sigma> =
      {v. \<exists>x y z. 0 < x \<and> 0 < y \<and> 0 < z \<and> x + y + z = 1
        \<and> x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = v}"
    by (rule geotop_2simplex_vertices_HOL_interior_explicit_dev34
        [OF hab hc_not_ab h\<sigma>V])
  obtain x y z where hx: "0 < x"
    and hy: "0 < y"
    and hz: "0 < z"
    and hsum: "x + y + z = 1"
    and hp_eq: "x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = p"
    using hp hinter by (by100 blast)
  have hp_eq': "p = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
    using hp_eq by (by100 simp)
  have hp_dot: "n \<bullet> p = x * r + y * r + z * (n \<bullet> c)"
  proof -
    have "n \<bullet> p = n \<bullet> (x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c)"
      using hp_eq' by (by100 simp)
    also have "\<dots> = n \<bullet> (x *\<^sub>R a) + n \<bullet> (y *\<^sub>R b) + n \<bullet> (z *\<^sub>R c)"
      by (simp add: inner_add_right)
    also have "\<dots> = x * (n \<bullet> a) + y * (n \<bullet> b) + z * (n \<bullet> c)"
      by (simp add: inner_scaleR_right)
    also have "\<dots> = x * r + y * r + z * (n \<bullet> c)"
      using ha_line hb_line by (by100 simp)
    finally show ?thesis .
  qed
  have hsum_r: "x * r + y * r + z * r = r"
  proof -
    have "r * (x + y + z) = r"
      using hsum by (by100 simp)
    thus ?thesis
      by (simp add: algebra_simps)
  qed
  have "n \<bullet> p - r = z * (n \<bullet> c - r)"
  proof -
    have "n \<bullet> p - r =
        (x * r + y * r + z * (n \<bullet> c)) - (x * r + y * r + z * r)"
      using hp_dot hsum_r by (by100 linarith)
    also have "\<dots> = z * (n \<bullet> c - r)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  moreover have "n \<bullet> c - r < 0"
    using hc_side by (by100 linarith)
  hence "z * (n \<bullet> c - r) < 0"
    by (rule mult_pos_neg[OF hz])
  ultimately have "n \<bullet> p - r < 0"
    by (by100 linarith)
  thus ?thesis
    by (by100 linarith)
qed

lemma geotop_2simplex_HOL_interior_subset_positive_side_of_edge_line_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c > r"
  shows "interior \<sigma> \<subseteq> {p. n \<bullet> p > r}"
  (**
    Set-form positive half-plane containment for the shared-edge triangle
    interior. **)
proof
  fix p
  assume hp: "p \<in> interior \<sigma>"
  have "n \<bullet> p > r"
    by (rule geotop_2simplex_HOL_interior_positive_side_of_edge_line_dev34
        [OF hab hc_not_ab h\<sigma>V hline hc_side hp])
  thus "p \<in> {p. n \<bullet> p > r}"
    by (by100 simp)
qed

lemma geotop_2simplex_HOL_interior_subset_negative_side_of_edge_line_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c < r"
  shows "interior \<sigma> \<subseteq> {p. n \<bullet> p < r}"
  (**
    Set-form negative half-plane containment for the shared-edge triangle
    interior. **)
proof
  fix p
  assume hp: "p \<in> interior \<sigma>"
  have "n \<bullet> p < r"
    by (rule geotop_2simplex_HOL_interior_negative_side_of_edge_line_dev34
        [OF hab hc_not_ab h\<sigma>V hline hc_side hp])
  thus "p \<in> {p. n \<bullet> p < r}"
    by (by100 simp)
qed

lemma geotop_two_2simplex_shared_edge_vertices_side_obtain_dev34:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  assumes hedge: "geotop_is_edge e"
  obtains a b c d n r where
    "a \<noteq> b"
    "c \<notin> {a, b}"
    "d \<notin> {a, b}"
    "c \<noteq> d"
    "e = geotop_convex_hull {a, b}"
    "geotop_simplex_vertices \<sigma> {a, b, c}"
    "geotop_simplex_vertices \<tau> {a, b, d}"
    "n \<noteq> 0"
    "affine hull {a, b} = {x. n \<bullet> x = r}"
    "n \<bullet> c \<noteq> r"
    "n \<bullet> d \<noteq> r"
    "n \<bullet> c > r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p > r}"
    "n \<bullet> c < r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p < r}"
    "n \<bullet> d > r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p > r}"
    "n \<bullet> d < r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p < r}"
  (**
    Shared-edge normal-coordinate package with the half-plane containments for
    the two triangle interiors. **)
proof -
  obtain a b c d n r where hab: "a \<noteq> b"
    and hc_not_ab: "c \<notin> {a, b}"
    and hd_not_ab: "d \<notin> {a, b}"
    and hcd: "c \<noteq> d"
    and he_eq: "e = geotop_convex_hull {a, b}"
    and h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
    and h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
    and hn: "n \<noteq> 0"
    and hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
    and hc_ne: "n \<bullet> c \<noteq> r"
    and hd_ne: "n \<bullet> d \<noteq> r"
    by (rule geotop_two_2simplex_shared_edge_vertices_normal_obtain_dev34
        [OF h\<sigma>2 h\<tau>2 h\<sigma>\<tau> he\<sigma> he\<tau> hedge])
  have h\<sigma>_pos: "n \<bullet> c > r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p > r}"
    by (rule geotop_2simplex_HOL_interior_subset_positive_side_of_edge_line_dev34
        [OF hab hc_not_ab h\<sigma>V hline])
  have h\<sigma>_neg: "n \<bullet> c < r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p < r}"
    by (rule geotop_2simplex_HOL_interior_subset_negative_side_of_edge_line_dev34
        [OF hab hc_not_ab h\<sigma>V hline])
  have h\<tau>_pos: "n \<bullet> d > r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p > r}"
    by (rule geotop_2simplex_HOL_interior_subset_positive_side_of_edge_line_dev34
        [OF hab hd_not_ab h\<tau>V hline])
  have h\<tau>_neg: "n \<bullet> d < r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p < r}"
    by (rule geotop_2simplex_HOL_interior_subset_negative_side_of_edge_line_dev34
        [OF hab hd_not_ab h\<tau>V hline])
  show ?thesis
    by (rule that[OF hab hc_not_ab hd_not_ab hcd he_eq h\<sigma>V h\<tau>V
          hn hline hc_ne hd_ne h\<sigma>_pos h\<sigma>_neg h\<tau>_pos h\<tau>_neg])
qed

lemma geotop_edge_vertices_subset_affine_hull_dev34:
  fixes e :: "(real^2) set"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  shows "e \<subseteq> affine hull {a, b}"
  (**
    Edge-line containment used in the shared-edge local model: the common edge
    itself lies in the affine line through its two vertices. **)
proof -
  have he_HOL: "e = convex hull {a, b}"
    using he_eq geotop_convex_hull_eq_HOL by (by100 simp)
  have "convex hull {a, b} \<subseteq> affine hull {a, b}"
    by (rule convex_hull_subset_affine_hull)
  thus ?thesis
    using he_HOL by (by100 simp)
qed

lemma geotop_edge_vertices_subset_normal_line_dev34:
  fixes e :: "(real^2) set"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  shows "e \<subseteq> {x. n \<bullet> x = r}"
  (**
    Normal-form version of edge-line containment for the half-plane
    contradiction in the two-triangle edge model. **)
proof -
  have he_aff: "e \<subseteq> affine hull {a, b}"
    by (rule geotop_edge_vertices_subset_affine_hull_dev34[OF he_eq])
  show ?thesis
    using he_aff hline by (by100 simp)
qed

lemma geotop_2simplex_HOL_interior_eq_rel_interior_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  shows "interior \<sigma> = rel_interior \<sigma>"
  (**
    A 2-simplex in the plane has full affine dimension, so its ordinary
    Euclidean interior is its relative interior. **)
proof -
  have hhyper: "geotop_hyperplane_dim (affine hull \<sigma>) 2"
    by (rule geotop_simplex_dim_imp_hyperplane_dim[OF h\<sigma>2])
  have hdim\<sigma>: "aff_dim \<sigma> = 2"
    using geotop_hyperplane_dim_imp_affine_aff_dim[OF hhyper] by (by100 simp)
  have hdim_UNIV: "aff_dim \<sigma> = int (DIM(real^2))"
    using hdim\<sigma> by (by100 simp)
  have hrel_eq_int: "rel_interior \<sigma> = interior \<sigma>"
    by (rule interior_rel_interior[OF hdim_UNIV])
  show ?thesis
    using hrel_eq_int by (by100 simp)
qed

lemma geotop_complex_distinct_2simplex_HOL_interiors_disjoint_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  shows "interior \<sigma> \<inter> interior \<tau> = {}"
  (**
    Complex disjointness in the ordinary plane-interior form needed by the
    shared-edge half-plane contradiction. **)
proof -
  have h\<sigma>_int: "interior \<sigma> = rel_interior \<sigma>"
    by (rule geotop_2simplex_HOL_interior_eq_rel_interior_dev34[OF h\<sigma>2])
  have h\<tau>_int: "interior \<tau> = rel_interior \<tau>"
    by (rule geotop_2simplex_HOL_interior_eq_rel_interior_dev34[OF h\<tau>2])
  have hrel_disj: "rel_interior \<sigma> \<inter> rel_interior \<tau> = {}"
    by (rule geotop_complex_rel_interior_disjoint_distinct[OF hK h\<sigma>K h\<tau>K h\<sigma>\<tau>])
  show ?thesis
    using h\<sigma>_int h\<tau>_int hrel_disj by (by100 simp)
qed

lemma geotop_2simplex_vertices_affine_hull_UNIV_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  shows "affine hull {a, b, c} = UNIV"
  (**
    Noncollinear vertices of a GeoTop 2-simplex affinely span the whole
    ambient plane. **)
proof -
  have h_ai: "\<not> affine_dependent {a, b, c}"
    by (rule geotop_general_position_imp_aff_indep[OF h\<sigma>V])
  have hac: "a \<noteq> c"
    using hc_not_ab by (by100 blast)
  have hbc: "b \<noteq> c"
    using hc_not_ab by (by100 blast)
  have hcard: "card {a, b, c} = 3"
    using hab hac hbc by (by100 simp)
  have hdim: "aff_dim {a, b, c} = 2"
    using h_ai hcard affine_independent_iff_card[of "{a, b, c}"] by (by100 simp)
  have hdim_UNIV: "aff_dim {a, b, c} = DIM(real^2)"
    using hdim by (by100 simp)
  show ?thesis
    using aff_dim_eq_full[of "{a, b, c}"] hdim_UNIV by (by100 simp)
qed

lemma geotop_2simplex_vertices_affine_coordinates_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  shows "\<exists>x y z. x + y + z = 1
      \<and> d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
  (**
    Affine-coordinate existence for the same-side overlap construction. **)
proof -
  have hUNIV: "affine hull {a, b, c} = UNIV"
    by (rule geotop_2simplex_vertices_affine_hull_UNIV_dev34
        [OF hab hc_not_ab h\<sigma>V])
  have hd_aff: "d \<in> affine hull {a, b, c}"
    using hUNIV by (by100 simp)
  obtain x y z where hsum: "x + y + z = 1"
    and hd: "d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
    using hd_aff affine_hull_3[of a b c] by (by100 blast)
  show ?thesis
    using hsum hd by (by100 blast)
qed

lemma geotop_2simplex_positive_side_affine_coordinate_positive_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c > r"
  assumes hd_side: "n \<bullet> d > r"
  shows "\<exists>x y z. x + y + z = 1
      \<and> d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c
      \<and> 0 < z"
  (**
    Same positive side of the edge line means the affine coordinate at the
    opposite vertex \<open>c\<close> is positive. **)
proof -
  have ha_aff: "a \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have hb_aff: "b \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have ha_line: "n \<bullet> a = r"
    using hline ha_aff by (by100 simp)
  have hb_line: "n \<bullet> b = r"
    using hline hb_aff by (by100 simp)
  obtain x y z where hsum: "x + y + z = 1"
    and hd: "d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
    using geotop_2simplex_vertices_affine_coordinates_dev34
      [OF hab hc_not_ab h\<sigma>V, of d]
    by (by100 blast)
  have hd_dot: "n \<bullet> d = x * r + y * r + z * (n \<bullet> c)"
  proof -
    have "n \<bullet> d = n \<bullet> (x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c)"
      using hd by (by100 simp)
    also have "\<dots> = n \<bullet> (x *\<^sub>R a) + n \<bullet> (y *\<^sub>R b) + n \<bullet> (z *\<^sub>R c)"
      by (simp add: inner_add_right)
    also have "\<dots> = x * (n \<bullet> a) + y * (n \<bullet> b) + z * (n \<bullet> c)"
      by (simp add: inner_scaleR_right)
    also have "\<dots> = x * r + y * r + z * (n \<bullet> c)"
      using ha_line hb_line by (by100 simp)
    finally show ?thesis .
  qed
  have hsum_r: "x * r + y * r + z * r = r"
  proof -
    have "r * (x + y + z) = r"
      using hsum by (by100 simp)
    thus ?thesis
      by (simp add: algebra_simps)
  qed
  have hdiff: "n \<bullet> d - r = z * (n \<bullet> c - r)"
  proof -
    have "n \<bullet> d - r =
        (x * r + y * r + z * (n \<bullet> c)) - (x * r + y * r + z * r)"
      using hd_dot hsum_r by (by100 linarith)
    also have "\<dots> = z * (n \<bullet> c - r)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have hprod_pos: "0 < z * (n \<bullet> c - r)"
    using hdiff hd_side by (by100 linarith)
  have hden_pos: "0 < n \<bullet> c - r"
    using hc_side by (by100 linarith)
  have hz: "0 < z"
    using hprod_pos hden_pos by (simp add: zero_less_mult_iff)
  show ?thesis
    using hsum hd hz by (by100 blast)
qed

lemma geotop_2simplex_negative_side_affine_coordinate_positive_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c < r"
  assumes hd_side: "n \<bullet> d < r"
  shows "\<exists>x y z. x + y + z = 1
      \<and> d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c
      \<and> 0 < z"
  (**
    Negative-side version, obtained by reversing the normal vector. **)
proof -
  have hline_neg: "affine hull {a, b} = {x. (-n) \<bullet> x = -r}"
    using hline by (simp add: set_eq_iff)
  have hc_pos: "(-n) \<bullet> c > -r"
    using hc_side by (by100 simp)
  have hd_pos: "(-n) \<bullet> d > -r"
    using hd_side by (by100 simp)
  show ?thesis
    by (rule geotop_2simplex_positive_side_affine_coordinate_positive_dev34
        [OF hab hc_not_ab h\<sigma>V hline_neg hc_pos hd_pos])
qed

lemma geotop_real_positive_overlap_parameter_dev34:
  fixes x y z :: real
  assumes hz: "0 < z"
  obtains s where
    "0 < s"
    "s < 1"
    "0 < (1 - s) / 2 + s * x"
    "0 < (1 - s) / 2 + s * y"
    "0 < s * z"
  (**
    Real parameter choice for the same-side overlap construction: move a small
    positive distance from the edge midpoint toward the second opposite vertex,
    while keeping positive barycentric coordinates in the first triangle. **)
proof -
  define bx where "bx = (if x < 1 / 2 then (1 / 2) / (1 / 2 - x) else 1)"
  define byy where "byy = (if y < 1 / 2 then (1 / 2) / (1 / 2 - y) else 1)"
  have hbx_pos: "0 < bx"
  proof (cases "x < 1 / 2")
    case True
    have "0 < 1 / 2 - x"
      using True by (by100 linarith)
    hence "0 < (1 / 2) / (1 / 2 - x)"
      by (simp add: divide_pos_pos)
    thus ?thesis
      using True bx_def by (by100 simp)
  next
    case False
    show ?thesis
      using False bx_def by (by100 simp)
  qed
  have hby_pos: "0 < byy"
  proof (cases "y < 1 / 2")
    case True
    have "0 < 1 / 2 - y"
      using True by (by100 linarith)
    hence "0 < (1 / 2) / (1 / 2 - y)"
      by (simp add: divide_pos_pos)
    thus ?thesis
      using True byy_def by (by100 simp)
  next
    case False
    show ?thesis
      using False byy_def by (by100 simp)
  qed
  obtain t where ht0: "0 < t" and htbx: "t < bx" and ht1: "t < 1"
    using field_lbound_gt_zero[OF hbx_pos zero_less_one] by (by100 blast)
  obtain s where hs0: "0 < s" and hst: "s < t" and hsby: "s < byy"
    using field_lbound_gt_zero[OF ht0 hby_pos] by (by100 blast)
  have hs1: "s < 1"
    using hst ht1 by (by100 linarith)
  have hsbx: "s < bx"
    using hst htbx by (by100 linarith)
  have hxpos: "0 < (1 - s) / 2 + s * x"
  proof (cases "x < 1 / 2")
    case True
    have hden: "0 < 1 / 2 - x"
      using True by (by100 linarith)
    have hsbound: "s < (1 / 2) / (1 / 2 - x)"
      using hsbx True bx_def by (by100 simp)
    have "s * (1 / 2 - x) < 1 / 2"
      using hsbound hden by (simp add: field_simps)
    hence "0 < 1 / 2 - s * (1 / 2 - x)"
      by (by100 linarith)
    also have "1 / 2 - s * (1 / 2 - x) = (1 - s) / 2 + s * x"
      by (simp add: field_simps algebra_simps)
    finally show ?thesis .
  next
    case False
    have hnonneg: "0 \<le> x - 1 / 2"
      using False by (by100 linarith)
    have hs_nonneg: "0 \<le> s"
      using hs0 by (by100 linarith)
    have "0 \<le> s * (x - 1 / 2)"
      by (rule mult_nonneg_nonneg[OF hs_nonneg hnonneg])
    moreover have "(1 - s) / 2 + s * x = 1 / 2 + s * (x - 1 / 2)"
      by (simp add: field_simps algebra_simps)
    ultimately show ?thesis
      by (by100 linarith)
  qed
  have hypos: "0 < (1 - s) / 2 + s * y"
  proof (cases "y < 1 / 2")
    case True
    have hden: "0 < 1 / 2 - y"
      using True by (by100 linarith)
    have hsbound: "s < (1 / 2) / (1 / 2 - y)"
      using hsby True byy_def by (by100 simp)
    have "s * (1 / 2 - y) < 1 / 2"
      using hsbound hden by (simp add: field_simps)
    hence "0 < 1 / 2 - s * (1 / 2 - y)"
      by (by100 linarith)
    also have "1 / 2 - s * (1 / 2 - y) = (1 - s) / 2 + s * y"
      by (simp add: field_simps algebra_simps)
    finally show ?thesis .
  next
    case False
    have hnonneg: "0 \<le> y - 1 / 2"
      using False by (by100 linarith)
    have hs_nonneg: "0 \<le> s"
      using hs0 by (by100 linarith)
    have "0 \<le> s * (y - 1 / 2)"
      by (rule mult_nonneg_nonneg[OF hs_nonneg hnonneg])
    moreover have "(1 - s) / 2 + s * y = 1 / 2 + s * (y - 1 / 2)"
      by (simp add: field_simps algebra_simps)
    ultimately show ?thesis
      by (by100 linarith)
  qed
  have hsz: "0 < s * z"
    by (rule mult_pos_pos[OF hs0 hz])
  show ?thesis
    by (rule that[OF hs0 hs1 hxpos hypos hsz])
qed

lemma geotop_2simplex_affine_coordinate_HOL_interiors_meet_dev34:
  fixes \<sigma> \<tau> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes hd_not_ab: "d \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
  assumes hsum: "x + y + z = 1"
  assumes hd: "d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
  assumes hz: "0 < z"
  shows "interior \<sigma> \<inter> interior \<tau> \<noteq> {}"
  (**
    Same-side overlap construction in barycentric coordinates: a small segment
    from the edge midpoint toward \<open>d\<close> lies in \<open>\<tau>\<close>'s interior and, after
    substituting the affine coordinates of \<open>d\<close>, also in \<open>\<sigma>\<close>'s interior. **)
proof -
  obtain s where hs0: "0 < s"
    and hs1: "s < 1"
    and hxpos: "0 < (1 - s) / 2 + s * x"
    and hypos: "0 < (1 - s) / 2 + s * y"
    and hsz: "0 < s * z"
    by (rule geotop_real_positive_overlap_parameter_dev34[OF hz])
  define u where "u = (1 - s) / 2"
  define p where "p = u *\<^sub>R a + u *\<^sub>R b + s *\<^sub>R d"
  have hu: "0 < u"
    using hs1 unfolding u_def by (simp add: field_simps)
  have hsum\<tau>: "u + u + s = 1"
    unfolding u_def by (simp add: field_simps)
  have hp\<tau>: "p \<in> interior \<tau>"
    by (rule geotop_2simplex_positive_bary_in_HOL_interior_dev34
        [OF hab hd_not_ab h\<tau>V hu hu hs0 hsum\<tau> p_def])
  have hxpos': "0 < u + s * x"
    using hxpos unfolding u_def by (by100 simp)
  have hypos': "0 < u + s * y"
    using hypos unfolding u_def by (by100 simp)
  have hsum\<sigma>: "(u + s * x) + (u + s * y) + s * z = 1"
  proof -
    have "(u + s * x) + (u + s * y) + s * z = u + u + s * (x + y + z)"
      by (simp add: algebra_simps)
    also have "\<dots> = u + u + s"
      using hsum by (by100 simp)
    also have "\<dots> = 1"
      using hsum\<tau> by (by100 simp)
    finally show ?thesis .
  qed
  have hp_eq\<sigma>:
      "p = (u + s * x) *\<^sub>R a + (u + s * y) *\<^sub>R b + (s * z) *\<^sub>R c"
    unfolding p_def hd by (simp add: algebra_simps scaleR_add_left scaleR_add_right)
  have hp\<sigma>: "p \<in> interior \<sigma>"
    by (rule geotop_2simplex_positive_bary_in_HOL_interior_dev34
        [OF hab hc_not_ab h\<sigma>V hxpos' hypos' hsz hsum\<sigma> hp_eq\<sigma>])
  have "p \<in> interior \<sigma> \<inter> interior \<tau>"
    using hp\<sigma> hp\<tau> by (by100 blast)
  thus ?thesis
    by (by100 blast)
qed

lemma geotop_2simplex_positive_same_side_HOL_interiors_meet_dev34:
  fixes \<sigma> \<tau> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes hd_not_ab: "d \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c > r"
  assumes hd_side: "n \<bullet> d > r"
  shows "interior \<sigma> \<inter> interior \<tau> \<noteq> {}"
  (**
    If both opposite vertices lie on the positive side of the shared-edge line,
    the barycentric overlap construction gives a common interior point. **)
proof -
  obtain x y z where hsum: "x + y + z = 1"
    and hd: "d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
    and hz: "0 < z"
    using geotop_2simplex_positive_side_affine_coordinate_positive_dev34
      [OF hab hc_not_ab h\<sigma>V hline hc_side hd_side]
    by (by100 blast)
  show ?thesis
    by (rule geotop_2simplex_affine_coordinate_HOL_interiors_meet_dev34
        [OF hab hc_not_ab hd_not_ab h\<sigma>V h\<tau>V hsum hd hz])
qed

lemma geotop_2simplex_negative_same_side_HOL_interiors_meet_dev34:
  fixes \<sigma> \<tau> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes hd_not_ab: "d \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c < r"
  assumes hd_side: "n \<bullet> d < r"
  shows "interior \<sigma> \<inter> interior \<tau> \<noteq> {}"
  (**
    Negative-side same-side version, symmetric to the positive-side wrapper. **)
proof -
  obtain x y z where hsum: "x + y + z = 1"
    and hd: "d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
    and hz: "0 < z"
    using geotop_2simplex_negative_side_affine_coordinate_positive_dev34
      [OF hab hc_not_ab h\<sigma>V hline hc_side hd_side]
    by (by100 blast)
  show ?thesis
    by (rule geotop_2simplex_affine_coordinate_HOL_interiors_meet_dev34
        [OF hab hc_not_ab hd_not_ab h\<sigma>V h\<tau>V hsum hd hz])
qed

lemma geotop_complex_two_2simplex_shared_edge_vertices_opposite_sides_dev34:
  fixes K :: "(real^2) set set"
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  assumes hedge: "geotop_is_edge e"
  obtains a b c d n r where
    "a \<noteq> b"
    "c \<notin> {a, b}"
    "d \<notin> {a, b}"
    "c \<noteq> d"
    "e = geotop_convex_hull {a, b}"
    "geotop_simplex_vertices \<sigma> {a, b, c}"
    "geotop_simplex_vertices \<tau> {a, b, d}"
    "n \<noteq> 0"
    "affine hull {a, b} = {x. n \<bullet> x = r}"
    "n \<bullet> c \<noteq> r"
    "n \<bullet> d \<noteq> r"
    "n \<bullet> c > r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p > r}"
    "n \<bullet> c < r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p < r}"
    "n \<bullet> d > r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p > r}"
    "n \<bullet> d < r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p < r}"
    "(n \<bullet> c > r \<and> n \<bullet> d < r) \<or> (n \<bullet> c < r \<and> n \<bullet> d > r)"
  (**
    Same-complex strengthening of the shared-edge side package: if the two
    2-simplexes put their opposite vertices on the same strict side of the
    shared edge line, the previous overlap lemma gives a common HOL-interior
    point, contradicting complex relative-interior disjointness. **)
proof (rule geotop_two_2simplex_shared_edge_vertices_side_obtain_dev34
    [OF h\<sigma>2 h\<tau>2 h\<sigma>\<tau> he\<sigma> he\<tau> hedge])
  fix a b c d n r
  assume hab: "a \<noteq> b"
    and hc_not_ab: "c \<notin> {a, b}"
    and hd_not_ab: "d \<notin> {a, b}"
    and hcd: "c \<noteq> d"
    and he_eq: "e = geotop_convex_hull {a, b}"
    and h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
    and h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
    and hn: "n \<noteq> 0"
    and hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
    and hc_ne: "n \<bullet> c \<noteq> r"
    and hd_ne: "n \<bullet> d \<noteq> r"
    and h\<sigma>_pos: "n \<bullet> c > r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p > r}"
    and h\<sigma>_neg: "n \<bullet> c < r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p < r}"
    and h\<tau>_pos: "n \<bullet> d > r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p > r}"
    and h\<tau>_neg: "n \<bullet> d < r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p < r}"
  have hdisj: "interior \<sigma> \<inter> interior \<tau> = {}"
    by (rule geotop_complex_distinct_2simplex_HOL_interiors_disjoint_dev34
        [OF hK h\<sigma>K h\<tau>K h\<sigma>2 h\<tau>2 h\<sigma>\<tau>])
  have hpos_not: "\<not> (n \<bullet> c > r \<and> n \<bullet> d > r)"
  proof
    assume hsame: "n \<bullet> c > r \<and> n \<bullet> d > r"
    have hc_side: "n \<bullet> c > r"
      using hsame by (by100 blast)
    have hd_side: "n \<bullet> d > r"
      using hsame by (by100 blast)
    have hmeet: "interior \<sigma> \<inter> interior \<tau> \<noteq> {}"
      by (rule geotop_2simplex_positive_same_side_HOL_interiors_meet_dev34
          [OF hab hc_not_ab hd_not_ab h\<sigma>V h\<tau>V hline hc_side hd_side])
    show False
      using hdisj hmeet by (by100 blast)
  qed
  have hneg_not: "\<not> (n \<bullet> c < r \<and> n \<bullet> d < r)"
  proof
    assume hsame: "n \<bullet> c < r \<and> n \<bullet> d < r"
    have hc_side: "n \<bullet> c < r"
      using hsame by (by100 blast)
    have hd_side: "n \<bullet> d < r"
      using hsame by (by100 blast)
    have hmeet: "interior \<sigma> \<inter> interior \<tau> \<noteq> {}"
      by (rule geotop_2simplex_negative_same_side_HOL_interiors_meet_dev34
          [OF hab hc_not_ab hd_not_ab h\<sigma>V h\<tau>V hline hc_side hd_side])
    show False
      using hdisj hmeet by (by100 blast)
  qed
  have hopp: "(n \<bullet> c > r \<and> n \<bullet> d < r) \<or> (n \<bullet> c < r \<and> n \<bullet> d > r)"
  proof -
    have hc_cases: "n \<bullet> c > r \<or> n \<bullet> c < r"
      using hc_ne by (by100 linarith)
    have hd_cases: "n \<bullet> d > r \<or> n \<bullet> d < r"
      using hd_ne by (by100 linarith)
    show ?thesis
      using hc_cases hd_cases hpos_not hneg_not by (by100 blast)
  qed
  show ?thesis
    by (rule that[OF hab hc_not_ab hd_not_ab hcd he_eq h\<sigma>V h\<tau>V
          hn hline hc_ne hd_ne h\<sigma>_pos h\<sigma>_neg h\<tau>_pos h\<tau>_neg hopp])
qed

lemma geotop_complex_no_three_2simplexes_share_edge_dev34:
  fixes K :: "(real^2) set set"
  fixes e \<sigma>1 \<sigma>2 \<sigma>3 :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hedge: "geotop_is_edge e"
  assumes h12: "\<sigma>1 \<noteq> \<sigma>2"
  assumes h23: "\<sigma>2 \<noteq> \<sigma>3"
  assumes h13: "\<sigma>1 \<noteq> \<sigma>3"
  assumes h\<sigma>1K: "\<sigma>1 \<in> K"
  assumes h\<sigma>1dim: "geotop_simplex_dim \<sigma>1 2"
  assumes h\<sigma>1face: "geotop_is_face e \<sigma>1"
  assumes h\<sigma>2K: "\<sigma>2 \<in> K"
  assumes h\<sigma>2dim: "geotop_simplex_dim \<sigma>2 2"
  assumes h\<sigma>2face: "geotop_is_face e \<sigma>2"
  assumes h\<sigma>3K: "\<sigma>3 \<in> K"
  assumes h\<sigma>3dim: "geotop_simplex_dim \<sigma>3 2"
  assumes h\<sigma>3face: "geotop_is_face e \<sigma>3"
  shows False
  (**
    In a planar complex, an edge has at most two incident 2-simplexes.  The
    first two incident triangles occupy opposite sides of the edge line; a
    third opposite vertex must lie on one of those two sides and would then
    force overlapping triangle interiors. **)
proof (rule geotop_complex_two_2simplex_shared_edge_vertices_opposite_sides_dev34
    [OF hK h\<sigma>1K h\<sigma>2K h\<sigma>1dim h\<sigma>2dim h12 h\<sigma>1face h\<sigma>2face hedge])
  fix a b c d n r
  assume hab: "a \<noteq> b"
    and hc_not_ab: "c \<notin> {a, b}"
    and hd_not_ab: "d \<notin> {a, b}"
    and hcd: "c \<noteq> d"
    and he_eq: "e = geotop_convex_hull {a, b}"
    and h\<sigma>1V: "geotop_simplex_vertices \<sigma>1 {a, b, c}"
    and h\<sigma>2V: "geotop_simplex_vertices \<sigma>2 {a, b, d}"
    and hn: "n \<noteq> 0"
    and hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
    and hc_ne: "n \<bullet> c \<noteq> r"
    and hd_ne: "n \<bullet> d \<noteq> r"
    and h\<sigma>1_pos: "n \<bullet> c > r \<Longrightarrow> interior \<sigma>1 \<subseteq> {p. n \<bullet> p > r}"
    and h\<sigma>1_neg: "n \<bullet> c < r \<Longrightarrow> interior \<sigma>1 \<subseteq> {p. n \<bullet> p < r}"
    and h\<sigma>2_pos: "n \<bullet> d > r \<Longrightarrow> interior \<sigma>2 \<subseteq> {p. n \<bullet> p > r}"
    and h\<sigma>2_neg: "n \<bullet> d < r \<Longrightarrow> interior \<sigma>2 \<subseteq> {p. n \<bullet> p < r}"
    and hopp: "(n \<bullet> c > r \<and> n \<bullet> d < r) \<or> (n \<bullet> c < r \<and> n \<bullet> d > r)"
  obtain a3 b3 g where ha3b3: "a3 \<noteq> b3"
    and hg_not_a3b3: "g \<notin> {a3, b3}"
    and he_eq3: "e = geotop_convex_hull {a3, b3}"
    and h\<sigma>3V_raw: "geotop_simplex_vertices \<sigma>3 {a3, b3, g}"
    by (rule geotop_2simplex_edge_face_vertices_prefix[OF h\<sigma>3dim hedge h\<sigma>3face])
  have heV_ab: "geotop_simplex_vertices e {a, b}"
    by (rule geotop_pair_convex_hull_simplex_vertices_prefix[OF hab, folded he_eq])
  have heV_a3b3: "geotop_simplex_vertices e {a3, b3}"
    by (rule geotop_pair_convex_hull_simplex_vertices_prefix[OF ha3b3, folded he_eq3])
  have hab_set: "{a3, b3} = {a, b}"
    by (rule geotop_simplex_vertices_unique[OF heV_a3b3 heV_ab])
  have h\<sigma>3V: "geotop_simplex_vertices \<sigma>3 {a, b, g}"
  proof -
    have "{a3, b3, g} = {a, b, g}"
      using hab_set by (by100 blast)
    thus ?thesis
      using h\<sigma>3V_raw by (by100 simp)
  qed
  have hg_not_ab: "g \<notin> {a, b}"
    using hg_not_a3b3 hab_set by (by100 simp)
  have hg_ne: "n \<bullet> g \<noteq> r"
  proof
    assume hg_line: "n \<bullet> g = r"
    have "g \<in> affine hull {a, b}"
      using hg_line hline by (by100 simp)
    moreover have "g \<notin> affine hull {a, b}"
      by (rule geotop_2simplex_opposite_vertex_notin_edge_affine_hull_dev34
          [OF h\<sigma>3V hg_not_ab])
    ultimately show False
      by (by100 blast)
  qed
  have hdisj13: "interior \<sigma>1 \<inter> interior \<sigma>3 = {}"
    by (rule geotop_complex_distinct_2simplex_HOL_interiors_disjoint_dev34
        [OF hK h\<sigma>1K h\<sigma>3K h\<sigma>1dim h\<sigma>3dim h13])
  have hdisj23: "interior \<sigma>2 \<inter> interior \<sigma>3 = {}"
    by (rule geotop_complex_distinct_2simplex_HOL_interiors_disjoint_dev34
        [OF hK h\<sigma>2K h\<sigma>3K h\<sigma>2dim h\<sigma>3dim h23])
  consider (cpos_dneg) "n \<bullet> c > r" "n \<bullet> d < r"
    | (cneg_dpos) "n \<bullet> c < r" "n \<bullet> d > r"
    using hopp by (by100 blast)
  then show False
  proof cases
    case cpos_dneg
    have hg_cases: "n \<bullet> g > r \<or> n \<bullet> g < r"
      using hg_ne by (by100 linarith)
    then show False
    proof
      assume hgpos: "n \<bullet> g > r"
      have hmeet: "interior \<sigma>1 \<inter> interior \<sigma>3 \<noteq> {}"
        by (rule geotop_2simplex_positive_same_side_HOL_interiors_meet_dev34
            [OF hab hc_not_ab hg_not_ab h\<sigma>1V h\<sigma>3V hline cpos_dneg(1) hgpos])
      show False using hdisj13 hmeet by (by100 blast)
    next
      assume hgneg: "n \<bullet> g < r"
      have hmeet: "interior \<sigma>2 \<inter> interior \<sigma>3 \<noteq> {}"
        by (rule geotop_2simplex_negative_same_side_HOL_interiors_meet_dev34
            [OF hab hd_not_ab hg_not_ab h\<sigma>2V h\<sigma>3V hline cpos_dneg(2) hgneg])
      show False using hdisj23 hmeet by (by100 blast)
    qed
  next
    case cneg_dpos
    have hg_cases: "n \<bullet> g > r \<or> n \<bullet> g < r"
      using hg_ne by (by100 linarith)
    then show False
    proof
      assume hgpos: "n \<bullet> g > r"
      have hmeet: "interior \<sigma>2 \<inter> interior \<sigma>3 \<noteq> {}"
        by (rule geotop_2simplex_positive_same_side_HOL_interiors_meet_dev34
            [OF hab hd_not_ab hg_not_ab h\<sigma>2V h\<sigma>3V hline cneg_dpos(2) hgpos])
      show False using hdisj23 hmeet by (by100 blast)
    next
      assume hgneg: "n \<bullet> g < r"
      have hmeet: "interior \<sigma>1 \<inter> interior \<sigma>3 \<noteq> {}"
        by (rule geotop_2simplex_negative_same_side_HOL_interiors_meet_dev34
            [OF hab hc_not_ab hg_not_ab h\<sigma>1V h\<sigma>3V hline cneg_dpos(1) hgneg])
      show False using hdisj13 hmeet by (by100 blast)
    qed
  qed
qed

lemma geotop_edge_rel_interior_parameter_dev34:
  fixes e :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes hp: "p \<in> rel_interior e"
  obtains t where "0 < t" "t < 1" "p = (1 - t) *\<^sub>R a + t *\<^sub>R b"
  (**
    Edge-relative-interior points are exactly open-segment points, recorded in
    the affine parameter form needed for the local diamond construction. **)
proof -
  have he_HOL: "e = closed_segment a b"
    using he_eq geotop_convex_hull_eq_HOL[of "{a, b}"] segment_convex_hull[of a b]
    by (by100 simp)
  have hrel: "rel_interior e = open_segment a b"
    using he_HOL hab rel_interior_closed_segment[of a b] by (by100 simp)
  have hp_open: "p \<in> open_segment a b"
    using hp hrel by (by100 simp)
  obtain t where ht0: "0 < t" and ht1: "t < 1"
    and hp_eq: "p = (1 - t) *\<^sub>R a + t *\<^sub>R b"
    using hp_open unfolding in_segment by (by100 auto)
  show ?thesis
    by (rule that[OF ht0 ht1 hp_eq])
qed

lemma geotop_edge_rel_interior_small_subsegment_dev34:
  fixes e :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes hp: "p \<in> rel_interior e"
  obtains u where
    "0 < u"
    "p - u *\<^sub>R (b - a) \<in> rel_interior e"
    "p + u *\<^sub>R (b - a) \<in> rel_interior e"
  (**
    Edge-relative-interior points contain a small open subsegment in the edge
    direction.  This is the horizontal base of the local diamond around a
    shared-edge point. **)
proof -
  obtain t where ht0: "0 < t" and ht1: "t < 1"
    and hp_eq: "p = (1 - t) *\<^sub>R a + t *\<^sub>R b"
    by (rule geotop_edge_rel_interior_parameter_dev34[OF hab he_eq hp])
  have h1mt: "0 < 1 - t"
    using ht1 by (by100 linarith)
  obtain u where hu0: "0 < u" and hut: "u < t" and hu1mt: "u < 1 - t"
    using field_lbound_gt_zero[OF ht0 h1mt] by (by100 blast)
  have he_HOL: "e = closed_segment a b"
    using he_eq geotop_convex_hull_eq_HOL[of "{a, b}"] segment_convex_hull[of a b]
    by (by100 simp)
  have hrel: "rel_interior e = open_segment a b"
    using he_HOL hab rel_interior_closed_segment[of a b] by (by100 simp)
  have htm0: "0 < t - u"
    using hut by (by100 linarith)
  have htm1: "t - u < 1"
    using ht1 hu0 by (by100 linarith)
  have htp0: "0 < t + u"
    using ht0 hu0 by (by100 linarith)
  have htp1: "t + u < 1"
    using hu1mt by (by100 linarith)
  have hminus_eq:
    "p - u *\<^sub>R (b - a) = (1 - (t - u)) *\<^sub>R a + (t - u) *\<^sub>R b"
    using hp_eq by (simp add: algebra_simps scaleR_diff_right)
  have hplus_eq:
    "p + u *\<^sub>R (b - a) = (1 - (t + u)) *\<^sub>R a + (t + u) *\<^sub>R b"
    using hp_eq by (simp add: algebra_simps scaleR_diff_right)
  have hminus_open: "p - u *\<^sub>R (b - a) \<in> open_segment a b"
    unfolding in_segment using hab htm0 htm1 hminus_eq by (by100 blast)
  have hplus_open: "p + u *\<^sub>R (b - a) \<in> open_segment a b"
    unfolding in_segment using hab htp0 htp1 hplus_eq by (by100 blast)
  have hminus_rel: "p - u *\<^sub>R (b - a) \<in> rel_interior e"
    using hminus_open hrel by (by100 simp)
  have hplus_rel: "p + u *\<^sub>R (b - a) \<in> rel_interior e"
    using hplus_open hrel by (by100 simp)
  show ?thesis
    by (rule that[OF hu0 hminus_rel hplus_rel])
qed

lemma geotop_real_positive_edge_probe_parameter_dev34:
  fixes u v x y z :: real
  assumes hu: "0 < u"
  assumes hv: "0 < v"
  assumes hz: "0 < z"
  obtains s where
    "0 < s"
    "s < 1"
    "0 < (1 - s) * u + s * x"
    "0 < (1 - s) * v + s * y"
    "0 < s * z"
  (**
    Real parameter choice for a small probe from an edge-interior point into a
    triangle: preserve the two positive edge barycentric coordinates while
    turning on a positive opposite-vertex coordinate. **)
proof -
  define bx where "bx = (if x < u then u / (u - x) else 1)"
  define byy where "byy = (if y < v then v / (v - y) else 1)"
  have hbx_pos: "0 < bx"
  proof (cases "x < u")
    case True
    have "0 < u - x"
      using True by (by100 linarith)
    hence "0 < u / (u - x)"
      using hu by (simp add: divide_pos_pos)
    thus ?thesis
      using True bx_def by (by100 simp)
  next
    case False
    show ?thesis
      using False bx_def by (by100 simp)
  qed
  have hby_pos: "0 < byy"
  proof (cases "y < v")
    case True
    have "0 < v - y"
      using True by (by100 linarith)
    hence "0 < v / (v - y)"
      using hv by (simp add: divide_pos_pos)
    thus ?thesis
      using True byy_def by (by100 simp)
  next
    case False
    show ?thesis
      using False byy_def by (by100 simp)
  qed
  obtain t where ht0: "0 < t" and htbx: "t < bx" and ht1: "t < 1"
    using field_lbound_gt_zero[OF hbx_pos zero_less_one] by (by100 blast)
  obtain s where hs0: "0 < s" and hst: "s < t" and hsby: "s < byy"
    using field_lbound_gt_zero[OF ht0 hby_pos] by (by100 blast)
  have hs1: "s < 1"
    using hst ht1 by (by100 linarith)
  have hsbx: "s < bx"
    using hst htbx by (by100 linarith)
  have hxpos: "0 < (1 - s) * u + s * x"
  proof (cases "x < u")
    case True
    have hden: "0 < u - x"
      using True by (by100 linarith)
    have hsbound: "s < u / (u - x)"
      using hsbx True bx_def by (by100 simp)
    have "s * (u - x) < u"
      using hsbound hden by (simp add: field_simps)
    hence "0 < u - s * (u - x)"
      by (by100 linarith)
    also have "u - s * (u - x) = (1 - s) * u + s * x"
      by (simp add: field_simps algebra_simps)
    finally show ?thesis .
  next
    case False
    have hnonneg: "0 \<le> x - u"
      using False by (by100 linarith)
    have hs_nonneg: "0 \<le> s"
      using hs0 by (by100 linarith)
    have "0 \<le> s * (x - u)"
      by (rule mult_nonneg_nonneg[OF hs_nonneg hnonneg])
    moreover have "(1 - s) * u + s * x = u + s * (x - u)"
      by (simp add: field_simps algebra_simps)
    ultimately show ?thesis
      using hu by (by100 linarith)
  qed
  have hypos: "0 < (1 - s) * v + s * y"
  proof (cases "y < v")
    case True
    have hden: "0 < v - y"
      using True by (by100 linarith)
    have hsbound: "s < v / (v - y)"
      using hsby True byy_def by (by100 simp)
    have "s * (v - y) < v"
      using hsbound hden by (simp add: field_simps)
    hence "0 < v - s * (v - y)"
      by (by100 linarith)
    also have "v - s * (v - y) = (1 - s) * v + s * y"
      by (simp add: field_simps algebra_simps)
    finally show ?thesis .
  next
    case False
    have hnonneg: "0 \<le> y - v"
      using False by (by100 linarith)
    have hs_nonneg: "0 \<le> s"
      using hs0 by (by100 linarith)
    have "0 \<le> s * (y - v)"
      by (rule mult_nonneg_nonneg[OF hs_nonneg hnonneg])
    moreover have "(1 - s) * v + s * y = v + s * (y - v)"
      by (simp add: field_simps algebra_simps)
    ultimately show ?thesis
      using hv by (by100 linarith)
  qed
  have hsz: "0 < s * z"
    by (rule mult_pos_pos[OF hs0 hz])
  show ?thesis
    by (rule that[OF hs0 hs1 hxpos hypos hsz])
qed

lemma geotop_2simplex_positive_side_edge_normal_probe_in_HOL_interior_dev34:
  fixes e \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes hn: "n \<noteq> 0"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c > r"
  assumes hp: "p \<in> rel_interior e"
  obtains s where "0 < s" "p + s *\<^sub>R n \<in> interior \<sigma>"
  (**
    Normal-probe half of the book's two-triangle edge-neighborhood
    construction: from an edge-interior point, a small move into the strict side
    of the opposite vertex lands in the triangle interior. **)
proof -
  obtain t where ht0: "0 < t" and ht1: "t < 1"
    and hp_eq: "p = (1 - t) *\<^sub>R a + t *\<^sub>R b"
    by (rule geotop_edge_rel_interior_parameter_dev34[OF hab he_eq hp])
  have ha_aff: "a \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have hb_aff: "b \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have ha_line: "n \<bullet> a = r"
    using hline ha_aff by (by100 simp)
  have hb_line: "n \<bullet> b = r"
    using hline hb_aff by (by100 simp)
  have hp_line: "n \<bullet> p = r"
  proof -
    have "n \<bullet> p = n \<bullet> ((1 - t) *\<^sub>R a + t *\<^sub>R b)"
      using hp_eq by (by100 simp)
    also have "\<dots> = (1 - t) * (n \<bullet> a) + t * (n \<bullet> b)"
      by (simp add: inner_add_right inner_scaleR_right)
    also have "\<dots> = (1 - t) * r + t * r"
      using ha_line hb_line by (by100 simp)
    also have "\<dots> = r"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have hnn_pos: "0 < n \<bullet> n"
    using hn by (simp add: inner_gt_zero_iff)
  define q where "q = p + n"
  have hq_side: "n \<bullet> q > r"
  proof -
    have "n \<bullet> q = n \<bullet> (p + n)"
      using q_def by (by100 simp)
    also have "\<dots> = n \<bullet> p + n \<bullet> n"
      by (simp add: inner_add_right)
    also have "\<dots> = r + n \<bullet> n"
      using hp_line by (by100 simp)
    finally show ?thesis
      using hnn_pos by (by100 linarith)
  qed
  obtain x y z where hsum: "x + y + z = 1"
    and hq_eq: "q = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
    and hz: "0 < z"
    using geotop_2simplex_positive_side_affine_coordinate_positive_dev34
      [OF hab hc_not_ab h\<sigma>V hline hc_side hq_side]
    by (by100 blast)
  have hu: "0 < 1 - t"
    using ht1 by (by100 linarith)
  have hv: "0 < t"
    using ht0 .
  obtain s where hs0: "0 < s" and hs1: "s < 1"
    and hxpos: "0 < (1 - s) * (1 - t) + s * x"
    and hypos: "0 < (1 - s) * t + s * y"
    and hzpos: "0 < s * z"
    using geotop_real_positive_edge_probe_parameter_dev34[OF hu hv hz]
    by (by100 blast)
  have hsum_probe:
    "((1 - s) * (1 - t) + s * x) + ((1 - s) * t + s * y) + s * z = 1"
  proof -
    have "((1 - s) * (1 - t) + s * x) + ((1 - s) * t + s * y) + s * z =
        (1 - s) + s * (x + y + z)"
      by (simp add: algebra_simps)
    also have "\<dots> = 1"
      using hsum by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have hprobe_eq:
    "p + s *\<^sub>R n =
      ((1 - s) * (1 - t) + s * x) *\<^sub>R a
        + ((1 - s) * t + s * y) *\<^sub>R b
        + (s * z) *\<^sub>R c"
  proof -
    have "p + s *\<^sub>R n = (1 - s) *\<^sub>R p + s *\<^sub>R q"
      using q_def by (simp add: algebra_simps)
    also have "\<dots> =
      (1 - s) *\<^sub>R ((1 - t) *\<^sub>R a + t *\<^sub>R b)
        + s *\<^sub>R (x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c)"
      using hp_eq hq_eq by (by100 simp)
    also have "\<dots> =
      ((1 - s) * (1 - t) + s * x) *\<^sub>R a
        + ((1 - s) * t + s * y) *\<^sub>R b
        + (s * z) *\<^sub>R c"
      by (simp add: algebra_simps scaleR_add_left scaleR_add_right)
    finally show ?thesis .
  qed
  have hprobe_in: "p + s *\<^sub>R n \<in> interior \<sigma>"
    by (rule geotop_2simplex_positive_bary_in_HOL_interior_dev34
        [OF hab hc_not_ab h\<sigma>V hxpos hypos hzpos hsum_probe hprobe_eq])
  show ?thesis
    by (rule that[OF hs0 hprobe_in])
qed

lemma geotop_2simplex_negative_side_edge_normal_probe_in_HOL_interior_dev34:
  fixes e \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes hn: "n \<noteq> 0"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c < r"
  assumes hp: "p \<in> rel_interior e"
  obtains s where "0 < s" "p - s *\<^sub>R n \<in> interior \<sigma>"
  (**
    Negative-side version of the normal probe, phrased with the original normal
    direction for use in the opposite-side shared-edge local model. **)
proof -
  have hn_neg: "-n \<noteq> 0"
    using hn by (by100 simp)
  have hline_neg: "affine hull {a, b} = {x. (-n) \<bullet> x = -r}"
    using hline by (simp add: set_eq_iff)
  have hc_pos: "(-n) \<bullet> c > -r"
    using hc_side by (by100 simp)
  obtain s where hs0: "0 < s"
    and hs_in: "p + s *\<^sub>R (-n) \<in> interior \<sigma>"
    by (rule geotop_2simplex_positive_side_edge_normal_probe_in_HOL_interior_dev34
        [OF hab hc_not_ab hn_neg he_eq h\<sigma>V hline_neg hc_pos hp])
  have hprobe: "p - s *\<^sub>R n \<in> interior \<sigma>"
    using hs_in by (by100 simp)
  show ?thesis
    by (rule that[OF hs0 hprobe])
qed

lemma geotop_2simplex_opposite_side_shared_edge_normal_probes_in_HOL_interiors_dev34:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes hd_not_ab: "d \<notin> {a, b}"
  assumes hn: "n \<noteq> 0"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hopp: "(n \<bullet> c > r \<and> n \<bullet> d < r) \<or> (n \<bullet> c < r \<and> n \<bullet> d > r)"
  assumes hp: "p \<in> rel_interior e"
  obtains s t where
    "0 < s"
    "0 < t"
    "(p + s *\<^sub>R n \<in> interior \<sigma> \<and> p - t *\<^sub>R n \<in> interior \<tau>)
      \<or> (p - s *\<^sub>R n \<in> interior \<sigma> \<and> p + t *\<^sub>R n \<in> interior \<tau>)"
  (**
    Opposite-side normal probes at an edge-interior point: according to the
    orientation of the two opposite vertices, the two incident triangle
    interiors meet the two normal rays from the edge point. **)
proof -
  consider (posneg) "n \<bullet> c > r" "n \<bullet> d < r"
    | (negpos) "n \<bullet> c < r" "n \<bullet> d > r"
    using hopp by (by100 blast)
  thus ?thesis
  proof cases
    case posneg
    obtain s where hs0: "0 < s"
      and hs_in: "p + s *\<^sub>R n \<in> interior \<sigma>"
      by (rule geotop_2simplex_positive_side_edge_normal_probe_in_HOL_interior_dev34
          [OF hab hc_not_ab hn he_eq h\<sigma>V hline posneg(1) hp])
    obtain t where ht0: "0 < t"
      and ht_in: "p - t *\<^sub>R n \<in> interior \<tau>"
      by (rule geotop_2simplex_negative_side_edge_normal_probe_in_HOL_interior_dev34
          [OF hab hd_not_ab hn he_eq h\<tau>V hline posneg(2) hp])
    show ?thesis
    proof (rule that[OF hs0 ht0])
      show "(p + s *\<^sub>R n \<in> interior \<sigma> \<and> p - t *\<^sub>R n \<in> interior \<tau>)
          \<or> (p - s *\<^sub>R n \<in> interior \<sigma> \<and> p + t *\<^sub>R n \<in> interior \<tau>)"
        using hs_in ht_in by (by100 blast)
    qed
  next
    case negpos
    obtain s where hs0: "0 < s"
      and hs_in: "p - s *\<^sub>R n \<in> interior \<sigma>"
      by (rule geotop_2simplex_negative_side_edge_normal_probe_in_HOL_interior_dev34
          [OF hab hc_not_ab hn he_eq h\<sigma>V hline negpos(1) hp])
    obtain t where ht0: "0 < t"
      and ht_in: "p + t *\<^sub>R n \<in> interior \<tau>"
      by (rule geotop_2simplex_positive_side_edge_normal_probe_in_HOL_interior_dev34
          [OF hab hd_not_ab hn he_eq h\<tau>V hline negpos(2) hp])
    show ?thesis
    proof (rule that[OF hs0 ht0])
      show "(p + s *\<^sub>R n \<in> interior \<sigma> \<and> p - t *\<^sub>R n \<in> interior \<tau>)
          \<or> (p - s *\<^sub>R n \<in> interior \<sigma> \<and> p + t *\<^sub>R n \<in> interior \<tau>)"
        using hs_in ht_in by (by100 blast)
    qed
  qed
qed

lemma geotop_edge_subset_2simplex_vertices_dev34:
  fixes e \<sigma> :: "(real^2) set"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  shows "e \<subseteq> \<sigma>"
  (**
    Vertex-form containment used in the local diamond argument: the edge
    spanned by two triangle vertices is contained in the triangle. **)
proof -
  have he_HOL: "e = convex hull {a, b}"
    using he_eq geotop_convex_hull_eq_HOL[of "{a, b}"] by (by100 simp)
  have h\<sigma>_geo: "\<sigma> = geotop_convex_hull {a, b, c}"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have h\<sigma>_HOL: "\<sigma> = convex hull {a, b, c}"
    using h\<sigma>_geo geotop_convex_hull_eq_HOL[of "{a, b, c}"] by (by100 simp)
  have hsub: "{a, b} \<subseteq> {a, b, c}"
    by (by100 blast)
  have "convex hull {a, b} \<subseteq> convex hull {a, b, c}"
    by (rule hull_mono[OF hsub])
  thus ?thesis
    using he_HOL h\<sigma>_HOL by (by100 simp)
qed

lemma geotop_shared_edge_rel_interior_subset_two_2simplexes_dev34:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
  shows "rel_interior e \<subseteq> \<sigma> \<inter> \<tau>"
  (**
    The common edge's relative interior is contained in both incident triangles,
    a direct set-level input for the local diamond neighborhood argument. **)
proof
  fix p
  assume hp: "p \<in> rel_interior e"
  have hp_e: "p \<in> e"
    using hp rel_interior_subset by (by100 blast)
  have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
    by (rule geotop_edge_subset_2simplex_vertices_dev34[OF he_eq h\<sigma>V])
  have he_sub_\<tau>: "e \<subseteq> \<tau>"
    by (rule geotop_edge_subset_2simplex_vertices_dev34[OF he_eq h\<tau>V])
  show "p \<in> \<sigma> \<inter> \<tau>"
    using hp_e he_sub_\<sigma> he_sub_\<tau> by (by100 blast)
qed

lemma geotop_shared_edge_small_subsegment_in_two_2simplexes_dev34:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
  assumes hp: "p \<in> rel_interior e"
  obtains u where
    "0 < u"
    "p - u *\<^sub>R (b - a) \<in> \<sigma> \<inter> \<tau>"
    "p + u *\<^sub>R (b - a) \<in> \<sigma> \<inter> \<tau>"
  (**
    Horizontal base of the local diamond in the two incident triangles: a
    sufficiently small edge-direction subsegment around \<open>p\<close> remains in both
    closed triangles. **)
proof -
  obtain u where hu0: "0 < u"
    and hminus_rel: "p - u *\<^sub>R (b - a) \<in> rel_interior e"
    and hplus_rel: "p + u *\<^sub>R (b - a) \<in> rel_interior e"
    by (rule geotop_edge_rel_interior_small_subsegment_dev34[OF hab he_eq hp])
  have hrel_sub: "rel_interior e \<subseteq> \<sigma> \<inter> \<tau>"
    by (rule geotop_shared_edge_rel_interior_subset_two_2simplexes_dev34
        [OF he_eq h\<sigma>V h\<tau>V])
  have hminus: "p - u *\<^sub>R (b - a) \<in> \<sigma> \<inter> \<tau>"
    using hminus_rel hrel_sub by (by100 blast)
  have hplus: "p + u *\<^sub>R (b - a) \<in> \<sigma> \<inter> \<tau>"
    using hplus_rel hrel_sub by (by100 blast)
  show ?thesis
    by (rule that[OF hu0 hminus hplus])
qed

lemma geotop_convex_hull_three_points_subset_2simplex_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hx: "x \<in> \<sigma>"
  assumes hy: "y \<in> \<sigma>"
  assumes hz: "z \<in> \<sigma>"
  shows "convex hull {x, y, z} \<subseteq> \<sigma>"
  (**
    Convexity wrapper for the local diamond construction: any small triangle
    whose vertices lie in a simplex is contained in that simplex. **)
proof -
  have h\<sigma>_geo: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have h\<sigma>_HOL: "\<sigma> = convex hull V"
    using h\<sigma>_geo geotop_convex_hull_eq_HOL[of V] by (by100 simp)
  have hconv: "convex \<sigma>"
    using h\<sigma>_HOL by (by100 simp)
  have hpts: "{x, y, z} \<subseteq> \<sigma>"
    using hx hy hz by (by100 blast)
  have "convex hull {x, y, z} \<subseteq> \<sigma>"
    by (rule hull_minimal[where S=convex, OF hpts hconv])
  thus ?thesis
    by (by100 simp)
qed

lemma geotop_shared_edge_probe_triangles_subset_union_dev34:
  fixes \<sigma> \<tau> :: "(real^2) set"
  fixes q1 q2 qtop qbot :: "real^2"
  fixes V\<sigma> V\<tau> :: "(real^2) set"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V\<sigma>"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> V\<tau>"
  assumes hq1: "q1 \<in> \<sigma> \<inter> \<tau>"
  assumes hq2: "q2 \<in> \<sigma> \<inter> \<tau>"
  assumes htop: "qtop \<in> interior \<sigma>"
  assumes hbot: "qbot \<in> interior \<tau>"
  shows "convex hull {q1, q2, qtop} \<union> convex hull {q1, q2, qbot} \<subseteq> \<sigma> \<union> \<tau>"
  (**
    Set-containment package for the local diamond: the upper small triangle
    lies in the first incident 2-simplex and the lower small triangle lies in
    the second. **)
proof -
  have hqtop_\<sigma>: "qtop \<in> \<sigma>"
    using htop interior_subset by (by100 blast)
  have hqbot_\<tau>: "qbot \<in> \<tau>"
    using hbot interior_subset by (by100 blast)
  have hq1_\<sigma>: "q1 \<in> \<sigma>" and hq2_\<sigma>: "q2 \<in> \<sigma>"
    using hq1 hq2 by (by100 blast)+
  have hq1_\<tau>: "q1 \<in> \<tau>" and hq2_\<tau>: "q2 \<in> \<tau>"
    using hq1 hq2 by (by100 blast)+
  have htop_sub: "convex hull {q1, q2, qtop} \<subseteq> \<sigma>"
    by (rule geotop_convex_hull_three_points_subset_2simplex_dev34
        [OF h\<sigma>V hq1_\<sigma> hq2_\<sigma> hqtop_\<sigma>])
  have hbot_sub: "convex hull {q1, q2, qbot} \<subseteq> \<tau>"
    by (rule geotop_convex_hull_three_points_subset_2simplex_dev34
        [OF h\<tau>V hq1_\<tau> hq2_\<tau> hqbot_\<tau>])
  show ?thesis
    using htop_sub hbot_sub by (by100 blast)
qed

lemma geotop_shared_edge_probe_diamond_contains_ball_dev34:
  fixes p v n :: "real^2"
  assumes hv: "v \<noteq> 0"
  assumes hn: "n \<noteq> 0"
  assumes horth: "v \<bullet> n = 0"
  assumes hu: "0 < u"
  assumes hs: "0 < s"
  assumes ht: "0 < t"
  obtains eps where
    "0 < eps"
    "ball p eps \<subseteq>
      convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p + s *\<^sub>R n}
        \<union> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p - t *\<^sub>R n}"
  (**
    Analytic diamond step in Moise's shared-edge local model: the two small
    triangles with common base in the edge direction and apices on opposite
    normal rays contain a genuine Euclidean ball around the edge point. **)
proof -
  have hspan: "span {v, n} = UNIV"
  proof -
    have hvn_distinct: "v \<noteq> n"
    proof
      assume hvn: "v = n"
      have "v \<bullet> v = 0"
        using horth hvn by (by100 simp)
      thus False
        using hv by (simp add: inner_eq_zero_iff)
    qed
    have hpair: "pairwise orthogonal {v, n}"
      using horth by (simp add: pairwise_def orthogonal_def inner_commute)
    have hzero: "0 \<notin> {v, n}"
      using hv hn by (by100 simp)
    have hind: "independent {v, n}"
      by (rule pairwise_orthogonal_independent[OF hpair hzero])
    have hcard: "card {v, n} = DIM(real^2)"
      using hvn_distinct by (by100 simp)
    have hdim: "dim {v, n} = DIM(real^2)"
      using indep_card_eq_dim_span[OF hind] hcard by (by100 simp)
    show ?thesis
      using hdim dim_eq_full[of "{v, n}"] by (by100 simp)
  qed
  have hcoords:
    "\<forall>x. \<exists>\<alpha> \<beta>. x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
  proof
    fix x
    have hxspan: "x - p \<in> span (insert v {n})"
      using hspan by (by100 simp)
    obtain \<alpha> where h\<alpha>: "x - p - \<alpha> *\<^sub>R v \<in> span {n}"
      using hxspan unfolding span_breakdown_eq by (by100 blast)
    obtain \<beta> where h\<beta>: "x - p - \<alpha> *\<^sub>R v - \<beta> *\<^sub>R n \<in> span ({} :: (real^2) set)"
      using h\<alpha> unfolding span_breakdown_eq by (by100 blast)
    have hzero: "x - p - \<alpha> *\<^sub>R v - \<beta> *\<^sub>R n = 0"
      using h\<beta> by (by100 simp)
    show "\<exists>\<alpha> \<beta>. x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
    proof (intro exI)
      show "x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
        using hzero by (simp add: algebra_simps)
    qed
  qed
  have hsmall_coords:
    "\<exists>eps>0. \<forall>x\<in>ball p eps.
      \<exists>\<alpha> \<beta>. x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
        \<and> \<bar>\<alpha>\<bar> < u / 2
        \<and> \<bar>\<beta>\<bar> < min s t / 2"
  proof -
    have hvn: "0 < norm v"
      using hv by (by100 simp)
    have hnn: "0 < norm n"
      using hn by (by100 simp)
    have hm: "0 < min s t"
      using hs ht by (by100 simp)
    define eps where "eps = min (u * norm v / 4) (min s t * norm n / 4)"
    have heps: "0 < eps"
      using hu hvn hm hnn unfolding eps_def by (by100 simp)
    have heps_v: "eps \<le> u * norm v / 4"
      unfolding eps_def by (by100 simp)
    have heps_n: "eps \<le> min s t * norm n / 4"
      unfolding eps_def by (by100 simp)
    have hvn_nonneg: "0 \<le> norm v"
      using hvn by (by100 linarith)
    have hnn_nonneg: "0 \<le> norm n"
      using hnn by (by100 linarith)
    have hbound:
      "\<forall>x\<in>ball p eps.
        \<exists>\<alpha> \<beta>. x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
          \<and> \<bar>\<alpha>\<bar> < u / 2
          \<and> \<bar>\<beta>\<bar> < min s t / 2"
    proof
      fix x
      assume hx: "x \<in> ball p eps"
      obtain \<alpha> \<beta> where hxrep: "x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
        using hcoords by (by100 blast)
      let ?y = "x - p"
      have hyrep: "?y = \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
        using hxrep by (simp add: algebra_simps)
      have hy_norm: "norm ?y < eps"
        using hx by (simp add: dist_norm norm_minus_commute)
      have hv_inner_pos: "0 < v \<bullet> v"
        using hv by (simp add: inner_gt_zero_iff)
      have hn_inner_pos: "0 < n \<bullet> n"
        using hn by (simp add: inner_gt_zero_iff)
      have hv_inner_nonneg: "0 \<le> v \<bullet> v"
        using hv_inner_pos by (by100 linarith)
      have hn_inner_nonneg: "0 \<le> n \<bullet> n"
        using hn_inner_pos by (by100 linarith)
      have hv_inner_norm: "v \<bullet> v = norm v * norm v"
        by (simp add: dot_square_norm power2_eq_square)
      have hn_inner_norm: "n \<bullet> n = norm n * norm n"
        by (simp add: dot_square_norm power2_eq_square)
      have hnv: "n \<bullet> v = 0"
        by (subst inner_commute) (rule horth)
      have hdot_v: "?y \<bullet> v = \<alpha> * (v \<bullet> v)"
      proof -
        have "?y \<bullet> v = (\<alpha> *\<^sub>R v + \<beta> *\<^sub>R n) \<bullet> v"
          using hyrep by (by100 simp)
        also have "\<dots> = \<alpha> * (v \<bullet> v) + \<beta> * (n \<bullet> v)"
          by (simp add: inner_add_left inner_scaleR_left)
        also have "\<dots> = \<alpha> * (v \<bullet> v)"
          using hnv by (by100 simp)
        finally show ?thesis .
      qed
      have halpha_eq: "\<alpha> = (?y \<bullet> v) / (v \<bullet> v)"
        using hdot_v hv_inner_pos by (simp add: field_simps)
      have hdot_n: "?y \<bullet> n = \<beta> * (n \<bullet> n)"
      proof -
        have "?y \<bullet> n = (\<alpha> *\<^sub>R v + \<beta> *\<^sub>R n) \<bullet> n"
          using hyrep by (by100 simp)
        also have "\<dots> = \<alpha> * (v \<bullet> n) + \<beta> * (n \<bullet> n)"
          by (simp add: inner_add_left inner_scaleR_left)
        also have "\<dots> = \<beta> * (n \<bullet> n)"
          using horth by (by100 simp)
        finally show ?thesis .
      qed
      have hbeta_eq: "\<beta> = (?y \<bullet> n) / (n \<bullet> n)"
        using hdot_n hn_inner_pos by (simp add: field_simps)
      have halpha_abs_le: "\<bar>\<alpha>\<bar> \<le> norm ?y / norm v"
      proof -
        have hcs: "\<bar>?y \<bullet> v\<bar> \<le> norm ?y * norm v"
          by (rule Cauchy_Schwarz_ineq2)
        have "\<bar>\<alpha>\<bar> = \<bar>?y \<bullet> v\<bar> / (v \<bullet> v)"
          using halpha_eq hv_inner_pos by (by100 simp)
        also have "\<dots> \<le> (norm ?y * norm v) / (v \<bullet> v)"
          by (rule divide_right_mono[OF hcs hv_inner_nonneg])
        also have "\<dots> = norm ?y / norm v"
          using hvn hv_inner_norm by (simp add: field_simps)
        finally show ?thesis .
      qed
      have hbeta_abs_le: "\<bar>\<beta>\<bar> \<le> norm ?y / norm n"
      proof -
        have hcs: "\<bar>?y \<bullet> n\<bar> \<le> norm ?y * norm n"
          by (rule Cauchy_Schwarz_ineq2)
        have "\<bar>\<beta>\<bar> = \<bar>?y \<bullet> n\<bar> / (n \<bullet> n)"
          using hbeta_eq hn_inner_pos by (by100 simp)
        also have "\<dots> \<le> (norm ?y * norm n) / (n \<bullet> n)"
          by (rule divide_right_mono[OF hcs hn_inner_nonneg])
        also have "\<dots> = norm ?y / norm n"
          using hnn hn_inner_norm by (simp add: field_simps)
        finally show ?thesis .
      qed
      have halpha_lt: "\<bar>\<alpha>\<bar> < u / 2"
      proof -
        have "norm ?y / norm v < eps / norm v"
          by (rule divide_strict_right_mono[OF hy_norm hvn])
        also have "\<dots> \<le> (u * norm v / 4) / norm v"
          by (rule divide_right_mono[OF heps_v hvn_nonneg])
        also have "\<dots> = u / 4"
          using hvn by (simp add: field_simps)
        also have "\<dots> < u / 2"
          using hu by (by100 linarith)
        finally show ?thesis
          using halpha_abs_le by (by100 linarith)
      qed
      have hbeta_lt: "\<bar>\<beta>\<bar> < min s t / 2"
      proof -
        have "norm ?y / norm n < eps / norm n"
          by (rule divide_strict_right_mono[OF hy_norm hnn])
        also have "\<dots> \<le> (min s t * norm n / 4) / norm n"
          by (rule divide_right_mono[OF heps_n hnn_nonneg])
        also have "\<dots> = min s t / 4"
          using hnn by (simp add: field_simps)
        also have "\<dots> < min s t / 2"
          using hm by (by100 linarith)
        finally show ?thesis
          using hbeta_abs_le by (by100 linarith)
      qed
      show "\<exists>\<alpha> \<beta>. x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
          \<and> \<bar>\<alpha>\<bar> < u / 2
          \<and> \<bar>\<beta>\<bar> < min s t / 2"
        using hxrep halpha_lt hbeta_lt by (by100 blast)
    qed
    show ?thesis
      using heps hbound by (by100 blast)
  qed
  have hupper_membership:
    "\<forall>\<alpha> \<beta>. \<bar>\<alpha>\<bar> < u / 2 \<and> 0 \<le> \<beta> \<and> \<beta> < s / 2 \<longrightarrow>
      p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
        \<in> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p + s *\<^sub>R n}"
  proof (intro allI impI)
    fix \<alpha> \<beta>
    assume h: "\<bar>\<alpha>\<bar> < u / 2 \<and> 0 \<le> \<beta> \<and> \<beta> < s / 2"
    define \<mu> where "\<mu> = \<beta> / s"
    define ell where "ell = ((\<alpha> / u) + 1 - \<mu>) / 2"
    have h\<mu>0: "0 \<le> \<mu>"
      using h hs unfolding \<mu>_def by (by100 simp)
    have h\<mu>half: "\<mu> < 1 / 2"
      using h hs unfolding \<mu>_def by (simp add: field_simps)
    have h\<alpha>abs: "\<bar>\<alpha>\<bar> < u / 2"
      using h by (by100 blast)
    have h\<alpha>gt: "- (u / 2) < \<alpha>"
    proof -
      have "- \<alpha> \<le> \<bar>\<alpha>\<bar>"
        by (by100 simp)
      thus ?thesis
        using h\<alpha>abs by (by100 linarith)
    qed
    have h\<alpha>lt: "\<alpha> < u / 2"
    proof -
      have "\<alpha> \<le> \<bar>\<alpha>\<bar>"
        by (by100 simp)
      thus ?thesis
        using h\<alpha>abs by (by100 linarith)
    qed
    have h\<alpha>u_gt: "- (1 / 2) < \<alpha> / u"
      using h\<alpha>gt hu by (simp add: field_simps)
    have h\<alpha>u_lt: "\<alpha> / u < 1 / 2"
      using h\<alpha>lt hu by (simp add: field_simps)
    have hell_num_pos: "0 < \<alpha> / u + 1 - \<mu>"
    proof -
      have "- (1 / 2) + 1 - (1 / 2) < \<alpha> / u + 1 - \<mu>"
        using h\<alpha>u_gt h\<mu>half by linarith
      thus ?thesis
        by (by100 simp)
    qed
    have hell0_strict: "0 < ell"
      using hell_num_pos unfolding ell_def by (by100 simp)
    have hell0: "0 \<le> ell"
      using hell0_strict by (by100 linarith)
    have hell\<mu>_num_lt: "\<alpha> / u + 1 + \<mu> < 2"
    proof -
      have "\<alpha> / u + 1 + \<mu> < (1 / 2) + 1 + (1 / 2)"
        using h\<alpha>u_lt h\<mu>half by linarith
      thus ?thesis
        by (by100 simp)
    qed
    have hell\<mu>_expr: "ell + \<mu> = (\<alpha> / u + 1 + \<mu>) / 2"
      unfolding ell_def by (simp add: field_simps)
    have hell\<mu>_strict: "ell + \<mu> < 1"
      using hell\<mu>_expr hell\<mu>_num_lt by (by100 simp)
    have hell\<mu>: "ell + \<mu> \<le> 1"
      using hell\<mu>_strict by (by100 linarith)
    have h\<mu>s: "\<mu> * s = \<beta>"
      using hs unfolding \<mu>_def by (by100 simp)
    have hv_coeff: "- u + 2 * u * ell + u * \<mu> = \<alpha>"
      using hu hs unfolding ell_def \<mu>_def by (simp add: field_simps)
    have heq:
      "p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n =
        (p - u *\<^sub>R v)
          + ell *\<^sub>R ((p + u *\<^sub>R v) - (p - u *\<^sub>R v))
          + \<mu> *\<^sub>R ((p + s *\<^sub>R n) - (p - u *\<^sub>R v))"
    proof -
      have hbase_diff:
        "(p + u *\<^sub>R v) - (p - u *\<^sub>R v) = (2 * u) *\<^sub>R v"
        by (simp add: vec_eq_iff algebra_simps)
      have hapex_diff:
        "(p + s *\<^sub>R n) - (p - u *\<^sub>R v) = u *\<^sub>R v + s *\<^sub>R n"
        by (simp add: vec_eq_iff algebra_simps)
      have "(p - u *\<^sub>R v)
          + ell *\<^sub>R ((p + u *\<^sub>R v) - (p - u *\<^sub>R v))
          + \<mu> *\<^sub>R ((p + s *\<^sub>R n) - (p - u *\<^sub>R v))
        = p + (- u + 2 * u * ell + u * \<mu>) *\<^sub>R v + (\<mu> * s) *\<^sub>R n"
        using hbase_diff hapex_diff
        by (simp add: algebra_simps scaleR_add_right)
      also have "\<dots> = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
        using h\<mu>s hv_coeff by (by100 simp)
      finally show ?thesis
        by (by100 simp)
    qed
    have "p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n \<in>
      {p - u *\<^sub>R v
        + ell *\<^sub>R ((p + u *\<^sub>R v) - (p - u *\<^sub>R v))
        + \<mu> *\<^sub>R ((p + s *\<^sub>R n) - (p - u *\<^sub>R v))
        | ell \<mu>. 0 \<le> ell \<and> 0 \<le> \<mu> \<and> ell + \<mu> \<le> 1}"
      using heq hell0 h\<mu>0 hell\<mu> by (by100 blast)
    thus "p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
        \<in> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p + s *\<^sub>R n}"
      using convex_hull_3_alt
        [of "p - u *\<^sub>R v" "p + u *\<^sub>R v" "p + s *\<^sub>R n"]
      by (by100 simp)
  qed
  have hlower_membership:
    "\<forall>\<alpha> \<beta>. \<bar>\<alpha>\<bar> < u / 2 \<and> - (t / 2) < \<beta> \<and> \<beta> < 0 \<longrightarrow>
      p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
        \<in> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p - t *\<^sub>R n}"
  proof (intro allI impI)
    fix \<alpha> \<beta>
    assume h: "\<bar>\<alpha>\<bar> < u / 2 \<and> - (t / 2) < \<beta> \<and> \<beta> < 0"
    define \<mu> where "\<mu> = - \<beta> / t"
    define ell where "ell = ((\<alpha> / u) + 1 - \<mu>) / 2"
    have h\<beta>neg: "\<beta> < 0"
      using h by (by100 blast)
    have hneg\<beta>_lt: "- \<beta> < t / 2"
      using h by (by100 linarith)
    have h\<mu>0: "0 \<le> \<mu>"
      using h\<beta>neg ht unfolding \<mu>_def by (simp add: field_simps)
    have h\<mu>half: "\<mu> < 1 / 2"
      using hneg\<beta>_lt ht unfolding \<mu>_def by (simp add: field_simps)
    have h\<alpha>abs: "\<bar>\<alpha>\<bar> < u / 2"
      using h by (by100 blast)
    have h\<alpha>gt: "- (u / 2) < \<alpha>"
    proof -
      have "- \<alpha> \<le> \<bar>\<alpha>\<bar>"
        by (by100 simp)
      thus ?thesis
        using h\<alpha>abs by (by100 linarith)
    qed
    have h\<alpha>lt: "\<alpha> < u / 2"
    proof -
      have "\<alpha> \<le> \<bar>\<alpha>\<bar>"
        by (by100 simp)
      thus ?thesis
        using h\<alpha>abs by (by100 linarith)
    qed
    have h\<alpha>u_gt: "- (1 / 2) < \<alpha> / u"
      using h\<alpha>gt hu by (simp add: field_simps)
    have h\<alpha>u_lt: "\<alpha> / u < 1 / 2"
      using h\<alpha>lt hu by (simp add: field_simps)
    have hell_num_pos: "0 < \<alpha> / u + 1 - \<mu>"
    proof -
      have "- (1 / 2) + 1 - (1 / 2) < \<alpha> / u + 1 - \<mu>"
        using h\<alpha>u_gt h\<mu>half by linarith
      thus ?thesis
        by (by100 simp)
    qed
    have hell0_strict: "0 < ell"
      using hell_num_pos unfolding ell_def by (by100 simp)
    have hell0: "0 \<le> ell"
      using hell0_strict by (by100 linarith)
    have hell\<mu>_num_lt: "\<alpha> / u + 1 + \<mu> < 2"
    proof -
      have "\<alpha> / u + 1 + \<mu> < (1 / 2) + 1 + (1 / 2)"
        using h\<alpha>u_lt h\<mu>half by linarith
      thus ?thesis
        by (by100 simp)
    qed
    have hell\<mu>_expr: "ell + \<mu> = (\<alpha> / u + 1 + \<mu>) / 2"
      unfolding ell_def by (simp add: field_simps)
    have hell\<mu>_strict: "ell + \<mu> < 1"
      using hell\<mu>_expr hell\<mu>_num_lt by (by100 simp)
    have hell\<mu>: "ell + \<mu> \<le> 1"
      using hell\<mu>_strict by (by100 linarith)
    have h\<mu>t: "- (\<mu> * t) = \<beta>"
      using ht unfolding \<mu>_def by (by100 simp)
    have hv_coeff: "- u + 2 * u * ell + u * \<mu> = \<alpha>"
      using hu ht unfolding ell_def \<mu>_def by (simp add: field_simps)
    have heq:
      "p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n =
        (p - u *\<^sub>R v)
          + ell *\<^sub>R ((p + u *\<^sub>R v) - (p - u *\<^sub>R v))
          + \<mu> *\<^sub>R ((p - t *\<^sub>R n) - (p - u *\<^sub>R v))"
    proof -
      have hbase_diff:
        "(p + u *\<^sub>R v) - (p - u *\<^sub>R v) = (2 * u) *\<^sub>R v"
        by (simp add: vec_eq_iff algebra_simps)
      have hapex_diff:
        "(p - t *\<^sub>R n) - (p - u *\<^sub>R v) = u *\<^sub>R v - t *\<^sub>R n"
        by (simp add: vec_eq_iff algebra_simps)
      have "(p - u *\<^sub>R v)
          + ell *\<^sub>R ((p + u *\<^sub>R v) - (p - u *\<^sub>R v))
          + \<mu> *\<^sub>R ((p - t *\<^sub>R n) - (p - u *\<^sub>R v))
        = p + (- u + 2 * u * ell + u * \<mu>) *\<^sub>R v + (- (\<mu> * t)) *\<^sub>R n"
        using hbase_diff hapex_diff
        by (simp add: algebra_simps scaleR_add_right)
      also have "\<dots> = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
        using h\<mu>t hv_coeff by (by100 simp)
      finally show ?thesis
        by (by100 simp)
    qed
    have "p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n \<in>
      {p - u *\<^sub>R v
        + ell *\<^sub>R ((p + u *\<^sub>R v) - (p - u *\<^sub>R v))
        + \<mu> *\<^sub>R ((p - t *\<^sub>R n) - (p - u *\<^sub>R v))
        | ell \<mu>. 0 \<le> ell \<and> 0 \<le> \<mu> \<and> ell + \<mu> \<le> 1}"
      using heq hell0 h\<mu>0 hell\<mu> by (by100 blast)
    thus "p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
        \<in> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p - t *\<^sub>R n}"
      using convex_hull_3_alt
        [of "p - u *\<^sub>R v" "p + u *\<^sub>R v" "p - t *\<^sub>R n"]
      by (by100 simp)
  qed
  have hdiamond_ball:
    "\<exists>eps>0. ball p eps \<subseteq>
      convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p + s *\<^sub>R n}
        \<union> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p - t *\<^sub>R n}"
    using hsmall_coords hupper_membership hlower_membership
  proof -
    obtain eps where heps: "0 < eps"
      and hball:
        "\<forall>x\<in>ball p eps.
          \<exists>\<alpha> \<beta>. x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
            \<and> \<bar>\<alpha>\<bar> < u / 2
            \<and> \<bar>\<beta>\<bar> < min s t / 2"
      using hsmall_coords by (by100 blast)
    have hsub:
      "ball p eps \<subseteq>
        convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p + s *\<^sub>R n}
          \<union> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p - t *\<^sub>R n}"
    proof
      fix x
      assume hx: "x \<in> ball p eps"
      obtain \<alpha> \<beta> where hx_eq: "x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
        and h\<alpha>: "\<bar>\<alpha>\<bar> < u / 2"
        and h\<beta>: "\<bar>\<beta>\<bar> < min s t / 2"
        using hball hx by (by100 blast)
      show "x \<in>
        convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p + s *\<^sub>R n}
          \<union> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p - t *\<^sub>R n}"
      proof (cases "0 \<le> \<beta>")
        case True
        have h\<beta>s: "\<beta> < s / 2"
          using h\<beta> True min.cobounded1[of s t] by (by100 linarith)
        have "x \<in> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p + s *\<^sub>R n}"
          using hupper_membership h\<alpha> True h\<beta>s hx_eq by (by100 blast)
        thus ?thesis
          by (by100 blast)
      next
        case False
        have h\<beta>neg: "\<beta> < 0"
          using False by (by100 linarith)
        have h\<beta>t: "- (t / 2) < \<beta>"
          using h\<beta> False min.cobounded2[of s t] by (by100 linarith)
        have "x \<in> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p - t *\<^sub>R n}"
          using hlower_membership h\<alpha> h\<beta>neg h\<beta>t hx_eq by (by100 blast)
        thus ?thesis
          by (by100 blast)
      qed
    qed
    show ?thesis
      using heps hsub by (by100 blast)
  qed
  show ?thesis
    using hdiamond_ball that
    by (by100 blast)
qed

lemma geotop_2simplex_opposite_side_shared_edge_rel_interior_subset_HOL_interior_union_dev34:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes hd_not_ab: "d \<notin> {a, b}"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hopp: "(n \<bullet> c > r \<and> n \<bullet> d < r) \<or> (n \<bullet> c < r \<and> n \<bullet> d > r)"
  shows "rel_interior e \<subseteq> interior (\<sigma> \<union> \<tau>)"
  (**
    Analytic local-neighborhood step for the shared-edge model: along the
    relative interior of the common edge, the two opposite-side 2-simplexes
    fill a full Euclidean disk neighborhood. **)
proof
  fix p
  assume hp: "p \<in> rel_interior e"
  have hv: "b - a \<noteq> 0"
    using hab by (by100 simp)
  have hn: "n \<noteq> 0"
  proof
    assume hn0: "n = 0"
    show False
      using hopp hn0 by (by100 auto)
  qed
  have ha_aff: "a \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have hb_aff: "b \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have ha_line: "n \<bullet> a = r"
    using hline ha_aff by (by100 simp)
  have hb_line: "n \<bullet> b = r"
    using hline hb_aff by (by100 simp)
  have horth_n: "n \<bullet> (b - a) = 0"
    using ha_line hb_line by (simp add: inner_diff_right)
  have horth: "(b - a) \<bullet> n = 0"
    using horth_n by (simp add: inner_commute)
  obtain u where hu: "0 < u"
    and hqminus: "p - u *\<^sub>R (b - a) \<in> \<sigma> \<inter> \<tau>"
    and hqplus: "p + u *\<^sub>R (b - a) \<in> \<sigma> \<inter> \<tau>"
    by (rule geotop_shared_edge_small_subsegment_in_two_2simplexes_dev34
        [OF hab he_eq h\<sigma>V h\<tau>V hp])
  obtain s t where hs: "0 < s"
    and ht: "0 < t"
    and hprobes:
      "(p + s *\<^sub>R n \<in> interior \<sigma> \<and> p - t *\<^sub>R n \<in> interior \<tau>)
        \<or> (p - s *\<^sub>R n \<in> interior \<sigma> \<and> p + t *\<^sub>R n \<in> interior \<tau>)"
    by (rule geotop_2simplex_opposite_side_shared_edge_normal_probes_in_HOL_interiors_dev34
        [OF hab hc_not_ab hd_not_ab hn he_eq h\<sigma>V h\<tau>V hline hopp hp])
  from hprobes show "p \<in> interior (\<sigma> \<union> \<tau>)"
  proof
    assume hside:
      "p + s *\<^sub>R n \<in> interior \<sigma> \<and> p - t *\<^sub>R n \<in> interior \<tau>"
    obtain eps where heps: "0 < eps"
      and hball:
        "ball p eps \<subseteq>
          convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p + s *\<^sub>R n}
            \<union> convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p - t *\<^sub>R n}"
      by (rule geotop_shared_edge_probe_diamond_contains_ball_dev34
          [OF hv hn horth hu hs ht])
    have hdiamond_sub:
      "convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p + s *\<^sub>R n}
        \<union> convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p - t *\<^sub>R n}
        \<subseteq> \<sigma> \<union> \<tau>"
      by (rule geotop_shared_edge_probe_triangles_subset_union_dev34
          [OF h\<sigma>V h\<tau>V hqminus hqplus hside[THEN conjunct1] hside[THEN conjunct2]])
    have hball_sub: "ball p eps \<subseteq> \<sigma> \<union> \<tau>"
      using hball hdiamond_sub by (by100 blast)
    have hp_ball: "p \<in> ball p eps"
      using heps by (by100 simp)
    show ?thesis
      by (rule interiorI[OF open_ball hp_ball hball_sub])
  next
    assume hside:
      "p - s *\<^sub>R n \<in> interior \<sigma> \<and> p + t *\<^sub>R n \<in> interior \<tau>"
    have hn_neg: "- n \<noteq> 0"
      using hn by (by100 simp)
    have horth_neg: "(b - a) \<bullet> (- n) = 0"
      using horth by (by100 simp)
    obtain eps where heps: "0 < eps"
      and hball_raw:
        "ball p eps \<subseteq>
          convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p + s *\<^sub>R (- n)}
            \<union> convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p - t *\<^sub>R (- n)}"
      by (rule geotop_shared_edge_probe_diamond_contains_ball_dev34
          [OF hv hn_neg horth_neg hu hs ht])
    have hball:
      "ball p eps \<subseteq>
        convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p - s *\<^sub>R n}
          \<union> convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p + t *\<^sub>R n}"
      using hball_raw by (by100 simp)
    have hdiamond_sub:
      "convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p - s *\<^sub>R n}
        \<union> convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p + t *\<^sub>R n}
        \<subseteq> \<sigma> \<union> \<tau>"
      by (rule geotop_shared_edge_probe_triangles_subset_union_dev34
          [OF h\<sigma>V h\<tau>V hqminus hqplus hside[THEN conjunct1] hside[THEN conjunct2]])
    have hball_sub: "ball p eps \<subseteq> \<sigma> \<union> \<tau>"
      using hball hdiamond_sub by (by100 blast)
    have hp_ball: "p \<in> ball p eps"
      using heps by (by100 simp)
    show ?thesis
      by (rule interiorI[OF open_ball hp_ball hball_sub])
  qed
qed

lemma geotop_complex_two_2simplex_shared_edge_rel_interior_subset_HOL_interior_union_dev34:
  fixes K :: "(real^2) set set"
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  assumes hedge: "geotop_is_edge e"
  shows "rel_interior e \<subseteq> interior (\<sigma> \<union> \<tau>)"
  (**
    Moise local model for the two-sided edge case: two distinct 2-simplexes
    of the same complex that share the edge \<open>e\<close> lie on opposite sides of
    \<open>e\<close>.  Their union fills the two local half-disks along
    \<open>rel_interior e\<close>, so it has ordinary Euclidean interior there. **)
proof (rule geotop_complex_two_2simplex_shared_edge_vertices_opposite_sides_dev34
    [OF hK h\<sigma>K h\<tau>K h\<sigma>2 h\<tau>2 h\<sigma>\<tau> he\<sigma> he\<tau> hedge])
  fix a b c d n r
  assume hab: "a \<noteq> b"
    and hc_not_ab: "c \<notin> {a, b}"
    and hd_not_ab: "d \<notin> {a, b}"
    and hcd: "c \<noteq> d"
    and he_eq: "e = geotop_convex_hull {a, b}"
    and h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
    and h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
    and hn: "n \<noteq> 0"
    and hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
    and hc_ne: "n \<bullet> c \<noteq> r"
    and hd_ne: "n \<bullet> d \<noteq> r"
    and h\<sigma>_pos: "n \<bullet> c > r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p > r}"
    and h\<sigma>_neg: "n \<bullet> c < r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p < r}"
    and h\<tau>_pos: "n \<bullet> d > r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p > r}"
    and h\<tau>_neg: "n \<bullet> d < r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p < r}"
    and hopp: "(n \<bullet> c > r \<and> n \<bullet> d < r) \<or> (n \<bullet> c < r \<and> n \<bullet> d > r)"
  show ?thesis
    by (rule geotop_2simplex_opposite_side_shared_edge_rel_interior_subset_HOL_interior_union_dev34
        [OF hab hc_not_ab hd_not_ab he_eq h\<sigma>V h\<tau>V hline hopp])
qed

lemma geotop_positive_radius_circle_is_1sphere_dev34:
  fixes p :: "real^2"
  assumes hr: "0 < r"
  shows "geotop_is_n_sphere (sphere p r)
      (subspace_topology UNIV geotop_euclidean_topology (sphere p r)) 1"
proof -
  have hhomeo_sphere: "sphere p r homeomorphic sphere (0::real^2) 1"
    using homeomorphic_spheres_gen[of r 1 p "0::real^2"] hr by (by100 simp)
  have hstd_eq: "(geotop_std_sphere::(real^2) set) = sphere (0::real^2) 1"
    unfolding geotop_std_sphere_def sphere_def by (by100 simp)
  have hhomeo_std: "sphere p r homeomorphic (geotop_std_sphere::(real^2) set)"
    using hhomeo_sphere hstd_eq by (by100 simp)
  obtain f where hf: "top1_homeomorphism_on (sphere p r)
        (subspace_topology UNIV geotop_euclidean_topology (sphere p r))
        (geotop_std_sphere::(real^2) set)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_std_sphere::(real^2) set)) f"
    using geotop_HOL_homeomorphic_imp_top1_homeomorphism_on[OF hhomeo_std]
    by (by100 blast)
  have htop: "is_topology_on (sphere p r)
        (subspace_topology UNIV geotop_euclidean_topology (sphere p r))"
    using hf unfolding top1_homeomorphism_on_def by (by100 blast)
  show ?thesis
    using htop hf unfolding geotop_is_n_sphere_def by (by100 blast)
qed

lemma geotop_three_incident_2simplex_small_circle_domain_sphere_exists_dev34:
  fixes K :: "(real^2) set set" and e U :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hfaces:
    "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
      \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
      \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
      \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
  assumes hlocal_ball: "\<exists>r>0. geotop_polyhedron K \<inter> ball p r \<subseteq> U"
  shows "\<exists>J. J \<subseteq> U
      \<and> geotop_is_n_sphere J
          (subspace_topology UNIV geotop_euclidean_topology J) 1"
  (**
    Moise Lemma 4, radius-choice part.  Two of the incident 2-simplexes fill a
    small two-sided disk around the edge-interior point; choose a small circle
    inside the given chart domain. **)
proof -
  have hp_e: "p \<in> e"
    using hp rel_interior_subset by (by100 blast)
  obtain rU where hrU: "0 < rU"
    and hballU: "geotop_polyhedron K \<inter> ball p rU \<subseteq> U"
    using hlocal_ball by (by100 blast)
  obtain \<sigma>1 \<sigma>2 \<sigma>3 where hfaces_data:
      "\<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
      \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
      \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
      \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
    using hfaces by (elim exE)
  have h12: "\<sigma>1 \<noteq> \<sigma>2"
    using hfaces_data by (by100 simp)
  have h\<sigma>1K: "\<sigma>1 \<in> K"
    using hfaces_data by (by100 simp)
  have h\<sigma>1dim: "geotop_simplex_dim \<sigma>1 2"
    using hfaces_data by (by100 simp)
  have h\<sigma>1face: "geotop_is_face e \<sigma>1"
    using hfaces_data by (by100 simp)
  have h\<sigma>2K: "\<sigma>2 \<in> K"
    using hfaces_data by (by100 simp)
  have h\<sigma>2dim: "geotop_simplex_dim \<sigma>2 2"
    using hfaces_data by (by100 simp)
  have h\<sigma>2face: "geotop_is_face e \<sigma>2"
    using hfaces_data by (by100 simp)
  have h\<sigma>1subM: "\<sigma>1 \<subseteq> geotop_polyhedron K"
    using h\<sigma>1K unfolding geotop_polyhedron_def by (by100 blast)
  have h\<sigma>2subM: "\<sigma>2 \<subseteq> geotop_polyhedron K"
    using h\<sigma>2K unfolding geotop_polyhedron_def by (by100 blast)
  have h\<sigma>12_local_U: "ball p rU \<inter> (\<sigma>1 \<union> \<sigma>2) \<subseteq> U"
  proof
    fix x
    assume hx: "x \<in> ball p rU \<inter> (\<sigma>1 \<union> \<sigma>2)"
    have hxM: "x \<in> geotop_polyhedron K"
      using hx h\<sigma>1subM h\<sigma>2subM by (by100 blast)
    have hxball: "x \<in> ball p rU"
      using hx by (by100 blast)
    have "x \<in> geotop_polyhedron K \<inter> ball p rU"
      using hxM hxball by (by100 blast)
    thus "x \<in> U"
      using hballU by (by100 blast)
  qed
  have hedge12_interior: "rel_interior e \<subseteq> interior (\<sigma>1 \<union> \<sigma>2)"
    by (rule geotop_complex_two_2simplex_shared_edge_rel_interior_subset_HOL_interior_union_dev34
        [OF hK h\<sigma>1K h\<sigma>2K h\<sigma>1dim h\<sigma>2dim h12 h\<sigma>1face h\<sigma>2face hedge])
  have hp_interior12: "p \<in> interior (\<sigma>1 \<union> \<sigma>2)"
    using hedge12_interior hp by (by100 blast)
  obtain eps12 where heps12: "0 < eps12"
    and hball12: "ball p eps12 \<subseteq> \<sigma>1 \<union> \<sigma>2"
  proof -
    have hballs_int:
      "\<forall>x\<in>interior (\<sigma>1 \<union> \<sigma>2).
        \<exists>e>0. ball x e \<subseteq> interior (\<sigma>1 \<union> \<sigma>2)"
      using open_interior open_contains_ball[of "interior (\<sigma>1 \<union> \<sigma>2)"]
      by (by100 simp)
    obtain e12 where he12: "0 < e12"
      and hball12_int: "ball p e12 \<subseteq> interior (\<sigma>1 \<union> \<sigma>2)"
      using hballs_int hp_interior12 by (by100 blast)
    have hball12_union: "ball p e12 \<subseteq> \<sigma>1 \<union> \<sigma>2"
      using hball12_int interior_subset by (by100 blast)
    show ?thesis
      by (rule that[OF he12 hball12_union])
  qed
  define eps where "eps = min rU eps12 / 2"
  have heps: "0 < eps"
    using hrU heps12 unfolding eps_def by (by100 simp)
  have heps_lt_rU: "eps < rU"
    using hrU heps12 unfolding eps_def by (by100 simp)
  have heps_lt_eps12: "eps < eps12"
    using hrU heps12 unfolding eps_def by (by100 simp)
  have hsphere_ball_rU: "sphere p eps \<subseteq> ball p rU"
  proof
    fix x
    assume hx: "x \<in> sphere p eps"
    have "dist p x = eps"
      using hx by (by100 simp)
    hence "dist p x < rU"
      using heps_lt_rU by (by100 simp)
    thus "x \<in> ball p rU"
      by (by100 simp)
  qed
  have hsphere_ball12: "sphere p eps \<subseteq> ball p eps12"
  proof
    fix x
    assume hx: "x \<in> sphere p eps"
    have "dist p x = eps"
      using hx by (by100 simp)
    hence "dist p x < eps12"
      using heps_lt_eps12 by (by100 simp)
    thus "x \<in> ball p eps12"
      by (by100 simp)
  qed
  have hsphere_union12: "sphere p eps \<subseteq> \<sigma>1 \<union> \<sigma>2"
    using hsphere_ball12 hball12 by (by100 blast)
  have hsphere_U: "sphere p eps \<subseteq> U"
  proof -
    have "sphere p eps \<subseteq> ball p rU \<inter> (\<sigma>1 \<union> \<sigma>2)"
      using hsphere_ball_rU hsphere_union12 by (by100 blast)
    thus ?thesis
      using h\<sigma>12_local_U by (by100 blast)
  qed
  have hsphere_1sphere: "geotop_is_n_sphere (sphere p eps)
      (subspace_topology UNIV geotop_euclidean_topology (sphere p eps)) 1"
    by (rule geotop_positive_radius_circle_is_1sphere_dev34[OF heps])
  show ?thesis
    using hsphere_U hsphere_1sphere by (by100 blast)
qed

lemma geotop_three_incident_2simplex_small_circle_radius_sphere_exists_dev34:
  fixes K :: "(real^2) set set" and e U :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hfaces:
    "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
      \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
      \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
      \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
  assumes hlocal_ball: "\<exists>r>0. geotop_polyhedron K \<inter> ball p r \<subseteq> U"
  shows "\<exists>eps. 0 < eps
      \<and> sphere p eps \<subseteq> U
      \<and> geotop_is_n_sphere (sphere p eps)
          (subspace_topology UNIV geotop_euclidean_topology (sphere p eps)) 1"
  (**
    Radius-explicit export of the same Moise Lemma 4 circle choice.  This keeps
    the later chart/Jordan proof tied to the actual small circle centered at
    the edge-interior point, rather than an opaque existential 1-sphere. **)
proof -
  have hp_e: "p \<in> e"
    using hp rel_interior_subset by (by100 blast)
  obtain rU where hrU: "0 < rU"
    and hballU: "geotop_polyhedron K \<inter> ball p rU \<subseteq> U"
    using hlocal_ball by (by100 blast)
  obtain \<sigma>1 \<sigma>2 \<sigma>3 where hfaces_data:
      "\<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
      \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
      \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
      \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
    using hfaces by (elim exE)
  have h12: "\<sigma>1 \<noteq> \<sigma>2"
    using hfaces_data by (by100 simp)
  have h\<sigma>1K: "\<sigma>1 \<in> K"
    using hfaces_data by (by100 simp)
  have h\<sigma>1dim: "geotop_simplex_dim \<sigma>1 2"
    using hfaces_data by (by100 simp)
  have h\<sigma>1face: "geotop_is_face e \<sigma>1"
    using hfaces_data by (by100 simp)
  have h\<sigma>2K: "\<sigma>2 \<in> K"
    using hfaces_data by (by100 simp)
  have h\<sigma>2dim: "geotop_simplex_dim \<sigma>2 2"
    using hfaces_data by (by100 simp)
  have h\<sigma>2face: "geotop_is_face e \<sigma>2"
    using hfaces_data by (by100 simp)
  have h\<sigma>1subM: "\<sigma>1 \<subseteq> geotop_polyhedron K"
    using h\<sigma>1K unfolding geotop_polyhedron_def by (by100 blast)
  have h\<sigma>2subM: "\<sigma>2 \<subseteq> geotop_polyhedron K"
    using h\<sigma>2K unfolding geotop_polyhedron_def by (by100 blast)
  have h\<sigma>12_local_U: "ball p rU \<inter> (\<sigma>1 \<union> \<sigma>2) \<subseteq> U"
  proof
    fix x
    assume hx: "x \<in> ball p rU \<inter> (\<sigma>1 \<union> \<sigma>2)"
    have hxM: "x \<in> geotop_polyhedron K"
      using hx h\<sigma>1subM h\<sigma>2subM by (by100 blast)
    have hxball: "x \<in> ball p rU"
      using hx by (by100 blast)
    have "x \<in> geotop_polyhedron K \<inter> ball p rU"
      using hxM hxball by (by100 blast)
    thus "x \<in> U"
      using hballU by (by100 blast)
  qed
  have hedge12_interior: "rel_interior e \<subseteq> interior (\<sigma>1 \<union> \<sigma>2)"
    by (rule geotop_complex_two_2simplex_shared_edge_rel_interior_subset_HOL_interior_union_dev34
        [OF hK h\<sigma>1K h\<sigma>2K h\<sigma>1dim h\<sigma>2dim h12 h\<sigma>1face h\<sigma>2face hedge])
  have hp_interior12: "p \<in> interior (\<sigma>1 \<union> \<sigma>2)"
    using hedge12_interior hp by (by100 blast)
  obtain eps12 where heps12: "0 < eps12"
    and hball12: "ball p eps12 \<subseteq> \<sigma>1 \<union> \<sigma>2"
  proof -
    have hballs_int:
      "\<forall>x\<in>interior (\<sigma>1 \<union> \<sigma>2).
        \<exists>e>0. ball x e \<subseteq> interior (\<sigma>1 \<union> \<sigma>2)"
      using open_interior open_contains_ball[of "interior (\<sigma>1 \<union> \<sigma>2)"]
      by (by100 simp)
    obtain e12 where he12: "0 < e12"
      and hball12_int: "ball p e12 \<subseteq> interior (\<sigma>1 \<union> \<sigma>2)"
      using hballs_int hp_interior12 by (by100 blast)
    have hball12_union: "ball p e12 \<subseteq> \<sigma>1 \<union> \<sigma>2"
      using hball12_int interior_subset by (by100 blast)
    show ?thesis
      by (rule that[OF he12 hball12_union])
  qed
  define eps where "eps = min rU eps12 / 2"
  have heps: "0 < eps"
    using hrU heps12 unfolding eps_def by (by100 simp)
  have heps_lt_rU: "eps < rU"
    using hrU heps12 unfolding eps_def by (by100 simp)
  have heps_lt_eps12: "eps < eps12"
    using hrU heps12 unfolding eps_def by (by100 simp)
  have hsphere_ball_rU: "sphere p eps \<subseteq> ball p rU"
  proof
    fix x
    assume hx: "x \<in> sphere p eps"
    have "dist p x = eps"
      using hx by (by100 simp)
    hence "dist p x < rU"
      using heps_lt_rU by (by100 simp)
    thus "x \<in> ball p rU"
      by (by100 simp)
  qed
  have hsphere_ball12: "sphere p eps \<subseteq> ball p eps12"
  proof
    fix x
    assume hx: "x \<in> sphere p eps"
    have "dist p x = eps"
      using hx by (by100 simp)
    hence "dist p x < eps12"
      using heps_lt_eps12 by (by100 simp)
    thus "x \<in> ball p eps12"
      by (by100 simp)
  qed
  have hsphere_union12: "sphere p eps \<subseteq> \<sigma>1 \<union> \<sigma>2"
    using hsphere_ball12 hball12 by (by100 blast)
  have hsphere_U: "sphere p eps \<subseteq> U"
  proof -
    have "sphere p eps \<subseteq> ball p rU \<inter> (\<sigma>1 \<union> \<sigma>2)"
      using hsphere_ball_rU hsphere_union12 by (by100 blast)
    thus ?thesis
      using h\<sigma>12_local_U by (by100 blast)
  qed
  have hsphere_1sphere: "geotop_is_n_sphere (sphere p eps)
      (subspace_topology UNIV geotop_euclidean_topology (sphere p eps)) 1"
    by (rule geotop_positive_radius_circle_is_1sphere_dev34[OF heps])
  show ?thesis
    using heps hsphere_U hsphere_1sphere by (by100 blast)
qed

lemma geotop_three_incident_small_circle_complement_connected_explicit_dev34:
  fixes K F :: "(real^2) set set"
  fixes e \<sigma>1 \<sigma>2 \<sigma>3 U :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hFfin: "finite F"
  assumes hFsub: "F \<subseteq> K"
  assumes h12: "\<sigma>1 \<noteq> \<sigma>2"
  assumes h23: "\<sigma>2 \<noteq> \<sigma>3"
  assumes h13: "\<sigma>1 \<noteq> \<sigma>3"
  assumes h\<sigma>1K: "\<sigma>1 \<in> K"
  assumes h\<sigma>1dim: "geotop_simplex_dim \<sigma>1 2"
  assumes h\<sigma>1face: "geotop_is_face e \<sigma>1"
  assumes h\<sigma>2K: "\<sigma>2 \<in> K"
  assumes h\<sigma>2dim: "geotop_simplex_dim \<sigma>2 2"
  assumes h\<sigma>2face: "geotop_is_face e \<sigma>2"
  assumes h\<sigma>3K: "\<sigma>3 \<in> K"
  assumes h\<sigma>3dim: "geotop_simplex_dim \<sigma>3 2"
  assumes h\<sigma>3face: "geotop_is_face e \<sigma>3"
  assumes hs: "0 < s"
  assumes heps: "0 < eps"
  assumes heps_lt_s: "eps < s"
  assumes hballU_s: "geotop_polyhedron K \<inter> ball p s \<subseteq> U"
  assumes hpoint_carriers_s:
    "ball p s \<inter> geotop_polyhedron K \<subseteq> \<Union>{\<tau>\<in>F. p \<in> \<tau>}"
  assumes h\<sigma>123_local_U: "ball p s \<inter> (\<sigma>1 \<union> \<sigma>2 \<union> \<sigma>3) \<subseteq> U"
  assumes hUsubM: "U \<subseteq> geotop_polyhedron K"
  assumes hsphere_union12: "sphere p eps \<subseteq> \<sigma>1 \<union> \<sigma>2"
  assumes hsphere_U: "sphere p eps \<subseteq> U"
  shows "top1_connected_on (U - sphere p eps)
      (subspace_topology UNIV geotop_euclidean_topology (U - sphere p eps))"
  (**
    Explicit Moise Lemma 4 local geometry.  The small circle is chosen in the
    union of two incident half-neighborhoods, and the third incident
    2-simplex supplies the passage joining the two sides in the punctured
    chart domain. **)
proof -
  have False
    by (rule geotop_complex_no_three_2simplexes_share_edge_dev34
        [OF hK hedge h12 h23 h13 h\<sigma>1K h\<sigma>1dim h\<sigma>1face
          h\<sigma>2K h\<sigma>2dim h\<sigma>2face h\<sigma>3K h\<sigma>3dim h\<sigma>3face])
  thus ?thesis
    by (by100 blast)
qed

lemma geotop_three_incident_2simplex_small_circle_radius_not_separates_chart_dev34:
  fixes K :: "(real^2) set set" and e U :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hfaces:
    "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
      \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
      \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
      \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
  assumes hlocal_ball: "\<exists>r>0. geotop_polyhedron K \<inter> ball p r \<subseteq> U"
  assumes hUsubM: "U \<subseteq> geotop_polyhedron K"
  shows "\<exists>eps. 0 < eps
      \<and> sphere p eps \<subseteq> U
      \<and> geotop_is_n_sphere (sphere p eps)
          (subspace_topology UNIV geotop_euclidean_topology (sphere p eps)) 1
      \<and> top1_connected_on (U - sphere p eps)
          (subspace_topology UNIV geotop_euclidean_topology (U - sphere p eps))"
  (**
    Moise Lemma 4 local picture: from three incident 2-simplexes, choose two
    same-radius small semicircles in two of the incident simplexes, centered at
    the edge-interior point.  Their union is the small 1-sphere \<open>J\<close> inside the
    subspace chart domain \<open>U \<subseteq> |K|\<close>; because the third incident simplex gives
    a passage around it, \<open>U - J\<close> remains connected. **)
proof -
  have hp_e: "p \<in> e"
    using hp rel_interior_subset by (by100 blast)
  obtain rU where hrU: "0 < rU"
    and hballU: "geotop_polyhedron K \<inter> ball p rU \<subseteq> U"
    using hlocal_ball by (by100 blast)
  obtain rK F \<sigma>1 \<sigma>2 \<sigma>3 where hrK: "0 < rK"
    and hFfin: "finite F"
    and hFsub: "F \<subseteq> K"
    and heF: "e \<in> F"
    and h\<sigma>1F: "\<sigma>1 \<in> F"
    and h\<sigma>2F: "\<sigma>2 \<in> F"
    and h\<sigma>3F: "\<sigma>3 \<in> F"
    and h12: "\<sigma>1 \<noteq> \<sigma>2"
    and h23: "\<sigma>2 \<noteq> \<sigma>3"
    and h13: "\<sigma>1 \<noteq> \<sigma>3"
    and h\<sigma>1K: "\<sigma>1 \<in> K"
    and h\<sigma>1dim: "geotop_simplex_dim \<sigma>1 2"
    and h\<sigma>1face: "geotop_is_face e \<sigma>1"
    and h\<sigma>2K: "\<sigma>2 \<in> K"
    and h\<sigma>2dim: "geotop_simplex_dim \<sigma>2 2"
    and h\<sigma>2face: "geotop_is_face e \<sigma>2"
    and h\<sigma>3K: "\<sigma>3 \<in> K"
    and h\<sigma>3dim: "geotop_simplex_dim \<sigma>3 2"
    and h\<sigma>3face: "geotop_is_face e \<sigma>3"
    and hcover: "ball p rK \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
    by (rule geotop_complex_three_edge_faces_point_finite_local_cover_dev34
        [OF hK heK hp_e hfaces])
  define r where "r = min rU rK"
  have hr: "0 < r"
    using hrU hrK unfolding r_def by (by100 simp)
  have hballU_r: "geotop_polyhedron K \<inter> ball p r \<subseteq> U"
  proof -
    have hball_sub: "ball p r \<subseteq> ball p rU"
      unfolding r_def by (by100 auto)
    have "geotop_polyhedron K \<inter> ball p r
        \<subseteq> geotop_polyhedron K \<inter> ball p rU"
      using hball_sub by (by100 blast)
    thus ?thesis
      using hballU by (by100 blast)
  qed
  have hcover_r: "ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
  proof -
    have hball_sub: "ball p r \<subseteq> ball p rK"
      unfolding r_def by (by100 auto)
    have "ball p r \<inter> geotop_polyhedron K
        \<subseteq> ball p rK \<inter> geotop_polyhedron K"
      using hball_sub by (by100 blast)
    thus ?thesis
      using hcover by (by100 blast)
  qed
  have hp_unionF: "p \<in> \<Union>F"
    using heF hp_e by (by100 blast)
  obtain \<delta> where h\<delta>: "0 < \<delta>"
    and hisolate: "ball p \<delta> \<inter> \<Union>F \<subseteq> \<Union>{\<tau>\<in>F. p \<in> \<tau>}"
    using geotop_complex_finite_subcomplex_local_point_carriers_dev34
      [OF hK hFfin hFsub hp_unionF]
    by (by100 blast)
  define s where "s = min r \<delta>"
  have hs: "0 < s"
    using hr h\<delta> unfolding s_def by (by100 simp)
  have hballU_s: "geotop_polyhedron K \<inter> ball p s \<subseteq> U"
  proof -
    have hball_sub: "ball p s \<subseteq> ball p r"
      unfolding s_def by (by100 auto)
    have "geotop_polyhedron K \<inter> ball p s
        \<subseteq> geotop_polyhedron K \<inter> ball p r"
      using hball_sub by (by100 blast)
    thus ?thesis
      using hballU_r by (by100 blast)
  qed
  have hcover_s: "ball p s \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
  proof -
    have hball_sub: "ball p s \<subseteq> ball p r"
      unfolding s_def by (by100 auto)
    have "ball p s \<inter> geotop_polyhedron K
        \<subseteq> ball p r \<inter> geotop_polyhedron K"
      using hball_sub by (by100 blast)
    thus ?thesis
      using hcover_r by (by100 blast)
  qed
  have hpoint_carriers_s:
    "ball p s \<inter> geotop_polyhedron K \<subseteq> \<Union>{\<tau>\<in>F. p \<in> \<tau>}"
  proof
    fix x
    assume hx: "x \<in> ball p s \<inter> geotop_polyhedron K"
    have hxF: "x \<in> \<Union>F"
      using hcover_s hx by (by100 blast)
    have hball_sub: "ball p s \<subseteq> ball p \<delta>"
      unfolding s_def by (by100 auto)
    have hx\<delta>: "x \<in> ball p \<delta>"
      using hx hball_sub by (by100 blast)
    have "x \<in> ball p \<delta> \<inter> \<Union>F"
      using hxF hx\<delta> by (by100 blast)
    thus "x \<in> \<Union>{\<tau>\<in>F. p \<in> \<tau>}"
      using hisolate by (by100 blast)
  qed
  have hp_\<sigma>1: "p \<in> \<sigma>1"
    using geotop_is_face_imp_subset[OF h\<sigma>1face] hp_e by (by100 blast)
  have hp_\<sigma>2: "p \<in> \<sigma>2"
    using geotop_is_face_imp_subset[OF h\<sigma>2face] hp_e by (by100 blast)
  have hp_\<sigma>3: "p \<in> \<sigma>3"
    using geotop_is_face_imp_subset[OF h\<sigma>3face] hp_e by (by100 blast)
  have h\<sigma>1subM: "\<sigma>1 \<subseteq> geotop_polyhedron K"
    using h\<sigma>1K unfolding geotop_polyhedron_def by (by100 blast)
  have h\<sigma>2subM: "\<sigma>2 \<subseteq> geotop_polyhedron K"
    using h\<sigma>2K unfolding geotop_polyhedron_def by (by100 blast)
  have h\<sigma>3subM: "\<sigma>3 \<subseteq> geotop_polyhedron K"
    using h\<sigma>3K unfolding geotop_polyhedron_def by (by100 blast)
  have h\<sigma>1_local_U: "ball p s \<inter> \<sigma>1 \<subseteq> U"
  proof -
    have "ball p s \<inter> \<sigma>1 \<subseteq> geotop_polyhedron K \<inter> ball p s"
      using h\<sigma>1subM by (by100 blast)
    thus ?thesis
      using hballU_s by (by100 blast)
  qed
  have h\<sigma>2_local_U: "ball p s \<inter> \<sigma>2 \<subseteq> U"
  proof -
    have "ball p s \<inter> \<sigma>2 \<subseteq> geotop_polyhedron K \<inter> ball p s"
      using h\<sigma>2subM by (by100 blast)
    thus ?thesis
      using hballU_s by (by100 blast)
  qed
  have h\<sigma>3_local_U: "ball p s \<inter> \<sigma>3 \<subseteq> U"
  proof -
    have "ball p s \<inter> \<sigma>3 \<subseteq> geotop_polyhedron K \<inter> ball p s"
      using h\<sigma>3subM by (by100 blast)
    thus ?thesis
      using hballU_s by (by100 blast)
  qed
  have h\<sigma>12_local_U: "ball p s \<inter> (\<sigma>1 \<union> \<sigma>2) \<subseteq> U"
    using h\<sigma>1_local_U h\<sigma>2_local_U by (by100 blast)
  have h\<sigma>123_local_U: "ball p s \<inter> (\<sigma>1 \<union> \<sigma>2 \<union> \<sigma>3) \<subseteq> U"
    using h\<sigma>1_local_U h\<sigma>2_local_U h\<sigma>3_local_U by (by100 blast)
  have hedge12_interior: "rel_interior e \<subseteq> interior (\<sigma>1 \<union> \<sigma>2)"
    by (rule geotop_complex_two_2simplex_shared_edge_rel_interior_subset_HOL_interior_union_dev34
        [OF hK h\<sigma>1K h\<sigma>2K h\<sigma>1dim h\<sigma>2dim h12 h\<sigma>1face h\<sigma>2face hedge])
  have hedge13_interior: "rel_interior e \<subseteq> interior (\<sigma>1 \<union> \<sigma>3)"
    by (rule geotop_complex_two_2simplex_shared_edge_rel_interior_subset_HOL_interior_union_dev34
        [OF hK h\<sigma>1K h\<sigma>3K h\<sigma>1dim h\<sigma>3dim h13 h\<sigma>1face h\<sigma>3face hedge])
  have hedge23_interior: "rel_interior e \<subseteq> interior (\<sigma>2 \<union> \<sigma>3)"
    by (rule geotop_complex_two_2simplex_shared_edge_rel_interior_subset_HOL_interior_union_dev34
        [OF hK h\<sigma>2K h\<sigma>3K h\<sigma>2dim h\<sigma>3dim h23 h\<sigma>2face h\<sigma>3face hedge])
  have hp_interior12: "p \<in> interior (\<sigma>1 \<union> \<sigma>2)"
    using hedge12_interior hp by (by100 blast)
  obtain eps12 where heps12: "0 < eps12"
    and hball12: "ball p eps12 \<subseteq> \<sigma>1 \<union> \<sigma>2"
  proof -
    have hballs_int:
      "\<forall>x\<in>interior (\<sigma>1 \<union> \<sigma>2).
        \<exists>e>0. ball x e \<subseteq> interior (\<sigma>1 \<union> \<sigma>2)"
      using open_interior open_contains_ball[of "interior (\<sigma>1 \<union> \<sigma>2)"]
      by (by100 simp)
    obtain e12 where he12: "0 < e12"
      and hball12_int: "ball p e12 \<subseteq> interior (\<sigma>1 \<union> \<sigma>2)"
      using hballs_int hp_interior12 by (by100 blast)
    have hball12_union: "ball p e12 \<subseteq> \<sigma>1 \<union> \<sigma>2"
      using hball12_int interior_subset by (by100 blast)
    show ?thesis
      by (rule that[OF he12 hball12_union])
  qed
  define eps where "eps = min s eps12 / 2"
  have heps: "0 < eps"
    using hs heps12 unfolding eps_def by (by100 simp)
  have heps_lt_s: "eps < s"
    using hs heps12 unfolding eps_def by (by100 simp)
  have heps_lt_eps12: "eps < eps12"
    using hs heps12 unfolding eps_def by (by100 simp)
  have hsphere_ball_s: "sphere p eps \<subseteq> ball p s"
  proof
    fix x
    assume hx: "x \<in> sphere p eps"
    have "dist p x = eps"
      using hx by (by100 simp)
    hence "dist p x < s"
      using heps_lt_s by (by100 simp)
    thus "x \<in> ball p s"
      by (by100 simp)
  qed
  have hsphere_ball12: "sphere p eps \<subseteq> ball p eps12"
  proof
    fix x
    assume hx: "x \<in> sphere p eps"
    have "dist p x = eps"
      using hx by (by100 simp)
    hence "dist p x < eps12"
      using heps_lt_eps12 by (by100 simp)
    thus "x \<in> ball p eps12"
      by (by100 simp)
  qed
  have hsphere_union12: "sphere p eps \<subseteq> \<sigma>1 \<union> \<sigma>2"
    using hsphere_ball12 hball12 by (by100 blast)
  have hsphere_U: "sphere p eps \<subseteq> U"
    using hsphere_ball_s hsphere_union12 h\<sigma>12_local_U by (by100 blast)
  have hsphere_1sphere: "geotop_is_n_sphere (sphere p eps)
      (subspace_topology UNIV geotop_euclidean_topology (sphere p eps)) 1"
    by (rule geotop_positive_radius_circle_is_1sphere_dev34[OF heps])
  have hsphere_complement_connected:
    "top1_connected_on (U - sphere p eps)
      (subspace_topology UNIV geotop_euclidean_topology (U - sphere p eps))"
    by (rule geotop_three_incident_small_circle_complement_connected_explicit_dev34
        [OF hK heK hedge hp hFfin hFsub h12 h23 h13
          h\<sigma>1K h\<sigma>1dim h\<sigma>1face h\<sigma>2K h\<sigma>2dim h\<sigma>2face
          h\<sigma>3K h\<sigma>3dim h\<sigma>3face hs heps heps_lt_s hballU_s
          hpoint_carriers_s h\<sigma>123_local_U hUsubM hsphere_union12 hsphere_U])
  (**
    Remaining Moise Lemma 4 geometry: choose a small circle from two incident
    half-neighborhoods and use the third incident 2-simplex to connect the
    complement in \<open>U\<close>. **)
  show ?thesis
    using heps hsphere_U hsphere_1sphere hsphere_complement_connected by (by100 blast)
qed

lemma geotop_three_incident_2simplex_small_circle_domain_not_separates_chart_dev34:
  fixes K :: "(real^2) set set" and e U J :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hfaces:
    "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
      \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
      \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
      \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
  assumes hlocal_ball: "\<exists>r>0. geotop_polyhedron K \<inter> ball p r \<subseteq> U"
  assumes hUsubM: "U \<subseteq> geotop_polyhedron K"
  shows "\<exists>J. J \<subseteq> U
      \<and> geotop_is_n_sphere J
          (subspace_topology UNIV geotop_euclidean_topology J) 1
      \<and> top1_connected_on (U - J)
          (subspace_topology UNIV geotop_euclidean_topology (U - J))"
  (**
    Existential-set form of the radius-explicit Moise Lemma 4 local circle. **)
proof -
  obtain eps where heps: "0 < eps"
    and hsphereU: "sphere p eps \<subseteq> U"
    and hsphere: "geotop_is_n_sphere (sphere p eps)
      (subspace_topology UNIV geotop_euclidean_topology (sphere p eps)) 1"
    and hconn: "top1_connected_on (U - sphere p eps)
      (subspace_topology UNIV geotop_euclidean_topology (U - sphere p eps))"
    using geotop_three_incident_2simplex_small_circle_radius_not_separates_chart_dev34
      [OF hK heK hedge hp hfaces hlocal_ball hUsubM]
    by (by100 blast)
  show ?thesis
    using hsphereU hsphere hconn by (by100 blast)
qed

lemma geotop_three_incident_2simplex_small_circle_not_separates_chart_dev34:
  fixes K :: "(real^2) set set" and e U J :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hfaces:
    "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
      \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
      \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
      \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
  assumes hlocal_ball: "\<exists>r>0. geotop_polyhedron K \<inter> ball p r \<subseteq> U"
  assumes hUsubM: "U \<subseteq> geotop_polyhedron K"
  assumes hhomeo: "top1_homeomorphism_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
  shows "\<exists>J. J \<subseteq> U
      \<and> geotop_is_n_sphere (f ` J)
          (subspace_topology UNIV geotop_euclidean_topology (f ` J)) 1
      \<and> top1_connected_on (U - J)
          (subspace_topology UNIV geotop_euclidean_topology (U - J))"
proof -
  obtain J where hJsub: "J \<subseteq> U"
    and hJsphere: "geotop_is_n_sphere J
          (subspace_topology UNIV geotop_euclidean_topology J) 1"
    and hJconn: "top1_connected_on (U - J)
          (subspace_topology UNIV geotop_euclidean_topology (U - J))"
    using geotop_three_incident_2simplex_small_circle_domain_not_separates_chart_dev34
      [OF hK heK hedge hp hfaces hlocal_ball hUsubM]
    by (by100 blast)
  have hJimg: "geotop_is_n_sphere (f ` J)
      (subspace_topology UNIV geotop_euclidean_topology (f ` J)) 1"
    by (rule geotop_homeomorphism_image_1sphere_dev34[OF hhomeo hJsub hJsphere])
  show ?thesis
    using hJsub hJimg hJconn by (by100 blast)
qed

lemma geotop_unique_incident_2simplex_semicircle_separates_chart_dev34:
  fixes K :: "(real^2) set set" and e U A :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hunique:
    "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  assumes hUopen: "openin_on (geotop_polyhedron K)
      (top1_metric_topology_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y))) U"
  assumes hpU: "p \<in> U"
  assumes hhomeo: "top1_homeomorphism_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
  shows "\<exists>A. A \<subseteq> U
      \<and> geotop_is_arc (f ` A)
          (subspace_topology UNIV geotop_euclidean_topology (f ` A))
      \<and> \<not> top1_connected_on (U - A)
          (subspace_topology UNIV geotop_euclidean_topology (U - A))"
proof -
  let ?M = "geotop_polyhedron K"
  have hlocal_ball: "\<exists>r>0. ?M \<inter> ball p r \<subseteq> U"
    by (rule geotop_openin_norm_polyhedron_contains_relative_ball_dev34
        [OF hUopen hpU])
  have hUsubM: "U \<subseteq> ?M"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hsemicircle:
    "\<exists>A. A \<subseteq> U
      \<and> geotop_is_arc (f ` A)
          (subspace_topology UNIV geotop_euclidean_topology (f ` A))
      \<and> \<not> top1_connected_on (U - A)
          (subspace_topology UNIV geotop_euclidean_topology (U - A))"
    by (rule geotop_unique_incident_2simplex_small_semicircle_separates_chart_dev34
        [OF hK heK hedge hp hunique hlocal_ball hUsubM hhomeo])
  show ?thesis
    using hsemicircle by (by100 blast)
qed

lemma geotop_three_incident_2simplex_sphere_not_separates_chart_dev34:
  fixes K :: "(real^2) set set" and e U J :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hfaces:
    "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
      \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
      \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
      \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
  assumes hUopen: "openin_on (geotop_polyhedron K)
      (top1_metric_topology_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y))) U"
  assumes hpU: "p \<in> U"
  assumes hhomeo: "top1_homeomorphism_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
  shows "\<exists>J. J \<subseteq> U
      \<and> geotop_is_n_sphere (f ` J)
          (subspace_topology UNIV geotop_euclidean_topology (f ` J)) 1
      \<and> top1_connected_on (U - J)
          (subspace_topology UNIV geotop_euclidean_topology (U - J))"
proof -
  let ?M = "geotop_polyhedron K"
  have hlocal_ball: "\<exists>r>0. ?M \<inter> ball p r \<subseteq> U"
    by (rule geotop_openin_norm_polyhedron_contains_relative_ball_dev34
        [OF hUopen hpU])
  have hUsubM: "U \<subseteq> ?M"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hcircle:
    "\<exists>J. J \<subseteq> U
      \<and> geotop_is_n_sphere (f ` J)
          (subspace_topology UNIV geotop_euclidean_topology (f ` J)) 1
      \<and> top1_connected_on (U - J)
          (subspace_topology UNIV geotop_euclidean_topology (U - J))"
    by (rule geotop_three_incident_2simplex_small_circle_not_separates_chart_dev34
        [OF hK heK hedge hp hfaces hlocal_ball hUsubM hhomeo])
  show ?thesis
    using hcircle by (by100 blast)
qed

lemma geotop_1sphere_Jordan_open_components_dev34:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J
      (subspace_topology UNIV geotop_euclidean_topology J) 1"
  obtains inner outer where
    "inner \<noteq> {}"
    "open inner"
    "connected inner"
    "bounded inner"
    "outer \<noteq> {}"
    "open outer"
    "connected outer"
    "\<not> bounded outer"
    "inner \<inter> outer = {}"
    "inner \<union> outer = UNIV - J"
  (**
    Export the open Jordan-side data used by the local chart transfer.  The
    cached Jordan component theorem already proves this internally; the active
    layer needs the open, disjoint, and cover facts explicitly. **)
proof -
  obtain c :: "real \<Rightarrow> real^2" where hc_simple: "simple_path c"
      and hc_loop: "pathfinish c = pathstart c"
      and hc_image: "path_image c = J"
    by (rule geotop_1sphere_simple_closed_path_R2[OF hJ])
  obtain inner outer where hinner_ne: "inner \<noteq> {}"
      and hinner_open: "open inner"
      and hinner_conn: "connected inner"
      and houter_ne: "outer \<noteq> {}"
      and houter_open: "open outer"
      and houter_conn: "connected outer"
      and hinner_bdd: "bounded inner"
      and houter_unbdd: "\<not> bounded outer"
      and hdisj: "inner \<inter> outer = {}"
      and hcover: "inner \<union> outer = - path_image c"
      and hfront_inner: "frontier inner = path_image c"
      and hfront_outer: "frontier outer = path_image c"
    by (rule Jordan_curve_real2[OF hc_simple hc_loop])
  have hcover_J: "inner \<union> outer = UNIV - J"
    using hcover hc_image by (by100 auto)
  show ?thesis
    by (rule that[OF hinner_ne hinner_open hinner_conn hinner_bdd
          houter_ne houter_open houter_conn houter_unbdd hdisj hcover_J])
qed

lemma geotop_jordan_components_separate_subset_dev34:
  fixes V J inner outer :: "(real^2) set"
  assumes hinner_open: "open inner"
  assumes houter_open: "open outer"
  assumes hinner_ne: "inner \<noteq> {}"
  assumes hVouter_ne: "V \<inter> outer \<noteq> {}"
  assumes hdisj: "inner \<inter> outer = {}"
  assumes hcover: "inner \<union> outer = UNIV - J"
  assumes hinner_subV: "inner \<subseteq> V"
  shows "\<not> top1_connected_on (V - J)
      (subspace_topology UNIV geotop_euclidean_topology (V - J))"
  (**
    Relative form of the local Jordan bookkeeping: if the chosen chart domain
    contains one Jordan side and meets the other, then the curve separates the
    domain.  No plane-openness of \<open>V\<close> is needed; the two pieces are open in
    the subspace \<open>V - J\<close>. **)
proof -
  have hinner_sub: "inner \<subseteq> V - J"
    using hcover hinner_subV by (by100 blast)
  have houter_piece_sub: "V \<inter> outer \<subseteq> V - J"
    using hcover by (by100 blast)
  have hcoverV: "inner \<union> (V \<inter> outer) = V - J"
    using hcover hinner_subV by (by100 blast)
  have hinner_open_sub: "inner \<in>
      subspace_topology UNIV geotop_euclidean_topology (V - J)"
  proof -
    have hinner_geo: "inner \<in> geotop_euclidean_topology"
      using hinner_open
      unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    have hrepr: "inner = (V - J) \<inter> inner"
      using hinner_sub by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hinner_geo hrepr by (by100 blast)
  qed
  have houter_open_sub: "V \<inter> outer \<in>
      subspace_topology UNIV geotop_euclidean_topology (V - J)"
  proof -
    have houter_geo: "outer \<in> geotop_euclidean_topology"
      using houter_open
      unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    have hrepr: "V \<inter> outer = (V - J) \<inter> outer"
      using houter_piece_sub by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using houter_geo hrepr by (by100 blast)
  qed
  have hdisjV: "inner \<inter> (V \<inter> outer) = {}"
    using hdisj by (by100 blast)
  show ?thesis
    by (rule top1_open_cover_separation_imp_not_connected_dev34
        [OF hinner_open_sub houter_open_sub hinner_ne hVouter_ne hdisjV hcoverV])
qed

lemma geotop_open_set_jordan_components_separate_subset_dev34:
  fixes V J inner outer :: "(real^2) set"
  assumes hVopen: "V \<in> geotop_euclidean_topology"
  assumes hinner_open: "open inner"
  assumes houter_open: "open outer"
  assumes hinner_ne: "inner \<noteq> {}"
  assumes hVouter_ne: "V \<inter> outer \<noteq> {}"
  assumes hdisj: "inner \<inter> outer = {}"
  assumes hcover: "inner \<union> outer = UNIV - J"
  assumes hinner_subV: "inner \<subseteq> V"
  shows "\<not> top1_connected_on (V - J)
      (subspace_topology UNIV geotop_euclidean_topology (V - J))"
  (**
    Local Jordan separation bookkeeping.  Once the bounded and unbounded
    Jordan components are known, any open set containing one side and meeting
    the other is split by the curve into the two relative-open pieces
    \<open>inner\<close> and \<open>V \<inter> outer\<close>. **)
proof -
  have hinner_sub: "inner \<subseteq> V - J"
    using hcover hinner_subV by (by100 blast)
  have houter_piece_sub: "V \<inter> outer \<subseteq> V - J"
    using hcover by (by100 blast)
  have hcoverV: "inner \<union> (V \<inter> outer) = V - J"
    using hcover hinner_subV by (by100 blast)
  have hinner_open_sub: "inner \<in>
      subspace_topology UNIV geotop_euclidean_topology (V - J)"
  proof -
    have hinner_geo: "inner \<in> geotop_euclidean_topology"
      using hinner_open
      unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    have hrepr: "inner = (V - J) \<inter> inner"
      using hinner_sub by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hinner_geo hrepr by (by100 blast)
  qed
  have houter_open_sub: "V \<inter> outer \<in>
      subspace_topology UNIV geotop_euclidean_topology (V - J)"
  proof -
    have hV_HOL: "open V"
      using hVopen
      unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    have hVouter_open: "open (V \<inter> outer)"
      by (rule open_Int[OF hV_HOL houter_open])
    have hVouter_geo: "V \<inter> outer \<in> geotop_euclidean_topology"
      using hVouter_open
      unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    have hrepr: "V \<inter> outer = (V - J) \<inter> (V \<inter> outer)"
      using houter_piece_sub by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hVouter_geo hrepr by (by100 blast)
  qed
  show ?thesis
  proof -
    have hdisjV: "inner \<inter> (V \<inter> outer) = {}"
      using hdisj by (by100 blast)
    show ?thesis
      by (rule top1_open_cover_separation_imp_not_connected_dev34
          [OF hinner_open_sub houter_open_sub hinner_ne hVouter_ne hdisjV hcoverV])
  qed
qed

lemma geotop_2cell_chart_open_domain_image_dev34:
  fixes M U \<sigma> :: "(real^2) set"
  assumes hUopen: "openin_on M
      (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U"
  assumes h\<phi>: "top1_homeomorphism_on
      (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U)
      (subspace_topology M (top1_metric_topology_on M (\<lambda>x y. norm (x - y)))
        (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U))
      \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<phi>"
  shows "\<phi> ` U \<in> subspace_topology UNIV geotop_euclidean_topology \<sigma>
      \<and> \<phi> ` U \<subseteq> \<sigma>"
  (**
    2-cell chart bookkeeping for the image-side Jordan step.  The chart is a
    homeomorphism on \<open>closure U\<close>; since \<open>U\<close> is open in the ambient
    polyhedron and lies in its closure, its image is open in the target
    2-simplex. **)
proof -
  let ?T = "top1_metric_topology_on M (\<lambda>x y. norm (x - y))"
  let ?C = "closure_on M ?T U"
  have hUsubM: "U \<subseteq> M"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hUmemT: "U \<in> ?T"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hUsubC: "U \<subseteq> ?C"
    by (rule subset_closure_on)
  have hUmemC: "U \<in> subspace_topology M ?T ?C"
  proof -
    have hrepr: "U = ?C \<inter> U"
      using hUsubC by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hUmemT hrepr by (by100 blast)
  qed
  have himage_open: "\<phi> ` U \<in> subspace_topology UNIV geotop_euclidean_topology \<sigma>"
    by (rule top1_homeomorphism_on_open_image[OF h\<phi> hUmemC hUsubC])
  have h\<phi>bij: "bij_betw \<phi> ?C \<sigma>"
    by (rule top1_homeomorphism_on_imp_bij[OF h\<phi>])
  have h\<phi>C: "\<phi> ` ?C = \<sigma>"
    using h\<phi>bij unfolding bij_betw_def by (by100 blast)
  have himage_sub: "\<phi> ` U \<subseteq> \<sigma>"
    using hUsubC h\<phi>C by (by100 blast)
  show ?thesis
    using himage_open himage_sub by (by100 blast)
qed

lemma geotop_2cell_chart_open_domain_image_bounded_dev34:
  fixes M U \<sigma> :: "(real^2) set"
  assumes hUopen: "openin_on M
      (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<phi>: "top1_homeomorphism_on
      (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U)
      (subspace_topology M (top1_metric_topology_on M (\<lambda>x y. norm (x - y)))
        (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U))
      \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<phi>"
  shows "bounded (\<phi> ` U)"
  (**
    Image-side bookkeeping for the local Jordan argument: the open chart image
    lies in the target 2-simplex, hence is bounded. **)
proof -
  have himage_data: "\<phi> ` U \<in> subspace_topology UNIV geotop_euclidean_topology \<sigma>
      \<and> \<phi> ` U \<subseteq> \<sigma>"
    by (rule geotop_2cell_chart_open_domain_image_dev34[OF hUopen h\<phi>])
  have himage_sub: "\<phi> ` U \<subseteq> \<sigma>"
    using himage_data by (by100 blast)
  have h\<sigma>_bounded: "bounded \<sigma>"
    by (rule geotop_simplex_dim_bounded_prefix[OF h\<sigma>2])
  show ?thesis
    using h\<sigma>_bounded himage_sub bounded_subset by (by100 blast)
qed

lemma geotop_2cell_chart_image_1sphere_dev34:
  fixes M U J \<sigma> :: "(real^2) set"
  assumes hUopen: "openin_on M
      (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U"
  assumes h\<phi>: "top1_homeomorphism_on
      (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U)
      (subspace_topology M (top1_metric_topology_on M (\<lambda>x y. norm (x - y)))
        (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U))
      \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<phi>"
  assumes hJsub: "J \<subseteq> U"
  assumes hJsphere: "geotop_is_n_sphere J
      (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "geotop_is_n_sphere (\<phi> ` J)
      (subspace_topology UNIV geotop_euclidean_topology (\<phi> ` J)) 1"
  (**
    Chart-image form of the book's local Jordan setup: the 2-cell chart used
    for \<open>closure U\<close> transports the chosen 1-sphere inside \<open>U\<close> to a
    1-sphere in the target simplex. **)
proof -
  let ?T = "top1_metric_topology_on M (\<lambda>x y. norm (x - y))"
  let ?C = "closure_on M ?T U"
  have hUsubM: "U \<subseteq> M"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hUsubC: "U \<subseteq> ?C"
    by (rule subset_closure_on)
  have hJsubC: "J \<subseteq> ?C"
    using hJsub hUsubC by (by100 blast)
  have hmetricM: "top1_metric_on M (\<lambda>x y. norm (x - y))"
    by (rule metric_on_subset[OF top1_norm_metric_on_UNIV_R2_dev34 subset_UNIV])
  have htopM: "is_topology_on M ?T"
    by (rule top1_metric_topology_on_is_topology_on[OF hmetricM])
  have hCsubM: "?C \<subseteq> M"
    by (rule closure_on_subset_carrier[OF htopM hUsubM])
  have hTM_eq: "?T = subspace_topology UNIV geotop_euclidean_topology M"
    by (rule top1_norm_metric_topology_on_eq_geotop_subspace_R2_dev34)
  have hsource_C_eq:
      "subspace_topology M ?T ?C =
       subspace_topology UNIV geotop_euclidean_topology ?C"
  proof -
    have htrans:
        "subspace_topology M
           (subspace_topology UNIV geotop_euclidean_topology M) ?C =
         subspace_topology UNIV geotop_euclidean_topology ?C"
      by (rule subspace_topology_trans[OF hCsubM])
    show ?thesis
      using hTM_eq htrans by (by100 simp)
  qed
  have hsource_J_eq:
      "subspace_topology ?C (subspace_topology M ?T ?C) J =
       subspace_topology UNIV geotop_euclidean_topology J"
  proof -
    have htrans:
        "subspace_topology ?C
           (subspace_topology UNIV geotop_euclidean_topology ?C) J =
         subspace_topology UNIV geotop_euclidean_topology J"
      by (rule subspace_topology_trans[OF hJsubC])
    show ?thesis
      using hsource_C_eq htrans by (by100 simp)
  qed
  have hres: "top1_homeomorphism_on J
      (subspace_topology ?C (subspace_topology M ?T ?C) J)
      (\<phi> ` J)
      (subspace_topology UNIV geotop_euclidean_topology (\<phi> ` J)) \<phi>"
  proof -
    have h\<phi>bij: "bij_betw \<phi> ?C \<sigma>"
      by (rule top1_homeomorphism_on_imp_bij[OF h\<phi>])
    have h\<phi>C: "\<phi> ` ?C = \<sigma>"
      using h\<phi>bij unfolding bij_betw_def by (by100 blast)
    have h\<phi>Jsub\<sigma>: "\<phi> ` J \<subseteq> \<sigma>"
      using hJsubC h\<phi>C by (by100 blast)
    have htarget_eq:
        "subspace_topology \<sigma>
           (subspace_topology UNIV geotop_euclidean_topology \<sigma>) (\<phi> ` J) =
         subspace_topology UNIV geotop_euclidean_topology (\<phi> ` J)"
      by (rule subspace_topology_trans[OF h\<phi>Jsub\<sigma>])
    have hres_raw: "top1_homeomorphism_on J
        (subspace_topology ?C (subspace_topology M ?T ?C) J)
        (\<phi> ` J)
        (subspace_topology \<sigma>
          (subspace_topology UNIV geotop_euclidean_topology \<sigma>) (\<phi> ` J)) \<phi>"
      by (rule top1_homeomorphism_on_subspace_image_dev34[OF h\<phi> hJsubC])
    show ?thesis
      using hres_raw htarget_eq by (by100 simp)
  qed
  have hres_geo: "top1_homeomorphism_on J
      (subspace_topology UNIV geotop_euclidean_topology J)
      (\<phi> ` J)
      (subspace_topology UNIV geotop_euclidean_topology (\<phi> ` J)) \<phi>"
    using hres hsource_J_eq by (by100 simp)
  obtain g where hg: "top1_homeomorphism_on J
      (subspace_topology UNIV geotop_euclidean_topology J)
      (geotop_std_sphere::(real^2) set)
      (subspace_topology UNIV geotop_euclidean_topology
        (geotop_std_sphere::(real^2) set)) g"
    using hJsphere unfolding geotop_is_n_sphere_def by (by100 blast)
  have hres_sym: "top1_homeomorphism_on (\<phi> ` J)
      (subspace_topology UNIV geotop_euclidean_topology (\<phi> ` J))
      J (subspace_topology UNIV geotop_euclidean_topology J) (inv_into J \<phi>)"
    by (rule top1_homeomorphism_on_sym[OF hres_geo])
  have hcomp: "top1_homeomorphism_on (\<phi> ` J)
      (subspace_topology UNIV geotop_euclidean_topology (\<phi> ` J))
      (geotop_std_sphere::(real^2) set)
      (subspace_topology UNIV geotop_euclidean_topology
        (geotop_std_sphere::(real^2) set))
      (g \<circ> inv_into J \<phi>)"
    by (rule top1_homeomorphism_on_comp[OF hres_sym hg])
  have htop_img: "is_topology_on (\<phi> ` J)
      (subspace_topology UNIV geotop_euclidean_topology (\<phi> ` J))"
    using hcomp unfolding top1_homeomorphism_on_def by (by100 blast)
  show ?thesis
    unfolding geotop_is_n_sphere_def
    using htop_img hcomp by (by100 blast)
qed

lemma geotop_2cell_chart_image_jordan_side_separation_dev34:
  fixes M U J \<sigma> :: "(real^2) set"
  assumes hUopen: "openin_on M
      (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U"
  assumes h\<phi>: "top1_homeomorphism_on
      (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U)
      (subspace_topology M (top1_metric_topology_on M (\<lambda>x y. norm (x - y)))
        (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U))
      \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<phi>"
  assumes hJsub: "J \<subseteq> U"
  assumes hJsphere: "geotop_is_n_sphere J
      (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes hside:
    "\<And>inner outer.
      inner \<noteq> {} \<Longrightarrow> open inner \<Longrightarrow> connected inner \<Longrightarrow> bounded inner \<Longrightarrow>
      outer \<noteq> {} \<Longrightarrow> open outer \<Longrightarrow> connected outer \<Longrightarrow> \<not> bounded outer \<Longrightarrow>
      inner \<inter> outer = {} \<Longrightarrow> inner \<union> outer = UNIV - (\<phi> ` J) \<Longrightarrow>
      inner \<subseteq> \<phi> ` U \<and> \<phi> ` U \<inter> outer \<noteq> {}"
  shows "\<not> top1_connected_on (\<phi> ` U - \<phi> ` J)
      (subspace_topology UNIV geotop_euclidean_topology (\<phi> ` U - \<phi> ` J))"
  (**
    Image-side Jordan criterion for a 2-cell chart.  After transporting the
    chosen 1-sphere to the target simplex, it remains only to show the chart
    image contains one Jordan side and meets the other; the relative
    separation split then gives non-connectedness. **)
proof -
  have hJimg: "geotop_is_n_sphere (\<phi> ` J)
      (subspace_topology UNIV geotop_euclidean_topology (\<phi> ` J)) 1"
    by (rule geotop_2cell_chart_image_1sphere_dev34[OF hUopen h\<phi> hJsub hJsphere])
  obtain inner outer where hinner_ne: "inner \<noteq> {}"
      and hinner_open: "open inner"
      and hinner_conn: "connected inner"
      and hinner_bdd: "bounded inner"
      and houter_ne: "outer \<noteq> {}"
      and houter_open: "open outer"
      and houter_conn: "connected outer"
      and houter_unbdd: "\<not> bounded outer"
      and hdisj: "inner \<inter> outer = {}"
      and hcover: "inner \<union> outer = UNIV - (\<phi> ` J)"
    by (rule geotop_1sphere_Jordan_open_components_dev34[OF hJimg])
  have hside_data: "inner \<subseteq> \<phi> ` U \<and> \<phi> ` U \<inter> outer \<noteq> {}"
    by (rule hside[OF hinner_ne hinner_open hinner_conn hinner_bdd
        houter_ne houter_open houter_conn houter_unbdd hdisj hcover])
  have hinner_sub: "inner \<subseteq> \<phi> ` U"
    using hside_data by (by100 blast)
  have hVouter_ne: "\<phi> ` U \<inter> outer \<noteq> {}"
    using hside_data by (by100 blast)
  show ?thesis
    by (rule geotop_jordan_components_separate_subset_dev34
        [OF hinner_open houter_open hinner_ne hVouter_ne hdisj hcover hinner_sub])
qed

lemma geotop_2cell_chart_1sphere_jordan_transfer_core_dev34:
  fixes M U J \<sigma> :: "(real^2) set"
  assumes hUopen: "openin_on M
      (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<phi>: "top1_homeomorphism_on
      (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U)
      (subspace_topology M (top1_metric_topology_on M (\<lambda>x y. norm (x - y)))
        (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U))
      \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<phi>"
  assumes hJsub: "J \<subseteq> U"
  assumes hJsphere: "geotop_is_n_sphere J
      (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes himage_sep: "\<not> top1_connected_on (\<phi> ` U - \<phi> ` J)
      (subspace_topology UNIV geotop_euclidean_topology (\<phi> ` U - \<phi> ` J))"
  shows "\<not> top1_connected_on (U - J)
      (subspace_topology UNIV geotop_euclidean_topology (U - J))"
  (**
    Core boundary-chart separation transfer.  The genuinely geometric book
    work is the image-side separation statement; this lemma only pulls that
    statement back across the chart homeomorphism. **)
proof -
  let ?T = "top1_metric_topology_on M (\<lambda>x y. norm (x - y))"
  let ?C = "closure_on M ?T U"
  have hUsubM: "U \<subseteq> M"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hUsubC: "U \<subseteq> ?C"
    by (rule subset_closure_on)
  have hJsubC: "J \<subseteq> ?C"
    using hJsub hUsubC by (by100 blast)
  have hJ_image_sphere: "geotop_is_n_sphere (\<phi> ` J)
      (subspace_topology UNIV geotop_euclidean_topology (\<phi> ` J)) 1"
    by (rule geotop_2cell_chart_image_1sphere_dev34[OF hUopen h\<phi> hJsub hJsphere])
  have hsimplex_chart_sep:
      "\<not> top1_connected_on (\<phi> ` U - \<phi> ` J)
        (subspace_topology UNIV geotop_euclidean_topology (\<phi> ` U - \<phi> ` J))"
    using himage_sep .
  have hpullback_sep:
      "\<not> top1_connected_on (U - J)
        (subspace_topology UNIV geotop_euclidean_topology (U - J))"
  proof
    assume hconn: "top1_connected_on (U - J)
        (subspace_topology UNIV geotop_euclidean_topology (U - J))"
    have hmetricM: "top1_metric_on M (\<lambda>x y. norm (x - y))"
      by (rule metric_on_subset[OF top1_norm_metric_on_UNIV_R2_dev34 subset_UNIV])
    have htopM: "is_topology_on M ?T"
      by (rule top1_metric_topology_on_is_topology_on[OF hmetricM])
    have hCsubM: "?C \<subseteq> M"
      by (rule closure_on_subset_carrier[OF htopM hUsubM])
    have hTM_eq: "?T = subspace_topology UNIV geotop_euclidean_topology M"
      by (rule top1_norm_metric_topology_on_eq_geotop_subspace_R2_dev34)
    have hsource_C_eq:
        "subspace_topology M ?T ?C =
         subspace_topology UNIV geotop_euclidean_topology ?C"
    proof -
      have htrans:
          "subspace_topology M
             (subspace_topology UNIV geotop_euclidean_topology M) ?C =
           subspace_topology UNIV geotop_euclidean_topology ?C"
        by (rule subspace_topology_trans[OF hCsubM])
      show ?thesis
        using hTM_eq htrans by (by100 simp)
    qed
    have hsource_UJ_eq:
        "subspace_topology ?C (subspace_topology M ?T ?C) (U - J) =
         subspace_topology UNIV geotop_euclidean_topology (U - J)"
    proof -
      have hUJsubC': "U - J \<subseteq> ?C"
        using hUsubC by (by100 blast)
      have htrans:
          "subspace_topology ?C
             (subspace_topology UNIV geotop_euclidean_topology ?C) (U - J) =
           subspace_topology UNIV geotop_euclidean_topology (U - J)"
        by (rule subspace_topology_trans[OF hUJsubC'])
      show ?thesis
        using hsource_C_eq htrans by (by100 simp)
    qed
    have hconn_C: "top1_connected_on (U - J)
        (subspace_topology ?C (subspace_topology M ?T ?C) (U - J))"
      using hconn hsource_UJ_eq by (by100 simp)
    have htopC: "is_topology_on ?C (subspace_topology M ?T ?C)"
      using h\<phi> unfolding top1_homeomorphism_on_def by (by100 blast)
    have htop\<sigma>: "is_topology_on \<sigma>
        (subspace_topology UNIV geotop_euclidean_topology \<sigma>)"
      using h\<phi> unfolding top1_homeomorphism_on_def by (by100 blast)
    have hcont\<phi>: "top1_continuous_map_on ?C
        (subspace_topology M ?T ?C) \<sigma>
        (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<phi>"
      by (rule top1_homeomorphism_on_imp_cont1[OF h\<phi>])
    have hUJsubC: "U - J \<subseteq> ?C"
      using hUsubC by (by100 blast)
    have himage_eq: "\<phi> ` (U - J) = \<phi> ` U - \<phi> ` J"
    proof
      show "\<phi> ` (U - J) \<subseteq> \<phi> ` U - \<phi> ` J"
      proof
        fix y assume hy: "y \<in> \<phi> ` (U - J)"
        then obtain x where hx: "x \<in> U - J" and hyx: "y = \<phi> x"
          by (by100 blast)
        have hxU: "x \<in> U"
          using hx by (by100 simp)
        have hxC: "x \<in> ?C"
          using hxU hUsubC by (by100 blast)
        have hxnotJ: "x \<notin> J"
          using hx by (by100 simp)
        have h\<phi>bij: "bij_betw \<phi> ?C \<sigma>"
          by (rule top1_homeomorphism_on_imp_bij[OF h\<phi>])
        have hinj: "inj_on \<phi> ?C"
          using h\<phi>bij by (rule bij_betw_imp_inj_on)
        have hy_not_imgJ: "y \<notin> \<phi> ` J"
        proof
          assume "y \<in> \<phi> ` J"
          then obtain z where hzJ: "z \<in> J" and hyz: "y = \<phi> z"
            by (by100 blast)
          have hzC: "z \<in> ?C"
            using hzJ hJsubC by (by100 blast)
          have h\<phi>xz: "\<phi> x = \<phi> z"
            using hyx hyz by (by100 simp)
          have "x = z"
            by (rule inj_onD[OF hinj h\<phi>xz hxC hzC])
          thus False
            using hxnotJ hzJ by (by100 simp)
        qed
        show "y \<in> \<phi> ` U - \<phi> ` J"
          using hxU hyx hy_not_imgJ by (by100 blast)
      qed
    next
      show "\<phi> ` U - \<phi> ` J \<subseteq> \<phi> ` (U - J)"
      proof
        fix y assume hy: "y \<in> \<phi> ` U - \<phi> ` J"
        then obtain x where hxU: "x \<in> U" and hyx: "y = \<phi> x"
          by (by100 blast)
        have hxnotJ: "x \<notin> J"
        proof
          assume "x \<in> J"
          hence "y \<in> \<phi> ` J"
            using hyx by (by100 blast)
          thus False
            using hy by (by100 blast)
        qed
        show "y \<in> \<phi> ` (U - J)"
          using hxU hxnotJ hyx by (by100 blast)
      qed
    qed
    have hconn_img_\<sigma>: "top1_connected_on (\<phi> ` U - \<phi> ` J)
        (subspace_topology \<sigma>
          (subspace_topology UNIV geotop_euclidean_topology \<sigma>)
          (\<phi> ` U - \<phi> ` J))"
      by (rule Theorem_GT_1_8[OF htopC htop\<sigma> hcont\<phi> hUJsubC himage_eq hconn_C])
    have htarget_eq:
        "subspace_topology \<sigma>
          (subspace_topology UNIV geotop_euclidean_topology \<sigma>)
          (\<phi> ` U - \<phi> ` J) =
         subspace_topology UNIV geotop_euclidean_topology (\<phi> ` U - \<phi> ` J)"
    proof -
      have h\<phi>bij: "bij_betw \<phi> ?C \<sigma>"
        by (rule top1_homeomorphism_on_imp_bij[OF h\<phi>])
      have h\<phi>C: "\<phi> ` ?C = \<sigma>"
        using h\<phi>bij unfolding bij_betw_def by (by100 blast)
      have h\<phi>Usub\<sigma>: "\<phi> ` U \<subseteq> \<sigma>"
        using hUsubC h\<phi>C by (by100 blast)
      have hdiffsub: "\<phi> ` U - \<phi> ` J \<subseteq> \<sigma>"
        using h\<phi>Usub\<sigma> by (by100 blast)
      show ?thesis
        by (rule subspace_topology_trans[OF hdiffsub])
    qed
    have hconn_img: "top1_connected_on (\<phi> ` U - \<phi> ` J)
        (subspace_topology UNIV geotop_euclidean_topology (\<phi> ` U - \<phi> ` J))"
      using hconn_img_\<sigma> htarget_eq by (by100 simp)
    show False
      using hconn_img hsimplex_chart_sep by (by100 blast)
  qed
  show ?thesis
    using hpullback_sep .
qed

lemma geotop_2cell_chart_1sphere_complement_not_connected_dev34:
  fixes M U J :: "(real^2) set"
  assumes hUopen: "openin_on M
      (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U"
  assumes hcell: "geotop_is_n_cell (closure_on M
        (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U)
      (subspace_topology M
        (top1_metric_topology_on M (\<lambda>x y. norm (x - y)))
        (closure_on M
          (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U)) 2"
  assumes hJsub: "J \<subseteq> U"
  assumes hJsphere: "geotop_is_n_sphere J
      (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes himage_sep:
    "\<And>(\<sigma> :: (real^2) set) (\<phi> :: real^2 \<Rightarrow> real^2).
      geotop_simplex_dim \<sigma> 2 \<Longrightarrow>
      top1_homeomorphism_on
        (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U)
        (subspace_topology M (top1_metric_topology_on M (\<lambda>x y. norm (x - y)))
          (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U))
        \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<phi> \<Longrightarrow>
      \<not> top1_connected_on (\<phi> ` U - \<phi> ` J)
        (subspace_topology UNIV geotop_euclidean_topology (\<phi> ` U - \<phi> ` J))"
  shows "\<not> top1_connected_on (U - J)
      (subspace_topology UNIV geotop_euclidean_topology (U - J))"
  (**
    Boundary-chart separation wrapper.  Transport the 2-cell closure of
    \<open>U\<close> to a 2-simplex and pull back the image-side separation supplied by
    the book's local Jordan argument for the chosen chart. **)
proof -
  let ?T = "top1_metric_topology_on M (\<lambda>x y. norm (x - y))"
  let ?C = "closure_on M ?T U"
  have hUsubM: "U \<subseteq> M"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hmetricM: "top1_metric_on M (\<lambda>x y. norm (x - y))"
    by (rule metric_on_subset[OF top1_norm_metric_on_UNIV_R2_dev34 subset_UNIV])
  have htopM: "is_topology_on M ?T"
    by (rule top1_metric_topology_on_is_topology_on[OF hmetricM])
  have hUsubC: "U \<subseteq> ?C"
    by (rule subset_closure_on)
  have hJsubC: "J \<subseteq> ?C"
    using hJsub hUsubC by (by100 blast)
  have hcell_ex: "\<exists>(\<sigma>::(real^2) set) \<phi>. geotop_simplex_dim \<sigma> 2
      \<and> top1_homeomorphism_on ?C
        (subspace_topology M ?T ?C) \<sigma>
        (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<phi>"
    by (rule geotop_is_n_cell_imp_homeo_ex[OF hcell])
  obtain \<sigma> and \<phi> :: "real^2 \<Rightarrow> real^2" where h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and h\<phi>: "top1_homeomorphism_on ?C
      (subspace_topology M ?T ?C) \<sigma>
      (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<phi>"
    using hcell_ex by (by100 blast)
  have hJ_separates_U:
      "\<not> top1_connected_on (U - J)
        (subspace_topology UNIV geotop_euclidean_topology (U - J))"
  proof (rule geotop_2cell_chart_1sphere_jordan_transfer_core_dev34
      [where M = M and U = U and J = J and \<sigma> = \<sigma> and \<phi> = \<phi>])
    show "openin_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U"
      by (rule hUopen)
    show "geotop_simplex_dim \<sigma> 2" by (rule h\<sigma>2)
    show "top1_homeomorphism_on
        (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U)
        (subspace_topology M (top1_metric_topology_on M (\<lambda>x y. norm (x - y)))
          (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U))
        \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<phi>"
      by (rule h\<phi>)
    show "J \<subseteq> U" by (rule hJsub)
    show "geotop_is_n_sphere J
        (subspace_topology UNIV geotop_euclidean_topology J) 1"
      by (rule hJsphere)
    show "\<not> top1_connected_on (\<phi> ` U - \<phi> ` J)
        (subspace_topology UNIV geotop_euclidean_topology (\<phi> ` U - \<phi> ` J))"
    proof (rule himage_sep)
      show "geotop_simplex_dim \<sigma> 2" by (rule h\<sigma>2)
      show "top1_homeomorphism_on
          (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U)
          (subspace_topology M (top1_metric_topology_on M (\<lambda>x y. norm (x - y)))
            (closure_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U))
          \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<phi>"
        by (rule h\<phi>)
    qed
  qed
  show ?thesis
    using hJ_separates_U .
qed

lemma geotop_boundary_2cell_chart_three_incident_2simplex_contradiction_dev34:
  fixes K :: "(real^2) set set" and e U :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hfaces:
    "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
      \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
      \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
      \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
  assumes hUopen: "openin_on (geotop_polyhedron K)
      (top1_metric_topology_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y))) U"
  assumes hlocal_ball: "\<exists>r>0. geotop_polyhedron K \<inter> ball p r \<subseteq> U"
  assumes hUsubM: "U \<subseteq> geotop_polyhedron K"
  assumes hcell: "geotop_is_n_cell (closure_on (geotop_polyhedron K)
        (top1_metric_topology_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y))) U)
      (subspace_topology (geotop_polyhedron K)
        (top1_metric_topology_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)))
        (closure_on (geotop_polyhedron K)
          (top1_metric_topology_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y))) U)) 2"
  shows False
proof -
  obtain \<sigma>1 \<sigma>2 \<sigma>3 where h12: "\<sigma>1 \<noteq> \<sigma>2"
    and h23: "\<sigma>2 \<noteq> \<sigma>3"
    and h13: "\<sigma>1 \<noteq> \<sigma>3"
    and h\<sigma>1K: "\<sigma>1 \<in> K"
    and h\<sigma>1dim: "geotop_simplex_dim \<sigma>1 2"
    and h\<sigma>1face: "geotop_is_face e \<sigma>1"
    and h\<sigma>2K: "\<sigma>2 \<in> K"
    and h\<sigma>2dim: "geotop_simplex_dim \<sigma>2 2"
    and h\<sigma>2face: "geotop_is_face e \<sigma>2"
    and h\<sigma>3K: "\<sigma>3 \<in> K"
    and h\<sigma>3dim: "geotop_simplex_dim \<sigma>3 2"
    and h\<sigma>3face: "geotop_is_face e \<sigma>3"
    using hfaces by (elim exE conjE)
  show False
    by (rule geotop_complex_no_three_2simplexes_share_edge_dev34
        [OF hK hedge h12 h23 h13 h\<sigma>1K h\<sigma>1dim h\<sigma>1face
          h\<sigma>2K h\<sigma>2dim h\<sigma>2face h\<sigma>3K h\<sigma>3dim h\<sigma>3face])
qed

lemma geotop_boundary_chart_three_incident_2simplex_contradiction_dev34:
  fixes K :: "(real^2) set set" and e U :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hfaces:
    "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
      \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
      \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
      \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
  assumes hUopen: "openin_on (geotop_polyhedron K)
      (top1_metric_topology_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y))) U"
  assumes hpU: "p \<in> U"
  assumes hcell: "geotop_is_n_cell (closure_on (geotop_polyhedron K)
        (top1_metric_topology_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y))) U)
      (subspace_topology (geotop_polyhedron K)
        (top1_metric_topology_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)))
        (closure_on (geotop_polyhedron K)
          (top1_metric_topology_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y))) U)) 2"
  shows False
proof -
  let ?M = "geotop_polyhedron K"
  have hlocal_ball: "\<exists>r>0. ?M \<inter> ball p r \<subseteq> U"
    by (rule geotop_openin_norm_polyhedron_contains_relative_ball_dev34
        [OF hUopen hpU])
  have hUsubM: "U \<subseteq> ?M"
    using hUopen unfolding openin_on_def by (by100 blast)
  show False
    by (rule geotop_boundary_2cell_chart_three_incident_2simplex_contradiction_dev34
        [OF hK heK hedge hp hfaces hUopen hlocal_ball hUsubM hcell])
qed

(** from \<S>4 Theorem 8 (geotop.tex:1020)
    LATEX VERSION: Let K be a complex such that M = |K| is a 2-manifold. Then K is a
      combinatorial 2-manifold; i.e., every subcomplex St v is a combinatorial 2-cell. **)
theorem Theorem_GT_4_8:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hM: "geotop_n_manifold_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  shows "\<forall>v\<in>geotop_complex_vertices K. geotop_comb_n_cell (geotop_star K v) 2"
  (** Moise proof (geotop.tex:1022). Via five lemmas:
      L1: Every vertex lies in an edge (R\<^sup>2 has no isolated points).
      L2: Every edge lies in \<ge> 1 2-simplex (else interior point has a plane-nbhd
          inside Int(edge), contradicting \"no point separates plane\").
      L3: Every edge lies in \<ge> 2 2-simplexes (else a semicircle in the
          2-simplex separates a plane-nbhd, contradicting \"no arc separates R\<^sup>2\").
      L4: Every edge lies in \<le> 2 2-simplexes (else 2 semicircles form a
          1-sphere not separating its plane-nbhd, contradicting Jordan).
      L5: |L(v)| is connected (v does not separate its plane-nbhd |St v|).
      From L1: L(v) \<noteq> \<emptyset>. From L2-L4: each component of |L(v)| is a polygon.
      With L5: |L(v)| is a single polygon. Form simplicial homeomorphism
      between (St v, L(v)) and a standard cone over a polygon (Fig 4.10). **)
proof
  fix v assume hv: "v \<in> geotop_complex_vertices K"
  \<comment> \<open>L1: every vertex lies in some edge (no isolated points in 2-manifold).\<close>
  have hL1: "\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e"
  proof (rule ccontr)
    assume hno: "\<not> (\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e)"
    have hvK: "{v} \<in> K"
      using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
    have hvM: "v \<in> geotop_polyhedron K"
      using hvK unfolding geotop_polyhedron_def by (by100 blast)
    have hsingle_open:
      "{v} \<in> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
      by (rule geotop_complex_no_incident_edge_vertex_open_singleton[OF hK hv hno])
    have hnot_open:
      "{v} \<notin> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
      by (rule geotop_2_manifold_no_open_singleton[OF hM hvM])
    show False
      using hsingle_open hnot_open by (by100 blast)
  qed
  \<comment> \<open>L1 consequence: the link is nonempty, taking the other endpoint
    of an incident edge.\<close>
  have hL1_link_poly_nonempty: "\<Union>(geotop_link K v) \<noteq> {}"
  proof -
    obtain e where heK: "e \<in> K" and hedge: "geotop_is_edge e" and hv_e: "v \<in> e"
      using hL1 by (by100 blast)
    have hvK: "{v} \<in> K"
      using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
    show ?thesis
      by (rule geotop_incident_edge_link_polyhedron_nonempty
          [OF hK hvK heK hedge hv_e])
  qed
  \<comment> \<open>L2: every incident edge in \<ge>1 two-simplex.\<close>
  have hL2: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
              (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>)"
  proof (intro ballI impI)
    fix e assume heK: "e \<in> K"
      and he_inc: "geotop_is_edge e \<and> v \<in> e"
    have hedge: "geotop_is_edge e"
      using he_inc by (by100 blast)
    show "\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>"
    proof (rule ccontr)
      assume hno2: "\<not> (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>)"
      have hrel_open:
        "rel_interior e \<in>
          subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
        by (rule geotop_complex_no_2_simplex_over_edge_rel_interior_open
            [OF hK heK hedge hno2])
      have hrel_sub: "rel_interior e \<subseteq> geotop_polyhedron K"
        using heK rel_interior_subset unfolding geotop_polyhedron_def by (by100 blast)
      show False
        by (rule geotop_2_manifold_no_open_edge_rel_interior
            [OF hM hedge hrel_open hrel_sub])
    qed
	  qed
  \<comment> \<open>Counted form of L2: every incident edge contributes at least one
    counted two-simplex face. This is the form used by the link analysis.\<close>
  have hL2_count: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
              card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 1"
  proof (intro ballI impI)
    fix e assume heK: "e \<in> K" and he_inc: "geotop_is_edge e \<and> v \<in> e"
    have hedge: "geotop_is_edge e"
      using he_inc by (by100 blast)
    have hex: "\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>"
      using hL2 heK he_inc by (by100 blast)
    show "1 \<le> card {\<sigma> \<in> K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
      by (rule geotop_complex_edge_in_2_simplex_imp_face_count_ge_1
          [OF hK heK hedge hex])
  qed
  \<comment> \<open>Counterexample form for L3: if an incident edge is not in at least
    two adjacent two-simplexes, Lemma 2 says it is in exactly one; name that
    unique two-simplex for the book's semicircle contradiction.\<close>
  have hL3_counterexample_face: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
              \<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 2 \<longrightarrow>
              (\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>)"
  proof (intro ballI impI)
    fix e assume heK: "e \<in> K" and he_inc: "geotop_is_edge e \<and> v \<in> e"
      and hnot_ge2: "\<not> 2 \<le> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
    have hedge: "geotop_is_edge e"
      using he_inc by (by100 blast)
    have hge1: "1 \<le> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
      using hL2_count heK he_inc by (by100 blast)
    have hcard1: "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
      using hge1 hnot_ge2 by (by100 linarith)
    show "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
      by (rule geotop_complex_edge_face_count_eq_1_unique[OF hK heK hedge hcard1])
  qed
  \<comment> \<open>L3: every incident edge in \<ge>2 two-simplexes (manifold without boundary).\<close>
  have hL3: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
              card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 2"
  proof (intro ballI impI)
    fix e assume heK: "e \<in> K" and he_inc: "geotop_is_edge e \<and> v \<in> e"
    show "2 \<le> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
    proof (rule ccontr)
      assume hnot_ge2:
        "\<not> 2 \<le> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
      have hedge: "geotop_is_edge e"
        using he_inc by (by100 blast)
      have hL3_at: "geotop_is_edge e \<and> v \<in> e \<longrightarrow>
              \<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 2 \<longrightarrow>
              (\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>)"
        using hL3_counterexample_face heK by (by100 simp)
      have hnot_ge2': "\<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 2"
        using hnot_ge2 by (by100 simp)
      have hL3_imp: "\<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 2 \<longrightarrow>
              (\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>)"
        by (rule mp[OF hL3_at he_inc])
      have hunique_ex:
        "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
        by (rule mp[OF hL3_imp hnot_ge2'])
      then obtain \<sigma> where h\<sigma>prop: "\<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
        and h\<sigma>uniq: "\<forall>\<tau>. \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau> \<longrightarrow> \<tau> = \<sigma>"
        unfolding Ex1_def by (by100 blast)
      have h\<sigma>K: "\<sigma> \<in> K"
        using h\<sigma>prop by (by100 blast)
      have h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
        using h\<sigma>prop by (by100 blast)
      have he_face_\<sigma>: "geotop_is_face e \<sigma>"
        using h\<sigma>prop by (by100 blast)
      obtain p where hp: "p \<in> rel_interior e"
        using geotop_edge_rel_interior_nonempty[OF hedge] by (by100 blast)
      have hpM: "p \<in> geotop_polyhedron K"
        using heK hp rel_interior_subset unfolding geotop_polyhedron_def by (by100 blast)
      let ?M = "geotop_polyhedron K"
      let ?TM = "top1_metric_topology_on ?M (\<lambda>x y. norm (x - y))"
      obtain U f where hUopen: "openin_on ?M ?TM U"
        and hpU: "p \<in> U"
        and hhomeo_geo: "top1_homeomorphism_on U
            (subspace_topology UNIV geotop_euclidean_topology U)
            (UNIV::(real^2) set) geotop_euclidean_topology f"
        using geotop_polyhedron_2_manifold_geo_chart_at_dev34[OF hM hpM]
        by (by100 blast)
      obtain A where hAsubU: "A \<subseteq> U"
        and hAimg: "geotop_is_arc (f ` A)
            (subspace_topology UNIV geotop_euclidean_topology (f ` A))"
        and hAsep: "\<not> top1_connected_on (U - A)
            (subspace_topology UNIV geotop_euclidean_topology (U - A))"
        using geotop_unique_incident_2simplex_semicircle_separates_chart_dev34
            [OF hK heK hedge hp hunique_ex hUopen hpU hhomeo_geo]
        by (by100 blast)
      have hconn: "top1_connected_on (U - A)
          (subspace_topology UNIV geotop_euclidean_topology (U - A))"
        by (rule geotop_plane_chart_arc_complement_connected[OF hhomeo_geo hAsubU hAimg])
      show False
        using hconn hAsep by (by100 blast)
    qed
  qed
  \<comment> \<open>Counterexample form for L4: if an incident edge has more than two
    adjacent two-simplexes, name the three simplexes used to build the two
    semicircles in the book's Jordan-curve contradiction.\<close>
  have hL4_counterexample_faces: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
              \<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2 \<longrightarrow>
              (\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
                \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
                \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
                \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3)"
  proof (intro ballI impI)
    fix e assume heK: "e \<in> K" and he_inc: "geotop_is_edge e \<and> v \<in> e"
      and hnot_le2: "\<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
    have hge3: "3 \<le> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
      using hnot_le2 by (by100 simp)
    show "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
                \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
                \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
                \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
      by (rule geotop_complex_edge_face_count_ge_3_obtain[OF hge3])
  qed
  \<comment> \<open>L4: every incident edge in \<le>2 two-simplexes.\<close>
  have hL4: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
              card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
  proof
    fix e assume heK: "e \<in> K"
    show "geotop_is_edge e \<and> v \<in> e \<longrightarrow>
        card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
    proof
      assume he_inc: "geotop_is_edge e \<and> v \<in> e"
      show "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
      proof -
        have hnot_counterexample:
          "\<not> \<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
        proof
          assume hnot_le2:
            "\<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
          have hL4_at: "geotop_is_edge e \<and> v \<in> e \<longrightarrow>
              \<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2 \<longrightarrow>
              (\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
                \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
                \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
                \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3)"
            using hL4_counterexample_faces heK by (by100 simp)
          have hL4_imp: "\<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2 \<longrightarrow>
              (\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
                \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
                \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
                \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3)"
            by (rule mp[OF hL4_at he_inc])
          have hfaces_ex:
              "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
                \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
                \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
                \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
            by (rule mp[OF hL4_imp hnot_le2])
          have hedge: "geotop_is_edge e"
            using he_inc by (by100 blast)
          obtain p where hp: "p \<in> rel_interior e"
            using geotop_edge_rel_interior_nonempty[OF hedge] by (by100 blast)
          have hpM: "p \<in> geotop_polyhedron K"
            using heK hp rel_interior_subset unfolding geotop_polyhedron_def by (by100 blast)
          let ?M = "geotop_polyhedron K"
          let ?TM = "top1_metric_topology_on ?M (\<lambda>x y. norm (x - y))"
          obtain U f where hUopen: "openin_on ?M ?TM U"
            and hpU: "p \<in> U"
            and hhomeo_geo: "top1_homeomorphism_on U
                (subspace_topology UNIV geotop_euclidean_topology U)
                (UNIV::(real^2) set) geotop_euclidean_topology f"
            using geotop_polyhedron_2_manifold_geo_chart_at_dev34[OF hM hpM]
            by (by100 blast)
          obtain J where hJsubU: "J \<subseteq> U"
            and hJimg_sphere: "geotop_is_n_sphere (f ` J)
                (subspace_topology UNIV geotop_euclidean_topology (f ` J)) 1"
            and hJ_not_sep: "top1_connected_on (U - J)
                (subspace_topology UNIV geotop_euclidean_topology (U - J))"
            using geotop_three_incident_2simplex_sphere_not_separates_chart_dev34
                [OF hK heK hedge hp hfaces_ex hUopen hpU hhomeo_geo]
            by (by100 blast)
          have hJ_sep: "\<not> top1_connected_on (U - J)
                (subspace_topology UNIV geotop_euclidean_topology (U - J))"
            by (rule geotop_plane_chart_1sphere_complement_not_connected
                [OF hhomeo_geo hJsubU hJimg_sphere])
          show False
            using hJ_not_sep hJ_sep by (by100 blast)
        qed
        show "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
          using hnot_counterexample by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>Combining L3 and L4: every incident edge has exactly two adjacent
    two-simplexes.\<close>
  have hL_count_eq2: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
              card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
  proof (intro ballI impI)
    fix e assume heK: "e \<in> K" and he_inc: "geotop_is_edge e \<and> v \<in> e"
    let ?S = "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
    have hge: "card ?S \<ge> 2"
      using hL3 heK he_inc by (by100 blast)
    have hle: "card ?S \<le> 2"
      using hL4 heK he_inc by (by100 blast)
    show "card ?S = 2"
      using hge hle by (by100 simp)
  qed
  \<comment> \<open>Witness form of L3-L4: each incident edge has exactly two named
    adjacent two-simplexes, matching the book's local picture around the edge.\<close>
  have hL_two_faces: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
              (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
                \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
                \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
                \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>})"
  proof (intro ballI impI)
    fix e assume heK: "e \<in> K" and he_inc: "geotop_is_edge e \<and> v \<in> e"
    have hcard2:
      "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
      using hL_count_eq2 heK he_inc by (by100 blast)
    show "\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
                \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
                \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
                \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
      by (rule geotop_complex_edge_face_count_eq_2_obtain[OF hcard2])
  qed
  \<comment> \<open>Book consequence of L2-L4: every link vertex is incident to a link edge.\<close>
  have hlink_vertices_incident_edges:
    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
        (\<exists>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l)"
  proof -
    have hvK: "{v} \<in> K"
      using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
    show ?thesis
      by (rule geotop_link_vertices_count_ge_1_incident_link_edges
          [OF hK hvK hL2_count])
  qed
  \<comment> \<open>L2-L4 local link picture: at each link vertex the two
    adjacent two-simplexes over the incident edge yield two link-edge
    witnesses through that link vertex.\<close>
  have hlink_vertices_two_adjacent_link_edges:
    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
      (\<exists>e \<sigma> \<tau> l\<^sub>\<sigma> l\<^sub>\<tau>. e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
        \<and> \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> l\<^sub>\<sigma> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<sigma> \<and> w \<in> l\<^sub>\<sigma>
        \<and> l\<^sub>\<tau> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<tau> \<and> w \<in> l\<^sub>\<tau>)"
  proof
    fix w
    show "{w} \<in> geotop_link K v \<longrightarrow>
      (\<exists>e \<sigma> \<tau> l\<^sub>\<sigma> l\<^sub>\<tau>. e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
        \<and> \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> l\<^sub>\<sigma> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<sigma> \<and> w \<in> l\<^sub>\<sigma>
        \<and> l\<^sub>\<tau> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<tau> \<and> w \<in> l\<^sub>\<tau>)"
    proof
      assume hwL: "{w} \<in> geotop_link K v"
      have hvK: "{v} \<in> K"
        using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
      show "\<exists>e \<sigma> \<tau> l\<^sub>\<sigma> l\<^sub>\<tau>. e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
        \<and> \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> l\<^sub>\<sigma> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<sigma> \<and> w \<in> l\<^sub>\<sigma>
        \<and> l\<^sub>\<tau> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<tau> \<and> w \<in> l\<^sub>\<tau>"
        by (rule geotop_link_vertex_two_adjacent_link_edge_witnesses
            [OF hK hvK hwL hL_two_faces])
    qed
  qed
  have hlink_vertices_two_opposite_link_edges:
    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
      (\<exists>e \<sigma> \<tau> u\<^sub>\<sigma> u\<^sub>\<tau>. e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
        \<and> \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> u\<^sub>\<sigma> \<in> \<sigma> \<and> u\<^sub>\<sigma> \<noteq> v \<and> u\<^sub>\<sigma> \<noteq> w
        \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> u\<^sub>\<tau> \<in> \<tau> \<and> u\<^sub>\<tau> \<noteq> v \<and> u\<^sub>\<tau> \<noteq> w
        \<and> geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
        \<and> u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>})"
  proof
    fix w
    show "{w} \<in> geotop_link K v \<longrightarrow>
      (\<exists>e \<sigma> \<tau> u\<^sub>\<sigma> u\<^sub>\<tau>. e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
        \<and> \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> u\<^sub>\<sigma> \<in> \<sigma> \<and> u\<^sub>\<sigma> \<noteq> v \<and> u\<^sub>\<sigma> \<noteq> w
        \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> u\<^sub>\<tau> \<in> \<tau> \<and> u\<^sub>\<tau> \<noteq> v \<and> u\<^sub>\<tau> \<noteq> w
        \<and> geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
        \<and> u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>})"
    proof
      assume hwL: "{w} \<in> geotop_link K v"
      have hvK: "{v} \<in> K"
        using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
      obtain e where heK: "e \<in> K"
        and hedge: "geotop_is_edge e"
        and hv_e: "v \<in> e"
        and hw_e: "w \<in> e"
        using geotop_link_vertex_incident_edge_witness[OF hK hvK hwL]
        by (by100 blast)
      have htwo_imp: "geotop_is_edge e \<and> v \<in> e \<longrightarrow>
          (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
            \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
            \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
            \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>})"
        using hL_two_faces heK by (by100 simp)
      have hinc: "geotop_is_edge e \<and> v \<in> e"
        using hedge hv_e by (by100 blast)
      have htwo_e: "\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
            \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
            \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
            \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
        by (rule mp[OF htwo_imp hinc])
      from htwo_e obtain \<sigma> where h\<sigma>ex:
        "\<exists>\<tau>. \<sigma> \<noteq> \<tau>
            \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
            \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
            \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}" ..
      from h\<sigma>ex obtain \<tau> where hpair:
        "\<sigma> \<noteq> \<tau>
            \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
            \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
            \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}" ..
      have h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
        using hpair by (by100 simp)
      have h\<sigma>K: "\<sigma> \<in> K"
        using hpair by (by100 simp)
      have h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
        using hpair by (by100 simp)
      have h\<sigma>face: "geotop_is_face e \<sigma>"
        using hpair by (by100 simp)
      have h\<tau>K: "\<tau> \<in> K"
        using hpair by (by100 simp)
      have h\<tau>2: "geotop_simplex_dim \<tau> 2"
        using hpair by (by100 simp)
      have h\<tau>face: "geotop_is_face e \<tau>"
        using hpair by (by100 simp)
      obtain u\<^sub>\<sigma> where hu\<sigma>\<sigma>: "u\<^sub>\<sigma> \<in> \<sigma>"
        and hu\<sigma>_ne_v: "u\<^sub>\<sigma> \<noteq> v"
        and hu\<sigma>_ne_w: "u\<^sub>\<sigma> \<noteq> w"
        and hl\<sigma>L: "geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v"
        and hl\<sigma>edge: "geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})"
        and hw_l\<sigma>: "w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}"
        and hu\<sigma>_l\<sigma>: "u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}"
        using geotop_link_vertex_incident_2simplex_opposite_link_edge
          [OF hK hvK hwL heK hedge hv_e hw_e h\<sigma>K h\<sigma>2 h\<sigma>face]
        by (by100 blast)
      obtain u\<^sub>\<tau> where hu\<tau>\<tau>: "u\<^sub>\<tau> \<in> \<tau>"
        and hu\<tau>_ne_v: "u\<^sub>\<tau> \<noteq> v"
        and hu\<tau>_ne_w: "u\<^sub>\<tau> \<noteq> w"
        and hl\<tau>L: "geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v"
        and hl\<tau>edge: "geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})"
        and hw_l\<tau>: "w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
        and hu\<tau>_l\<tau>: "u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
        using geotop_link_vertex_incident_2simplex_opposite_link_edge
          [OF hK hvK hwL heK hedge hv_e hw_e h\<tau>K h\<tau>2 h\<tau>face]
        by (by100 blast)
      show "\<exists>e \<sigma> \<tau> u\<^sub>\<sigma> u\<^sub>\<tau>. e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
        \<and> \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> u\<^sub>\<sigma> \<in> \<sigma> \<and> u\<^sub>\<sigma> \<noteq> v \<and> u\<^sub>\<sigma> \<noteq> w
        \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> u\<^sub>\<tau> \<in> \<tau> \<and> u\<^sub>\<tau> \<noteq> v \<and> u\<^sub>\<tau> \<noteq> w
        \<and> geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
        \<and> u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
        using heK hedge hv_e hw_e h\<sigma>\<tau> h\<sigma>K h\<sigma>2 h\<sigma>face h\<tau>K h\<tau>2 h\<tau>face
          hu\<sigma>\<sigma> hu\<sigma>_ne_v hu\<sigma>_ne_w hl\<sigma>L hl\<sigma>edge hw_l\<sigma> hu\<sigma>_l\<sigma>
          hu\<tau>\<tau> hu\<tau>_ne_v hu\<tau>_ne_w hl\<tau>L hl\<tau>edge hw_l\<tau> hu\<tau>_l\<tau>
        by (by100 blast)
    qed
  qed
  have hlink_vertices_two_opposite_face_link_edges:
    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
      (\<exists>e \<sigma> \<tau> u\<^sub>\<sigma> u\<^sub>\<tau>. e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
        \<and> \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> u\<^sub>\<sigma> \<in> \<sigma> \<and> u\<^sub>\<sigma> \<noteq> v \<and> u\<^sub>\<sigma> \<noteq> w
        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<sigma>}) \<sigma>
        \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> u\<^sub>\<tau> \<in> \<tau> \<and> u\<^sub>\<tau> \<noteq> v \<and> u\<^sub>\<tau> \<noteq> w
        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>
        \<and> geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
        \<and> u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>})"
  proof
    fix w
    show "{w} \<in> geotop_link K v \<longrightarrow>
      (\<exists>e \<sigma> \<tau> u\<^sub>\<sigma> u\<^sub>\<tau>. e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
        \<and> \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> u\<^sub>\<sigma> \<in> \<sigma> \<and> u\<^sub>\<sigma> \<noteq> v \<and> u\<^sub>\<sigma> \<noteq> w
        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<sigma>}) \<sigma>
        \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> u\<^sub>\<tau> \<in> \<tau> \<and> u\<^sub>\<tau> \<noteq> v \<and> u\<^sub>\<tau> \<noteq> w
        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>
        \<and> geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
        \<and> u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>})"
    proof
      assume hwL: "{w} \<in> geotop_link K v"
      have hvK: "{v} \<in> K"
        using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
      obtain e where heK: "e \<in> K"
        and hedge: "geotop_is_edge e"
        and hv_e: "v \<in> e"
        and hw_e: "w \<in> e"
        using geotop_link_vertex_incident_edge_witness[OF hK hvK hwL]
        by (by100 blast)
      have htwo_imp: "geotop_is_edge e \<and> v \<in> e \<longrightarrow>
          (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
            \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
            \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
            \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>})"
        using hL_two_faces heK by (by100 simp)
      have hinc: "geotop_is_edge e \<and> v \<in> e"
        using hedge hv_e by (by100 blast)
      have htwo_e: "\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
            \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
            \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
            \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
        by (rule mp[OF htwo_imp hinc])
      from htwo_e obtain \<sigma> where h\<sigma>ex:
        "\<exists>\<tau>. \<sigma> \<noteq> \<tau>
            \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
            \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
            \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}" ..
      from h\<sigma>ex obtain \<tau> where hpair:
        "\<sigma> \<noteq> \<tau>
            \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
            \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
            \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}" ..
      have h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
        using hpair by (by100 simp)
      have h\<sigma>K: "\<sigma> \<in> K"
        using hpair by (by100 simp)
      have h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
        using hpair by (by100 simp)
      have h\<sigma>face: "geotop_is_face e \<sigma>"
        using hpair by (by100 simp)
      have h\<tau>K: "\<tau> \<in> K"
        using hpair by (by100 simp)
      have h\<tau>2: "geotop_simplex_dim \<tau> 2"
        using hpair by (by100 simp)
      have h\<tau>face: "geotop_is_face e \<tau>"
        using hpair by (by100 simp)
      obtain u\<^sub>\<sigma> where hu\<sigma>\<sigma>: "u\<^sub>\<sigma> \<in> \<sigma>"
        and hu\<sigma>_ne_v: "u\<^sub>\<sigma> \<noteq> v"
        and hu\<sigma>_ne_w: "u\<^sub>\<sigma> \<noteq> w"
        and hface_l\<sigma>: "geotop_is_face (geotop_convex_hull {w, u\<^sub>\<sigma>}) \<sigma>"
        and hl\<sigma>L: "geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v"
        and hl\<sigma>edge: "geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})"
        and hw_l\<sigma>: "w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}"
        and hu\<sigma>_l\<sigma>: "u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}"
        using geotop_link_vertex_incident_2simplex_opposite_face_link_edge
          [OF hK hvK hwL heK hedge hv_e hw_e h\<sigma>K h\<sigma>2 h\<sigma>face]
        by (by100 blast)
      obtain u\<^sub>\<tau> where hu\<tau>\<tau>: "u\<^sub>\<tau> \<in> \<tau>"
        and hu\<tau>_ne_v: "u\<^sub>\<tau> \<noteq> v"
        and hu\<tau>_ne_w: "u\<^sub>\<tau> \<noteq> w"
        and hface_l\<tau>: "geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>"
        and hl\<tau>L: "geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v"
        and hl\<tau>edge: "geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})"
        and hw_l\<tau>: "w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
        and hu\<tau>_l\<tau>: "u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
        using geotop_link_vertex_incident_2simplex_opposite_face_link_edge
          [OF hK hvK hwL heK hedge hv_e hw_e h\<tau>K h\<tau>2 h\<tau>face]
        by (by100 blast)
      show "\<exists>e \<sigma> \<tau> u\<^sub>\<sigma> u\<^sub>\<tau>. e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
        \<and> \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> u\<^sub>\<sigma> \<in> \<sigma> \<and> u\<^sub>\<sigma> \<noteq> v \<and> u\<^sub>\<sigma> \<noteq> w
        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<sigma>}) \<sigma>
        \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> u\<^sub>\<tau> \<in> \<tau> \<and> u\<^sub>\<tau> \<noteq> v \<and> u\<^sub>\<tau> \<noteq> w
        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>
        \<and> geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
        \<and> u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
        using heK hedge hv_e hw_e h\<sigma>\<tau> h\<sigma>K h\<sigma>2 h\<sigma>face h\<tau>K h\<tau>2 h\<tau>face
          hu\<sigma>\<sigma> hu\<sigma>_ne_v hu\<sigma>_ne_w hface_l\<sigma> hl\<sigma>L hl\<sigma>edge hw_l\<sigma> hu\<sigma>_l\<sigma>
          hu\<tau>\<tau> hu\<tau>_ne_v hu\<tau>_ne_w hface_l\<tau> hl\<tau>L hl\<tau>edge hw_l\<tau> hu\<tau>_l\<tau>
        by (by100 blast)
    qed
  qed
  have hlink_vertices_two_opposite_vertex_face_link_edges:
    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
      (\<exists>e \<sigma> \<tau> V\<^sub>\<sigma> V\<^sub>\<tau> u\<^sub>\<sigma> u\<^sub>\<tau>.
        e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
        \<and> \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>
        \<and> v \<in> V\<^sub>\<sigma> \<and> w \<in> V\<^sub>\<sigma> \<and> u\<^sub>\<sigma> \<in> V\<^sub>\<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> geotop_simplex_vertices \<tau> V\<^sub>\<tau>
        \<and> v \<in> V\<^sub>\<tau> \<and> w \<in> V\<^sub>\<tau> \<and> u\<^sub>\<tau> \<in> V\<^sub>\<tau>
        \<and> u\<^sub>\<sigma> \<noteq> v \<and> u\<^sub>\<sigma> \<noteq> w
        \<and> u\<^sub>\<tau> \<noteq> v \<and> u\<^sub>\<tau> \<noteq> w
        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<sigma>}) \<sigma>
        \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>
        \<and> geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
        \<and> u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>})"
  proof
    fix w
    show "{w} \<in> geotop_link K v \<longrightarrow>
      (\<exists>e \<sigma> \<tau> V\<^sub>\<sigma> V\<^sub>\<tau> u\<^sub>\<sigma> u\<^sub>\<tau>.
        e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
        \<and> \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>
        \<and> v \<in> V\<^sub>\<sigma> \<and> w \<in> V\<^sub>\<sigma> \<and> u\<^sub>\<sigma> \<in> V\<^sub>\<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> geotop_simplex_vertices \<tau> V\<^sub>\<tau>
        \<and> v \<in> V\<^sub>\<tau> \<and> w \<in> V\<^sub>\<tau> \<and> u\<^sub>\<tau> \<in> V\<^sub>\<tau>
        \<and> u\<^sub>\<sigma> \<noteq> v \<and> u\<^sub>\<sigma> \<noteq> w
        \<and> u\<^sub>\<tau> \<noteq> v \<and> u\<^sub>\<tau> \<noteq> w
        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<sigma>}) \<sigma>
        \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>
        \<and> geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
        \<and> u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>})"
    proof
      assume hwL: "{w} \<in> geotop_link K v"
      have hvK: "{v} \<in> K"
        using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
      obtain e where heK: "e \<in> K"
        and hedge: "geotop_is_edge e"
        and hv_e: "v \<in> e"
        and hw_e: "w \<in> e"
        using geotop_link_vertex_incident_edge_witness[OF hK hvK hwL]
        by (by100 blast)
      have htwo_imp: "geotop_is_edge e \<and> v \<in> e \<longrightarrow>
          (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
            \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
            \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
            \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>})"
        using hL_two_faces heK by (by100 simp)
      have hinc: "geotop_is_edge e \<and> v \<in> e"
        using hedge hv_e by (by100 blast)
      have htwo_e: "\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
            \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
            \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
            \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
        by (rule mp[OF htwo_imp hinc])
      from htwo_e obtain \<sigma> where h\<sigma>ex:
        "\<exists>\<tau>. \<sigma> \<noteq> \<tau>
            \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
            \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
            \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}" ..
      from h\<sigma>ex obtain \<tau> where hpair:
        "\<sigma> \<noteq> \<tau>
            \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
            \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
            \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}" ..
      have h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
        using hpair by (by100 simp)
      have h\<sigma>K: "\<sigma> \<in> K"
        using hpair by (by100 simp)
      have h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
        using hpair by (by100 simp)
      have h\<sigma>face: "geotop_is_face e \<sigma>"
        using hpair by (by100 simp)
      have h\<tau>K: "\<tau> \<in> K"
        using hpair by (by100 simp)
      have h\<tau>2: "geotop_simplex_dim \<tau> 2"
        using hpair by (by100 simp)
      have h\<tau>face: "geotop_is_face e \<tau>"
        using hpair by (by100 simp)
      obtain V\<^sub>\<sigma> u\<^sub>\<sigma> where hV\<sigma>: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>"
        and hvV\<sigma>: "v \<in> V\<^sub>\<sigma>"
        and hwV\<sigma>: "w \<in> V\<^sub>\<sigma>"
        and huV\<sigma>: "u\<^sub>\<sigma> \<in> V\<^sub>\<sigma>"
        and hu\<sigma>_ne_v: "u\<^sub>\<sigma> \<noteq> v"
        and hu\<sigma>_ne_w: "u\<^sub>\<sigma> \<noteq> w"
        and hu\<sigma>\<sigma>: "u\<^sub>\<sigma> \<in> \<sigma>"
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
        and hu\<tau>\<tau>: "u\<^sub>\<tau> \<in> \<tau>"
        and hface_l\<tau>: "geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>"
        and hl\<tau>L: "geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v"
        and hl\<tau>edge: "geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})"
        and hw_l\<tau>: "w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
        and hu\<tau>_l\<tau>: "u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
        using geotop_link_vertex_incident_2simplex_opposite_vertex_face_link_edge
          [OF hK hvK hwL heK hedge hv_e hw_e h\<tau>K h\<tau>2 h\<tau>face]
        by (by100 blast)
      show "\<exists>e \<sigma> \<tau> V\<^sub>\<sigma> V\<^sub>\<tau> u\<^sub>\<sigma> u\<^sub>\<tau>.
        e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
        \<and> \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>
        \<and> v \<in> V\<^sub>\<sigma> \<and> w \<in> V\<^sub>\<sigma> \<and> u\<^sub>\<sigma> \<in> V\<^sub>\<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> geotop_simplex_vertices \<tau> V\<^sub>\<tau>
        \<and> v \<in> V\<^sub>\<tau> \<and> w \<in> V\<^sub>\<tau> \<and> u\<^sub>\<tau> \<in> V\<^sub>\<tau>
        \<and> u\<^sub>\<sigma> \<noteq> v \<and> u\<^sub>\<sigma> \<noteq> w
        \<and> u\<^sub>\<tau> \<noteq> v \<and> u\<^sub>\<tau> \<noteq> w
        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<sigma>}) \<sigma>
        \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>
        \<and> geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v
        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})
        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
        \<and> u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
        using heK hedge hv_e hw_e h\<sigma>\<tau> h\<sigma>K h\<sigma>2 h\<sigma>face hV\<sigma> hvV\<sigma> hwV\<sigma> huV\<sigma>
          h\<tau>K h\<tau>2 h\<tau>face hV\<tau> hvV\<tau> hwV\<tau> huV\<tau>
          hu\<sigma>_ne_v hu\<sigma>_ne_w hu\<tau>_ne_v hu\<tau>_ne_w
          hface_l\<sigma> hl\<sigma>L hl\<sigma>edge hw_l\<sigma> hu\<sigma>_l\<sigma>
          hface_l\<tau> hl\<tau>L hl\<tau>edge hw_l\<tau> hu\<tau>_l\<tau>
        by (by100 blast)
    qed
	  qed
	  have hlink_vertices_two_distinct_opposite_link_edges:
	    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
	      (\<exists>e \<sigma> \<tau> V\<^sub>\<sigma> V\<^sub>\<tau> u\<^sub>\<sigma> u\<^sub>\<tau>.
	        e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
	        \<and> \<sigma> \<noteq> \<tau>
	        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
	        \<and> geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>
	        \<and> v \<in> V\<^sub>\<sigma> \<and> w \<in> V\<^sub>\<sigma> \<and> u\<^sub>\<sigma> \<in> V\<^sub>\<sigma>
	        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
	        \<and> geotop_simplex_vertices \<tau> V\<^sub>\<tau>
	        \<and> v \<in> V\<^sub>\<tau> \<and> w \<in> V\<^sub>\<tau> \<and> u\<^sub>\<tau> \<in> V\<^sub>\<tau>
	        \<and> u\<^sub>\<sigma> \<noteq> v \<and> u\<^sub>\<sigma> \<noteq> w
	        \<and> u\<^sub>\<tau> \<noteq> v \<and> u\<^sub>\<tau> \<noteq> w
	        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<sigma>}) \<sigma>
	        \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v
	        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})
	        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
	        \<and> u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
	        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>
	        \<and> geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v
	        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})
	        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
	        \<and> u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
	        \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<noteq> geotop_convex_hull {w, u\<^sub>\<tau>})"
	  proof
	    fix w
	    show "{w} \<in> geotop_link K v \<longrightarrow>
	      (\<exists>e \<sigma> \<tau> V\<^sub>\<sigma> V\<^sub>\<tau> u\<^sub>\<sigma> u\<^sub>\<tau>.
	        e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
	        \<and> \<sigma> \<noteq> \<tau>
	        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
	        \<and> geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>
	        \<and> v \<in> V\<^sub>\<sigma> \<and> w \<in> V\<^sub>\<sigma> \<and> u\<^sub>\<sigma> \<in> V\<^sub>\<sigma>
	        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
	        \<and> geotop_simplex_vertices \<tau> V\<^sub>\<tau>
	        \<and> v \<in> V\<^sub>\<tau> \<and> w \<in> V\<^sub>\<tau> \<and> u\<^sub>\<tau> \<in> V\<^sub>\<tau>
	        \<and> u\<^sub>\<sigma> \<noteq> v \<and> u\<^sub>\<sigma> \<noteq> w
	        \<and> u\<^sub>\<tau> \<noteq> v \<and> u\<^sub>\<tau> \<noteq> w
	        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<sigma>}) \<sigma>
	        \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v
	        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})
	        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
	        \<and> u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
	        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>
	        \<and> geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v
	        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})
	        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
	        \<and> u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
	        \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<noteq> geotop_convex_hull {w, u\<^sub>\<tau>})"
	    proof
	      assume hwL: "{w} \<in> geotop_link K v"
	      have hex_opposite:
	        "\<exists>e \<sigma> \<tau> V\<^sub>\<sigma> V\<^sub>\<tau> u\<^sub>\<sigma> u\<^sub>\<tau>.
	          e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
	          \<and> \<sigma> \<noteq> \<tau>
	          \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
	          \<and> geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>
	          \<and> v \<in> V\<^sub>\<sigma> \<and> w \<in> V\<^sub>\<sigma> \<and> u\<^sub>\<sigma> \<in> V\<^sub>\<sigma>
	          \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
	          \<and> geotop_simplex_vertices \<tau> V\<^sub>\<tau>
	          \<and> v \<in> V\<^sub>\<tau> \<and> w \<in> V\<^sub>\<tau> \<and> u\<^sub>\<tau> \<in> V\<^sub>\<tau>
	          \<and> u\<^sub>\<sigma> \<noteq> v \<and> u\<^sub>\<sigma> \<noteq> w
	          \<and> u\<^sub>\<tau> \<noteq> v \<and> u\<^sub>\<tau> \<noteq> w
	          \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<sigma>}) \<sigma>
	          \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v
	          \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})
	          \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
	          \<and> u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
	          \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>
	          \<and> geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v
	          \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})
	          \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
	          \<and> u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
	        by (rule mp[OF spec[OF hlink_vertices_two_opposite_vertex_face_link_edges] hwL])
	      obtain e \<sigma> \<tau> V\<^sub>\<sigma> V\<^sub>\<tau> u\<^sub>\<sigma> u\<^sub>\<tau> where heK: "e \<in> K"
	        and hedge: "geotop_is_edge e"
	        and hv_e: "v \<in> e"
	        and hw_e: "w \<in> e"
	        and h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
	        and h\<sigma>K: "\<sigma> \<in> K"
	        and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
	        and h\<sigma>face: "geotop_is_face e \<sigma>"
	        and hV\<sigma>: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>"
	        and hvV\<sigma>: "v \<in> V\<^sub>\<sigma>"
	        and hwV\<sigma>: "w \<in> V\<^sub>\<sigma>"
	        and huV\<sigma>: "u\<^sub>\<sigma> \<in> V\<^sub>\<sigma>"
	        and h\<tau>K: "\<tau> \<in> K"
	        and h\<tau>2: "geotop_simplex_dim \<tau> 2"
	        and h\<tau>face: "geotop_is_face e \<tau>"
	        and hV\<tau>: "geotop_simplex_vertices \<tau> V\<^sub>\<tau>"
	        and hvV\<tau>: "v \<in> V\<^sub>\<tau>"
	        and hwV\<tau>: "w \<in> V\<^sub>\<tau>"
	        and huV\<tau>: "u\<^sub>\<tau> \<in> V\<^sub>\<tau>"
	        and hu\<sigma>_ne_v: "u\<^sub>\<sigma> \<noteq> v"
	        and hu\<sigma>_ne_w: "u\<^sub>\<sigma> \<noteq> w"
	        and hu\<tau>_ne_v: "u\<^sub>\<tau> \<noteq> v"
	        and hu\<tau>_ne_w: "u\<^sub>\<tau> \<noteq> w"
	        and hface_l\<sigma>: "geotop_is_face (geotop_convex_hull {w, u\<^sub>\<sigma>}) \<sigma>"
	        and hl\<sigma>L: "geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v"
	        and hl\<sigma>edge: "geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})"
	        and hw_l\<sigma>: "w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}"
	        and hu\<sigma>_l\<sigma>: "u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}"
	        and hface_l\<tau>: "geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>"
	        and hl\<tau>L: "geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v"
	        and hl\<tau>edge: "geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})"
	        and hw_l\<tau>: "w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
	        and hu\<tau>_l\<tau>: "u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
	        using hex_opposite by (elim exE conjE)
	      have hv_ne_w: "v \<noteq> w"
	        using hwL unfolding geotop_link_def by (by100 blast)
	      have hdistinct:
	        "geotop_convex_hull {w, u\<^sub>\<sigma>} \<noteq> geotop_convex_hull {w, u\<^sub>\<tau>}"
	        by (rule geotop_two_2simplex_opposite_edges_distinct_dev34
	            [OF h\<sigma>2 h\<tau>2 hV\<sigma> hV\<tau> h\<sigma>\<tau> hv_ne_w hvV\<sigma> hwV\<sigma> huV\<sigma>
	                hvV\<tau> hwV\<tau> huV\<tau> hu\<sigma>_ne_v hu\<sigma>_ne_w hu\<tau>_ne_v hu\<tau>_ne_w])
	      show "\<exists>e \<sigma> \<tau> V\<^sub>\<sigma> V\<^sub>\<tau> u\<^sub>\<sigma> u\<^sub>\<tau>.
	        e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
	        \<and> \<sigma> \<noteq> \<tau>
	        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
	        \<and> geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>
	        \<and> v \<in> V\<^sub>\<sigma> \<and> w \<in> V\<^sub>\<sigma> \<and> u\<^sub>\<sigma> \<in> V\<^sub>\<sigma>
	        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
	        \<and> geotop_simplex_vertices \<tau> V\<^sub>\<tau>
	        \<and> v \<in> V\<^sub>\<tau> \<and> w \<in> V\<^sub>\<tau> \<and> u\<^sub>\<tau> \<in> V\<^sub>\<tau>
	        \<and> u\<^sub>\<sigma> \<noteq> v \<and> u\<^sub>\<sigma> \<noteq> w
	        \<and> u\<^sub>\<tau> \<noteq> v \<and> u\<^sub>\<tau> \<noteq> w
	        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<sigma>}) \<sigma>
	        \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v
	        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})
	        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
	        \<and> u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
	        \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>
	        \<and> geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v
	        \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})
	        \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
	        \<and> u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
	        \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<noteq> geotop_convex_hull {w, u\<^sub>\<tau>}"
	        using heK hedge hv_e hw_e h\<sigma>\<tau> h\<sigma>K h\<sigma>2 h\<sigma>face hV\<sigma> hvV\<sigma> hwV\<sigma> huV\<sigma>
	          h\<tau>K h\<tau>2 h\<tau>face hV\<tau> hvV\<tau> hwV\<tau> huV\<tau>
	          hu\<sigma>_ne_v hu\<sigma>_ne_w hu\<tau>_ne_v hu\<tau>_ne_w
	          hface_l\<sigma> hl\<sigma>L hl\<sigma>edge hw_l\<sigma> hu\<sigma>_l\<sigma>
	          hface_l\<tau> hl\<tau>L hl\<tau>edge hw_l\<tau> hu\<tau>_l\<tau> hdistinct
	        by (by100 blast)
	    qed
	  qed
	  \<comment> \<open>L5: link |L(v)| is connected.\<close>
	  have hL5: "top1_connected_on (\<Union>(geotop_link K v))
	               (subspace_topology UNIV geotop_euclidean_topology
	                  (\<Union>(geotop_link K v)))"
	    by (rule geotop_2_manifold_link_polyhedron_connected_from_vertex_star_dev34
	        [OF hK hM hv])
  \<comment> \<open>L6: link is a polygon (single 1-sphere from L2-L4 + L5).\<close>
  have hL6: "geotop_is_polygon (\<Union>(geotop_link K v))"
  proof -
    have hlink_complex: "geotop_is_complex (geotop_link K v)"
      by (rule geotop_link_is_complex[OF hK])
    have hlink_nonempty: "\<Union>(geotop_link K v) \<noteq> {}"
      using hL1_link_poly_nonempty .
    have hcomponent_nonisolated_witnesses:
      "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
          C = geotop_component_at UNIV geotop_euclidean_topology
                (\<Union>(geotop_link K v)) P)
        \<longrightarrow> (\<exists>L. geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> geotop_complex_connected L
          \<and> (\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>l\<in>L. geotop_is_edge l \<and> w \<in> l)))"
      by (rule geotop_link_components_nonisolated_subcomplex_witnesses
          [OF hK hv hlink_vertices_incident_edges])
	    have hcomponent_linear_graph_witnesses:
	      "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
	          C = geotop_component_at UNIV geotop_euclidean_topology
	                (\<Union>(geotop_link K v)) P)
	        \<longrightarrow> (\<exists>L. geotop_is_linear_graph L
	          \<and> finite L
	          \<and> geotop_polyhedron L = C
	          \<and> geotop_complex_connected L
	          \<and> (\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>l\<in>L. geotop_is_edge l \<and> w \<in> l)))"
	      by (rule geotop_link_components_nonisolated_linear_graph_witnesses
	          [OF hK hv hlink_vertices_incident_edges])
	    have hlink_vertices_two_distinct_incident_edges:
	      "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
	        (\<exists>l\<^sub>1 l\<^sub>2. l\<^sub>1 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
	          \<and> l\<^sub>2 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
	          \<and> l\<^sub>1 \<noteq> l\<^sub>2)"
	    proof (intro allI impI)
	      fix w
	      assume hwL: "{w} \<in> geotop_link K v"
	      have hex_distinct:
	        "\<exists>e \<sigma> \<tau> V\<^sub>\<sigma> V\<^sub>\<tau> u\<^sub>\<sigma> u\<^sub>\<tau>.
	          e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
	          \<and> \<sigma> \<noteq> \<tau>
	          \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
	          \<and> geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>
	          \<and> v \<in> V\<^sub>\<sigma> \<and> w \<in> V\<^sub>\<sigma> \<and> u\<^sub>\<sigma> \<in> V\<^sub>\<sigma>
	          \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
	          \<and> geotop_simplex_vertices \<tau> V\<^sub>\<tau>
	          \<and> v \<in> V\<^sub>\<tau> \<and> w \<in> V\<^sub>\<tau> \<and> u\<^sub>\<tau> \<in> V\<^sub>\<tau>
	          \<and> u\<^sub>\<sigma> \<noteq> v \<and> u\<^sub>\<sigma> \<noteq> w
	          \<and> u\<^sub>\<tau> \<noteq> v \<and> u\<^sub>\<tau> \<noteq> w
	          \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<sigma>}) \<sigma>
	          \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v
	          \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})
	          \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
	          \<and> u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}
	          \<and> geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>
	          \<and> geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v
	          \<and> geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})
	          \<and> w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
	          \<and> u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>}
	          \<and> geotop_convex_hull {w, u\<^sub>\<sigma>} \<noteq> geotop_convex_hull {w, u\<^sub>\<tau>}"
	        by (rule mp[OF spec[OF hlink_vertices_two_distinct_opposite_link_edges] hwL])
	      obtain e \<sigma> \<tau> V\<^sub>\<sigma> V\<^sub>\<tau> u\<^sub>\<sigma> u\<^sub>\<tau> where
	        hl\<sigma>L: "geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v"
	        and hl\<sigma>edge: "geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})"
	        and hw_l\<sigma>: "w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}"
	        and hl\<tau>L: "geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v"
	        and hl\<tau>edge: "geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})"
	        and hw_l\<tau>: "w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
	        and hl_distinct: "geotop_convex_hull {w, u\<^sub>\<sigma>} \<noteq> geotop_convex_hull {w, u\<^sub>\<tau>}"
	        using hex_distinct by (elim exE conjE)
	      show "\<exists>l\<^sub>1 l\<^sub>2. l\<^sub>1 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
	          \<and> l\<^sub>2 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
	          \<and> l\<^sub>1 \<noteq> l\<^sub>2"
	        using hl\<sigma>L hl\<sigma>edge hw_l\<sigma> hl\<tau>L hl\<tau>edge hw_l\<tau> hl_distinct
	        by (by100 blast)
		    qed
		    have hlink_vertices_two_exact_incident_edges:
		      "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
		        (\<exists>l\<^sub>1 l\<^sub>2. l\<^sub>1 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
		          \<and> l\<^sub>2 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
		          \<and> l\<^sub>1 \<noteq> l\<^sub>2
		          \<and> (\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
		              \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2))"
		    proof (intro allI impI)
		      fix w
		      assume hwL: "{w} \<in> geotop_link K v"
		      have hvK: "{v} \<in> K"
		        using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
		      have hexact_ex:
		        "\<exists>e \<sigma> \<tau> l\<^sub>\<sigma> l\<^sub>\<tau>. e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
		          \<and> \<sigma> \<noteq> \<tau>
		          \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
		          \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
		          \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}
		          \<and> l\<^sub>\<sigma> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<sigma> \<and> w \<in> l\<^sub>\<sigma>
		          \<and> l\<^sub>\<tau> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<tau> \<and> w \<in> l\<^sub>\<tau>
		          \<and> l\<^sub>\<sigma> \<noteq> l\<^sub>\<tau>
		          \<and> (\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
		              \<longrightarrow> l = l\<^sub>\<sigma> \<or> l = l\<^sub>\<tau>)"
		        by (rule geotop_link_vertex_two_incident_link_edges_exhaust
		            [OF hK hvK hwL hL_two_faces])
		      obtain e \<sigma> \<tau> l\<^sub>\<sigma> l\<^sub>\<tau> where hexact_w:
		        "e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
		          \<and> \<sigma> \<noteq> \<tau>
		          \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
		          \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
		          \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}
		          \<and> l\<^sub>\<sigma> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<sigma> \<and> w \<in> l\<^sub>\<sigma>
		          \<and> l\<^sub>\<tau> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<tau> \<and> w \<in> l\<^sub>\<tau>
		          \<and> l\<^sub>\<sigma> \<noteq> l\<^sub>\<tau>
		          \<and> (\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
		              \<longrightarrow> l = l\<^sub>\<sigma> \<or> l = l\<^sub>\<tau>)"
		        using hexact_ex by (elim exE)
		      have hl\<sigma>L: "l\<^sub>\<sigma> \<in> geotop_link K v"
		        using hexact_w by (by100 blast)
		      have hl\<sigma>edge: "geotop_is_edge l\<^sub>\<sigma>"
		        using hexact_w by (by100 blast)
		      have hw_l\<sigma>: "w \<in> l\<^sub>\<sigma>"
		        using hexact_w by (by100 blast)
		      have hl\<tau>L: "l\<^sub>\<tau> \<in> geotop_link K v"
		        using hexact_w by (by100 blast)
		      have hl\<tau>edge: "geotop_is_edge l\<^sub>\<tau>"
		        using hexact_w by (by100 blast)
		      have hw_l\<tau>: "w \<in> l\<^sub>\<tau>"
		        using hexact_w by (by100 blast)
		      have hl_distinct: "l\<^sub>\<sigma> \<noteq> l\<^sub>\<tau>"
		        using hexact_w by (by100 blast)
		      have hexact: "\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
		          \<longrightarrow> l = l\<^sub>\<sigma> \<or> l = l\<^sub>\<tau>"
		        using hexact_w by (by100 simp)
		      show "\<exists>l\<^sub>1 l\<^sub>2. l\<^sub>1 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
		          \<and> l\<^sub>2 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
		          \<and> l\<^sub>1 \<noteq> l\<^sub>2
		          \<and> (\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
		              \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2)"
		        using hl\<sigma>L hl\<sigma>edge hw_l\<sigma> hl\<tau>L hl\<tau>edge hw_l\<tau> hl_distinct hexact
		        by (by100 blast)
		    qed
		    have hcomponent_two_distinct_edge_witnesses:
		      "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
		          C = geotop_component_at UNIV geotop_euclidean_topology
		                (\<Union>(geotop_link K v)) P)
	        \<longrightarrow> (\<exists>L. geotop_is_complex L
	          \<and> geotop_complex_is_1dim L
	          \<and> finite L
	          \<and> geotop_polyhedron L = C
	          \<and> geotop_complex_connected L
	          \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
	            (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
	              geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
	              \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
	              \<and> l\<^sub>1 \<noteq> l\<^sub>2)))"
	    proof (intro allI impI)
	      fix C
	      assume hC_ex: "\<exists>P\<in>\<Union>(geotop_link K v).
	          C = geotop_component_at UNIV geotop_euclidean_topology
	                (\<Union>(geotop_link K v)) P"
	      obtain P where hP: "P \<in> \<Union>(geotop_link K v)"
	        and hC: "C = geotop_component_at UNIV geotop_euclidean_topology
	                (\<Union>(geotop_link K v)) P"
	        using hC_ex by (by100 blast)
	      show "\<exists>L. geotop_is_complex L
	          \<and> geotop_complex_is_1dim L
	          \<and> finite L
	          \<and> geotop_polyhedron L = C
	          \<and> geotop_complex_connected L
	          \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
	            (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
	              geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
	              \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
	              \<and> l\<^sub>1 \<noteq> l\<^sub>2))"
		        by (rule geotop_link_component_two_distinct_subcomplex_witness
		            [OF hK hv hP hC hlink_vertices_two_distinct_incident_edges])
		    qed
		    have hcomponent_two_exact_edge_witnesses:
		      "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
		          C = geotop_component_at UNIV geotop_euclidean_topology
		                (\<Union>(geotop_link K v)) P)
		        \<longrightarrow> (\<exists>L. geotop_is_complex L
		          \<and> geotop_complex_is_1dim L
		          \<and> finite L
		          \<and> geotop_polyhedron L = C
		          \<and> geotop_complex_connected L
		          \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
		            (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
		              geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
		              \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
		              \<and> l\<^sub>1 \<noteq> l\<^sub>2
		              \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
		                  \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2))))"
		    proof (intro allI impI)
		      fix C
		      assume hC_ex: "\<exists>P\<in>\<Union>(geotop_link K v).
		          C = geotop_component_at UNIV geotop_euclidean_topology
		                (\<Union>(geotop_link K v)) P"
		      obtain P where hP: "P \<in> \<Union>(geotop_link K v)"
		        and hC: "C = geotop_component_at UNIV geotop_euclidean_topology
		                (\<Union>(geotop_link K v)) P"
		        using hC_ex by (by100 blast)
		      show "\<exists>L. geotop_is_complex L
		          \<and> geotop_complex_is_1dim L
		          \<and> finite L
		          \<and> geotop_polyhedron L = C
		          \<and> geotop_complex_connected L
		          \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
		            (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
		              geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
		              \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
		              \<and> l\<^sub>1 \<noteq> l\<^sub>2
		              \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
		                  \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2)))"
		        by (rule geotop_link_component_two_exact_subcomplex_witness
		            [OF hK hv hP hC hlink_vertices_two_exact_incident_edges])
		    qed
		    have hcomponent_two_exact_no_endpoint_linear_graph_witnesses:
		      "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
		          C = geotop_component_at UNIV geotop_euclidean_topology
		                (\<Union>(geotop_link K v)) P)
		        \<longrightarrow> (\<exists>L. geotop_is_linear_graph L
		          \<and> finite L
		          \<and> geotop_polyhedron L = C
		          \<and> geotop_complex_connected L
		          \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
		            (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
		              geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
		              \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
		              \<and> l\<^sub>1 \<noteq> l\<^sub>2
		              \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
		                  \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2)))
		          \<and> (\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w))"
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
		            (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
		              geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
		              \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
		              \<and> l\<^sub>1 \<noteq> l\<^sub>2
		              \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
		                  \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2)))
		          \<and> (\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w)"
		        by (rule geotop_link_component_two_exact_no_endpoint_linear_graph_witness
		            [OF hK hv hP hC hlink_vertices_two_exact_incident_edges])
		    qed
		    have hcomponent_degree_two_linear_graph_witnesses:
		      "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
		          C = geotop_component_at UNIV geotop_euclidean_topology
		                (\<Union>(geotop_link K v)) P)
		        \<longrightarrow> (\<exists>L. geotop_is_linear_graph L
		          \<and> finite L
		          \<and> geotop_polyhedron L = C
		          \<and> geotop_complex_connected L
		          \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
		            (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
		              geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
		              \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
		              \<and> l\<^sub>1 \<noteq> l\<^sub>2
		              \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
		                  \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2)))
		          \<and> (\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w)
		          \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
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
		      have hL_ex: "\<exists>L. geotop_is_linear_graph L
		          \<and> finite L
		          \<and> geotop_polyhedron L = C
		          \<and> geotop_complex_connected L
		          \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
		            (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
		              geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
		              \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
		              \<and> l\<^sub>1 \<noteq> l\<^sub>2
		              \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
		                  \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2)))
		          \<and> (\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w)"
		        by (rule geotop_link_component_two_exact_no_endpoint_linear_graph_witness
		            [OF hK hv hP hC hlink_vertices_two_exact_incident_edges])
		      obtain L where hL_linear: "geotop_is_linear_graph L"
		        and hL_fin: "finite L"
		        and hL_poly: "geotop_polyhedron L = C"
		        and hL_conn: "geotop_complex_connected L"
		        and hL_two: "\<forall>w. {w} \<in> L \<longrightarrow>
		            (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
		              geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
		              \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
		              \<and> l\<^sub>1 \<noteq> l\<^sub>2
			              \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
			                  \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2))"
		        and hL_noend: "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
		        using hL_ex by (elim exE conjE)
		      have hL_degree: "\<forall>w. {w} \<in> L \<longrightarrow>
		          card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 2"
		        by (rule geotop_exact_two_incident_edges_card_eq_two_dev34[OF hL_fin hL_two])
		      show "\<exists>L. geotop_is_linear_graph L
		          \<and> finite L
		          \<and> geotop_polyhedron L = C
		          \<and> geotop_complex_connected L
		          \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
		            (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
		              geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
		              \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
		              \<and> l\<^sub>1 \<noteq> l\<^sub>2
		              \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
		                  \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2)))
		          \<and> (\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w)
		          \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
		              card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 2)"
		        using hL_linear hL_fin hL_poly hL_conn hL_two hL_noend hL_degree
		        by (by100 blast)
		    qed
		    have hlocal_polygon_components:
		      "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
		             C = geotop_component_at UNIV geotop_euclidean_topology
	                   (\<Union>(geotop_link K v)) P)
          \<longrightarrow> geotop_is_polygon C"
    proof (intro allI impI)
      fix C
      assume hC_ex: "\<exists>P\<in>\<Union>(geotop_link K v).
             C = geotop_component_at UNIV geotop_euclidean_topology
                   (\<Union>(geotop_link K v)) P"
      obtain P where hP: "P \<in> \<Union>(geotop_link K v)"
        and hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                   (\<Union>(geotop_link K v)) P"
        using hC_ex by (by100 blast)
      have hP_C: "P \<in> C"
        using geotop_link_component_summary[OF hK hv hP hC] by (by100 blast)
      have hC_imp: "(\<exists>P\<in>\<Union>(geotop_link K v).
             C = geotop_component_at UNIV geotop_euclidean_topology
                   (\<Union>(geotop_link K v)) P) \<longrightarrow>
          (\<exists>L. geotop_is_linear_graph L
            \<and> finite L
            \<and> geotop_polyhedron L = C
            \<and> geotop_complex_connected L
            \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
              (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
                geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
                \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
                \<and> l\<^sub>1 \<noteq> l\<^sub>2
                \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
                    \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2)))
            \<and> (\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w)
            \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
                card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 2))"
        by (rule spec[OF hcomponent_degree_two_linear_graph_witnesses])
      have hL_ex: "\<exists>L. geotop_is_linear_graph L
            \<and> finite L
            \<and> geotop_polyhedron L = C
            \<and> geotop_complex_connected L
            \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
              (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
                geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
                \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
                \<and> l\<^sub>1 \<noteq> l\<^sub>2
                \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
                    \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2)))
            \<and> (\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w)
            \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
                card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 2)"
        by (rule mp[OF hC_imp hC_ex])
      obtain L where hL_linear: "geotop_is_linear_graph L"
        and hL_fin: "finite L"
        and hL_poly: "geotop_polyhedron L = C"
        and hL_conn: "geotop_complex_connected L"
        and hL_degree: "\<forall>w. {w} \<in> L \<longrightarrow>
                card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 2"
        using hL_ex by (elim exE conjE)
      have hL_nonempty: "L \<noteq> {}"
        using hP_C hL_poly unfolding geotop_polyhedron_def by (by100 blast)
      have hpoly_L: "geotop_is_polygon (geotop_polyhedron L)"
        by (rule geotop_finite_connected_degree_two_linear_graph_polygon_dev34
            [OF hL_linear hL_fin hL_nonempty hL_conn hL_degree])
      show "geotop_is_polygon C"
        using hpoly_L hL_poly by (by100 simp)
    qed
    have hsingle_polygon_from_connected:
      "geotop_is_polygon (\<Union>(geotop_link K v))"
    proof -
      obtain P where hP: "P \<in> \<Union>(geotop_link K v)"
        using hlink_nonempty by (by100 blast)
      let ?C = "geotop_component_at UNIV geotop_euclidean_topology
                   (\<Union>(geotop_link K v)) P"
      have hC_polygon: "geotop_is_polygon ?C"
        using hlocal_polygon_components hP by (by100 blast)
      have hC_eq: "?C = \<Union>(geotop_link K v)"
        by (rule geotop_connected_component_at_eq_self[OF hP hL5])
      show ?thesis
        using hC_polygon hC_eq by (by100 simp)
    qed
    show ?thesis
      using hsingle_polygon_from_connected .
  qed
  \<comment> \<open>L7 (main conclusion): Star is a combinatorial 2-cell.\<close>
  have hL7: "geotop_comb_n_cell (geotop_star K v) 2"
  proof -
    have hshape:
      "geotop_is_broken_line (\<Union>(geotop_link K v))
        \<or> geotop_is_polygon (\<Union>(geotop_link K v))"
      using hL6 by (by100 blast)
    show ?thesis
      by (rule geotop_vertex_star_comb_2cell_from_link_line_or_polygon_dev34
          [OF hK hv hshape])
  qed
  have hL_all:
    "(\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e) \<and>
     (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
             (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>)) \<and>
     (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
             card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 1) \<and>
     (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
             card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 2) \<and>
     (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
             \<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2 \<longrightarrow>
             (\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
               \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
               \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
               \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3)) \<and>
     (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
             card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2) \<and>
     (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
             card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2) \<and>
     (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
             (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
               \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
               \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
               \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>})) \<and>
     top1_connected_on (\<Union>(geotop_link K v))
               (subspace_topology UNIV geotop_euclidean_topology (\<Union>(geotop_link K v))) \<and>
     geotop_is_polygon (\<Union>(geotop_link K v)) \<and>
     geotop_comb_n_cell (geotop_star K v) 2"
    using hL1 hL2 hL2_count hL3 hL4_counterexample_faces hL4 hL_count_eq2
      hL_two_faces hL5 hL6 hL7
    by (by100 blast)
  show "geotop_comb_n_cell (geotop_star K v) 2" using hL7 .
qed

lemma geotop_manifold_interior_if_HOL_interior_early_dev34:
  fixes M :: "(real^2) set"
  assumes hP: "P \<in> interior M"
  shows "P \<in> geotop_manifold_interior M (\<lambda>x y. norm (x - y))"
  (**
    Ordinary Euclidean interior points have a ball neighborhood in \<open>M\<close>;
    that ball is homeomorphic to the plane, so it is a manifold-interior
    chart. **)
proof -
  obtain r where hr: "0 < r" and hball_sub_int: "ball P r \<subseteq> interior M"
  proof -
    have "\<forall>x\<in>interior M. \<exists>e>0. ball x e \<subseteq> interior M"
      using open_interior open_contains_ball by (by100 blast)
    thus ?thesis using hP that by (by100 blast)
  qed
  let ?U = "ball P r"
  have hU_sub_M: "?U \<subseteq> M"
    using hball_sub_int interior_subset by (by100 blast)
  have hP_U: "P \<in> ?U"
    using hr by (by100 simp)
  have hP_M: "P \<in> M"
    using hP_U hU_sub_M by (by100 blast)
  have hU_geotop_open: "?U \<in> geotop_euclidean_topology"
    using open_ball unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have hU_subspace: "?U \<in> subspace_topology UNIV geotop_euclidean_topology M"
  proof -
    have "?U = M \<inter> ?U"
      using hU_sub_M by (by100 blast)
    thus ?thesis
      unfolding subspace_topology_def using hU_geotop_open by (by100 blast)
  qed
  have htopM: "top1_metric_topology_on M (\<lambda>x y. norm (x - y)) =
               subspace_topology UNIV geotop_euclidean_topology M"
    by (rule top1_norm_metric_topology_on_eq_geotop_subspace_early)
  have hU_openin: "openin_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) ?U"
    unfolding openin_on_def using htopM hU_sub_M hU_subspace by (by100 simp)
  obtain f where hf:
    "top1_homeomorphism_on ?U
        (subspace_topology UNIV geotop_euclidean_topology ?U)
        (UNIV::(real^2) set) (subspace_topology UNIV geotop_euclidean_topology UNIV) f"
    using geotop_HOL_homeomorphic_imp_top1_homeomorphism_on[
        OF homeomorphic_ball_UNIV[OF hr]]
    by (by100 blast)
  have hUNIV: "subspace_topology UNIV geotop_euclidean_topology (UNIV::(real^2) set) =
               geotop_euclidean_topology"
    by (rule subspace_topology_self_carrier) (by100 simp)
  have hf_geo:
    "top1_homeomorphism_on ?U
        (subspace_topology UNIV geotop_euclidean_topology ?U)
        (UNIV::(real^2) set) geotop_euclidean_topology f"
    using hf hUNIV by (by100 simp)
  have hsubU:
    "subspace_topology M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) ?U =
     subspace_topology UNIV geotop_euclidean_topology ?U"
  proof -
    have "subspace_topology M (subspace_topology UNIV geotop_euclidean_topology M) ?U =
          subspace_topology UNIV geotop_euclidean_topology ?U"
      by (rule subspace_topology_trans[OF hU_sub_M])
    thus ?thesis using htopM by (by100 simp)
  qed
  have hf_metric:
    "top1_homeomorphism_on ?U
        (subspace_topology M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) ?U)
        (UNIV::(real^2) set) geotop_euclidean_topology f"
    using hf_geo hsubU by (by100 simp)
  show ?thesis
    unfolding geotop_manifold_interior_def
    using hP_M hU_openin hP_U hf_metric by (by100 blast)
qed

lemma geotop_2simplex_rel_interior_subset_manifold_interior_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  shows "rel_interior \<sigma>
      \<subseteq> geotop_manifold_interior (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  (**
    First local case for the converse boundary inclusion in Moise Theorem 9:
    a point in the interior of a 2-simplex is an ordinary interior point of
    the polyhedron, hence not a manifold-boundary point. **)
proof
  fix p
  assume hp: "p \<in> rel_interior \<sigma>"
  have h\<sigma>_subM: "\<sigma> \<subseteq> geotop_polyhedron K"
    using h\<sigma>K unfolding geotop_polyhedron_def by (by100 blast)
  have hhyper: "geotop_hyperplane_dim (affine hull \<sigma>) 2"
    by (rule geotop_simplex_dim_imp_hyperplane_dim[OF h\<sigma>2])
  have hdim\<sigma>: "aff_dim \<sigma> = 2"
    using geotop_hyperplane_dim_imp_affine_aff_dim[OF hhyper] by (by100 simp)
  have hdim_UNIV: "aff_dim \<sigma> = int (DIM(real^2))"
    using hdim\<sigma> by (by100 simp)
  have hrel_eq_int: "rel_interior \<sigma> = interior \<sigma>"
    by (rule interior_rel_interior[OF hdim_UNIV])
  have hp_int_\<sigma>: "p \<in> interior \<sigma>"
    using hp hrel_eq_int by (by100 simp)
  have hp_int_M: "p \<in> interior (geotop_polyhedron K)"
    using interior_mono[OF h\<sigma>_subM] hp_int_\<sigma> by (by100 blast)
  show "p \<in> geotop_manifold_interior (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
    by (rule geotop_manifold_interior_if_HOL_interior_early_dev34[OF hp_int_M])
qed

lemma geotop_manifold_boundary_disjoint_2simplex_rel_interior_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hbd: "p \<in> geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  shows "p \<notin> rel_interior \<sigma>"
  (**
    Converse-boundary bookkeeping for Theorem 9: a carrier 2-simplex would
    put \<open>p\<close> in the manifold interior, contradicting \<open>p \<in> Bd |K|\<close>. **)
proof
  assume hp_rel: "p \<in> rel_interior \<sigma>"
  have hp_int: "p \<in> geotop_manifold_interior (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  proof -
    have hsub: "rel_interior \<sigma>
        \<subseteq> geotop_manifold_interior (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
      by (rule geotop_2simplex_rel_interior_subset_manifold_interior_dev34
          [OF hK h\<sigma>K h\<sigma>2])
    show ?thesis
      using hsub hp_rel by (by100 blast)
  qed
  have hp_not_int: "p \<notin> geotop_manifold_interior (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
    using hbd unfolding geotop_manifold_boundary_def by (by100 blast)
  show False
    using hp_int hp_not_int by (by100 blast)
qed

lemma geotop_manifold_boundary_carrier_dim_le_1_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hbd: "p \<in> geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes hp\<tau>: "p \<in> rel_interior \<tau>"
  shows "\<exists>n. n \<le> 1 \<and> geotop_simplex_dim \<tau> n"
  (**
    Carrier case split for the converse inclusion in Theorem 9.  The carrier
    of a boundary point is not a 2-simplex, because 2-simplex relative
    interiors are manifold-interior points. **)
proof -
  have h_simp_all: "\<forall>\<rho>\<in>K. geotop_is_simplex \<rho>"
    by (rule conjunct1[OF hK[unfolded geotop_is_complex_def]])
  have h\<tau>simp: "geotop_is_simplex \<tau>"
    by (rule bspec[OF h_simp_all h\<tau>K])
  obtain n where h\<tau>dim: "geotop_simplex_dim \<tau> n"
    using h\<tau>simp unfolding geotop_is_simplex_def geotop_simplex_dim_def
    by (by100 blast)
  have hnle2: "n \<le> 2"
    by (rule geotop_simplex_dim_le_2_R2[OF h\<tau>dim])
  have hnnot2: "n \<noteq> 2"
  proof
    assume hn2: "n = 2"
    have h\<tau>2: "geotop_simplex_dim \<tau> 2"
      using h\<tau>dim hn2 by (by100 simp)
    have hp_not: "p \<notin> rel_interior \<tau>"
      by (rule geotop_manifold_boundary_disjoint_2simplex_rel_interior_dev34
          [OF hK hbd h\<tau>K h\<tau>2])
    show False
      using hp\<tau> hp_not by (by100 blast)
  qed
  have hnle1: "n \<le> 1"
    using hnle2 hnnot2 by (by100 arith)
  show ?thesis
    using hnle1 h\<tau>dim by (by100 blast)
qed

lemma geotop_manifold_boundary_has_low_dim_carrier_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hbd: "p \<in> geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  shows "\<exists>\<tau> n. \<tau> \<in> K \<and> p \<in> rel_interior \<tau>
      \<and> n \<le> 1 \<and> geotop_simplex_dim \<tau> n"
  (**
    Beginning of the converse boundary inclusion case split: a boundary point
    has a carrier, and that carrier is either a vertex or an edge. **)
proof -
  have hpM: "p \<in> geotop_polyhedron K"
    using hbd unfolding geotop_manifold_boundary_def by (by100 blast)
  obtain \<tau> where h\<tau>K: "\<tau> \<in> K" and hp\<tau>: "p \<in> rel_interior \<tau>"
    using geotop_complex_polyhedron_point_carrier_local_dev34[OF hK hpM]
    by (by100 blast)
  obtain n where hnle1: "n \<le> 1" and h\<tau>dim: "geotop_simplex_dim \<tau> n"
    using geotop_manifold_boundary_carrier_dim_le_1_dev34
      [OF hK hbd h\<tau>K hp\<tau>]
    by (by100 blast)
  show ?thesis
    using h\<tau>K hp\<tau> hnle1 h\<tau>dim by (by100 blast)
qed

lemma geotop_0simplex_contains_point_eq_singleton_dev34:
  fixes \<tau> :: "(real^2) set"
  assumes h\<tau>0: "geotop_simplex_dim \<tau> 0"
  assumes hp\<tau>: "p \<in> \<tau>"
  shows "\<tau> = {p}"
  (**
    Elementary 0-simplex carrier fact: a 0-simplex is the convex hull of one
    vertex, so any point it contains is that vertex. **)
proof -
  have hex: "\<exists>V m. finite V \<and> card V = 0 + 1 \<and> 0 \<le> m
      \<and> geotop_general_position V m \<and> \<tau> = geotop_convex_hull V"
    using h\<tau>0 unfolding geotop_simplex_dim_def by (by100 simp)
  obtain V m where hVm:
    "finite V \<and> card V = 0 + 1 \<and> 0 \<le> m
      \<and> geotop_general_position V m \<and> \<tau> = geotop_convex_hull V"
    using hex by (elim exE)
  have hVfin: "finite V" using hVm by (by100 simp)
  have hVcard: "card V = 1" using hVm by (by100 simp)
  have h\<tau>V: "\<tau> = geotop_convex_hull V" using hVm by (by100 simp)
  obtain v where hVeq: "V = {v}"
    by (rule card_1_singletonE[OF hVcard])
  have hconv_single: "geotop_convex_hull {v} = {v}"
  proof -
    have "geotop_convex_hull {v} = convex hull {v}"
      by (rule geotop_convex_hull_eq_HOL)
    also have "... = {v}"
      by (by100 simp)
    finally show ?thesis .
  qed
  have h\<tau>eq: "\<tau> = {v}"
    using h\<tau>V hVeq hconv_single by (by100 simp)
  have hpv: "p = v"
    using hp\<tau> h\<tau>eq by (by100 blast)
  show ?thesis
    using h\<tau>eq hpv by (by100 simp)
qed

lemma geotop_boundary_0carrier_is_complex_vertex_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes h\<tau>0: "geotop_simplex_dim \<tau> 0"
  assumes hp\<tau>: "p \<in> rel_interior \<tau>"
  shows "p \<in> geotop_complex_vertices K"
  (**
    Vertex-carrier branch bookkeeping: if the carrier of \<open>p\<close> is
    0-dimensional, then \<open>{p}\<close> is a simplex of \<open>K\<close>. **)
proof -
  have hp\<tau>_set: "p \<in> \<tau>"
    using hp\<tau> rel_interior_subset by (by100 blast)
  have h\<tau>eq: "\<tau> = {p}"
    by (rule geotop_0simplex_contains_point_eq_singleton_dev34[OF h\<tau>0 hp\<tau>_set])
  have hpK: "{p} \<in> K"
    using h\<tau>K h\<tau>eq by (by100 simp)
  show ?thesis
    using geotop_complex_vertices_eq_0_simplexes[OF hK] hpK by (by100 blast)
qed

lemma geotop_edge_face_count_one_or_two_in_manifold_with_boundary_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  shows "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1
      \<or> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
  (**
    Moise Theorem 9 edge count, extracted from the vertex-local proof:
    no edge can be incident to zero 2-simplexes, and no edge can be incident
    to three or more 2-simplexes. **)
proof -
  let ?S = "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
  have h2_exists: "\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>"
  proof (rule ccontr)
    assume hno2: "\<not> (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>)"
    have hrel_open:
      "rel_interior e \<in>
        subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
      by (rule geotop_complex_no_2_simplex_over_edge_rel_interior_open
          [OF hK heK hedge hno2])
    have hrel_sub: "rel_interior e \<subseteq> geotop_polyhedron K"
      using heK rel_interior_subset unfolding geotop_polyhedron_def by (by100 blast)
    show False
      by (rule geotop_2_manifold_with_boundary_no_open_edge_rel_interior
          [OF hKM hedge hrel_open hrel_sub])
  qed
  have hge: "card ?S \<ge> 1"
    by (rule geotop_complex_edge_in_2_simplex_imp_face_count_ge_1
        [OF hK heK hedge h2_exists])
  have hle: "card ?S \<le> 2"
  proof (rule ccontr)
    assume hnot_le2: "\<not> card ?S \<le> 2"
    have hge3: "3 \<le> card ?S"
      using hnot_le2 by (by100 simp)
    have hfaces_ex:
        "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
          \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
          \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
          \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
      by (rule geotop_complex_edge_face_count_ge_3_obtain[OF hge3])
    obtain p where hp: "p \<in> rel_interior e"
      using geotop_edge_rel_interior_nonempty[OF hedge] by (by100 blast)
    have hpM: "p \<in> geotop_polyhedron K"
      using heK hp rel_interior_subset unfolding geotop_polyhedron_def by (by100 blast)
    let ?M = "geotop_polyhedron K"
    let ?d = "\<lambda>x y. norm (x - y)"
    let ?TM = "top1_metric_topology_on ?M ?d"
    obtain U where hUopen: "openin_on ?M ?TM U"
      and hpU: "p \<in> U"
      and hcell: "geotop_is_n_cell (closure_on ?M ?TM U)
          (subspace_topology ?M ?TM (closure_on ?M ?TM U)) 2"
      using hKM hpM unfolding geotop_n_manifold_with_boundary_on_def by (by100 blast)
    show False
      by (rule geotop_boundary_chart_three_incident_2simplex_contradiction_dev34
          [OF hK heK hedge hp hfaces_ex hUopen hpU hcell])
  qed
  show ?thesis
    using hge hle by (by100 arith)
qed

lemma geotop_edge_carrier_not_one_incident_count_two_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp_e: "p \<in> e"
  assumes hnot_one:
    "p \<notin> \<Union>{e\<in>K. geotop_is_edge e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
  shows "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
  (**
    Edge-carrier branch of Theorem 9's converse: the global one-or-two edge
    count leaves only the two-sided edge case if the point is not already in
    the union of one-incident edges. **)
proof -
  let ?S = "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
  have hcount: "card ?S = 1 \<or> card ?S = 2"
    by (rule geotop_edge_face_count_one_or_two_in_manifold_with_boundary_dev34
        [OF hK hKM heK hedge])
  show ?thesis
  proof (cases "card ?S = 1")
    case True
    have he_in_one: "e \<in> {e\<in>K. geotop_is_edge e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
      using heK hedge True by (by100 blast)
    have "p \<in> \<Union>{e\<in>K. geotop_is_edge e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
      using he_in_one hp_e by (by100 blast)
    show ?thesis
      using hnot_one \<open>p \<in> \<Union>{e\<in>K. geotop_is_edge e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}\<close>
      by (by100 blast)
  next
    case False
    show ?thesis
      using hcount False by (by100 blast)
  qed
qed

lemma geotop_vertex_not_one_incident_union_incident_edge_count_two_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes hnot_one:
    "v \<notin> \<Union>{e\<in>K. geotop_is_edge e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  shows "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
  (**
    Vertex-carrier branch of Theorem 9's converse: if the boundary point
    is not on any one-incident edge, then every edge through that vertex is
    two-sided. **)
proof -
  let ?S = "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
  have hcount: "card ?S = 1 \<or> card ?S = 2"
    by (rule geotop_edge_face_count_one_or_two_in_manifold_with_boundary_dev34
        [OF hK hKM heK hedge])
  show ?thesis
  proof (cases "card ?S = 1")
    case True
    have he_in_one: "e \<in> {e\<in>K. geotop_is_edge e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
      using heK hedge True by (by100 blast)
    have "v \<in> \<Union>{e\<in>K. geotop_is_edge e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
      using he_in_one hv_e by (by100 blast)
    show ?thesis
      using hnot_one \<open>v \<in> \<Union>{e\<in>K. geotop_is_edge e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}\<close>
      by (by100 blast)
  next
    case False
    show ?thesis
      using hcount False by (by100 blast)
  qed
qed

lemma geotop_boundary_not_one_incident_carrier_cases_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes hbd: "p \<in> geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  assumes hnot_one:
    "p \<notin> \<Union>{e\<in>K. geotop_is_edge e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
  shows "(\<exists>e. e \<in> K \<and> geotop_is_edge e \<and> p \<in> rel_interior e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2)
      \<or> (p \<in> geotop_complex_vertices K
        \<and> (\<forall>e\<in>K. geotop_is_edge e \<and> p \<in> e \<longrightarrow>
          card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2))"
  (**
    Converse-inclusion case split from Moise Theorem 9: after excluding
    one-incident edges, the low-dimensional carrier is either a two-sided edge
    or a vertex all of whose incident edges are two-sided. **)
proof -
  obtain \<tau> n where h\<tau>K: "\<tau> \<in> K"
    and hp\<tau>: "p \<in> rel_interior \<tau>"
    and hnle1: "n \<le> 1"
    and h\<tau>dim: "geotop_simplex_dim \<tau> n"
    using geotop_manifold_boundary_has_low_dim_carrier_dev34[OF hK hbd]
    by (by100 blast)
  show ?thesis
  proof (cases "n = 0")
    case True
    have h\<tau>0: "geotop_simplex_dim \<tau> 0"
      using h\<tau>dim True by (by100 simp)
    have hp_vertex: "p \<in> geotop_complex_vertices K"
      by (rule geotop_boundary_0carrier_is_complex_vertex_dev34
          [OF hK h\<tau>K h\<tau>0 hp\<tau>])
    have hall_edges: "\<forall>e\<in>K. geotop_is_edge e \<and> p \<in> e \<longrightarrow>
        card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
    proof (intro ballI impI)
      fix e
      assume heK: "e \<in> K"
      assume he_inc: "geotop_is_edge e \<and> p \<in> e"
      have hedge: "geotop_is_edge e"
        using he_inc by (by100 blast)
      have hp_e: "p \<in> e"
        using he_inc by (by100 blast)
      show "card {\<sigma> \<in> K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
        by (rule geotop_vertex_not_one_incident_union_incident_edge_count_two_dev34
            [OF hK hKM hnot_one heK hedge hp_e])
    qed
    show ?thesis
      using hp_vertex hall_edges by (by100 blast)
  next
    case False
    have hn1: "n = 1"
      using hnle1 False by (by100 arith)
    have h\<tau>1: "geotop_simplex_dim \<tau> 1"
      using h\<tau>dim hn1 by (by100 simp)
    have h\<tau>edge: "geotop_is_edge \<tau>"
      unfolding geotop_is_edge_def using h\<tau>1 by (by100 simp)
    have hp_in_\<tau>: "p \<in> \<tau>"
      using hp\<tau> rel_interior_subset by (by100 blast)
    have hcount2:
      "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face \<tau> \<sigma>} = 2"
      by (rule geotop_edge_carrier_not_one_incident_count_two_dev34
          [OF hK hKM h\<tau>K h\<tau>edge hp_in_\<tau> hnot_one])
    show ?thesis
      using h\<tau>K h\<tau>edge hp\<tau> hcount2 by (by100 blast)
  qed
qed

lemma geotop_two_incident_edge_rel_interior_subset_HOL_interior_polyhedron_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hcard2:
    "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
  shows "rel_interior e \<subseteq> interior (geotop_polyhedron K)"
  (**
    Euclidean local form of the two-sided edge branch: the two incident
    2-simplexes occupy the two local half-neighborhoods along an interior
    point of \<open>e\<close>, so such points are ordinary interior points of \<open>|K|\<close>. **)
proof -
  have hex:
    "\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
      \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
      \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
      \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
    by (rule geotop_complex_edge_face_count_eq_2_obtain[OF hcard2])
  obtain \<sigma> \<tau> where h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
    and h\<sigma>K: "\<sigma> \<in> K"
    and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and he\<sigma>: "geotop_is_face e \<sigma>"
    and h\<tau>K: "\<tau> \<in> K"
    and h\<tau>2: "geotop_simplex_dim \<tau> 2"
    and he\<tau>: "geotop_is_face e \<tau>"
    and hfaces: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
    using hex by (elim exE conjE)
  have hlocal: "rel_interior e \<subseteq> interior (\<sigma> \<union> \<tau>)"
    by (rule geotop_complex_two_2simplex_shared_edge_rel_interior_subset_HOL_interior_union_dev34
        [OF hK h\<sigma>K h\<tau>K h\<sigma>2 h\<tau>2 h\<sigma>\<tau> he\<sigma> he\<tau> hedge])
  have hunion_sub: "\<sigma> \<union> \<tau> \<subseteq> geotop_polyhedron K"
    using h\<sigma>K h\<tau>K unfolding geotop_polyhedron_def by (by100 blast)
  have hinterior_sub: "interior (\<sigma> \<union> \<tau>) \<subseteq> interior (geotop_polyhedron K)"
    by (rule interior_mono[OF hunion_sub])
  show ?thesis
    using hlocal hinterior_sub by (by100 blast)
qed

lemma geotop_two_incident_edge_rel_interior_subset_manifold_interior_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hcard2:
    "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
  shows "rel_interior e
      \<subseteq> geotop_manifold_interior (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  (**
    Moise Theorem 9 converse, edge-carrier case: an interior point of an edge
    incident with exactly two 2-simplexes has the ordinary plane local model,
    made from the two half-neighborhoods on the two sides of the edge. **)
proof
  fix p
  assume hp: "p \<in> rel_interior e"
  have hrel_HOL: "rel_interior e \<subseteq> interior (geotop_polyhedron K)"
    by (rule geotop_two_incident_edge_rel_interior_subset_HOL_interior_polyhedron_dev34
        [OF hK heK hedge hcard2])
  have hp_HOL: "p \<in> interior (geotop_polyhedron K)"
    using hp hrel_HOL by (by100 blast)
  show "p \<in> geotop_manifold_interior (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
    by (rule geotop_manifold_interior_if_HOL_interior_early_dev34[OF hp_HOL])
qed

lemma geotop_link_vertices_face_count_two_incident_link_edge_card_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes htwo:
    "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
      (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>})"
  shows "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
      card {l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l} = 2"
proof (intro allI impI)
  fix w
  let ?S = "{l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l}"
  assume hwL: "{w} \<in> geotop_link K v"
  have hex:
    "\<exists>e \<sigma> \<tau> l\<^sub>\<sigma> l\<^sub>\<tau>.
      e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
      \<and> \<sigma> \<noteq> \<tau>
      \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
      \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
      \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}
      \<and> l\<^sub>\<sigma> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<sigma> \<and> w \<in> l\<^sub>\<sigma>
      \<and> l\<^sub>\<tau> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<tau> \<and> w \<in> l\<^sub>\<tau>
      \<and> l\<^sub>\<sigma> \<noteq> l\<^sub>\<tau>
      \<and> (\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
            \<longrightarrow> l = l\<^sub>\<sigma> \<or> l = l\<^sub>\<tau>)"
    by (rule geotop_link_vertex_two_incident_link_edges_exhaust[OF hK hvK hwL htwo])
  obtain e \<sigma> \<tau> l\<^sub>\<sigma> l\<^sub>\<tau> where heK: "e \<in> K"
    and hedge: "geotop_is_edge e"
    and hv_e: "v \<in> e"
    and hw_e: "w \<in> e"
    and h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
    and h\<sigma>K: "\<sigma> \<in> K"
    and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and h\<sigma>face: "geotop_is_face e \<sigma>"
    and h\<tau>K: "\<tau> \<in> K"
    and h\<tau>2: "geotop_simplex_dim \<tau> 2"
    and h\<tau>face: "geotop_is_face e \<tau>"
    and hfaces: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
    and hl\<sigma>L: "l\<^sub>\<sigma> \<in> geotop_link K v"
    and hl\<sigma>edge: "geotop_is_edge l\<^sub>\<sigma>"
    and hw_l\<sigma>: "w \<in> l\<^sub>\<sigma>"
    and hl\<tau>L: "l\<^sub>\<tau> \<in> geotop_link K v"
    and hl\<tau>edge: "geotop_is_edge l\<^sub>\<tau>"
    and hw_l\<tau>: "w \<in> l\<^sub>\<tau>"
    and hl_distinct: "l\<^sub>\<sigma> \<noteq> l\<^sub>\<tau>"
    and hexhaust: "\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
            \<longrightarrow> l = l\<^sub>\<sigma> \<or> l = l\<^sub>\<tau>"
    using hex by (elim exE conjE)
  have hS_eq: "?S = {l\<^sub>\<sigma>, l\<^sub>\<tau>}"
  proof
    show "?S \<subseteq> {l\<^sub>\<sigma>, l\<^sub>\<tau>}"
      using hexhaust by (by100 blast)
  next
    show "{l\<^sub>\<sigma>, l\<^sub>\<tau>} \<subseteq> ?S"
      using hl\<sigma>L hl\<sigma>edge hw_l\<sigma> hl\<tau>L hl\<tau>edge hw_l\<tau> by (by100 blast)
  qed
  show "card ?S = 2"
    using hS_eq hl_distinct by (by100 simp)
qed

lemma geotop_link_component_preserves_incident_edge_card_two_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  assumes hdegree_link: "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
      card {l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l} = 2"
  shows "\<forall>w. {w} \<in> {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C} \<longrightarrow>
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
  have hdegree: "card ?S = 2"
    using hdegree_link hw_link by (by100 blast)
  show "card ?S\<^sub>C = 2"
    using hsets hdegree by (by100 simp)
qed

lemma geotop_link_component_degree_two_polygon_witness_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  assumes hdegree_link: "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
      card {l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l} = 2"
  shows "geotop_is_polygon C"
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
      card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 2"
    using geotop_link_component_preserves_incident_edge_card_two_dev34
      [OF hK hP hC hdegree_link] hL_eq by (by100 simp)
  have hP_C: "P \<in> C"
    using geotop_link_component_summary[OF hK hv hP hC] by (by100 blast)
  have hL_nonempty: "L \<noteq> {}"
    using hP_C hL_poly unfolding geotop_polyhedron_def by (by100 blast)
  have hpoly_polygon: "geotop_is_polygon (geotop_polyhedron L)"
    by (rule geotop_finite_connected_degree_two_linear_graph_polygon_dev34
        [OF hL_linear hL_fin hL_nonempty hL_conn hdegree_L])
  show ?thesis
    using hpoly_polygon hL_poly by (by100 simp)
qed

lemma geotop_two_sided_vertex_link_polygon_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hall_edges:
    "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
      card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
  shows "geotop_is_polygon (\<Union>(geotop_link K v))"
  (**
    Moise Theorem 9 vertex-link branch: if every edge incident with \<open>v\<close> is
    two-sided, then every link vertex has degree two.  Lemma 5 gives
    connectedness of \<open>|L(v)|\<close>, hence the link is a single polygon. **)
proof -
  have hvK: "{v} \<in> K"
    using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
  have hvM: "v \<in> geotop_polyhedron K"
    using hvK unfolding geotop_polyhedron_def by (by100 blast)
  have hincident: "\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e"
  proof (rule ccontr)
    assume hno: "\<not> (\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e)"
    have hsingle_open: "{v} \<in>
        subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
      by (rule geotop_complex_no_incident_edge_vertex_open_singleton[OF hK hv hno])
    have hnot_open: "{v} \<notin>
        subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
      by (rule geotop_2_manifold_with_boundary_no_open_singleton[OF hKM hvM])
    show False
      using hsingle_open hnot_open by (by100 blast)
  qed
  have hlink_nonempty: "\<Union>(geotop_link K v) \<noteq> {}"
  proof -
    obtain e where heK: "e \<in> K" and hedge: "geotop_is_edge e" and hv_e: "v \<in> e"
      using hincident by (by100 blast)
    show ?thesis
      by (rule geotop_incident_edge_link_polyhedron_nonempty
          [OF hK hvK heK hedge hv_e])
  qed
  have htwo_faces:
    "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
      (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>})"
  proof (intro ballI impI)
    fix e
    assume heK: "e \<in> K"
    assume he_inc: "geotop_is_edge e \<and> v \<in> e"
    have hcount2:
      "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
      using hall_edges heK he_inc by (by100 blast)
    show "\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
      by (rule geotop_complex_edge_face_count_eq_2_obtain[OF hcount2])
  qed
  have hdegree_link: "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
      card {l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l} = 2"
    by (rule geotop_link_vertices_face_count_two_incident_link_edge_card_dev34
        [OF hK hvK htwo_faces])
  have hconn: "top1_connected_on (\<Union>(geotop_link K v))
      (subspace_topology UNIV geotop_euclidean_topology
        (\<Union>(geotop_link K v)))"
    by (rule geotop_2_manifold_with_boundary_link_polyhedron_connected_from_vertex_star_dev34
        [OF hK hKM hv])
  obtain P where hP: "P \<in> \<Union>(geotop_link K v)"
    using hlink_nonempty by (by100 blast)
  let ?C = "geotop_component_at UNIV geotop_euclidean_topology
      (\<Union>(geotop_link K v)) P"
  have hC_def: "?C = geotop_component_at UNIV geotop_euclidean_topology
      (\<Union>(geotop_link K v)) P"
    by (by100 simp)
  have hC_polygon: "geotop_is_polygon ?C"
    by (rule geotop_link_component_degree_two_polygon_witness_dev34
        [OF hK hv hP hC_def hdegree_link])
  have hC_eq: "?C = \<Union>(geotop_link K v)"
    by (rule geotop_connected_component_at_eq_self[OF hP hconn])
  show ?thesis
    using hC_polygon hC_eq by (by100 simp)
qed

lemma geotop_linear_on_continuous_on_dev34:
  fixes \<sigma> :: "(real^2) set"
  fixes f :: "real^2 \<Rightarrow> real^2"
  assumes hlin: "geotop_linear_on \<sigma> f"
  shows "continuous_on \<sigma> f"
  (**
    Standard PL fact used in the Figure 4.10 local model: a map that is
    barycentrically linear on one simplex is continuous on that simplex. **)
proof -
  obtain V where hV: "geotop_simplex_vertices \<sigma> V"
      and hlin_V:
        "\<forall>\<alpha>. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1 \<longrightarrow>
          f (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
    using hlin unfolding geotop_linear_on_def by (by100 blast)
  have hV_fin: "finite V"
    using hV unfolding geotop_simplex_vertices_def by (by100 blast)
  have hV_ne: "V \<noteq> {}"
    using hV unfolding geotop_simplex_vertices_def by (by100 fastforce)
  have hV_ai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF hV])
  obtain a where haV: "a \<in> V"
    using hV_ne by (by100 blast)
  define B where "B = ((\<lambda>v. v - a) ` (V - {a}))"
  have hB_indep: "independent B"
    using affine_dependent_iff_dependent2[OF haV] hV_ai
    unfolding B_def by (by100 simp)
  define fb where "fb b = f (SOME v. v \<in> V - {a} \<and> b = v - a) - f a" for b
  obtain A :: "real^2 \<Rightarrow> real^2" where hA_lin: "linear A"
      and hA_B: "\<forall>b\<in>B. A b = fb b"
    using linear_independent_extend[OF hB_indep, of fb] by (by100 blast)
  interpret A: linear A
    by (rule hA_lin)
  define g where "g x = f a + A (x - a)" for x
  have hA_vertex: "\<forall>v\<in>V. A (v - a) = f v - f a"
  proof
    fix v assume hvV: "v \<in> V"
    show "A (v - a) = f v - f a"
    proof (cases "v = a")
      case True
      then show ?thesis using A.zero by (by100 simp)
    next
      case False
      have hvB: "v - a \<in> B"
        unfolding B_def using hvV False by (by100 blast)
      have hsome: "(SOME w. w \<in> V - {a} \<and> v - a = w - a) = v"
      proof (rule some_equality)
        show "v \<in> V - {a} \<and> v - a = v - a"
          using hvV False by (by100 simp)
      next
        fix w assume "w \<in> V - {a} \<and> v - a = w - a"
        then show "w = v" by (by100 simp)
      qed
      have "A (v - a) = fb (v - a)"
        using hA_B hvB by (by100 blast)
      also have "\<dots> = f v - f a"
        unfolding fb_def using hsome by (by100 simp)
      finally show ?thesis .
    qed
  qed
  have hg_cont: "continuous_on \<sigma> g"
  proof -
    have hA_bounded: "bounded_linear A"
      using hA_lin linear_conv_bounded_linear by (by100 blast)
    have hA_cont: "continuous_on UNIV A"
      by (rule linear_continuous_on[OF hA_bounded])
    have hminus_cont: "continuous_on \<sigma> (\<lambda>x. x - a)"
      by (intro continuous_intros)
    have hA_minus_cont: "continuous_on \<sigma> (\<lambda>x. A (x - a))"
    proof -
      have hA_on_image: "continuous_on ((\<lambda>x. x - a) ` \<sigma>) A"
        by (rule continuous_on_subset[OF hA_cont]) (by100 blast)
      have "continuous_on \<sigma> (A \<circ> (\<lambda>x. x - a))"
        by (rule continuous_on_compose[OF hminus_cont hA_on_image])
      thus ?thesis
        unfolding comp_def by (by100 simp)
    qed
    show ?thesis
      unfolding g_def
      using hA_minus_cont by (intro continuous_intros)
  qed
  show ?thesis
  proof (rule continuous_on_eq[OF hg_cont])
    fix x assume hx\<sigma>: "x \<in> \<sigma>"
    have h\<sigma>_HOL: "\<sigma> = convex hull V"
    proof -
      have "\<sigma> = geotop_convex_hull V"
        using hV unfolding geotop_simplex_vertices_def by (by100 blast)
      thus ?thesis using geotop_convex_hull_eq_HOL by (by100 simp)
    qed
    have hx_hull: "x \<in> convex hull V"
      using hx\<sigma> h\<sigma>_HOL by (by100 simp)
    have h_hull_char:
      "convex hull V =
        {y. \<exists>\<alpha>::real^2 \<Rightarrow> real. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1 \<and>
              (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = y}"
      by (rule convex_hull_finite[OF hV_fin])
    obtain \<alpha> :: "real^2 \<Rightarrow> real"
      where h\<alpha>_nn: "\<forall>v\<in>V. 0 \<le> \<alpha> v"
        and h\<alpha>_sum: "sum \<alpha> V = 1"
        and h\<alpha>_x: "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = x"
      using hx_hull h_hull_char by (by100 blast)
    have hf_x: "f x = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
      using hlin_V h\<alpha>_nn h\<alpha>_sum h\<alpha>_x by (by100 blast)
    have hshift: "x - a = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R (v - a))"
    proof -
      have "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R (v - a)) =
          (\<Sum>v\<in>V. (\<alpha> v *\<^sub>R v) - (\<alpha> v *\<^sub>R a))"
      proof (rule sum.cong)
        show "V = V" by (by100 simp)
        fix v assume "v \<in> V"
        show "\<alpha> v *\<^sub>R (v - a) = \<alpha> v *\<^sub>R v - \<alpha> v *\<^sub>R a"
          by (rule scaleR_right_diff_distrib)
      qed
      also have "\<dots> = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) - (\<Sum>v\<in>V. \<alpha> v *\<^sub>R a)"
        by (rule sum_subtractf)
      also have "\<dots> = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) - (sum \<alpha> V) *\<^sub>R a"
      proof -
        have "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R a) = (sum \<alpha> V) *\<^sub>R a"
          by (simp only: scaleR_sum_left)
        thus ?thesis by (by100 simp)
      qed
      also have "\<dots> = x - (sum \<alpha> V) *\<^sub>R a"
        using h\<alpha>_x by (by100 simp)
      also have "\<dots> = x - a"
        using h\<alpha>_sum by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
    have hA_sum: "A (x - a) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R (f v - f a))"
    proof -
      have "A (x - a) = A (\<Sum>v\<in>V. \<alpha> v *\<^sub>R (v - a))"
        using hshift by (by100 simp)
      also have "\<dots> = (\<Sum>v\<in>V. A (\<alpha> v *\<^sub>R (v - a)))"
        by (rule A.sum)
      also have "\<dots> = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R A (v - a))"
      proof (rule sum.cong)
        show "V = V" by (by100 simp)
        fix v assume "v \<in> V"
        show "A (\<alpha> v *\<^sub>R (v - a)) = \<alpha> v *\<^sub>R A (v - a)"
          by (rule A.scale)
      qed
      also have "\<dots> = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R (f v - f a))"
        using hA_vertex by (by100 simp)
      finally show ?thesis .
    qed
    have hsum_aff:
      "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R (f v - f a)) =
        (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v) - f a"
    proof -
      have "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R (f v - f a)) =
          (\<Sum>v\<in>V. (\<alpha> v *\<^sub>R f v) - (\<alpha> v *\<^sub>R f a))"
      proof (rule sum.cong)
        show "V = V" by (by100 simp)
        fix v assume "v \<in> V"
        show "\<alpha> v *\<^sub>R (f v - f a) = \<alpha> v *\<^sub>R f v - \<alpha> v *\<^sub>R f a"
          by (rule scaleR_right_diff_distrib)
      qed
      also have "\<dots> = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v) - (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f a)"
        by (rule sum_subtractf)
      also have "\<dots> = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v) - (sum \<alpha> V) *\<^sub>R f a"
      proof -
        have "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R f a) = (sum \<alpha> V) *\<^sub>R f a"
          by (simp only: scaleR_sum_left)
        thus ?thesis by (by100 simp)
      qed
      also have "\<dots> = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v) - f a"
        using h\<alpha>_sum by (by100 simp)
      finally show ?thesis .
    qed
    have hg_x: "g x = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
      unfolding g_def using hA_sum hsum_aff by (by100 simp)
    show "g x = f x"
      using hf_x hg_x by (by100 simp)
  qed
qed

lemma geotop_standard_fan_target_vertex_HOL_interior_polyhedron_dev34:
  fixes K L' :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hc_int: "c \<in> interior \<sigma>"
  assumes hsubdiv:
    "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
  assumes h\<psi>: "bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B"
  assumes hcB: "c \<notin> B"
  assumes hvertices: "geotop_complex_vertices L' = insert c B"
  assumes hc_simplex: "geotop_convex_hull {c} \<in> L'"
  assumes hlink_target:
    "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
      (geotop_convex_hull W \<in> geotop_link K v
        \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
  assumes hcone_target:
    "\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
      W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
      (geotop_convex_hull W \<in> geotop_link K v
        \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L')"
  assumes hpolygon: "geotop_is_polygon (\<Union>(geotop_link K v))"
  shows "v \<in> interior (geotop_polyhedron K)"
  (**
    Moise Figure 4.10 local Euclidean step with the cone data explicit.  The
    target fan has one new vertex \<open>c\<close>, old boundary simplexes exactly matching
    the link through \<open>\<psi>\<close>, and cone simplexes exactly over nonempty link
    simplexes.  The extended vertex map sends \<open>v\<close> to \<open>c\<close>; transport the
    ordinary interior of the fan's cone vertex back to obtain a Euclidean disk
    about \<open>v\<close> inside \<open>|K|\<close>. **)
proof -
  have hc_target: "c \<in> interior (geotop_polyhedron L')"
    by (rule geotop_2simplex_face_complex_subdivision_HOL_interior_point_dev34
        [OF h\<sigma> hc_int hsubdiv])
  define \<phi> where "\<phi> x = (if x = v then c else \<psi> x)" for x
  have hlink_finite: "finite (geotop_link K v)"
    by (rule geotop_link_finite_at_complex_vertex[OF hK hv])
  have hstar_vertices_finite:
      "finite (geotop_complex_vertices (geotop_star K v))"
    using geotop_fig410_link_and_star_vertices_finite_dev34
      [OF hK hv hlink_finite]
    by (by100 blast)
  have hstar_finite: "finite (geotop_star K v)"
    by (rule geotop_star_finite_at_complex_vertex[OF hK hv])
  have hiso_star_target: "geotop_isomorphism (geotop_star K v) L' \<phi>"
  proof -
    have hiso_raw:
        "geotop_isomorphism (geotop_star K v) L'
          (\<lambda>x. if x = v then c else \<psi> x)"
      by (rule_tac geotop_star_fan_isomorphism_from_link_and_cone_target_cases_dev34
          [OF hK hv h\<psi> hcB hvertices hstar_vertices_finite hlink_target
            hc_simplex hcone_target])
    have h\<phi>_eq: "\<phi> = (\<lambda>x. if x = v then c else \<psi> x)"
      using \<phi>_def by (by100 blast)
    show ?thesis
      using hiso_raw h\<phi>_eq by (by100 simp)
  qed
  have hstar_complex: "geotop_is_complex (geotop_star K v)"
    by (rule geotop_star_is_complex[OF hK])
  have hL'_complex: "geotop_is_complex L'"
    by (rule geotop_subdivision_source_is_complex_dev34[OF hsubdiv])
  have hL'_finite: "finite L'"
  proof -
    have hface_fin:
        "finite {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
      by (rule geotop_simplex_dim_face_complex_finite_R2[OF h\<sigma>])
    show ?thesis
      by (rule geotop_subdivision_of_finite_is_finite[OF hface_fin hsubdiv])
  qed
  obtain f where hPLH_star: "geotop_PLH (geotop_star K v) L' f"
    and hf_image: "f ` geotop_polyhedron (geotop_star K v) = geotop_polyhedron L'"
    and hf_vertices:
      "\<forall>w\<in>geotop_complex_vertices (geotop_star K v). f w = \<phi> w"
    and hf_linear: "\<forall>\<rho>\<in>geotop_star K v. geotop_linear_on \<rho> f"
    and hfinv_linear:
      "\<forall>\<tau>\<in>L'. geotop_linear_on \<tau>
        (inv_into (geotop_polyhedron (geotop_star K v)) f)"
    using geotop_isomorphism_induces_PLH
      [OF hstar_complex hL'_complex hiso_star_target]
    by (by100 blast)
  have hv_star_vertex: "v \<in> geotop_complex_vertices (geotop_star K v)"
  proof -
    have hvertices_star:
        "geotop_complex_vertices (geotop_star K v) =
          insert v (geotop_complex_vertices (geotop_link K v))"
      by (rule geotop_star_vertices_eq_insert_link_vertices_dev34[OF hK hv])
    show ?thesis
      using hvertices_star by (by100 simp)
  qed
  have hf_v: "f v = c"
    using hf_vertices hv_star_vertex \<phi>_def by (by100 simp)
  have hbij_star:
      "bij_betw f (geotop_polyhedron (geotop_star K v)) (geotop_polyhedron L')"
    using hPLH_star unfolding geotop_PLH_def by (by100 blast)
  have hc_target_poly: "c \<in> geotop_polyhedron L'"
    using hc_target interior_subset by (by100 blast)
  obtain r where hr_pos: "0 < r"
    and hball_c_target: "ball c r \<subseteq> geotop_polyhedron L'"
  proof -
    have hopen_int: "open (interior (geotop_polyhedron L'))"
      by (rule open_interior)
    have hall_ball:
        "\<forall>x\<in>interior (geotop_polyhedron L').
          \<exists>e>0. ball x e \<subseteq> interior (geotop_polyhedron L')"
      using hopen_int unfolding open_contains_ball by (by100 simp)
    have hex_ball:
        "\<exists>r>0. ball c r \<subseteq> interior (geotop_polyhedron L')"
      using hall_ball hc_target by (by100 blast)
    obtain r where hr: "0 < r"
      and hball_int: "ball c r \<subseteq> interior (geotop_polyhedron L')"
      using hex_ball by (by100 blast)
    have hball_target: "ball c r \<subseteq> geotop_polyhedron L'"
      using hball_int interior_subset by (by100 blast)
    show ?thesis
      by (rule that[OF hr hball_target])
  qed
  have hv_star_poly: "v \<in> geotop_polyhedron (geotop_star K v)"
    using hv_star_vertex geotop_complex_vertices_subset_polyhedron_dev34
    by (by100 blast)
  have hinv_c:
      "inv_into (geotop_polyhedron (geotop_star K v)) f c = v"
  proof -
    have "inv_into (geotop_polyhedron (geotop_star K v)) f (f v) = v"
      by (rule bij_betw_inv_into_left[OF hbij_star hv_star_poly])
    then show ?thesis
      using hf_v by (by100 simp)
  qed
  define U where
    "U = (inv_into (geotop_polyhedron (geotop_star K v)) f) ` ball c r"
  have hU_subset_star: "U \<subseteq> geotop_polyhedron (geotop_star K v)"
  proof
    fix x assume hxU: "x \<in> U"
    obtain y where hy_ball: "y \<in> ball c r"
      and hx_eq: "x = inv_into (geotop_polyhedron (geotop_star K v)) f y"
      using hxU unfolding U_def by (by100 blast)
    have hy_target: "y \<in> geotop_polyhedron L'"
      using hball_c_target hy_ball by (by100 blast)
    have himage_eq:
        "f ` geotop_polyhedron (geotop_star K v) = geotop_polyhedron L'"
      using hbij_star unfolding bij_betw_def by (by100 blast)
    have hy_image: "y \<in> f ` geotop_polyhedron (geotop_star K v)"
      using hy_target himage_eq by (by100 simp)
    have hinv_y:
        "inv_into (geotop_polyhedron (geotop_star K v)) f y
          \<in> geotop_polyhedron (geotop_star K v)"
      by (rule inv_into_into[OF hy_image])
    show "x \<in> geotop_polyhedron (geotop_star K v)"
      using hx_eq hinv_y by (by100 simp)
  qed
  have hv_U: "v \<in> U"
  proof -
    have hc_ball: "c \<in> ball c r"
      using hr_pos by (by100 simp)
    have hinv_image:
        "inv_into (geotop_polyhedron (geotop_star K v)) f c \<in> U"
      unfolding U_def by (rule imageI[OF hc_ball])
    show ?thesis
      using hinv_image hinv_c by (by100 simp)
  qed
  have hstar_poly_subset_K:
      "geotop_polyhedron (geotop_star K v) \<subseteq> geotop_polyhedron K"
    using geotop_star_polyhedron_subset_polyhedron[OF hK, of v]
    unfolding geotop_polyhedron_def by (by100 blast)
  have hU_subset_K: "U \<subseteq> geotop_polyhedron K"
    using hU_subset_star hstar_poly_subset_K by (by100 blast)
  have hf_U: "f ` U = ball c r"
  proof
    show "f ` U \<subseteq> ball c r"
    proof
      fix z assume hz: "z \<in> f ` U"
      obtain x where hxU: "x \<in> U" and hz_eq: "z = f x"
        using hz by (by100 blast)
      obtain y where hy_ball: "y \<in> ball c r"
        and hx_eq: "x = inv_into (geotop_polyhedron (geotop_star K v)) f y"
        using hxU unfolding U_def by (by100 blast)
      have hy_target: "y \<in> geotop_polyhedron L'"
        using hball_c_target hy_ball by (by100 blast)
      have hcancel:
          "f (inv_into (geotop_polyhedron (geotop_star K v)) f y) = y"
        by (rule bij_betw_inv_into_right[OF hbij_star hy_target])
      show "z \<in> ball c r"
        using hz_eq hx_eq hcancel hy_ball by (by100 simp)
    qed
    show "ball c r \<subseteq> f ` U"
    proof
      fix y assume hy_ball: "y \<in> ball c r"
      have hy_target: "y \<in> geotop_polyhedron L'"
        using hball_c_target hy_ball by (by100 blast)
      have hinv_U:
          "inv_into (geotop_polyhedron (geotop_star K v)) f y \<in> U"
        unfolding U_def by (rule imageI[OF hy_ball])
      have hcancel:
          "f (inv_into (geotop_polyhedron (geotop_star K v)) f y) = y"
        by (rule bij_betw_inv_into_right[OF hbij_star hy_target])
      have hy_eq:
          "y = f (inv_into (geotop_polyhedron (geotop_star K v)) f y)"
        using hcancel by (by100 simp)
      show "y \<in> f ` U"
        using hy_eq hinv_U by (by100 blast)
    qed
  qed
  have hbij_U_ball: "bij_betw f U (ball c r)"
  proof -
    have hinj_star: "inj_on f (geotop_polyhedron (geotop_star K v))"
      using hbij_star by (rule bij_betw_imp_inj_on)
    have hinj_U: "inj_on f U"
      using hinj_star hU_subset_star inj_on_subset by (by100 blast)
    show ?thesis
      using hinj_U hf_U unfolding bij_betw_def by (by100 blast)
  qed
  have hv_poly: "v \<in> geotop_polyhedron K"
    using hv_star_poly hstar_poly_subset_K by (by100 blast)
  have hfinv_cont_each:
      "\<forall>\<tau>\<in>L'. continuous_on \<tau>
        (inv_into (geotop_polyhedron (geotop_star K v)) f)"
  proof
    fix \<tau> assume h\<tau>: "\<tau> \<in> L'"
    have hlin\<tau>:
        "geotop_linear_on \<tau>
          (inv_into (geotop_polyhedron (geotop_star K v)) f)"
      using hfinv_linear h\<tau> by (by100 blast)
    show "continuous_on \<tau>
        (inv_into (geotop_polyhedron (geotop_star K v)) f)"
      by (rule geotop_linear_on_continuous_on_dev34[OF hlin\<tau>])
  qed
  have hfinv_cont_poly:
      "continuous_on (geotop_polyhedron L')
        (inv_into (geotop_polyhedron (geotop_star K v)) f)"
  proof -
    have hL'_simp: "\<forall>\<tau>\<in>L'. geotop_is_simplex \<tau>"
      by (rule conjunct1[OF hL'_complex[unfolded geotop_is_complex_def]])
    have hcont_union:
        "continuous_on (\<Union>\<tau>\<in>L'. \<tau>)
          (inv_into (geotop_polyhedron (geotop_star K v)) f)"
    proof (rule continuous_on_closed_Union[OF hL'_finite])
      fix \<tau> assume h\<tau>: "\<tau> \<in> L'"
      have h\<tau>_simp: "geotop_is_simplex \<tau>"
        using hL'_simp h\<tau> by (by100 blast)
      show "closed \<tau>"
        by (rule geotop_is_simplex_closed[OF h\<tau>_simp])
    next
      fix \<tau> assume h\<tau>: "\<tau> \<in> L'"
      show "continuous_on \<tau>
          (inv_into (geotop_polyhedron (geotop_star K v)) f)"
        using hfinv_cont_each h\<tau> by (by100 blast)
    qed
    show ?thesis
      using hcont_union unfolding geotop_polyhedron_def by (by100 simp)
  qed
  have hfinv_cont_ball:
      "continuous_on (ball c r)
        (inv_into (geotop_polyhedron (geotop_star K v)) f)"
    by (rule continuous_on_subset[OF hfinv_cont_poly hball_c_target])
  have hfinv_inj_ball:
      "inj_on (inv_into (geotop_polyhedron (geotop_star K v)) f) (ball c r)"
  proof -
    have hbij_inv:
        "bij_betw (inv_into (geotop_polyhedron (geotop_star K v)) f)
          (geotop_polyhedron L') (geotop_polyhedron (geotop_star K v))"
      by (rule bij_betw_inv_into[OF hbij_star])
    have hinj_target:
        "inj_on (inv_into (geotop_polyhedron (geotop_star K v)) f)
          (geotop_polyhedron L')"
      using hbij_inv by (rule bij_betw_imp_inj_on)
    show ?thesis
      using hinj_target hball_c_target inj_on_subset by (by100 blast)
  qed
  have hU_open: "open U"
  proof -
    have himg_U:
        "(inv_into (geotop_polyhedron (geotop_star K v)) f) ` ball c r = U"
      unfolding U_def by (by100 simp)
    have hdim: "DIM(real^2) \<le> DIM(real^2)"
      by (by100 simp)
    have hopen_img:
        "open ((inv_into (geotop_polyhedron (geotop_star K v)) f) ` ball c r)"
      by (rule invariance_of_domain_gen
          [OF open_ball hfinv_cont_ball hfinv_inj_ball hdim])
    show ?thesis
      using hopen_img himg_U by (by100 simp)
  qed
  show ?thesis
    by (rule interiorI[OF hU_open hv_U hU_subset_K])
qed

lemma geotop_polygon_link_vertex_is_HOL_interior_polyhedron_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hpolygon: "geotop_is_polygon (\<Union>(geotop_link K v))"
  shows "v \<in> interior (geotop_polyhedron K)"
  (**
    Moise Figure 4.10 local model: if the link of \<open>v\<close> is a polygon, then
    the open star is a full disk fan and contains a Euclidean disk around
    \<open>v\<close> in \<open>|K|\<close>. **)
proof -
  have hshape:
      "geotop_is_broken_line (\<Union>(geotop_link K v))
        \<or> geotop_is_polygon (\<Union>(geotop_link K v))"
    using hpolygon by (by100 blast)
  have hlink_data:
      "geotop_is_complex (geotop_link K v)
      \<and> geotop_complex_is_1dim (geotop_link K v)
      \<and> finite (geotop_link K v)
      \<and> (geotop_is_broken_line (geotop_polyhedron (geotop_link K v))
          \<or> geotop_is_polygon (geotop_polyhedron (geotop_link K v)))"
    by (rule geotop_link_finite_1dim_line_or_polygon_dev34[OF hK hv hshape])
  have hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  proof -
    have hlink_complex: "geotop_is_complex (geotop_link K v)"
      using hlink_data by (by100 blast)
    have hlink_1dim: "geotop_complex_is_1dim (geotop_link K v)"
      using hlink_data by (by100 blast)
    show ?thesis
      by (rule geotop_complex_1dim_imp_linear_graph_dev34
          [OF hlink_complex hlink_1dim])
  qed
  have hlink_finite: "finite (geotop_link K v)"
    using hlink_data by (by100 blast)
  have hpolygon_poly:
      "geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
    using hpolygon unfolding geotop_polyhedron_def by (by100 simp)
  obtain \<sigma> :: "(real^2) set" and L' B c \<psi>
    where hfan:
      "geotop_simplex_dim \<sigma> 2
      \<and> c \<in> interior \<sigma>
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B
      \<and> c \<notin> B
      \<and> geotop_complex_vertices L' = insert c B
      \<and> geotop_convex_hull {c} \<in> L'
      \<and> (\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L'))
      \<and> (\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L'))"
    using geotop_standard_fan_target_from_finite_linear_link_polygon_with_interior_dev34
      [OF hK hv hlink_linear hlink_finite hpolygon_poly]
    by (elim exE) assumption
  have h\<sigma>: "geotop_simplex_dim \<sigma> 2"
    using hfan by (by100 blast)
  have hc_int: "c \<in> interior \<sigma>"
    using hfan by (by100 blast)
  have hsubdiv:
      "geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
    using hfan by (by100 blast)
  have h\<psi>: "bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B"
    using hfan by (by100 blast)
  have hcB: "c \<notin> B"
    using hfan by (by100 blast)
  have hvertices: "geotop_complex_vertices L' = insert c B"
    using hfan by (by100 blast)
  have hc_simplex: "geotop_convex_hull {c} \<in> L'"
    using hfan by (by100 blast)
  have hlink_target:
    "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
      (geotop_convex_hull W \<in> geotop_link K v
        \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
    using hfan by (by100 blast)
  have hcone_target:
    "\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
      W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
      (geotop_convex_hull W \<in> geotop_link K v
        \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L')"
    using hfan by (by100 blast)
  show ?thesis
    by (rule geotop_standard_fan_target_vertex_HOL_interior_polyhedron_dev34
        [OF hK hv h\<sigma> hc_int hsubdiv h\<psi> hcB hvertices hc_simplex hlink_target
          hcone_target hpolygon])
qed

lemma geotop_two_sided_vertex_is_HOL_interior_polyhedron_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hall_edges:
    "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
      card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
  shows "v \<in> interior (geotop_polyhedron K)"
  (**
    Euclidean local form of the full-disk vertex branch: when every edge at
    \<open>v\<close> is two-sided, the connected link is a polygon and the open star
    contains a small Euclidean disk around \<open>v\<close>. **)
proof -
  have hpolygon: "geotop_is_polygon (\<Union>(geotop_link K v))"
    by (rule geotop_two_sided_vertex_link_polygon_dev34
        [OF hK hKM hv hall_edges])
  show ?thesis
    by (rule geotop_polygon_link_vertex_is_HOL_interior_polyhedron_dev34
        [OF hK hv hpolygon])
qed

lemma geotop_two_sided_vertex_is_manifold_interior_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hall_edges:
    "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
      card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
  shows "v \<in> geotop_manifold_interior (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  (**
    Moise Theorem 9 converse, vertex-carrier case: if every edge at the
    boundary-candidate vertex is two-sided, the connected link is a polygon,
    so the vertex star is a full disk fan and gives a plane neighborhood. **)
proof -
  have hv_HOL: "v \<in> interior (geotop_polyhedron K)"
    by (rule geotop_two_sided_vertex_is_HOL_interior_polyhedron_dev34
        [OF hK hKM hv hall_edges])
  show ?thesis
    by (rule geotop_manifold_interior_if_HOL_interior_early_dev34[OF hv_HOL])
qed

lemma geotop_boundary_not_one_incident_point_is_manifold_interior_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes hbd: "p \<in> geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  assumes hnot_one:
    "p \<notin> \<Union>{e\<in>K. geotop_is_edge e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
  shows "p \<in> geotop_manifold_interior (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  (**
    Wrapper for the converse inclusion in Theorem 9: the carrier split leaves
    only the two-sided edge model or the full-disk vertex-star model, both of
    which are manifold-interior local pictures. **)
proof -
  have hcases:
    "(\<exists>e. e \<in> K \<and> geotop_is_edge e \<and> p \<in> rel_interior e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2)
      \<or> (p \<in> geotop_complex_vertices K
        \<and> (\<forall>e\<in>K. geotop_is_edge e \<and> p \<in> e \<longrightarrow>
          card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2))"
    by (rule geotop_boundary_not_one_incident_carrier_cases_dev34
        [OF hK hKM hbd hnot_one])
  show ?thesis
  proof (rule disjE[OF hcases])
    assume h_edge:
      "\<exists>e. e \<in> K \<and> geotop_is_edge e \<and> p \<in> rel_interior e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
    obtain e where heK: "e \<in> K"
      and hedge: "geotop_is_edge e"
      and hp_rel: "p \<in> rel_interior e"
      and hcard2:
        "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
      using h_edge by (by100 blast)
    have hrel_int: "rel_interior e
        \<subseteq> geotop_manifold_interior (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
      by (rule geotop_two_incident_edge_rel_interior_subset_manifold_interior_dev34
          [OF hK hKM heK hedge hcard2])
    show ?thesis
      using hp_rel hrel_int by (by100 blast)
  next
    assume h_vertex:
      "p \<in> geotop_complex_vertices K
        \<and> (\<forall>e\<in>K. geotop_is_edge e \<and> p \<in> e \<longrightarrow>
          card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2)"
    have hp_vertex: "p \<in> geotop_complex_vertices K"
      using h_vertex by (by100 blast)
    have hall_edges: "\<forall>e\<in>K. geotop_is_edge e \<and> p \<in> e \<longrightarrow>
          card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
      using h_vertex by (by100 blast)
    show ?thesis
      by (rule geotop_two_sided_vertex_is_manifold_interior_dev34
          [OF hK hKM hp_vertex hall_edges])
  qed
qed

lemma geotop_one_incident_edge_rel_interior_subset_manifold_boundary_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hcard1:
    "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
  shows "rel_interior e
      \<subseteq> geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  (**
    Moise Theorem 9 boundary-edge direction, edge-interior case.  At an
    interior point of a one-incident edge, the small semicircle in the unique
    incident 2-simplex separates the local half-neighborhood; a plane chart
    would make its image an arc separating an open subset of the plane. **)
proof
  fix p assume hp: "p \<in> rel_interior e"
  let ?M = "geotop_polyhedron K"
  let ?d = "\<lambda>x y. norm (x - y)"
  let ?TM = "top1_metric_topology_on ?M ?d"
  have hpM: "p \<in> ?M"
    using heK hp rel_interior_subset unfolding geotop_polyhedron_def by (by100 blast)
  have hunique:
    "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
    by (rule geotop_complex_edge_face_count_eq_1_unique[OF hK heK hedge hcard1])
  have hnot_int: "p \<notin> geotop_manifold_interior ?M ?d"
  proof
    assume hpint: "p \<in> geotop_manifold_interior ?M ?d"
    obtain U f where hUopen: "openin_on ?M ?TM U"
      and hpU: "p \<in> U"
      and hhomeo_geo: "top1_homeomorphism_on U
          (subspace_topology UNIV geotop_euclidean_topology U)
          (UNIV::(real^2) set) geotop_euclidean_topology f"
      using geotop_manifold_interior_geo_chart_at_dev34[OF hpint]
      by (by100 blast)
    obtain A where hAsubU: "A \<subseteq> U"
      and hAimg: "geotop_is_arc (f ` A)
          (subspace_topology UNIV geotop_euclidean_topology (f ` A))"
      and hAsep: "\<not> top1_connected_on (U - A)
          (subspace_topology UNIV geotop_euclidean_topology (U - A))"
      using geotop_unique_incident_2simplex_semicircle_separates_chart_dev34
          [OF hK heK hedge hp hunique hUopen hpU hhomeo_geo]
      by (by100 blast)
    have hconn: "top1_connected_on (U - A)
        (subspace_topology UNIV geotop_euclidean_topology (U - A))"
      by (rule geotop_plane_chart_arc_complement_connected[OF hhomeo_geo hAsubU hAimg])
    show False
      using hconn hAsep by (by100 blast)
  qed
  show "p \<in> geotop_manifold_boundary ?M ?d"
    unfolding geotop_manifold_boundary_def using hpM hnot_int by (by100 blast)
qed

lemma geotop_one_incident_edge_non_rel_interior_subset_manifold_boundary_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hcard1:
    "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
  shows "e - rel_interior e
      \<subseteq> geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  (**
    Remaining endpoint/vertex case of Moise Theorem 9's boundary-edge
    direction.  At an endpoint of a one-incident edge, the vertex star is the
    boundary fan of Fig. 4.10 rather than a full disk fan, so there is no
    Euclidean plane chart at that endpoint. **)
proof
  fix x
  assume hx_nonrel: "x \<in> e - rel_interior e"
  let ?M = "geotop_polyhedron K"
  let ?d = "\<lambda>x y. norm (x - y)"
  let ?TM = "top1_metric_topology_on ?M ?d"
  have hx_e: "x \<in> e"
    using hx_nonrel by (by100 blast)
  have hxM: "x \<in> ?M"
    using heK hx_e unfolding geotop_polyhedron_def by (by100 blast)
  have hrel_bd: "rel_interior e
      \<subseteq> geotop_manifold_boundary ?M ?d"
    by (rule geotop_one_incident_edge_rel_interior_subset_manifold_boundary_dev34
        [OF hK hKM heK hedge hcard1])
  have hnot_int: "x \<notin> geotop_manifold_interior ?M ?d"
  proof
    assume hxint: "x \<in> geotop_manifold_interior ?M ?d"
    obtain U f where hUopen: "openin_on ?M ?TM U"
      and hxU: "x \<in> U"
      and hhomeo: "top1_homeomorphism_on U
          (subspace_topology ?M ?TM U)
          (UNIV::(real^2) set) geotop_euclidean_topology f"
      using hxint unfolding geotop_manifold_interior_def by (by100 blast)
    obtain r where hr: "r > 0"
      and hball_sub: "?M \<inter> ball x r \<subseteq> U"
      using geotop_openin_norm_polyhedron_contains_relative_ball_dev34
        [OF hUopen hxU]
      by (by100 blast)
    have hclosure_e: "closure (rel_interior e) = e"
      by (rule geotop_complex_simplex_closure_rel_interior[OF hK heK])
    have hx_closure: "x \<in> closure (rel_interior e)"
      using hclosure_e hx_e by (by100 simp)
    obtain p where hp_rel: "p \<in> rel_interior e"
      and hdist: "dist x p < r"
      using closure_approachableD[OF hx_closure hr] by (by100 blast)
    have hp_ball: "p \<in> ball x r"
      using hdist by (by100 simp)
    have hpM: "p \<in> ?M"
      using heK hp_rel rel_interior_subset unfolding geotop_polyhedron_def
      by (by100 blast)
    have hpU: "p \<in> U"
      using hball_sub hpM hp_ball by (by100 blast)
    have hpint: "p \<in> geotop_manifold_interior ?M ?d"
      unfolding geotop_manifold_interior_def
      using hpM hUopen hpU hhomeo by (by100 blast)
    have hpbd: "p \<in> geotop_manifold_boundary ?M ?d"
      using hrel_bd hp_rel by (by100 blast)
    have hp_not_int: "p \<notin> geotop_manifold_interior ?M ?d"
      using hpbd unfolding geotop_manifold_boundary_def by (by100 blast)
    show False
      using hpint hp_not_int by (by100 blast)
  qed
  show "x \<in> geotop_manifold_boundary ?M ?d"
    unfolding geotop_manifold_boundary_def using hxM hnot_int by (by100 blast)
qed

lemma geotop_one_incident_edges_subset_manifold_boundary_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  shows "\<Union>{e\<in>K. geotop_is_edge e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}
      \<subseteq> geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  (**
    Moise Theorem 9, boundary-edge direction: at an interior point of an edge
    incident with exactly one 2-simplex, the local star is a half-plane
    neighborhood, so the point has no plane chart in \<open>|K|\<close>. **)
proof
  fix x
  assume hx: "x \<in> \<Union>{e \<in> K. geotop_is_edge e \<and>
        card {\<sigma> \<in> K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
  show "x \<in> geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  proof -
    obtain e where heK: "e \<in> K"
      and hedge: "geotop_is_edge e"
      and hcard1:
        "card {\<sigma> \<in> K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
      and hx_e: "x \<in> e"
      using hx by (by100 blast)
    show ?thesis
    proof (cases "x \<in> rel_interior e")
      case True
      have hrel_sub: "rel_interior e
          \<subseteq> geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
        by (rule geotop_one_incident_edge_rel_interior_subset_manifold_boundary_dev34
            [OF hK hKM heK hedge hcard1])
      show ?thesis
        using True hrel_sub by (by100 blast)
    next
      case False
      have hx_nonrel: "x \<in> e - rel_interior e"
        using hx_e False by (by100 blast)
      have hnonrel_sub: "e - rel_interior e
          \<subseteq> geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
        by (rule geotop_one_incident_edge_non_rel_interior_subset_manifold_boundary_dev34
            [OF hK hKM heK hedge hcard1])
      show ?thesis
        using hx_nonrel hnonrel_sub by (by100 blast)
    qed
  qed
qed

lemma geotop_manifold_boundary_subset_one_incident_edges_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  shows "geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))
      \<subseteq> \<Union>{e\<in>K. geotop_is_edge e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
  (**
    Moise Theorem 9, converse direction: if a point is not in a one-incident
    edge, then the one-or-two edge count and the connected link/star
    classification give a plane neighborhood, so it lies in the manifold
    interior. **)
proof
  fix p
  assume hpbd: "p \<in> geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  show "p \<in> \<Union>{e \<in> K. geotop_is_edge e \<and>
        card {\<sigma> \<in> K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
  proof (rule ccontr)
    assume hnot:
      "p \<notin> \<Union>{e \<in> K. geotop_is_edge e \<and>
        card {\<sigma> \<in> K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
    have hpint: "p \<in> geotop_manifold_interior
        (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
      by (rule geotop_boundary_not_one_incident_point_is_manifold_interior_dev34
          [OF hK hKM hpbd hnot])
    have hpnotint: "p \<notin> geotop_manifold_interior
        (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
      using hpbd unfolding geotop_manifold_boundary_def by (by100 blast)
    show False
      using hpint hpnotint by (by100 blast)
  qed
qed

lemma geotop_manifold_boundary_eq_one_incident_edges_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  shows "geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) =
      \<Union>{e\<in>K. geotop_is_edge e
        \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
  (**
    Moise Theorem 9 final sentence (geotop.tex:1056): if \<open>\<partial>K\<close> is the
    set of all edges lying in exactly one 2-simplex, then
    \<open>Bd |K| = |\<partial>K|\<close>.  The proof is the two local chart directions:
    one-incident edge interiors have half-plane neighborhoods, while points
    not on such edges have plane neighborhoods from the one-or-two edge count
    and connected link/star classification. **)
proof (rule subset_antisym)
  show "geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))
      \<subseteq> \<Union>{e \<in> K. geotop_is_edge e \<and>
            card {\<sigma> \<in> K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
    by (rule geotop_manifold_boundary_subset_one_incident_edges_dev34[OF hK hKM])
  show "\<Union>{e \<in> K. geotop_is_edge e \<and>
            card {\<sigma> \<in> K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}
      \<subseteq> geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
    by (rule geotop_one_incident_edges_subset_manifold_boundary_dev34[OF hK hKM])
qed

(** from \<S>4 Theorem 9 (geotop.tex:1052)
    LATEX VERSION: Let K be a complex such that M = |K| is a 2-manifold with boundary. Then
      K is a combinatorial 2-manifold with boundary, and Bd M is the union of the edges of K
      that lie in only one 2-simplex of K. **)
theorem Theorem_GT_4_9:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  shows "\<forall>v\<in>geotop_complex_vertices K. geotop_comb_n_cell (geotop_star K v) 2"
    and "geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) =
         \<Union>{e\<in>K. geotop_is_edge e \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
  (** Moise proof (geotop.tex:1054): As in Theorem 8, #(2-simplexes containing
      an edge e) is 1 or 2 (L2-L4 reused). Hence each component of |L(v)| is
      a broken line (edges with 1 triangle) or a 1-sphere (all edges with 2).
      |L(v)| connected (L5). So |L(v)| is a single broken line or polygon. St v
      is a combinatorial 2-cell.
      For Bd |K| = \<Union>(edges in only 1 triangle): such edges are exactly the ones
      at the manifold boundary. **)
proof -
  show "\<forall>v\<in>geotop_complex_vertices K. geotop_comb_n_cell (geotop_star K v) 2"
  proof
    fix v assume hv: "v \<in> geotop_complex_vertices K"
    (** Same five lemmas as in 4.8 but weakened L3: each edge in \<ge> 1 triangle. **)
    \<comment> \<open>L1: \<exists> incident edge at v.\<close>
    have hL1: "\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e"
    proof (rule ccontr)
      assume hno: "\<not> (\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e)"
      have hvK: "{v} \<in> K"
        using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
      have hvM: "v \<in> geotop_polyhedron K"
        using hvK unfolding geotop_polyhedron_def by (by100 blast)
      have hsingle_open:
        "{v} \<in> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
        by (rule geotop_complex_no_incident_edge_vertex_open_singleton[OF hK hv hno])
      have hnot_open:
        "{v} \<notin> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
        by (rule geotop_2_manifold_with_boundary_no_open_singleton[OF hKM hvM])
      show False
        using hsingle_open hnot_open by (by100 blast)
    qed
    \<comment> \<open>L1 consequence: the link is nonempty, taking the other endpoint
      of an incident edge.\<close>
    have hL1_link_poly_nonempty: "\<Union>(geotop_link K v) \<noteq> {}"
    proof -
      obtain e where heK: "e \<in> K" and hedge: "geotop_is_edge e" and hv_e: "v \<in> e"
        using hL1 by (by100 blast)
      have hvK: "{v} \<in> K"
        using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
      show ?thesis
        by (rule geotop_incident_edge_link_polyhedron_nonempty
            [OF hK hvK heK hedge hv_e])
    qed
    \<comment> \<open>L2: every incident edge is contained in some 2-simplex.\<close>
    have hL2: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
                (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>)"
    proof (intro ballI impI)
      fix e assume heK: "e \<in> K"
        and he_inc: "geotop_is_edge e \<and> v \<in> e"
      have hedge: "geotop_is_edge e"
        using he_inc by (by100 blast)
      show "\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>"
      proof (rule ccontr)
        assume hno2: "\<not> (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>)"
        have hrel_open:
          "rel_interior e \<in>
            subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
          by (rule geotop_complex_no_2_simplex_over_edge_rel_interior_open
              [OF hK heK hedge hno2])
        have hrel_sub: "rel_interior e \<subseteq> geotop_polyhedron K"
          using heK rel_interior_subset unfolding geotop_polyhedron_def by (by100 blast)
        show False
          by (rule geotop_2_manifold_with_boundary_no_open_edge_rel_interior
              [OF hKM hedge hrel_open hrel_sub])
      qed
	    qed
    \<comment> \<open>Counted form of L2: every incident edge has at least one counted
      two-simplex face.\<close>
    have hL2_count: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
                card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 1"
    proof (intro ballI impI)
      fix e assume heK: "e \<in> K" and he_inc: "geotop_is_edge e \<and> v \<in> e"
      have hedge: "geotop_is_edge e"
        using he_inc by (by100 blast)
      have hex: "\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>"
        using hL2 heK he_inc by (by100 blast)
      show "1 \<le> card {\<sigma> \<in> K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
        by (rule geotop_complex_edge_in_2_simplex_imp_face_count_ge_1
            [OF hK heK hedge hex])
    qed
    \<comment> \<open>L3-with-boundary: each incident edge in \<le> 2 triangles
      (\<le> 2, not = 2 — this is the manifold-with-boundary case).\<close>
    have hL3_counterexample_faces: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
                \<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2 \<longrightarrow>
                (\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
                  \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
                  \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
                  \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3)"
    proof (intro ballI impI)
      fix e assume heK: "e \<in> K" and he_inc: "geotop_is_edge e \<and> v \<in> e"
        and hnot_le2: "\<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
      have hge3: "3 \<le> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
        using hnot_le2 by (by100 simp)
      show "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
                  \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
                  \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
                  \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
        by (rule geotop_complex_edge_face_count_ge_3_obtain[OF hge3])
	    qed
	    have hL3: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
	                card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
    proof
      fix e assume heK: "e \<in> K"
      show "geotop_is_edge e \<and> v \<in> e \<longrightarrow>
          card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
      proof
        assume he_inc: "geotop_is_edge e \<and> v \<in> e"
        show "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
        proof -
          have hnot_counterexample:
            "\<not> \<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
          proof
            assume hnot_le2:
              "\<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
            have hfaces_ex:
                "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
                  \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
                  \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
                  \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
            proof -
              have hL3_at: "geotop_is_edge e \<and> v \<in> e \<longrightarrow>
                \<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2 \<longrightarrow>
                (\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
                  \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
                  \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
                  \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3)"
                using hL3_counterexample_faces heK by (by100 simp)
              have hL3_imp: "\<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2 \<longrightarrow>
                (\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
                  \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
                  \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
                  \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3)"
                by (rule mp[OF hL3_at he_inc])
              show ?thesis
                by (rule mp[OF hL3_imp hnot_le2])
            qed
            have hedge: "geotop_is_edge e"
              using he_inc by (by100 blast)
            obtain p where hp: "p \<in> rel_interior e"
              using geotop_edge_rel_interior_nonempty[OF hedge] by (by100 blast)
            have hpM: "p \<in> geotop_polyhedron K"
              using heK hp rel_interior_subset unfolding geotop_polyhedron_def by (by100 blast)
            let ?M = "geotop_polyhedron K"
            let ?d = "\<lambda>x y. norm (x - y)"
            let ?TM = "top1_metric_topology_on ?M ?d"
            obtain U where hUopen: "openin_on ?M ?TM U"
              and hpU: "p \<in> U"
            and hcell: "geotop_is_n_cell (closure_on ?M ?TM U)
                (subspace_topology ?M ?TM (closure_on ?M ?TM U)) 2"
            using hKM hpM unfolding geotop_n_manifold_with_boundary_on_def by (by100 blast)
          show False
            by (rule geotop_boundary_chart_three_incident_2simplex_contradiction_dev34
                [OF hK heK hedge hp hfaces_ex hUopen hpU hcell])
          qed
          show "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
            using hnot_counterexample by (by100 blast)
        qed
      qed
    qed
	    \<comment> \<open>Combining counted L2 with L3: each incident edge has one or two
	      adjacent two-simplexes.\<close>
    have hL_count_1_or_2: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
                (card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1
                 \<or> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2)"
    proof (intro ballI impI)
      fix e assume heK: "e \<in> K" and he_inc: "geotop_is_edge e \<and> v \<in> e"
      let ?S = "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
      have hge: "card ?S \<ge> 1"
        using hL2_count heK he_inc by (by100 blast)
      have hle: "card ?S \<le> 2"
        using hL3 heK he_inc by (by100 blast)
      show "card ?S = 1 \<or> card ?S = 2"
        using hge hle by (by100 arith)
    qed
    \<comment> \<open>Witness form of the boundary/interior edge split: a one-sided
      edge has a unique incident two-simplex; a two-sided edge has exactly
      two named incident two-simplexes.\<close>
    have hL_one_or_two_faces: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
                ((\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>)
                 \<or> (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
                    \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
                    \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
                    \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}))"
    proof (intro ballI impI)
      fix e assume heK: "e \<in> K" and he_inc: "geotop_is_edge e \<and> v \<in> e"
      have hedge: "geotop_is_edge e"
        using he_inc by (by100 blast)
      let ?S = "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
      have hge: "card ?S \<ge> 1"
        using hL2_count heK he_inc by (by100 blast)
      have hle: "card ?S \<le> 2"
        using hL3 heK he_inc by (by100 blast)
      show "(\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>)
                 \<or> (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
                    \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
                    \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
                    \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>})"
        by (rule geotop_complex_edge_face_count_between_1_2_cases
            [OF hK heK hedge hge hle])
    qed
    \<comment> \<open>Boundary-case analogue: every link vertex is incident to a link edge.\<close>
    have hlink_vertices_incident_edges:
      "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
          (\<exists>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l)"
    proof -
      have hvK: "{v} \<in> K"
        using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
      show ?thesis
        by (rule geotop_link_vertices_count_ge_1_incident_link_edges
            [OF hK hvK hL2_count])
    qed
    \<comment> \<open>L4: link |L(v)| is connected.\<close>
    have hL4: "top1_connected_on (\<Union>(geotop_link K v))
                 (subspace_topology UNIV geotop_euclidean_topology
                    (\<Union>(geotop_link K v)))"
      by (rule geotop_2_manifold_with_boundary_link_polyhedron_connected_from_vertex_star_dev34
          [OF hK hKM hv])
    \<comment> \<open>L5: link is a broken line or polygon.\<close>
    have hL5: "geotop_is_broken_line (\<Union>(geotop_link K v)) \<or>
                geotop_is_polygon (\<Union>(geotop_link K v))"
    proof -
      have hlink_complex: "geotop_is_complex (geotop_link K v)"
        by (rule geotop_link_is_complex[OF hK])
      have hlink_nonempty: "\<Union>(geotop_link K v) \<noteq> {}"
        using hL1_link_poly_nonempty .
      have hcomponent_nonisolated_witnesses:
        "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
            C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P)
          \<longrightarrow> (\<exists>L. geotop_is_complex L
            \<and> geotop_complex_is_1dim L
            \<and> finite L
            \<and> geotop_polyhedron L = C
            \<and> geotop_complex_connected L
            \<and> (\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>l\<in>L. geotop_is_edge l \<and> w \<in> l)))"
        by (rule geotop_link_components_nonisolated_subcomplex_witnesses
            [OF hK hv hlink_vertices_incident_edges])
      have hcomponent_linear_graph_witnesses:
        "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
            C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P)
          \<longrightarrow> (\<exists>L. geotop_is_linear_graph L
            \<and> finite L
            \<and> geotop_polyhedron L = C
            \<and> geotop_complex_connected L
            \<and> (\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>l\<in>L. geotop_is_edge l \<and> w \<in> l)))"
        by (rule geotop_link_components_nonisolated_linear_graph_witnesses
            [OF hK hv hlink_vertices_incident_edges])
      have hlink_vertices_degree_one_or_two_incident_edges:
        "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
            card {l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l} = 1 \<or>
            card {l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l} = 2"
      proof -
        have hvK: "{v} \<in> K"
          using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
        show ?thesis
          by (rule geotop_link_vertices_face_count_one_or_two_incident_link_edge_card_dev34
              [OF hK hvK hL_one_or_two_faces])
      qed
      have hcomponent_degree_one_or_two_linear_graph_witnesses:
        "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
            C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P)
          \<longrightarrow> (\<exists>L. geotop_is_linear_graph L
            \<and> finite L
            \<and> geotop_polyhedron L = C
            \<and> geotop_complex_connected L
            \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
                card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 1 \<or>
                card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 2))"
        by (rule geotop_link_components_degree_one_or_two_linear_graph_witnesses_dev34
            [OF hK hv hlink_vertices_degree_one_or_two_incident_edges])
      have hlocal_line_or_polygon_components:
        "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
               C = geotop_component_at UNIV geotop_euclidean_topology
                     (\<Union>(geotop_link K v)) P)
            \<longrightarrow> geotop_is_broken_line C \<or> geotop_is_polygon C"
      proof (intro allI impI)
        fix C
        assume hC_ex: "\<exists>P\<in>\<Union>(geotop_link K v).
               C = geotop_component_at UNIV geotop_euclidean_topology
                     (\<Union>(geotop_link K v)) P"
        obtain P where hP: "P \<in> \<Union>(geotop_link K v)"
          and hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                     (\<Union>(geotop_link K v)) P"
          using hC_ex by (by100 blast)
        have hP_C: "P \<in> C"
          using geotop_link_component_summary[OF hK hv hP hC] by (by100 blast)
        have hC_imp: "(\<exists>P\<in>\<Union>(geotop_link K v).
               C = geotop_component_at UNIV geotop_euclidean_topology
                     (\<Union>(geotop_link K v)) P) \<longrightarrow>
            (\<exists>L. geotop_is_linear_graph L
              \<and> finite L
              \<and> geotop_polyhedron L = C
              \<and> geotop_complex_connected L
              \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
                  card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 1 \<or>
                  card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 2))"
          by (rule spec[OF hcomponent_degree_one_or_two_linear_graph_witnesses])
        have hL_ex: "\<exists>L. geotop_is_linear_graph L
              \<and> finite L
              \<and> geotop_polyhedron L = C
              \<and> geotop_complex_connected L
              \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
                  card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 1 \<or>
                  card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 2)"
          by (rule mp[OF hC_imp hC_ex])
        obtain L where hL_linear: "geotop_is_linear_graph L"
          and hL_fin: "finite L"
          and hL_poly: "geotop_polyhedron L = C"
          and hL_conn: "geotop_complex_connected L"
          and hL_degree12: "\<forall>w. {w} \<in> L \<longrightarrow>
                  card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 1 \<or>
                  card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 2"
          using hL_ex by (elim exE conjE)
        have hL_nonempty: "L \<noteq> {}"
          using hP_C hL_poly unfolding geotop_polyhedron_def by (by100 blast)
        have hshape_L: "geotop_is_broken_line (geotop_polyhedron L) \<or>
            geotop_is_polygon (geotop_polyhedron L)"
          by (rule geotop_finite_connected_degree_one_or_two_linear_graph_line_or_polygon_dev34
              [OF hL_linear hL_fin hL_nonempty hL_conn hL_degree12])
        show "geotop_is_broken_line C \<or> geotop_is_polygon C"
          using hshape_L hL_poly by (by100 simp)
      qed
      have hsingle_shape_from_connected:
        "geotop_is_broken_line (\<Union>(geotop_link K v)) \<or>
         geotop_is_polygon (\<Union>(geotop_link K v))"
      proof -
        obtain P where hP: "P \<in> \<Union>(geotop_link K v)"
          using hlink_nonempty by (by100 blast)
        let ?C = "geotop_component_at UNIV geotop_euclidean_topology
                     (\<Union>(geotop_link K v)) P"
        have hC_shape: "geotop_is_broken_line ?C \<or> geotop_is_polygon ?C"
          using hlocal_line_or_polygon_components hP by (by100 blast)
        have hC_eq: "?C = \<Union>(geotop_link K v)"
          by (rule geotop_connected_component_at_eq_self[OF hP hL4])
        show ?thesis
          using hC_shape hC_eq by (by100 simp)
      qed
      show ?thesis
        using hsingle_shape_from_connected .
    qed
    \<comment> \<open>L6 (main conclusion): Star is a combinatorial 2-cell.\<close>
    have hL6: "geotop_comb_n_cell (geotop_star K v) 2"
    proof -
      show ?thesis
        by (rule geotop_vertex_star_comb_2cell_from_link_line_or_polygon_dev34
            [OF hK hv hL5])
    qed
    have hL_all:
      "(\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e) \<and>
       (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
               (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>)) \<and>
       (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
               card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 1) \<and>
       (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
               \<not> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2 \<longrightarrow>
               (\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
                 \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
                 \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
                 \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3)) \<and>
       (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
               card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2) \<and>
       (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
               (card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1
                \<or> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2)) \<and>
       (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
               ((\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>)
                \<or> (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
                   \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
                   \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
                   \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}))) \<and>
       top1_connected_on (\<Union>(geotop_link K v))
                 (subspace_topology UNIV geotop_euclidean_topology (\<Union>(geotop_link K v))) \<and>
       (geotop_is_broken_line (\<Union>(geotop_link K v))
                     \<or> geotop_is_polygon (\<Union>(geotop_link K v))) \<and>
       geotop_comb_n_cell (geotop_star K v) 2"
      using hL1 hL2 hL2_count hL3_counterexample_faces hL3 hL_count_1_or_2
        hL_one_or_two_faces hL4 hL5 hL6
      by (by100 blast)
    show "geotop_comb_n_cell (geotop_star K v) 2" using hL6 .
  qed
next
  (** Bd |K| = union of edges lying in only one 2-simplex. **)
  show "geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) =
         \<Union>{e\<in>K. geotop_is_edge e \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
    by (rule geotop_manifold_boundary_eq_one_incident_edges_dev34[OF hK hKM])
qed

lemma top1_norm_metric_on_UNIV:
  "top1_metric_on (UNIV::'a::real_normed_vector set) (\<lambda>x y. norm (x - y))"
  unfolding top1_metric_on_def
  by (auto simp: dist_norm [symmetric] dist_commute intro: dist_triangle)

lemma top1_norm_metric_topology_on_eq_geotop_subspace:
  fixes M :: "'a::real_normed_vector set"
  shows "top1_metric_topology_on M (\<lambda>x y. norm (x - y)) =
         subspace_topology UNIV geotop_euclidean_topology M"
proof -
  have hsub:
    "subspace_topology UNIV
        (top1_metric_topology_on UNIV (\<lambda>x y. norm (x - y))) M =
     top1_metric_topology_on M (\<lambda>x y. norm (x - y))"
    by (rule subspace_metric_topology_eq_metric_topology[
        OF top1_norm_metric_on_UNIV subset_UNIV])
  show ?thesis
    using hsub unfolding geotop_euclidean_topology_def by (by100 simp)
qed

lemma geotop_open_ball_homeomorphic_UNIV:
  fixes a :: "'a::real_normed_vector"
  assumes hr: "0 < r"
  shows "\<exists>f. top1_homeomorphism_on (ball a r)
              (subspace_topology UNIV geotop_euclidean_topology (ball a r))
              (UNIV::'a set) geotop_euclidean_topology f"
proof -
  obtain f where hf:
    "top1_homeomorphism_on (ball a r)
       (subspace_topology UNIV geotop_euclidean_topology (ball a r))
       (UNIV::'a set) (subspace_topology UNIV geotop_euclidean_topology UNIV) f"
    using geotop_HOL_homeomorphic_imp_top1_homeomorphism_on[
        OF homeomorphic_ball_UNIV[OF hr]]
    by (by100 blast)
  have hUNIV: "subspace_topology UNIV geotop_euclidean_topology (UNIV::'a set) =
               geotop_euclidean_topology"
    by (rule subspace_topology_self_carrier) (by100 simp)
  show ?thesis
    by (rule exI[where x=f]) (use hf hUNIV in \<open>by100 simp\<close>)
qed

lemma geotop_manifold_interior_if_HOL_interior:
  fixes M :: "(real^2) set"
  assumes hP: "P \<in> interior M"
  shows "P \<in> geotop_manifold_interior M (\<lambda>x y. norm (x - y))"
proof -
  obtain r where hr: "0 < r" and hball_sub_int: "ball P r \<subseteq> interior M"
  proof -
    have "\<forall>x\<in>interior M. \<exists>e>0. ball x e \<subseteq> interior M"
      using open_interior open_contains_ball by (by100 blast)
    thus ?thesis using hP that by (by100 blast)
  qed
  let ?U = "ball P r"
  have hU_sub_M: "?U \<subseteq> M"
    using hball_sub_int interior_subset by (by100 blast)
  have hP_U: "P \<in> ?U"
    using hr by (by100 simp)
  have hP_M: "P \<in> M"
    using hP_U hU_sub_M by (by100 blast)
  have hU_geotop_open: "?U \<in> geotop_euclidean_topology"
    using open_ball unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have hU_subspace: "?U \<in> subspace_topology UNIV geotop_euclidean_topology M"
  proof -
    have "?U = M \<inter> ?U"
      using hU_sub_M by (by100 blast)
    thus ?thesis
      unfolding subspace_topology_def using hU_geotop_open by (by100 blast)
  qed
  have htopM: "top1_metric_topology_on M (\<lambda>x y. norm (x - y)) =
               subspace_topology UNIV geotop_euclidean_topology M"
    by (rule top1_norm_metric_topology_on_eq_geotop_subspace)
  have hU_openin: "openin_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) ?U"
    unfolding openin_on_def using htopM hU_sub_M hU_subspace by (by100 simp)
  obtain f where hf:
    "top1_homeomorphism_on ?U
        (subspace_topology UNIV geotop_euclidean_topology ?U)
        (UNIV::(real^2) set) geotop_euclidean_topology f"
    using geotop_open_ball_homeomorphic_UNIV[OF hr] by (by100 blast)
  have hsubU:
    "subspace_topology M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) ?U =
     subspace_topology UNIV geotop_euclidean_topology ?U"
  proof -
    have "subspace_topology M (subspace_topology UNIV geotop_euclidean_topology M) ?U =
          subspace_topology UNIV geotop_euclidean_topology ?U"
      by (rule subspace_topology_trans[OF hU_sub_M])
    thus ?thesis using htopM by (by100 simp)
  qed
  have hf_metric:
    "top1_homeomorphism_on ?U
        (subspace_topology M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) ?U)
        (UNIV::(real^2) set) geotop_euclidean_topology f"
    using hf hsubU by (by100 simp)
  show ?thesis
    unfolding geotop_manifold_interior_def
    using hP_M hU_openin hP_U hf_metric by (by100 blast)
qed

(** from \<S>4 Theorem 10 (geotop.tex:1058)
    LATEX VERSION: Let M be a 2-manifold with boundary, lying in R^2. If M is closed, then
      Bd M = Fr M. **)
theorem Theorem_GT_4_10:
  fixes M :: "(real^2) set"
  assumes hM: "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2"
  assumes hMcl: "closedin_on UNIV geotop_euclidean_topology M"
  shows "geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) =
         geotop_frontier UNIV geotop_euclidean_topology M"
  (** Moise proof (geotop.tex:1060): Two inclusions.
      (1) Since Fr M is closed, every point of M - Fr M has a locally Euclidean
          open neighborhood in M. Hence M - Fr M \<subseteq> Int M = M - Bd M, i.e. Bd M \<subseteq> Fr M.
      (2) M closed in R\<^sup>2 so Fr M \<subseteq> M. If P \<in> Fr M, then P does NOT have a locally
          Euclidean (plane-homeomorphic) open nbhd in M \<Rightarrow> by Invariance of Domain
          (Theorem 4 = our Theorem_GT_4_invariance_of_domain) would give such a nbhd
          open in R\<^sup>2, contradicting P \<in> Fr M. Hence Fr M \<subseteq> Bd M. **)
proof -
  (** T4_10-A: Bd M \<subseteq> Fr M. Each P \<in> M - Fr M has a locally Euclidean nbhd
      open in M; hence P \<in> Int M = M - Bd M. **)
  have h_A: "geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) \<subseteq>
             geotop_frontier UNIV geotop_euclidean_topology M"
  proof
    fix P
    assume hP_bd: "P \<in> geotop_manifold_boundary M (\<lambda>x y. norm (x - y))"
    have hP_M: "P \<in> M"
      using hP_bd unfolding geotop_manifold_boundary_def by (by100 blast)
    have hP_not_mint: "P \<notin> geotop_manifold_interior M (\<lambda>x y. norm (x - y))"
      using hP_bd unfolding geotop_manifold_boundary_def by (by100 blast)
    show "P \<in> geotop_frontier UNIV geotop_euclidean_topology M"
    proof (rule ccontr)
      assume hP_not_front: "P \<notin> geotop_frontier UNIV geotop_euclidean_topology M"
      have hP_not_front_HOL: "P \<notin> frontier M"
        using hP_not_front geotop_frontier_UNIV_eq_frontier[of M] by (by100 simp)
      have hP_closure: "P \<in> closure M"
        using hP_M closure_subset by (by100 blast)
      have hP_int: "P \<in> interior M"
        using hP_not_front_HOL hP_closure
        unfolding Elementary_Topology.frontier_def by (by100 blast)
      have hP_mint: "P \<in> geotop_manifold_interior M (\<lambda>x y. norm (x - y))"
        by (rule geotop_manifold_interior_if_HOL_interior[OF hP_int])
      show False using hP_not_mint hP_mint by (by100 blast)
    qed
  qed
  (** T4_10-B: Fr M \<subseteq> Bd M. P \<in> Fr M cannot have plane-homeomorphic open nbhd
      open in M (Invariance of Domain would extend it to be open in R\<^sup>2). **)
  have h_B: "geotop_frontier UNIV geotop_euclidean_topology M \<subseteq>
             geotop_manifold_boundary M (\<lambda>x y. norm (x - y))"
  proof
    fix P
    assume hP_front: "P \<in> geotop_frontier UNIV geotop_euclidean_topology M"
    have hP_front_HOL: "P \<in> frontier M"
      using hP_front geotop_frontier_UNIV_eq_frontier[of M] by (by100 simp)
    have hM_closed: "closed M"
      using hMcl closedin_on_geotop_UNIV_iff_closed by (by100 blast)
    have hP_M: "P \<in> M"
      using hP_front_HOL hM_closed
      unfolding Elementary_Topology.frontier_def by (by100 simp)
    have hP_not_int: "P \<notin> interior M"
      using hP_front_HOL unfolding Elementary_Topology.frontier_def by (by100 blast)
    have hP_not_mint: "P \<notin> geotop_manifold_interior M (\<lambda>x y. norm (x - y))"
    proof
      assume hP_mint: "P \<in> geotop_manifold_interior M (\<lambda>x y. norm (x - y))"
      obtain U f where hU_openin:
          "openin_on M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U"
        and hP_U: "P \<in> U"
        and hf_geotop:
          "top1_homeomorphism_on U
             (subspace_topology UNIV geotop_euclidean_topology U)
             (UNIV::(real^2) set) geotop_euclidean_topology f"
        using geotop_manifold_interior_geo_chart_at_dev34[OF hP_mint]
        by (by100 blast)
      have hU_sub_M: "U \<subseteq> M"
        using hU_openin unfolding openin_on_def by (by100 blast)
      have hU_geotop_open: "U \<in> geotop_euclidean_topology"
        by (rule Theorem_GT_4_invariance_of_domain[OF hf_geotop])
      have hU_open: "open U"
        using hU_geotop_open
        unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
        by (by100 simp)
      have hP_int: "P \<in> interior M"
        by (rule interiorI[OF hU_open hP_U hU_sub_M])
      show False using hP_not_int hP_int by (by100 blast)
    qed
    show "P \<in> geotop_manifold_boundary M (\<lambda>x y. norm (x - y))"
      unfolding geotop_manifold_boundary_def using hP_M hP_not_mint by (by100 blast)
  qed
  show ?thesis using h_A h_B by (by100 blast)
qed



end
