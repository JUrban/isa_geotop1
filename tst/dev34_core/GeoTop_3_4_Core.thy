theory GeoTop_3_4_Core
  imports "GeoTop34OpenStarDirty.GeoTop_3_4_OpenStar"
begin

lemma geotop_punctured_star_radial_endpoint_choice_property_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  defines "\<rho> \<equiv> (\<lambda>x. SOME y. y \<in> \<Union>(geotop_link K v)
      \<and> (\<exists>t. 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y))"
  shows "\<forall>x\<in>\<Union>(geotop_star K v) - {v}.
      \<rho> x \<in> \<Union>(geotop_link K v)
      \<and> (\<exists>t. 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R \<rho> x)"
proof
  fix x
  assume hx: "x \<in> \<Union>(geotop_star K v) - {v}"
  have hex: "\<exists>y. y \<in> \<Union>(geotop_link K v)
      \<and> (\<exists>t. 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y)"
    using geotop_star_punctured_point_radial_to_link_dev34[OF hK hv hx]
    by (by100 blast)
  show "\<rho> x \<in> \<Union>(geotop_link K v)
      \<and> (\<exists>t. 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R \<rho> x)"
    unfolding \<rho>_def by (rule someI_ex[OF hex])
qed

lemma geotop_radial_endpoint_choice_preimage_eq_cone_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hC_sub: "C \<subseteq> \<Union>(geotop_link K v)"
  defines "\<rho> \<equiv> (\<lambda>x. SOME y. y \<in> \<Union>(geotop_link K v)
      \<and> (\<exists>t. 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y))"
  shows "{x \<in> \<Union>(geotop_star K v) - {v}. \<rho> x \<in> C}
      = {x \<in> \<Union>(geotop_star K v) - {v}.
          \<exists>y t. y \<in> C \<and> 0 < t \<and> t \<le> 1
            \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
proof -
  let ?S = "\<Union>(geotop_star K v) - {v}"
  let ?L = "\<Union>(geotop_link K v)"
  have hradial:
      "\<forall>x\<in>?S. \<rho> x \<in> ?L
        \<and> (\<exists>t. 0 < t \<and> t \<le> 1
            \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R \<rho> x)"
    using geotop_punctured_star_radial_endpoint_choice_property_dev34[OF hK hv]
    unfolding \<rho>_def by (by100 simp)
  show ?thesis
  proof
    show "{x \<in> ?S. \<rho> x \<in> C}
        \<subseteq> {x \<in> ?S. \<exists>y t. y \<in> C \<and> 0 < t \<and> t \<le> 1
              \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
    proof
      fix x
      assume hx: "x \<in> {x \<in> ?S. \<rho> x \<in> C}"
      have hxS: "x \<in> ?S"
        using hx by (by100 blast)
      have h\<rho>C: "\<rho> x \<in> C"
        using hx by (by100 blast)
      obtain t where ht_pos: "0 < t"
        and ht_le: "t \<le> 1"
        and hx_rad: "x = (1 - t) *\<^sub>R v + t *\<^sub>R \<rho> x"
        using hradial hxS by (by100 blast)
      show "x \<in> {x \<in> ?S. \<exists>y t. y \<in> C \<and> 0 < t \<and> t \<le> 1
              \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
        using hxS h\<rho>C ht_pos ht_le hx_rad by (by100 blast)
    qed
  next
    show "{x \<in> ?S. \<exists>y t. y \<in> C \<and> 0 < t \<and> t \<le> 1
              \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}
        \<subseteq> {x \<in> ?S. \<rho> x \<in> C}"
    proof
      fix x
      assume hx: "x \<in> {x \<in> ?S. \<exists>y t. y \<in> C \<and> 0 < t \<and> t \<le> 1
              \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
      obtain y t where hxS: "x \<in> ?S"
        and hyC: "y \<in> C"
        and ht_pos: "0 < t"
        and ht_le: "t \<le> 1"
        and hx_rad: "x = (1 - t) *\<^sub>R v + t *\<^sub>R y"
        using hx by (by100 blast)
      have hyL: "y \<in> ?L"
        using hyC hC_sub by (by100 blast)
      obtain t' where h\<rho>L: "\<rho> x \<in> ?L"
        and ht'_pos: "0 < t'"
        and ht'_le: "t' \<le> 1"
        and hx\<rho>_rad: "x = (1 - t') *\<^sub>R v + t' *\<^sub>R \<rho> x"
        using hradial hxS by (by100 blast)
      have hrad_eq:
        "(1 - t) *\<^sub>R v + t *\<^sub>R y =
         (1 - t') *\<^sub>R v + t' *\<^sub>R \<rho> x"
        using hx_rad hx\<rho>_rad by (by100 simp)
      have "y = \<rho> x"
        by (rule geotop_link_radial_endpoint_unique_dev34
            [OF hK hv hyL h\<rho>L ht_pos ht_le ht'_pos ht'_le hrad_eq])
      show "x \<in> {x \<in> ?S. \<rho> x \<in> C}"
        using hxS hyC \<open>y = \<rho> x\<close> by (by100 blast)
    qed
  qed
qed

lemma geotop_subspace_open_from_euclidean_ball_witness_dev34:
  fixes A S :: "(real^2) set"
  assumes hA_sub: "A \<subseteq> S"
  assumes hlocal:
    "\<And>x. x \<in> A \<Longrightarrow> \<exists>r. 0 < r \<and> ball x r \<inter> S \<subseteq> A"
  shows "A \<in> subspace_topology UNIV geotop_euclidean_topology S"
proof -
  let ?B = "{B. \<exists>x\<in>A. \<exists>r. 0 < r \<and> B = ball x r \<and> ball x r \<inter> S \<subseteq> A}"
  let ?U = "\<Union>?B"
  have hB_open: "\<forall>B\<in>?B. open B"
    by (by100 auto)
  have hU_open_HOL: "open ?U"
    by (rule open_Union) (use hB_open in \<open>by100 blast\<close>)
  have hA_eq: "A = S \<inter> ?U"
  proof
    show "A \<subseteq> S \<inter> ?U"
    proof
      fix x
      assume hxA: "x \<in> A"
      obtain r where hr_pos: "0 < r" and hr_sub: "ball x r \<inter> S \<subseteq> A"
        using hlocal[OF hxA] by (by100 blast)
      have hball_mem: "ball x r \<in> ?B"
        using hxA hr_pos hr_sub by (by100 blast)
      have hx_ball: "x \<in> ball x r"
        using hr_pos by (by100 simp)
      show "x \<in> S \<inter> ?U"
        using hA_sub hxA hball_mem hx_ball by (by100 blast)
    qed
  next
    show "S \<inter> ?U \<subseteq> A"
    proof
      fix z
      assume hz: "z \<in> S \<inter> ?U"
      obtain B where hB: "B \<in> ?B" and hzB: "z \<in> B"
        using hz by (by100 blast)
      obtain x r where hxA: "x \<in> A" and hr_pos: "0 < r"
        and hB_eq: "B = ball x r"
        and hr_sub: "ball x r \<inter> S \<subseteq> A"
        using hB by (by100 blast)
      have "z \<in> ball x r \<inter> S"
        using hz hzB hB_eq by (by100 blast)
      show "z \<in> A"
        using hr_sub \<open>z \<in> ball x r \<inter> S\<close> by (by100 blast)
    qed
  qed
  have hU_open_top: "?U \<in> geotop_euclidean_topology"
    using hU_open_HOL
    unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  show ?thesis
    unfolding subspace_topology_def
    using hA_eq hU_open_top by (by100 blast)
qed

lemma geotop_complex_point_finite_local_carrier_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hx: "x \<in> geotop_polyhedron K"
  shows "\<exists>r F. 0 < r \<and> finite F \<and> F \<subseteq> K
      \<and> ball x r \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
proof -
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K" and hx\<sigma>: "x \<in> \<sigma>"
    using hx unfolding geotop_polyhedron_def by (by100 blast)
  have hK_local:
    "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U
        \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule geotop_is_complex_locally_finite[OF hK])
  have hlocal_\<sigma>: "\<exists>U. open U \<and> \<sigma> \<subseteq> U
        \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule bspec[OF hK_local h\<sigma>K])
  obtain U where hU_open: "open U" and h\<sigma>U: "\<sigma> \<subseteq> U"
    and hU_finite: "finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    using hlocal_\<sigma> by (by100 blast)
  have hxU: "x \<in> U"
    using hx\<sigma> h\<sigma>U by (by100 blast)
  have hU_ball: "\<forall>x\<in>U. \<exists>r>0. ball x r \<subseteq> U"
    using hU_open open_contains_ball[of U] by (by100 simp)
  have hex_r: "\<exists>r>0. ball x r \<subseteq> U"
    using hU_ball hxU by (by100 blast)
  obtain r where hr_pos: "0 < r" and hballU: "ball x r \<subseteq> U"
    using hex_r by (by100 blast)
  let ?F = "{\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
  have hF_sub: "?F \<subseteq> K"
    by (by100 blast)
  have hlocal_cover: "ball x r \<inter> geotop_polyhedron K \<subseteq> \<Union>?F"
  proof
    fix z
    assume hz: "z \<in> ball x r \<inter> geotop_polyhedron K"
    obtain \<tau> where h\<tau>K: "\<tau> \<in> K" and hz\<tau>: "z \<in> \<tau>"
      using hz unfolding geotop_polyhedron_def by (by100 blast)
    have hzU: "z \<in> U"
      using hz hballU by (by100 blast)
    have "\<tau> \<inter> U \<noteq> {}"
      using hz\<tau> hzU by (by100 blast)
    have "\<tau> \<in> ?F"
      using h\<tau>K \<open>\<tau> \<inter> U \<noteq> {}\<close> by (by100 blast)
    show "z \<in> \<Union>?F"
      using \<open>\<tau> \<in> ?F\<close> hz\<tau> by (by100 blast)
  qed
  show ?thesis
    using hr_pos hU_finite hF_sub hlocal_cover by (by100 blast)
qed

lemma geotop_complex_edge_point_finite_local_cover_dev34:
  fixes K :: "(real^2) set set" and e :: "(real^2) set" and p :: "real^2"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hp: "p \<in> e"
  shows "\<exists>r F. 0 < r \<and> finite F \<and> F \<subseteq> K \<and> e \<in> F
      \<and> ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
proof -
  have hpM: "p \<in> geotop_polyhedron K"
    using heK hp unfolding geotop_polyhedron_def by (by100 blast)
  obtain r F where hr: "0 < r"
    and hFfin: "finite F"
    and hFsub: "F \<subseteq> K"
    and hcover: "ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
    using geotop_complex_point_finite_local_carrier_dev34[OF hK hpM]
    by (by100 blast)
  let ?F = "insert e F"
  have hFfin': "finite ?F"
    using hFfin by (by100 simp)
  have hFsub': "?F \<subseteq> K"
    using heK hFsub by (by100 blast)
  have hcover': "ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>?F"
    using hcover by (by100 blast)
  show ?thesis
    using hr hFfin' hFsub' hcover' by (by100 blast)
qed

lemma geotop_complex_edge_unique_face_count_eq_1_dev34:
  fixes K :: "(real^2) set set" and e :: "(real^2) set"
  assumes hunique:
    "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  shows "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
proof -
  let ?S = "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
  let ?P = "\<lambda>\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  have hunique_def: "\<exists>\<sigma>. ?P \<sigma> \<and> (\<forall>\<tau>. ?P \<tau> \<longrightarrow> \<tau> = \<sigma>)"
    using hunique unfolding Ex1_def by (by100 simp)
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
    and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and h\<sigma>face: "geotop_is_face e \<sigma>"
    and huniq_all: "\<forall>\<tau>. ?P \<tau> \<longrightarrow> \<tau> = \<sigma>"
    using hunique_def by (elim exE conjE)
  have huniqP: "\<And>\<tau>. ?P \<tau> \<Longrightarrow> \<tau> = \<sigma>"
    using huniq_all by (by100 simp)
  have hSeq: "?S = {\<sigma>}"
  proof
    show "?S \<subseteq> {\<sigma>}"
    proof
      fix \<tau>
      assume h\<tau>S: "\<tau> \<in> ?S"
      have h\<tau>K: "\<tau> \<in> K"
        using h\<tau>S by (by100 simp)
      have h\<tau>2: "geotop_simplex_dim \<tau> 2"
        using h\<tau>S by (by100 simp)
      have h\<tau>face: "geotop_is_face e \<tau>"
        using h\<tau>S by (by100 simp)
      have h\<tau>P: "?P \<tau>"
        using h\<tau>K h\<tau>2 h\<tau>face by (by100 simp)
      have "\<tau> = \<sigma>"
        by (rule huniqP[OF h\<tau>P])
      thus "\<tau> \<in> {\<sigma>}"
        by (by100 simp)
    qed
  next
    show "{\<sigma>} \<subseteq> ?S"
      using h\<sigma>K h\<sigma>2 h\<sigma>face by (by100 simp)
  qed
  show ?thesis
    using hSeq by (by100 simp)
qed

lemma geotop_complex_edge_unique_face_obtain_dev34:
  fixes K :: "(real^2) set set" and e :: "(real^2) set"
  assumes hunique:
    "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  obtains \<sigma> where "\<sigma> \<in> K" and "geotop_simplex_dim \<sigma> 2" and "geotop_is_face e \<sigma>"
    and "{\<tau>\<in>K. geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>} = {\<sigma>}"
proof -
  let ?S = "{\<tau>\<in>K. geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>}"
  let ?P = "\<lambda>\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  have hunique_def: "\<exists>\<sigma>. ?P \<sigma> \<and> (\<forall>\<tau>. ?P \<tau> \<longrightarrow> \<tau> = \<sigma>)"
    using hunique unfolding Ex1_def by (by100 simp)
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
    and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and h\<sigma>face: "geotop_is_face e \<sigma>"
    and huniq_all: "\<forall>\<tau>. ?P \<tau> \<longrightarrow> \<tau> = \<sigma>"
    using hunique_def by (elim exE conjE)
  have huniqP: "\<And>\<tau>. ?P \<tau> \<Longrightarrow> \<tau> = \<sigma>"
    using huniq_all by (by100 simp)
  have hSeq: "?S = {\<sigma>}"
  proof
    show "?S \<subseteq> {\<sigma>}"
    proof
      fix \<tau>
      assume h\<tau>S: "\<tau> \<in> ?S"
      have h\<tau>K: "\<tau> \<in> K"
        using h\<tau>S by (by100 simp)
      have h\<tau>2: "geotop_simplex_dim \<tau> 2"
        using h\<tau>S by (by100 simp)
      have h\<tau>face: "geotop_is_face e \<tau>"
        using h\<tau>S by (by100 simp)
      have h\<tau>P: "?P \<tau>"
        using h\<tau>K h\<tau>2 h\<tau>face by (by100 simp)
      have "\<tau> = \<sigma>"
        by (rule huniqP[OF h\<tau>P])
      thus "\<tau> \<in> {\<sigma>}"
        by (by100 simp)
    qed
  next
    show "{\<sigma>} \<subseteq> ?S"
      using h\<sigma>K h\<sigma>2 h\<sigma>face by (by100 simp)
  qed
  show ?thesis
    by (rule that[OF h\<sigma>K h\<sigma>2 h\<sigma>face hSeq])
qed

lemma geotop_complex_unique_edge_face_point_finite_local_cover_dev34:
  fixes K :: "(real^2) set set" and e :: "(real^2) set" and p :: "real^2"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hp: "p \<in> e"
  assumes hunique:
    "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  obtains r F \<sigma>
    where "0 < r"
      and "finite F"
      and "F \<subseteq> K"
      and "e \<in> F"
      and "\<sigma> \<in> F"
      and "\<sigma> \<in> K"
      and "geotop_simplex_dim \<sigma> 2"
      and "geotop_is_face e \<sigma>"
      and "{\<tau>\<in>K. geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>} = {\<sigma>}"
      and "ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
proof -
  obtain r F where hr: "0 < r"
    and hFfin: "finite F"
    and hFsub: "F \<subseteq> K"
    and heF: "e \<in> F"
    and hcover: "ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
    using geotop_complex_edge_point_finite_local_cover_dev34[OF hK heK hp]
    by (by100 blast)
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
    and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and h\<sigma>face: "geotop_is_face e \<sigma>"
    and hfaces: "{\<tau>\<in>K. geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>} = {\<sigma>}"
    by (rule geotop_complex_edge_unique_face_obtain_dev34[OF hunique])
  let ?F = "insert \<sigma> F"
  have hFfin': "finite ?F"
    using hFfin by (by100 simp)
  have hFsub': "?F \<subseteq> K"
    using hFsub h\<sigma>K by (by100 blast)
  have heF': "e \<in> ?F"
    using heF by (by100 simp)
  have h\<sigma>F': "\<sigma> \<in> ?F"
    by (by100 simp)
  have hcover': "ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>?F"
    using hcover by (by100 blast)
  show ?thesis
    by (rule that[OF hr hFfin' hFsub' heF' h\<sigma>F' h\<sigma>K h\<sigma>2 h\<sigma>face hfaces hcover'])
qed

lemma geotop_complex_three_edge_faces_point_finite_local_cover_dev34:
  fixes K :: "(real^2) set set" and e :: "(real^2) set" and p :: "real^2"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hp: "p \<in> e"
  assumes hfaces:
    "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
      \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
      \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
      \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
  obtains r F \<sigma>1 \<sigma>2 \<sigma>3
    where "0 < r"
      and "finite F"
      and "F \<subseteq> K"
      and "e \<in> F"
      and "\<sigma>1 \<in> F"
      and "\<sigma>2 \<in> F"
      and "\<sigma>3 \<in> F"
      and "\<sigma>1 \<noteq> \<sigma>2"
      and "\<sigma>2 \<noteq> \<sigma>3"
      and "\<sigma>1 \<noteq> \<sigma>3"
      and "\<sigma>1 \<in> K" and "geotop_simplex_dim \<sigma>1 2" and "geotop_is_face e \<sigma>1"
      and "\<sigma>2 \<in> K" and "geotop_simplex_dim \<sigma>2 2" and "geotop_is_face e \<sigma>2"
      and "\<sigma>3 \<in> K" and "geotop_simplex_dim \<sigma>3 2" and "geotop_is_face e \<sigma>3"
      and "ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
proof -
  obtain r F where hr: "0 < r"
    and hFfin: "finite F"
    and hFsub: "F \<subseteq> K"
    and heF: "e \<in> F"
    and hcover: "ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
    using geotop_complex_edge_point_finite_local_cover_dev34[OF hK heK hp]
    by (by100 blast)
  obtain \<sigma>1 \<sigma>2 \<sigma>3 where hfaces_w:
    "\<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
      \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
      \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
      \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
    using hfaces by (elim exE)
  have h12: "\<sigma>1 \<noteq> \<sigma>2"
    using hfaces_w by (by100 simp)
  have h23: "\<sigma>2 \<noteq> \<sigma>3"
    using hfaces_w by (by100 simp)
  have h13: "\<sigma>1 \<noteq> \<sigma>3"
    using hfaces_w by (by100 simp)
  have h\<sigma>1K: "\<sigma>1 \<in> K"
    using hfaces_w by (by100 simp)
  have h\<sigma>1dim: "geotop_simplex_dim \<sigma>1 2"
    using hfaces_w by (by100 simp)
  have h\<sigma>1face: "geotop_is_face e \<sigma>1"
    using hfaces_w by (by100 simp)
  have h\<sigma>2K: "\<sigma>2 \<in> K"
    using hfaces_w by (by100 simp)
  have h\<sigma>2dim: "geotop_simplex_dim \<sigma>2 2"
    using hfaces_w by (by100 simp)
  have h\<sigma>2face: "geotop_is_face e \<sigma>2"
    using hfaces_w by (by100 simp)
  have h\<sigma>3K: "\<sigma>3 \<in> K"
    using hfaces_w by (by100 simp)
  have h\<sigma>3dim: "geotop_simplex_dim \<sigma>3 2"
    using hfaces_w by (by100 simp)
  have h\<sigma>3face: "geotop_is_face e \<sigma>3"
    using hfaces_w by (by100 simp)
  let ?F = "insert \<sigma>1 (insert \<sigma>2 (insert \<sigma>3 F))"
  have hFfin': "finite ?F"
    using hFfin by (by100 simp)
  have hFsub': "?F \<subseteq> K"
    using hFsub h\<sigma>1K h\<sigma>2K h\<sigma>3K by (by100 blast)
  have heF': "e \<in> ?F"
    using heF by (by100 simp)
  have h\<sigma>1F': "\<sigma>1 \<in> ?F"
    by (by100 simp)
  have h\<sigma>2F': "\<sigma>2 \<in> ?F"
    by (by100 simp)
  have h\<sigma>3F': "\<sigma>3 \<in> ?F"
    by (by100 simp)
  have hcover': "ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>?F"
    using hcover by (by100 blast)
  show ?thesis
    by (rule that[OF hr hFfin' hFsub' heF' h\<sigma>1F' h\<sigma>2F' h\<sigma>3F'
          h12 h23 h13 h\<sigma>1K h\<sigma>1dim h\<sigma>1face h\<sigma>2K h\<sigma>2dim h\<sigma>2face
          h\<sigma>3K h\<sigma>3dim h\<sigma>3face hcover'])
qed

lemma geotop_complex_finite_subcomplex_local_point_carriers_dev34:
  fixes K F :: "(real^2) set set" and p :: "real^2"
  assumes hK: "geotop_is_complex K"
  assumes hFfin: "finite F"
  assumes hFsub: "F \<subseteq> K"
  assumes hpF: "p \<in> \<Union>F"
  shows "\<exists>\<delta>>0. ball p \<delta> \<inter> \<Union>F \<subseteq> \<Union>{\<tau>\<in>F. p \<in> \<tau>}"
proof -
  have hclosed: "\<forall>\<tau>\<in>F. closed \<tau>"
  proof
    fix \<tau>
    assume h\<tau>F: "\<tau> \<in> F"
    have h\<tau>K: "\<tau> \<in> K"
      using hFsub h\<tau>F by (by100 blast)
    show "closed \<tau>"
      by (rule geotop_complex_simplex_closed[OF hK h\<tau>K])
  qed
  have hB: "\<Union>F = \<Union>F"
    by (by100 simp)
  show ?thesis
    by (rule finite_union_closed_local_isolation[OF hFfin hclosed hB hpF])
qed

lemma geotop_complex_unique_edge_face_point_carrier_subset_unique_face_dev34:
  fixes K :: "(real^2) set set" and e \<sigma> \<tau> :: "(real^2) set" and p :: "real^2"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>face: "geotop_is_face e \<sigma>"
  assumes hfaces: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>}"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes hp\<tau>: "p \<in> \<tau>"
  shows "\<tau> \<subseteq> \<sigma>"
proof -
  have he_sub_\<tau>: "e \<subseteq> \<tau>"
    by (rule geotop_complex_rel_interior_imp_subset[OF hK heK h\<tau>K hp hp\<tau>])
  have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
    by (rule geotop_is_face_imp_subset[OF h\<sigma>face])
  have h\<tau>simp: "geotop_is_simplex \<tau>"
    using geotop_is_complex_simplex[OF hK] h\<tau>K by (by100 blast)
  obtain n where h\<tau>dim: "geotop_simplex_dim \<tau> n"
    using h\<tau>simp unfolding geotop_is_simplex_def geotop_simplex_dim_def
    by (by100 blast)
  have hn_le2: "n \<le> 2"
    by (rule geotop_simplex_dim_le_2_R2[OF h\<tau>dim])
  show ?thesis
  proof (cases "n = 2")
    case True
    have h\<tau>2: "geotop_simplex_dim \<tau> 2"
      using h\<tau>dim True by (by100 simp)
    have hface: "geotop_is_face e \<tau>"
      by (rule geotop_complex_subset_simplex_face[OF hK heK h\<tau>K he_sub_\<tau>])
    have h\<tau>in: "\<tau> \<in> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
      using h\<tau>K h\<tau>2 hface by (by100 simp)
    have "\<tau> = \<sigma>"
      using h\<tau>in hfaces by (by100 simp)
    thus ?thesis
      by (by100 simp)
  next
    case False
    have hn_le1: "n \<le> 1"
      using hn_le2 False by (by100 arith)
    have hn_cases: "n = 0 \<or> n = 1"
      using hn_le1 by (by100 arith)
    show ?thesis
    proof (rule disjE[OF hn_cases])
      assume hn0: "n = 0"
      obtain a b where hab: "a \<noteq> b" and he_seg: "e = closed_segment a b"
        by (rule geotop_edge_closed_segment_obtain[OF hedge])
      obtain V m where hV_fin: "finite V"
        and hV_card: "card V = 0 + 1"
        and h\<tau>_eq: "\<tau> = geotop_convex_hull V"
        using h\<tau>dim hn0 unfolding geotop_simplex_dim_def by (by100 blast)
      have hV_card1: "card V = 1"
        using hV_card by (by100 simp)
      obtain c where hV_eq: "V = {c}"
        using hV_card1 by (rule card_1_singletonE)
      have h\<tau>_sing: "\<tau> = {c}"
        using h\<tau>_eq hV_eq geotop_convex_hull_eq_HOL[of "{c}"] by (by100 simp)
      have ha\<tau>: "a \<in> \<tau>"
      proof -
        have "a \<in> e"
          using he_seg by (by100 simp)
        thus ?thesis
          using he_sub_\<tau> by (by100 blast)
      qed
      have hb\<tau>: "b \<in> \<tau>"
      proof -
        have "b \<in> e"
          using he_seg by (by100 simp)
        thus ?thesis
          using he_sub_\<tau> by (by100 blast)
      qed
      have "a = b"
        using ha\<tau> hb\<tau> h\<tau>_sing by (by100 simp)
      thus ?thesis
        using hab by (by100 blast)
    next
      assume hn1: "n = 1"
      have h\<tau>edge: "geotop_is_edge \<tau>"
        using h\<tau>dim hn1 unfolding geotop_is_edge_def by (by100 simp)
      have hface: "geotop_is_face e \<tau>"
        by (rule geotop_complex_subset_simplex_face[OF hK heK h\<tau>K he_sub_\<tau>])
      have heq: "e = \<tau>"
        by (rule geotop_edge_face_of_edge_eq[OF hedge h\<tau>edge hface])
      show ?thesis
        using heq he_sub_\<sigma> by (by100 blast)
    qed
  qed
qed

lemma geotop_complex_unique_edge_face_point_carrier_union_subset_unique_face_dev34:
  fixes K F :: "(real^2) set set" and e \<sigma> :: "(real^2) set" and p :: "real^2"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>face: "geotop_is_face e \<sigma>"
  assumes hfaces: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>}"
  assumes hFsub: "F \<subseteq> K"
  shows "\<Union>{\<tau>\<in>F. p \<in> \<tau>} \<subseteq> \<sigma>"
proof
  fix x
  assume hx: "x \<in> \<Union>{\<tau>\<in>F. p \<in> \<tau>}"
  obtain \<tau> where h\<tau>F: "\<tau> \<in> F" and hp\<tau>: "p \<in> \<tau>" and hx\<tau>: "x \<in> \<tau>"
    using hx by (by100 blast)
  have h\<tau>K: "\<tau> \<in> K"
    using hFsub h\<tau>F by (by100 blast)
  have h\<tau>sub: "\<tau> \<subseteq> \<sigma>"
    by (rule geotop_complex_unique_edge_face_point_carrier_subset_unique_face_dev34
        [OF hK heK hedge hp h\<sigma>K h\<sigma>2 h\<sigma>face hfaces h\<tau>K hp\<tau>])
  show "x \<in> \<sigma>"
    using h\<tau>sub hx\<tau> by (by100 blast)
qed

lemma geotop_complex_polyhedron_point_carrier_local_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hx: "x \<in> geotop_polyhedron K"
  shows "\<exists>\<tau>\<in>K. x \<in> rel_interior \<tau>"
  (**
    Carrier decomposition for locally finite complexes.  This is the same
    minimal-face argument as the finite carrier lemma, with local finiteness
    used only to make the set of simplices containing \<open>x\<close> finite. **)
proof -
  define F where "F = {\<sigma>\<in>K. x \<in> \<sigma>}"
  have hF_sub: "F \<subseteq> K" unfolding F_def by (by100 blast)
  obtain \<sigma>\<^sub>0 where h\<sigma>\<^sub>0K: "\<sigma>\<^sub>0 \<in> K" and hx_\<sigma>\<^sub>0: "x \<in> \<sigma>\<^sub>0"
    using hx unfolding geotop_polyhedron_def by (by100 blast)
  have h\<sigma>\<^sub>0_F: "\<sigma>\<^sub>0 \<in> F"
    unfolding F_def using h\<sigma>\<^sub>0K hx_\<sigma>\<^sub>0 by (by100 blast)
  have hF_ne: "F \<noteq> {}" using h\<sigma>\<^sub>0_F by (by100 blast)
  have hK_local:
    "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U
        \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule geotop_is_complex_locally_finite[OF hK])
  have hlocal_\<sigma>\<^sub>0:
    "\<exists>U. open U \<and> \<sigma>\<^sub>0 \<subseteq> U
        \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule bspec[OF hK_local h\<sigma>\<^sub>0K])
  obtain U where hU_open: "open U" and h\<sigma>\<^sub>0U: "\<sigma>\<^sub>0 \<subseteq> U"
    and hU_finite: "finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    using hlocal_\<sigma>\<^sub>0 by (by100 blast)
  have hxU: "x \<in> U"
    using hx_\<sigma>\<^sub>0 h\<sigma>\<^sub>0U by (by100 blast)
  have hF_fin: "finite F"
  proof -
    have hF_sub_local: "F \<subseteq> {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    proof
      fix \<tau>
      assume h\<tau>F: "\<tau> \<in> F"
      have h\<tau>K: "\<tau> \<in> K"
        using h\<tau>F unfolding F_def by (by100 blast)
      have hx\<tau>: "x \<in> \<tau>"
        using h\<tau>F unfolding F_def by (by100 blast)
      have "\<tau> \<inter> U \<noteq> {}"
        using hx\<tau> hxU by (by100 blast)
      show "\<tau> \<in> {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
        using h\<tau>K \<open>\<tau> \<inter> U \<noteq> {}\<close> by (by100 blast)
    qed
    show ?thesis
      by (rule finite_subset[OF hF_sub_local hU_finite])
  qed
  define card_v :: "(real^2) set \<Rightarrow> nat" where
    "card_v = (\<lambda>\<sigma>. card (SOME V::(real^2) set. geotop_simplex_vertices \<sigma> V))"
  have h_simp_all: "\<forall>\<rho>\<in>K. geotop_is_simplex \<rho>"
    by (rule conjunct1[OF hK[unfolded geotop_is_complex_def]])
  have h_card_pos_F: "\<forall>\<sigma>\<in>F. 0 < card_v \<sigma>"
  proof
    fix \<sigma> assume h\<sigma>: "\<sigma> \<in> F"
    have h\<sigma>K: "\<sigma> \<in> K" using h\<sigma> hF_sub by (by100 blast)
    have h\<sigma>_simp: "geotop_is_simplex \<sigma>" using h\<sigma>K h_simp_all by (by100 blast)
    have h_ex: "\<exists>V. geotop_simplex_vertices \<sigma> V"
      using h\<sigma>_simp unfolding geotop_is_simplex_def geotop_simplex_vertices_def
      by (by100 blast)
    have h_some: "geotop_simplex_vertices \<sigma> (SOME V. geotop_simplex_vertices \<sigma> V)"
      using h_ex by (rule someI_ex)
    have h_card: "\<exists>n. card (SOME V. geotop_simplex_vertices \<sigma> V) = n + 1"
      using h_some unfolding geotop_simplex_vertices_def by (by100 blast)
    show "0 < card_v \<sigma>" unfolding card_v_def using h_card by (by100 auto)
  qed
  define n_min where "n_min = Min (card_v ` F)"
  have hcF_fin: "finite (card_v ` F)" using hF_fin by (by100 simp)
  have hcF_ne: "card_v ` F \<noteq> {}" using hF_ne by (by100 blast)
  have h_n_min_in: "n_min \<in> card_v ` F"
    unfolding n_min_def using Min_in[OF hcF_fin hcF_ne] by (by100 blast)
  obtain \<tau> where h\<tau>_F: "\<tau> \<in> F" and h\<tau>_min: "card_v \<tau> = n_min"
    using h_n_min_in by (by100 blast)
  have h\<tau>_min_prop: "\<forall>\<sigma>\<in>F. card_v \<tau> \<le> card_v \<sigma>"
  proof
    fix \<sigma> assume h\<sigma>F: "\<sigma> \<in> F"
    have h_image: "card_v \<sigma> \<in> card_v ` F" using h\<sigma>F by (by100 blast)
    have h_min_le: "Min (card_v ` F) \<le> card_v \<sigma>"
      using Min_le[OF hcF_fin h_image] by (by100 blast)
    show "card_v \<tau> \<le> card_v \<sigma>"
      using h\<tau>_min h_min_le unfolding n_min_def by (by100 simp)
  qed
  have h\<tau>_K: "\<tau> \<in> K" using h\<tau>_F hF_sub by (by100 blast)
  have hx_\<tau>: "x \<in> \<tau>" using h\<tau>_F unfolding F_def by (by100 blast)
  have hx_ri: "x \<in> rel_interior \<tau>"
  proof (rule ccontr)
    assume h_not_ri: "x \<notin> rel_interior \<tau>"
    have h\<tau>_simp: "geotop_is_simplex \<tau>" using h\<tau>_K h_simp_all by (by100 blast)
    obtain V where hV: "geotop_simplex_vertices \<tau> V"
      using h\<tau>_simp unfolding geotop_is_simplex_def geotop_simplex_vertices_def
      by (by100 blast)
    have hV_fin: "finite V" using hV unfolding geotop_simplex_vertices_def by (by100 blast)
    have hV_ai: "\<not> affine_dependent V"
      by (rule geotop_general_position_imp_aff_indep[OF hV])
    have h\<tau>_hull_g: "\<tau> = geotop_convex_hull V"
      using hV unfolding geotop_simplex_vertices_def by (by100 blast)
    have h\<tau>_hull: "\<tau> = convex hull V"
      using h\<tau>_hull_g geotop_convex_hull_eq_HOL by (by100 simp)
    have h_chull_finite: "convex hull V
                          = {y. \<exists>u. (\<forall>w\<in>V. 0 \<le> u w)
                                  \<and> sum u V = 1
                                  \<and> (\<Sum>w\<in>V. u w *\<^sub>R w) = y}"
      by (rule convex_hull_finite[OF hV_fin])
    have hx_in_set: "x \<in> {y. \<exists>u. (\<forall>w\<in>V. 0 \<le> u w)
                                  \<and> sum u V = 1
                                  \<and> (\<Sum>w\<in>V. u w *\<^sub>R w) = y}"
      using hx_\<tau> h\<tau>_hull h_chull_finite by (by100 metis)
    obtain u where hu_nn: "\<forall>w\<in>V. 0 \<le> u w"
      and hu_sum: "sum u V = 1"
      and hu_combo: "(\<Sum>w\<in>V. u w *\<^sub>R w) = x"
      using hx_in_set by (by100 blast)
    have h_ri_char: "rel_interior \<tau>
                       = {y. \<exists>u. (\<forall>v\<in>V. 0 < u v)
                                 \<and> sum u V = 1
                                 \<and> (\<Sum>v\<in>V. u v *\<^sub>R v) = y}"
      using rel_interior_convex_hull_explicit[OF hV_ai] h\<tau>_hull by (by100 simp)
    have h_some_zero: "\<exists>w\<in>V. u w = 0"
    proof (rule ccontr)
      assume h_no: "\<not> (\<exists>w\<in>V. u w = 0)"
      have h_all_pos: "\<forall>w\<in>V. 0 < u w"
      proof
        fix w assume hw: "w \<in> V"
        have h_nn: "0 \<le> u w" using hu_nn hw by (by100 blast)
        have h_ne: "u w \<noteq> 0" using h_no hw by (by100 blast)
        show "0 < u w" using h_nn h_ne by (by100 force)
      qed
      have hx_in_ri: "x \<in> rel_interior \<tau>"
        unfolding h_ri_char using h_all_pos hu_sum hu_combo by (by100 blast)
      show False using hx_in_ri h_not_ri by (by100 blast)
    qed
    define W where "W = {w\<in>V. 0 < u w}"
    have hW_sub: "W \<subseteq> V" unfolding W_def by (by100 blast)
    have hW_fin: "finite W" using finite_subset[OF hW_sub hV_fin] by (by100 simp)
    have hW_strict: "W \<noteq> V"
    proof
      assume h_eq: "W = V"
      obtain w where hw_V: "w \<in> V" and hw_zero: "u w = 0"
        using h_some_zero by (by100 blast)
      have hw_W: "w \<in> W" using hw_V h_eq by (by100 simp)
      have h_pos_W: "0 < u w" using hw_W unfolding W_def by (by100 blast)
      show False using h_pos_W hw_zero by (by100 linarith)
    qed
    have hW_ne: "W \<noteq> {}"
    proof (rule ccontr)
      assume hW_em: "\<not> W \<noteq> {}"
      have hW_emp: "W = {}" using hW_em by (by100 blast)
      have h_all_zero: "\<forall>w\<in>V. u w = 0"
      proof
        fix w assume hw: "w \<in> V"
        have h_nn: "0 \<le> u w" using hu_nn hw by (by100 blast)
        have h_not_pos: "\<not> (0 < u w)"
          using hw hW_emp unfolding W_def by (by100 blast)
        thus "u w = 0" using h_nn by (by100 force)
      qed
      have h_sum_zero: "sum u V = 0" using h_all_zero by (by100 simp)
      show False using h_sum_zero hu_sum by (by100 simp)
    qed
    have h_VmW_zero: "\<forall>w\<in>V - W. u w = 0"
    proof
      fix w assume hw: "w \<in> V - W"
      have hw_V: "w \<in> V" using hw by (by100 blast)
      have hw_nW: "w \<notin> W" using hw by (by100 blast)
      have h_nn: "0 \<le> u w" using hu_nn hw_V by (by100 blast)
      have h_not_pos: "\<not> (0 < u w)" using hw_nW hw_V unfolding W_def by (by100 blast)
      show "u w = 0" using h_nn h_not_pos by (by100 force)
    qed
    have h_VmW_combo_zero: "(\<Sum>w\<in>V-W. u w *\<^sub>R w) = 0"
    proof (rule sum.neutral)
      show "\<forall>w\<in>V-W. u w *\<^sub>R w = 0" using h_VmW_zero by (by100 simp)
    qed
    have h_V_split: "V = W \<union> (V - W)" using hW_sub by (by100 blast)
    have h_disj: "W \<inter> (V - W) = {}" by (by100 blast)
    have h_VmW_fin: "finite (V - W)" using hV_fin by (by100 simp)
    have h_split_combo:
      "(\<Sum>w\<in>V. u w *\<^sub>R w) =
       (\<Sum>w\<in>W. u w *\<^sub>R w) + (\<Sum>w\<in>V-W. u w *\<^sub>R w)"
    proof -
      have h1: "(\<Sum>w\<in>W \<union> (V - W). u w *\<^sub>R w)
                  = (\<Sum>w\<in>W. u w *\<^sub>R w) + (\<Sum>w\<in>V-W. u w *\<^sub>R w)"
        by (rule sum.union_disjoint[OF hW_fin h_VmW_fin h_disj])
      have h2: "(\<Sum>w\<in>V. u w *\<^sub>R w) = (\<Sum>w\<in>W \<union> (V - W). u w *\<^sub>R w)"
        using h_V_split by (by100 simp)
      show ?thesis using h1 h2 by (by100 simp)
    qed
    have hx_W_combo: "x = (\<Sum>w\<in>W. u w *\<^sub>R w)"
      using hu_combo h_split_combo h_VmW_combo_zero by (by100 simp)
    have h_VmW_sum_zero: "sum u (V - W) = 0"
      using h_VmW_zero by (by100 simp)
    have h_split_sum: "sum u V = sum u W + sum u (V - W)"
      using sum.union_disjoint[OF hW_fin h_VmW_fin h_disj] h_V_split by (by100 simp)
    have hu_W_sum: "sum u W = 1"
      using h_split_sum h_VmW_sum_zero hu_sum by (by100 simp)
    define F\<^sub>x where "F\<^sub>x = convex hull W"
    have h_HOL_eq_W: "geotop_convex_hull W = convex hull W"
      by (rule geotop_convex_hull_eq_HOL)
    have hF\<^sub>x_g: "F\<^sub>x = geotop_convex_hull W"
      unfolding F\<^sub>x_def using h_HOL_eq_W by (by100 simp)
    have h_face: "geotop_is_face F\<^sub>x \<tau>"
      unfolding geotop_is_face_def
      using hV hW_ne hW_sub hF\<^sub>x_g by (by100 blast)
    have h_face_closed: "\<forall>\<rho>\<in>K. \<forall>\<phi>. geotop_is_face \<phi> \<rho> \<longrightarrow> \<phi> \<in> K"
      by (rule conjunct1[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]])
    have hF\<^sub>x_K: "F\<^sub>x \<in> K"
      using h_face_closed h\<tau>_K h_face by (by100 blast)
    have h_F_chull_finite: "convex hull W
                              = {y. \<exists>u. (\<forall>w\<in>W. 0 \<le> u w)
                                       \<and> sum u W = 1
                                       \<and> (\<Sum>w\<in>W. u w *\<^sub>R w) = y}"
      by (rule convex_hull_finite[OF hW_fin])
    have hu_W_nn: "\<forall>w\<in>W. 0 \<le> u w" using hu_nn hW_sub by (by100 blast)
    have hx_F\<^sub>x: "x \<in> F\<^sub>x"
      unfolding F\<^sub>x_def
      using h_F_chull_finite hu_W_nn hu_W_sum hx_W_combo by (by100 blast)
    have hF\<^sub>x_F: "F\<^sub>x \<in> F" unfolding F_def using hF\<^sub>x_K hx_F\<^sub>x by (by100 blast)
    have h_W_psub: "W \<subset> V" using hW_sub hW_strict by (by100 blast)
    have h_W_card_lt: "card W < card V"
      using psubset_card_mono[OF hV_fin h_W_psub] by (by100 simp)
    have hF\<^sub>x_card: "card_v F\<^sub>x = card W"
    proof -
      have hF\<^sub>x_simp: "geotop_is_simplex F\<^sub>x" using hF\<^sub>x_K h_simp_all by (by100 blast)
      have hW_ai: "\<not> affine_dependent W"
        by (rule affine_independent_subset[OF hV_ai hW_sub])
      have hF\<^sub>x_HOL: "F\<^sub>x = convex hull W" unfolding F\<^sub>x_def by (by100 simp)
      have hF\<^sub>x_geo: "F\<^sub>x = geotop_convex_hull W"
        using hF\<^sub>x_HOL h_HOL_eq_W by (by100 simp)
      have hW_card_pos: "0 < card W"
        using hW_fin hW_ne card_gt_0_iff by (by100 blast)
      define n where "n = card W - 1"
      have h_card_n: "card W = n + 1" unfolding n_def using hW_card_pos by (by100 linarith)
      have h_n_le_n: "n \<le> n" by (by100 simp)
      have hW_gp: "geotop_general_position W n"
        by (rule geotop_ai_imp_general_position[OF hW_fin h_card_n hW_ai])
      have hF\<^sub>x_sv: "geotop_simplex_vertices F\<^sub>x W"
        unfolding geotop_simplex_vertices_def
        using hW_fin h_card_n h_n_le_n hW_gp hF\<^sub>x_geo by (by100 blast)
      have hF\<^sub>x_ex: "\<exists>V'. geotop_simplex_vertices F\<^sub>x V'" using hF\<^sub>x_sv by (by100 blast)
      have hF\<^sub>x_some: "geotop_simplex_vertices F\<^sub>x (SOME V'. geotop_simplex_vertices F\<^sub>x V')"
        using hF\<^sub>x_ex by (rule someI_ex)
      have h_some_eq: "(SOME V'. geotop_simplex_vertices F\<^sub>x V') = W"
        by (rule geotop_simplex_vertices_unique[OF hF\<^sub>x_some hF\<^sub>x_sv])
      show "card_v F\<^sub>x = card W" unfolding card_v_def using h_some_eq by (by100 simp)
    qed
    have h\<tau>_card: "card_v \<tau> = card V"
    proof -
      have h_ex: "\<exists>V'. geotop_simplex_vertices \<tau> V'" using hV by (by100 blast)
      have h_some: "geotop_simplex_vertices \<tau> (SOME V'. geotop_simplex_vertices \<tau> V')"
        using h_ex by (rule someI_ex)
      have h_some_eq: "(SOME V'. geotop_simplex_vertices \<tau> V') = V"
        by (rule geotop_simplex_vertices_unique[OF h_some hV])
      show "card_v \<tau> = card V" unfolding card_v_def using h_some_eq by (by100 simp)
    qed
    have h_lt: "card_v F\<^sub>x < card_v \<tau>"
      using hF\<^sub>x_card h\<tau>_card h_W_card_lt by (by100 simp)
    have h_min_violate: "card_v \<tau> \<le> card_v F\<^sub>x"
      using h\<tau>_min_prop hF\<^sub>x_F by (by100 blast)
    show False using h_lt h_min_violate by (by100 linarith)
  qed
  show ?thesis using h\<tau>_K hx_ri by (by100 blast)
qed

lemma geotop_complex_polyhedron_point_carrier_unique_local_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hx: "x \<in> geotop_polyhedron K"
  shows "\<exists>!\<tau>. \<tau> \<in> K \<and> x \<in> rel_interior \<tau>"
  (**
    Local-finite carrier uniqueness: existence uses the previous local
    carrier lemma; uniqueness is the standard disjoint-relative-interior
    property of complexes. **)
proof -
  obtain \<tau> where h\<tau>K: "\<tau> \<in> K" and hx\<tau>: "x \<in> rel_interior \<tau>"
    using geotop_complex_polyhedron_point_carrier_local_dev34[OF hK hx]
    by (by100 blast)
  show ?thesis
  proof (rule ex1I[where a=\<tau>])
    show "\<tau> \<in> K \<and> x \<in> rel_interior \<tau>"
      using h\<tau>K hx\<tau> by (by100 blast)
  next
    fix \<tau>'
    assume h\<tau>': "\<tau>' \<in> K \<and> x \<in> rel_interior \<tau>'"
    have h\<tau>'K: "\<tau>' \<in> K" using h\<tau>' by (by100 blast)
    have hx\<tau>': "x \<in> rel_interior \<tau>'" using h\<tau>' by (by100 blast)
    show "\<tau>' = \<tau>"
      using geotop_carrier_unique[OF hK h\<tau>'K h\<tau>K hx\<tau>' hx\<tau>] by (by100 blast)
  qed
qed

lemma geotop_finite_carrier_local_ball_glue_dev34:
  fixes F :: "(real^2) set set"
  assumes hr0: "0 < r0"
  assumes hF_fin: "finite F"
  assumes hcover: "ball x r0 \<inter> S \<subseteq> \<Union>F"
  assumes hlocal:
    "\<And>C. C \<in> F \<Longrightarrow> \<exists>r. 0 < r \<and> ball x r \<inter> S \<inter> C \<subseteq> A"
  shows "\<exists>r. 0 < r \<and> ball x r \<inter> S \<subseteq> A"
proof -
  obtain rad where hrad:
    "\<forall>C\<in>F. 0 < rad C \<and> ball x (rad C) \<inter> S \<inter> C \<subseteq> A"
    using hlocal by (by100 metis)
  let ?R = "insert r0 (rad ` F)"
  have hR_fin: "finite ?R"
    using hF_fin by (by100 simp)
  have hR_nonempty: "?R \<noteq> {}"
    by (by100 simp)
  have hR_pos: "\<forall>a\<in>?R. 0 < a"
    using hr0 hrad by (by100 blast)
  define r where "r = Min ?R"
  have hr_in: "r \<in> ?R"
    unfolding r_def by (rule Min_in[OF hR_fin hR_nonempty])
  have hr_pos: "0 < r"
    using hR_pos hr_in by (by100 blast)
  have hr_le_r0: "r \<le> r0"
    unfolding r_def by (rule Min_le[OF hR_fin]) (by100 simp)
  have hr_le_rad: "\<And>C. C \<in> F \<Longrightarrow> r \<le> rad C"
    unfolding r_def by (rule Min_le[OF hR_fin]) (by100 blast)
  have hball_sub: "ball x r \<inter> S \<subseteq> A"
  proof
    fix z
    assume hz: "z \<in> ball x r \<inter> S"
    have hz_r0: "z \<in> ball x r0"
      using hz hr_le_r0 by (by100 simp)
    have hz_cover: "z \<in> \<Union>F"
      using hcover hz hz_r0 by (by100 blast)
    obtain C where hC: "C \<in> F" and hzC: "z \<in> C"
      using hz_cover by (by100 blast)
    have hz_rad: "z \<in> ball x (rad C)"
      using hz hr_le_rad[OF hC] by (by100 simp)
    have "z \<in> ball x (rad C) \<inter> S \<inter> C"
      using hz hzC hz_rad by (by100 blast)
    show "z \<in> A"
      using hrad hC \<open>z \<in> ball x (rad C) \<inter> S \<inter> C\<close>
      by (by100 blast)
  qed
  show ?thesis
    using hr_pos hball_sub by (by100 blast)
qed

lemma geotop_simplex_point_neighborhood_empty_if_notin_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes hx_not: "x \<notin> \<sigma>"
  shows "\<exists>r. 0 < r \<and> ball x r \<inter> \<sigma> = {}"
proof -
  have h\<sigma>_closed: "closed \<sigma>"
    by (rule geotop_complex_simplex_closed[OF hK h\<sigma>K])
  have h\<sigma>_ne: "\<sigma> \<noteq> {}"
    by (rule geotop_complex_simplex_nonempty[OF hK h\<sigma>K])
  show ?thesis
    by (rule geotop_ball_avoids_closed_not_containing
        [OF h\<sigma>_closed h\<sigma>_ne hx_not])
qed

lemma geotop_ball_avoids_closed_not_containing_allow_empty_dev34:
  fixes C :: "'a::metric_space set" and x :: 'a
  assumes hC_closed: "closed C"
  assumes hx_not: "x \<notin> C"
  shows "\<exists>r. 0 < r \<and> ball x r \<inter> C = {}"
proof -
  have hopen: "open (- C)"
    using hC_closed unfolding closed_def by (by100 simp)
  have hx: "x \<in> - C"
    using hx_not by (by100 simp)
  have hball_all: "\<forall>z\<in>- C. \<exists>r>0. ball z r \<subseteq> - C"
    using hopen open_contains_ball[of "- C"] by (by100 simp)
  obtain r where hr_pos: "0 < r" and hball: "ball x r \<subseteq> - C"
    using hball_all hx by (by100 blast)
  have "ball x r \<inter> C = {}"
    using hball by (by100 blast)
  show ?thesis
    using hr_pos \<open>ball x r \<inter> C = {}\<close> by (by100 blast)
qed

lemma geotop_radial_cone_over_compact_closed_dev34:
  fixes C :: "(real^2) set"
  assumes hC_compact: "compact C"
  shows "closed {z. \<exists>y s.
      y \<in> C \<and> 0 \<le> s \<and> s \<le> 1
        \<and> z = (1 - s) *\<^sub>R v + s *\<^sub>R y}"
proof -
  let ?D = "{0..1::real} \<times> C"
  let ?f = "(\<lambda>p::real \<times> (real^2).
      (1 - fst p) *\<^sub>R v + fst p *\<^sub>R snd p)"
  have hcone_eq:
    "{z. \<exists>y s.
        y \<in> C \<and> 0 \<le> s \<and> s \<le> 1
          \<and> z = (1 - s) *\<^sub>R v + s *\<^sub>R y} = ?f ` ?D"
  proof
    show "{z. \<exists>y s.
        y \<in> C \<and> 0 \<le> s \<and> s \<le> 1
          \<and> z = (1 - s) *\<^sub>R v + s *\<^sub>R y} \<subseteq> ?f ` ?D"
    proof
      fix z
      assume "z \<in> {z. \<exists>y s.
        y \<in> C \<and> 0 \<le> s \<and> s \<le> 1
          \<and> z = (1 - s) *\<^sub>R v + s *\<^sub>R y}"
      then obtain y s where hyC: "y \<in> C"
        and hs0: "0 \<le> s" and hs1: "s \<le> 1"
        and hz: "z = (1 - s) *\<^sub>R v + s *\<^sub>R y"
        by (by100 blast)
      have hsI: "s \<in> {0..1::real}"
        using hs0 hs1 by (by100 simp)
      have hpD: "(s, y) \<in> ?D"
        using hsI hyC by (by100 simp)
      have "z = ?f (s, y)"
        using hz by (by100 simp)
      show "z \<in> ?f ` ?D"
        using hpD \<open>z = ?f (s, y)\<close> by (by100 blast)
    qed
  next
    show "?f ` ?D \<subseteq> {z. \<exists>y s.
        y \<in> C \<and> 0 \<le> s \<and> s \<le> 1
          \<and> z = (1 - s) *\<^sub>R v + s *\<^sub>R y}"
    proof
      fix z
      assume "z \<in> ?f ` ?D"
      then obtain p where hpD: "p \<in> ?D" and hz: "z = ?f p"
        by (by100 blast)
      obtain s y where hp: "p = (s, y)"
        by (cases p) (by100 blast)
      have hsI: "s \<in> {0..1::real}" and hyC: "y \<in> C"
        using hpD hp by (by100 simp_all)
      have hs0: "0 \<le> s" and hs1: "s \<le> 1"
        using hsI by (by100 simp_all)
      have "z = (1 - s) *\<^sub>R v + s *\<^sub>R y"
        using hz hp by (by100 simp)
      show "z \<in> {z. \<exists>y s.
        y \<in> C \<and> 0 \<le> s \<and> s \<le> 1
          \<and> z = (1 - s) *\<^sub>R v + s *\<^sub>R y}"
        using hyC hs0 hs1 \<open>z = (1 - s) *\<^sub>R v + s *\<^sub>R y\<close>
        by (by100 blast)
    qed
  qed
  have hI_compact: "compact ({0..1::real})"
    by (rule compact_Icc)
  have hD_compact: "compact ?D"
    by (rule compact_Times[OF hI_compact hC_compact])
  have hf_cont: "continuous_on ?D ?f"
    by (intro continuous_intros)
  have himg_compact: "compact (?f ` ?D)"
    by (rule compact_continuous_image[OF hf_cont hD_compact])
  have "closed (?f ` ?D)"
    by (rule compact_imp_closed[OF himg_compact])
  show ?thesis
    using hcone_eq \<open>closed (?f ` ?D)\<close> by (by100 simp)
qed

lemma geotop_radial_bad_endpoint_cone_closed_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes h\<epsilon>_pos: "0 < \<epsilon>"
  shows "closed {z. \<exists>y' s.
      y' \<in> \<Union>(geotop_link K v) - ball y \<epsilon>
        \<and> 0 \<le> s \<and> s \<le> 1
        \<and> z = (1 - s) *\<^sub>R v + s *\<^sub>R y'}"
proof -
  let ?L = "\<Union>(geotop_link K v)"
  let ?C = "?L - ball y \<epsilon>"
  have hL_compact: "compact ?L"
    by (rule geotop_link_polyhedron_compact_at_complex_vertex[OF hK hv])
  have hball_open: "open (ball y \<epsilon>)"
    by (rule open_ball)
  have hball_compl_closed: "closed (- ball y \<epsilon>)"
    by (rule closed_Compl[OF hball_open])
  have hC_eq: "?C = ?L \<inter> (- ball y \<epsilon>)"
    by (by100 blast)
  have hC_compact: "compact ?C"
  proof -
    have "compact (?L \<inter> (- ball y \<epsilon>))"
      by (rule compact_Int_closed[OF hL_compact hball_compl_closed])
    thus ?thesis
      using hC_eq by (by100 simp)
  qed
  show ?thesis
    by (rule geotop_radial_cone_over_compact_closed_dev34[OF hC_compact])
qed

lemma geotop_radial_bad_endpoint_cone_avoids_point_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hyL: "y \<in> \<Union>(geotop_link K v)"
  assumes ht_pos: "0 < t"
  assumes ht_le: "t \<le> 1"
  assumes hx_rad: "x = (1 - t) *\<^sub>R v + t *\<^sub>R y"
  assumes h\<epsilon>_pos: "0 < \<epsilon>"
  shows "x \<notin> {z. \<exists>y' s.
      y' \<in> \<Union>(geotop_link K v) - ball y \<epsilon>
        \<and> 0 \<le> s \<and> s \<le> 1
        \<and> z = (1 - s) *\<^sub>R v + s *\<^sub>R y'}"
proof
  assume hx_bad:
    "x \<in> {z. \<exists>y' s.
      y' \<in> \<Union>(geotop_link K v) - ball y \<epsilon>
        \<and> 0 \<le> s \<and> s \<le> 1
        \<and> z = (1 - s) *\<^sub>R v + s *\<^sub>R y'}"
  obtain y' s where hy'_bad: "y' \<in> \<Union>(geotop_link K v) - ball y \<epsilon>"
    and hs_nonneg: "0 \<le> s"
    and hs_le: "s \<le> 1"
    and hx_bad_rad: "x = (1 - s) *\<^sub>R v + s *\<^sub>R y'"
    using hx_bad by (by100 blast)
  have hy'_L: "y' \<in> \<Union>(geotop_link K v)"
    using hy'_bad by (by100 blast)
  have hy'_not_ball: "y' \<notin> ball y \<epsilon>"
    using hy'_bad by (by100 blast)
  have hy_ball: "y \<in> ball y \<epsilon>"
    using h\<epsilon>_pos by (by100 simp)
  show False
  proof (cases "s = 0")
    case True
    have hxv: "x = v"
      using hx_bad_rad True by (by100 simp)
    have "y = v"
      using hx_rad hxv ht_pos by (simp add: algebra_simps)
    have "v \<in> \<Union>(geotop_link K v)"
      using hyL \<open>y = v\<close> by (by100 simp)
    thus False
      using geotop_link_polyhedron_avoids_vertex[of v K] by (by100 blast)
  next
    case False
    have hs_pos: "0 < s"
      using hs_nonneg False by (by100 simp)
    have hrad_eq:
      "(1 - t) *\<^sub>R v + t *\<^sub>R y =
       (1 - s) *\<^sub>R v + s *\<^sub>R y'"
      using hx_rad hx_bad_rad by (by100 simp)
    have "y = y'"
      by (rule geotop_link_radial_endpoint_unique_dev34
          [OF hK hv hyL hy'_L ht_pos ht_le hs_pos hs_le hrad_eq])
    show False
      using hy'_not_ball hy_ball \<open>y = y'\<close> by (by100 simp)
  qed
qed

lemma geotop_radial_endpoint_simplex_local_ball_control_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes hx\<sigma>: "x \<in> \<sigma>"
  assumes hyL: "y \<in> \<Union>(geotop_link K v)"
  assumes ht_pos: "0 < t"
  assumes ht_le: "t \<le> 1"
  assumes hx_rad: "x = (1 - t) *\<^sub>R v + t *\<^sub>R y"
  assumes h\<epsilon>_pos: "0 < \<epsilon>"
  shows "\<exists>r. 0 < r \<and>
      ball x r \<inter> (\<Union>(geotop_star K v) - {v}) \<inter> \<sigma>
        \<subseteq> {z \<in> \<Union>(geotop_star K v) - {v}.
             \<exists>y' t'. y' \<in> \<Union>(geotop_link K v) \<inter> ball y \<epsilon>
               \<and> 0 < t' \<and> t' \<le> 1
               \<and> z = (1 - t') *\<^sub>R v + t' *\<^sub>R y'}"
proof -
  let ?S = "\<Union>(geotop_star K v) - {v}"
  let ?BadCone = "{z. \<exists>y' s.
      y' \<in> \<Union>(geotop_link K v) - ball y \<epsilon>
        \<and> 0 \<le> s \<and> s \<le> 1
        \<and> z = (1 - s) *\<^sub>R v + s *\<^sub>R y'}"
  let ?GoodCone = "{z \<in> ?S.
             \<exists>y' t'. y' \<in> \<Union>(geotop_link K v) \<inter> ball y \<epsilon>
               \<and> 0 < t' \<and> t' \<le> 1
               \<and> z = (1 - t') *\<^sub>R v + t' *\<^sub>R y'}"
  have hBad_closed: "closed ?BadCone"
    by (rule geotop_radial_bad_endpoint_cone_closed_dev34
        [OF hK hv h\<epsilon>_pos])
  have hx_not_Bad: "x \<notin> ?BadCone"
    by (rule geotop_radial_bad_endpoint_cone_avoids_point_dev34
        [OF hK hv hyL ht_pos ht_le hx_rad h\<epsilon>_pos])
  obtain r where hr_pos: "0 < r" and hball_bad: "ball x r \<inter> ?BadCone = {}"
    using geotop_ball_avoids_closed_not_containing_allow_empty_dev34
      [OF hBad_closed hx_not_Bad]
    by (by100 blast)
  have hsub: "ball x r \<inter> ?S \<inter> \<sigma> \<subseteq> ?GoodCone"
  proof
    fix z
    assume hz: "z \<in> ball x r \<inter> ?S \<inter> \<sigma>"
    have hz_ball: "z \<in> ball x r"
      using hz by (by100 blast)
    have hzS: "z \<in> ?S"
      using hz by (by100 blast)
    obtain y' t' where hy'L: "y' \<in> \<Union>(geotop_link K v)"
      and ht'_pos: "0 < t'"
      and ht'_le: "t' \<le> 1"
      and hz_rad: "z = (1 - t') *\<^sub>R v + t' *\<^sub>R y'"
      using geotop_star_punctured_point_radial_to_link_dev34[OF hK hv hzS]
      by (by100 blast)
    have hy'_ball: "y' \<in> ball y \<epsilon>"
    proof (rule ccontr)
      assume hy'_not_ball: "y' \<notin> ball y \<epsilon>"
      have hy'_bad: "y' \<in> \<Union>(geotop_link K v) - ball y \<epsilon>"
        using hy'L hy'_not_ball by (by100 blast)
      have ht'_nonneg: "0 \<le> t'"
        using ht'_pos by (by100 simp)
      have "z \<in> ?BadCone"
        using hy'_bad ht'_nonneg ht'_le hz_rad by (by100 blast)
      have "z \<in> ball x r \<inter> ?BadCone"
        using hz_ball \<open>z \<in> ?BadCone\<close> by (by100 blast)
      show False
        using hball_bad \<open>z \<in> ball x r \<inter> ?BadCone\<close> by (by100 blast)
    qed
    have hy'_good: "y' \<in> \<Union>(geotop_link K v) \<inter> ball y \<epsilon>"
      using hy'L hy'_ball by (by100 blast)
    show "z \<in> ?GoodCone"
      using hzS hy'_good ht'_pos ht'_le hz_rad by (by100 blast)
  qed
  show ?thesis
    using hr_pos hsub by (by100 blast)
qed

lemma geotop_radial_cone_simplex_point_neighborhood_at_member_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hW_open: "W \<in> geotop_euclidean_topology"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes hx\<sigma>: "x \<in> \<sigma>"
  assumes hx:
    "x \<in> {x \<in> \<Union>(geotop_star K v) - {v}.
       \<exists>y t. y \<in> \<Union>(geotop_link K v) \<inter> W \<and> 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
  shows "\<exists>r. 0 < r \<and>
      ball x r \<inter> (\<Union>(geotop_star K v) - {v}) \<inter> \<sigma>
        \<subseteq> {x \<in> \<Union>(geotop_star K v) - {v}.
             \<exists>y t. y \<in> \<Union>(geotop_link K v) \<inter> W \<and> 0 < t \<and> t \<le> 1
                \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
proof -
  let ?S = "\<Union>(geotop_star K v) - {v}"
  let ?A = "{z \<in> ?S.
       \<exists>y t. y \<in> \<Union>(geotop_link K v) \<inter> W \<and> 0 < t \<and> t \<le> 1
          \<and> z = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
  obtain y t where hyLW: "y \<in> \<Union>(geotop_link K v) \<inter> W"
    and ht_pos: "0 < t"
    and ht_le: "t \<le> 1"
    and hx_rad: "x = (1 - t) *\<^sub>R v + t *\<^sub>R y"
    using hx by (by100 blast)
  have hyL: "y \<in> \<Union>(geotop_link K v)"
    using hyLW by (by100 blast)
  have hyW: "y \<in> W"
    using hyLW by (by100 blast)
  have hW_open_HOL: "open W"
    using hW_open
    unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have hW_ball_all: "\<forall>z\<in>W. \<exists>\<epsilon>>0. ball z \<epsilon> \<subseteq> W"
    using hW_open_HOL open_contains_ball[of W] by (by100 simp)
  obtain \<epsilon> where h\<epsilon>_pos: "0 < \<epsilon>" and hballW: "ball y \<epsilon> \<subseteq> W"
    using hW_ball_all hyW by (by100 blast)
  obtain r where hr_pos: "0 < r"
    and hlocal:
      "ball x r \<inter> ?S \<inter> \<sigma>
        \<subseteq> {z \<in> ?S.
             \<exists>y' t'. y' \<in> \<Union>(geotop_link K v) \<inter> ball y \<epsilon>
               \<and> 0 < t' \<and> t' \<le> 1
               \<and> z = (1 - t') *\<^sub>R v + t' *\<^sub>R y'}"
    using geotop_radial_endpoint_simplex_local_ball_control_dev34
      [OF hK hv h\<sigma>K hx\<sigma> hyL ht_pos ht_le hx_rad h\<epsilon>_pos]
    by (by100 blast)
  have hsub: "ball x r \<inter> ?S \<inter> \<sigma> \<subseteq> ?A"
  proof
    fix z
    assume hz: "z \<in> ball x r \<inter> ?S \<inter> \<sigma>"
    have hz_local:
      "z \<in> {z \<in> ?S.
             \<exists>y' t'. y' \<in> \<Union>(geotop_link K v) \<inter> ball y \<epsilon>
               \<and> 0 < t' \<and> t' \<le> 1
               \<and> z = (1 - t') *\<^sub>R v + t' *\<^sub>R y'}"
      using hlocal hz by (by100 blast)
    obtain y' t' where hzS: "z \<in> ?S"
      and hy'_ball: "y' \<in> \<Union>(geotop_link K v) \<inter> ball y \<epsilon>"
      and ht'_pos: "0 < t'"
      and ht'_le: "t' \<le> 1"
      and hz_rad: "z = (1 - t') *\<^sub>R v + t' *\<^sub>R y'"
      using hz_local by (by100 blast)
    have hy'_W: "y' \<in> W"
      using hy'_ball hballW by (by100 blast)
    have hy'_LW: "y' \<in> \<Union>(geotop_link K v) \<inter> W"
      using hy'_ball hy'_W by (by100 blast)
    show "z \<in> ?A"
      using hzS hy'_LW ht'_pos ht'_le hz_rad by (by100 blast)
  qed
  show ?thesis
    using hr_pos hsub by (by100 blast)
qed

lemma geotop_radial_cone_simplex_point_neighborhood_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hW_open: "W \<in> geotop_euclidean_topology"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes hx:
    "x \<in> {x \<in> \<Union>(geotop_star K v) - {v}.
       \<exists>y t. y \<in> \<Union>(geotop_link K v) \<inter> W \<and> 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
  shows "\<exists>r. 0 < r \<and>
      ball x r \<inter> (\<Union>(geotop_star K v) - {v}) \<inter> \<sigma>
        \<subseteq> {x \<in> \<Union>(geotop_star K v) - {v}.
             \<exists>y t. y \<in> \<Union>(geotop_link K v) \<inter> W \<and> 0 < t \<and> t \<le> 1
                \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
proof (cases "x \<in> \<sigma>")
  case True
  show ?thesis
    by (rule geotop_radial_cone_simplex_point_neighborhood_at_member_dev34
        [OF hK hv hW_open h\<sigma>K True hx])
next
  case False
  obtain r where hr_pos: "0 < r" and hdisj: "ball x r \<inter> \<sigma> = {}"
    using geotop_simplex_point_neighborhood_empty_if_notin_dev34[OF hK h\<sigma>K False]
    by (by100 blast)
  have hsub:
      "ball x r \<inter> (\<Union>(geotop_star K v) - {v}) \<inter> \<sigma>
        \<subseteq> {x \<in> \<Union>(geotop_star K v) - {v}.
             \<exists>y t. y \<in> \<Union>(geotop_link K v) \<inter> W \<and> 0 < t \<and> t \<le> 1
                \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
    using hdisj by (by100 blast)
  show ?thesis
    using hr_pos hsub by (by100 blast)
qed

lemma geotop_finite_local_carrier_radial_cone_point_neighborhood_dev34:
  fixes K F :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hW_open: "W \<in> geotop_euclidean_topology"
  assumes hx:
    "x \<in> {x \<in> \<Union>(geotop_star K v) - {v}.
       \<exists>y t. y \<in> \<Union>(geotop_link K v) \<inter> W \<and> 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
  assumes hr0: "0 < r0"
  assumes hF_fin: "finite F"
  assumes hF_sub: "F \<subseteq> K"
  assumes hF_cover: "ball x r0 \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
  shows "\<exists>r. 0 < r \<and>
      ball x r \<inter> (\<Union>(geotop_star K v) - {v})
        \<subseteq> {x \<in> \<Union>(geotop_star K v) - {v}.
             \<exists>y t. y \<in> \<Union>(geotop_link K v) \<inter> W \<and> 0 < t \<and> t \<le> 1
                \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
proof -
  let ?S = "\<Union>(geotop_star K v) - {v}"
  let ?A = "{x \<in> ?S.
       \<exists>y t. y \<in> \<Union>(geotop_link K v) \<inter> W \<and> 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
  have hS_poly: "?S \<subseteq> geotop_polyhedron K"
  proof
    fix z
    assume hzS: "z \<in> ?S"
    obtain \<sigma> where h\<sigma>star: "\<sigma> \<in> geotop_star K v" and hz\<sigma>: "z \<in> \<sigma>"
      using hzS by (by100 blast)
    have hstar_sub: "geotop_star K v \<subseteq> K"
      by (rule geotop_star_subset_complex[OF hK])
    have h\<sigma>K: "\<sigma> \<in> K"
      using hstar_sub h\<sigma>star by (by100 blast)
    show "z \<in> geotop_polyhedron K"
      unfolding geotop_polyhedron_def using h\<sigma>K hz\<sigma> by (by100 blast)
  qed
  have hcoverS: "ball x r0 \<inter> ?S \<subseteq> \<Union>F"
    using hF_cover hS_poly by (by100 blast)
  have hlocal:
    "\<And>C. C \<in> F \<Longrightarrow> \<exists>r. 0 < r \<and> ball x r \<inter> ?S \<inter> C \<subseteq> ?A"
  proof -
    fix C
    assume hC: "C \<in> F"
    have hCK: "C \<in> K"
      using hF_sub hC by (by100 blast)
    show "\<exists>r. 0 < r \<and> ball x r \<inter> ?S \<inter> C \<subseteq> ?A"
      by (rule geotop_radial_cone_simplex_point_neighborhood_dev34
          [OF hK hv hW_open hCK hx])
  qed
  show ?thesis
    by (rule geotop_finite_carrier_local_ball_glue_dev34
        [OF hr0 hF_fin hcoverS hlocal])
qed

lemma geotop_euclidean_open_radial_cone_point_neighborhood_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hW_open: "W \<in> geotop_euclidean_topology"
  assumes hx:
    "x \<in> {x \<in> \<Union>(geotop_star K v) - {v}.
       \<exists>y t. y \<in> \<Union>(geotop_link K v) \<inter> W \<and> 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
  shows "\<exists>r. 0 < r \<and>
      ball x r \<inter> (\<Union>(geotop_star K v) - {v})
        \<subseteq> {x \<in> \<Union>(geotop_star K v) - {v}.
             \<exists>y t. y \<in> \<Union>(geotop_link K v) \<inter> W \<and> 0 < t \<and> t \<le> 1
                \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
proof -
  let ?S = "\<Union>(geotop_star K v) - {v}"
  let ?A = "{x \<in> ?S.
       \<exists>y t. y \<in> \<Union>(geotop_link K v) \<inter> W \<and> 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
  have hxS: "x \<in> ?S"
    using hx by (by100 blast)
  have hx_poly: "x \<in> geotop_polyhedron K"
  proof -
    obtain \<sigma> where h\<sigma>star: "\<sigma> \<in> geotop_star K v" and hx\<sigma>: "x \<in> \<sigma>"
      using hxS by (by100 blast)
    have hstar_sub: "geotop_star K v \<subseteq> K"
      by (rule geotop_star_subset_complex[OF hK])
    have h\<sigma>K: "\<sigma> \<in> K"
      using hstar_sub h\<sigma>star by (by100 blast)
    show ?thesis
      unfolding geotop_polyhedron_def using h\<sigma>K hx\<sigma> by (by100 blast)
  qed
  obtain r0 F where hr0: "0 < r0" and hF_fin: "finite F"
    and hF_sub: "F \<subseteq> K"
    and hF_cover: "ball x r0 \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
    using geotop_complex_point_finite_local_carrier_dev34[OF hK hx_poly]
    by (by100 blast)
  show ?thesis
    by (rule geotop_finite_local_carrier_radial_cone_point_neighborhood_dev34
        [OF hK hv hW_open hx hr0 hF_fin hF_sub hF_cover])
qed

lemma geotop_euclidean_open_radial_cone_open_in_punctured_star_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hW_open: "W \<in> geotop_euclidean_topology"
  shows "{x \<in> \<Union>(geotop_star K v) - {v}.
       \<exists>y t. y \<in> \<Union>(geotop_link K v) \<inter> W \<and> 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}
      \<in> subspace_topology UNIV geotop_euclidean_topology
          (\<Union>(geotop_star K v) - {v})"
proof -
  let ?S = "\<Union>(geotop_star K v) - {v}"
  let ?A = "{x \<in> ?S.
       \<exists>y t. y \<in> \<Union>(geotop_link K v) \<inter> W \<and> 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
  have hA_sub: "?A \<subseteq> ?S"
    by (by100 blast)
  have hlocal:
    "\<And>x. x \<in> ?A \<Longrightarrow> \<exists>r. 0 < r \<and> ball x r \<inter> ?S \<subseteq> ?A"
    by (rule geotop_euclidean_open_radial_cone_point_neighborhood_dev34
        [OF hK hv hW_open])
  show ?thesis
    by (rule geotop_subspace_open_from_euclidean_ball_witness_dev34
        [OF hA_sub hlocal])
qed

lemma geotop_link_open_radial_cone_open_in_punctured_star_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hC_open:
    "C \<in> subspace_topology UNIV geotop_euclidean_topology
       (\<Union>(geotop_link K v))"
  shows "{x \<in> \<Union>(geotop_star K v) - {v}.
       \<exists>y t. y \<in> C \<and> 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}
      \<in> subspace_topology UNIV geotop_euclidean_topology
          (\<Union>(geotop_star K v) - {v})"
proof -
  let ?L = "\<Union>(geotop_link K v)"
  let ?S = "\<Union>(geotop_star K v) - {v}"
  obtain W where hW_open: "W \<in> geotop_euclidean_topology"
      and hC_eq: "C = ?L \<inter> W"
    using hC_open unfolding subspace_topology_def by (by100 blast)
  have hcone_eq:
    "{x \<in> ?S. \<exists>y t. y \<in> C \<and> 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}
     = {x \<in> ?S. \<exists>y t. y \<in> ?L \<inter> W \<and> 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
    using hC_eq by (by100 simp)
  have hopen:
    "{x \<in> ?S. \<exists>y t. y \<in> ?L \<inter> W \<and> 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}
      \<in> subspace_topology UNIV geotop_euclidean_topology ?S"
    by (rule geotop_euclidean_open_radial_cone_open_in_punctured_star_dev34
        [OF hK hv hW_open])
  show ?thesis
    using hcone_eq hopen by (by100 simp)
qed

lemma geotop_punctured_star_radial_endpoint_projection_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "\<exists>\<rho>. top1_continuous_map_on
        (\<Union>(geotop_star K v) - {v})
        (subspace_topology UNIV geotop_euclidean_topology
          (\<Union>(geotop_star K v) - {v}))
        (\<Union>(geotop_link K v))
        (subspace_topology UNIV geotop_euclidean_topology
          (\<Union>(geotop_link K v))) \<rho>
      \<and> (\<forall>x\<in>\<Union>(geotop_star K v) - {v}.
          \<rho> x \<in> \<Union>(geotop_link K v)
          \<and> (\<exists>t. 0 < t \<and> t \<le> 1
              \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R \<rho> x))"
proof -
  let ?S = "\<Union>(geotop_star K v) - {v}"
  let ?L = "\<Union>(geotop_link K v)"
  let ?TS = "subspace_topology UNIV geotop_euclidean_topology ?S"
  let ?TL = "subspace_topology UNIV geotop_euclidean_topology ?L"
  define \<rho> where "\<rho> = (\<lambda>x. SOME y. y \<in> ?L
      \<and> (\<exists>t. 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y))"
  have hradial:
      "\<forall>x\<in>?S. \<rho> x \<in> ?L
        \<and> (\<exists>t. 0 < t \<and> t \<le> 1
            \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R \<rho> x)"
    using geotop_punctured_star_radial_endpoint_choice_property_dev34[OF hK hv]
    unfolding \<rho>_def by (by100 simp)
  have hcont: "top1_continuous_map_on ?S ?TS ?L ?TL \<rho>"
  proof (rule continuous_map_onI)
    show "\<forall>x\<in>?S. \<rho> x \<in> ?L"
      using hradial by (by100 blast)
  next
    show "\<forall>C\<in>?TL. {x \<in> ?S. \<rho> x \<in> C} \<in> ?TS"
    proof
      fix C
      assume hC_open: "C \<in> ?TL"
      have hC_sub: "C \<subseteq> ?L"
        using hC_open unfolding subspace_topology_def by (by100 blast)
      have hpre_eq:
        "{x \<in> ?S. \<rho> x \<in> C}
          = {x \<in> ?S. \<exists>y t. y \<in> C \<and> 0 < t \<and> t \<le> 1
              \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
        using geotop_radial_endpoint_choice_preimage_eq_cone_dev34
          [OF hK hv hC_sub]
        unfolding \<rho>_def by (by100 simp)
      have hcone_open:
        "{x \<in> ?S. \<exists>y t. y \<in> C \<and> 0 < t \<and> t \<le> 1
              \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y} \<in> ?TS"
        by (rule geotop_link_open_radial_cone_open_in_punctured_star_dev34
            [OF hK hv hC_open])
      show "{x \<in> ?S. \<rho> x \<in> C} \<in> ?TS"
        using hpre_eq hcone_open by (by100 simp)
    qed
  qed
  show ?thesis
    using hcont hradial by (intro exI[of _ \<rho>]) (by100 blast)
qed

lemma geotop_radial_cone_over_link_open_in_punctured_star_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hC_open:
    "C \<in> subspace_topology UNIV geotop_euclidean_topology
       (\<Union>(geotop_link K v))"
  shows "{x \<in> \<Union>(geotop_star K v) - {v}.
       \<exists>y t. y \<in> C \<and> 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}
      \<in> subspace_topology UNIV geotop_euclidean_topology
          (\<Union>(geotop_star K v) - {v})"
proof -
  let ?S = "\<Union>(geotop_star K v) - {v}"
  let ?L = "\<Union>(geotop_link K v)"
  let ?TS = "subspace_topology UNIV geotop_euclidean_topology ?S"
  let ?TL = "subspace_topology UNIV geotop_euclidean_topology ?L"
  let ?Cone =
    "{x \<in> ?S. \<exists>y t. y \<in> C \<and> 0 < t \<and> t \<le> 1
       \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
  obtain \<rho> where h\<rho>_cont:
      "top1_continuous_map_on ?S ?TS ?L ?TL \<rho>"
    and h\<rho>_radial:
      "\<forall>x\<in>?S. \<rho> x \<in> ?L \<and> (\<exists>t. 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R \<rho> x)"
    using geotop_punctured_star_radial_endpoint_projection_dev34[OF hK hv]
    by (by100 blast)
  have hpre_open: "{x \<in> ?S. \<rho> x \<in> C} \<in> ?TS"
    by (rule continuous_map_preimage_open[OF h\<rho>_cont hC_open])
  have hC_sub_link: "C \<subseteq> ?L"
    using hC_open unfolding subspace_topology_def by (by100 blast)
  have hCone_eq: "?Cone = {x \<in> ?S. \<rho> x \<in> C}"
  proof
    show "?Cone \<subseteq> {x \<in> ?S. \<rho> x \<in> C}"
    proof
      fix x
      assume hx: "x \<in> ?Cone"
      obtain y t where hxS: "x \<in> ?S"
        and hyC: "y \<in> C"
        and ht_pos: "0 < t"
        and ht_le: "t \<le> 1"
        and hx_rad: "x = (1 - t) *\<^sub>R v + t *\<^sub>R y"
        using hx by (by100 blast)
      have hyL: "y \<in> ?L"
        using hyC hC_sub_link by (by100 blast)
      obtain t' where h\<rho>L: "\<rho> x \<in> ?L"
        and ht'_pos: "0 < t'"
        and ht'_le: "t' \<le> 1"
        and hx\<rho>_rad: "x = (1 - t') *\<^sub>R v + t' *\<^sub>R \<rho> x"
        using h\<rho>_radial hxS by (by100 blast)
      have hrad_eq:
        "(1 - t) *\<^sub>R v + t *\<^sub>R y =
         (1 - t') *\<^sub>R v + t' *\<^sub>R \<rho> x"
        using hx_rad hx\<rho>_rad by (by100 simp)
      have "y = \<rho> x"
        by (rule geotop_link_radial_endpoint_unique_dev34
            [OF hK hv hyL h\<rho>L ht_pos ht_le ht'_pos ht'_le hrad_eq])
      show "x \<in> {x \<in> ?S. \<rho> x \<in> C}"
        using hxS hyC \<open>y = \<rho> x\<close> by (by100 blast)
    qed
  next
    show "{x \<in> ?S. \<rho> x \<in> C} \<subseteq> ?Cone"
    proof
      fix x
      assume hx: "x \<in> {x \<in> ?S. \<rho> x \<in> C}"
      have hxS: "x \<in> ?S"
        using hx by (by100 blast)
      have h\<rho>C: "\<rho> x \<in> C"
        using hx by (by100 blast)
      obtain t where ht_pos: "0 < t"
        and ht_le: "t \<le> 1"
        and hx_rad: "x = (1 - t) *\<^sub>R v + t *\<^sub>R \<rho> x"
        using h\<rho>_radial hxS by (by100 blast)
      show "x \<in> ?Cone"
        using hxS h\<rho>C ht_pos ht_le hx_rad by (by100 blast)
    qed
  qed
  show ?thesis
    using hpre_open hCone_eq by (by100 simp)
qed

lemma geotop_disconnected_link_separates_punctured_star_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hnot_connected:
    "\<not> top1_connected_on (\<Union>(geotop_link K v))
       (subspace_topology UNIV geotop_euclidean_topology
         (\<Union>(geotop_link K v)))"
  shows "\<not> top1_connected_on (\<Union>(geotop_star K v) - {v})
       (subspace_topology UNIV geotop_euclidean_topology
         (\<Union>(geotop_star K v) - {v}))"
proof -
  \<comment> \<open>Book Lemma 5 geometry: every point of the punctured star lies on
      a radial segment from the vertex to a point of the link.\<close>
  have hradial:
    "\<forall>x\<in>\<Union>(geotop_star K v) - {v}.
       \<exists>y t. y \<in> \<Union>(geotop_link K v)
          \<and> 0 < t \<and> t \<le> 1
          \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y"
    by (intro ballI)
      (rule geotop_star_punctured_point_radial_to_link_dev34[OF hK hv])
  \<comment> \<open>Book Lemma 5 separation input: if the link is disconnected, split it
      into two nonempty disjoint open parts.\<close>
  obtain A B where hlink_sep:
    "top1_is_separation_on (\<Union>(geotop_link K v))
       (subspace_topology UNIV geotop_euclidean_topology
         (\<Union>(geotop_link K v))) A B"
    using top1_not_connected_geotop_subspace_obtain_separation_dev34[OF hnot_connected]
    by (by100 blast)
  have hA_open:
    "A \<in> subspace_topology UNIV geotop_euclidean_topology
       (\<Union>(geotop_link K v))"
    using hlink_sep unfolding top1_is_separation_on_def by (by100 simp)
  have hB_open:
    "B \<in> subspace_topology UNIV geotop_euclidean_topology
       (\<Union>(geotop_link K v))"
    using hlink_sep unfolding top1_is_separation_on_def by (by100 simp)
  have hA_nonempty: "A \<noteq> {}"
    using hlink_sep unfolding top1_is_separation_on_def by (by100 simp)
  have hB_nonempty: "B \<noteq> {}"
    using hlink_sep unfolding top1_is_separation_on_def by (by100 simp)
  have hAB_disjoint: "A \<inter> B = {}"
    using hlink_sep unfolding top1_is_separation_on_def by (by100 simp)
  have hAB_cover: "A \<union> B = \<Union>(geotop_link K v)"
    using hlink_sep unfolding top1_is_separation_on_def by (by100 simp)
  let ?S = "\<Union>(geotop_star K v) - {v}"
  let ?SA =
    "{x \<in> ?S. \<exists>y t. y \<in> A \<and> 0 < t \<and> t \<le> 1
       \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
  let ?SB =
    "{x \<in> ?S. \<exists>y t. y \<in> B \<and> 0 < t \<and> t \<le> 1
       \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y}"
  have hA_sub_link: "A \<subseteq> \<Union>(geotop_link K v)"
    using hA_open unfolding subspace_topology_def by (by100 blast)
  have hB_sub_link: "B \<subseteq> \<Union>(geotop_link K v)"
    using hB_open unfolding subspace_topology_def by (by100 blast)
  have hSA_nonempty: "?SA \<noteq> {}"
  proof -
    obtain y where hyA: "y \<in> A"
      using hA_nonempty by (by100 blast)
    have hyS: "y \<in> ?S"
      using hyA hA_sub_link geotop_link_polyhedron_subset_punctured_star_polyhedron
      by (by100 blast)
    have "y \<in> ?SA"
      using hyA hyS by (by100 force)
    show ?thesis
      using \<open>y \<in> ?SA\<close> by (by100 blast)
  qed
  have hSB_nonempty: "?SB \<noteq> {}"
  proof -
    obtain y where hyB: "y \<in> B"
      using hB_nonempty by (by100 blast)
    have hyS: "y \<in> ?S"
      using hyB hB_sub_link geotop_link_polyhedron_subset_punctured_star_polyhedron
      by (by100 blast)
    have "y \<in> ?SB"
      using hyB hyS by (by100 force)
    show ?thesis
      using \<open>y \<in> ?SB\<close> by (by100 blast)
  qed
  have hS_cover: "?SA \<union> ?SB = ?S"
  proof
    show "?SA \<union> ?SB \<subseteq> ?S"
      by (by100 blast)
  next
    show "?S \<subseteq> ?SA \<union> ?SB"
    proof
      fix x assume hxS: "x \<in> ?S"
      obtain y t where hy_link: "y \<in> \<Union>(geotop_link K v)"
        and ht_pos: "0 < t" and ht_le: "t \<le> 1"
        and hx_radial: "x = (1 - t) *\<^sub>R v + t *\<^sub>R y"
        using hradial hxS by (by100 blast)
      have "y \<in> A \<or> y \<in> B"
        using hAB_cover hy_link by (by100 blast)
      thus "x \<in> ?SA \<union> ?SB"
        using hxS ht_pos ht_le hx_radial by (by100 blast)
    qed
  qed
  \<comment> \<open>The remaining book step is to transport a separation of the link along
      these radial segments to a separation of the punctured star.\<close>
  have hSA_open_geom:
    "?SA \<in> subspace_topology UNIV geotop_euclidean_topology ?S"
    by (rule geotop_radial_cone_over_link_open_in_punctured_star_dev34
        [OF hK hv hA_open])
  have hSB_open_geom:
    "?SB \<in> subspace_topology UNIV geotop_euclidean_topology ?S"
    by (rule geotop_radial_cone_over_link_open_in_punctured_star_dev34
        [OF hK hv hB_open])
  have hSA_SB_disjoint_geom: "?SA \<inter> ?SB = {}"
  proof
    show "?SA \<inter> ?SB \<subseteq> {}"
    proof
      fix x assume hx: "x \<in> ?SA \<inter> ?SB"
      obtain yA tA where hyA: "yA \<in> A"
        and htA_pos: "0 < tA" and htA_le: "tA \<le> 1"
        and hxA: "x = (1 - tA) *\<^sub>R v + tA *\<^sub>R yA"
        using hx by (by100 blast)
      obtain yB tB where hyB: "yB \<in> B"
        and htB_pos: "0 < tB" and htB_le: "tB \<le> 1"
        and hxB: "x = (1 - tB) *\<^sub>R v + tB *\<^sub>R yB"
        using hx by (by100 blast)
      have hyA_link: "yA \<in> \<Union>(geotop_link K v)"
        using hyA hA_sub_link by (by100 blast)
      have hyB_link: "yB \<in> \<Union>(geotop_link K v)"
        using hyB hB_sub_link by (by100 blast)
      have hrad_eq:
        "(1 - tA) *\<^sub>R v + tA *\<^sub>R yA =
         (1 - tB) *\<^sub>R v + tB *\<^sub>R yB"
        using hxA hxB by (by100 simp)
      have hy_eq: "yA = yB"
        by (rule geotop_link_radial_endpoint_unique_dev34
            [OF hK hv hyA_link hyB_link htA_pos htA_le htB_pos htB_le hrad_eq])
      have "yA \<in> A \<inter> B"
        using hyA hyB hy_eq by (by100 blast)
      thus "x \<in> {}"
        using hAB_disjoint by (by100 blast)
    qed
  qed (by100 blast)
  have hcone_sep:
    "top1_is_separation_on ?S
       (subspace_topology UNIV geotop_euclidean_topology ?S) ?SA ?SB"
    unfolding top1_is_separation_on_def
    using hSA_open_geom hSB_open_geom hSA_nonempty hSB_nonempty
      hSA_SB_disjoint_geom hS_cover
    by (by100 blast)
  have hSA_open_top:
    "?SA \<in> subspace_topology UNIV geotop_euclidean_topology ?S"
    using hcone_sep unfolding top1_is_separation_on_def by (by100 simp)
  have hSB_open_top:
    "?SB \<in> subspace_topology UNIV geotop_euclidean_topology ?S"
    using hcone_sep unfolding top1_is_separation_on_def by (by100 simp)
  have hSA_SB_disjoint: "?SA \<inter> ?SB = {}"
    using hcone_sep unfolding top1_is_separation_on_def by (by100 simp)
  show ?thesis
    by (rule top1_open_cover_separation_imp_not_connected_dev34
        [OF hSA_open_top hSB_open_top hSA_nonempty hSB_nonempty
            hSA_SB_disjoint hS_cover])
qed

lemma geotop_connected_punctured_neighborhood_cannot_cross_separation_dev34:
  fixes S N A B :: "(real^2) set"
  assumes hsep:
    "top1_is_separation_on S
       (subspace_topology UNIV geotop_euclidean_topology S) A B"
  assumes hNsub: "N - {p} \<subseteq> S"
  assumes hNconn:
    "top1_connected_on (N - {p})
       (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
  assumes hNA: "(N - {p}) \<inter> A \<noteq> {}"
  assumes hNB: "(N - {p}) \<inter> B \<noteq> {}"
  shows False
proof -
  let ?T = "subspace_topology UNIV geotop_euclidean_topology S"
  let ?Y = "N - {p}"
  have htop_UNIV: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
    unfolding geotop_euclidean_topology_eq_open_sets
    by (rule top1_open_sets_is_topology_on_UNIV)
  have htopS: "is_topology_on S ?T"
    by (rule subspace_topology_is_topology_on[OF htop_UNIV subset_UNIV])
  have hsub_eq:
    "subspace_topology S ?T ?Y =
     subspace_topology UNIV geotop_euclidean_topology ?Y"
    by (rule subspace_topology_trans[OF hNsub])
  have hconnS:
    "top1_connected_on ?Y (subspace_topology S ?T ?Y)"
    using hNconn hsub_eq by (by100 simp)
  have hside: "?Y \<inter> B = {} \<or> ?Y \<inter> A = {}"
    by (rule Lemma_23_2_disjoint[OF htopS hsep hNsub hconnS])
  show False
    using hside hNA hNB by (by100 blast)
qed

lemma geotop_link_radial_segment_in_star_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hy: "y \<in> \<Union>(geotop_link K v)"
  assumes ht0: "0 \<le> t"
  assumes ht1: "t \<le> 1"
  shows "(1 - t) *\<^sub>R v + t *\<^sub>R y \<in> \<Union>(geotop_star K v)"
proof -
  obtain \<tau> where h\<tau>L: "\<tau> \<in> geotop_link K v" and hy\<tau>: "y \<in> \<tau>"
    using hy by (by100 blast)
  have h\<tau>star: "\<tau> \<in> geotop_star K v"
    using h\<tau>L unfolding geotop_link_def by (by100 blast)
  have hv_not_\<tau>: "v \<notin> \<tau>"
    using h\<tau>L unfolding geotop_link_def by (by100 blast)
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K" and hv\<sigma>: "v \<in> \<sigma>"
      and h\<tau>\<sigma>: "geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>"
    using h\<tau>star unfolding geotop_star_def by (by100 blast)
  have h\<tau>_ne_\<sigma>: "\<tau> \<noteq> \<sigma>"
    using hv\<sigma> hv_not_\<tau> by (by100 blast)
  have hface: "geotop_is_face \<tau> \<sigma>"
    using h\<tau>\<sigma> h\<tau>_ne_\<sigma> by (by100 blast)
  have h\<tau>sub\<sigma>: "\<tau> \<subseteq> \<sigma>"
    by (rule geotop_is_face_imp_subset[OF hface])
  have hy\<sigma>: "y \<in> \<sigma>"
    using hy\<tau> h\<tau>sub\<sigma> by (by100 blast)
  have hKsimplex: "\<forall>\<rho>\<in>K. geotop_is_simplex \<rho>"
    by (rule geotop_is_complex_simplex[OF hK])
  have h\<sigma>simplex: "geotop_is_simplex \<sigma>"
    using hKsimplex h\<sigma>K by (by100 blast)
  have h\<sigma>conv: "convex \<sigma>"
    by (rule GeoTopBase0.geotop_simplex_is_convex[OF h\<sigma>simplex])
  have ht0': "0 \<le> 1 - t"
    using ht1 by (by100 simp)
  have hsum: "(1 - t) + t = 1"
    by (by100 simp)
  have hz\<sigma>: "(1 - t) *\<^sub>R v + t *\<^sub>R y \<in> \<sigma>"
    using h\<sigma>conv hv\<sigma> hy\<sigma> ht0 ht0' hsum unfolding convex_def
    by (by100 blast)
  have h\<sigma>star: "\<sigma> \<in> geotop_star K v"
    unfolding geotop_star_def using h\<sigma>K hv\<sigma> by (by100 blast)
  show ?thesis
    using hz\<sigma> h\<sigma>star by (by100 blast)
qed

lemma geotop_link_point_ne_vertex_dev34:
  assumes hy: "y \<in> \<Union>(geotop_link K v)"
  shows "y \<noteq> v"
proof -
  have "y \<in> \<Union>(geotop_star K v) - {v}"
    using hy geotop_link_polyhedron_subset_punctured_star_polyhedron
    by (by100 blast)
  show ?thesis
    using \<open>y \<in> \<Union>(geotop_star K v) - {v}\<close> by (by100 blast)
qed

lemma geotop_radial_point_ne_vertex_dev34:
  fixes v y :: "real^2"
  assumes hy: "y \<noteq> v"
  assumes ht: "0 < t"
  shows "(1 - t) *\<^sub>R v + t *\<^sub>R y \<noteq> v"
proof
  assume h: "(1 - t) *\<^sub>R v + t *\<^sub>R y = v"
  have heq:
    "(1 - t) *\<^sub>R v + t *\<^sub>R y =
     (1 - 1) *\<^sub>R v + 1 *\<^sub>R v"
    using h by (by100 simp)
  have "v - v = (t / 1) *\<^sub>R (y - v)"
    by (rule geotop_radial_equal_imp_same_ray_dev34[OF ht _ heq])
      (by100 simp)
  then have "t *\<^sub>R (y - v) = 0"
    by (by100 simp)
  then have "y - v = 0"
    using ht by (by100 simp)
  then show False
    using hy by (by100 simp)
qed

lemma geotop_link_radial_tail_in_punctured_star_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hy: "y \<in> \<Union>(geotop_link K v)"
  assumes ht0: "0 < t"
  assumes ht1: "t \<le> 1"
  shows "(1 - t) *\<^sub>R v + t *\<^sub>R y \<in> \<Union>(geotop_star K v) - {v}"
proof -
  have ht_nonneg: "0 \<le> t"
    using ht0 by (by100 simp)
  have hstar: "(1 - t) *\<^sub>R v + t *\<^sub>R y \<in> \<Union>(geotop_star K v)"
    by (rule geotop_link_radial_segment_in_star_dev34[OF hK hy ht_nonneg ht1])
  have hy_ne: "y \<noteq> v"
    by (rule geotop_link_point_ne_vertex_dev34[OF hy])
  have hne: "(1 - t) *\<^sub>R v + t *\<^sub>R y \<noteq> v"
    by (rule geotop_radial_point_ne_vertex_dev34[OF hy_ne ht0])
  show ?thesis
    using hstar hne by (by100 blast)
qed

lemma geotop_punctured_star_separation_side_meets_vertex_neighborhood_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hsep:
    "top1_is_separation_on (\<Union>(geotop_star K v) - {v})
       (subspace_topology UNIV geotop_euclidean_topology
         (\<Union>(geotop_star K v) - {v})) A B"
  assumes ha: "a \<in> A"
  assumes hU:
    "U \<in> subspace_topology UNIV geotop_euclidean_topology
       (geotop_polyhedron K)"
  assumes hvU: "v \<in> U"
  shows "(U - {v}) \<inter> A \<noteq> {}"
proof -
  let ?S = "\<Union>(geotop_star K v) - {v}"
  have hAopen:
    "A \<in> subspace_topology UNIV geotop_euclidean_topology ?S"
    using hsep unfolding top1_is_separation_on_def by (by100 simp)
  have hA_subS: "A \<subseteq> ?S"
    using hAopen unfolding subspace_topology_def by (by100 blast)
  have haS: "a \<in> ?S"
    using ha hA_subS by (by100 blast)
  obtain y s where hy: "y \<in> \<Union>(geotop_link K v)"
    and hs0: "0 < s"
    and hs1: "s \<le> 1"
    and ha_rad: "a = (1 - s) *\<^sub>R v + s *\<^sub>R y"
    using geotop_star_punctured_point_radial_to_link_dev34[OF hK hv haS]
    by (by100 blast)
  obtain W where hWopen: "W \<in> geotop_euclidean_topology"
    and hUeq: "U = geotop_polyhedron K \<inter> W"
    using hU unfolding subspace_topology_def by (by100 blast)
  have hvW: "v \<in> W"
    using hvU hUeq by (by100 blast)
  obtain \<delta> where h\<delta>pos: "\<delta> > 0"
    and hballW: "ball v \<delta> \<subseteq> W"
  proof -
    have "open W"
      using hWopen
      unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    then have hballs: "\<forall>x\<in>W. \<exists>\<epsilon>>0. ball x \<epsilon> \<subseteq> W"
      unfolding open_contains_ball by (by100 simp)
    obtain \<delta> where "\<delta> > 0" and "ball v \<delta> \<subseteq> W"
      using hballs hvW by (by100 blast)
    then show ?thesis
      by (rule that)
  qed
  have hy_ne: "y \<noteq> v"
    by (rule geotop_link_point_ne_vertex_dev34[OF hy])
  obtain q where hq_seg: "q \<in> closed_segment v y"
    and hq_ne: "q \<noteq> v"
    and hq_ball: "q \<in> ball v \<delta>"
  proof -
    obtain q where hq: "q \<in> (closed_segment v y - {v}) \<inter> ball v \<delta>"
      using nondegenerate_segment_meets_ball[OF hy_ne h\<delta>pos] by (by100 blast)
    have "q \<in> closed_segment v y"
      using hq by (by100 blast)
    have "q \<noteq> v"
      using hq by (by100 blast)
    have "q \<in> ball v \<delta>"
      using hq by (by100 blast)
    show ?thesis
      by (rule that[OF \<open>q \<in> closed_segment v y\<close> \<open>q \<noteq> v\<close> \<open>q \<in> ball v \<delta>\<close>])
  qed
  obtain r where hr0: "0 \<le> r"
    and hr1: "r \<le> 1"
    and hq_rad: "q = (1 - r) *\<^sub>R v + r *\<^sub>R y"
    using hq_seg unfolding closed_segment_def by (by100 blast)
  have hrpos: "0 < r"
  proof (rule ccontr)
    assume "\<not> 0 < r"
    then have "r = 0"
      using hr0 by (by100 linarith)
    then have "q = v"
      using hq_rad by (by100 simp)
    show False
      using hq_ne \<open>q = v\<close> by (by100 blast)
  qed
  have hqS: "q \<in> ?S"
  proof -
    have "(1 - r) *\<^sub>R v + r *\<^sub>R y \<in> ?S"
      by (rule geotop_link_radial_tail_in_punctured_star_dev34[OF hK hy hrpos hr1])
    show ?thesis
      using hq_rad \<open>(1 - r) *\<^sub>R v + r *\<^sub>R y \<in> ?S\<close> by (by100 simp)
  qed
  have hqU: "q \<in> U - {v}"
  proof -
    have hq_star: "q \<in> \<Union>(geotop_star K v)"
      using hqS by (by100 blast)
    have hqM: "q \<in> geotop_polyhedron K"
      using hq_star geotop_star_polyhedron_subset_polyhedron[OF hK] by (by100 blast)
    have hqW: "q \<in> W"
      using hq_ball hballW by (by100 blast)
    show ?thesis
      using hUeq hqM hqW hq_ne by (by100 blast)
  qed
  have hseg_subS: "closed_segment q a \<subseteq> ?S"
  proof
    fix z
    assume hzseg: "z \<in> closed_segment q a"
    obtain l where hl0: "0 \<le> l" and hl1: "l \<le> 1"
      and hz: "z = (1 - l) *\<^sub>R q + l *\<^sub>R a"
      using hzseg unfolding closed_segment_def by (by100 blast)
    define u where "u = (1 - l) * r + l * s"
    have hu0: "0 < u"
    proof (cases "l = 1")
      case True
      show ?thesis
        unfolding u_def using True hs0 by (by100 simp)
    next
      case False
      have h1l_pos: "0 < 1 - l"
        using hl1 False by (by100 linarith)
      have hleft_pos: "0 < (1 - l) * r"
        by (rule mult_pos_pos[OF h1l_pos hrpos])
      have hright_nonneg: "0 \<le> l * s"
        using hl0 hs0 by (by100 simp)
      show ?thesis
        unfolding u_def using hleft_pos hright_nonneg by (by100 linarith)
    qed
    have hu1: "u \<le> 1"
    proof -
      have h1l_nonneg: "0 \<le> 1 - l"
        using hl1 by (by100 linarith)
      have hleft_le: "(1 - l) * r \<le> (1 - l) * 1"
        by (rule mult_left_mono[OF hr1 h1l_nonneg])
      have hright_le: "l * s \<le> l * 1"
        by (rule mult_left_mono[OF hs1 hl0])
      have hsum: "(1 - l) * 1 + l * 1 = 1"
        by (by100 simp)
      show ?thesis
        unfolding u_def using hleft_le hright_le hsum by (by100 linarith)
    qed
    have hz_rad: "z = (1 - u) *\<^sub>R v + u *\<^sub>R y"
      unfolding u_def using hz hq_rad ha_rad by (simp add: algebra_simps)
    have "(1 - u) *\<^sub>R v + u *\<^sub>R y \<in> ?S"
      by (rule geotop_link_radial_tail_in_punctured_star_dev34[OF hK hy hu0 hu1])
    show "z \<in> ?S"
      using hz_rad \<open>(1 - u) *\<^sub>R v + u *\<^sub>R y \<in> ?S\<close> by (by100 simp)
  qed
  have hseg_conn:
    "top1_connected_on (closed_segment q a)
       (subspace_topology UNIV geotop_euclidean_topology (closed_segment q a))"
  proof -
    have "connected (closed_segment q a)"
      by (rule convex_connected[OF convex_closed_segment])
    show ?thesis
      using \<open>connected (closed_segment q a)\<close>
        top1_connected_on_geotop_iff_connected[of "closed_segment q a"]
      by (by100 simp)
  qed
  have hseg_meets_A: "closed_segment q a \<inter> A \<noteq> {}"
  proof -
    have "a \<in> closed_segment q a"
    proof -
      have "0 \<le> (1::real) \<and> (1::real) \<le> 1
          \<and> a = (1 - 1) *\<^sub>R q + 1 *\<^sub>R a"
        by (by100 simp)
      show ?thesis
        unfolding closed_segment_def using \<open>0 \<le> (1::real) \<and> (1::real) \<le> 1
          \<and> a = (1 - 1) *\<^sub>R q + 1 *\<^sub>R a\<close>
        by (by100 blast)
    qed
    show ?thesis
      using \<open>a \<in> closed_segment q a\<close> ha by (by100 blast)
  qed
  have hq_in_seg: "q \<in> closed_segment q a"
  proof -
    have "0 \<le> (0::real) \<and> (0::real) \<le> 1
        \<and> q = (1 - 0) *\<^sub>R q + 0 *\<^sub>R a"
      by (by100 simp)
    show ?thesis
      unfolding closed_segment_def using \<open>0 \<le> (0::real) \<and> (0::real) \<le> 1
        \<and> q = (1 - 0) *\<^sub>R q + 0 *\<^sub>R a\<close>
      by (by100 blast)
  qed
  have hqA: "q \<in> A"
  proof -
    have htop_UNIV: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
      unfolding geotop_euclidean_topology_eq_open_sets
      by (rule top1_open_sets_is_topology_on_UNIV)
    have htopS:
      "is_topology_on ?S
        (subspace_topology UNIV geotop_euclidean_topology ?S)"
      by (rule subspace_topology_is_topology_on[OF htop_UNIV subset_UNIV])
    have hsub_eq:
      "subspace_topology ?S
        (subspace_topology UNIV geotop_euclidean_topology ?S)
        (closed_segment q a)
       = subspace_topology UNIV geotop_euclidean_topology (closed_segment q a)"
      by (rule subspace_topology_trans[OF hseg_subS])
    have hseg_connS:
      "top1_connected_on (closed_segment q a)
        (subspace_topology ?S
          (subspace_topology UNIV geotop_euclidean_topology ?S)
          (closed_segment q a))"
      using hseg_conn hsub_eq by (by100 simp)
    have hside:
      "closed_segment q a \<inter> B = {} \<or> closed_segment q a \<inter> A = {}"
      by (rule Lemma_23_2_disjoint[OF htopS hsep hseg_subS hseg_connS])
    have hcover: "A \<union> B = ?S"
      using hsep unfolding top1_is_separation_on_def by (by100 simp)
    have hqAB: "q \<in> A \<or> q \<in> B"
      using hcover hqS by (by100 blast)
    have hq_notB: "q \<notin> B"
    proof
      assume hqB: "q \<in> B"
      have hseg_meets_B: "closed_segment q a \<inter> B \<noteq> {}"
        using hq_in_seg hqB by (by100 blast)
      show False
        using hside hseg_meets_A hseg_meets_B by (by100 blast)
    qed
    show ?thesis
      using hqAB hq_notB by (by100 blast)
  qed
  show ?thesis
    using hqU hqA by (by100 blast)
qed

lemma geotop_2_manifold_open_subset_connected_punctured_neighborhood_dev34:
  fixes M A :: "(real^2) set" and p :: "real^2"
  assumes hM: "geotop_n_manifold_on M (\<lambda>x y. norm (x - y)) 2"
  assumes hAopen: "A \<in> subspace_topology UNIV geotop_euclidean_topology M"
  assumes hAsub: "A \<subseteq> M"
  assumes hpA: "p \<in> A"
  shows "\<exists>N. p \<in> N \<and> N \<subseteq> A
      \<and> N \<in> subspace_topology UNIV geotop_euclidean_topology A
      \<and> N \<in> subspace_topology UNIV geotop_euclidean_topology M
      \<and> top1_connected_on (N - {p})
          (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
proof -
  let ?d = "\<lambda>x y. norm (x - y)"
  let ?TM = "top1_metric_topology_on M ?d"
  let ?GM = "subspace_topology UNIV geotop_euclidean_topology M"
  have hpM: "p \<in> M"
    using hpA hAsub by (by100 blast)
  obtain U f where hUopen: "openin_on M ?TM U" and hpU: "p \<in> U"
      and hhomeo_metric: "top1_homeomorphism_on U (subspace_topology M ?TM U)
          (UNIV::(real^2) set) geotop_euclidean_topology f"
    using hM hpM unfolding geotop_n_manifold_on_def by (by100 blast)
  have hUsubM: "U \<subseteq> M"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hUmemTM: "U \<in> ?TM"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hTM_eq: "?TM = ?GM"
    by (rule top1_norm_metric_topology_on_eq_geotop_subspace_R2_dev34)
  have hUmemG: "U \<in> ?GM"
    using hUmemTM hTM_eq by (by100 simp)
  have hsource_eq: "subspace_topology M ?TM U =
      subspace_topology UNIV geotop_euclidean_topology U"
  proof -
    have htrans: "subspace_topology M ?GM U =
        subspace_topology UNIV geotop_euclidean_topology U"
      by (rule subspace_topology_trans[OF hUsubM])
    show ?thesis
      using hTM_eq htrans by (by100 simp)
  qed
  have hhomeo_geo: "top1_homeomorphism_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
    using hhomeo_metric hsource_eq by (by100 simp)
  define B where "B = U \<inter> A"
  have hpB: "p \<in> B"
    unfolding B_def using hpU hpA by (by100 blast)
  have hBsubU: "B \<subseteq> U"
    unfolding B_def by (by100 blast)
  have hBopenU: "B \<in> subspace_topology UNIV geotop_euclidean_topology U"
  proof -
    obtain W where hWtop: "W \<in> geotop_euclidean_topology" and hAeq: "A = M \<inter> W"
      using hAopen unfolding subspace_topology_def by (by100 blast)
    have hBeq: "B = U \<inter> W"
      unfolding B_def using hUsubM hAeq by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hWtop hBeq by (by100 blast)
  qed
  have hBopenA: "B \<in> subspace_topology UNIV geotop_euclidean_topology A"
  proof -
    obtain V where hVtop: "V \<in> geotop_euclidean_topology" and hUeq: "U = M \<inter> V"
      using hUmemG unfolding subspace_topology_def by (by100 blast)
    have hBeq: "B = A \<inter> V"
      unfolding B_def using hAsub hUeq by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hVtop hBeq by (by100 blast)
  qed
  obtain N where hpN: "p \<in> N" and hNsubB: "N \<subseteq> B"
      and hNopenB: "N \<in> subspace_topology UNIV geotop_euclidean_topology B"
      and hNconn: "top1_connected_on (N - {p})
          (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
    using geotop_plane_chart_open_subset_connected_punctured_neighborhood
      [OF hhomeo_geo hBopenU hBsubU hpB]
    by (by100 blast)
  have hNsubA: "N \<subseteq> A"
    using hNsubB unfolding B_def by (by100 blast)
  have hNopenA: "N \<in> subspace_topology UNIV geotop_euclidean_topology A"
    by (rule geotop_subspace_open_trans[OF hBopenA hNopenB])
  have hNopenM: "N \<in> subspace_topology UNIV geotop_euclidean_topology M"
    by (rule geotop_subspace_open_trans[OF hAopen hNopenA])
  show ?thesis
    using hpN hNsubA hNopenA hNopenM hNconn by (by100 blast)
qed

lemma geotop_2_manifold_with_boundary_open_subset_connected_punctured_neighborhood_dev34:
  fixes M A :: "(real^2) set" and p :: "real^2"
  assumes hM: "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2"
  assumes hAopen: "A \<in> subspace_topology UNIV geotop_euclidean_topology M"
  assumes hAsub: "A \<subseteq> M"
  assumes hpA: "p \<in> A"
  shows "\<exists>N. p \<in> N \<and> N \<subseteq> A
      \<and> N \<in> subspace_topology UNIV geotop_euclidean_topology A
      \<and> N \<in> subspace_topology UNIV geotop_euclidean_topology M
      \<and> top1_connected_on (N - {p})
          (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
proof -
  let ?d = "\<lambda>x y. norm (x - y)"
  let ?T = "top1_metric_topology_on M ?d"
  let ?GM = "subspace_topology UNIV geotop_euclidean_topology M"
  have hpM: "p \<in> M"
    using hpA hAsub by (by100 blast)
  have hmetric: "top1_metric_on M ?d"
    using hM unfolding geotop_n_manifold_with_boundary_on_def by (by100 blast)
  have htopT: "is_topology_on M ?T"
    by (rule top1_metric_topology_on_is_topology_on[OF hmetric])
  obtain U where hUopen: "openin_on M ?T U" and hpU: "p \<in> U"
      and hcell: "geotop_is_n_cell (closure_on M ?T U)
          (subspace_topology M ?T (closure_on M ?T U)) 2"
    using hM hpM unfolding geotop_n_manifold_with_boundary_on_def by (by100 blast)
  let ?C = "closure_on M ?T U"
  have hUsubM: "U \<subseteq> M"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hUmemT: "U \<in> ?T"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hCsubM: "?C \<subseteq> M"
    by (rule closure_on_subset_carrier[OF htopT hUsubM])
  have hUsubC: "U \<subseteq> ?C"
    by (rule subset_closure_on)
  have hT_eq: "?T = ?GM"
    by (rule top1_norm_metric_topology_on_eq_geotop_subspace_R2_dev34)
  have hTC_eq: "subspace_topology M ?T ?C =
      subspace_topology UNIV geotop_euclidean_topology ?C"
  proof -
    have htrans: "subspace_topology M ?GM ?C =
        subspace_topology UNIV geotop_euclidean_topology ?C"
      by (rule subspace_topology_trans[OF hCsubM])
    show ?thesis
      using hT_eq htrans by (by100 simp)
  qed
  have hcell_geo: "geotop_is_n_cell ?C
      (subspace_topology UNIV geotop_euclidean_topology ?C) 2"
    using hcell hTC_eq by (by100 simp)
  have hUmemG: "U \<in> ?GM"
    using hUmemT hT_eq by (by100 simp)
  define B where "B = U \<inter> A"
  have hpB: "p \<in> B"
    unfolding B_def using hpU hpA by (by100 blast)
  have hBsubC: "B \<subseteq> ?C"
    unfolding B_def using hUsubC by (by100 blast)
  have hBopenM: "B \<in> ?GM"
  proof -
    obtain V where hVtop: "V \<in> geotop_euclidean_topology" and hUeq: "U = M \<inter> V"
      using hUmemG unfolding subspace_topology_def by (by100 blast)
    obtain W where hWtop: "W \<in> geotop_euclidean_topology" and hAeq: "A = M \<inter> W"
      using hAopen unfolding subspace_topology_def by (by100 blast)
    have hVopen: "open V"
      using hVtop unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    have hWopen: "open W"
      using hWtop unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    have hVWtop: "V \<inter> W \<in> geotop_euclidean_topology"
      using open_Int[OF hVopen hWopen]
      unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    have hBeq: "B = M \<inter> (V \<inter> W)"
      unfolding B_def using hUeq hAeq by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hVWtop hBeq by (by100 blast)
  qed
  have hBopenC: "B \<in> subspace_topology UNIV geotop_euclidean_topology ?C"
  proof -
    obtain V where hVtop: "V \<in> geotop_euclidean_topology" and hBeqM: "B = M \<inter> V"
      using hBopenM unfolding subspace_topology_def by (by100 blast)
    have hBeqC: "B = ?C \<inter> V"
      using hBeqM hBsubC hCsubM by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hVtop hBeqC by (by100 blast)
  qed
  have hBopenA: "B \<in> subspace_topology UNIV geotop_euclidean_topology A"
  proof -
    obtain V where hVtop: "V \<in> geotop_euclidean_topology" and hUeq: "U = M \<inter> V"
      using hUmemG unfolding subspace_topology_def by (by100 blast)
    have hBeq: "B = A \<inter> V"
      unfolding B_def using hAsub hUeq by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hVtop hBeq by (by100 blast)
  qed
  obtain N where hpN: "p \<in> N" and hNsubB: "N \<subseteq> B"
      and hNopenB: "N \<in> subspace_topology UNIV geotop_euclidean_topology B"
      and hNconn: "top1_connected_on (N - {p})
          (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
    using geotop_2_cell_open_subset_connected_punctured_neighborhood
      [OF hcell_geo hBopenC hBsubC hpB]
    by (by100 blast)
  have hNsubA: "N \<subseteq> A"
    using hNsubB unfolding B_def by (by100 blast)
  have hNopenA: "N \<in> subspace_topology UNIV geotop_euclidean_topology A"
    by (rule geotop_subspace_open_trans[OF hBopenA hNopenB])
  have hNopenM: "N \<in> subspace_topology UNIV geotop_euclidean_topology M"
    by (rule geotop_subspace_open_trans[OF hAopen hNopenA])
  show ?thesis
    using hpN hNsubA hNopenA hNopenM hNconn by (by100 blast)
qed

lemma geotop_2_manifold_vertex_star_punctured_connected_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hM: "geotop_n_manifold_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "top1_connected_on (\<Union>(geotop_star K v) - {v})
       (subspace_topology UNIV geotop_euclidean_topology
         (\<Union>(geotop_star K v) - {v}))"
proof -
  let ?M = "geotop_polyhedron K"
  let ?S = "\<Union>(geotop_star K v) - {v}"
  let ?TS = "subspace_topology UNIV geotop_euclidean_topology ?S"
  have hnot_not:
    "\<not> \<not> top1_connected_on ?S ?TS"
  proof
    assume hnot_connected: "\<not> top1_connected_on ?S ?TS"
    obtain A B where hsep: "top1_is_separation_on ?S ?TS A B"
      using top1_not_connected_geotop_subspace_obtain_separation_dev34[OF hnot_connected]
      by (by100 blast)
    have hAopen: "A \<in> ?TS"
      using hsep unfolding top1_is_separation_on_def by (by100 simp)
    have hBopen: "B \<in> ?TS"
      using hsep unfolding top1_is_separation_on_def by (by100 simp)
    have hAne: "A \<noteq> {}"
      using hsep unfolding top1_is_separation_on_def by (by100 simp)
    have hBne: "B \<noteq> {}"
      using hsep unfolding top1_is_separation_on_def by (by100 simp)
    have hABdisj: "A \<inter> B = {}"
      using hsep unfolding top1_is_separation_on_def by (by100 simp)
    have hABcover: "A \<union> B = ?S"
      using hsep unfolding top1_is_separation_on_def by (by100 simp)
    obtain a where ha: "a \<in> A"
      using hAne by (by100 blast)
    obtain b where hb: "b \<in> B"
      using hBne by (by100 blast)
    have hBAdisj: "B \<inter> A = {}"
      using hABdisj by (by100 blast)
    have hBAcover: "B \<union> A = ?S"
      using hABcover by (by100 blast)
    have hsep_sym: "top1_is_separation_on ?S ?TS B A"
      unfolding top1_is_separation_on_def
      using hBopen hAopen hBne hAne hBAdisj hBAcover by (by100 simp)
    obtain V where hVopen: "V \<in> subspace_topology UNIV geotop_euclidean_topology ?M"
        and hvV: "v \<in> V"
        and hVsub: "V \<subseteq> \<Union>(geotop_star K v)"
      using geotop_complex_vertex_star_neighborhood_dev34[OF hK hv] by (by100 blast)
    have hVsubM: "V \<subseteq> ?M"
      using hVopen unfolding subspace_topology_def by (by100 blast)
    obtain N where hvN: "v \<in> N" and hNsubV: "N \<subseteq> V"
        and hNopenV: "N \<in> subspace_topology UNIV geotop_euclidean_topology V"
        and hNopenM: "N \<in> subspace_topology UNIV geotop_euclidean_topology ?M"
        and hNconn: "top1_connected_on (N - {v})
            (subspace_topology UNIV geotop_euclidean_topology (N - {v}))"
      using geotop_2_manifold_open_subset_connected_punctured_neighborhood_dev34
        [OF hM hVopen hVsubM hvV]
      by (by100 blast)
    have hNminus_subS: "N - {v} \<subseteq> ?S"
      using hNsubV hVsub by (by100 blast)
    have hNA: "(N - {v}) \<inter> A \<noteq> {}"
      by (rule geotop_punctured_star_separation_side_meets_vertex_neighborhood_dev34
          [OF hK hv hsep ha hNopenM hvN])
    have hNB: "(N - {v}) \<inter> B \<noteq> {}"
      by (rule geotop_punctured_star_separation_side_meets_vertex_neighborhood_dev34
          [OF hK hv hsep_sym hb hNopenM hvN])
    show False
      by (rule geotop_connected_punctured_neighborhood_cannot_cross_separation_dev34
          [OF hsep hNminus_subS hNconn hNA hNB])
  qed
  show ?thesis
    using hnot_not by (by100 blast)
qed

lemma geotop_2_manifold_with_boundary_vertex_star_punctured_connected_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "top1_connected_on (\<Union>(geotop_star K v) - {v})
       (subspace_topology UNIV geotop_euclidean_topology
         (\<Union>(geotop_star K v) - {v}))"
proof -
  let ?M = "geotop_polyhedron K"
  let ?S = "\<Union>(geotop_star K v) - {v}"
  let ?TS = "subspace_topology UNIV geotop_euclidean_topology ?S"
  have hnot_not:
    "\<not> \<not> top1_connected_on ?S ?TS"
  proof
    assume hnot_connected: "\<not> top1_connected_on ?S ?TS"
    obtain A B where hsep: "top1_is_separation_on ?S ?TS A B"
      using top1_not_connected_geotop_subspace_obtain_separation_dev34[OF hnot_connected]
      by (by100 blast)
    have hAopen: "A \<in> ?TS"
      using hsep unfolding top1_is_separation_on_def by (by100 simp)
    have hBopen: "B \<in> ?TS"
      using hsep unfolding top1_is_separation_on_def by (by100 simp)
    have hAne: "A \<noteq> {}"
      using hsep unfolding top1_is_separation_on_def by (by100 simp)
    have hBne: "B \<noteq> {}"
      using hsep unfolding top1_is_separation_on_def by (by100 simp)
    have hABdisj: "A \<inter> B = {}"
      using hsep unfolding top1_is_separation_on_def by (by100 simp)
    have hABcover: "A \<union> B = ?S"
      using hsep unfolding top1_is_separation_on_def by (by100 simp)
    obtain a where ha: "a \<in> A"
      using hAne by (by100 blast)
    obtain b where hb: "b \<in> B"
      using hBne by (by100 blast)
    have hBAdisj: "B \<inter> A = {}"
      using hABdisj by (by100 blast)
    have hBAcover: "B \<union> A = ?S"
      using hABcover by (by100 blast)
    have hsep_sym: "top1_is_separation_on ?S ?TS B A"
      unfolding top1_is_separation_on_def
      using hBopen hAopen hBne hAne hBAdisj hBAcover by (by100 simp)
    obtain V where hVopen: "V \<in> subspace_topology UNIV geotop_euclidean_topology ?M"
        and hvV: "v \<in> V"
        and hVsub: "V \<subseteq> \<Union>(geotop_star K v)"
      using geotop_complex_vertex_star_neighborhood_dev34[OF hK hv] by (by100 blast)
    have hVsubM: "V \<subseteq> ?M"
      using hVopen unfolding subspace_topology_def by (by100 blast)
    obtain N where hvN: "v \<in> N" and hNsubV: "N \<subseteq> V"
        and hNopenV: "N \<in> subspace_topology UNIV geotop_euclidean_topology V"
        and hNopenM: "N \<in> subspace_topology UNIV geotop_euclidean_topology ?M"
        and hNconn: "top1_connected_on (N - {v})
            (subspace_topology UNIV geotop_euclidean_topology (N - {v}))"
      using geotop_2_manifold_with_boundary_open_subset_connected_punctured_neighborhood_dev34
        [OF hM hVopen hVsubM hvV]
      by (by100 blast)
    have hNminus_subS: "N - {v} \<subseteq> ?S"
      using hNsubV hVsub by (by100 blast)
    have hNA: "(N - {v}) \<inter> A \<noteq> {}"
      by (rule geotop_punctured_star_separation_side_meets_vertex_neighborhood_dev34
          [OF hK hv hsep ha hNopenM hvN])
    have hNB: "(N - {v}) \<inter> B \<noteq> {}"
      by (rule geotop_punctured_star_separation_side_meets_vertex_neighborhood_dev34
          [OF hK hv hsep_sym hb hNopenM hvN])
    show False
      by (rule geotop_connected_punctured_neighborhood_cannot_cross_separation_dev34
          [OF hsep hNminus_subS hNconn hNA hNB])
  qed
  show ?thesis
    using hnot_not by (by100 blast)
qed

lemma geotop_2_manifold_link_polyhedron_connected_from_vertex_star_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hM: "geotop_n_manifold_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "top1_connected_on (\<Union>(geotop_link K v))
           (subspace_topology UNIV geotop_euclidean_topology
             (\<Union>(geotop_link K v)))"
proof (rule ccontr)
  assume hnot_connected:
    "\<not> top1_connected_on (\<Union>(geotop_link K v))
       (subspace_topology UNIV geotop_euclidean_topology
         (\<Union>(geotop_link K v)))"
  \<comment> \<open>Moise Lemma 5: if the link is disconnected, then the vertex separates
      the polyhedron of its star.\<close>
  have hstar_separated:
    "\<not> top1_connected_on (\<Union>(geotop_star K v) - {v})
       (subspace_topology UNIV geotop_euclidean_topology
         (\<Union>(geotop_star K v) - {v}))"
    by (rule geotop_disconnected_link_separates_punctured_star_dev34
        [OF hK hv hnot_connected])
  \<comment> \<open>The star of a vertex is a sufficiently small polyhedral neighborhood of
      the vertex in the triangulated surface.\<close>
  have hstar_neighborhood:
    "\<exists>U. U \<in> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)
       \<and> v \<in> U \<and> U \<subseteq> \<Union>(geotop_star K v)"
    by (rule geotop_complex_vertex_star_neighborhood_dev34[OF hK hv])
  \<comment> \<open>A point does not separate a plane chart neighborhood; transported back to
      the star neighborhood this contradicts the separation above.\<close>
  have hstar_not_separated:
    "top1_connected_on (\<Union>(geotop_star K v) - {v})
       (subspace_topology UNIV geotop_euclidean_topology
         (\<Union>(geotop_star K v) - {v}))"
    by (rule geotop_2_manifold_vertex_star_punctured_connected_dev34[OF hK hM hv])
  show False
    using hstar_separated hstar_not_separated by (by100 blast)
qed

lemma geotop_2_manifold_with_boundary_link_polyhedron_connected_from_vertex_star_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hM: "geotop_n_manifold_with_boundary_on
      (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "top1_connected_on (\<Union>(geotop_link K v))
           (subspace_topology UNIV geotop_euclidean_topology
             (\<Union>(geotop_link K v)))"
proof (rule ccontr)
  assume hnot_connected:
    "\<not> top1_connected_on (\<Union>(geotop_link K v))
       (subspace_topology UNIV geotop_euclidean_topology
         (\<Union>(geotop_link K v)))"
  \<comment> \<open>The manifold-with-boundary proof uses the same Lemma 5 argument from
      Moise: disconnected link means the vertex separates its star.\<close>
  have hstar_separated:
    "\<not> top1_connected_on (\<Union>(geotop_star K v) - {v})
       (subspace_topology UNIV geotop_euclidean_topology
         (\<Union>(geotop_star K v) - {v}))"
    by (rule geotop_disconnected_link_separates_punctured_star_dev34
        [OF hK hv hnot_connected])
  \<comment> \<open>The same open-star neighborhood is available in the boundary case.\<close>
  have hstar_neighborhood:
    "\<exists>U. U \<in> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)
       \<and> v \<in> U \<and> U \<subseteq> \<Union>(geotop_star K v)"
    by (rule geotop_complex_vertex_star_neighborhood_dev34[OF hK hv])
  \<comment> \<open>In a half-plane chart, as in a plane chart, deleting one point does not
      disconnect a sufficiently small open neighborhood.\<close>
  have hstar_not_separated:
    "top1_connected_on (\<Union>(geotop_star K v) - {v})
       (subspace_topology UNIV geotop_euclidean_topology
         (\<Union>(geotop_star K v) - {v}))"
    by (rule geotop_2_manifold_with_boundary_vertex_star_punctured_connected_dev34
        [OF hK hM hv])
  show False
    using hstar_separated hstar_not_separated by (by100 blast)
qed

lemma geotop_link_finite_1dim_line_or_polygon_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hshape:
    "geotop_is_broken_line (\<Union>(geotop_link K v))
      \<or> geotop_is_polygon (\<Union>(geotop_link K v))"
  shows "geotop_is_complex (geotop_link K v)
      \<and> geotop_complex_is_1dim (geotop_link K v)
      \<and> finite (geotop_link K v)
      \<and> (geotop_is_broken_line (geotop_polyhedron (geotop_link K v))
          \<or> geotop_is_polygon (geotop_polyhedron (geotop_link K v)))"
proof -
  have hlink_complex: "geotop_is_complex (geotop_link K v)"
    by (rule geotop_link_is_complex[OF hK])
  have hlink_1dim: "geotop_complex_is_1dim (geotop_link K v)"
    by (rule geotop_link_complex_is_1dim_R2[OF hK])
  have hlink_finite: "finite (geotop_link K v)"
    by (rule geotop_link_finite_at_complex_vertex[OF hK hv])
  have hpoly_eq: "geotop_polyhedron (geotop_link K v) = \<Union>(geotop_link K v)"
    unfolding geotop_polyhedron_def by (by100 simp)
  have hshape_poly:
    "geotop_is_broken_line (geotop_polyhedron (geotop_link K v))
      \<or> geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
    using hshape hpoly_eq by (by100 simp)
  show ?thesis
    using hlink_complex hlink_1dim hlink_finite hshape_poly by (by100 blast)
qed

lemma geotop_link_vertices_subset_star_vertices_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_complex_vertices (geotop_link K v)
      \<subseteq> geotop_complex_vertices (geotop_star K v)"
  (**
    Fig. 4.10 sends the old link vertices to the subdivided boundary vertices
    and sends the original star vertex to the new cone vertex.  This records
    the elementary inclusion needed before the eventual vertex-bijection split:
    every vertex of the link complex is already a vertex of the star complex. **)
proof
  fix w
  assume hw: "w \<in> geotop_complex_vertices (geotop_link K v)"
  obtain \<tau> V where h\<tau>L: "\<tau> \<in> geotop_link K v"
    and hV: "geotop_simplex_vertices \<tau> V"
    and hwV: "w \<in> V"
    using hw unfolding geotop_complex_vertices_def by (by100 blast)
  have h\<tau>S: "\<tau> \<in> geotop_star K v"
    using h\<tau>L unfolding geotop_link_def by (by100 blast)
  show "w \<in> geotop_complex_vertices (geotop_star K v)"
    unfolding geotop_complex_vertices_def using h\<tau>S hV hwV by (by100 blast)
qed

lemma geotop_star_vertices_eq_insert_link_vertices_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "geotop_complex_vertices (geotop_star K v)
      = insert v (geotop_complex_vertices (geotop_link K v))"
  (**
    Vertex part of Moise Fig. 4.10: the star is the cone vertex \<open>v\<close>
    together with the vertices already lying in the link.  The later fan
    isomorphism should map exactly these two pieces to the new interior vertex
    and to the subdivided frontier vertices of the standard triangle. **)
proof -
  have hstar_complex: "geotop_is_complex (geotop_star K v)"
    by (rule geotop_star_is_complex[OF hK])
  have hlink_complex: "geotop_is_complex (geotop_link K v)"
    by (rule geotop_link_is_complex[OF hK])
  have hstar_subset:
    "geotop_complex_vertices (geotop_star K v)
      \<subseteq> insert v (geotop_complex_vertices (geotop_link K v))"
  proof
    fix w
    assume hwS: "w \<in> geotop_complex_vertices (geotop_star K v)"
    have hw_single_S: "{w} \<in> geotop_star K v"
      using hwS geotop_complex_vertices_eq_0_simplexes[OF hstar_complex]
      by (by100 simp)
    show "w \<in> insert v (geotop_complex_vertices (geotop_link K v))"
    proof (cases "w = v")
      case True
      show ?thesis using True by (by100 simp)
    next
      case False
      have hw_single_L: "{w} \<in> geotop_link K v"
        using hw_single_S False unfolding geotop_link_def by (by100 blast)
      have hwL: "w \<in> geotop_complex_vertices (geotop_link K v)"
        using hw_single_L geotop_complex_vertices_eq_0_simplexes[OF hlink_complex]
        by (by100 simp)
      show ?thesis using hwL by (by100 simp)
    qed
  qed
  have hinsert_subset:
    "insert v (geotop_complex_vertices (geotop_link K v))
      \<subseteq> geotop_complex_vertices (geotop_star K v)"
  proof
    fix w
    assume hw: "w \<in> insert v (geotop_complex_vertices (geotop_link K v))"
    have hvK_single: "{v} \<in> K"
      using hv geotop_complex_vertices_eq_0_simplexes[OF hK] by (by100 simp)
    have hvS_single: "{v} \<in> geotop_star K v"
      unfolding geotop_star_def using hvK_single by (by100 blast)
    have hvS: "v \<in> geotop_complex_vertices (geotop_star K v)"
      using hvS_single geotop_complex_vertices_eq_0_simplexes[OF hstar_complex]
      by (by100 simp)
    have hlink_subset:
      "geotop_complex_vertices (geotop_link K v)
        \<subseteq> geotop_complex_vertices (geotop_star K v)"
      by (rule geotop_link_vertices_subset_star_vertices_dev34[OF hK])
    show "w \<in> geotop_complex_vertices (geotop_star K v)"
      using hw hvS hlink_subset by (by100 blast)
  qed
  show ?thesis
    using hstar_subset hinsert_subset by (by100 blast)
qed

lemma geotop_link_vertices_avoid_star_vertex_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  shows "v \<notin> geotop_complex_vertices (geotop_link K v)"
  (**
    Completes the vertex partition used in the Fig. 4.10 fan bijection:
    the cone vertex is not one of the old link vertices. **)
proof
  assume hvL: "v \<in> geotop_complex_vertices (geotop_link K v)"
  have hlink_complex: "geotop_is_complex (geotop_link K v)"
    by (rule geotop_link_is_complex[OF hK])
  have hv_single_L: "{v} \<in> geotop_link K v"
    using hvL geotop_complex_vertices_eq_0_simplexes[OF hlink_complex]
    by (by100 simp)
  show False
    using hv_single_L unfolding geotop_link_def by (by100 blast)
qed

lemma geotop_star_vertices_minus_vertex_eq_link_vertices_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "geotop_complex_vertices (geotop_star K v) - {v}
      = geotop_complex_vertices (geotop_link K v)"
  (**
    The old vertices of the star, after deleting the cone vertex, are exactly
    the link vertices.  This is the vertex-domain part of the Fig. 4.10
    simplicial bijection. **)
proof -
  have hstar_vertices:
    "geotop_complex_vertices (geotop_star K v)
      = insert v (geotop_complex_vertices (geotop_link K v))"
    by (rule geotop_star_vertices_eq_insert_link_vertices_dev34[OF hK hv])
  have hv_not_link: "v \<notin> geotop_complex_vertices (geotop_link K v)"
    by (rule geotop_link_vertices_avoid_star_vertex_dev34[OF hK])
  show ?thesis
    using hstar_vertices hv_not_link by (by100 blast)
qed

lemma geotop_star_simplex_vertices_subset_insert_link_vertices_dev34:
  fixes K :: "(real^2) set set" and \<tau> V :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes h\<tau>S: "\<tau> \<in> geotop_star K v"
  assumes hV: "geotop_simplex_vertices \<tau> V"
  shows "V \<subseteq> insert v (geotop_complex_vertices (geotop_link K v))"
  (**
    Simplex-level form of the Fig. 4.10 vertex split.  Every simplex in the
    star is supported on the cone vertex together with old link vertices. **)
proof -
  have hV_star: "V \<subseteq> geotop_complex_vertices (geotop_star K v)"
    unfolding geotop_complex_vertices_def using h\<tau>S hV by (by100 blast)
  have hstar_vertices:
    "geotop_complex_vertices (geotop_star K v)
      = insert v (geotop_complex_vertices (geotop_link K v))"
    by (rule geotop_star_vertices_eq_insert_link_vertices_dev34[OF hK hv])
  show ?thesis
    using hV_star hstar_vertices by (by100 blast)
qed

lemma geotop_star_simplex_vertices_minus_vertex_subset_link_vertices_dev34:
  fixes K :: "(real^2) set set" and \<tau> V :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes h\<tau>S: "\<tau> \<in> geotop_star K v"
  assumes hV: "geotop_simplex_vertices \<tau> V"
  shows "V - {v} \<subseteq> geotop_complex_vertices (geotop_link K v)"
  (**
    Removing the cone vertex from any star simplex leaves only link vertices;
    this is the vertex-support statement used by the fan subdivision map. **)
proof -
  have hV_insert: "V \<subseteq> insert v (geotop_complex_vertices (geotop_link K v))"
    by (rule geotop_star_simplex_vertices_subset_insert_link_vertices_dev34
        [OF hK hv h\<tau>S hV])
  show ?thesis
    using hV_insert by (by100 blast)
qed

lemma geotop_link_simplex_in_star_dev34:
  fixes K :: "(real^2) set set" and \<tau> :: "(real^2) set"
  assumes h\<tau>L: "\<tau> \<in> geotop_link K v"
  shows "\<tau> \<in> geotop_star K v"
  (**
    Direct half of the simplex split underlying Fig. 4.10: the old link
    simplexes are simplexes of the star. **)
  using h\<tau>L unfolding geotop_link_def by (by100 blast)

lemma geotop_star_simplex_not_containing_vertex_in_link_dev34:
  fixes K :: "(real^2) set set" and \<tau> :: "(real^2) set"
  assumes h\<tau>S: "\<tau> \<in> geotop_star K v"
  assumes hv_not: "v \<notin> \<tau>"
  shows "\<tau> \<in> geotop_link K v"
  (**
    Converse half used when the fan map checks a simplex not containing the
    cone vertex: it is exactly a simplex of the link. **)
  unfolding geotop_link_def using h\<tau>S hv_not by (by100 blast)

lemma geotop_star_simplex_opposite_face_in_link_dev34:
  fixes K :: "(real^2) set set" and \<tau> V :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<tau>S: "\<tau> \<in> geotop_star K v"
  assumes hV: "geotop_simplex_vertices \<tau> V"
  assumes hvV: "v \<in> V"
  assumes hW_ne: "V - {v} \<noteq> {}"
  shows "geotop_convex_hull (V - {v}) \<in> geotop_link K v"
  (**
    Cone-simplex form of Fig. 4.10: a star simplex that contains the cone
    vertex has its opposite face in the old link. **)
proof -
  have hstar_sub: "geotop_star K v \<subseteq> K"
    by (rule geotop_star_subset_complex[OF hK])
  have h\<tau>K: "\<tau> \<in> K"
    using hstar_sub h\<tau>S by (by100 blast)
  show ?thesis
    by (rule geotop_simplex_opposite_face_in_link_dev34
        [OF hK h\<tau>K hV hvV hW_ne])
qed

lemma geotop_simplex_vertices_minus_vertex_empty_singleton_dev34:
  fixes \<tau> V :: "(real^2) set"
  assumes hV: "geotop_simplex_vertices \<tau> V"
  assumes hvV: "v \<in> V"
  assumes hW_empty: "V - {v} = {}"
  shows "\<tau> = {v}"
  (**
    Degenerate cone case for Fig. 4.10: if a simplex containing the cone vertex
    has no old vertices, it is the cone vertex itself. **)
proof -
  have hV_eq: "V = {v}"
    using hvV hW_empty by (by100 blast)
  have h\<tau>_hull: "\<tau> = geotop_convex_hull V"
    using hV unfolding geotop_simplex_vertices_def by (by100 blast)
  have hsingleton_hull: "geotop_convex_hull {v} = {v}"
    using geotop_convex_hull_eq_HOL[of "{v}"] by (by100 simp)
  show ?thesis
    using h\<tau>_hull hV_eq hsingleton_hull by (by100 simp)
qed

lemma geotop_star_simplex_cone_case_dev34:
  fixes K :: "(real^2) set set" and \<tau> V :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<tau>S: "\<tau> \<in> geotop_star K v"
  assumes hV: "geotop_simplex_vertices \<tau> V"
  assumes hvV: "v \<in> V"
  shows "\<tau> = {v} \<or> geotop_convex_hull (V - {v}) \<in> geotop_link K v"
  (**
    Fig. 4.10 cone case for a simplex of the star: either it is the cone
    vertex, or its face opposite the cone vertex is an old link simplex. **)
proof (cases "V - {v} = {}")
  case True
  have hsingleton: "\<tau> = {v}"
    by (rule geotop_simplex_vertices_minus_vertex_empty_singleton_dev34
        [OF hV hvV True])
  show ?thesis
    using hsingleton by (by100 blast)
next
  case False
  have hopposite: "geotop_convex_hull (V - {v}) \<in> geotop_link K v"
    by (rule geotop_star_simplex_opposite_face_in_link_dev34
        [OF hK h\<tau>S hV hvV False])
  show ?thesis
    using hopposite by (by100 blast)
qed

lemma geotop_star_simplex_link_or_cone_case_dev34:
  fixes K :: "(real^2) set set" and \<tau> V :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes h\<tau>S: "\<tau> \<in> geotop_star K v"
  assumes hV: "geotop_simplex_vertices \<tau> V"
  shows "\<tau> \<in> geotop_link K v
      \<or> \<tau> = {v}
      \<or> geotop_convex_hull (V - {v}) \<in> geotop_link K v"
  (**
    Complete simplex dichotomy for the Fig. 4.10 fan map: every star simplex is
    either an old link simplex, the cone vertex, or a cone simplex over an old
    link face. **)
proof -
  have hstar_sub: "geotop_star K v \<subseteq> K"
    by (rule geotop_star_subset_complex[OF hK])
  have h\<tau>K: "\<tau> \<in> K"
    using hstar_sub h\<tau>S by (by100 blast)
  have hvK: "{v} \<in> K"
    using hv geotop_complex_vertices_eq_0_simplexes[OF hK] by (by100 simp)
  show ?thesis
  proof (cases "v \<in> \<tau>")
    case False
    have hlink: "\<tau> \<in> geotop_link K v"
      by (rule geotop_star_simplex_not_containing_vertex_in_link_dev34
          [OF h\<tau>S False])
    show ?thesis
      using hlink by (by100 blast)
  next
    case True
    obtain V' where hV': "geotop_simplex_vertices \<tau> V'"
      and hvV': "v \<in> V'"
      using geotop_complex_singleton_point_is_simplex_vertex[OF hK hvK h\<tau>K True]
      by (by100 blast)
    have hVeq: "V' = V"
      by (rule geotop_simplex_vertices_unique[OF hV' hV])
    have hvV: "v \<in> V"
      using hvV' hVeq by (by100 simp)
    have hcone:
        "\<tau> = {v}
          \<or> geotop_convex_hull (V - {v}) \<in> geotop_link K v"
      by (rule geotop_star_simplex_cone_case_dev34[OF hK h\<tau>S hV hvV])
    show ?thesis
      using hcone by (by100 blast)
  qed
qed

lemma geotop_link_vertex_set_cone_simplex_in_star_dev34:
  fixes K :: "(real^2) set set" and W :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hW_fin: "finite W"
  assumes hW_ne: "W \<noteq> {}"
  assumes hW_sub: "W \<subseteq> geotop_complex_vertices (geotop_link K v)"
  assumes hW_link: "geotop_convex_hull W \<in> geotop_link K v"
  shows "geotop_convex_hull (insert v W) \<in> geotop_star K v"
  (**
    Fig. 4.10 cone direction: an old link simplex with vertex set \<open>W\<close>
    becomes a star simplex after adjoining the cone vertex \<open>v\<close>. **)
proof -
  let ?\<tau> = "geotop_convex_hull W"
  have hlink_complex: "geotop_is_complex (geotop_link K v)"
    by (rule geotop_link_is_complex[OF hK])
  have hW_vertices: "geotop_simplex_vertices ?\<tau> W"
    by (rule geotop_V_subK_convhullK_is_simplex_vertices
        [OF hlink_complex hW_fin hW_ne hW_sub hW_link])
  have h\<tau>star: "?\<tau> \<in> geotop_star K v"
    using hW_link unfolding geotop_link_def by (by100 blast)
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
    and hv\<sigma>: "v \<in> \<sigma>"
    and h\<tau>\<sigma>_case: "geotop_is_face ?\<tau> \<sigma> \<or> ?\<tau> = \<sigma>"
    using h\<tau>star unfolding geotop_star_def by (by100 blast)
  have hv_not_\<tau>: "v \<notin> ?\<tau>"
    using hW_link unfolding geotop_link_def by (by100 blast)
  have h\<tau>\<sigma>: "geotop_is_face ?\<tau> \<sigma>"
  proof (cases "geotop_is_face ?\<tau> \<sigma>")
    case True
    show ?thesis
      using True by (by100 blast)
  next
    case False
    have "?\<tau> = \<sigma>"
      using h\<tau>\<sigma>_case False by (by100 blast)
    thus ?thesis
      using hv\<sigma> hv_not_\<tau> by (by100 blast)
  qed
  obtain V\<^sub>\<sigma> W\<^sub>\<tau> where hV\<sigma>: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>"
    and hW\<tau>_ne: "W\<^sub>\<tau> \<noteq> {}"
    and hW\<tau>_sub: "W\<^sub>\<tau> \<subseteq> V\<^sub>\<sigma>"
    and h\<tau>eq: "?\<tau> = geotop_convex_hull W\<^sub>\<tau>"
    and hW\<tau>_vertices: "geotop_simplex_vertices ?\<tau> W\<^sub>\<tau>"
    by (rule geotop_face_witness_simplex_vertices[OF h\<tau>\<sigma>])
  have hW\<tau>_eq: "W\<^sub>\<tau> = W"
    by (rule geotop_simplex_vertices_unique[OF hW\<tau>_vertices hW_vertices])
  have hW_sub_V\<sigma>: "W \<subseteq> V\<^sub>\<sigma>"
    using hW\<tau>_sub hW\<tau>_eq by (by100 simp)
  have hvK: "{v} \<in> K"
    using hv geotop_complex_vertices_eq_0_simplexes[OF hK] by (by100 simp)
  obtain V\<^sub>v where hVv: "geotop_simplex_vertices \<sigma> V\<^sub>v"
    and hvVv: "v \<in> V\<^sub>v"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hvK h\<sigma>K hv\<sigma>]
    by (by100 blast)
  have hVv_eq: "V\<^sub>v = V\<^sub>\<sigma>"
    by (rule geotop_simplex_vertices_unique[OF hVv hV\<sigma>])
  have hvV\<sigma>: "v \<in> V\<^sub>\<sigma>"
    using hvVv hVv_eq by (by100 simp)
  have hinsert_sub: "insert v W \<subseteq> V\<^sub>\<sigma>"
    using hvV\<sigma> hW_sub_V\<sigma> by (by100 blast)
  have hinsert_ne: "insert v W \<noteq> {}"
    by (by100 simp)
  have hcone_face: "geotop_is_face (geotop_convex_hull (insert v W)) \<sigma>"
    by (rule geotop_is_face_of_subset[OF hV\<sigma> hinsert_ne hinsert_sub])
  show ?thesis
    unfolding geotop_star_def using h\<sigma>K hv\<sigma> hcone_face by (by100 blast)
qed

lemma geotop_star_convex_hull_vertex_set_cases_dev34:
  fixes K :: "(real^2) set set" and V :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hV_fin: "finite V"
  assumes hV_sub: "V \<subseteq> geotop_complex_vertices (geotop_star K v)"
  shows "geotop_convex_hull V \<in> geotop_star K v
      \<longleftrightarrow> V = {v}
        \<or> (v \<notin> V \<and> geotop_convex_hull V \<in> geotop_link K v)
        \<or> (v \<in> V \<and> V - {v} \<noteq> {}
            \<and> geotop_convex_hull (V - {v}) \<in> geotop_link K v)"
  (**
    Vertex-set form of Moise Fig. 4.10: every star simplex is either the cone
    vertex, an old link simplex, or the cone over an old link simplex; and
    each of those three cases gives a simplex of the star. **)
proof
  show "geotop_convex_hull V \<in> geotop_star K v \<Longrightarrow>
      V = {v}
        \<or> (v \<notin> V \<and> geotop_convex_hull V \<in> geotop_link K v)
        \<or> (v \<in> V \<and> V - {v} \<noteq> {}
            \<and> geotop_convex_hull (V - {v}) \<in> geotop_link K v)"
  proof -
    assume hVstar: "geotop_convex_hull V \<in> geotop_star K v"
    let ?\<tau> = "geotop_convex_hull V"
    have hstar_complex: "geotop_is_complex (geotop_star K v)"
      by (rule geotop_star_is_complex[OF hK])
    have hV_ne: "V \<noteq> {}"
    proof
      assume hV_empty: "V = {}"
      have "?\<tau> = {}"
        using hV_empty geotop_convex_hull_eq_HOL[of V] by (by100 simp)
      moreover have "?\<tau> \<noteq> {}"
        by (rule geotop_complex_simplex_nonempty[OF hstar_complex hVstar])
      ultimately show False
        by (by100 blast)
    qed
    have hV_vertices: "geotop_simplex_vertices ?\<tau> V"
      by (rule geotop_V_subK_convhullK_is_simplex_vertices
          [OF hstar_complex hV_fin hV_ne hV_sub hVstar])
    show ?thesis
    proof (cases "v \<in> V")
      case False
      have hvK: "{v} \<in> K"
        using hv geotop_complex_vertices_eq_0_simplexes[OF hK] by (by100 simp)
      have hvStar: "{v} \<in> geotop_star K v"
        unfolding geotop_star_def using hvK by (by100 blast)
      have hv_not_\<tau>: "v \<notin> ?\<tau>"
      proof
        assume hv\<tau>: "v \<in> ?\<tau>"
        obtain V' where hV': "geotop_simplex_vertices ?\<tau> V'"
          and hvV': "v \<in> V'"
          using geotop_complex_singleton_point_is_simplex_vertex
            [OF hstar_complex hvStar hVstar hv\<tau>]
          by (by100 blast)
        have "V' = V"
          by (rule geotop_simplex_vertices_unique[OF hV' hV_vertices])
        thus False
          using hvV' False by (by100 blast)
      qed
      have hlink: "?\<tau> \<in> geotop_link K v"
        by (rule geotop_star_simplex_not_containing_vertex_in_link_dev34
            [OF hVstar hv_not_\<tau>])
      show ?thesis
        using False hlink by (by100 blast)
    next
      case True
      have hcone:
          "?\<tau> = {v}
            \<or> geotop_convex_hull (V - {v}) \<in> geotop_link K v"
        by (rule geotop_star_simplex_cone_case_dev34
            [OF hK hVstar hV_vertices True])
      show ?thesis
      proof (cases "?\<tau> = {v}")
        case True
        have hV_single: "geotop_simplex_vertices {v} V"
          using hV_vertices True by (by100 simp)
        have "V = {v}"
          by (rule geotop_singleton_simplex_vertices[OF hV_single])
        show ?thesis
          using \<open>V = {v}\<close> by (by100 blast)
      next
        case False
        have hW_link: "geotop_convex_hull (V - {v}) \<in> geotop_link K v"
          using hcone False by (by100 blast)
        have hlink_complex: "geotop_is_complex (geotop_link K v)"
          by (rule geotop_link_is_complex[OF hK])
        have hW_ne: "V - {v} \<noteq> {}"
        proof
          assume hW_empty: "V - {v} = {}"
          have "geotop_convex_hull (V - {v}) = {}"
            using hW_empty geotop_convex_hull_eq_HOL[of "V - {v}"]
            by (by100 simp)
          moreover have "geotop_convex_hull (V - {v}) \<noteq> {}"
            by (rule geotop_complex_simplex_nonempty[OF hlink_complex hW_link])
          ultimately show False
            by (by100 blast)
        qed
        show ?thesis
          using True hW_ne hW_link by (by100 blast)
      qed
    qed
  qed
  show "V = {v}
        \<or> (v \<notin> V \<and> geotop_convex_hull V \<in> geotop_link K v)
        \<or> (v \<in> V \<and> V - {v} \<noteq> {}
            \<and> geotop_convex_hull (V - {v}) \<in> geotop_link K v)
      \<Longrightarrow> geotop_convex_hull V \<in> geotop_star K v"
  proof -
    assume hcases:
      "V = {v}
        \<or> (v \<notin> V \<and> geotop_convex_hull V \<in> geotop_link K v)
        \<or> (v \<in> V \<and> V - {v} \<noteq> {}
            \<and> geotop_convex_hull (V - {v}) \<in> geotop_link K v)"
    show ?thesis
    proof (cases "V = {v}")
      case True
      have hvK: "{v} \<in> K"
        using hv geotop_complex_vertices_eq_0_simplexes[OF hK] by (by100 simp)
      have hvStar: "{v} \<in> geotop_star K v"
        unfolding geotop_star_def using hvK by (by100 blast)
      have "geotop_convex_hull V = {v}"
        using True geotop_convex_hull_eq_HOL[of "{v}"] by (by100 simp)
      show ?thesis
        using hvStar \<open>geotop_convex_hull V = {v}\<close> by (by100 simp)
    next
      case False
      note hV_not_single = False
      show ?thesis
      proof (cases "v \<notin> V \<and> geotop_convex_hull V \<in> geotop_link K v")
        case True
        show ?thesis
          using True unfolding geotop_link_def by (by100 blast)
      next
        case False
        note hnot_link_case = False
        have hthird:
          "v \<in> V \<and> V - {v} \<noteq> {}
            \<and> geotop_convex_hull (V - {v}) \<in> geotop_link K v"
        proof -
          from hcases show ?thesis
          proof
            assume hfirst: "V = {v}"
            show ?thesis
              using hV_not_single hfirst by (by100 blast)
          next
            assume hrest:
              "(v \<notin> V \<and> geotop_convex_hull V \<in> geotop_link K v)
              \<or> (v \<in> V \<and> V - {v} \<noteq> {}
                  \<and> geotop_convex_hull (V - {v}) \<in> geotop_link K v)"
            from hrest show ?thesis
            proof
              assume hlink_case:
                "v \<notin> V \<and> geotop_convex_hull V \<in> geotop_link K v"
              show ?thesis
                using hnot_link_case hlink_case by (by100 blast)
            next
              assume hcone_case:
                "v \<in> V \<and> V - {v} \<noteq> {}
                  \<and> geotop_convex_hull (V - {v}) \<in> geotop_link K v"
              show ?thesis
                using hcone_case by (by100 blast)
            qed
          qed
        qed
        have hvin: "v \<in> V"
          using hthird by (by100 blast)
        have hW_ne: "V - {v} \<noteq> {}"
          using hthird by (by100 blast)
        have hW_link: "geotop_convex_hull (V - {v}) \<in> geotop_link K v"
          using hthird by (by100 blast)
        have hW_fin: "finite (V - {v})"
          using hV_fin by (by100 simp)
        have hstar_minus:
          "geotop_complex_vertices (geotop_star K v) - {v}
            = geotop_complex_vertices (geotop_link K v)"
          by (rule geotop_star_vertices_minus_vertex_eq_link_vertices_dev34
              [OF hK hv])
        have hW_sub: "V - {v} \<subseteq> geotop_complex_vertices (geotop_link K v)"
          using hV_sub hstar_minus by (by100 blast)
        have hcone: "geotop_convex_hull (insert v (V - {v}))
            \<in> geotop_star K v"
          by (rule geotop_link_vertex_set_cone_simplex_in_star_dev34
              [OF hK hv hW_fin hW_ne hW_sub hW_link])
        have "V = insert v (V - {v})"
          using hvin by (by100 blast)
        show ?thesis
          using hcone \<open>V = insert v (V - {v})\<close> by (by100 simp)
      qed
    qed
  qed
qed

lemma geotop_star_cone_map_image_without_vertex_dev34:
  fixes V :: "(real^2) set" and v c :: "real^2"
    and \<psi> :: "real^2 \<Rightarrow> real^2"
  defines "\<phi> \<equiv> (\<lambda>x. if x = v then c else \<psi> x)"
  assumes hv_not: "v \<notin> V"
  shows "\<phi> ` V = \<psi> ` V"
  (**
    Fig. 4.10 map bookkeeping: away from the cone vertex, the extended star
    vertex map is just the old link-boundary map. **)
proof -
  show ?thesis
  proof
    show "\<phi> ` V \<subseteq> \<psi> ` V"
    proof
      fix y assume hy: "y \<in> \<phi> ` V"
      obtain x where hxV: "x \<in> V" and hy_eq: "y = \<phi> x"
        using hy by (by100 blast)
      have hx_ne: "x \<noteq> v"
        using hxV hv_not by (by100 blast)
      have "y = \<psi> x"
        using hy_eq hx_ne unfolding \<phi>_def by (by100 simp)
      show "y \<in> \<psi> ` V"
        using hxV \<open>y = \<psi> x\<close> by (by100 blast)
    qed
    show "\<psi> ` V \<subseteq> \<phi> ` V"
    proof
      fix y assume hy: "y \<in> \<psi> ` V"
      obtain x where hxV: "x \<in> V" and hy_eq: "y = \<psi> x"
        using hy by (by100 blast)
      have hx_ne: "x \<noteq> v"
        using hxV hv_not by (by100 blast)
      have "y = \<phi> x"
        using hy_eq hx_ne unfolding \<phi>_def by (by100 simp)
      show "y \<in> \<phi> ` V"
        using hxV \<open>y = \<phi> x\<close> by (by100 blast)
    qed
  qed
qed

lemma geotop_star_cone_map_image_with_vertex_dev34:
  fixes V :: "(real^2) set" and v c :: "real^2"
    and \<psi> :: "real^2 \<Rightarrow> real^2"
  defines "\<phi> \<equiv> (\<lambda>x. if x = v then c else \<psi> x)"
  assumes hv_in: "v \<in> V"
  shows "\<phi> ` V = insert c (\<psi> ` (V - {v}))"
  (**
    Fig. 4.10 map bookkeeping: a star vertex set containing \<open>v\<close> maps to
    the new cone vertex together with the image of the old opposite face. **)
proof -
  show ?thesis
  proof
    show "\<phi> ` V \<subseteq> insert c (\<psi> ` (V - {v}))"
    proof
      fix y assume hy: "y \<in> \<phi> ` V"
      obtain x where hxV: "x \<in> V" and hy_eq: "y = \<phi> x"
        using hy by (by100 blast)
      show "y \<in> insert c (\<psi> ` (V - {v}))"
      proof (cases "x = v")
        case True
        have "y = c"
          using hy_eq True unfolding \<phi>_def by (by100 simp)
        show ?thesis
          using \<open>y = c\<close> by (by100 simp)
      next
        case False
        have hxW: "x \<in> V - {v}"
          using hxV False by (by100 blast)
        have "y = \<psi> x"
          using hy_eq False unfolding \<phi>_def by (by100 simp)
        show ?thesis
          using hxW \<open>y = \<psi> x\<close> by (by100 blast)
      qed
    qed
    show "insert c (\<psi> ` (V - {v})) \<subseteq> \<phi> ` V"
    proof
      fix y assume hy: "y \<in> insert c (\<psi> ` (V - {v}))"
      show "y \<in> \<phi> ` V"
      proof (cases "y = c")
        case True
        have "\<phi> v = c"
          unfolding \<phi>_def by (by100 simp)
        show ?thesis
          using hv_in True \<open>\<phi> v = c\<close> by (by100 blast)
      next
        case False
        have "y \<in> \<psi> ` (V - {v})"
          using hy False by (by100 blast)
        obtain x where hxW: "x \<in> V - {v}" and hy_eq: "y = \<psi> x"
          using \<open>y \<in> \<psi> ` (V - {v})\<close> by (by100 blast)
        have hxV: "x \<in> V"
          using hxW by (by100 blast)
        have hx_ne: "x \<noteq> v"
          using hxW by (by100 blast)
        have "y = \<phi> x"
          using hy_eq hx_ne unfolding \<phi>_def by (by100 simp)
        show ?thesis
          using hxV \<open>y = \<phi> x\<close> by (by100 blast)
      qed
    qed
  qed
qed

lemma geotop_star_fan_simplex_iff_from_link_and_cone_target_cases_dev34:
  fixes K L' :: "(real^2) set set" and v c :: "real^2"
    and \<psi> :: "real^2 \<Rightarrow> real^2"
  defines "\<phi> \<equiv> (\<lambda>x. if x = v then c else \<psi> x)"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hstar_vertices_finite:
    "finite (geotop_complex_vertices (geotop_star K v))"
  assumes hlink_target:
    "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
  assumes hcone_vertex_target:
    "geotop_convex_hull {c} \<in> L'"
  assumes hcone_target:
    "\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L')"
  shows "\<forall>V. V \<subseteq> geotop_complex_vertices (geotop_star K v) \<longrightarrow>
        (geotop_convex_hull V \<in> geotop_star K v
          \<longleftrightarrow> geotop_convex_hull (\<phi> ` V) \<in> L')"
  (**
    Fig. 4.10 simplex-membership packaging: once the target fan has exactly
    the old boundary simplexes and exactly the cones on those boundary
    simplexes, the extended vertex map preserves and reflects membership in
    the star complex. **)
proof
  fix V
  show "V \<subseteq> geotop_complex_vertices (geotop_star K v) \<longrightarrow>
        (geotop_convex_hull V \<in> geotop_star K v
          \<longleftrightarrow> geotop_convex_hull (\<phi> ` V) \<in> L')"
  proof
    assume hV_sub: "V \<subseteq> geotop_complex_vertices (geotop_star K v)"
    let ?LV = "geotop_complex_vertices (geotop_link K v)"
    have hV_fin: "finite V"
      by (rule finite_subset[OF hV_sub hstar_vertices_finite])
    have hstar_cases:
      "geotop_convex_hull V \<in> geotop_star K v
        \<longleftrightarrow> V = {v}
          \<or> (v \<notin> V \<and> geotop_convex_hull V \<in> geotop_link K v)
          \<or> (v \<in> V \<and> V - {v} \<noteq> {}
              \<and> geotop_convex_hull (V - {v}) \<in> geotop_link K v)"
      by (rule geotop_star_convex_hull_vertex_set_cases_dev34
          [OF hK hv hV_fin hV_sub])
    show "geotop_convex_hull V \<in> geotop_star K v
          \<longleftrightarrow> geotop_convex_hull (\<phi> ` V) \<in> L'"
    proof (cases "V = {v}")
      case True
      have hsource: "geotop_convex_hull V \<in> geotop_star K v"
        using hstar_cases True by (by100 blast)
      have h\<phi>V: "\<phi> ` V = {c}"
      proof -
        have hvin: "v \<in> V"
          using True by (by100 simp)
        have h\<phi>V_insert_raw:
          "(\<lambda>x. if x = v then c else \<psi> x) ` V
            = insert c (\<psi> ` (V - {v}))"
          by (rule geotop_star_cone_map_image_with_vertex_dev34[OF hvin])
        have h\<phi>V_insert: "\<phi> ` V = insert c (\<psi> ` (V - {v}))"
          using h\<phi>V_insert_raw \<phi>_def by (by100 simp)
        show ?thesis
          using h\<phi>V_insert True by (by100 simp)
      qed
      have htarget: "geotop_convex_hull (\<phi> ` V) \<in> L'"
        using hcone_vertex_target h\<phi>V by (by100 simp)
      show ?thesis
        using hsource htarget by (by100 blast)
    next
      case False
      show ?thesis
      proof (cases "v \<in> V")
        case False
        have hV_LV: "V \<subseteq> ?LV"
        proof -
          have "V \<subseteq> geotop_complex_vertices (geotop_star K v) - {v}"
            using hV_sub False by (by100 blast)
          also have "\<dots> = ?LV"
            by (rule geotop_star_vertices_minus_vertex_eq_link_vertices_dev34
                [OF hK hv])
          finally show ?thesis .
        qed
        have hsource_link:
          "geotop_convex_hull V \<in> geotop_star K v
            \<longleftrightarrow> geotop_convex_hull V \<in> geotop_link K v"
          using hstar_cases False by (by100 blast)
        have h\<phi>V_raw:
          "(\<lambda>x. if x = v then c else \<psi> x) ` V = \<psi> ` V"
          by (rule geotop_star_cone_map_image_without_vertex_dev34[OF False])
        have h\<phi>V: "\<phi> ` V = \<psi> ` V"
          using h\<phi>V_raw \<phi>_def by (by100 simp)
        have htarget_link:
          "geotop_convex_hull V \<in> geotop_link K v
            \<longleftrightarrow> geotop_convex_hull (\<phi> ` V) \<in> L'"
          using hlink_target hV_LV h\<phi>V by (by100 simp)
        show ?thesis
          using hsource_link htarget_link by (by100 blast)
      next
        case True
        let ?W = "V - {v}"
        have hW_ne: "?W \<noteq> {}"
          using True False by (by100 blast)
        have hW_fin: "finite ?W"
          using hV_fin by (by100 simp)
        have hW_LV: "?W \<subseteq> ?LV"
        proof -
          have "?W \<subseteq> geotop_complex_vertices (geotop_star K v) - {v}"
            using hV_sub by (by100 blast)
          also have "\<dots> = ?LV"
            by (rule geotop_star_vertices_minus_vertex_eq_link_vertices_dev34
                [OF hK hv])
          finally show ?thesis .
        qed
        have hsource_cone:
          "geotop_convex_hull V \<in> geotop_star K v
            \<longleftrightarrow> geotop_convex_hull ?W \<in> geotop_link K v"
          using hstar_cases True False hW_ne by (by100 blast)
        have h\<phi>V_raw:
          "(\<lambda>x. if x = v then c else \<psi> x) ` V
            = insert c (\<psi> ` ?W)"
          by (rule geotop_star_cone_map_image_with_vertex_dev34[OF True])
        have h\<phi>V: "\<phi> ` V = insert c (\<psi> ` ?W)"
          using h\<phi>V_raw \<phi>_def by (by100 simp)
        have htarget_cone:
          "geotop_convex_hull ?W \<in> geotop_link K v
            \<longleftrightarrow> geotop_convex_hull (\<phi> ` V) \<in> L'"
          using hcone_target hW_fin hW_ne hW_LV h\<phi>V by (by100 simp)
        show ?thesis
          using hsource_cone htarget_cone by (by100 blast)
      qed
    qed
  qed
qed

lemma geotop_star_cone_vertex_map_bij_dev34:
  fixes K :: "(real^2) set set" and B :: "(real^2) set"
    and v c :: "real^2"
    and \<psi> :: "real^2 \<Rightarrow> real^2"
  defines "\<phi> \<equiv> (\<lambda>x. if x = v then c else \<psi> x)"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes h\<psi>: "bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B"
  assumes hcB: "c \<notin> B"
  shows "bij_betw \<phi> (geotop_complex_vertices (geotop_star K v)) (insert c B)"
  (**
    Fig. 4.10 vertex bookkeeping: after ordering the link vertices against the
    subdivided frontier vertices, extend the correspondence by sending the old
    vertex \<open>v\<close> to the new cone vertex \<open>c\<close>. **)
proof -
  let ?LV = "geotop_complex_vertices (geotop_link K v)"
  let ?SV = "geotop_complex_vertices (geotop_star K v)"
  have hstar: "?SV = insert v ?LV"
    by (rule geotop_star_vertices_eq_insert_link_vertices_dev34[OF hK hv])
  have hv_not_LV: "v \<notin> ?LV"
    by (rule geotop_link_vertices_avoid_star_vertex_dev34[OF hK])
  have h\<psi>inj: "inj_on \<psi> ?LV"
    using h\<psi> unfolding bij_betw_def by (by100 blast)
  have h\<psi>img: "\<psi> ` ?LV = B"
    using h\<psi> unfolding bij_betw_def by (by100 blast)
  have h\<phi>v: "\<phi> v = c"
    unfolding \<phi>_def by (by100 simp)
  have h\<phi>link: "\<forall>x\<in>?LV. \<phi> x = \<psi> x"
    unfolding \<phi>_def using hv_not_LV by (by100 simp)
  have h\<phi>link_img: "\<phi> ` ?LV = B"
  proof -
    have "\<phi> ` ?LV = \<psi> ` ?LV"
      using h\<phi>link by (by100 force)
    thus ?thesis
      using h\<psi>img by (by100 simp)
  qed
  have h\<phi>img: "\<phi> ` ?SV = insert c B"
    using hstar h\<phi>v h\<phi>link_img by (by100 simp)
  have h\<phi>inj_insert: "inj_on \<phi> (insert v ?LV)"
  proof (rule inj_onI)
    fix x y
    assume hx: "x \<in> insert v ?LV"
    assume hy: "y \<in> insert v ?LV"
    assume hxy: "\<phi> x = \<phi> y"
    show "x = y"
    proof (cases "x = v")
      case True
      show ?thesis
      proof (cases "y = v")
        case True
        show ?thesis
          using \<open>x = v\<close> True by (by100 simp)
      next
        case False
        have hyLV: "y \<in> ?LV"
          using hy False by (by100 blast)
        have h\<phi>yB: "\<phi> y \<in> B"
          using h\<phi>link_img hyLV by (by100 blast)
        have "c \<in> B"
          using hxy \<open>x = v\<close> h\<phi>v h\<phi>yB by (by100 simp)
        thus ?thesis
          using hcB by (by100 blast)
      qed
    next
      case False
      have hxLV: "x \<in> ?LV"
        using hx False by (by100 blast)
      show ?thesis
      proof (cases "y = v")
        case True
        have h\<phi>xB: "\<phi> x \<in> B"
          using h\<phi>link_img hxLV by (by100 blast)
        have "c \<in> B"
          using hxy True h\<phi>v h\<phi>xB by (by100 simp)
        thus ?thesis
          using hcB by (by100 blast)
      next
        case False
        have hyLV: "y \<in> ?LV"
          using hy False by (by100 blast)
        have h\<psi>xy: "\<psi> x = \<psi> y"
          using hxy h\<phi>link hxLV hyLV by (by100 simp)
        show ?thesis
          by (rule inj_onD[OF h\<psi>inj h\<psi>xy hxLV hyLV])
      qed
    qed
  qed
  have h\<phi>inj: "inj_on \<phi> ?SV"
    using hstar h\<phi>inj_insert by (by100 simp)
  show ?thesis
    unfolding bij_betw_def using h\<phi>inj h\<phi>img by (by100 blast)
qed

lemma geotop_fig410_link_and_star_vertices_finite_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink_finite: "finite (geotop_link K v)"
  shows "finite (geotop_complex_vertices (geotop_link K v))
      \<and> finite (geotop_complex_vertices (geotop_star K v))"
  (**
    Fig. 4.10 finiteness bookkeeping: before matching the link with a
    subdivision of the frontier of a 2-simplex, both the old boundary vertices
    and the whole cone-star vertex set are finite. **)
proof -
  have hlink_complex: "geotop_is_complex (geotop_link K v)"
    by (rule geotop_link_is_complex[OF hK])
  have hlink_vertices_finite: "finite (geotop_complex_vertices (geotop_link K v))"
    by (rule geotop_finite_complex_vertices_finite_dev34
        [OF hlink_complex hlink_finite])
  have hstar_vertices:
      "geotop_complex_vertices (geotop_star K v)
        = insert v (geotop_complex_vertices (geotop_link K v))"
    by (rule geotop_star_vertices_eq_insert_link_vertices_dev34[OF hK hv])
  have hstar_vertices_finite:
      "finite (geotop_complex_vertices (geotop_star K v))"
    using hstar_vertices hlink_vertices_finite by (by100 simp)
  show ?thesis
    using hlink_vertices_finite hstar_vertices_finite by (by100 blast)
qed

lemma geotop_star_fan_isomorphism_from_link_bij_and_simplex_iff_dev34:
  fixes K L' :: "(real^2) set set" and B :: "(real^2) set"
    and v c :: "real^2"
    and \<psi> :: "real^2 \<Rightarrow> real^2"
  defines "\<phi> \<equiv> (\<lambda>x. if x = v then c else \<psi> x)"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes h\<psi>: "bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B"
  assumes hcB: "c \<notin> B"
  assumes hL_vertices: "geotop_complex_vertices L' = insert c B"
  assumes hsimplex:
    "\<forall>V. V \<subseteq> geotop_complex_vertices (geotop_star K v) \<longrightarrow>
        (geotop_convex_hull V \<in> geotop_star K v
          \<longleftrightarrow> geotop_convex_hull (\<phi> ` V) \<in> L')"
  shows "geotop_isomorphism (geotop_star K v) L' \<phi>"
  (**
    Fig. 4.10 isomorphism packaging: once the link-boundary vertex
    correspondence is fixed and the old-link/cone simplex cases match the
    target fan, the extended vertex map is a simplicial isomorphism. **)
proof -
  have hbij_insert:
      "bij_betw \<phi> (geotop_complex_vertices (geotop_star K v)) (insert c B)"
  proof -
    have "bij_betw (\<lambda>x. if x = v then c else \<psi> x)
        (geotop_complex_vertices (geotop_star K v)) (insert c B)"
      by (rule geotop_star_cone_vertex_map_bij_dev34[OF hK hv h\<psi> hcB])
    thus ?thesis
      using \<phi>_def by (by100 simp)
  qed
  have hbij:
      "bij_betw \<phi> (geotop_complex_vertices (geotop_star K v))
        (geotop_complex_vertices L')"
    using hbij_insert hL_vertices by (by100 simp)
  show ?thesis
    unfolding geotop_isomorphism_def using hbij hsimplex by (by100 blast)
qed

lemma geotop_star_fan_isomorphism_from_link_and_cone_target_cases_dev34:
  fixes K L' :: "(real^2) set set" and B :: "(real^2) set"
    and v c :: "real^2"
    and \<psi> :: "real^2 \<Rightarrow> real^2"
  defines "\<phi> \<equiv> (\<lambda>x. if x = v then c else \<psi> x)"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes h\<psi>: "bij_betw \<psi> (geotop_complex_vertices (geotop_link K v)) B"
  assumes hcB: "c \<notin> B"
  assumes hL_vertices: "geotop_complex_vertices L' = insert c B"
  assumes hstar_vertices_finite:
    "finite (geotop_complex_vertices (geotop_star K v))"
  assumes hlink_target:
    "\<forall>W. W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> L')"
  assumes hcone_vertex_target:
    "geotop_convex_hull {c} \<in> L'"
  assumes hcone_target:
    "\<forall>W. finite W \<longrightarrow> W \<noteq> {} \<longrightarrow>
        W \<subseteq> geotop_complex_vertices (geotop_link K v) \<longrightarrow>
        (geotop_convex_hull W \<in> geotop_link K v
          \<longleftrightarrow> geotop_convex_hull (insert c (\<psi> ` W)) \<in> L')"
  shows "geotop_isomorphism (geotop_star K v) L' \<phi>"
  (**
    Fig. 4.10 isomorphism step from target fan cases: the link-boundary
    bijection plus the target's old-link/cone membership facts give a
    simplicial isomorphism of the whole star. **)
proof -
  have hsimplex_raw:
    "\<forall>V. V \<subseteq> geotop_complex_vertices (geotop_star K v) \<longrightarrow>
        (geotop_convex_hull V \<in> geotop_star K v
          \<longleftrightarrow> geotop_convex_hull ((\<lambda>x. if x = v then c else \<psi> x) ` V) \<in> L')"
    by (rule geotop_star_fan_simplex_iff_from_link_and_cone_target_cases_dev34
        [OF hK hv hstar_vertices_finite hlink_target hcone_vertex_target
          hcone_target])
  have hiso_raw:
    "geotop_isomorphism (geotop_star K v) L' (\<lambda>x. if x = v then c else \<psi> x)"
    by (rule geotop_star_fan_isomorphism_from_link_bij_and_simplex_iff_dev34
        [OF hK hv h\<psi> hcB hL_vertices hsimplex_raw])
  show ?thesis
    using hiso_raw \<phi>_def by (by100 simp)
qed

lemma geotop_finite_linear_graph_polygon_polyhedron_connected_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron L)"
  shows "geotop_complex_connected L"
  (**
    First graph-theoretic step behind Moise Fig. 4.10: the linear graph
    triangulating a polygonal link is a single connected cycle, since its
    polyhedron is a topological 1-sphere. **)
proof -
  have hL_complex: "geotop_is_complex L"
    using hL_linear unfolding geotop_is_linear_graph_def by (by100 blast)
  have hhomeo: "geotop_polyhedron L homeomorphic sphere (0::real^2) 1"
    by (rule polygon_homeomorphic_S1_helper[OF hpolygon])
  have hdim: "(2::nat) \<le> DIM(real^2)"
    by (by100 simp)
  have hsphere_conn: "connected (sphere (0::real^2) 1)"
    by (rule connected_sphere[OF hdim])
  have hpoly_conn_HOL: "connected (geotop_polyhedron L)"
    using hhomeo hsphere_conn homeomorphic_connectedness by (by100 blast)
  have hpoly_conn:
      "top1_connected_on (geotop_polyhedron L)
        (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    using hpoly_conn_HOL top1_connected_on_geotop_iff_connected by (by100 blast)
  have hpath:
      "top1_path_connected_on (geotop_polyhedron L)
        (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    by (rule iffD2[OF Theorem_GT_1_12(2)[OF hL_complex] hpoly_conn])
  show ?thesis
    by (rule iffD2[OF Theorem_GT_1_12(1)[OF hL_complex] hpath])
qed

lemma geotop_connected_geotop_subspace_no_open_singleton_if_two_points_dev34:
  fixes S :: "(real^2) set"
  assumes hconn: "top1_connected_on S
      (subspace_topology UNIV geotop_euclidean_topology S)"
  assumes hpS: "p \<in> S"
  assumes hqS: "q \<in> S"
  assumes hpq: "p \<noteq> q"
  shows "{p} \<notin> subspace_topology UNIV geotop_euclidean_topology S"
proof
  let ?T = "subspace_topology UNIV geotop_euclidean_topology S"
  assume hp_open: "{p} \<in> ?T"
  have htop: "is_topology_on S ?T"
    using hconn unfolding top1_connected_on_def by (by100 blast)
  have hp_subset: "{p} \<subseteq> S"
    using hpS by (by100 blast)
  have hclosed: "closedin_on S ?T {p}"
    unfolding closedin_on_def
  proof
    show "S - {p} \<in> ?T"
    proof -
      have hopen_compl_univ: "open (UNIV - {p})"
      proof -
        have "closed ({p} :: (real^2) set)"
          by (rule closed_singleton)
        hence "open (- {p})"
          by (rule open_Compl)
        moreover have "(UNIV - {p} :: (real^2) set) = - {p}"
          by (by100 blast)
        thus ?thesis
          using calculation by (by100 simp)
      qed
      have hSdiff: "S - {p} = (UNIV - {p}) \<inter> S"
        by (by100 blast)
      show ?thesis
        unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
          subspace_topology_def
        using hopen_compl_univ hSdiff by (by100 blast)
    qed
  next
    show "{p} \<subseteq> S"
      by (rule hp_subset)
  qed
  have hp_ne: "{p} \<noteq> {}"
    by (by100 simp)
  have hp_eq_S: "{p} = S"
    using connected_iff_clopen[OF htop] hconn hp_open hclosed hp_ne
    by (by100 blast)
  have "q \<in> {p}"
    using hqS hp_eq_S by (by100 blast)
  thus False
    using hpq by (by100 simp)
qed

lemma geotop_finite_linear_graph_polygon_vertices_nonisolated_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron L)"
  shows "\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e)"
proof (intro allI impI)
  fix w
  assume hwL: "{w} \<in> L"
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL_linear])
  have hw_vertex: "w \<in> geotop_complex_vertices L"
    using geotop_complex_vertices_eq_0_simplexes[OF hL_complex] hwL
    by (by100 blast)
  have hw_poly: "w \<in> geotop_polyhedron L"
    using hwL unfolding geotop_polyhedron_def by (by100 blast)
  have hn_sphere: "geotop_is_n_sphere (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L)) 1"
    using hpolygon unfolding geotop_is_polygon_def by (by100 blast)
  have hnot_singleton_poly: "geotop_polyhedron L \<noteq> {w}"
  proof
    assume hpoly_eq: "geotop_polyhedron L = {w}"
    have hnot_conn: "\<not> top1_connected_on (UNIV - geotop_polyhedron L)
        (subspace_topology UNIV geotop_euclidean_topology (UNIV - geotop_polyhedron L))"
      by (rule Theorem_GT_4_3[OF hn_sphere])
    have hconn_point: "top1_connected_on (UNIV - {w})
        (subspace_topology UNIV geotop_euclidean_topology (UNIV - {w}))"
      by (rule geotop_punctured_plane_connected)
    show False
      using hnot_conn hconn_point hpoly_eq by (by100 simp)
  qed
  obtain q where hq_poly: "q \<in> geotop_polyhedron L" and hqw: "q \<noteq> w"
    using hnot_singleton_poly hw_poly by (by100 blast)
  have hwq: "w \<noteq> q"
    using hqw by (by100 blast)
  have hconn: "top1_connected_on (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    using geotop_finite_linear_graph_polygon_polyhedron_connected_dev34
      [OF hL_linear hpolygon]
      geotop_complex_connected_top1_connected_polyhedron_dev34
    by (by100 blast)
  show "\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e"
  proof (rule ccontr)
    assume hno: "\<not> (\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e)"
    have hno_edge: "\<not> (\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e)"
      by (rule hno)
    have hsingle_open: "{w} \<in> subspace_topology UNIV
        geotop_euclidean_topology (geotop_polyhedron L)"
      by (rule geotop_complex_no_incident_edge_vertex_open_singleton
          [OF hL_complex hw_vertex hno_edge])
    have hsingle_not_open: "{w} \<notin> subspace_topology UNIV
        geotop_euclidean_topology (geotop_polyhedron L)"
      by (rule geotop_connected_geotop_subspace_no_open_singleton_if_two_points_dev34
          [OF hconn hw_poly hq_poly hwq])
    show False
      using hsingle_open hsingle_not_open by (by100 blast)
  qed
qed

lemma geotop_polygon_not_broken_line_dev34:
  fixes J :: "(real^2) set"
  assumes hpolygon: "geotop_is_polygon J"
  assumes hbroken: "geotop_is_broken_line J"
  shows False
  (**
    Separation distinction used in the graph-cycle classification: a polygon
    separates the plane, while a broken line does not. **)
proof -
  have hJsphere:
      "geotop_is_n_sphere J
        (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hpolygon unfolding geotop_is_polygon_def by (by100 blast)
  have hnot_conn:
      "\<not> top1_connected_on (UNIV - J)
        (subspace_topology UNIV geotop_euclidean_topology (UNIV - J))"
    by (rule Theorem_GT_4_3[OF hJsphere])
  have hconn:
      "top1_connected_on (UNIV - J)
        (subspace_topology UNIV geotop_euclidean_topology (UNIV - J))"
    by (rule Theorem_GT_2_3[OF hbroken])
  show False
    using hnot_conn hconn by (by100 blast)
qed

lemma geotop_finite_linear_graph_polygon_connected_nonisolated_dev34:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron L)"
  shows "geotop_complex_connected L
      \<and> (\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e))"
  (**
    First Fig. 4.10 graph prerequisite: the polygonal carrier gives one
    connected component and no isolated complex vertices. **)
proof -
  have hconn: "geotop_complex_connected L"
    by (rule geotop_finite_linear_graph_polygon_polyhedron_connected_dev34
        [OF hL_linear hpolygon])
  have hnonisolated:
      "\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e)"
    by (rule geotop_finite_linear_graph_polygon_vertices_nonisolated_dev34
        [OF hL_linear hL_finite hpolygon])
  show ?thesis
    using hconn hnonisolated by (by100 blast)
qed

lemma geotop_finite_connected_degree_one_or_two_polygon_degree_two_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron L)"
  shows "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  (**
    Finite graph-cycle prerequisite for Fig. 4.10: in the classified
    degree-one-or-two case, the polygon alternative excludes endpoints, hence
    every vertex has exactly two incident edges. **)
proof -
  have hendpoint_or_noendpoint:
      "(\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w) \<or>
       (\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w)"
    by (by100 blast)
  show ?thesis
  proof (rule disjE[OF hendpoint_or_noendpoint])
    assume hend: "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
    have hbroken: "geotop_is_broken_line (geotop_polyhedron L)"
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
    have False
      by (rule geotop_polygon_not_broken_line_dev34[OF hpolygon hbroken])
    then show ?thesis
      by (by100 blast)
  next
    assume hnoend:
        "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
    show ?thesis
    proof (rule geotop_degree_one_or_two_no_endpoint_degree_two_dev34
        [where L = L])
      show "geotop_is_linear_graph L" by (rule hL)
      show "\<forall>w. {w} \<in> L \<longrightarrow>
          card {e \<in> L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
          card {e \<in> L. geotop_is_edge e \<and> w \<in> e} = 2"
        by (rule hdegree12)
      show "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
        by (rule hnoend)
    qed
  qed
qed

lemma geotop_finite_connected_degree_one_or_two_polygon_no_endpoint_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron L)"
  shows "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
  (**
    No-endpoint form of the same Fig. 4.10 cycle prerequisite. **)
proof -
  have hdegree2: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
    by (rule geotop_finite_connected_degree_one_or_two_polygon_degree_two_dev34
        [OF hL hfin hconn hdegree12 hpolygon])
  show ?thesis
    by (rule geotop_degree_two_vertices_no_graph_endpoint_dev34[OF hdegree2])
qed

lemma geotop_finite_linear_graph_polygon_degree_one_or_two_degree_two_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron L)"
  shows "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  (**
    Fig. 4.10 cycle prerequisite with connectedness discharged from the
    polygonal carrier: once the local Lemmas 2--4 give degree one or two,
    the polygon alternative forces the degree-two cycle case. **)
proof -
  have hconn: "geotop_complex_connected L"
    using geotop_finite_linear_graph_polygon_connected_nonisolated_dev34
      [OF hL hfin hpolygon] by (by100 blast)
  show ?thesis
    by (rule geotop_finite_connected_degree_one_or_two_polygon_degree_two_dev34
        [OF hL hfin hconn hdegree12 hpolygon])
qed

lemma geotop_finite_linear_graph_polygon_degree_one_or_two_no_endpoint_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron L)"
  shows "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
  (**
    No-endpoint form of the same Fig. 4.10 cycle prerequisite, again with
    connectedness obtained from the polygonal carrier. **)
proof -
  have hdegree2: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
    by (rule geotop_finite_linear_graph_polygon_degree_one_or_two_degree_two_dev34
        [OF hL hfin hdegree12 hpolygon])
  show ?thesis
    by (rule geotop_degree_two_vertices_no_graph_endpoint_dev34[OF hdegree2])
qed

end
