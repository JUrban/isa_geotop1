theory GeoTop_3_4
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

lemma geotop_vertex_star_standard_fan_isomorphism_from_finite_linear_link_line_or_polygon_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  assumes hlink_finite: "finite (geotop_link K v)"
  assumes hshape:
    "geotop_is_broken_line (geotop_polyhedron (geotop_link K v))
      \<or> geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
  shows "\<exists>(\<sigma> :: (real^2) set) L' \<phi>.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_isomorphism (geotop_star K v) L' \<phi>"
  (**
    Moise Fig. 4.10 with the simplicial bijection made explicit.  The missing
    combinatorial content is to enumerate the finite linear link as either an
    edge-chain or an edge-cycle, subdivide \<open>Fr \<sigma>\<close> with the same ordered
    edge data, and define \<open>\<phi>\<close> on vertices by the corresponding order-preserving
    match, with \<open>v\<close> sent to the new cone vertex. **)
  sorry

lemma geotop_vertex_star_standard_fan_model_from_finite_linear_link_line_or_polygon_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hlink_linear: "geotop_is_linear_graph (geotop_link K v)"
  assumes hlink_finite: "finite (geotop_link K v)"
  assumes hshape:
    "geotop_is_broken_line (geotop_polyhedron (geotop_link K v))
      \<or> geotop_is_polygon (geotop_polyhedron (geotop_link K v))"
  shows "\<exists>(\<sigma> :: (real^2) set) L'.
      geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_isomorphic (geotop_star K v) L'"
  (**
    Moise Fig. 4.10, isolated in the exact form used below.  Subdivide the
    frontier of a 2-simplex so its edge-chain/cycle has the same combinatorial
    order as the finite linear link, add one interior vertex, and cone that
    subdivided frontier to the new vertex.  The simplicial bijection sends
    \<open>v\<close> to the new cone vertex and sends the link vertices, in linear/cyclic
    order, to the subdivided frontier vertices. **)
proof -
  obtain \<sigma> :: "(real^2) set" and L' \<phi>
    where hfan:
      "geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_isomorphism (geotop_star K v) L' \<phi>"
    using geotop_vertex_star_standard_fan_isomorphism_from_finite_linear_link_line_or_polygon_dev34
      [OF hK hv hlink_linear hlink_finite hshape]
    by (by100 blast)
  show ?thesis
    unfolding geotop_isomorphic_def using hfan by (by100 blast)
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
    Moise Fig. 4.10 step. Take a 2-simplex \<open>\<sigma>\<close>; subdivide
    \<open>Fr \<sigma>\<close> so its edge-cycle or edge-chain matches the finite
    polygonal/broken-line link; add one interior vertex and cone the boundary
    subdivision to that vertex. The resulting fan subdivision of
    \<open>{\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}\<close> is simplicially isomorphic to a
    subdivision of \<open>St v\<close>, with the link corresponding to the subdivided
    boundary. **)
proof -
  obtain \<sigma> :: "(real^2) set" and L'
    where hfan:
      "geotop_simplex_dim \<sigma> 2
      \<and> geotop_is_subdivision L' {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
      \<and> geotop_isomorphic (geotop_star K v) L'"
    using geotop_vertex_star_standard_fan_model_from_finite_linear_link_line_or_polygon_dev34
      [OF hK hv hlink_linear hlink_finite hshape]
    by (by100 blast)
  have hstar_complex: "geotop_is_complex (geotop_star K v)"
    by (rule geotop_star_is_complex[OF hK])
  have hstar_sub: "geotop_is_subdivision (geotop_star K v) (geotop_star K v)"
    by (rule geotop_is_subdivision_refl[OF hstar_complex])
  show ?thesis
    using hfan hstar_sub by (intro exI[of _ "{\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"])
      (by100 blast)
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

lemma geotop_unique_incident_2simplex_small_semicircle_domain_separates_chart_dev34:
  fixes K :: "(real^2) set set" and e U A :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hunique:
    "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  assumes hlocal_ball: "\<exists>r>0. geotop_polyhedron K \<inter> ball p r \<subseteq> U"
  shows "\<exists>A. A \<subseteq> U
      \<and> geotop_is_arc A
          (subspace_topology UNIV geotop_euclidean_topology A)
      \<and> \<not> top1_connected_on (U - A)
          (subspace_topology UNIV geotop_euclidean_topology (U - A))"
  (**
    Moise Lemma 3 local picture: with only one 2-simplex incident to the edge,
    choose a sufficiently small semicircle in that simplex, centered at the
    edge-interior point.  The local-ball assumption keeps the semicircle inside
    the chart domain \<open>U\<close>, and the semicircle separates the half-neighborhood
    in \<open>U\<close>. **)
  sorry

lemma geotop_unique_incident_2simplex_small_semicircle_separates_chart_dev34:
  fixes K :: "(real^2) set set" and e U A :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hunique:
    "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  assumes hlocal_ball: "\<exists>r>0. geotop_polyhedron K \<inter> ball p r \<subseteq> U"
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
      [OF hK heK hedge hp hunique hlocal_ball]
    by (by100 blast)
  have hAimg: "geotop_is_arc (f ` A)
      (subspace_topology UNIV geotop_euclidean_topology (f ` A))"
    by (rule geotop_homeomorphism_image_arc_dev34[OF hhomeo hAsub hAarc])
  show ?thesis
    using hAsub hAimg hAsep by (by100 blast)
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
  shows "\<exists>J. J \<subseteq> U
      \<and> geotop_is_n_sphere J
          (subspace_topology UNIV geotop_euclidean_topology J) 1
      \<and> top1_connected_on (U - J)
          (subspace_topology UNIV geotop_euclidean_topology (U - J))"
  (**
    Moise Lemma 4 local picture: from three incident 2-simplexes, choose two
    same-radius small semicircles in two of the incident simplexes, centered at
    the edge-interior point.  Their union is the small 1-sphere \<open>J\<close> inside the
    chart domain \<open>U\<close>; because the third incident simplex gives a passage
    around it, \<open>U - J\<close> remains connected. **)
  sorry

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
      [OF hK heK hedge hp hfaces hlocal_ball]
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
  have hsemicircle:
    "\<exists>A. A \<subseteq> U
      \<and> geotop_is_arc (f ` A)
          (subspace_topology UNIV geotop_euclidean_topology (f ` A))
      \<and> \<not> top1_connected_on (U - A)
          (subspace_topology UNIV geotop_euclidean_topology (U - A))"
    by (rule geotop_unique_incident_2simplex_small_semicircle_separates_chart_dev34
        [OF hK heK hedge hp hunique hlocal_ball hhomeo])
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
  have hcircle:
    "\<exists>J. J \<subseteq> U
      \<and> geotop_is_n_sphere (f ` J)
          (subspace_topology UNIV geotop_euclidean_topology (f ` J)) 1
      \<and> top1_connected_on (U - J)
          (subspace_topology UNIV geotop_euclidean_topology (U - J))"
    by (rule geotop_three_incident_2simplex_small_circle_not_separates_chart_dev34
        [OF hK heK hedge hp hfaces hlocal_ball hhomeo])
  show ?thesis
    using hcircle by (by100 blast)
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
  assumes hlocal_ball: "\<exists>r>0. geotop_polyhedron K \<inter> ball p r \<subseteq> U"
  assumes hcell: "geotop_is_n_cell (closure_on (geotop_polyhedron K)
        (top1_metric_topology_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y))) U)
      (subspace_topology (geotop_polyhedron K)
        (top1_metric_topology_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)))
        (closure_on (geotop_polyhedron K)
          (top1_metric_topology_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y))) U)) 2"
  shows False
  sorry

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
  show False
    by (rule geotop_boundary_2cell_chart_three_incident_2simplex_contradiction_dev34
        [OF hK heK hedge hp hfaces hlocal_ball hcell])
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
      have hpoly_L: "geotop_is_polygon (geotop_polyhedron L)"
        by (rule geotop_finite_connected_degree_two_linear_graph_polygon_dev34
            [OF hL_linear hL_fin hL_conn hL_degree])
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
        have hshape_L: "geotop_is_broken_line (geotop_polyhedron L) \<or>
            geotop_is_polygon (geotop_polyhedron L)"
          by (rule geotop_finite_connected_degree_one_or_two_linear_graph_line_or_polygon_dev34
              [OF hL_linear hL_fin hL_conn hL_degree12])
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
    sorry
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
        and hf:
          "top1_homeomorphism_on U
             (subspace_topology M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U)
             (UNIV::(real^2) set) geotop_euclidean_topology f"
        using hP_mint unfolding geotop_manifold_interior_def by (by100 blast)
      have hU_sub_M: "U \<subseteq> M"
        using hU_openin unfolding openin_on_def by (by100 blast)
      have htopM: "top1_metric_topology_on M (\<lambda>x y. norm (x - y)) =
                   subspace_topology UNIV geotop_euclidean_topology M"
        by (rule top1_norm_metric_topology_on_eq_geotop_subspace)
      have hsubU:
        "subspace_topology M (top1_metric_topology_on M (\<lambda>x y. norm (x - y))) U =
         subspace_topology UNIV geotop_euclidean_topology U"
      proof -
        have "subspace_topology M (subspace_topology UNIV geotop_euclidean_topology M) U =
              subspace_topology UNIV geotop_euclidean_topology U"
          by (rule subspace_topology_trans[OF hU_sub_M])
        thus ?thesis using htopM by (by100 simp)
      qed
      have hf_geotop:
        "top1_homeomorphism_on U
           (subspace_topology UNIV geotop_euclidean_topology U)
           (UNIV::(real^2) set) geotop_euclidean_topology f"
        using hf hsubU by (by100 simp)
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
