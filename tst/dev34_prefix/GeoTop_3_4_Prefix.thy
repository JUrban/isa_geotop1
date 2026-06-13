theory GeoTop_3_4_Prefix
  imports "GeoTop34PrefixMidDirty.GeoTop_3_4_Prefix_Mid"
begin

(** from \<S>4 Theorem 3 (geotop.tex:886)
    LATEX VERSION: Let J be a topological 1-sphere in R^2. Then R^2 - J is not connected. **)
theorem Theorem_GT_4_3:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "\<not> top1_connected_on (UNIV - J)
           (subspace_topology UNIV geotop_euclidean_topology (UNIV - J))"
  (** Moise proof (geotop.tex:886): J homeomorphic to the unit 1-sphere in R^2
      (= HOL `sphere 0 1`). Apply HOL-Analysis's Jordan_Brouwer_separation
      (euclidean_space version) and bridge back. **)
proof -
  obtain f where hhomeo: "top1_homeomorphism_on J
                           (subspace_topology UNIV geotop_euclidean_topology J)
                           (geotop_std_sphere::(real^2) set)
                           (subspace_topology UNIV geotop_euclidean_topology
                              (geotop_std_sphere::(real^2) set)) f"
    using hJ unfolding geotop_is_n_sphere_def by blast
  have hhomeo_HOL: "J homeomorphic (geotop_std_sphere::(real^2) set)"
    by (rule top1_homeomorphism_on_geotop_imp_HOL_homeomorphic[OF hhomeo])
  have hstd_eq: "(geotop_std_sphere::(real^2) set) = sphere 0 1"
    unfolding geotop_std_sphere_def sphere_def by simp
  have hJ_sphere: "J homeomorphic sphere (0::real^2) 1"
    using hhomeo_HOL hstd_eq by simp
  have hnotconn_HOL: "\<not> connected (- J)"
    using Jordan_Brouwer_separation[OF hJ_sphere] zero_less_one by blast
  have hnotconn_D: "\<not> connected (UNIV - J)"
    by (metis Compl_eq_Diff_UNIV hnotconn_HOL)
  show ?thesis
    using hnotconn_D top1_connected_on_geotop_iff_connected by metis
qed

(** from \<S>4: brick-decomposition (geotop.tex:943)
    LATEX VERSION: By a brick-decomposition of the plane we mean a collection G = {g_i} of
      polyhedral disks (=2-cells) such that (1) union is R^2, (2) if g_i and g_j intersect,
      their intersection is a broken line lying in the frontier of each, and (3) every point
      has a neighborhood intersecting at most three of the g_i. **)
definition geotop_brick_decomposition :: "(real^2) set set \<Rightarrow> bool" where
  "geotop_brick_decomposition G \<longleftrightarrow>
    (\<forall>g\<in>G. geotop_is_disk g (subspace_topology UNIV geotop_euclidean_topology g) \<and>
       (\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = g)) \<and>
    \<Union>G = UNIV \<and>
    (\<forall>g\<^sub>1\<in>G. \<forall>g\<^sub>2\<in>G. g\<^sub>1 \<noteq> g\<^sub>2 \<longrightarrow> g\<^sub>1 \<inter> g\<^sub>2 \<noteq> {} \<longrightarrow>
       geotop_is_broken_line (g\<^sub>1 \<inter> g\<^sub>2) \<and>
       g\<^sub>1 \<inter> g\<^sub>2 \<subseteq> geotop_frontier UNIV geotop_euclidean_topology g\<^sub>1 \<and>
       g\<^sub>1 \<inter> g\<^sub>2 \<subseteq> geotop_frontier UNIV geotop_euclidean_topology g\<^sub>2) \<and>
    (\<forall>P. \<exists>N. N \<in> geotop_euclidean_topology \<and> P \<in> N \<and> card {g\<in>G. g \<inter> N \<noteq> {}} \<le> 3)"

lemma geotop_two_arcs_compact_closed_prefix:
  fixes A1 A2 :: "(real^2) set"
  assumes hA1: "geotop_is_arc A1 (subspace_topology UNIV geotop_euclidean_topology A1)"
  assumes hA2: "geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2)"
  shows "compact A1 \<and> compact A2
      \<and> closed A1 \<and> closed A2
      \<and> A1 \<noteq> {} \<and> A2 \<noteq> {}
      \<and> compact (A1 \<union> A2) \<and> closed (A1 \<union> A2)"
proof -
  obtain \<gamma>1 :: "real \<Rightarrow> real^2" where h\<gamma>1_arc: "arc \<gamma>1"
    and h\<gamma>1_img: "path_image \<gamma>1 = A1"
    using geotop_is_arc_imp_HOL_arc[OF hA1] by (by100 blast)
  obtain \<gamma>2 :: "real \<Rightarrow> real^2" where h\<gamma>2_arc: "arc \<gamma>2"
    and h\<gamma>2_img: "path_image \<gamma>2 = A2"
    using geotop_is_arc_imp_HOL_arc[OF hA2] by (by100 blast)
  have hA1_compact: "compact A1"
    using compact_arc_image[OF h\<gamma>1_arc] h\<gamma>1_img by (by100 simp)
  have hA2_compact: "compact A2"
    using compact_arc_image[OF h\<gamma>2_arc] h\<gamma>2_img by (by100 simp)
  have hA1_closed: "closed A1"
    using closed_arc_image[OF h\<gamma>1_arc] h\<gamma>1_img by (by100 simp)
  have hA2_closed: "closed A2"
    using closed_arc_image[OF h\<gamma>2_arc] h\<gamma>2_img by (by100 simp)
  have hA1_nonempty: "A1 \<noteq> {}"
    using h\<gamma>1_img by (by100 simp)
  have hA2_nonempty: "A2 \<noteq> {}"
    using h\<gamma>2_img by (by100 simp)
  have hA12_compact: "compact (A1 \<union> A2)"
    using hA1_compact hA2_compact by (by100 simp)
  have hA12_closed: "closed (A1 \<union> A2)"
    using hA1_closed hA2_closed by (by100 simp)
  show ?thesis
    using hA1_compact hA2_compact hA1_closed hA2_closed
      hA1_nonempty hA2_nonempty hA12_compact hA12_closed
    by (by100 blast)
qed

lemma geotop_disjoint_arcs_positive_setdist_prefix:
  fixes A1 A2 :: "(real^2) set"
  assumes hA1: "geotop_is_arc A1 (subspace_topology UNIV geotop_euclidean_topology A1)"
  assumes hA2: "geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2)"
  assumes hA12: "A1 \<inter> A2 = {}"
  shows "0 < setdist A1 A2"
proof -
  have hpack: "compact A1 \<and> compact A2
      \<and> closed A1 \<and> closed A2
      \<and> A1 \<noteq> {} \<and> A2 \<noteq> {}
      \<and> compact (A1 \<union> A2) \<and> closed (A1 \<union> A2)"
    using geotop_two_arcs_compact_closed_prefix[OF hA1 hA2] .
  have hsep: "setdist A1 A2 > 0"
    using setdist_gt_0_compact_closed[of A1 A2] hpack hA12 by (by100 blast)
  show ?thesis
    using hsep by (by100 simp)
qed

lemma geotop_disjoint_arcs_uniform_distance_gap_prefix:
  fixes A1 A2 :: "(real^2) set"
  assumes hA1: "geotop_is_arc A1 (subspace_topology UNIV geotop_euclidean_topology A1)"
  assumes hA2: "geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2)"
  assumes hA12: "A1 \<inter> A2 = {}"
  shows "\<exists>\<delta>>0. \<forall>x\<in>A1. \<forall>y\<in>A2. \<delta> \<le> dist x y"
proof -
  have hsd_pos: "0 < setdist A1 A2"
    by (rule geotop_disjoint_arcs_positive_setdist_prefix[OF hA1 hA2 hA12])
  define \<delta> where "\<delta> = setdist A1 A2 / 2"
  have h\<delta>_pos: "0 < \<delta>"
    unfolding \<delta>_def using hsd_pos by (by100 simp)
  have h\<delta>_le: "\<delta> \<le> setdist A1 A2"
    unfolding \<delta>_def using hsd_pos by (by100 simp)
  have hgap: "\<forall>x\<in>A1. \<forall>y\<in>A2. \<delta> \<le> dist x y"
    using h\<delta>_le le_setdist_iff[of \<delta> A1 A2] by (by100 blast)
  show ?thesis
    using h\<delta>_pos hgap by (by100 blast)
qed

lemma geotop_small_diameter_set_misses_one_of_separated_arcs_prefix:
  fixes B A1 A2 :: "(real^2) set"
  assumes hgap: "\<forall>x\<in>A1. \<forall>y\<in>A2. \<delta> \<le> dist x y"
  assumes hBne: "B \<noteq> {}"
  assumes hBbdd: "bounded B"
  assumes hBdiam: "geotop_diameter (\<lambda>x y. norm (x - y)) B < \<delta>"
  shows "B \<inter> A1 = {} \<or> B \<inter> A2 = {}"
proof (rule ccontr)
  assume hnot: "\<not> (B \<inter> A1 = {} \<or> B \<inter> A2 = {})"
  obtain x where hxB: "x \<in> B" and hxA1: "x \<in> A1"
    using hnot by (by100 blast)
  obtain y where hyB: "y \<in> B" and hyA2: "y \<in> A2"
    using hnot by (by100 blast)
  have hdist_le_HOL: "dist x y \<le> diameter B"
    by (rule diameter_bounded_bound[OF hBbdd hxB hyB])
  have hHOL_le_geo: "diameter B \<le> geotop_diameter (\<lambda>x y. norm (x - y)) B"
    by (rule geotop_diameter_ge_HOL_diameter[OF hBne hBbdd])
  have hdist_lt: "dist x y < \<delta>"
    using hdist_le_HOL hHOL_le_geo hBdiam by (by100 linarith)
  have hgap_xy: "\<delta> \<le> dist x y"
    using hgap hxA1 hyA2 by (by100 blast)
  show False
    using hgap_xy hdist_lt by (by100 linarith)
qed

lemma geotop_mesh_member_misses_one_of_separated_arcs_prefix:
  fixes G :: "(real^2) set set"
  assumes hgap: "\<forall>x\<in>A1. \<forall>y\<in>A2. \<delta> \<le> dist x y"
  assumes hGfin: "finite G"
  assumes hBG: "B \<in> G"
  assumes hBne: "B \<noteq> {}"
  assumes hBbdd: "bounded B"
  assumes hmesh: "geotop_mesh (\<lambda>x y. norm (x - y)) G < \<delta>"
  shows "B \<inter> A1 = {} \<or> B \<inter> A2 = {}"
proof -
  have hBdiam_le_mesh: "geotop_diameter (\<lambda>x y. norm (x - y)) B
      \<le> geotop_mesh (\<lambda>x y. norm (x - y)) G"
    by (rule geotop_diameter_le_mesh[OF hGfin hBG])
  have hBdiam_lt: "geotop_diameter (\<lambda>x y. norm (x - y)) B < \<delta>"
    using hBdiam_le_mesh hmesh by (by100 linarith)
  show ?thesis
    by (rule geotop_small_diameter_set_misses_one_of_separated_arcs_prefix
        [OF hgap hBne hBbdd hBdiam_lt])
qed

lemma geotop_mesh_subfamily_meeting_first_arc_misses_second_prefix:
  fixes G :: "(real^2) set set"
  assumes hgap: "\<forall>x\<in>A1. \<forall>y\<in>A2. \<delta> \<le> dist x y"
  assumes hGfin: "finite G"
  assumes hG_nonempty_bounded: "\<forall>B\<in>G. B \<noteq> {} \<and> bounded B"
  assumes hmesh: "geotop_mesh (\<lambda>x y. norm (x - y)) G < \<delta>"
  shows "(\<Union>{B\<in>G. B \<inter> A1 \<noteq> {}}) \<inter> A2 = {}"
proof (rule ccontr)
  assume hnot: "(\<Union>{B\<in>G. B \<inter> A1 \<noteq> {}}) \<inter> A2 \<noteq> {}"
  obtain y B where hyB: "y \<in> B" and hyA2: "y \<in> A2"
    and hBG: "B \<in> G" and hB_A1: "B \<inter> A1 \<noteq> {}"
    using hnot by (by100 blast)
  have hBne: "B \<noteq> {}"
    using hG_nonempty_bounded hBG by (by100 blast)
  have hBbdd: "bounded B"
    using hG_nonempty_bounded hBG by (by100 blast)
  have hB_misses: "B \<inter> A1 = {} \<or> B \<inter> A2 = {}"
    by (rule geotop_mesh_member_misses_one_of_separated_arcs_prefix
        [OF hgap hGfin hBG hBne hBbdd hmesh])
  have hB_A2_nonempty: "B \<inter> A2 \<noteq> {}"
    using hyB hyA2 by (by100 blast)
  show False
    using hB_misses hB_A1 hB_A2_nonempty by (by100 blast)
qed

lemma geotop_finite_complex_iterated_Sd_mesh_lt_prefix:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKfin: "finite K"
  assumes h\<epsilon>: "0 < \<epsilon>"
  shows "\<exists>m. geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd m K) < \<epsilon>"
proof -
  have hlim: "(\<lambda>m. geotop_mesh (\<lambda>x y. norm (x - y))
               (geotop_iterated_Sd m K)) \<longlonglongrightarrow> 0"
    by (rule geotop_mesh_iterated_Sd_tends_to_zero[OF hK hKfin])
  have hevent:
      "eventually (\<lambda>m. geotop_mesh (\<lambda>x y. norm (x - y))
               (geotop_iterated_Sd m K) < \<epsilon>) sequentially"
    using order_tendstoD(2)[OF hlim h\<epsilon>] .
  show ?thesis
    using hevent unfolding eventually_sequentially by (by100 blast)
qed

lemma geotop_iterated_Sd_members_nonempty_bounded_prefix:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKfin: "finite K"
  shows "\<forall>B\<in>geotop_iterated_Sd m K. B \<noteq> {} \<and> bounded B"
proof
  fix B
  assume hB: "B \<in> geotop_iterated_Sd m K"
  have hsub: "geotop_is_subdivision (geotop_iterated_Sd m K) K"
    by (rule geotop_iterated_Sd_is_subdivision[OF hK hKfin])
  have hSd_comp: "geotop_is_complex (geotop_iterated_Sd m K)"
    using hsub unfolding geotop_is_subdivision_def by (by100 blast)
  have hB_simplex: "geotop_is_simplex B"
    using geotop_is_complex_simplex[OF hSd_comp] hB by (by100 blast)
  have hB_ne: "B \<noteq> {}"
    by (rule geotop_simplex_nonempty[OF hB_simplex])
  have hB_compact: "compact B"
    by (rule geotop_simplex_compact[OF hB_simplex])
  have hB_bounded: "bounded B"
    using hB_compact compact_imp_bounded by (by100 blast)
  show "B \<noteq> {} \<and> bounded B"
    using hB_ne hB_bounded by (by100 blast)
qed

lemma geotop_fine_iterated_Sd_carrier_meeting_first_arc_misses_second_prefix:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKfin: "finite K"
  assumes h\<delta>: "0 < \<delta>"
  assumes hgap: "\<forall>x\<in>A1. \<forall>y\<in>A2. \<delta> \<le> dist x y"
  shows "\<exists>m. (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}}) \<inter> A2 = {}"
proof -
  obtain m where hmesh:
      "geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd m K) < \<delta>"
    using geotop_finite_complex_iterated_Sd_mesh_lt_prefix[OF hK hKfin h\<delta>]
    by (by100 blast)
  have hsub: "geotop_is_subdivision (geotop_iterated_Sd m K) K"
    by (rule geotop_iterated_Sd_is_subdivision[OF hK hKfin])
  have hfin: "finite (geotop_iterated_Sd m K)"
    by (rule geotop_subdivision_of_finite_is_finite[OF hKfin hsub])
  have hmembers: "\<forall>B\<in>geotop_iterated_Sd m K. B \<noteq> {} \<and> bounded B"
    by (rule geotop_iterated_Sd_members_nonempty_bounded_prefix[OF hK hKfin])
  have hmiss:
      "(\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}}) \<inter> A2 = {}"
    by (rule geotop_mesh_subfamily_meeting_first_arc_misses_second_prefix
        [OF hgap hfin hmembers hmesh])
  show ?thesis
    using hmiss by (by100 blast)
qed

lemma geotop_polygon_disk_fine_Sd_carrier_meeting_first_arc_misses_second_prefix:
  fixes J A1 A2 :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  assumes h\<delta>: "0 < \<delta>"
  assumes hgap: "\<forall>x\<in>A1. \<forall>y\<in>A2. \<delta> \<le> dist x y"
  shows "\<exists>K m. geotop_is_complex K
      \<and> finite K
      \<and> geotop_polyhedron K =
          closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)
      \<and> (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}}) \<inter> A2 = {}"
proof -
  obtain K where hK: "geotop_is_complex K"
    and hKfin: "finite K"
    and hK_poly: "geotop_polyhedron K =
        closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
    using Theorem_GT_2_2[OF hJ] by (by100 blast)
  obtain m where hcarrier:
      "(\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}}) \<inter> A2 = {}"
    using geotop_fine_iterated_Sd_carrier_meeting_first_arc_misses_second_prefix
        [OF hK hKfin h\<delta> hgap]
    by (by100 blast)
  show ?thesis
    using hK hKfin hK_poly hcarrier by (by100 blast)
qed

lemma geotop_polygon_boundary_point_two_arcs_avoiding_ball_prefix:
  fixes J A1 A2 :: "(real^2) set"
  assumes hX: "X \<in> J"
  assumes hX_ne_P: "X \<noteq> P"
  assumes hX_ne_R: "X \<noteq> R"
  assumes hA1: "geotop_is_arc A1 (subspace_topology UNIV geotop_euclidean_topology A1)"
  assumes hA2: "geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2)"
  assumes hA1J: "A1 \<inter> J = {P}"
  assumes hA2J: "A2 \<inter> J = {R}"
  shows "\<exists>r>0. ball X r \<inter> (A1 \<union> A2) = {}"
  (**
    D44 endpoint-locality step.  A boundary point different from the two arc
    attachment points has a small ball disjoint from both cutting arcs, since
    each arc is closed and meets the polygon boundary only at its prescribed
    endpoint. **)
proof -
  have hA12_closed: "closed (A1 \<union> A2)"
    using geotop_two_arcs_compact_closed_prefix[OF hA1 hA2] by (by100 blast)
  have hX_not_A1: "X \<notin> A1"
  proof
    assume hXA1: "X \<in> A1"
    have "X \<in> A1 \<inter> J"
      using hXA1 hX by (by100 blast)
    hence "X = P"
      using hA1J by (by100 simp)
    thus False
      using hX_ne_P by (by100 blast)
  qed
  have hX_not_A2: "X \<notin> A2"
  proof
    assume hXA2: "X \<in> A2"
    have "X \<in> A2 \<inter> J"
      using hXA2 hX by (by100 blast)
    hence "X = R"
      using hA2J by (by100 simp)
    thus False
      using hX_ne_R by (by100 blast)
  qed
  have hX_not_union: "X \<notin> A1 \<union> A2"
    using hX_not_A1 hX_not_A2 by (by100 blast)
  have hopen_compl: "open (-(A1 \<union> A2))"
    by (rule open_Compl[OF hA12_closed])
  obtain r where hr_pos: "0 < r" and hr_sub: "ball X r \<subseteq> -(A1 \<union> A2)"
    using hopen_compl hX_not_union open_contains_ball by blast
  have hr_disj: "ball X r \<inter> (A1 \<union> A2) = {}"
    using hr_sub by (by100 blast)
  show ?thesis
    using hr_pos hr_disj by (by100 blast)
qed

lemma geotop_polygon_interior_minus_two_arcs_connected_frontier_witness_in_ball_prefix:
  fixes J A1 A2 :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  assumes hX: "X \<in> J"
  assumes hX_ne: "X \<noteq> P \<and> X \<noteq> R"
  assumes hA1: "geotop_is_arc A1 (subspace_topology UNIV geotop_euclidean_topology A1)"
  assumes hA2: "geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2)"
  assumes hA1J: "A1 \<inter> J = {P}"
  assumes hA2J: "A2 \<inter> J = {R}"
  assumes hr: "0 < r"
  shows "\<exists>U X'. connected U
        \<and> U \<in> geotop_euclidean_topology
        \<and> U \<subseteq> geotop_polygon_interior J - (A1 \<union> A2)
        \<and> U \<subseteq> ball X r
        \<and> X \<in> geotop_frontier UNIV geotop_euclidean_topology U
        \<and> X' \<in> U
        \<and> X' \<in> geotop_polygon_interior J - (A1 \<union> A2)"
  (**
    D44 two-arc analogue of the D42 local-side witness.  Near a boundary
    point away from the two arc endpoints, the complement of both arcs agrees
    locally with the polygon interior, so Moise's local polygon side can be
    chosen inside the cut-open set. **)
proof -
  have hX_ne_P: "X \<noteq> P"
    using hX_ne by (by100 blast)
  have hX_ne_R: "X \<noteq> R"
    using hX_ne by (by100 blast)
  obtain rA where hrA_pos: "0 < rA"
    and hrA_disj: "ball X rA \<inter> (A1 \<union> A2) = {}"
    using geotop_polygon_boundary_point_two_arcs_avoiding_ball_prefix
        [OF hX hX_ne_P hX_ne_R hA1 hA2 hA1J hA2J]
    by (elim exE conjE)
  define \<rho> where "\<rho> = min r rA / 2"
  have h\<rho>_pos: "0 < \<rho>"
    unfolding \<rho>_def using hr hrA_pos by (by100 simp)
  have h\<rho>_le_r: "\<rho> \<le> r"
    unfolding \<rho>_def using hr hrA_pos by (by100 simp)
  have h\<rho>_le_rA: "\<rho> \<le> rA"
    unfolding \<rho>_def using hr hrA_pos by (by100 simp)
  have hball_\<rho>_sub_r: "ball X \<rho> \<subseteq> ball X r"
    using h\<rho>_le_r by (by100 auto)
  have hball_\<rho>_sub_rA: "ball X \<rho> \<subseteq> ball X rA"
    using h\<rho>_le_rA by (by100 auto)
  have hball_\<rho>_A12: "ball X \<rho> \<inter> (A1 \<union> A2) = {}"
    using hball_\<rho>_sub_rA hrA_disj by (by100 blast)
  obtain U X' where hU_conn: "connected U"
    and hU_open: "U \<in> geotop_euclidean_topology"
    and hU_I: "U \<subseteq> geotop_polygon_interior J"
    and hU_ball_\<rho>: "U \<subseteq> ball X \<rho>"
    and hX_front_U:
      "X \<in> geotop_frontier UNIV geotop_euclidean_topology U"
    and hX'_U: "X' \<in> U"
    and hX'_I: "X' \<in> geotop_polygon_interior J"
    using geotop_polygon_local_side_witness_dev34[OF hJ hX h\<rho>_pos]
    by (elim exE conjE)
  have hU_ball_r: "U \<subseteq> ball X r"
    using hU_ball_\<rho> hball_\<rho>_sub_r by (by100 blast)
  have hU_A12_empty: "U \<inter> (A1 \<union> A2) = {}"
    using hU_ball_\<rho> hball_\<rho>_A12 by (by100 blast)
  have hU_cut: "U \<subseteq> geotop_polygon_interior J - (A1 \<union> A2)"
    using hU_I hU_A12_empty by (by100 blast)
  have hX'_cut: "X' \<in> geotop_polygon_interior J - (A1 \<union> A2)"
    using hX'_U hU_cut by (by100 blast)
  show ?thesis
    using hU_conn hU_open hU_cut hU_ball_r hX_front_U hX'_U hX'_cut
    by (intro exI conjI)
qed

lemma geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix:
  fixes J A1 A2 :: "(real^2) set" and P Q R S :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hP: "P \<in> J" and hQ: "Q \<in> J" and hR: "R \<in> J" and hS: "S \<in> J"
  assumes hcyc: "geotop_polygon_cyclic_order J P Q R S"
  assumes hcard: "card {P, Q, R, S} = 4"
  assumes hA1: "geotop_is_arc A1 (subspace_topology UNIV geotop_euclidean_topology A1)"
  assumes hA2: "geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2)"
  assumes hA12: "A1 \<inter> A2 = {}"
  assumes hA1_sub: "A1 \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hA2_sub: "A2 \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hA1J: "A1 \<inter> J = {P}"
  assumes hA2J: "A2 \<inter> J = {R}"
  shows "\<exists>C. Q \<in> geotop_frontier UNIV geotop_euclidean_topology C
          \<and> S \<in> geotop_frontier UNIV geotop_euclidean_topology C
          \<and> (\<exists>P'. P' \<in> geotop_polygon_interior J - (A1 \<union> A2) \<and>
              C = geotop_component_at UNIV geotop_euclidean_topology
                     (geotop_polygon_interior J - (A1 \<union> A2)) P')"
  (**
    Moise Theorem 4.4 brick/regular-neighborhood package.  Choose a fine
    brick-decomposition, take the brick neighborhood of \<open>A1\<close> inside \<open>\<bar>I\<close>,
    read the relevant frontier component as a 1-sphere with a broken-line
    subarc, obtain one component whose frontier contains the subarc endpoints,
    and transfer that component-frontier statement to \<open>Q,S\<close> by cyclic order. **)
proof -
  have hQ_ne_P: "Q \<noteq> P"
    using hcard by (auto simp: card_insert_if split: if_splits)
  have hQ_ne_R: "Q \<noteq> R"
    using hcard by (auto simp: card_insert_if split: if_splits)
  have hS_ne_P: "S \<noteq> P"
    using hcard by (auto simp: card_insert_if split: if_splits)
  have hS_ne_R: "S \<noteq> R"
    using hcard by (auto simp: card_insert_if split: if_splits)
  have hP_in_A1: "P \<in> A1"
    using hA1J by (by100 blast)
  have hR_in_A2: "R \<in> A2"
    using hA2J by (by100 blast)
  have hQ_not_A1: "Q \<notin> A1"
    using hA1J hQ hQ_ne_P by (by100 blast)
  have hQ_not_A2: "Q \<notin> A2"
    using hA2J hQ hQ_ne_R by (by100 blast)
  have hS_not_A1: "S \<notin> A1"
    using hA1J hS hS_ne_P by (by100 blast)
  have hS_not_A2: "S \<notin> A2"
    using hA2J hS hS_ne_R by (by100 blast)
  have hQ_not_A12: "Q \<notin> A1 \<union> A2"
    using hQ_not_A1 hQ_not_A2 by (by100 blast)
  have hS_not_A12: "S \<notin> A1 \<union> A2"
    using hS_not_A1 hS_not_A2 by (by100 blast)
  have hQ_not_cut: "Q \<notin> geotop_polygon_interior J - (A1 \<union> A2)"
    using polygon_interior_disjoint_polygon[OF hJ] hQ by (by100 blast)
  have hS_not_cut: "S \<notin> geotop_polygon_interior J - (A1 \<union> A2)"
    using polygon_interior_disjoint_polygon[OF hJ] hS by (by100 blast)
  have hA12_metric_separation:
      "\<exists>\<delta>>0. compact A1 \<and> compact A2
        \<and> closed A1 \<and> closed A2
        \<and> A1 \<noteq> {} \<and> A2 \<noteq> {}
        \<and> compact (A1 \<union> A2) \<and> closed (A1 \<union> A2)
        \<and> 0 < setdist A1 A2
        \<and> (\<forall>x\<in>A1. \<forall>y\<in>A2. \<delta> \<le> dist x y)"
  proof -
    obtain \<delta> where h\<delta>_pos: "0 < \<delta>"
      and h\<delta>_gap: "\<forall>x\<in>A1. \<forall>y\<in>A2. \<delta> \<le> dist x y"
      using geotop_disjoint_arcs_uniform_distance_gap_prefix[OF hA1 hA2 hA12]
      by (elim exE conjE)
    have hpack: "compact A1 \<and> compact A2
        \<and> closed A1 \<and> closed A2
        \<and> A1 \<noteq> {} \<and> A2 \<noteq> {}
        \<and> compact (A1 \<union> A2) \<and> closed (A1 \<union> A2)"
      using geotop_two_arcs_compact_closed_prefix[OF hA1 hA2] .
    have hsd: "0 < setdist A1 A2"
      by (rule geotop_disjoint_arcs_positive_setdist_prefix[OF hA1 hA2 hA12])
    show ?thesis
      using h\<delta>_pos h\<delta>_gap hpack hsd by (by100 blast)
  qed
  have hD44_fine_disk_carrier_avoids_A2:
      "\<exists>K m. geotop_is_complex K
        \<and> finite K
        \<and> geotop_polyhedron K =
            closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)
        \<and> (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}}) \<inter> A2 = {}"
  proof -
    obtain \<delta> where h\<delta>_pos: "0 < \<delta>"
      and h\<delta>_gap: "\<forall>x\<in>A1. \<forall>y\<in>A2. \<delta> \<le> dist x y"
      using hA12_metric_separation by (by100 blast)
    show ?thesis
      by (rule geotop_polygon_disk_fine_Sd_carrier_meeting_first_arc_misses_second_prefix
          [OF hJ h\<delta>_pos h\<delta>_gap])
  qed
  have hQ_S_two_arc_local_access:
      "\<exists>r U\<^sub>Q U\<^sub>S Q' S'.
        0 < r
        \<and> connected U\<^sub>Q
        \<and> connected U\<^sub>S
        \<and> U\<^sub>Q \<in> geotop_euclidean_topology
        \<and> U\<^sub>S \<in> geotop_euclidean_topology
        \<and> U\<^sub>Q \<subseteq> geotop_polygon_interior J - (A1 \<union> A2)
        \<and> U\<^sub>S \<subseteq> geotop_polygon_interior J - (A1 \<union> A2)
        \<and> U\<^sub>Q \<subseteq> ball Q r
        \<and> U\<^sub>S \<subseteq> ball S r
        \<and> ball Q r \<inter> ball S r = {}
        \<and> Q \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>Q
        \<and> S \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>S
        \<and> Q' \<in> U\<^sub>Q
        \<and> S' \<in> U\<^sub>S
        \<and> Q' \<in> geotop_polygon_interior J - (A1 \<union> A2)
        \<and> S' \<in> geotop_polygon_interior J - (A1 \<union> A2)
        \<and> U\<^sub>Q \<inter> U\<^sub>S = {}"
  proof -
    have hQ_ne_S: "Q \<noteq> S"
      using hcard by (auto simp: card_insert_if split: if_splits)
    obtain r where hr_pos: "0 < r"
      and hr_disj: "ball Q r \<inter> ball S r = {}"
      using geotop_distinct_points_disjoint_small_balls_prefix[OF hQ_ne_S]
      by (elim exE conjE)
    have hQ_ne_PR: "Q \<noteq> P \<and> Q \<noteq> R"
      using hQ_ne_P hQ_ne_R by (by100 blast)
    have hS_ne_PR: "S \<noteq> P \<and> S \<noteq> R"
      using hS_ne_P hS_ne_R by (by100 blast)
    obtain U\<^sub>Q Q' where hU\<^sub>Q_conn: "connected U\<^sub>Q"
      and hU\<^sub>Q_open: "U\<^sub>Q \<in> geotop_euclidean_topology"
      and hU\<^sub>Q_sub: "U\<^sub>Q \<subseteq> geotop_polygon_interior J - (A1 \<union> A2)"
      and hU\<^sub>Q_ball: "U\<^sub>Q \<subseteq> ball Q r"
      and hQ_front:
        "Q \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>Q"
      and hQ'_U\<^sub>Q: "Q' \<in> U\<^sub>Q"
      and hQ'_cut: "Q' \<in> geotop_polygon_interior J - (A1 \<union> A2)"
      using geotop_polygon_interior_minus_two_arcs_connected_frontier_witness_in_ball_prefix
          [OF hJ hQ hQ_ne_PR hA1 hA2 hA1J hA2J hr_pos]
      by (elim exE conjE)
    obtain U\<^sub>S S' where hU\<^sub>S_conn: "connected U\<^sub>S"
      and hU\<^sub>S_open: "U\<^sub>S \<in> geotop_euclidean_topology"
      and hU\<^sub>S_sub: "U\<^sub>S \<subseteq> geotop_polygon_interior J - (A1 \<union> A2)"
      and hU\<^sub>S_ball: "U\<^sub>S \<subseteq> ball S r"
      and hS_front:
        "S \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>S"
      and hS'_U\<^sub>S: "S' \<in> U\<^sub>S"
      and hS'_cut: "S' \<in> geotop_polygon_interior J - (A1 \<union> A2)"
      using geotop_polygon_interior_minus_two_arcs_connected_frontier_witness_in_ball_prefix
          [OF hJ hS hS_ne_PR hA1 hA2 hA1J hA2J hr_pos]
      by (elim exE conjE)
    have hU_disj: "U\<^sub>Q \<inter> U\<^sub>S = {}"
      using hU\<^sub>Q_ball hU\<^sub>S_ball hr_disj by (by100 blast)
    show ?thesis
      using hr_pos hU\<^sub>Q_conn hU\<^sub>S_conn hU\<^sub>Q_open hU\<^sub>S_open
        hU\<^sub>Q_sub hU\<^sub>S_sub hU\<^sub>Q_ball hU\<^sub>S_ball hr_disj
        hQ_front hS_front hQ'_U\<^sub>Q hS'_U\<^sub>S hQ'_cut hS'_cut hU_disj
      by (intro exI conjI)
  qed
  have hD44_component_transfer:
    "\<exists>C. Q \<in> geotop_frontier UNIV geotop_euclidean_topology C
       \<and> S \<in> geotop_frontier UNIV geotop_euclidean_topology C
       \<and> (\<exists>P'. P' \<in> geotop_polygon_interior J - (A1 \<union> A2) \<and>
           C = geotop_component_at UNIV geotop_euclidean_topology
                  (geotop_polygon_interior J - (A1 \<union> A2)) P')"
    (**
      Remaining Moise Theorem 4.4 regular-neighborhood component-transfer
      package.  Following the book, choose a fine brick decomposition whose
      bricks separate \<open>A1\<close> from \<open>A2\<close>, form the brick regular neighborhood
      of \<open>A1\<close> inside the closed polygonal disk, read the relevant frontier
      component as a 1-sphere with a broken-line subarc, obtain one component
      of \<open>geotop_polygon_interior J - (A1 \<union> A2)\<close> whose frontier contains the
      subarc endpoints, and then use cyclic order to transfer that component
      frontier statement to the prescribed opposite boundary points \<open>Q,S\<close>.

      The previous placeholder bundled the intermediate brick decomposition,
      regular-neighborhood manifold, frontier sphere, and endpoint-transfer
      facts as separate conjuncts.  The surrounding theorem only needs this
      final component-transfer conclusion, so the open obligation is kept as
      one exact Moise book package rather than five unrelated local goals. **)
    sorry
  show ?thesis
    using hD44_component_transfer by (by100 blast)
qed

(** from \<S>4 Theorem 4 (geotop.tex:931)
    LATEX VERSION: Let I, P, Q, R, S be as before, and let A_1 and A_2 be disjoint arcs in \<bar>I\<close>,
    with A_1 \<inter> Fr I = {P} and A_2 \<inter> Fr I = {R}. Then S and Q are in the frontier of the
    same component of I - (A_1 \<union> A_2). **)
theorem Theorem_GT_4_4:
  fixes J A1 A2 :: "(real^2) set" and P Q R S :: "real^2"
  assumes "geotop_is_polygon J"
  assumes "P \<in> J" "Q \<in> J" "R \<in> J" "S \<in> J"
  assumes "geotop_polygon_cyclic_order J P Q R S"
  assumes "card {P, Q, R, S} = 4"
  assumes "geotop_is_arc A1 (subspace_topology UNIV geotop_euclidean_topology A1)"
  assumes "geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2)"
  assumes "A1 \<inter> A2 = {}"
  assumes "A1 \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes "A2 \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes "A1 \<inter> J = {P}" "A2 \<inter> J = {R}"
  shows "\<exists>C. Q \<in> geotop_frontier UNIV geotop_euclidean_topology C
          \<and> S \<in> geotop_frontier UNIV geotop_euclidean_topology C
          \<and> (\<exists>P'. P' \<in> geotop_polygon_interior J - (A1 \<union> A2) \<and>
              C = geotop_component_at UNIV geotop_euclidean_topology
                     (geotop_polygon_interior J - (A1 \<union> A2)) P')"
  (** Moise proof sketch (geotop.tex:931-ff.): after reducing to the rectangular
      picture, choose a sufficiently fine brick-decomposition of the plane so that
      \<bar>I\<close> is a union of bricks and no brick meets both A\<^sub>1 and A\<^sub>2. Let N be the
      union of bricks meeting A\<^sub>1 and N' = N \<inter> \<bar>I\<close>. The component J' of Fr N'
      containing P is a 1-sphere. Its two boundary broken lines determine a
      sub-broken-line B with B \<inter> Fr I = {V,W}; V,W lie in the frontier of one
      component of I - (A\<^sub>1 \<union> A\<^sub>2). The cyclic order then transfers this frontier
      statement from V,W to Q,S. **)
proof -
  show ?thesis
    by (rule geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
        [OF assms])
qed


end
