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

lemma geotop_broken_line_connected_on_prefix:
  fixes B :: "(real^2) set"
  assumes hB: "geotop_is_broken_line B"
  shows "top1_connected_on B
    (subspace_topology UNIV geotop_euclidean_topology B)"
proof -
  have hB_arc: "geotop_is_arc B
      (subspace_topology UNIV geotop_euclidean_topology B)"
    using hB unfolding geotop_is_broken_line_def by (by100 blast)
  obtain \<gamma> :: "real \<Rightarrow> real^2" where h\<gamma>_arc: "arc \<gamma>"
    and h\<gamma>_img: "path_image \<gamma> = B"
    using geotop_is_arc_imp_HOL_arc[OF hB_arc] by (by100 blast)
  have h\<gamma>_path: "path \<gamma>"
    using h\<gamma>_arc unfolding arc_def by (by100 simp)
  have hB_conn_HOL: "connected B"
    using connected_path_image[OF h\<gamma>_path] h\<gamma>_img by (by100 simp)
  show ?thesis
    using hB_conn_HOL top1_connected_on_geotop_iff_connected by (by100 blast)
qed

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

lemma geotop_polygon_disk_fine_Sd_named_carrier_meeting_first_arc_misses_second_prefix:
  fixes J A1 A2 :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  assumes hA1_sub:
    "A1 \<subseteq> closure_on UNIV geotop_euclidean_topology
      (geotop_polygon_interior J)"
  assumes h\<delta>: "0 < \<delta>"
  assumes hgap: "\<forall>x\<in>A1. \<forall>y\<in>A2. \<delta> \<le> dist x y"
  shows "\<exists>K m N. geotop_is_complex K
      \<and> finite K
      \<and> geotop_polyhedron K =
          closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)
      \<and> N = (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}})
      \<and> A1 \<subseteq> N
      \<and> N \<inter> A2 = {}"
proof -
  obtain K m where hK: "geotop_is_complex K"
    and hKfin: "finite K"
    and hK_poly: "geotop_polyhedron K =
        closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
    and hcarrier_miss:
      "(\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}}) \<inter> A2 = {}"
    using geotop_polygon_disk_fine_Sd_carrier_meeting_first_arc_misses_second_prefix
        [OF hJ h\<delta> hgap]
    by (elim exE conjE)
  define N where "N = (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}})"
  have hsub: "geotop_is_subdivision (geotop_iterated_Sd m K) K"
    by (rule geotop_iterated_Sd_is_subdivision[OF hK hKfin])
  have hSd_poly:
      "geotop_polyhedron (geotop_iterated_Sd m K) =
        geotop_polyhedron K"
    using hsub unfolding geotop_is_subdivision_def by (by100 blast)
  have hA1_sub_Sd_poly:
      "A1 \<subseteq> geotop_polyhedron (geotop_iterated_Sd m K)"
    using hA1_sub hK_poly hSd_poly by (by100 simp)
  have hA1_sub_N: "A1 \<subseteq> N"
  proof
    fix x
    assume hx: "x \<in> A1"
    have hx_poly: "x \<in> geotop_polyhedron (geotop_iterated_Sd m K)"
      using hA1_sub_Sd_poly hx by (by100 blast)
    obtain B where hB: "B \<in> geotop_iterated_Sd m K" and hxB: "x \<in> B"
      using hx_poly unfolding geotop_polyhedron_def by (by100 blast)
    have hB_meets: "B \<inter> A1 \<noteq> {}"
      using hx hxB by (by100 blast)
    show "x \<in> N"
      unfolding N_def using hB hxB hB_meets by (by100 blast)
  qed
  have hN_miss: "N \<inter> A2 = {}"
    unfolding N_def by (rule hcarrier_miss)
  show ?thesis
    using hK hKfin hK_poly N_def hA1_sub_N hN_miss
    by (intro exI conjI)
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

lemma geotop_same_component_local_access_frontier_transfer_prefix:
  fixes U U\<^sub>Q U\<^sub>S :: "(real^2) set" and Q S Q' S' :: "real^2"
  assumes hUQ_conn: "connected U\<^sub>Q"
  assumes hUS_conn: "connected U\<^sub>S"
  assumes hUQ_sub: "U\<^sub>Q \<subseteq> U"
  assumes hUS_sub: "U\<^sub>S \<subseteq> U"
  assumes hQ'_UQ: "Q' \<in> U\<^sub>Q"
  assumes hS'_US: "S' \<in> U\<^sub>S"
  assumes hQ_front: "Q \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>Q"
  assumes hS_front: "S \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>S"
  assumes hQ_not_U: "Q \<notin> U"
  assumes hS_not_U: "S \<notin> U"
  assumes hS'_comp:
    "S' \<in> geotop_component_at UNIV geotop_euclidean_topology U Q'"
  shows "\<exists>C. Q \<in> geotop_frontier UNIV geotop_euclidean_topology C
          \<and> S \<in> geotop_frontier UNIV geotop_euclidean_topology C
          \<and> (\<exists>P'. P' \<in> U \<and>
              C = geotop_component_at UNIV geotop_euclidean_topology U P')"
  (**
    D44 packaging step: once Moise's regular-neighborhood argument has put the
    two local access witnesses in the same cut-open component, the frontier
    points carried by the connected local access sets transfer to that one
    ambient component. **)
proof -
  let ?C\<^sub>Q = "geotop_component_at UNIV geotop_euclidean_topology U Q'"
  let ?C\<^sub>S = "geotop_component_at UNIV geotop_euclidean_topology U S'"
  have hQ'_U: "Q' \<in> U"
    using hUQ_sub hQ'_UQ by (by100 blast)
  have hS'_U: "S' \<in> U"
    using hUS_sub hS'_US by (by100 blast)
  have hQ_front_CQ:
      "Q \<in> geotop_frontier UNIV geotop_euclidean_topology ?C\<^sub>Q"
    by (rule geotop_connected_subset_frontier_component_transfer_prefix
        [OF hUQ_conn hUQ_sub hQ'_UQ hQ_front hQ_not_U])
  have hS_front_CS:
      "S \<in> geotop_frontier UNIV geotop_euclidean_topology ?C\<^sub>S"
    by (rule geotop_connected_subset_frontier_component_transfer_prefix
        [OF hUS_conn hUS_sub hS'_US hS_front hS_not_U])
  have hTU: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have hS'_sing_conn:
      "top1_connected_on {S'}
        (subspace_topology UNIV geotop_euclidean_topology {S'})"
    by (rule top1_connected_on_singleton[OF hTU], simp)
  have hS'_CS: "S' \<in> ?C\<^sub>S"
    by (rule geotop_self_in_component_at[OF hS'_U hS'_sing_conn])
  have hcomponent_dichotomy:
      "?C\<^sub>Q = ?C\<^sub>S \<or> ?C\<^sub>Q \<inter> ?C\<^sub>S = {}"
    by (rule Theorem_GT_1_16[OF hTU subset_UNIV hQ'_U hS'_U])
  have hcomponent_meets: "?C\<^sub>Q \<inter> ?C\<^sub>S \<noteq> {}"
    using hS'_comp hS'_CS by (by100 blast)
  have hcomponent_eq: "?C\<^sub>Q = ?C\<^sub>S"
    using hcomponent_dichotomy hcomponent_meets by (by100 blast)
  have hS_front_CQ:
      "S \<in> geotop_frontier UNIV geotop_euclidean_topology ?C\<^sub>Q"
    using hS_front_CS hcomponent_eq by (by100 simp)
  show ?thesis
    using hQ_front_CQ hS_front_CQ hQ'_U by (intro exI conjI)
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
  have hD44_named_fine_disk_carrier:
      "\<exists>K m N. geotop_is_complex K
        \<and> finite K
        \<and> geotop_polyhedron K =
            closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)
        \<and> N = (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}})
        \<and> A1 \<subseteq> N
        \<and> N \<inter> A2 = {}"
  proof -
    obtain \<delta> where h\<delta>_pos: "0 < \<delta>"
      and h\<delta>_gap: "\<forall>x\<in>A1. \<forall>y\<in>A2. \<delta> \<le> dist x y"
      using hA12_metric_separation by (by100 blast)
    show ?thesis
      by (rule geotop_polygon_disk_fine_Sd_named_carrier_meeting_first_arc_misses_second_prefix
          [OF hJ hA1_sub h\<delta>_pos h\<delta>_gap])
  qed
  have hD44_named_fine_disk_carrier_avoids_A2_QS:
      "\<exists>K m N. geotop_is_complex K
        \<and> finite K
        \<and> geotop_polyhedron K =
            closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)
        \<and> N = (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}})
        \<and> A1 \<subseteq> N
        \<and> N \<inter> (A2 \<union> {Q, S}) = {}"
  proof -
    obtain \<delta>\<^sub>0 where h\<delta>\<^sub>0_pos: "0 < \<delta>\<^sub>0"
      and h\<delta>\<^sub>0_gap: "\<forall>x\<in>A1. \<forall>y\<in>A2. \<delta>\<^sub>0 \<le> dist x y"
      using hA12_metric_separation by (by100 blast)
    have hA1_compact: "compact A1"
      using hA12_metric_separation by (by100 blast)
    have hA1_closed: "closed A1"
      using hA12_metric_separation by (by100 blast)
    have hA1_nonempty: "A1 \<noteq> {}"
      using hA12_metric_separation by (by100 blast)
    have hA2_compact: "compact A2"
      using hA12_metric_separation by (by100 blast)
    have hA2_closed: "closed A2"
      using hA12_metric_separation by (by100 blast)
    have hF_compact: "compact (A2 \<union> {Q, S})"
      using hA2_compact by (by100 simp)
    have hF_closed: "closed (A2 \<union> {Q, S})"
      using hA2_closed by (by100 simp)
    have hF_nonempty: "A2 \<union> {Q, S} \<noteq> {}"
      by (by100 blast)
    have hA1F_disj: "A1 \<inter> (A2 \<union> {Q, S}) = {}"
      using hA12 hQ_not_A1 hS_not_A1 by (by100 blast)
    have hsdF_iff:
        "(0 < setdist A1 (A2 \<union> {Q, S})) =
          (A1 \<noteq> {} \<and> A2 \<union> {Q, S} \<noteq> {} \<and>
            A1 \<inter> (A2 \<union> {Q, S}) = {})"
      by (rule setdist_gt_0_compact_closed[OF hA1_compact hF_closed])
    have hsdF_pos: "0 < setdist A1 (A2 \<union> {Q, S})"
      using hsdF_iff hA1_nonempty hF_nonempty hA1F_disj by (by100 blast)
    define \<delta> where "\<delta> = min \<delta>\<^sub>0 (setdist A1 (A2 \<union> {Q, S}) / 2)"
    have h\<delta>_pos: "0 < \<delta>"
      unfolding \<delta>_def using h\<delta>\<^sub>0_pos hsdF_pos by (by100 simp)
    have h\<delta>_le_sdF: "\<delta> \<le> setdist A1 (A2 \<union> {Q, S})"
      unfolding \<delta>_def using h\<delta>\<^sub>0_pos hsdF_pos by (by100 simp)
    have h\<delta>_gapF: "\<forall>x\<in>A1. \<forall>y\<in>A2 \<union> {Q, S}. \<delta> \<le> dist x y"
      using h\<delta>_le_sdF le_setdist_iff[of \<delta> A1 "A2 \<union> {Q, S}"]
      by (by100 blast)
    show ?thesis
      by (rule geotop_polygon_disk_fine_Sd_named_carrier_meeting_first_arc_misses_second_prefix
          [OF hJ hA1_sub h\<delta>_pos h\<delta>_gapF])
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

      The named carrier package above now supplies the fine closed-disk brick
      neighborhood \<open>N\<close> with \<open>A1 \<subseteq> N\<close> and \<open>N \<inter> A2 = {}\<close>.  The remaining
      open book step starts from that carrier, restricts it to the closed
      polygonal disk, analyzes the frontier component through \<open>P\<close>, and uses
      the cyclic order of \<open>P,Q,R,S\<close> on \<open>J\<close> to transfer the component frontier
      to the opposite boundary points \<open>Q,S\<close>. **)
  proof -
    obtain K m N where hK_complex: "geotop_is_complex K"
      and hK_fin: "finite K"
      and hK_poly:
        "geotop_polyhedron K =
          closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
      and hN_def:
        "N = (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}})"
      and hA1_N: "A1 \<subseteq> N"
      and hN_A2_QS: "N \<inter> (A2 \<union> {Q, S}) = {}"
      using hD44_named_fine_disk_carrier_avoids_A2_QS
      by (elim exE conjE)
    have hN_A2_only: "N \<inter> A2 = {}"
      using hN_A2_QS by (by100 blast)
    have hQ_not_N: "Q \<notin> N"
      using hN_A2_QS by (by100 blast)
    have hS_not_N: "S \<notin> N"
      using hN_A2_QS by (by100 blast)
    have hSd_sub: "geotop_is_subdivision (geotop_iterated_Sd m K) K"
      by (rule geotop_iterated_Sd_is_subdivision[OF hK_complex hK_fin])
    have hSd_complex: "geotop_is_complex (geotop_iterated_Sd m K)"
      using hSd_sub unfolding geotop_is_subdivision_def by (by100 blast)
    have hSd_fin: "finite (geotop_iterated_Sd m K)"
      by (rule geotop_subdivision_of_finite_is_finite[OF hK_fin hSd_sub])
    have hSd_poly:
        "geotop_polyhedron (geotop_iterated_Sd m K) = geotop_polyhedron K"
      using hSd_sub unfolding geotop_is_subdivision_def by (by100 blast)
    have hN_sub_Sd_poly: "N \<subseteq> geotop_polyhedron (geotop_iterated_Sd m K)"
      unfolding hN_def geotop_polyhedron_def by (by100 blast)
    have hN_sub_disk:
        "N \<subseteq> closure_on UNIV geotop_euclidean_topology
          (geotop_polygon_interior J)"
      using hN_sub_Sd_poly hSd_poly hK_poly by (by100 simp)
    have hSd_compact_all: "\<forall>B\<in>geotop_iterated_Sd m K. compact B"
    proof
      fix B
      assume hB: "B \<in> geotop_iterated_Sd m K"
      have hB_simplex: "geotop_is_simplex B"
        using geotop_is_complex_simplex[OF hSd_complex] hB by (by100 blast)
      show "compact B"
        by (rule geotop_simplex_compact[OF hB_simplex])
    qed
    have hSd_closed_all: "\<forall>B\<in>geotop_iterated_Sd m K. closed B"
    proof
      fix B
      assume hB: "B \<in> geotop_iterated_Sd m K"
      have hB_compact: "compact B"
        using hSd_compact_all hB by (by100 blast)
      show "closed B"
        by (rule compact_imp_closed[OF hB_compact])
    qed
    have hN_index_fin:
        "finite {B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}}"
      using hSd_fin by (by100 simp)
    have hN_index_compact:
        "\<forall>B\<in>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}}. compact B"
      using hSd_compact_all by (by100 blast)
    have hN_compact: "compact N"
      unfolding hN_def
      by (rule compact_Union[OF hN_index_fin hN_index_compact])
    have hN_index_closed:
        "\<forall>B\<in>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}}. closed B"
      using hSd_closed_all by (by100 blast)
    have hN_closed: "closed N"
      unfolding hN_def
      by (rule closed_Union[OF hN_index_fin hN_index_closed])
    have hN_connected_HOL: "connected N"
    proof -
      let ?I = "{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}}"
      let ?S = "(\<lambda>B. A1 \<union> B) ` ?I"
      have hA1_connected: "connected A1"
      proof -
        obtain \<gamma> :: "real \<Rightarrow> real^2" where h\<gamma>_arc: "arc \<gamma>"
          and h\<gamma>_img: "path_image \<gamma> = A1"
          using geotop_is_arc_imp_HOL_arc[OF hA1] by (by100 blast)
        have h\<gamma>_path: "path \<gamma>"
          using h\<gamma>_arc unfolding arc_def by (by100 simp)
        show ?thesis
          using connected_path_image[OF h\<gamma>_path] h\<gamma>_img by (by100 simp)
      qed
      have hS_connected: "\<And>T. T \<in> ?S \<Longrightarrow> connected T"
      proof -
        fix T
        assume hT: "T \<in> ?S"
        obtain B where hB_I: "B \<in> ?I" and hT_eq: "T = A1 \<union> B"
          using hT by (by100 blast)
        have hB_Sd: "B \<in> geotop_iterated_Sd m K"
          using hB_I by (by100 simp)
        have hB_meets_A1: "A1 \<inter> B \<noteq> {}"
          using hB_I by (by100 blast)
        have hB_simplex: "geotop_is_simplex B"
          using geotop_is_complex_simplex[OF hSd_complex] hB_Sd by (by100 blast)
        have hB_path_connected:
            "top1_path_connected_on B
              (subspace_topology UNIV geotop_euclidean_topology B)"
          by (rule Theorem_GT_1_3[OF hB_simplex])
        have hB_connected_top:
            "top1_connected_on B
              (subspace_topology UNIV geotop_euclidean_topology B)"
          by (rule top1_path_connected_on_geotop_imp_connected[OF hB_path_connected])
        have hB_connected: "connected B"
          using hB_connected_top top1_connected_on_geotop_iff_connected by (by100 blast)
        have hA1B_meet: "A1 \<inter> B \<noteq> {}"
          using hB_meets_A1 by (by100 blast)
        show "connected T"
          unfolding hT_eq
          by (rule connected_Un[OF hA1_connected hB_connected hA1B_meet])
      qed
      have hInter_nonempty: "\<Inter>?S \<noteq> {}"
      proof -
        have hP_all: "\<And>T. T \<in> ?S \<Longrightarrow> P \<in> T"
          using hP_in_A1 by (by100 blast)
        have "P \<in> \<Inter>?S"
          using hP_all by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      have hUnion_connected: "connected (\<Union>?S)"
        by (rule connected_Union[OF hS_connected hInter_nonempty])
      have hUnion_eq_N: "\<Union>?S = N"
      proof
        show "\<Union>?S \<subseteq> N"
        proof
          fix x
          assume hx: "x \<in> \<Union>?S"
          then obtain B where hB_I: "B \<in> ?I" and hxAB: "x \<in> A1 \<union> B"
            by (by100 blast)
          have hB_sub_N: "B \<subseteq> N"
            unfolding hN_def using hB_I by (by100 blast)
          show "x \<in> N"
            using hxAB hA1_N hB_sub_N by (by100 blast)
        qed
        show "N \<subseteq> \<Union>?S"
        proof
          fix x
          assume hxN: "x \<in> N"
          obtain B where hB_I: "B \<in> ?I" and hxB: "x \<in> B"
            using hxN unfolding hN_def by (by100 blast)
          have "x \<in> A1 \<union> B"
            using hxB by (by100 blast)
          thus "x \<in> \<Union>?S"
            using hB_I by (by100 blast)
        qed
      qed
      show ?thesis
        using hUnion_connected hUnion_eq_N by (by100 simp)
    qed
    have hN_connected:
        "top1_connected_on N
          (subspace_topology UNIV geotop_euclidean_topology N)"
      using hN_connected_HOL top1_connected_on_geotop_iff_connected by (by100 blast)
    define N\<^sub>I where
        "N\<^sub>I = N \<inter> closure_on UNIV geotop_euclidean_topology
          (geotop_polygon_interior J)"
    have hN\<^sub>I_eq_N: "N\<^sub>I = N"
      unfolding N\<^sub>I_def using hN_sub_disk by (by100 blast)
    have hN\<^sub>I_compact: "compact N\<^sub>I"
      using hN\<^sub>I_eq_N hN_compact by (by100 simp)
    have hN\<^sub>I_closed: "closed N\<^sub>I"
      using hN\<^sub>I_eq_N hN_closed by (by100 simp)
    have hN\<^sub>I_connected_HOL: "connected N\<^sub>I"
      using hN_connected_HOL hN\<^sub>I_eq_N by (by100 simp)
    have hN\<^sub>I_connected:
        "top1_connected_on N\<^sub>I
          (subspace_topology UNIV geotop_euclidean_topology N\<^sub>I)"
      using hN\<^sub>I_connected_HOL top1_connected_on_geotop_iff_connected by (by100 blast)
    define FrN\<^sub>I where
        "FrN\<^sub>I = geotop_frontier UNIV geotop_euclidean_topology N\<^sub>I"
    have hFrN\<^sub>I_HOL: "FrN\<^sub>I = frontier N\<^sub>I"
      unfolding FrN\<^sub>I_def by (rule geotop_frontier_UNIV_eq_frontier)
    have hFrN\<^sub>I_eq_N: "FrN\<^sub>I = geotop_frontier UNIV geotop_euclidean_topology N"
      unfolding FrN\<^sub>I_def using hN\<^sub>I_eq_N by (by100 simp)
    have hFrN\<^sub>I_sub_N\<^sub>I: "FrN\<^sub>I \<subseteq> N\<^sub>I"
      using hFrN\<^sub>I_HOL frontier_subset_closed[OF hN\<^sub>I_closed] by (by100 simp)
    have hFrN\<^sub>I_sub_N: "FrN\<^sub>I \<subseteq> N"
      using hFrN\<^sub>I_sub_N\<^sub>I hN\<^sub>I_eq_N by (by100 simp)
    have hFrN\<^sub>I_closed: "closed FrN\<^sub>I"
      using hFrN\<^sub>I_HOL frontier_closed by (by100 simp)
    have hFrN\<^sub>I_compact: "compact FrN\<^sub>I"
      by (rule closed_subset_compact[OF hN\<^sub>I_compact hFrN\<^sub>I_closed hFrN\<^sub>I_sub_N\<^sub>I])
    have hFrN\<^sub>I_A2_QS_disj: "FrN\<^sub>I \<inter> (A2 \<union> {Q, S}) = {}"
      using hFrN\<^sub>I_sub_N hN_A2_QS by (by100 blast)
    have hQ_not_FrN\<^sub>I: "Q \<notin> FrN\<^sub>I"
      using hFrN\<^sub>I_A2_QS_disj by (by100 blast)
    have hS_not_FrN\<^sub>I: "S \<notin> FrN\<^sub>I"
      using hFrN\<^sub>I_A2_QS_disj by (by100 blast)
    have hR_not_FrN\<^sub>I: "R \<notin> FrN\<^sub>I"
      using hR_in_A2 hFrN\<^sub>I_A2_QS_disj by (by100 blast)
    have hN\<^sub>I_sub_K_poly: "N\<^sub>I \<subseteq> geotop_polyhedron K"
      using hN\<^sub>I_eq_N hN_sub_disk hK_poly by (by100 simp)
    have hP_N\<^sub>I: "P \<in> N\<^sub>I"
      using hP_in_A1 hA1_N hN\<^sub>I_eq_N by (by100 blast)
    have hK_poly_frontier_eq_J: "frontier (geotop_polyhedron K) = J"
      by (rule geotop_polygon_disk_polyhedron_frontier_prefix[OF hJ hK_poly])
    have hP_front_K_poly: "P \<in> frontier (geotop_polyhedron K)"
      using hP hK_poly_frontier_eq_J by (by100 simp)
    have hP_not_int_K_poly: "P \<notin> interior (geotop_polyhedron K)"
      using hP_front_K_poly unfolding Elementary_Topology.frontier_def by (by100 blast)
    have hP_not_int_N\<^sub>I: "P \<notin> interior N\<^sub>I"
    proof
      assume hP_int: "P \<in> interior N\<^sub>I"
      have hinter_sub: "interior N\<^sub>I \<subseteq> interior (geotop_polyhedron K)"
        by (rule interior_mono[OF hN\<^sub>I_sub_K_poly])
      have hP_int_K: "P \<in> interior (geotop_polyhedron K)"
        using hinter_sub hP_int by (by100 blast)
      show False
        using hP_not_int_K_poly hP_int_K by (by100 blast)
    qed
    have hP_FrN\<^sub>I: "P \<in> FrN\<^sub>I"
    proof -
      have hP_cl: "P \<in> closure N\<^sub>I"
        using hP_N\<^sub>I closure_subset by (by100 blast)
      have hP_front: "P \<in> frontier N\<^sub>I"
        using hP_cl hP_not_int_N\<^sub>I
        unfolding Elementary_Topology.frontier_def by (by100 blast)
      show ?thesis
        using hFrN\<^sub>I_HOL hP_front by (by100 simp)
    qed
    define J\<^sub>N where
        "J\<^sub>N = geotop_component_at UNIV geotop_euclidean_topology FrN\<^sub>I P"
    have hP_J\<^sub>N: "P \<in> J\<^sub>N"
    proof -
      have hTU: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
        by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
      have hP_singleton_conn:
          "top1_connected_on {P}
            (subspace_topology UNIV geotop_euclidean_topology {P})"
        by (rule top1_connected_on_singleton[OF hTU], simp)
      show ?thesis
        unfolding J\<^sub>N_def
        by (rule geotop_self_in_component_at[OF hP_FrN\<^sub>I hP_singleton_conn])
    qed
    have hJ\<^sub>N_sub_FrN\<^sub>I: "J\<^sub>N \<subseteq> FrN\<^sub>I"
      unfolding J\<^sub>N_def geotop_component_at_def by (by100 blast)
    have hJ\<^sub>N_sub_N: "J\<^sub>N \<subseteq> N"
      using hJ\<^sub>N_sub_FrN\<^sub>I hFrN\<^sub>I_sub_N by (by100 blast)
    have hJ\<^sub>N_A2_QS_disj: "J\<^sub>N \<inter> (A2 \<union> {Q, S}) = {}"
      using hJ\<^sub>N_sub_N hN_A2_QS by (by100 blast)
    have hQ_not_J\<^sub>N: "Q \<notin> J\<^sub>N"
      using hJ\<^sub>N_A2_QS_disj by (by100 blast)
    have hS_not_J\<^sub>N: "S \<notin> J\<^sub>N"
      using hJ\<^sub>N_A2_QS_disj by (by100 blast)
    have hR_not_J\<^sub>N: "R \<notin> J\<^sub>N"
      using hR_in_A2 hJ\<^sub>N_A2_QS_disj by (by100 blast)
    have hJ\<^sub>N_eq_connected_component:
        "J\<^sub>N = connected_component_set FrN\<^sub>I P"
      unfolding J\<^sub>N_def by (rule geotop_component_at_UNIV_eq_connected_component_set)
    have hJ\<^sub>N_connected_HOL: "connected J\<^sub>N"
      using hJ\<^sub>N_eq_connected_component connected_connected_component by (by100 simp)
    have hJ\<^sub>N_connected:
        "top1_connected_on J\<^sub>N
          (subspace_topology UNIV geotop_euclidean_topology J\<^sub>N)"
      using hJ\<^sub>N_connected_HOL top1_connected_on_geotop_iff_connected by (by100 blast)
    have hJ\<^sub>N_nonempty: "J\<^sub>N \<noteq> {}"
      using hP_J\<^sub>N by (by100 blast)
    have hJ\<^sub>N_closedin_FrN\<^sub>I: "closedin (top_of_set FrN\<^sub>I) J\<^sub>N"
      using hJ\<^sub>N_eq_connected_component closedin_connected_component by (by100 simp)
    have hJ\<^sub>N_compact: "compact J\<^sub>N"
      by (rule closedin_compact[OF hFrN\<^sub>I_compact hJ\<^sub>N_closedin_FrN\<^sub>I])
    have hJ\<^sub>N_closed: "closed J\<^sub>N"
      by (rule compact_imp_closed[OF hJ\<^sub>N_compact])
    have hJ\<^sub>N_forbidden_setdist_pos:
        "0 < setdist J\<^sub>N (A2 \<union> {Q, S})"
    proof -
      have hA2_closed: "closed A2"
        using geotop_two_arcs_compact_closed_prefix[OF hA1 hA2] by (by100 blast)
      have hF_closed: "closed (A2 \<union> {Q, S})"
        using hA2_closed by (by100 simp)
      have hF_nonempty: "A2 \<union> {Q, S} \<noteq> {}"
        by (by100 blast)
      have hsd_iff:
          "(0 < setdist J\<^sub>N (A2 \<union> {Q, S})) =
            (J\<^sub>N \<noteq> {} \<and> A2 \<union> {Q, S} \<noteq> {} \<and>
              J\<^sub>N \<inter> (A2 \<union> {Q, S}) = {})"
        by (rule setdist_gt_0_compact_closed[OF hJ\<^sub>N_compact hF_closed])
      show ?thesis
        using hsd_iff hJ\<^sub>N_nonempty hF_nonempty hJ\<^sub>N_A2_QS_disj by (by100 blast)
    qed
    obtain \<delta>\<^sub>J\<^sub>N where h\<delta>\<^sub>J\<^sub>N_pos: "0 < \<delta>\<^sub>J\<^sub>N"
      and h\<delta>\<^sub>J\<^sub>N_gap:
        "\<forall>x\<in>J\<^sub>N. \<forall>y\<in>A2 \<union> {Q, S}. \<delta>\<^sub>J\<^sub>N \<le> dist x y"
    proof -
      define \<delta>\<^sub>J\<^sub>N where "\<delta>\<^sub>J\<^sub>N = setdist J\<^sub>N (A2 \<union> {Q, S}) / 2"
      have hpos: "0 < \<delta>\<^sub>J\<^sub>N"
        unfolding \<delta>\<^sub>J\<^sub>N_def using hJ\<^sub>N_forbidden_setdist_pos by (by100 simp)
      have hle: "\<delta>\<^sub>J\<^sub>N \<le> setdist J\<^sub>N (A2 \<union> {Q, S})"
        unfolding \<delta>\<^sub>J\<^sub>N_def using hJ\<^sub>N_forbidden_setdist_pos by (by100 simp)
      have hgap:
          "\<forall>x\<in>J\<^sub>N. \<forall>y\<in>A2 \<union> {Q, S}. \<delta>\<^sub>J\<^sub>N \<le> dist x y"
        using hle le_setdist_iff[of \<delta>\<^sub>J\<^sub>N J\<^sub>N "A2 \<union> {Q, S}"] by (by100 blast)
      show ?thesis
        using hpos hgap by (rule that)
    qed
    define K\<^sub>N where "K\<^sub>N = {\<sigma>\<in>geotop_iterated_Sd m K. \<sigma> \<subseteq> N}"
    have hK\<^sub>N_complex: "geotop_is_complex K\<^sub>N"
      unfolding K\<^sub>N_def
      by (rule geotop_complex_restrict_subset_is_complex[OF hSd_complex])
    have hK\<^sub>N_fin: "finite K\<^sub>N"
      unfolding K\<^sub>N_def using hSd_fin by (by100 simp)
    have hK\<^sub>N_poly: "geotop_polyhedron K\<^sub>N = N"
    proof -
      have hK\<^sub>N_poly_sub_N: "geotop_polyhedron K\<^sub>N \<subseteq> N"
        unfolding K\<^sub>N_def geotop_polyhedron_def by (by100 blast)
      have hcarrier_sub_N:
          "\<And>x. x \<in> N \<Longrightarrow>
            geotop_K_carrier (geotop_iterated_Sd m K) x \<subseteq> N"
      proof -
        fix x
        assume hxN: "x \<in> N"
        obtain B where hB_Sd: "B \<in> geotop_iterated_Sd m K"
          and hB_A1: "B \<inter> A1 \<noteq> {}"
          and hxB: "x \<in> B"
          using hxN unfolding hN_def by (by100 blast)
        have hB_sub_N: "B \<subseteq> N"
          unfolding hN_def using hB_Sd hB_A1 by (by100 blast)
        have hcarrier_sub_B:
            "geotop_K_carrier (geotop_iterated_Sd m K) x \<subseteq> B"
          by (rule geotop_K_carrier_subset_containing_simplex
              [OF hSd_complex hSd_fin hB_Sd hxB])
        show "geotop_K_carrier (geotop_iterated_Sd m K) x \<subseteq> N"
          using hcarrier_sub_B hB_sub_N by (by100 blast)
      qed
      have hN_sub_K\<^sub>N_poly:
          "N \<subseteq> geotop_polyhedron K\<^sub>N"
      proof -
        have "N \<subseteq>
            geotop_polyhedron {\<sigma>\<in>geotop_iterated_Sd m K. \<sigma> \<subseteq> N}"
          by (rule geotop_restrict_polyhedron_contains_if_carriers_subset_prefix
              [OF hSd_complex hSd_fin hN_sub_Sd_poly hcarrier_sub_N])
        thus ?thesis
          unfolding K\<^sub>N_def by (by100 simp)
      qed
      show ?thesis
        using hK\<^sub>N_poly_sub_N hN_sub_K\<^sub>N_poly by (by100 blast)
    qed
    have hK\<^sub>N_poly_connected:
        "top1_connected_on (geotop_polyhedron K\<^sub>N)
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron K\<^sub>N))"
      using hN_connected hK\<^sub>N_poly by (by100 simp)
    have hK\<^sub>N_connected: "geotop_complex_connected K\<^sub>N"
    proof -
      have hK\<^sub>N_poly_path_connected:
          "top1_path_connected_on (geotop_polyhedron K\<^sub>N)
            (subspace_topology UNIV geotop_euclidean_topology
              (geotop_polyhedron K\<^sub>N))"
        by (rule iffD2[OF Theorem_GT_1_12(2)[OF hK\<^sub>N_complex]
              hK\<^sub>N_poly_connected])
      show ?thesis
        by (rule iffD2[OF Theorem_GT_1_12(1)[OF hK\<^sub>N_complex]
              hK\<^sub>N_poly_path_connected])
    qed
    have hA1_not_subset_singleton:
        "\<And>x. \<not> A1 \<subseteq> {x}"
    proof
      fix x
      assume hsub: "A1 \<subseteq> {x}"
      obtain \<gamma> :: "real \<Rightarrow> real^2" where h\<gamma>_arc: "arc \<gamma>"
        and h\<gamma>_img: "path_image \<gamma> = A1"
        using geotop_is_arc_imp_HOL_arc[OF hA1] by (by100 blast)
      have h0_img: "\<gamma> 0 \<in> path_image \<gamma>"
        unfolding path_image_def by (rule image_eqI[where x = 0], simp_all)
      have h0A1: "\<gamma> 0 \<in> A1"
        by (subst h\<gamma>_img[symmetric], rule h0_img)
      have h1_img: "\<gamma> 1 \<in> path_image \<gamma>"
        unfolding path_image_def by (rule image_eqI[where x = 1], simp_all)
      have h1A1: "\<gamma> 1 \<in> A1"
        by (subst h\<gamma>_img[symmetric], rule h1_img)
      have h0_in_single: "\<gamma> 0 \<in> {x}"
        by (rule subsetD[OF hsub h0A1])
      have h0x: "\<gamma> 0 = x"
        by (rule singletonD[OF h0_in_single])
      have h1_in_single: "\<gamma> 1 \<in> {x}"
        by (rule subsetD[OF hsub h1A1])
      have h1x: "\<gamma> 1 = x"
        by (rule singletonD[OF h1_in_single])
      have hinj: "inj_on \<gamma> {0..1}"
        using h\<gamma>_arc unfolding arc_def by (by100 simp)
      have h01: "(0::real) \<in> {0..1}"
        by (by100 simp)
      have h11: "(1::real) \<in> {0..1}"
        by (by100 simp)
      have h\<gamma>01: "\<gamma> 0 = \<gamma> 1"
        by (subst h0x, rule h1x[symmetric])
      have "0 = (1::real)"
        by (rule inj_onD[OF hinj h\<gamma>01 h01 h11])
      thus False by (by100 simp)
    qed
    have hK\<^sub>N_vertex_incident_edge:
        "\<And>p. {p} \<in> K\<^sub>N \<Longrightarrow>
          \<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> p \<in> e"
    proof (rule ccontr)
      fix p
      assume hpK: "{p} \<in> K\<^sub>N"
        and hno: "\<not> (\<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> p \<in> e)"
      have hp_vertex: "p \<in> geotop_complex_vertices K\<^sub>N"
        using geotop_complex_vertices_eq_0_simplexes[OF hK\<^sub>N_complex] hpK
        by (by100 blast)
      have hsingle_top:
          "{p} \<in>
            subspace_topology UNIV geotop_euclidean_topology
              (geotop_polyhedron K\<^sub>N)"
        by (rule geotop_complex_no_incident_edge_vertex_open_singleton_prefix
            [OF hK\<^sub>N_complex hp_vertex hno])
      obtain U where hsingle_eq: "{p} = geotop_polyhedron K\<^sub>N \<inter> U"
        and hU_top: "U \<in> geotop_euclidean_topology"
        using hsingle_top unfolding subspace_topology_def by (by100 blast)
      have hU_open: "open U"
        using hU_top unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
        by (by100 simp)
      have hsingle_openin:
          "openin (top_of_set (geotop_polyhedron K\<^sub>N)) {p}"
        unfolding openin_open
        using hU_open hsingle_eq by (by100 blast)
      have hp_poly: "p \<in> geotop_polyhedron K\<^sub>N"
        unfolding geotop_polyhedron_def using hpK by (by100 blast)
      have hsingle_closedin:
          "closedin (top_of_set (geotop_polyhedron K\<^sub>N)) {p}"
      proof -
        have hclosed_single: "closed {p}"
          by (by100 simp)
        have hsingle_eq_poly:
            "{p} = geotop_polyhedron K\<^sub>N \<inter> {p}"
          using hp_poly by (by100 blast)
        show ?thesis
          unfolding closedin_closed
          using hclosed_single hsingle_eq_poly by (by100 blast)
      qed
      have hK\<^sub>N_poly_connected_HOL: "connected (geotop_polyhedron K\<^sub>N)"
        using hN_connected_HOL hK\<^sub>N_poly by (by100 simp)
      have hsingle_cases:
          "{p} = {} \<or> {p} = geotop_polyhedron K\<^sub>N"
        using connected_clopen[THEN iffD1, OF hK\<^sub>N_poly_connected_HOL]
          hsingle_openin hsingle_closedin by (by100 blast)
      have hpoly_single: "geotop_polyhedron K\<^sub>N = {p}"
        using hsingle_cases by (by100 blast)
      have hA1_sub_single: "A1 \<subseteq> {p}"
        using hA1_N hK\<^sub>N_poly hpoly_single by (by100 simp)
      show False
        using hA1_not_subset_singleton[of p] hA1_sub_single by (by100 blast)
    qed
    have hK\<^sub>N_poly_N\<^sub>I: "geotop_polyhedron K\<^sub>N = N\<^sub>I"
      using hK\<^sub>N_poly hN\<^sub>I_eq_N by (by100 simp)
    have hK\<^sub>N_edge_owned_by_Sd_2simplex:
        "\<And>e. e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          \<exists>\<sigma>\<in>geotop_iterated_Sd m K.
            geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
    proof -
      fix e
      assume heK\<^sub>N: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
      have heSd: "e \<in> geotop_iterated_Sd m K"
        using heK\<^sub>N unfolding K\<^sub>N_def by (by100 simp)
      have hSd_poly_disk:
          "geotop_polyhedron (geotop_iterated_Sd m K) =
            closure_on UNIV geotop_euclidean_topology
              (geotop_polygon_interior J)"
        using hSd_poly hK_poly by (by100 simp)
      show "\<exists>\<sigma>\<in>geotop_iterated_Sd m K.
          geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
        by (rule geotop_polygon_disk_edge_owned_by_2simplex_prefix
            [OF hJ hSd_complex hSd_poly_disk heSd hedge])
    qed
    have hK\<^sub>N_Sd_owner_meeting_A1_count_ge1:
        "\<And>e \<sigma>. e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          \<sigma> \<in> geotop_iterated_Sd m K \<Longrightarrow>
          geotop_simplex_dim \<sigma> 2 \<Longrightarrow>
          geotop_is_face e \<sigma> \<Longrightarrow>
          \<sigma> \<inter> A1 \<noteq> {} \<Longrightarrow>
          card {\<tau>\<in>K\<^sub>N. geotop_simplex_dim \<tau> 2
            \<and> geotop_is_face e \<tau>} \<ge> 1"
    proof -
      fix e \<sigma>
      assume heK\<^sub>N: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
        and h\<sigma>Sd: "\<sigma> \<in> geotop_iterated_Sd m K"
        and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
        and heface\<sigma>: "geotop_is_face e \<sigma>"
        and h\<sigma>A1: "\<sigma> \<inter> A1 \<noteq> {}"
      have h\<sigma>subN: "\<sigma> \<subseteq> N"
        unfolding hN_def using h\<sigma>Sd h\<sigma>A1 by (by100 blast)
      have h\<sigma>K\<^sub>N: "\<sigma> \<in> K\<^sub>N"
        unfolding K\<^sub>N_def using h\<sigma>Sd h\<sigma>subN by (by100 simp)
      let ?F = "{\<tau>\<in>K\<^sub>N. geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>}"
      have hF_sub: "?F \<subseteq> K\<^sub>N"
        by (by100 blast)
      have hF_fin: "finite ?F"
        by (rule finite_subset[OF hF_sub hK\<^sub>N_fin])
      have h\<sigma>F: "\<sigma> \<in> ?F"
        using h\<sigma>K\<^sub>N h\<sigma>2 heface\<sigma> by (by100 blast)
      have hF_ne: "?F \<noteq> {}"
        using h\<sigma>F by (by100 blast)
      have hcard_pos_iff: "(0 < card ?F) = (?F \<noteq> {} \<and> finite ?F)"
        by (rule card_gt_0_iff)
      have hcard_pos: "0 < card ?F"
        using hcard_pos_iff hF_fin hF_ne by (by100 blast)
      show "card ?F \<ge> 1"
        using hcard_pos by (by100 linarith)
    qed
    have hK\<^sub>N_edge_rel_interior_incident_count_ge1:
        "\<And>e p. e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          p \<in> rel_interior e \<Longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} \<ge> 1"
    proof -
      fix e p
      assume heK\<^sub>N: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hp_rel: "p \<in> rel_interior e"
      have heSd: "e \<in> geotop_iterated_Sd m K"
        using heK\<^sub>N unfolding K\<^sub>N_def by (by100 simp)
      have he_sub_N: "e \<subseteq> N"
        using heK\<^sub>N unfolding K\<^sub>N_def by (by100 simp)
      have hp_e: "p \<in> e"
        using hp_rel rel_interior_subset by (by100 blast)
      have hpN: "p \<in> N"
        using he_sub_N hp_e by (by100 blast)
      obtain B where hB_Sd: "B \<in> geotop_iterated_Sd m K"
        and hB_A1: "B \<inter> A1 \<noteq> {}"
        and hpB: "p \<in> B"
        using hpN unfolding hN_def by (by100 blast)
      have hcarrier_eq_e:
          "geotop_K_carrier (geotop_iterated_Sd m K) p = e"
        by (rule geotop_K_carrier_eq[OF hSd_complex heSd hp_rel])
      have hcarrier_sub_B:
          "geotop_K_carrier (geotop_iterated_Sd m K) p \<subseteq> B"
        by (rule geotop_K_carrier_subset_containing_simplex
            [OF hSd_complex hSd_fin hB_Sd hpB])
      have he_sub_B: "e \<subseteq> B"
        using hcarrier_eq_e hcarrier_sub_B by (by100 simp)
      have hface_eB: "geotop_is_face e B"
        by (rule geotop_complex_subset_simplex_face_prefix
            [OF hSd_complex heSd hB_Sd he_sub_B])
      have hB_simplex: "geotop_is_simplex B"
        using geotop_is_complex_simplex[OF hSd_complex] hB_Sd by (by100 blast)
      obtain n where hBdim: "geotop_simplex_dim B n"
        using hB_simplex unfolding geotop_is_simplex_def geotop_simplex_dim_def
        by (by100 blast)
      have hn_le2: "n \<le> 2"
        by (rule geotop_simplex_dim_le_2_R2_prefix[OF hBdim])
      show "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} \<ge> 1"
      proof (cases "n = 2")
        case True
        have hB2: "geotop_simplex_dim B 2"
          using hBdim True by (by100 simp)
        show ?thesis
          by (rule hK\<^sub>N_Sd_owner_meeting_A1_count_ge1
              [OF heK\<^sub>N hedge hB_Sd hB2 hface_eB hB_A1])
      next
        case False
        have hn_le1: "n \<le> 1"
          using hn_le2 False by (by100 linarith)
        obtain k where hk_le_n: "k \<le> n"
          and hedimk: "geotop_simplex_dim e k"
          using geotop_face_dim_le_prefix[OF hBdim hface_eB] by (by100 blast)
        have hedim1: "geotop_simplex_dim e 1"
          using hedge unfolding geotop_is_edge_def by (by100 simp)
        have hk_eq1: "k = 1"
          by (rule geotop_simplex_dim_unique[OF hedimk hedim1])
        have hn1: "n = 1"
          using hk_le_n hk_eq1 hn_le1 by (by100 linarith)
        have hBedge: "geotop_is_edge B"
          using hBdim hn1 unfolding geotop_is_edge_def by (by100 simp)
        have he_eq_B: "e = B"
          by (rule geotop_edge_face_of_edge_eq_prefix[OF hedge hBedge hface_eB])
        obtain \<sigma> where h\<sigma>Sd: "\<sigma> \<in> geotop_iterated_Sd m K"
          and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
          and heface\<sigma>: "geotop_is_face e \<sigma>"
          using hK\<^sub>N_edge_owned_by_Sd_2simplex[OF heK\<^sub>N hedge]
          by (by100 blast)
        have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
          by (rule geotop_is_face_imp_subset_prefix[OF heface\<sigma>])
        have he_A1: "e \<inter> A1 \<noteq> {}"
          using hB_A1 he_eq_B by (by100 simp)
        have h\<sigma>A1: "\<sigma> \<inter> A1 \<noteq> {}"
          using he_sub_\<sigma> he_A1 by (by100 blast)
        show ?thesis
          by (rule hK\<^sub>N_Sd_owner_meeting_A1_count_ge1
              [OF heK\<^sub>N hedge h\<sigma>Sd h\<sigma>2 heface\<sigma> h\<sigma>A1])
      qed
    qed
    have hK\<^sub>N_edge_incident_2faces_card_le2:
        "\<And>e. e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
    proof -
      fix e
      assume heK: "e \<in> K\<^sub>N" and hedge: "geotop_is_edge e"
      let ?F = "{\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
      show "card ?F \<le> 2"
      proof (rule ccontr)
        assume hnot: "\<not> card ?F \<le> 2"
        have hge3: "3 \<le> card ?F"
          using hnot by (by100 linarith)
        obtain W where hW_sub: "W \<subseteq> ?F" and hW_card: "card W = 3"
          by (rule obtain_subset_with_card_n[OF hge3])
        have hW_three:
            "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. W = {\<sigma>1, \<sigma>2, \<sigma>3}
              \<and> \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3"
          by (rule iffD1[OF card_3_iff hW_card])
        obtain \<sigma>1 \<sigma>2 \<sigma>3 where hW_eq: "W = {\<sigma>1, \<sigma>2, \<sigma>3}"
          and h12: "\<sigma>1 \<noteq> \<sigma>2"
          and h23: "\<sigma>2 \<noteq> \<sigma>3"
          and h13: "\<sigma>1 \<noteq> \<sigma>3"
          using hW_three by (elim exE conjE)
        have h\<sigma>1F: "\<sigma>1 \<in> ?F"
          using hW_sub hW_eq by (by100 blast)
        have h\<sigma>2F: "\<sigma>2 \<in> ?F"
          using hW_sub hW_eq by (by100 blast)
        have h\<sigma>3F: "\<sigma>3 \<in> ?F"
          using hW_sub hW_eq by (by100 blast)
        have h\<sigma>1K: "\<sigma>1 \<in> K\<^sub>N"
          using h\<sigma>1F by (by100 simp)
        have h\<sigma>1dim: "geotop_simplex_dim \<sigma>1 2"
          using h\<sigma>1F by (by100 simp)
        have h\<sigma>1face: "geotop_is_face e \<sigma>1"
          using h\<sigma>1F by (by100 simp)
        have h\<sigma>2K: "\<sigma>2 \<in> K\<^sub>N"
          using h\<sigma>2F by (by100 simp)
        have h\<sigma>2dim: "geotop_simplex_dim \<sigma>2 2"
          using h\<sigma>2F by (by100 simp)
        have h\<sigma>2face: "geotop_is_face e \<sigma>2"
          using h\<sigma>2F by (by100 simp)
        have h\<sigma>3K: "\<sigma>3 \<in> K\<^sub>N"
          using h\<sigma>3F by (by100 simp)
        have h\<sigma>3dim: "geotop_simplex_dim \<sigma>3 2"
          using h\<sigma>3F by (by100 simp)
        have h\<sigma>3face: "geotop_is_face e \<sigma>3"
          using h\<sigma>3F by (by100 simp)
        show False
          by (rule geotop_complex_no_three_2simplexes_share_edge_prefix
              [OF hK\<^sub>N_complex hedge h12 h23 h13 h\<sigma>1K h\<sigma>1dim h\<sigma>1face
                h\<sigma>2K h\<sigma>2dim h\<sigma>2face h\<sigma>3K h\<sigma>3dim h\<sigma>3face])
      qed
    qed
    have hK\<^sub>N_edge_incident_2faces_one_or_two_cases:
        "\<And>e. e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 1
          \<Longrightarrow>
          (\<exists>!\<sigma>. \<sigma> \<in> K\<^sub>N \<and> geotop_simplex_dim \<sigma> 2 \<and>
            geotop_is_face e \<sigma>)
          \<or> (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
            \<and> \<sigma> \<in> K\<^sub>N \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
            \<and> \<tau> \<in> K\<^sub>N \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
            \<and> {\<rho>\<in>K\<^sub>N. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} =
              {\<sigma>, \<tau>})"
    proof -
      fix e
      assume heK: "e \<in> K\<^sub>N" and hedge: "geotop_is_edge e"
        and hge1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}
            \<ge> 1"
      have hle2:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}
            \<le> 2"
        by (rule hK\<^sub>N_edge_incident_2faces_card_le2[OF heK hedge])
      show
          "(\<exists>!\<sigma>. \<sigma> \<in> K\<^sub>N \<and> geotop_simplex_dim \<sigma> 2 \<and>
            geotop_is_face e \<sigma>)
          \<or> (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
            \<and> \<sigma> \<in> K\<^sub>N \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
            \<and> \<tau> \<in> K\<^sub>N \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
            \<and> {\<rho>\<in>K\<^sub>N. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} =
              {\<sigma>, \<tau>})"
      proof -
        let ?F = "{\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
        have hcard_cases: "card ?F = 1 \<or> card ?F = 2"
          using hge1 hle2 by (by100 linarith)
        show ?thesis
        proof (rule disjE[OF hcard_cases])
          assume hcard1: "card ?F = 1"
          obtain \<sigma> where hF_eq: "?F = {\<sigma>}"
            by (rule card_1_singletonE[OF hcard1])
          have h\<sigma>F: "\<sigma> \<in> ?F"
            using hF_eq by (by100 simp)
          have h\<sigma>K: "\<sigma> \<in> K\<^sub>N"
            using h\<sigma>F by (by100 simp)
          have h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
            using h\<sigma>F by (by100 simp)
          have h\<sigma>face: "geotop_is_face e \<sigma>"
            using h\<sigma>F by (by100 simp)
          have huniq:
              "\<forall>\<tau>. \<tau> \<in> K\<^sub>N \<and> geotop_simplex_dim \<tau> 2
                \<and> geotop_is_face e \<tau> \<longrightarrow> \<tau> = \<sigma>"
          proof (intro allI impI)
            fix \<tau>
            assume h\<tau>:
              "\<tau> \<in> K\<^sub>N \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>"
            have h\<tau>F: "\<tau> \<in> ?F"
              using h\<tau> by (by100 simp)
            show "\<tau> = \<sigma>"
              using hF_eq h\<tau>F by (by100 simp)
          qed
          have hone: "\<exists>!\<tau>. \<tau> \<in> K\<^sub>N \<and> geotop_simplex_dim \<tau> 2
              \<and> geotop_is_face e \<tau>"
          proof (rule ex1I[of _ \<sigma>])
            show "\<sigma> \<in> K\<^sub>N \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
              using h\<sigma>K h\<sigma>2 h\<sigma>face by (by100 simp)
          next
            fix \<tau>
            assume h\<tau>:
              "\<tau> \<in> K\<^sub>N \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>"
            show "\<tau> = \<sigma>"
              using huniq h\<tau> by (by100 simp)
          qed
          show ?thesis
            using hone by (rule disjI1)
        next
          assume hcard2: "card ?F = 2"
          have hcard2_ex:
              "\<exists>\<sigma> \<tau>. ?F = {\<sigma>, \<tau>} \<and> \<sigma> \<noteq> \<tau>"
            by (rule iffD1[OF card_2_iff hcard2])
          obtain \<sigma> \<tau> where hF_eq: "?F = {\<sigma>, \<tau>}" and h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
            using hcard2_ex by (elim exE conjE)
          have h\<sigma>F: "\<sigma> \<in> ?F"
            using hF_eq by (by100 simp)
          have h\<tau>F: "\<tau> \<in> ?F"
            using hF_eq by (by100 simp)
          have h\<sigma>K: "\<sigma> \<in> K\<^sub>N"
            using h\<sigma>F by (by100 simp)
          have h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
            using h\<sigma>F by (by100 simp)
          have h\<sigma>face: "geotop_is_face e \<sigma>"
            using h\<sigma>F by (by100 simp)
          have h\<tau>K: "\<tau> \<in> K\<^sub>N"
            using h\<tau>F by (by100 simp)
          have h\<tau>2: "geotop_simplex_dim \<tau> 2"
            using h\<tau>F by (by100 simp)
          have h\<tau>face: "geotop_is_face e \<tau>"
            using h\<tau>F by (by100 simp)
          show ?thesis
          proof (rule disjI2)
            show "\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
              \<and> \<sigma> \<in> K\<^sub>N \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
              \<and> \<tau> \<in> K\<^sub>N \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
              \<and> ?F = {\<sigma>, \<tau>}"
              using h\<sigma>\<tau> h\<sigma>K h\<sigma>2 h\<sigma>face h\<tau>K h\<tau>2 h\<tau>face hF_eq
              by (intro exI conjI)
          qed
        qed
      qed
    qed
    have hFrN\<^sub>I_frontier_K\<^sub>N_poly:
        "FrN\<^sub>I = frontier (geotop_polyhedron K\<^sub>N)"
      using hFrN\<^sub>I_HOL hK\<^sub>N_poly_N\<^sub>I by (by100 simp)
    have hK\<^sub>N_two_incident_edge_rel_interior_subset_interior_N:
        "\<And>e. e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2
          \<Longrightarrow> rel_interior e \<subseteq> interior N"
    proof -
      fix e
      assume heK: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hcard2:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
      let ?F = "{\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
      obtain \<sigma> \<tau> where hF_eq: "?F = {\<sigma>, \<tau>}" and h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
      proof -
        have hex: "\<exists>a b. ?F = {a, b} \<and> a \<noteq> b"
          by (rule iffD1[OF card_2_iff hcard2])
        obtain a b where hab: "?F = {a, b} \<and> a \<noteq> b"
          using hex by (elim exE)
        have hF: "?F = {a, b}"
          using hab by (by100 simp)
        have hab_ne: "a \<noteq> b"
          using hab by (by100 simp)
        show ?thesis
          by (rule that[OF hF hab_ne])
      qed
      have h\<sigma>F: "\<sigma> \<in> ?F"
      proof -
        have "\<sigma> \<in> {\<sigma>, \<tau>}"
          by (by100 simp)
        thus ?thesis
          using hF_eq by (by100 simp)
      qed
      have h\<tau>F: "\<tau> \<in> ?F"
      proof -
        have "\<tau> \<in> {\<sigma>, \<tau>}"
          by (by100 simp)
        thus ?thesis
          using hF_eq by (by100 simp)
      qed
      have h\<sigma>K: "\<sigma> \<in> K\<^sub>N"
        using h\<sigma>F by (by100 blast)
      have h\<tau>K: "\<tau> \<in> K\<^sub>N"
        using h\<tau>F by (by100 blast)
      have h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
        using h\<sigma>F by (by100 blast)
      have h\<tau>2: "geotop_simplex_dim \<tau> 2"
        using h\<tau>F by (by100 blast)
      have h\<sigma>face: "geotop_is_face e \<sigma>"
        using h\<sigma>F by (by100 blast)
      have h\<tau>face: "geotop_is_face e \<tau>"
        using h\<tau>F by (by100 blast)
      have hrel_int_union: "rel_interior e \<subseteq> interior (\<sigma> \<union> \<tau>)"
        by (rule geotop_complex_two_2simplex_shared_edge_rel_interior_subset_HOL_interior_union_prefix
            [OF hK\<^sub>N_complex h\<sigma>K h\<tau>K h\<sigma>2 h\<tau>2 h\<sigma>\<tau> h\<sigma>face h\<tau>face hedge])
      have hunion_sub_K\<^sub>N: "\<sigma> \<union> \<tau> \<subseteq> geotop_polyhedron K\<^sub>N"
      proof
        fix x
        assume hx: "x \<in> \<sigma> \<union> \<tau>"
        show "x \<in> geotop_polyhedron K\<^sub>N"
        proof (cases "x \<in> \<sigma>")
          case True
          show ?thesis
            unfolding geotop_polyhedron_def using h\<sigma>K True by (by100 blast)
        next
          case False
          have "x \<in> \<tau>"
            using hx False by (by100 blast)
          show ?thesis
            unfolding geotop_polyhedron_def using h\<tau>K \<open>x \<in> \<tau>\<close> by (by100 blast)
        qed
      qed
      have hrel_int_K\<^sub>N:
          "rel_interior e \<subseteq> interior (geotop_polyhedron K\<^sub>N)"
      proof -
        have hinter_sub:
            "interior (\<sigma> \<union> \<tau>) \<subseteq> interior (geotop_polyhedron K\<^sub>N)"
          by (rule interior_mono[OF hunion_sub_K\<^sub>N])
        show ?thesis
          using hrel_int_union hinter_sub by (by100 blast)
      qed
      show "rel_interior e \<subseteq> interior N"
        using hrel_int_K\<^sub>N hK\<^sub>N_poly by (by100 simp)
    qed
    have hK\<^sub>N_two_incident_edge_rel_interior_disj_FrN\<^sub>I:
        "\<And>e. e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2
          \<Longrightarrow> rel_interior e \<inter> FrN\<^sub>I = {}"
    proof -
      fix e
      assume heK: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hcard2:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
      have hrel_int: "rel_interior e \<subseteq> interior N"
        by (rule hK\<^sub>N_two_incident_edge_rel_interior_subset_interior_N
            [OF heK hedge hcard2])
      show "rel_interior e \<inter> FrN\<^sub>I = {}"
      proof (rule ccontr)
        assume hne: "rel_interior e \<inter> FrN\<^sub>I \<noteq> {}"
        obtain x where hx: "x \<in> rel_interior e \<inter> FrN\<^sub>I"
          using hne by (by100 blast)
        have hx_int: "x \<in> interior N"
          using hx hrel_int by (by100 blast)
        have hx_front: "x \<in> frontier N"
          using hx hFrN\<^sub>I_HOL hN\<^sub>I_eq_N by (by100 simp)
        have hx_not_int: "x \<notin> interior N"
          using hx_front unfolding Elementary_Topology.frontier_def by (by100 blast)
        show False
          using hx_int hx_not_int by (by100 blast)
      qed
    qed
    have hK\<^sub>N_edge_frontier_rel_interior_not_two_incident:
        "\<And>e p. e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          p \<in> rel_interior e \<Longrightarrow> p \<in> FrN\<^sub>I \<Longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<noteq> 2"
    proof -
      fix e p
      assume heK: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hp_rel: "p \<in> rel_interior e"
        and hp_Fr: "p \<in> FrN\<^sub>I"
      show "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<noteq> 2"
      proof
        assume hcard2:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
        have hdisj: "rel_interior e \<inter> FrN\<^sub>I = {}"
          by (rule hK\<^sub>N_two_incident_edge_rel_interior_disj_FrN\<^sub>I
              [OF heK hedge hcard2])
        show False
          using hp_rel hp_Fr hdisj by (by100 blast)
      qed
    qed
    have hK\<^sub>N_frontier_carrier_dim_le1:
        "\<And>p. p \<in> FrN\<^sub>I \<Longrightarrow>
          \<exists>n\<le>1. geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) n"
    proof -
      fix p
      assume hp_Fr: "p \<in> FrN\<^sub>I"
      have hpN: "p \<in> N"
        using hp_Fr hFrN\<^sub>I_sub_N by (by100 blast)
      have hp_poly: "p \<in> geotop_polyhedron K\<^sub>N"
        using hpN hK\<^sub>N_poly by (by100 simp)
      have hcarrierK: "geotop_K_carrier K\<^sub>N p \<in> K\<^sub>N"
        by (rule geotop_K_carrier_in[OF hK\<^sub>N_complex hK\<^sub>N_fin hp_poly])
      have hp_rel:
          "p \<in> rel_interior (geotop_K_carrier K\<^sub>N p)"
        by (rule geotop_K_carrier_rel_interior[OF hK\<^sub>N_complex hK\<^sub>N_fin hp_poly])
      have hK\<^sub>N_simplices: "\<forall>\<sigma>\<in>K\<^sub>N. geotop_is_simplex \<sigma>"
        using hK\<^sub>N_complex unfolding geotop_is_complex_def by (by100 simp)
      have hcarrier_simplex: "geotop_is_simplex (geotop_K_carrier K\<^sub>N p)"
        by (rule bspec[OF hK\<^sub>N_simplices hcarrierK])
      obtain V m n where hVfin: "finite V"
        and hVcard: "card V = n + 1"
        and hnm: "n \<le> m"
        and hVgp: "geotop_general_position V m"
        and hcarrier_eq: "geotop_K_carrier K\<^sub>N p = geotop_convex_hull V"
        using hcarrier_simplex unfolding geotop_is_simplex_def by (elim exE conjE)
      have hdim:
          "geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) n"
        unfolding geotop_simplex_dim_def
        using hVfin hVcard hnm hVgp hcarrier_eq by (by100 blast)
      have hn_le2: "n \<le> 2"
        by (rule geotop_simplex_dim_le_2_R2_prefix[OF hdim])
      have hn_ne2: "n \<noteq> 2"
      proof
        assume hn2: "n = 2"
        have hdim2: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) 2"
          using hdim hn2 by (by100 simp)
        have hri_eq:
            "rel_interior (geotop_K_carrier K\<^sub>N p) =
              interior (geotop_K_carrier K\<^sub>N p)"
          using geotop_2simplex_HOL_interior_eq_rel_interior_prefix[OF hdim2]
          by (by100 simp)
        have hp_int_carrier: "p \<in> interior (geotop_K_carrier K\<^sub>N p)"
          using hp_rel hri_eq by (by100 simp)
        have hcarrier_sub_poly:
            "geotop_K_carrier K\<^sub>N p \<subseteq> geotop_polyhedron K\<^sub>N"
          using hcarrierK unfolding geotop_polyhedron_def by (by100 blast)
        have hinterior_sub:
            "interior (geotop_K_carrier K\<^sub>N p)
              \<subseteq> interior (geotop_polyhedron K\<^sub>N)"
          by (rule interior_mono[OF hcarrier_sub_poly])
        have hp_int_poly: "p \<in> interior (geotop_polyhedron K\<^sub>N)"
          using hp_int_carrier hinterior_sub by (by100 blast)
        have hp_front_poly: "p \<in> frontier (geotop_polyhedron K\<^sub>N)"
          using hp_Fr hFrN\<^sub>I_frontier_K\<^sub>N_poly by (by100 simp)
        have hp_not_int: "p \<notin> interior (geotop_polyhedron K\<^sub>N)"
          using hp_front_poly unfolding Elementary_Topology.frontier_def by (by100 blast)
        show False
          using hp_int_poly hp_not_int by (by100 blast)
      qed
      have hn_le1: "n \<le> 1"
        using hn_le2 hn_ne2 by (by100 linarith)
      show "\<exists>n\<le>1. geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) n"
        using hn_le1 hdim by (intro exI conjI)
    qed
    have hJ\<^sub>N_carrier_dim_le1:
        "\<And>p. p \<in> J\<^sub>N \<Longrightarrow>
          \<exists>n\<le>1. geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) n"
    proof -
      fix p
      assume hpJ: "p \<in> J\<^sub>N"
      have hp_Fr: "p \<in> FrN\<^sub>I"
        using hpJ hJ\<^sub>N_sub_FrN\<^sub>I by (by100 blast)
      show "\<exists>n\<le>1. geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) n"
        by (rule hK\<^sub>N_frontier_carrier_dim_le1[OF hp_Fr])
    qed
    have hJ\<^sub>N_carrier_dim0_singleton:
        "\<And>p. p \<in> J\<^sub>N \<Longrightarrow>
          geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) 0
          \<Longrightarrow> geotop_K_carrier K\<^sub>N p = {p}"
    proof -
      fix p
      assume hpJ: "p \<in> J\<^sub>N"
        and hdim0: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) 0"
      have hpN: "p \<in> N"
        using hpJ hJ\<^sub>N_sub_N by (by100 blast)
      have hp_poly: "p \<in> geotop_polyhedron K\<^sub>N"
        using hpN hK\<^sub>N_poly by (by100 simp)
      have hp_rel:
          "p \<in> rel_interior (geotop_K_carrier K\<^sub>N p)"
        by (rule geotop_K_carrier_rel_interior[OF hK\<^sub>N_complex hK\<^sub>N_fin hp_poly])
      have hp_carrier: "p \<in> geotop_K_carrier K\<^sub>N p"
        using hp_rel rel_interior_subset by (by100 blast)
      show "geotop_K_carrier K\<^sub>N p = {p}"
        by (rule geotop_0simplex_contains_point_eq_singleton_prefix
            [OF hdim0 hp_carrier])
    qed
    have hJ\<^sub>N_carrier_dim0_incident_edge:
        "\<And>p. p \<in> J\<^sub>N \<Longrightarrow>
          geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) 0
          \<Longrightarrow> \<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> p \<in> e"
    proof -
      fix p
      assume hpJ: "p \<in> J\<^sub>N"
        and hdim0: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) 0"
      have hpN: "p \<in> N"
        using hpJ hJ\<^sub>N_sub_N by (by100 blast)
      have hp_poly: "p \<in> geotop_polyhedron K\<^sub>N"
        using hpN hK\<^sub>N_poly by (by100 simp)
      have hcarrierK: "geotop_K_carrier K\<^sub>N p \<in> K\<^sub>N"
        by (rule geotop_K_carrier_in[OF hK\<^sub>N_complex hK\<^sub>N_fin hp_poly])
      have hcarrier_eq: "geotop_K_carrier K\<^sub>N p = {p}"
        by (rule hJ\<^sub>N_carrier_dim0_singleton[OF hpJ hdim0])
      have hpK: "{p} \<in> K\<^sub>N"
        using hcarrierK hcarrier_eq by (by100 simp)
      show "\<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> p \<in> e"
        by (rule hK\<^sub>N_vertex_incident_edge[OF hpK])
    qed
    have hFrN\<^sub>I_geotop_frontier_K\<^sub>N_poly:
        "FrN\<^sub>I =
          geotop_frontier UNIV geotop_euclidean_topology
            (geotop_polyhedron K\<^sub>N)"
      using hFrN\<^sub>I_frontier_K\<^sub>N_poly
        geotop_frontier_UNIV_eq_frontier[of "geotop_polyhedron K\<^sub>N"]
      by (by100 simp)
    have hJ\<^sub>N_sub_frontier_K\<^sub>N_poly:
        "J\<^sub>N \<subseteq> frontier (geotop_polyhedron K\<^sub>N)"
      using hJ\<^sub>N_sub_FrN\<^sub>I hFrN\<^sub>I_frontier_K\<^sub>N_poly by (by100 simp)
    have hP_front_K\<^sub>N_poly: "P \<in> frontier (geotop_polyhedron K\<^sub>N)"
      using hP_FrN\<^sub>I hFrN\<^sub>I_frontier_K\<^sub>N_poly by (by100 simp)
    have hA1_K\<^sub>N_poly: "A1 \<subseteq> geotop_polyhedron K\<^sub>N"
      using hA1_N hK\<^sub>N_poly by (by100 simp)
    have hP_K\<^sub>N_poly: "P \<in> geotop_polyhedron K\<^sub>N"
      using hP_in_A1 hA1_K\<^sub>N_poly by (by100 blast)
    have hQ_not_K\<^sub>N_poly: "Q \<notin> geotop_polyhedron K\<^sub>N"
      using hQ_not_N hK\<^sub>N_poly by (by100 simp)
    have hS_not_K\<^sub>N_poly: "S \<notin> geotop_polyhedron K\<^sub>N"
      using hS_not_N hK\<^sub>N_poly by (by100 simp)
    have hR_not_K\<^sub>N_poly: "R \<notin> geotop_polyhedron K\<^sub>N"
      using hR_in_A2 hN_A2_only hK\<^sub>N_poly by (by100 blast)
    define BdK\<^sub>N where "BdK\<^sub>N = geotop_comb_boundary K\<^sub>N 2"
    have hBdK\<^sub>N_sub_K\<^sub>N: "BdK\<^sub>N \<subseteq> K\<^sub>N"
    proof
      fix \<rho>
      assume h\<rho>: "\<rho> \<in> BdK\<^sub>N"
      let ?S = "{\<tau> \<in> K\<^sub>N. geotop_simplex_dim \<tau> (2 - 1) \<and>
          card {\<sigma> \<in> K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and>
            geotop_is_face \<tau> \<sigma>} = 1}"
      have hface_closed:
          "\<forall>\<sigma>\<in>K\<^sub>N. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K\<^sub>N"
        by (rule geotop_is_complex_face_closed[OF hK\<^sub>N_complex])
      have h\<rho>_cases:
          "\<rho> \<in> ?S \<union> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
        using h\<rho> unfolding BdK\<^sub>N_def geotop_comb_boundary_def by (by100 simp)
      show "\<rho> \<in> K\<^sub>N"
      proof (rule UnE[OF h\<rho>_cases])
        assume "\<rho> \<in> ?S"
        thus "\<rho> \<in> K\<^sub>N"
          by (by100 blast)
      next
        assume "\<rho> \<in> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
        then obtain \<tau> where h\<tau>S: "\<tau> \<in> ?S" and h\<rho>\<tau>: "geotop_is_face \<rho> \<tau>"
          by (by100 blast)
        have h\<tau>K\<^sub>N: "\<tau> \<in> K\<^sub>N"
          using h\<tau>S by (by100 blast)
        show "\<rho> \<in> K\<^sub>N"
          using hface_closed h\<tau>K\<^sub>N h\<rho>\<tau> by (by100 blast)
      qed
    qed
    have hBdK\<^sub>N_fin: "finite BdK\<^sub>N"
      by (rule finite_subset[OF hBdK\<^sub>N_sub_K\<^sub>N hK\<^sub>N_fin])
    have hBdK\<^sub>N_face_closed:
        "\<forall>\<sigma>\<in>BdK\<^sub>N. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> BdK\<^sub>N"
    proof (intro ballI allI impI)
      fix \<sigma> \<tau>
      assume h\<sigma>Bd: "\<sigma> \<in> BdK\<^sub>N"
        and h\<tau>\<sigma>: "geotop_is_face \<tau> \<sigma>"
      let ?S = "{\<eta> \<in> K\<^sub>N. geotop_simplex_dim \<eta> (2 - 1) \<and>
          card {\<omega> \<in> K\<^sub>N. geotop_simplex_dim \<omega> 2 \<and>
            geotop_is_face \<eta> \<omega>} = 1}"
      have h\<sigma>_cases:
          "\<sigma> \<in> ?S \<union> {\<rho>. \<exists>\<eta>\<in>?S. geotop_is_face \<rho> \<eta>}"
        using h\<sigma>Bd unfolding BdK\<^sub>N_def geotop_comb_boundary_def by (by100 simp)
      show "\<tau> \<in> BdK\<^sub>N"
      proof (rule UnE[OF h\<sigma>_cases])
        assume h\<sigma>S: "\<sigma> \<in> ?S"
        have "\<tau> \<in> {\<rho>. \<exists>\<eta>\<in>?S. geotop_is_face \<rho> \<eta>}"
          using h\<sigma>S h\<tau>\<sigma> by (by100 blast)
        thus "\<tau> \<in> BdK\<^sub>N"
          unfolding BdK\<^sub>N_def geotop_comb_boundary_def by (by100 simp)
      next
        assume "\<sigma> \<in> {\<rho>. \<exists>\<eta>\<in>?S. geotop_is_face \<rho> \<eta>}"
        then obtain \<eta> where h\<eta>S: "\<eta> \<in> ?S" and h\<sigma>\<eta>: "geotop_is_face \<sigma> \<eta>"
          by (by100 blast)
        have h\<tau>\<eta>: "geotop_is_face \<tau> \<eta>"
          by (rule geotop_is_face_trans_prefix[OF h\<tau>\<sigma> h\<sigma>\<eta>])
        have "\<tau> \<in> {\<rho>. \<exists>\<eta>\<in>?S. geotop_is_face \<rho> \<eta>}"
          using h\<eta>S h\<tau>\<eta> by (by100 blast)
        thus "\<tau> \<in> BdK\<^sub>N"
          unfolding BdK\<^sub>N_def geotop_comb_boundary_def by (by100 simp)
      qed
    qed
    have hBdK\<^sub>N_complex: "geotop_is_complex BdK\<^sub>N"
      by (rule geotop_complex_subset_is_complex
          [OF hK\<^sub>N_complex hBdK\<^sub>N_sub_K\<^sub>N hBdK\<^sub>N_face_closed])
    have hBdK\<^sub>N_1dim: "geotop_complex_is_1dim BdK\<^sub>N"
    proof -
      let ?S = "{\<tau> \<in> K\<^sub>N. geotop_simplex_dim \<tau> (2 - 1) \<and>
          card {\<sigma> \<in> K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and>
            geotop_is_face \<tau> \<sigma>} = 1}"
      show ?thesis
        unfolding geotop_complex_is_1dim_def
      proof
        fix \<rho>
        assume h\<rho>Bd: "\<rho> \<in> BdK\<^sub>N"
        have h\<rho>_cases:
            "\<rho> \<in> ?S \<union> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
          using h\<rho>Bd unfolding BdK\<^sub>N_def geotop_comb_boundary_def by (by100 simp)
        show "\<exists>n\<le>1. geotop_simplex_dim \<rho> n"
        proof (rule UnE[OF h\<rho>_cases])
          assume h\<rho>S: "\<rho> \<in> ?S"
          have h\<rho>1: "geotop_simplex_dim \<rho> 1"
            using h\<rho>S by (by100 simp)
          show "\<exists>n\<le>1. geotop_simplex_dim \<rho> n"
            using h\<rho>1 by (by100 blast)
        next
          assume "\<rho> \<in> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
          then obtain \<tau> where h\<tau>S: "\<tau> \<in> ?S"
            and h\<rho>\<tau>: "geotop_is_face \<rho> \<tau>"
            by (by100 blast)
          have h\<tau>1: "geotop_simplex_dim \<tau> 1"
            using h\<tau>S by (by100 simp)
          obtain k where hk_le: "k \<le> 1"
            and h\<rho>k: "geotop_simplex_dim \<rho> k"
            using geotop_face_dim_le_prefix[OF h\<tau>1 h\<rho>\<tau>] by (by100 blast)
          show "\<exists>n\<le>1. geotop_simplex_dim \<rho> n"
            using hk_le h\<rho>k by (by100 blast)
        qed
      qed
    qed
    have hBdK\<^sub>N_linear_graph: "geotop_is_linear_graph BdK\<^sub>N"
      by (rule geotop_complex_1dim_imp_linear_graph_prefix
          [OF hBdK\<^sub>N_complex hBdK\<^sub>N_1dim])
    have hBdK\<^sub>N_poly_compact: "compact (geotop_polyhedron BdK\<^sub>N)"
      by (rule geotop_complex_polyhedron_compact[OF hBdK\<^sub>N_complex hBdK\<^sub>N_fin])
    have hBdK\<^sub>N_poly_closed: "closed (geotop_polyhedron BdK\<^sub>N)"
      by (rule geotop_complex_polyhedron_closed[OF hBdK\<^sub>N_complex hBdK\<^sub>N_fin])
    have hBdK\<^sub>N_poly_sub_N: "geotop_polyhedron BdK\<^sub>N \<subseteq> N"
      using hBdK\<^sub>N_sub_K\<^sub>N hK\<^sub>N_poly unfolding geotop_polyhedron_def by (by100 blast)
    have hBdK\<^sub>N_one_incident_edge_subset_FrN\<^sub>I:
        "\<And>e. e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1
          \<Longrightarrow> e \<subseteq> FrN\<^sub>I"
    proof -
      fix e
      assume heK: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hcard1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
      obtain \<sigma> where hfaces:
          "{\<rho>\<in>K\<^sub>N. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>}"
        using hcard1 by (rule card_1_singletonE)
      have h\<sigma>in: "\<sigma> \<in> {\<rho>\<in>K\<^sub>N. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
        using hfaces by (by100 simp)
      have h\<sigma>K: "\<sigma> \<in> K\<^sub>N"
        using h\<sigma>in by (by100 simp)
      have h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
        using h\<sigma>in by (by100 simp)
      have h\<sigma>face: "geotop_is_face e \<sigma>"
        using h\<sigma>in by (by100 simp)
      have hrel_front:
          "rel_interior e \<subseteq> frontier (geotop_polyhedron K\<^sub>N)"
        by (rule geotop_unique_incident_edge_rel_interior_subset_polyhedron_frontier_prefix
            [OF hK\<^sub>N_complex heK hedge h\<sigma>K h\<sigma>2 h\<sigma>face hfaces])
      have hfront_closed: "closed (frontier (geotop_polyhedron K\<^sub>N))"
        by (rule frontier_closed)
      have hclosure_sub:
          "closure (rel_interior e) \<subseteq> frontier (geotop_polyhedron K\<^sub>N)"
        by (rule closure_minimal[OF hrel_front hfront_closed])
      have hclosure_e: "closure (rel_interior e) = e"
        by (rule geotop_edge_closure_rel_interior_prefix[OF hedge])
      have he_front: "e \<subseteq> frontier (geotop_polyhedron K\<^sub>N)"
        using hclosure_sub hclosure_e by (by100 simp)
      show "e \<subseteq> FrN\<^sub>I"
        using he_front hFrN\<^sub>I_frontier_K\<^sub>N_poly by (by100 simp)
    qed
    have hBdK\<^sub>N_edge_member_incident_count_one:
        "\<And>e. e \<in> BdK\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
    proof -
      fix e
      assume heBd: "e \<in> BdK\<^sub>N" and hedge: "geotop_is_edge e"
      let ?S = "{\<tau> \<in> K\<^sub>N. geotop_simplex_dim \<tau> (2 - 1) \<and>
          card {\<sigma> \<in> K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and>
            geotop_is_face \<tau> \<sigma>} = 1}"
      have he_cases:
          "e \<in> ?S \<union> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
        using heBd unfolding BdK\<^sub>N_def geotop_comb_boundary_def by (by100 simp)
      show "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
      proof (rule UnE[OF he_cases])
        assume heS: "e \<in> ?S"
        show ?thesis
          using heS by (by100 simp)
      next
        assume he_face_case: "e \<in> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
        obtain \<tau> where h\<tau>S: "\<tau> \<in> ?S" and he\<tau>: "geotop_is_face e \<tau>"
          using he_face_case by (by100 blast)
        have h\<tau>edge: "geotop_is_edge \<tau>"
          using h\<tau>S unfolding geotop_is_edge_def by (by100 simp)
        have he_eq: "e = \<tau>"
          by (rule geotop_edge_face_of_edge_eq_prefix[OF hedge h\<tau>edge he\<tau>])
        show ?thesis
          using h\<tau>S he_eq by (by100 simp)
      qed
    qed
    have hK\<^sub>N_one_incident_edge_member_BdK\<^sub>N:
        "\<And>e. e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1
          \<Longrightarrow> e \<in> BdK\<^sub>N"
    proof -
      fix e
      assume heK: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hcard1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
      let ?S = "{\<tau> \<in> K\<^sub>N. geotop_simplex_dim \<tau> (2 - 1) \<and>
          card {\<sigma> \<in> K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and>
            geotop_is_face \<tau> \<sigma>} = 1}"
      have he_dim: "geotop_simplex_dim e (2 - 1)"
        using hedge unfolding geotop_is_edge_def by (by100 simp)
      have heS: "e \<in> ?S"
        using heK he_dim hcard1 by (by100 simp)
      show "e \<in> BdK\<^sub>N"
        unfolding BdK\<^sub>N_def geotop_comb_boundary_def using heS by (by100 simp)
    qed
    have hK\<^sub>N_edge_frontier_rel_interior_member_BdK\<^sub>N:
        "\<And>e p. e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 1
          \<Longrightarrow> p \<in> rel_interior e \<Longrightarrow> p \<in> FrN\<^sub>I \<Longrightarrow> e \<in> BdK\<^sub>N"
    proof -
      fix e p
      assume heK: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hge1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 1"
        and hp_rel: "p \<in> rel_interior e"
        and hp_Fr: "p \<in> FrN\<^sub>I"
      have hle2:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
        by (rule hK\<^sub>N_edge_incident_2faces_card_le2[OF heK hedge])
      have hnot2:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<noteq> 2"
        by (rule hK\<^sub>N_edge_frontier_rel_interior_not_two_incident
            [OF heK hedge hp_rel hp_Fr])
      have hcard1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
        using hge1 hle2 hnot2 by (by100 linarith)
      show "e \<in> BdK\<^sub>N"
        by (rule hK\<^sub>N_one_incident_edge_member_BdK\<^sub>N
            [OF heK hedge hcard1])
    qed
    have hBdK\<^sub>N_edge_member_subset_FrN\<^sub>I:
        "\<And>e. e \<in> BdK\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> e \<subseteq> FrN\<^sub>I"
    proof -
      fix e
      assume heBd: "e \<in> BdK\<^sub>N" and hedge: "geotop_is_edge e"
      have heK: "e \<in> K\<^sub>N"
        using hBdK\<^sub>N_sub_K\<^sub>N heBd by (by100 blast)
      have hcount:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
        by (rule hBdK\<^sub>N_edge_member_incident_count_one[OF heBd hedge])
      show "e \<subseteq> FrN\<^sub>I"
        by (rule hBdK\<^sub>N_one_incident_edge_subset_FrN\<^sub>I[OF heK hedge hcount])
    qed
    have hBdK\<^sub>N_poly_sub_FrN\<^sub>I: "geotop_polyhedron BdK\<^sub>N \<subseteq> FrN\<^sub>I"
    proof
      fix x
      assume hx: "x \<in> geotop_polyhedron BdK\<^sub>N"
      obtain \<rho> where h\<rho>Bd: "\<rho> \<in> BdK\<^sub>N" and hx\<rho>: "x \<in> \<rho>"
        using hx unfolding geotop_polyhedron_def by (by100 blast)
      let ?S = "{\<tau> \<in> K\<^sub>N. geotop_simplex_dim \<tau> (2 - 1) \<and>
          card {\<sigma> \<in> K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and>
            geotop_is_face \<tau> \<sigma>} = 1}"
      have h\<rho>_cases:
          "\<rho> \<in> ?S \<union> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
        using h\<rho>Bd unfolding BdK\<^sub>N_def geotop_comb_boundary_def by (by100 simp)
      show "x \<in> FrN\<^sub>I"
      proof (rule UnE[OF h\<rho>_cases])
        assume h\<rho>S: "\<rho> \<in> ?S"
        have h\<rho>K: "\<rho> \<in> K\<^sub>N"
          using h\<rho>S by (by100 simp)
        have h\<rho>edge: "geotop_is_edge \<rho>"
          using h\<rho>S unfolding geotop_is_edge_def by (by100 simp)
        have h\<rho>card:
            "card {\<sigma> \<in> K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and>
              geotop_is_face \<rho> \<sigma>} = 1"
          using h\<rho>S by (by100 simp)
        have h\<rho>Fr: "\<rho> \<subseteq> FrN\<^sub>I"
          by (rule hBdK\<^sub>N_one_incident_edge_subset_FrN\<^sub>I
              [OF h\<rho>K h\<rho>edge h\<rho>card])
        show "x \<in> FrN\<^sub>I"
          using hx\<rho> h\<rho>Fr by (by100 blast)
      next
        assume h\<rho>face_case: "\<rho> \<in> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
        obtain \<tau> where h\<tau>S: "\<tau> \<in> ?S" and h\<rho>\<tau>: "geotop_is_face \<rho> \<tau>"
          using h\<rho>face_case by (by100 blast)
        have h\<tau>K: "\<tau> \<in> K\<^sub>N"
          using h\<tau>S by (by100 simp)
        have h\<tau>edge: "geotop_is_edge \<tau>"
          using h\<tau>S unfolding geotop_is_edge_def by (by100 simp)
        have h\<tau>card:
            "card {\<sigma> \<in> K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and>
              geotop_is_face \<tau> \<sigma>} = 1"
          using h\<tau>S by (by100 simp)
        have h\<tau>Fr: "\<tau> \<subseteq> FrN\<^sub>I"
          by (rule hBdK\<^sub>N_one_incident_edge_subset_FrN\<^sub>I
              [OF h\<tau>K h\<tau>edge h\<tau>card])
        have h\<rho>sub\<tau>: "\<rho> \<subseteq> \<tau>"
          by (rule geotop_is_face_imp_subset_prefix[OF h\<rho>\<tau>])
        show "x \<in> FrN\<^sub>I"
          using hx\<rho> h\<rho>sub\<tau> h\<tau>Fr by (by100 blast)
      qed
    qed
    have hBdK\<^sub>N_edge_meets_J\<^sub>N_subset_J\<^sub>N:
        "\<And>e. e \<in> BdK\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          e \<inter> J\<^sub>N \<noteq> {} \<Longrightarrow> e \<subseteq> J\<^sub>N"
    proof -
      fix e
      assume heBd: "e \<in> BdK\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hmeet: "e \<inter> J\<^sub>N \<noteq> {}"
      have he_Fr: "e \<subseteq> FrN\<^sub>I"
        by (rule hBdK\<^sub>N_edge_member_subset_FrN\<^sub>I[OF heBd hedge])
      have he_dim: "geotop_simplex_dim e 1"
        using hedge unfolding geotop_is_edge_def by (by100 simp)
      have he_simplex: "geotop_is_simplex e"
        by (rule geotop_simplex_dim_imp_is_simplex[OF he_dim])
      have he_path_connected:
          "top1_path_connected_on e
            (subspace_topology UNIV geotop_euclidean_topology e)"
        by (rule Theorem_GT_1_3[OF he_simplex])
      have he_connected_top:
          "top1_connected_on e
            (subspace_topology UNIV geotop_euclidean_topology e)"
        by (rule top1_path_connected_on_geotop_imp_connected[OF he_path_connected])
      have he_connected: "connected e"
        using he_connected_top top1_connected_on_geotop_iff_connected by (by100 blast)
      have hunion_connected: "connected (e \<union> J\<^sub>N)"
        by (rule connected_Un[OF he_connected hJ\<^sub>N_connected_HOL hmeet])
      have hunion_sub: "e \<union> J\<^sub>N \<subseteq> FrN\<^sub>I"
        using he_Fr hJ\<^sub>N_sub_FrN\<^sub>I by (by100 blast)
      have hP_union: "P \<in> e \<union> J\<^sub>N"
        using hP_J\<^sub>N by (by100 blast)
      have hunion_sub_comp: "e \<union> J\<^sub>N \<subseteq> connected_component_set FrN\<^sub>I P"
        by (rule connected_component_maximal
            [OF hP_union hunion_connected hunion_sub])
      show "e \<subseteq> J\<^sub>N"
        using hunion_sub_comp hJ\<^sub>N_eq_connected_component by (by100 blast)
    qed
    define BdJ\<^sub>N where "BdJ\<^sub>N = {\<rho>\<in>BdK\<^sub>N. \<rho> \<subseteq> J\<^sub>N}"
    have hBdJ\<^sub>N_sub_BdK\<^sub>N: "BdJ\<^sub>N \<subseteq> BdK\<^sub>N"
      unfolding BdJ\<^sub>N_def by (by100 simp)
    have hBdJ\<^sub>N_fin: "finite BdJ\<^sub>N"
      by (rule finite_subset[OF hBdJ\<^sub>N_sub_BdK\<^sub>N hBdK\<^sub>N_fin])
    have hBdJ\<^sub>N_face_closed:
        "\<forall>\<sigma>\<in>BdJ\<^sub>N. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> BdJ\<^sub>N"
    proof (intro ballI allI impI)
      fix \<sigma> \<tau>
      assume h\<sigma>BdJ: "\<sigma> \<in> BdJ\<^sub>N"
        and h\<tau>\<sigma>: "geotop_is_face \<tau> \<sigma>"
      have h\<sigma>Bd: "\<sigma> \<in> BdK\<^sub>N"
        using h\<sigma>BdJ unfolding BdJ\<^sub>N_def by (by100 simp)
      have h\<sigma>J: "\<sigma> \<subseteq> J\<^sub>N"
        using h\<sigma>BdJ unfolding BdJ\<^sub>N_def by (by100 simp)
      have h\<tau>Bd: "\<tau> \<in> BdK\<^sub>N"
        using hBdK\<^sub>N_face_closed h\<sigma>Bd h\<tau>\<sigma> by (by100 blast)
      have h\<tau>sub\<sigma>: "\<tau> \<subseteq> \<sigma>"
        by (rule geotop_is_face_imp_subset_prefix[OF h\<tau>\<sigma>])
      have h\<tau>J: "\<tau> \<subseteq> J\<^sub>N"
        using h\<tau>sub\<sigma> h\<sigma>J by (by100 blast)
      show "\<tau> \<in> BdJ\<^sub>N"
        unfolding BdJ\<^sub>N_def using h\<tau>Bd h\<tau>J by (by100 simp)
    qed
    have hBdJ\<^sub>N_complex: "geotop_is_complex BdJ\<^sub>N"
      by (rule geotop_complex_subset_is_complex
          [OF hBdK\<^sub>N_complex hBdJ\<^sub>N_sub_BdK\<^sub>N hBdJ\<^sub>N_face_closed])
    have hBdJ\<^sub>N_1dim: "geotop_complex_is_1dim BdJ\<^sub>N"
      using hBdK\<^sub>N_1dim hBdJ\<^sub>N_sub_BdK\<^sub>N
      unfolding geotop_complex_is_1dim_def by (by100 blast)
    have hBdJ\<^sub>N_linear_graph: "geotop_is_linear_graph BdJ\<^sub>N"
      by (rule geotop_complex_1dim_imp_linear_graph_prefix
          [OF hBdJ\<^sub>N_complex hBdJ\<^sub>N_1dim])
    have hBdJ\<^sub>N_poly_sub_J\<^sub>N: "geotop_polyhedron BdJ\<^sub>N \<subseteq> J\<^sub>N"
      unfolding BdJ\<^sub>N_def geotop_polyhedron_def by (by100 blast)
    have hBdJ\<^sub>N_poly_sub_FrN\<^sub>I: "geotop_polyhedron BdJ\<^sub>N \<subseteq> FrN\<^sub>I"
      using hBdJ\<^sub>N_poly_sub_J\<^sub>N hJ\<^sub>N_sub_FrN\<^sub>I by (by100 blast)
    have hBdJ\<^sub>N_edge_sub_J\<^sub>N:
        "\<And>e. e \<in> BdJ\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> e \<subseteq> J\<^sub>N"
      unfolding BdJ\<^sub>N_def by (by100 simp)
    have hBdK\<^sub>N_edge_meets_J\<^sub>N_in_BdJ\<^sub>N:
        "\<And>e. e \<in> BdK\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          e \<inter> J\<^sub>N \<noteq> {} \<Longrightarrow> e \<in> BdJ\<^sub>N"
      unfolding BdJ\<^sub>N_def
      using hBdK\<^sub>N_edge_meets_J\<^sub>N_subset_J\<^sub>N by (by100 blast)
    have hK\<^sub>N_edge_J\<^sub>N_rel_interior_member_BdJ\<^sub>N:
        "\<And>e p. e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 1
          \<Longrightarrow> p \<in> rel_interior e \<Longrightarrow> p \<in> J\<^sub>N \<Longrightarrow> e \<in> BdJ\<^sub>N"
    proof -
      fix e p
      assume heK: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hge1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 1"
        and hp_rel: "p \<in> rel_interior e"
        and hpJ: "p \<in> J\<^sub>N"
      have hp_Fr: "p \<in> FrN\<^sub>I"
        using hpJ hJ\<^sub>N_sub_FrN\<^sub>I by (by100 blast)
      have heBd: "e \<in> BdK\<^sub>N"
        by (rule hK\<^sub>N_edge_frontier_rel_interior_member_BdK\<^sub>N
            [OF heK hedge hge1 hp_rel hp_Fr])
      have hp_e: "p \<in> e"
        using hp_rel rel_interior_subset by (by100 blast)
      have hmeet: "e \<inter> J\<^sub>N \<noteq> {}"
        using hp_e hpJ by (by100 blast)
      show "e \<in> BdJ\<^sub>N"
        by (rule hBdK\<^sub>N_edge_meets_J\<^sub>N_in_BdJ\<^sub>N[OF heBd hedge hmeet])
    qed
    have hJ\<^sub>N_carrier_edge_member_BdJ\<^sub>N:
        "\<And>p. p \<in> J\<^sub>N \<Longrightarrow>
          geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) 1
          \<Longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face (geotop_K_carrier K\<^sub>N p) \<sigma>} \<ge> 1
          \<Longrightarrow> geotop_K_carrier K\<^sub>N p \<in> BdJ\<^sub>N"
    proof -
      fix p
      assume hpJ: "p \<in> J\<^sub>N"
        and hdim1: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) 1"
        and hge1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face (geotop_K_carrier K\<^sub>N p) \<sigma>} \<ge> 1"
      have hpN: "p \<in> N"
        using hpJ hJ\<^sub>N_sub_N by (by100 blast)
      have hp_poly: "p \<in> geotop_polyhedron K\<^sub>N"
        using hpN hK\<^sub>N_poly by (by100 simp)
      have hcarrierK: "geotop_K_carrier K\<^sub>N p \<in> K\<^sub>N"
        by (rule geotop_K_carrier_in[OF hK\<^sub>N_complex hK\<^sub>N_fin hp_poly])
      have hp_rel:
          "p \<in> rel_interior (geotop_K_carrier K\<^sub>N p)"
        by (rule geotop_K_carrier_rel_interior[OF hK\<^sub>N_complex hK\<^sub>N_fin hp_poly])
      have hedge: "geotop_is_edge (geotop_K_carrier K\<^sub>N p)"
        using hdim1 unfolding geotop_is_edge_def by (by100 simp)
      show "geotop_K_carrier K\<^sub>N p \<in> BdJ\<^sub>N"
        by (rule hK\<^sub>N_edge_J\<^sub>N_rel_interior_member_BdJ\<^sub>N
            [OF hcarrierK hedge hge1 hp_rel hpJ])
    qed
    have hJ\<^sub>N_carrier_edge_with_2simplex_point_in_BdJ\<^sub>N_poly:
        "\<And>p. p \<in> J\<^sub>N \<Longrightarrow>
          geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) 1
          \<Longrightarrow>
          (\<exists>\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_K_carrier K\<^sub>N p \<subseteq> \<sigma>)
          \<Longrightarrow> p \<in> geotop_polyhedron BdJ\<^sub>N"
    proof -
      fix p
      assume hpJ: "p \<in> J\<^sub>N"
        and hdim1: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) 1"
        and h2:
          "\<exists>\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_K_carrier K\<^sub>N p \<subseteq> \<sigma>"
      have hpN: "p \<in> N"
        using hpJ hJ\<^sub>N_sub_N by (by100 blast)
      have hp_poly: "p \<in> geotop_polyhedron K\<^sub>N"
        using hpN hK\<^sub>N_poly by (by100 simp)
      have hcarrierK: "geotop_K_carrier K\<^sub>N p \<in> K\<^sub>N"
        by (rule geotop_K_carrier_in[OF hK\<^sub>N_complex hK\<^sub>N_fin hp_poly])
      have hp_rel:
          "p \<in> rel_interior (geotop_K_carrier K\<^sub>N p)"
        by (rule geotop_K_carrier_rel_interior[OF hK\<^sub>N_complex hK\<^sub>N_fin hp_poly])
      have hp_carrier: "p \<in> geotop_K_carrier K\<^sub>N p"
        using hp_rel rel_interior_subset by (by100 blast)
      have hge1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face (geotop_K_carrier K\<^sub>N p) \<sigma>} \<ge> 1"
      proof -
        obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K\<^sub>N"
          and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
          and hcarrier_sub_\<sigma>: "geotop_K_carrier K\<^sub>N p \<subseteq> \<sigma>"
          using h2 by (by100 blast)
        have hcarrier_face_\<sigma>:
            "geotop_is_face (geotop_K_carrier K\<^sub>N p) \<sigma>"
          by (rule geotop_complex_subset_simplex_face_prefix
              [OF hK\<^sub>N_complex hcarrierK h\<sigma>K hcarrier_sub_\<sigma>])
        let ?F = "{\<tau>\<in>K\<^sub>N. geotop_simplex_dim \<tau> 2
          \<and> geotop_is_face (geotop_K_carrier K\<^sub>N p) \<tau>}"
        have hF_sub: "?F \<subseteq> K\<^sub>N"
          by (by100 blast)
        have hF_fin: "finite ?F"
          by (rule finite_subset[OF hF_sub hK\<^sub>N_fin])
        have h\<sigma>F: "\<sigma> \<in> ?F"
          using h\<sigma>K h\<sigma>2 hcarrier_face_\<sigma> by (by100 blast)
        have hF_ne: "?F \<noteq> {}"
          using h\<sigma>F by (by100 blast)
        have hcard_pos_iff:
            "(0 < card ?F) = (?F \<noteq> {} \<and> finite ?F)"
          by (rule card_gt_0_iff)
        have hcard_pos: "0 < card ?F"
          using hcard_pos_iff hF_fin hF_ne by (by100 blast)
        show ?thesis
          using hcard_pos by (by100 linarith)
      qed
      have hcarrier_BdJ: "geotop_K_carrier K\<^sub>N p \<in> BdJ\<^sub>N"
        by (rule hJ\<^sub>N_carrier_edge_member_BdJ\<^sub>N
            [OF hpJ hdim1 hge1])
      show "p \<in> geotop_polyhedron BdJ\<^sub>N"
        unfolding geotop_polyhedron_def using hcarrier_BdJ hp_carrier by (by100 blast)
    qed
    have hJ\<^sub>N_carrier_edge_point_in_BdJ\<^sub>N_poly:
        "\<And>p. p \<in> J\<^sub>N \<Longrightarrow>
          geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) 1
          \<Longrightarrow> p \<in> geotop_polyhedron BdJ\<^sub>N"
    proof -
      fix p
      assume hpJ: "p \<in> J\<^sub>N"
        and hdim1: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) 1"
      have hpN: "p \<in> N"
        using hpJ hJ\<^sub>N_sub_N by (by100 blast)
      have hp_poly: "p \<in> geotop_polyhedron K\<^sub>N"
        using hpN hK\<^sub>N_poly by (by100 simp)
      have hcarrierK: "geotop_K_carrier K\<^sub>N p \<in> K\<^sub>N"
        by (rule geotop_K_carrier_in[OF hK\<^sub>N_complex hK\<^sub>N_fin hp_poly])
      have hp_rel:
          "p \<in> rel_interior (geotop_K_carrier K\<^sub>N p)"
        by (rule geotop_K_carrier_rel_interior[OF hK\<^sub>N_complex hK\<^sub>N_fin hp_poly])
      have hp_carrier: "p \<in> geotop_K_carrier K\<^sub>N p"
        using hp_rel rel_interior_subset by (by100 blast)
      have hedge: "geotop_is_edge (geotop_K_carrier K\<^sub>N p)"
        using hdim1 unfolding geotop_is_edge_def by (by100 simp)
      have hge1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face (geotop_K_carrier K\<^sub>N p) \<sigma>} \<ge> 1"
        by (rule hK\<^sub>N_edge_rel_interior_incident_count_ge1
            [OF hcarrierK hedge hp_rel])
      have hcarrier_BdJ: "geotop_K_carrier K\<^sub>N p \<in> BdJ\<^sub>N"
        by (rule hJ\<^sub>N_carrier_edge_member_BdJ\<^sub>N
            [OF hpJ hdim1 hge1])
      show "p \<in> geotop_polyhedron BdJ\<^sub>N"
        unfolding geotop_polyhedron_def using hcarrier_BdJ hp_carrier by (by100 blast)
    qed
    have hJ\<^sub>N_nonvertex_point_in_BdJ\<^sub>N_poly:
        "\<And>p. p \<in> J\<^sub>N \<Longrightarrow>
          p \<notin> geotop_complex_vertices K\<^sub>N
          \<Longrightarrow> p \<in> geotop_polyhedron BdJ\<^sub>N"
    proof -
      fix p
      assume hpJ: "p \<in> J\<^sub>N"
        and hp_not_vertex: "p \<notin> geotop_complex_vertices K\<^sub>N"
      obtain n where hn_le: "n \<le> 1"
        and hdim: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) n"
        using hJ\<^sub>N_carrier_dim_le1[OF hpJ] by (by100 blast)
      have hn_not0: "n \<noteq> 0"
      proof
        assume hn0: "n = 0"
        have hdim0: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) 0"
          using hdim hn0 by (by100 simp)
        have hpN: "p \<in> N"
          using hpJ hJ\<^sub>N_sub_N by (by100 blast)
        have hp_poly: "p \<in> geotop_polyhedron K\<^sub>N"
          using hpN hK\<^sub>N_poly by (by100 simp)
        have hcarrierK: "geotop_K_carrier K\<^sub>N p \<in> K\<^sub>N"
          by (rule geotop_K_carrier_in[OF hK\<^sub>N_complex hK\<^sub>N_fin hp_poly])
        have hcarrier_eq: "geotop_K_carrier K\<^sub>N p = {p}"
          by (rule hJ\<^sub>N_carrier_dim0_singleton[OF hpJ hdim0])
        have hpK: "{p} \<in> K\<^sub>N"
          using hcarrierK hcarrier_eq by (by100 simp)
        have hp_vertex: "p \<in> geotop_complex_vertices K\<^sub>N"
          using geotop_complex_vertices_eq_0_simplexes[OF hK\<^sub>N_complex] hpK
          by (by100 blast)
        show False
          using hp_not_vertex hp_vertex by (by100 blast)
      qed
      have hn1: "n = 1"
        using hn_le hn_not0 by (by100 linarith)
      have hdim1: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) 1"
        using hdim hn1 by (by100 simp)
      show "p \<in> geotop_polyhedron BdJ\<^sub>N"
        by (rule hJ\<^sub>N_carrier_edge_point_in_BdJ\<^sub>N_poly[OF hpJ hdim1])
    qed
    have hJ\<^sub>N_uncovered_sub_vertices:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N
          \<subseteq> geotop_complex_vertices K\<^sub>N"
    proof
      fix p
      assume hp: "p \<in> J\<^sub>N - geotop_polyhedron BdJ\<^sub>N"
      have hpJ: "p \<in> J\<^sub>N"
        using hp by (by100 simp)
      have hp_not_BdJ: "p \<notin> geotop_polyhedron BdJ\<^sub>N"
        using hp by (by100 simp)
      show "p \<in> geotop_complex_vertices K\<^sub>N"
      proof (rule ccontr)
        assume hp_not_vertex: "p \<notin> geotop_complex_vertices K\<^sub>N"
        have "p \<in> geotop_polyhedron BdJ\<^sub>N"
          by (rule hJ\<^sub>N_nonvertex_point_in_BdJ\<^sub>N_poly
              [OF hpJ hp_not_vertex])
        thus False
          using hp_not_BdJ by (by100 blast)
      qed
    qed
    have hJ\<^sub>N_uncovered_finite:
        "finite (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N)"
    proof -
      have hverts_fin: "finite (geotop_complex_vertices K\<^sub>N)"
        by (rule geotop_finite_complex_vertices_finite_prefix
            [OF hK\<^sub>N_complex hK\<^sub>N_fin])
      show ?thesis
        by (rule finite_subset[OF hJ\<^sub>N_uncovered_sub_vertices hverts_fin])
    qed
    have hJ\<^sub>N_carrier_vertex_edge_germ_point_in_BdJ\<^sub>N_poly:
        "\<And>p e q. p \<in> J\<^sub>N \<Longrightarrow>
          geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) 0
          \<Longrightarrow> e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> p \<in> e \<Longrightarrow>
          q \<in> rel_interior e \<Longrightarrow> q \<in> J\<^sub>N
          \<Longrightarrow> p \<in> geotop_polyhedron BdJ\<^sub>N"
    proof -
      fix p e q
      assume hpJ: "p \<in> J\<^sub>N"
        and hdim0: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N p) 0"
        and heK: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hp_e: "p \<in> e"
        and hq_rel: "q \<in> rel_interior e"
        and hqJ: "q \<in> J\<^sub>N"
      have hpN: "p \<in> N"
        using hpJ hJ\<^sub>N_sub_N by (by100 blast)
      have hp_poly: "p \<in> geotop_polyhedron K\<^sub>N"
        using hpN hK\<^sub>N_poly by (by100 simp)
      have hcarrierK: "geotop_K_carrier K\<^sub>N p \<in> K\<^sub>N"
        by (rule geotop_K_carrier_in[OF hK\<^sub>N_complex hK\<^sub>N_fin hp_poly])
      have hcarrier_eq: "geotop_K_carrier K\<^sub>N p = {p}"
        by (rule hJ\<^sub>N_carrier_dim0_singleton[OF hpJ hdim0])
      have hpK: "{p} \<in> K\<^sub>N"
        using hcarrierK hcarrier_eq by (by100 simp)
      have hface_pe: "geotop_is_face {p} e"
        by (rule geotop_1dim_vertex_in_simplex_is_face
            [OF hK\<^sub>N_complex hpK heK hp_e])
      have hge1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} \<ge> 1"
        by (rule hK\<^sub>N_edge_rel_interior_incident_count_ge1
            [OF heK hedge hq_rel])
      have heBdJ: "e \<in> BdJ\<^sub>N"
        by (rule hK\<^sub>N_edge_J\<^sub>N_rel_interior_member_BdJ\<^sub>N
            [OF heK hedge hge1 hq_rel hqJ])
      have hpBdJ: "{p} \<in> BdJ\<^sub>N"
        using hBdJ\<^sub>N_face_closed heBdJ hface_pe by (by100 blast)
      show "p \<in> geotop_polyhedron BdJ\<^sub>N"
        unfolding geotop_polyhedron_def using hpBdJ by (by100 blast)
    qed
    have hBdJ\<^sub>N_poly_sub_BdK\<^sub>N_poly:
        "geotop_polyhedron BdJ\<^sub>N \<subseteq> geotop_polyhedron BdK\<^sub>N"
      unfolding geotop_polyhedron_def using hBdJ\<^sub>N_sub_BdK\<^sub>N by (by100 blast)
    have hJ\<^sub>N_BdK\<^sub>N_poly_eq_BdJ\<^sub>N_poly:
        "J\<^sub>N \<inter> geotop_polyhedron BdK\<^sub>N = geotop_polyhedron BdJ\<^sub>N"
    proof
      show "J\<^sub>N \<inter> geotop_polyhedron BdK\<^sub>N \<subseteq> geotop_polyhedron BdJ\<^sub>N"
      proof
        fix x
        assume hx: "x \<in> J\<^sub>N \<inter> geotop_polyhedron BdK\<^sub>N"
        obtain \<rho> where h\<rho>Bd: "\<rho> \<in> BdK\<^sub>N" and hx\<rho>: "x \<in> \<rho>"
          using hx unfolding geotop_polyhedron_def by (by100 blast)
        have hxJ: "x \<in> J\<^sub>N"
          using hx by (by100 simp)
        obtain n where hn_le: "n \<le> 1" and h\<rho>dim: "geotop_simplex_dim \<rho> n"
          using hBdK\<^sub>N_1dim h\<rho>Bd
          unfolding geotop_complex_is_1dim_def by (by100 blast)
        have hcases: "n = 0 \<or> n = 1"
          using hn_le by (by100 linarith)
        show "x \<in> geotop_polyhedron BdJ\<^sub>N"
        proof (rule disjE[OF hcases])
          assume hn0: "n = 0"
          have h\<rho>0: "geotop_simplex_dim \<rho> 0"
            using h\<rho>dim hn0 by (by100 simp)
          have h\<rho>eq: "\<rho> = {x}"
            by (rule geotop_0simplex_contains_point_eq_singleton_prefix[OF h\<rho>0 hx\<rho>])
          have h\<rho>J: "\<rho> \<subseteq> J\<^sub>N"
            using h\<rho>eq hxJ by (by100 blast)
          have h\<rho>BdJ: "\<rho> \<in> BdJ\<^sub>N"
            unfolding BdJ\<^sub>N_def using h\<rho>Bd h\<rho>J by (by100 simp)
          show "x \<in> geotop_polyhedron BdJ\<^sub>N"
            unfolding geotop_polyhedron_def using h\<rho>BdJ hx\<rho> by (by100 blast)
        next
          assume hn1: "n = 1"
          have h\<rho>edge: "geotop_is_edge \<rho>"
            using h\<rho>dim hn1 unfolding geotop_is_edge_def by (by100 simp)
          have h\<rho>meet: "\<rho> \<inter> J\<^sub>N \<noteq> {}"
            using hx\<rho> hxJ by (by100 blast)
          have h\<rho>BdJ: "\<rho> \<in> BdJ\<^sub>N"
            by (rule hBdK\<^sub>N_edge_meets_J\<^sub>N_in_BdJ\<^sub>N[OF h\<rho>Bd h\<rho>edge h\<rho>meet])
          show "x \<in> geotop_polyhedron BdJ\<^sub>N"
            unfolding geotop_polyhedron_def using h\<rho>BdJ hx\<rho> by (by100 blast)
        qed
      qed
      show "geotop_polyhedron BdJ\<^sub>N \<subseteq> J\<^sub>N \<inter> geotop_polyhedron BdK\<^sub>N"
        using hBdJ\<^sub>N_poly_sub_J\<^sub>N hBdJ\<^sub>N_poly_sub_BdK\<^sub>N_poly by (by100 blast)
    qed
    have hBdK\<^sub>N_poly_closedin_FrN\<^sub>I:
        "closedin (top_of_set FrN\<^sub>I) (geotop_polyhedron BdK\<^sub>N)"
    proof -
      have hclosedin_int:
          "closedin (top_of_set FrN\<^sub>I)
            (FrN\<^sub>I \<inter> geotop_polyhedron BdK\<^sub>N)"
        using hBdK\<^sub>N_poly_closed by (rule closedin_closed_Int)
      have heq:
          "FrN\<^sub>I \<inter> geotop_polyhedron BdK\<^sub>N =
            geotop_polyhedron BdK\<^sub>N"
        using hBdK\<^sub>N_poly_sub_FrN\<^sub>I by (by100 blast)
      show ?thesis
        using hclosedin_int heq by (by100 simp)
    qed
    have hBdK\<^sub>N_poly_compact_in_FrN\<^sub>I:
        "compact (geotop_polyhedron BdK\<^sub>N)"
      using hBdK\<^sub>N_poly_compact .
    have hJ\<^sub>N_BdK\<^sub>N_poly_closedin_J\<^sub>N:
        "closedin (top_of_set J\<^sub>N) (J\<^sub>N \<inter> geotop_polyhedron BdK\<^sub>N)"
      using hBdK\<^sub>N_poly_closed by (rule closedin_closed_Int)
    have hJ\<^sub>N_BdK\<^sub>N_poly_closed:
        "closed (J\<^sub>N \<inter> geotop_polyhedron BdK\<^sub>N)"
      by (rule closed_Int[OF hJ\<^sub>N_closed hBdK\<^sub>N_poly_closed])
    have hJ\<^sub>N_BdK\<^sub>N_poly_compact:
        "compact (J\<^sub>N \<inter> geotop_polyhedron BdK\<^sub>N)"
    proof -
      have hsub: "J\<^sub>N \<inter> geotop_polyhedron BdK\<^sub>N \<subseteq> J\<^sub>N"
        by (by100 blast)
      show ?thesis
        by (rule closed_subset_compact
            [OF hJ\<^sub>N_compact hJ\<^sub>N_BdK\<^sub>N_poly_closed hsub])
    qed
    have hBdJ\<^sub>N_poly_closedin_J\<^sub>N:
        "closedin (top_of_set J\<^sub>N) (geotop_polyhedron BdJ\<^sub>N)"
      using hJ\<^sub>N_BdK\<^sub>N_poly_closedin_J\<^sub>N hJ\<^sub>N_BdK\<^sub>N_poly_eq_BdJ\<^sub>N_poly
      by (by100 simp)
    have hBdJ\<^sub>N_poly_closed: "closed (geotop_polyhedron BdJ\<^sub>N)"
      using hJ\<^sub>N_BdK\<^sub>N_poly_closed hJ\<^sub>N_BdK\<^sub>N_poly_eq_BdJ\<^sub>N_poly
      by (by100 simp)
    have hBdJ\<^sub>N_poly_compact: "compact (geotop_polyhedron BdJ\<^sub>N)"
      using hJ\<^sub>N_BdK\<^sub>N_poly_compact hJ\<^sub>N_BdK\<^sub>N_poly_eq_BdJ\<^sub>N_poly
      by (by100 simp)
    have hBdJ\<^sub>N_poly_A2_QS_disj:
        "geotop_polyhedron BdJ\<^sub>N \<inter> (A2 \<union> {Q, S}) = {}"
      using hBdJ\<^sub>N_poly_sub_J\<^sub>N hJ\<^sub>N_A2_QS_disj by (by100 blast)
    have hQ_not_BdJ\<^sub>N_poly: "Q \<notin> geotop_polyhedron BdJ\<^sub>N"
      using hBdJ\<^sub>N_poly_A2_QS_disj by (by100 blast)
    have hS_not_BdJ\<^sub>N_poly: "S \<notin> geotop_polyhedron BdJ\<^sub>N"
      using hBdJ\<^sub>N_poly_A2_QS_disj by (by100 blast)
    have hR_not_BdJ\<^sub>N_poly: "R \<notin> geotop_polyhedron BdJ\<^sub>N"
      using hR_in_A2 hBdJ\<^sub>N_poly_A2_QS_disj by (by100 blast)
    have hBdK\<^sub>N_poly_A2_QS_disj:
        "geotop_polyhedron BdK\<^sub>N \<inter> (A2 \<union> {Q, S}) = {}"
      using hBdK\<^sub>N_poly_sub_N hN_A2_QS by (by100 blast)
    have hQ_not_BdK\<^sub>N_poly: "Q \<notin> geotop_polyhedron BdK\<^sub>N"
      using hBdK\<^sub>N_poly_A2_QS_disj by (by100 blast)
    have hS_not_BdK\<^sub>N_poly: "S \<notin> geotop_polyhedron BdK\<^sub>N"
      using hBdK\<^sub>N_poly_A2_QS_disj by (by100 blast)
    have hR_not_BdK\<^sub>N_poly: "R \<notin> geotop_polyhedron BdK\<^sub>N"
      using hR_in_A2 hBdK\<^sub>N_poly_A2_QS_disj by (by100 blast)
    obtain r\<^sub>Q\<^sub>N where hr\<^sub>Q\<^sub>N_pos: "0 < r\<^sub>Q\<^sub>N"
      and hball_Q_N: "ball Q r\<^sub>Q\<^sub>N \<inter> N = {}"
    proof -
      have hcompl_open: "open (- N)"
        by (rule open_Compl[OF hN_closed])
      have hQ_compl: "Q \<in> - N"
        using hQ_not_N by (by100 simp)
      have hQ_ball_ex: "\<exists>e>0. ball Q e \<subseteq> - N"
        using hcompl_open hQ_compl unfolding open_contains_ball by (by100 simp)
      obtain r\<^sub>Q\<^sub>N where hr_pos: "0 < r\<^sub>Q\<^sub>N"
        and hball: "ball Q r\<^sub>Q\<^sub>N \<subseteq> - N"
        using hQ_ball_ex by (elim exE conjE)
      have hdisj: "ball Q r\<^sub>Q\<^sub>N \<inter> N = {}"
        using hball by (by100 auto)
      show ?thesis
        using hr_pos hdisj by (rule that)
    qed
    obtain r\<^sub>S\<^sub>N where hr\<^sub>S\<^sub>N_pos: "0 < r\<^sub>S\<^sub>N"
      and hball_S_N: "ball S r\<^sub>S\<^sub>N \<inter> N = {}"
    proof -
      have hcompl_open: "open (- N)"
        by (rule open_Compl[OF hN_closed])
      have hS_compl: "S \<in> - N"
        using hS_not_N by (by100 simp)
      have hS_ball_ex: "\<exists>e>0. ball S e \<subseteq> - N"
        using hcompl_open hS_compl unfolding open_contains_ball by (by100 simp)
      obtain r\<^sub>S\<^sub>N where hr_pos: "0 < r\<^sub>S\<^sub>N"
        and hball: "ball S r\<^sub>S\<^sub>N \<subseteq> - N"
        using hS_ball_ex by (elim exE conjE)
      have hdisj: "ball S r\<^sub>S\<^sub>N \<inter> N = {}"
        using hball by (by100 auto)
      show ?thesis
        using hr_pos hdisj by (rule that)
    qed
    have hQ_ne_S: "Q \<noteq> S"
      using hcard by (auto simp: card_insert_if split: if_splits)
    obtain r\<^sub>Q\<^sub>S where hr\<^sub>Q\<^sub>S_pos: "0 < r\<^sub>Q\<^sub>S"
      and hball_QS_disj: "ball Q r\<^sub>Q\<^sub>S \<inter> ball S r\<^sub>Q\<^sub>S = {}"
      using geotop_distinct_points_disjoint_small_balls_prefix[OF hQ_ne_S]
      by (elim exE conjE)
    define r where "r = min r\<^sub>Q\<^sub>S (min r\<^sub>Q\<^sub>N r\<^sub>S\<^sub>N)"
    have hr_pos: "0 < r"
      unfolding r_def using hr\<^sub>Q\<^sub>S_pos hr\<^sub>Q\<^sub>N_pos hr\<^sub>S\<^sub>N_pos by (by100 simp)
    have hr_le_QS: "r \<le> r\<^sub>Q\<^sub>S"
      unfolding r_def by (by100 simp)
    have hr_le_QN: "r \<le> r\<^sub>Q\<^sub>N"
      unfolding r_def by (by100 simp)
    have hr_le_SN: "r \<le> r\<^sub>S\<^sub>N"
      unfolding r_def by (by100 simp)
    have hball_Q_r_QS: "ball Q r \<subseteq> ball Q r\<^sub>Q\<^sub>S"
      unfolding ball_subset_ball_iff using hr_pos hr_le_QS by (by100 simp)
    have hball_S_r_QS: "ball S r \<subseteq> ball S r\<^sub>Q\<^sub>S"
      unfolding ball_subset_ball_iff using hr_pos hr_le_QS by (by100 simp)
    have hr_disj: "ball Q r \<inter> ball S r = {}"
      using hball_Q_r_QS hball_S_r_QS hball_QS_disj by (by100 blast)
    have hball_Q_r_QN: "ball Q r \<subseteq> ball Q r\<^sub>Q\<^sub>N"
      unfolding ball_subset_ball_iff using hr_pos hr_le_QN by (by100 simp)
    have hball_S_r_SN: "ball S r \<subseteq> ball S r\<^sub>S\<^sub>N"
      unfolding ball_subset_ball_iff using hr_pos hr_le_SN by (by100 simp)
    have hball_Q_r_N: "ball Q r \<inter> N = {}"
      using hball_Q_r_QN hball_Q_N by (by100 blast)
    have hball_S_r_N: "ball S r \<inter> N = {}"
      using hball_S_r_SN hball_S_N by (by100 blast)
    have hQ_ne_PR: "Q \<noteq> P \<and> Q \<noteq> R"
      using hQ_ne_P hQ_ne_R by (by100 blast)
    have hS_ne_PR: "S \<noteq> P \<and> S \<noteq> R"
      using hS_ne_P hS_ne_R by (by100 blast)
    have hQ_S_two_arc_local_access_outside_N:
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
          \<and> U\<^sub>Q \<inter> U\<^sub>S = {}
          \<and> U\<^sub>Q \<inter> N = {}
          \<and> U\<^sub>S \<inter> N = {}"
    proof -
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
      have hU\<^sub>Q_N_disj: "U\<^sub>Q \<inter> N = {}"
        using hU\<^sub>Q_ball hball_Q_r_N by (by100 blast)
      have hU\<^sub>S_N_disj: "U\<^sub>S \<inter> N = {}"
        using hU\<^sub>S_ball hball_S_r_N by (by100 blast)
      show ?thesis
        using hr_pos hU\<^sub>Q_conn hU\<^sub>S_conn hU\<^sub>Q_open hU\<^sub>S_open
          hU\<^sub>Q_sub hU\<^sub>S_sub hU\<^sub>Q_ball hU\<^sub>S_ball hr_disj
          hQ_front hS_front hQ'_U\<^sub>Q hS'_U\<^sub>S hQ'_cut hS'_cut hU_disj
          hU\<^sub>Q_N_disj hU\<^sub>S_N_disj
        by (intro exI conjI)
    qed
    obtain r U\<^sub>Q U\<^sub>S Q' S'
      where hr_pos: "0 < r"
        and hU\<^sub>Q_conn: "connected U\<^sub>Q"
        and hU\<^sub>S_conn: "connected U\<^sub>S"
        and hU\<^sub>Q_open: "U\<^sub>Q \<in> geotop_euclidean_topology"
        and hU\<^sub>S_open: "U\<^sub>S \<in> geotop_euclidean_topology"
        and hU\<^sub>Q_sub: "U\<^sub>Q \<subseteq> geotop_polygon_interior J - (A1 \<union> A2)"
        and hU\<^sub>S_sub: "U\<^sub>S \<subseteq> geotop_polygon_interior J - (A1 \<union> A2)"
        and hU\<^sub>Q_ball: "U\<^sub>Q \<subseteq> ball Q r"
        and hU\<^sub>S_ball: "U\<^sub>S \<subseteq> ball S r"
        and hr_disj: "ball Q r \<inter> ball S r = {}"
        and hQ_front:
          "Q \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>Q"
        and hS_front:
          "S \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>S"
        and hQ'_U\<^sub>Q: "Q' \<in> U\<^sub>Q"
        and hS'_U\<^sub>S: "S' \<in> U\<^sub>S"
        and hQ'_cut: "Q' \<in> geotop_polygon_interior J - (A1 \<union> A2)"
        and hS'_cut: "S' \<in> geotop_polygon_interior J - (A1 \<union> A2)"
        and hU_disj: "U\<^sub>Q \<inter> U\<^sub>S = {}"
        and hU\<^sub>Q_N_disj: "U\<^sub>Q \<inter> N = {}"
        and hU\<^sub>S_N_disj: "U\<^sub>S \<inter> N = {}"
      using hQ_S_two_arc_local_access_outside_N
      by (elim exE conjE)
    let ?cut = "geotop_polygon_interior J - (A1 \<union> A2)"
    let ?Ncut = "geotop_polygon_interior J - (N \<union> A2)"
    have hI_open_HOL: "open (geotop_polygon_interior J)"
      by (rule polygon_interior_open[OF hJ])
    have hA2_closed: "closed A2"
      using hA12_metric_separation by (by100 blast)
    have hN_A2_closed: "closed (N \<union> A2)"
      by (rule closed_Un[OF hN_closed hA2_closed])
    have hNcut_open_HOL: "open ?Ncut"
      by (rule open_Diff[OF hI_open_HOL hN_A2_closed])
    have hNcut_open: "?Ncut \<in> geotop_euclidean_topology"
      using hNcut_open_HOL
      unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    have hNcut_sub_cut: "?Ncut \<subseteq> ?cut"
      using hA1_N by (by100 blast)
    have hU\<^sub>Q_sub_Ncut: "U\<^sub>Q \<subseteq> ?Ncut"
      using hU\<^sub>Q_sub hU\<^sub>Q_N_disj by (by100 blast)
    have hU\<^sub>S_sub_Ncut: "U\<^sub>S \<subseteq> ?Ncut"
      using hU\<^sub>S_sub hU\<^sub>S_N_disj by (by100 blast)
    have hQ'_Ncut: "Q' \<in> ?Ncut"
      using hQ'_U\<^sub>Q hU\<^sub>Q_sub_Ncut by (by100 blast)
    have hS'_Ncut: "S' \<in> ?Ncut"
      using hS'_U\<^sub>S hU\<^sub>S_sub_Ncut by (by100 blast)
    have hcomponent_Ncut_sub_cut:
        "geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q'
          \<subseteq> geotop_component_at UNIV geotop_euclidean_topology ?cut Q'"
    proof (rule subsetI)
      fix x
      assume hx:
        "x \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q'"
      obtain C where hC:
          "C \<subseteq> ?Ncut \<and> Q' \<in> C \<and>
            top1_connected_on C (subspace_topology UNIV geotop_euclidean_topology C)"
        and hxC: "x \<in> C"
        using hx unfolding geotop_component_at_def by (by100 blast)
      have hC_sub_cut: "C \<subseteq> ?cut"
        using hC hNcut_sub_cut by (by100 blast)
      have hC_witness:
          "C \<in> {C. C \<subseteq> ?cut \<and> Q' \<in> C \<and>
            top1_connected_on C (subspace_topology UNIV geotop_euclidean_topology C)}"
        using hC hC_sub_cut by (by100 simp)
      show "x \<in> geotop_component_at UNIV geotop_euclidean_topology ?cut Q'"
        unfolding geotop_component_at_def using hC_witness hxC by (by100 blast)
    qed
    have hD44_same_component_from_Ncut_suffices:
        "S' \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q'
          \<Longrightarrow> S' \<in> geotop_component_at UNIV geotop_euclidean_topology ?cut Q'"
      using hcomponent_Ncut_sub_cut by (rule subsetD)
    have hD44_QS_witnesses_same_component_in_Ncut:
        "S' \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q'"
      (**
        Remaining regular-neighborhood step in Moise 4.4, now stated in the
        smaller complement outside the chosen carrier \<open>N\<close>.  Use the compact
        finite polyhedral carrier \<open>N\<close> with \<open>A1 \<subseteq> N\<close>, \<open>N \<inter> A2 = {}\<close>,
        and the local witnesses already chosen outside \<open>N\<close>.  Analyze the
        frontier component of \<open>N\<close> through \<open>P\<close>, extract the broken-line subarc
        with endpoints on \<open>J\<close>, and use the cyclic-order/D42 transfer to show
        the outside witnesses \<open>Q'\<close> and \<open>S'\<close> lie in one component of
        \<open>geotop_polygon_interior J - (N \<union> A2)\<close>. **)
    proof -
      obtain Q1 B\<^sub>Q where hQ1_U\<^sub>Q: "Q1 \<in> U\<^sub>Q"
        and hQ1_ball: "Q1 \<in> ball Q r"
        and hB\<^sub>Q_bl: "geotop_is_broken_line B\<^sub>Q"
        and hB\<^sub>Q_U\<^sub>Q: "B\<^sub>Q \<subseteq> U\<^sub>Q"
        and hQ1_B\<^sub>Q: "Q1 \<in> B\<^sub>Q"
        and hQ'_B\<^sub>Q: "Q' \<in> B\<^sub>Q"
        using geotop_connected_open_frontier_near_broken_access_prefix
            [OF hU\<^sub>Q_conn hU\<^sub>Q_open hQ_front hQ'_U\<^sub>Q hr_pos]
        by (elim exE conjE)
      obtain S1 B\<^sub>S where hS1_U\<^sub>S: "S1 \<in> U\<^sub>S"
        and hS1_ball: "S1 \<in> ball S r"
        and hB\<^sub>S_bl: "geotop_is_broken_line B\<^sub>S"
        and hB\<^sub>S_U\<^sub>S: "B\<^sub>S \<subseteq> U\<^sub>S"
        and hS1_B\<^sub>S: "S1 \<in> B\<^sub>S"
        and hS'_B\<^sub>S: "S' \<in> B\<^sub>S"
        using geotop_connected_open_frontier_near_broken_access_prefix
            [OF hU\<^sub>S_conn hU\<^sub>S_open hS_front hS'_U\<^sub>S hr_pos]
        by (elim exE conjE)
      have hB\<^sub>Q_Ncut: "B\<^sub>Q \<subseteq> ?Ncut"
        using hB\<^sub>Q_U\<^sub>Q hU\<^sub>Q_sub_Ncut by (by100 blast)
      have hB\<^sub>S_Ncut: "B\<^sub>S \<subseteq> ?Ncut"
        using hB\<^sub>S_U\<^sub>S hU\<^sub>S_sub_Ncut by (by100 blast)
      have hQ1_Ncut: "Q1 \<in> ?Ncut"
        using hB\<^sub>Q_Ncut hQ1_B\<^sub>Q by (by100 blast)
      have hS1_Ncut: "S1 \<in> ?Ncut"
        using hB\<^sub>S_Ncut hS1_B\<^sub>S by (by100 blast)
      have hQ1_I: "Q1 \<in> geotop_polygon_interior J"
        using hQ1_Ncut by (by100 blast)
      have hS1_I: "S1 \<in> geotop_polygon_interior J"
        using hS1_Ncut by (by100 blast)
      have hQ1_not_N: "Q1 \<notin> N"
        using hQ1_Ncut by (by100 blast)
      have hS1_not_N: "S1 \<notin> N"
        using hS1_Ncut by (by100 blast)
      have hQ1_not_FrN\<^sub>I: "Q1 \<notin> FrN\<^sub>I"
        using hQ1_not_N hFrN\<^sub>I_sub_N by (by100 blast)
      have hS1_not_FrN\<^sub>I: "S1 \<notin> FrN\<^sub>I"
        using hS1_not_N hFrN\<^sub>I_sub_N by (by100 blast)
      have hQ1_not_J\<^sub>N: "Q1 \<notin> J\<^sub>N"
        using hQ1_not_N hJ\<^sub>N_sub_N by (by100 blast)
      have hS1_not_J\<^sub>N: "S1 \<notin> J\<^sub>N"
        using hS1_not_N hJ\<^sub>N_sub_N by (by100 blast)
      have hQ1_not_A2: "Q1 \<notin> A2"
        using hQ1_Ncut by (by100 blast)
      have hS1_not_A2: "S1 \<notin> A2"
        using hS1_Ncut by (by100 blast)
      have hQ1_not_A1: "Q1 \<notin> A1"
        using hQ1_not_N hA1_N by (by100 blast)
      have hS1_not_A1: "S1 \<notin> A1"
        using hS1_not_N hA1_N by (by100 blast)
      have hQ1_not_K\<^sub>N_poly: "Q1 \<notin> geotop_polyhedron K\<^sub>N"
        using hQ1_not_N hK\<^sub>N_poly by (by100 simp)
      have hS1_not_K\<^sub>N_poly: "S1 \<notin> geotop_polyhedron K\<^sub>N"
        using hS1_not_N hK\<^sub>N_poly by (by100 simp)
      have hQ1_not_BdK\<^sub>N_poly: "Q1 \<notin> geotop_polyhedron BdK\<^sub>N"
        using hQ1_not_N hBdK\<^sub>N_poly_sub_N by (by100 blast)
      have hS1_not_BdK\<^sub>N_poly: "S1 \<notin> geotop_polyhedron BdK\<^sub>N"
        using hS1_not_N hBdK\<^sub>N_poly_sub_N by (by100 blast)
      have hD44_connected_route_component_suffices:
          "\<And>W. W \<subseteq> ?Ncut \<Longrightarrow> Q1 \<in> W \<Longrightarrow> S1 \<in> W \<Longrightarrow>
            top1_connected_on W
              (subspace_topology UNIV geotop_euclidean_topology W) \<Longrightarrow>
            S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
        (**
          Pure component bookkeeping for the Moise frontier route: once the
          regular-neighborhood boundary analysis supplies a connected witness
          in \<open>I - (N \<union> A2)\<close> through the two local access endpoints, the
          endpoints are in the same ambient component. **)
      proof -
        fix W
        assume hW_Ncut: "W \<subseteq> ?Ncut"
          and hQ1_W: "Q1 \<in> W"
          and hS1_W: "S1 \<in> W"
          and hW_conn:
            "top1_connected_on W
              (subspace_topology UNIV geotop_euclidean_topology W)"
        have hW_witness:
            "W \<in> {C. C \<subseteq> ?Ncut \<and> Q1 \<in> C \<and>
              top1_connected_on C
                (subspace_topology UNIV geotop_euclidean_topology C)}"
          using hW_Ncut hQ1_W hW_conn by (by100 simp)
        show "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
          unfolding geotop_component_at_def
          using hW_witness hS1_W by (by100 blast)
      qed
      have hD44_access_same_component_from_central:
          "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
            \<Longrightarrow> S' \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q'"
        (**
          Access bookkeeping around Moise's central frontier route: once the
          near-boundary access endpoint \<open>S1\<close> lies in the same outside-carrier
          component as \<open>Q1\<close>, the already constructed local broken lines inside
          \<open>U_Q\<close> and \<open>U_S\<close> transfer that component relation back to the
          original witnesses \<open>Q'\<close> and \<open>S'\<close>. **)
      proof -
        assume hcentral:
          "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
        have hB\<^sub>Q_conn:
            "top1_connected_on B\<^sub>Q
              (subspace_topology UNIV geotop_euclidean_topology B\<^sub>Q)"
          by (rule geotop_broken_line_connected_on_prefix[OF hB\<^sub>Q_bl])
        have hB\<^sub>Q_witness:
            "B\<^sub>Q \<in> {C. C \<subseteq> ?Ncut \<and> Q' \<in> C \<and>
              top1_connected_on C
                (subspace_topology UNIV geotop_euclidean_topology C)}"
          using hB\<^sub>Q_Ncut hQ'_B\<^sub>Q hB\<^sub>Q_conn by (by100 simp)
        have hQ1_comp_Q':
            "Q1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q'"
          unfolding geotop_component_at_def
          using hB\<^sub>Q_witness hQ1_B\<^sub>Q by (by100 blast)
        have hB\<^sub>S_conn:
            "top1_connected_on B\<^sub>S
              (subspace_topology UNIV geotop_euclidean_topology B\<^sub>S)"
          by (rule geotop_broken_line_connected_on_prefix[OF hB\<^sub>S_bl])
        have hB\<^sub>S_witness:
            "B\<^sub>S \<in> {C. C \<subseteq> ?Ncut \<and> S1 \<in> C \<and>
              top1_connected_on C
                (subspace_topology UNIV geotop_euclidean_topology C)}"
          using hB\<^sub>S_Ncut hS1_B\<^sub>S hB\<^sub>S_conn by (by100 simp)
        have hS'_comp_S1:
            "S' \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut S1"
          unfolding geotop_component_at_def
          using hB\<^sub>S_witness hS'_B\<^sub>S by (by100 blast)
        have hQ1_HOL:
            "Q1 \<in> connected_component_set ?Ncut Q'"
          using hQ1_comp_Q'
            geotop_component_at_UNIV_eq_connected_component_set[of ?Ncut Q']
          by (by100 simp)
        have hS1_HOL:
            "S1 \<in> connected_component_set ?Ncut Q1"
          using hcentral
            geotop_component_at_UNIV_eq_connected_component_set[of ?Ncut Q1]
          by (by100 simp)
        have hS'_HOL_S1:
            "S' \<in> connected_component_set ?Ncut S1"
          using hS'_comp_S1
            geotop_component_at_UNIV_eq_connected_component_set[of ?Ncut S1]
          by (by100 simp)
        have hcomp_Q1_Q':
            "connected_component_set ?Ncut Q1 =
             connected_component_set ?Ncut Q'"
          by (rule connected_component_eq[OF hQ1_HOL])
        have hcomp_S1_Q1:
            "connected_component_set ?Ncut S1 =
             connected_component_set ?Ncut Q1"
          by (rule connected_component_eq[OF hS1_HOL])
        have hS'_HOL_Q':
            "S' \<in> connected_component_set ?Ncut Q'"
          using hS'_HOL_S1 hcomp_S1_Q1 hcomp_Q1_Q' by (by100 simp)
        show "S' \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q'"
          using hS'_HOL_Q'
            geotop_component_at_UNIV_eq_connected_component_set[of ?Ncut Q']
          by (by100 simp)
      qed
      have hD44_central_frontier_broken_line_route_exists:
          "\<exists>B\<^sub>c. geotop_is_broken_line B\<^sub>c
            \<and> B\<^sub>c \<subseteq> ?Ncut
            \<and> Q1 \<in> B\<^sub>c
            \<and> S1 \<in> B\<^sub>c"
        (**
          Remaining book step in its literal broken-line form.  Moise's
          frontier-component construction supplies a broken-line subarc of the
          frontier of the regular neighborhood of \<open>A1\<close>, lying outside
          \<open>N \<union> A2\<close>, whose ends attach to the chosen access points near
          \<open>Q\<close> and \<open>S\<close>. **)
        sorry
      have hD44_central_frontier_route_exists:
          "\<exists>W. W \<subseteq> ?Ncut
            \<and> Q1 \<in> W
            \<and> S1 \<in> W
            \<and> top1_connected_on W
              (subspace_topology UNIV geotop_euclidean_topology W)"
        (**
          Remaining book step in its frontier-route form.  Moise constructs
          this connected witness from the component of the frontier of the
          fine carrier \<open>N\<close> through \<open>P\<close>: after extracting the broken-line
          subarc between the last lower and first upper boundary hits, the
          subarc lies in \<open>I - (N \<union> A2)\<close> and connects the two access points
          selected near \<open>Q\<close> and \<open>S\<close>. **)
      proof -
        obtain B\<^sub>c where hB\<^sub>c_bl: "geotop_is_broken_line B\<^sub>c"
          and hB\<^sub>c_Ncut: "B\<^sub>c \<subseteq> ?Ncut"
          and hQ1_B\<^sub>c: "Q1 \<in> B\<^sub>c"
          and hS1_B\<^sub>c: "S1 \<in> B\<^sub>c"
          using hD44_central_frontier_broken_line_route_exists
          by (elim exE conjE)
        have hB\<^sub>c_conn:
            "top1_connected_on B\<^sub>c
              (subspace_topology UNIV geotop_euclidean_topology B\<^sub>c)"
          by (rule geotop_broken_line_connected_on_prefix[OF hB\<^sub>c_bl])
        show ?thesis
          using hB\<^sub>c_Ncut hQ1_B\<^sub>c hS1_B\<^sub>c hB\<^sub>c_conn
          by (intro exI conjI)
      qed
      have hD44_central_same_component:
          "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
        (**
          Core Moise D44 regular-neighborhood component step: analyze the
          frontier component of the fine carrier \<open>N\<close> through \<open>P\<close>, extract
          the outside boundary/frontier route in \<open>geotop_polygon_interior J -
          (N \<union> A2)\<close>, and show that the two near-boundary access endpoints
          \<open>Q1\<close> and \<open>S1\<close> are in the same outside-carrier component. **)
      proof -
        obtain W where hW_Ncut: "W \<subseteq> ?Ncut"
          and hQ1_W: "Q1 \<in> W"
          and hS1_W: "S1 \<in> W"
          and hW_conn:
            "top1_connected_on W
              (subspace_topology UNIV geotop_euclidean_topology W)"
          using hD44_central_frontier_route_exists
          by (elim exE conjE)
        show ?thesis
          by (rule hD44_connected_route_component_suffices
              [OF hW_Ncut hQ1_W hS1_W hW_conn])
      qed
      show ?thesis
        by (rule hD44_access_same_component_from_central
            [OF hD44_central_same_component])
    qed
    have hD44_QS_witnesses_same_component_from_fine_A1_neighborhood:
        "S' \<in> geotop_component_at UNIV geotop_euclidean_topology
          (geotop_polygon_interior J - (A1 \<union> A2)) Q'"
      by (rule hD44_same_component_from_Ncut_suffices
          [OF hD44_QS_witnesses_same_component_in_Ncut])
    show ?thesis
      by (rule geotop_same_component_local_access_frontier_transfer_prefix
          [where U = "geotop_polygon_interior J - (A1 \<union> A2)"
             and U\<^sub>Q = U\<^sub>Q and U\<^sub>S = U\<^sub>S and Q' = Q' and S' = S',
           OF hU\<^sub>Q_conn hU\<^sub>S_conn hU\<^sub>Q_sub hU\<^sub>S_sub hQ'_U\<^sub>Q hS'_U\<^sub>S
              hQ_front hS_front hQ_not_cut hS_not_cut
              hD44_QS_witnesses_same_component_from_fine_A1_neighborhood])
  qed
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
