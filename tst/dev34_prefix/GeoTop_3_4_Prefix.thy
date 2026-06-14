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
    define N\<^sub>I where
        "N\<^sub>I = N \<inter> closure_on UNIV geotop_euclidean_topology
          (geotop_polygon_interior J)"
    have hN\<^sub>I_eq_N: "N\<^sub>I = N"
      unfolding N\<^sub>I_def using hN_sub_disk by (by100 blast)
    have hN\<^sub>I_compact: "compact N\<^sub>I"
      using hN\<^sub>I_eq_N hN_compact by (by100 simp)
    have hN\<^sub>I_closed: "closed N\<^sub>I"
      using hN\<^sub>I_eq_N hN_closed by (by100 simp)
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
    have hK\<^sub>N_poly_N\<^sub>I: "geotop_polyhedron K\<^sub>N = N\<^sub>I"
      using hK\<^sub>N_poly hN\<^sub>I_eq_N by (by100 simp)
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
    have hBdK\<^sub>N_poly_compact: "compact (geotop_polyhedron BdK\<^sub>N)"
      by (rule geotop_complex_polyhedron_compact[OF hBdK\<^sub>N_complex hBdK\<^sub>N_fin])
    have hBdK\<^sub>N_poly_closed: "closed (geotop_polyhedron BdK\<^sub>N)"
      by (rule geotop_complex_polyhedron_closed[OF hBdK\<^sub>N_complex hBdK\<^sub>N_fin])
    have hBdK\<^sub>N_poly_sub_N: "geotop_polyhedron BdK\<^sub>N \<subseteq> N"
      using hBdK\<^sub>N_sub_K\<^sub>N hK\<^sub>N_poly unfolding geotop_polyhedron_def by (by100 blast)
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
    have hQ'_Ncut_component_open:
        "geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q'
          \<in> geotop_euclidean_topology"
      by (rule geotop_component_at_open_in_euclidean[OF hNcut_open hQ'_Ncut])
    have hD44_broken_line_in_Ncut_suffices:
        "\<And>B. geotop_is_broken_line B \<Longrightarrow> B \<subseteq> ?Ncut \<Longrightarrow>
          Q' \<in> B \<Longrightarrow> S' \<in> B \<Longrightarrow>
          S' \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q'"
    proof -
      fix B
      assume hB_bl: "geotop_is_broken_line B"
        and hB_Ncut: "B \<subseteq> ?Ncut"
        and hQ'_B: "Q' \<in> B"
        and hS'_B: "S' \<in> B"
      have hB_conn:
          "top1_connected_on B
            (subspace_topology UNIV geotop_euclidean_topology B)"
        by (rule geotop_broken_line_connected_on_prefix[OF hB_bl])
      have hB_witness:
          "B \<in> {C. C \<subseteq> ?Ncut \<and> Q' \<in> C \<and>
            top1_connected_on C (subspace_topology UNIV geotop_euclidean_topology C)}"
        using hB_Ncut hQ'_B hB_conn by (by100 simp)
      show "S' \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q'"
        unfolding geotop_component_at_def using hB_witness hS'_B by (by100 blast)
    qed
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
      have hD44_central_component_chord_suffices:
          "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
            \<Longrightarrow> \<exists>B\<^sub>0. geotop_is_broken_line B\<^sub>0
              \<and> B\<^sub>0 \<subseteq> ?Ncut
              \<and> Q1 \<in> B\<^sub>0
              \<and> S1 \<in> B\<^sub>0"
      proof -
        assume hS1_comp:
          "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
        obtain B\<^sub>0 where hB\<^sub>0_bl: "geotop_is_broken_line B\<^sub>0"
          and hB\<^sub>0_Ncut: "B\<^sub>0 \<subseteq> ?Ncut"
          and hQ1_B\<^sub>0: "Q1 \<in> B\<^sub>0"
          and hS1_B\<^sub>0: "S1 \<in> B\<^sub>0"
          using geotop_open_component_broken_line_between_prefix
              [OF hNcut_open hQ1_Ncut hS1_comp]
          by (elim exE conjE)
        show ?thesis
          using hB\<^sub>0_bl hB\<^sub>0_Ncut hQ1_B\<^sub>0 hS1_B\<^sub>0 by (intro exI conjI)
      qed
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
      obtain B\<^sub>0 where hB\<^sub>0_bl: "geotop_is_broken_line B\<^sub>0"
        and hB\<^sub>0_Ncut: "B\<^sub>0 \<subseteq> ?Ncut"
        and hQ1_B\<^sub>0: "Q1 \<in> B\<^sub>0"
        and hS1_B\<^sub>0: "S1 \<in> B\<^sub>0"
        using hD44_central_component_chord_suffices
            [OF hD44_central_same_component]
        by (elim exE conjE)
      obtain B\<^sub>m where hB\<^sub>m_bl: "geotop_is_broken_line B\<^sub>m"
        and hB\<^sub>m_sub: "B\<^sub>m \<subseteq> B\<^sub>Q \<union> B\<^sub>0"
        and hQ'_B\<^sub>m: "Q' \<in> B\<^sub>m"
        and hS1_B\<^sub>m: "S1 \<in> B\<^sub>m"
        using geotop_broken_line_arc_reduction
            [OF hB\<^sub>Q_bl hB\<^sub>0_bl hQ'_B\<^sub>Q hQ1_B\<^sub>Q hQ1_B\<^sub>0 hS1_B\<^sub>0]
        by (elim exE conjE)
      obtain B where hB_bl: "geotop_is_broken_line B"
        and hB_Ncut: "B \<subseteq> ?Ncut"
        and hQ'_B: "Q' \<in> B"
        and hS'_B: "S' \<in> B"
      proof -
        obtain B where hB_bl: "geotop_is_broken_line B"
          and hB_sub: "B \<subseteq> B\<^sub>m \<union> B\<^sub>S"
          and hQ'_B: "Q' \<in> B"
          and hS'_B: "S' \<in> B"
          using geotop_broken_line_arc_reduction
              [OF hB\<^sub>m_bl hB\<^sub>S_bl hQ'_B\<^sub>m hS1_B\<^sub>m hS1_B\<^sub>S hS'_B\<^sub>S]
          by (elim exE conjE)
        have hB\<^sub>m_Ncut: "B\<^sub>m \<subseteq> ?Ncut"
          using hB\<^sub>m_sub hB\<^sub>Q_Ncut hB\<^sub>0_Ncut by (by100 blast)
        have hB_Ncut: "B \<subseteq> ?Ncut"
          using hB_sub hB\<^sub>m_Ncut hB\<^sub>S_Ncut by (by100 blast)
        show ?thesis
          using hB_bl hB_Ncut hQ'_B hS'_B by (rule that)
      qed
      show ?thesis
        by (rule hD44_broken_line_in_Ncut_suffices
            [OF hB_bl hB_Ncut hQ'_B hS'_B])
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
