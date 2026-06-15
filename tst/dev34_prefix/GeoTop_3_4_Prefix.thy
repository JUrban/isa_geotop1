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

lemma geotop_iterated_Sd_selected_arc_carrier_compact_prefix:
  fixes K :: "(real^2) set set" and A N :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hKfin: "finite K"
  assumes hN_def:
    "N = (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A \<noteq> {}})"
  shows "compact N"
proof -
  have hSd_sub: "geotop_is_subdivision (geotop_iterated_Sd m K) K"
    by (rule geotop_iterated_Sd_is_subdivision[OF hK hKfin])
  have hSd_complex: "geotop_is_complex (geotop_iterated_Sd m K)"
    using hSd_sub unfolding geotop_is_subdivision_def by (by100 blast)
  have hSd_fin: "finite (geotop_iterated_Sd m K)"
    by (rule geotop_subdivision_of_finite_is_finite[OF hKfin hSd_sub])
  have hSd_compact_all: "\<forall>B\<in>geotop_iterated_Sd m K. compact B"
  proof
    fix B
    assume hB: "B \<in> geotop_iterated_Sd m K"
    have hB_simplex: "geotop_is_simplex B"
      using geotop_is_complex_simplex[OF hSd_complex] hB by (by100 blast)
    show "compact B"
      by (rule geotop_simplex_compact[OF hB_simplex])
  qed
  have hN_index_fin:
      "finite {B\<in>geotop_iterated_Sd m K. B \<inter> A \<noteq> {}}"
    using hSd_fin by (by100 simp)
  have hN_index_compact:
      "\<forall>B\<in>{B\<in>geotop_iterated_Sd m K. B \<inter> A \<noteq> {}}. compact B"
    using hSd_compact_all by (by100 blast)
  show ?thesis
    unfolding hN_def
    by (rule compact_Union[OF hN_index_fin hN_index_compact])
qed

lemma geotop_iterated_Sd_selected_arc_carrier_closed_prefix:
  fixes K :: "(real^2) set set" and A N :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hKfin: "finite K"
  assumes hN_def:
    "N = (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A \<noteq> {}})"
  shows "closed N"
proof -
  have hN_compact: "compact N"
    by (rule geotop_iterated_Sd_selected_arc_carrier_compact_prefix
        [OF hK hKfin hN_def])
  show ?thesis
    by (rule compact_imp_closed[OF hN_compact])
qed

lemma geotop_iterated_Sd_selected_arc_carrier_subset_polyhedron_prefix:
  fixes K :: "(real^2) set set" and A N :: "(real^2) set"
  assumes hN_def:
    "N = (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A \<noteq> {}})"
  shows "N \<subseteq> geotop_polyhedron (geotop_iterated_Sd m K)"
  unfolding hN_def geotop_polyhedron_def by (by100 blast)

lemma geotop_polygon_iterated_Sd_selected_arc_carrier_subset_closed_disk_prefix:
  fixes J A N :: "(real^2) set" and K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKfin: "finite K"
  assumes hK_poly:
    "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hN_def:
    "N = (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A \<noteq> {}})"
  shows
    "N \<subseteq> closure_on UNIV geotop_euclidean_topology
      (geotop_polygon_interior J)"
proof -
  have hSd_sub: "geotop_is_subdivision (geotop_iterated_Sd m K) K"
    by (rule geotop_iterated_Sd_is_subdivision[OF hK hKfin])
  have hSd_poly:
      "geotop_polyhedron (geotop_iterated_Sd m K) = geotop_polyhedron K"
    using hSd_sub unfolding geotop_is_subdivision_def by (by100 blast)
  have hN_sub_Sd_poly: "N \<subseteq> geotop_polyhedron (geotop_iterated_Sd m K)"
    by (rule geotop_iterated_Sd_selected_arc_carrier_subset_polyhedron_prefix
        [OF hN_def])
  show ?thesis
    using hN_sub_Sd_poly hSd_poly hK_poly by (by100 simp)
qed

lemma geotop_polygon_iterated_Sd_selected_arc_carrier_closed_disk_restrict_eq_prefix:
  fixes J A N N\<^sub>I :: "(real^2) set" and K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKfin: "finite K"
  assumes hK_poly:
    "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hN_def:
    "N = (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A \<noteq> {}})"
  assumes hN\<^sub>I_def:
    "N\<^sub>I =
      N \<inter> closure_on UNIV geotop_euclidean_topology
        (geotop_polygon_interior J)"
  shows "N\<^sub>I = N"
proof -
  have hN_sub_disk:
      "N \<subseteq> closure_on UNIV geotop_euclidean_topology
        (geotop_polygon_interior J)"
    by (rule geotop_polygon_iterated_Sd_selected_arc_carrier_subset_closed_disk_prefix
        [OF hK hKfin hK_poly hN_def])
  show ?thesis
    unfolding hN\<^sub>I_def using hN_sub_disk by (by100 blast)
qed

lemma geotop_polygon_iterated_Sd_selected_arc_carrier_cut_open_prefix:
  fixes J A1 A2 N :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hA2:
    "geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2)"
  assumes hK: "geotop_is_complex K"
  assumes hKfin: "finite K"
  assumes hN_def:
    "N = (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}})"
  shows "geotop_polygon_interior J - (N \<union> A2) \<in> geotop_euclidean_topology"
proof -
  have hN_closed: "closed N"
    by (rule geotop_iterated_Sd_selected_arc_carrier_closed_prefix
        [OF hK hKfin hN_def])
  obtain \<gamma> :: "real \<Rightarrow> real^2" where h\<gamma>_arc: "arc \<gamma>"
    and h\<gamma>_img: "path_image \<gamma> = A2"
    using geotop_is_arc_imp_HOL_arc[OF hA2] by (by100 blast)
  have hA2_closed: "closed A2"
    using closed_arc_image[OF h\<gamma>_arc] h\<gamma>_img by (by100 simp)
  have hI_open_HOL: "open (geotop_polygon_interior J)"
    by (rule polygon_interior_open[OF hJ])
  have hN_A2_closed: "closed (N \<union> A2)"
    by (rule closed_Un[OF hN_closed hA2_closed])
  have hNcut_open_HOL: "open (geotop_polygon_interior J - (N \<union> A2))"
    by (rule open_Diff[OF hI_open_HOL hN_A2_closed])
  show ?thesis
    using hNcut_open_HOL
    unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
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

lemma geotop_connected_subset_broken_line_subarc_with_endpoints_prefix:
  fixes B W :: "(real^2) set" and X Y :: "real^2"
  assumes hB: "geotop_is_broken_line B"
  assumes hW_sub: "W \<subseteq> B"
  assumes hW_conn: "connected W"
  assumes hX: "X \<in> W"
  assumes hY: "Y \<in> W"
  assumes hXY: "X \<noteq> Y"
  shows "\<exists>C. geotop_is_broken_line C
      \<and> C \<subseteq> W
      \<and> X \<in> C
      \<and> Y \<in> C
      \<and> geotop_arc_endpoints C {X, Y}"
proof -
  have hB_arc:
      "geotop_is_arc B
        (subspace_topology UNIV geotop_euclidean_topology B)"
    using hB unfolding geotop_is_broken_line_def by (by100 blast)
  obtain \<gamma> :: "real \<Rightarrow> real^2"
    where h\<gamma>_arc: "arc \<gamma>" and h\<gamma>_img: "path_image \<gamma> = B"
    using geotop_is_arc_imp_HOL_arc[OF hB_arc] by (by100 blast)
  have hX_B: "X \<in> B"
    using hW_sub hX by (by100 blast)
  have hY_B: "Y \<in> B"
    using hW_sub hY by (by100 blast)
  obtain sX where hsX: "sX \<in> {0::real..1}" and h\<gamma>sX: "\<gamma> sX = X"
    using hX_B h\<gamma>_img unfolding path_image_def by (by100 blast)
  obtain sY where hsY: "sY \<in> {0::real..1}" and h\<gamma>sY: "\<gamma> sY = Y"
    using hY_B h\<gamma>_img unfolding path_image_def by (by100 blast)
  have hsXY: "sX \<noteq> sY"
    using h\<gamma>sX h\<gamma>sY hXY by (by100 blast)
  define s_lo where "s_lo = min sX sY"
  define s_hi where "s_hi = max sX sY"
  have hsX_lb: "0 \<le> sX" and hsX_ub: "sX \<le> 1"
    using hsX by (by100 simp_all)
  have hsY_lb: "0 \<le> sY" and hsY_ub: "sY \<le> 1"
    using hsY by (by100 simp_all)
  have hs_lo_range: "s_lo \<in> {0..1}"
    unfolding s_lo_def using hsX_lb hsX_ub hsY_lb hsY_ub by (by100 simp)
  have hs_hi_range: "s_hi \<in> {0..1}"
    unfolding s_hi_def using hsX_lb hsX_ub hsY_lb hsY_ub by (by100 simp)
  have hs_lt: "s_lo < s_hi"
    using hsXY unfolding s_lo_def s_hi_def by (by100 simp)
  have hs_lo_ne_hi: "s_lo \<noteq> s_hi"
    using hs_lt by (by100 simp)
  let ?T = "{t\<in>{0..1}. \<gamma> t \<in> W}"
  have hW_sub_path: "W \<subseteq> path_image \<gamma>"
    using hW_sub h\<gamma>_img by (by100 simp)
  have hT_interval: "is_interval ?T"
    by (rule geotop_arc_preimage_is_interval
        [OF h\<gamma>_arc hW_sub_path hW_conn])
  have hsX_T: "sX \<in> ?T"
    using hsX h\<gamma>sX hX by (by100 simp)
  have hsY_T: "sY \<in> ?T"
    using hsY h\<gamma>sY hY by (by100 simp)
  have h_seg_eq: "closed_segment s_lo s_hi = {s_lo..s_hi}"
    using hs_lt unfolding closed_segment_eq_real_ivl by (by100 simp)
  have hseg_T: "closed_segment s_lo s_hi \<subseteq> ?T"
  proof
    fix t
    assume ht: "t \<in> closed_segment s_lo s_hi"
    have ht_ivl: "t \<in> {s_lo..s_hi}"
      using ht h_seg_eq by (by100 simp)
    have hbetween:
        "(sX \<le> t \<and> t \<le> sY) \<or> (sY \<le> t \<and> t \<le> sX)"
      using ht_ivl unfolding s_lo_def s_hi_def by (by100 simp)
    show "t \<in> ?T"
      using hT_interval hsX_T hsY_T hbetween
      unfolding is_interval_1 by (by100 blast)
  qed
  define \<gamma>' where "\<gamma>' = subpath sX sY \<gamma>"
  let ?C = "path_image (subpath s_lo s_hi \<gamma>)"
  have hsub_arc: "arc (subpath s_lo s_hi \<gamma>)"
    by (rule arc_subpath_arc[OF h\<gamma>_arc hs_lo_range hs_hi_range hs_lo_ne_hi])
  have hC_img: "?C = \<gamma> ` closed_segment s_lo s_hi"
    by (rule path_image_subpath_gen)
  have hC_sub_W: "?C \<subseteq> W"
    using hC_img hseg_T by (by100 blast)
  have hsX_seg: "sX \<in> closed_segment s_lo s_hi"
  proof -
    have "sX \<in> {s_lo..s_hi}"
      unfolding s_lo_def s_hi_def by (by100 simp)
    thus ?thesis
      using h_seg_eq by (by100 simp)
  qed
  have hsY_seg: "sY \<in> closed_segment s_lo s_hi"
  proof -
    have "sY \<in> {s_lo..s_hi}"
      unfolding s_lo_def s_hi_def by (by100 simp)
    thus ?thesis
      using h_seg_eq by (by100 simp)
  qed
  have hX_C: "X \<in> ?C"
    using hC_img hsX_seg h\<gamma>sX by (by100 blast)
  have hY_C: "Y \<in> ?C"
    using hC_img hsY_seg h\<gamma>sY by (by100 blast)
  have hC_geotop_arc:
      "geotop_is_arc ?C
        (subspace_topology UNIV geotop_euclidean_topology ?C)"
    by (rule geotop_HOL_arc_imp_geotop_is_arc[OF hsub_arc])
  have hC_poly_im:
      "\<exists>K'. geotop_is_complex K'
        \<and> geotop_polyhedron K' = \<gamma> ` closed_segment s_lo s_hi
        \<and> geotop_complex_is_1dim K'"
    by (rule geotop_subarc_polyhedron
        [OF hB h\<gamma>_arc h\<gamma>_img hs_lo_range hs_hi_range hs_lt])
  have hC_poly:
      "\<exists>K'. geotop_is_complex K'
        \<and> geotop_polyhedron K' = ?C
        \<and> geotop_complex_is_1dim K'"
    using hC_poly_im hC_img by (by100 simp)
  have hC_bl: "geotop_is_broken_line ?C"
    unfolding geotop_is_broken_line_def
    using hC_poly hC_geotop_arc by (by100 blast)
  have h\<gamma>'_arc: "arc \<gamma>'"
    unfolding \<gamma>'_def
    by (rule arc_subpath_arc[OF h\<gamma>_arc hsX hsY hsXY])
  have h\<gamma>'_start: "pathstart \<gamma>' = X"
    unfolding \<gamma>'_def pathstart_def subpath_def using h\<gamma>sX by (by100 simp)
  have h\<gamma>'_finish: "pathfinish \<gamma>' = Y"
    unfolding \<gamma>'_def pathfinish_def subpath_def using h\<gamma>sY by (by100 simp)
  have h\<gamma>'_image: "path_image \<gamma>' = ?C"
  proof -
    have h1: "path_image \<gamma>' = \<gamma> ` closed_segment sX sY"
      unfolding \<gamma>'_def by (rule path_image_subpath_gen)
    have h2: "?C = \<gamma> ` closed_segment s_lo s_hi"
      by (rule path_image_subpath_gen)
    have hseg_eq:
        "closed_segment sX sY = closed_segment s_lo s_hi"
    proof -
      have hleft:
          "closed_segment sX sY = {min sX sY..max sX sY}"
        unfolding closed_segment_eq_real_ivl by (by100 simp)
      have hright: "closed_segment s_lo s_hi = {s_lo..s_hi}"
        using hs_lt unfolding closed_segment_eq_real_ivl by (by100 simp)
      show ?thesis
        using hleft hright unfolding s_lo_def s_hi_def by (by100 simp)
    qed
    show ?thesis
      using h1 h2 hseg_eq by (by100 simp)
  qed
  have hC_end_raw:
      "geotop_arc_endpoints (path_image \<gamma>')
        {pathstart \<gamma>', pathfinish \<gamma>'}"
    by (rule geotop_HOL_arc_imp_geotop_arc_endpoints_prefix[OF h\<gamma>'_arc])
  have hC_end: "geotop_arc_endpoints ?C {X, Y}"
    using hC_end_raw h\<gamma>'_image h\<gamma>'_start h\<gamma>'_finish by (by100 simp)
  show ?thesis
    using hC_bl hC_sub_W hX_C hY_C hC_end by (intro exI conjI)
qed

lemma geotop_connected_witness_component_at_intro_prefix:
  fixes U W :: "(real^2) set" and X Y :: "real^2"
  assumes hW_U: "W \<subseteq> U"
  assumes hX_W: "X \<in> W"
  assumes hY_W: "Y \<in> W"
  assumes hW_conn:
    "top1_connected_on W
      (subspace_topology UNIV geotop_euclidean_topology W)"
  shows "Y \<in> geotop_component_at UNIV geotop_euclidean_topology U X"
  (**
    Component bookkeeping used in D42/D44: a connected witness inside the
    ambient open set is already a witness for membership in the component at
    its base point. **)
proof -
  have hW_witness:
      "W \<in> {C. C \<subseteq> U \<and> X \<in> C \<and>
        top1_connected_on C
          (subspace_topology UNIV geotop_euclidean_topology C)}"
    using hW_U hX_W hW_conn by (by100 simp)
  show ?thesis
    unfolding geotop_component_at_def
    using hW_witness hY_W by (by100 blast)
qed

lemma geotop_connected_closure_corridor_same_component_open_prefix:
  fixes U C :: "(real^2) set" and X Y :: "real^2"
  assumes hUopen: "U \<in> geotop_euclidean_topology"
  assumes hXU: "X \<in> U"
  assumes hYU: "Y \<in> U"
  assumes hC_U: "C \<subseteq> U"
  assumes hC_conn:
    "top1_connected_on C
      (subspace_topology UNIV geotop_euclidean_topology C)"
  assumes hX_cl: "X \<in> closure C"
  assumes hY_cl: "Y \<in> closure C"
  shows "Y \<in> geotop_component_at UNIV geotop_euclidean_topology U X"
  (**
    Closure-corridor form of the component bookkeeping used in D44.  If an
    open Euclidean region contains a connected corridor whose closure touches
    two interior access points, small balls at the access points attach to the
    corridor and give an actual connected witness inside the region. **)
proof -
  have hUopen_HOL: "open U"
    using hUopen
    unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  obtain r\<^sub>X where hr\<^sub>X_pos: "0 < r\<^sub>X"
    and hball_X_U: "ball X r\<^sub>X \<subseteq> U"
    using hUopen_HOL hXU open_contains_ball by (by100 blast)
  obtain r\<^sub>Y where hr\<^sub>Y_pos: "0 < r\<^sub>Y"
    and hball_Y_U: "ball Y r\<^sub>Y \<subseteq> U"
    using hUopen_HOL hYU open_contains_ball by (by100 blast)
  have hC_conn_HOL: "connected C"
    by (rule iffD1[OF top1_connected_on_geotop_iff_connected hC_conn])
  have hball_X_conn: "connected (ball X r\<^sub>X)"
    by (rule connected_ball)
  have hball_Y_conn: "connected (ball Y r\<^sub>Y)"
    by (rule connected_ball)
  have hC_X_meet: "C \<inter> ball X r\<^sub>X \<noteq> {}"
    by (rule geotop_closure_point_meets_centered_ball_prefix
        [OF hX_cl hr\<^sub>X_pos])
  have hC_Y_meet: "C \<inter> ball Y r\<^sub>Y \<noteq> {}"
    by (rule geotop_closure_point_meets_centered_ball_prefix
        [OF hY_cl hr\<^sub>Y_pos])
  have hCX_conn: "connected (C \<union> ball X r\<^sub>X)"
    by (rule connected_Un[OF hC_conn_HOL hball_X_conn hC_X_meet])
  have hCX_Y_meet: "(C \<union> ball X r\<^sub>X) \<inter> ball Y r\<^sub>Y \<noteq> {}"
  proof -
    obtain z where hz: "z \<in> C \<inter> ball Y r\<^sub>Y"
      using hC_Y_meet by (by100 blast)
    have "z \<in> (C \<union> ball X r\<^sub>X) \<inter> ball Y r\<^sub>Y"
      using hz by (by100 blast)
    thus ?thesis
      by (by100 blast)
  qed
  let ?W = "C \<union> ball X r\<^sub>X \<union> ball Y r\<^sub>Y"
  have hW_conn_HOL: "connected ?W"
    by (rule connected_Un[OF hCX_conn hball_Y_conn hCX_Y_meet])
  have hW_conn:
      "top1_connected_on ?W
        (subspace_topology UNIV geotop_euclidean_topology ?W)"
    by (rule iffD2[OF top1_connected_on_geotop_iff_connected hW_conn_HOL])
  have hW_U: "?W \<subseteq> U"
    using hC_U hball_X_U hball_Y_U by (by100 blast)
  have hX_W: "X \<in> ?W"
    using hr\<^sub>X_pos by (by100 simp)
  have hY_W: "Y \<in> ?W"
    using hr\<^sub>Y_pos by (by100 simp)
  show ?thesis
    by (rule geotop_connected_witness_component_at_intro_prefix
        [OF hW_U hX_W hY_W hW_conn])
qed

lemma geotop_component_member_gives_closed_corridor_prefix:
  fixes U :: "(real^2) set" and X Y :: "real^2"
  assumes hY_comp:
    "Y \<in> geotop_component_at UNIV geotop_euclidean_topology U X"
  shows "\<exists>C. C \<subseteq> U
      \<and> top1_connected_on C
          (subspace_topology UNIV geotop_euclidean_topology C)
      \<and> X \<in> closure C
      \<and> Y \<in> closure C"
  (**
    Component-to-corridor bookkeeping used in D44: an actual component
    membership already contains a connected witness inside the ambient cut-open
    set; taking its ordinary closure gives the closed-corridor form used by
    the access-collar reductions. **)
proof -
  obtain C where hC:
      "C \<subseteq> U
        \<and> X \<in> C
        \<and> top1_connected_on C
            (subspace_topology UNIV geotop_euclidean_topology C)"
    and hY_C: "Y \<in> C"
    using hY_comp unfolding geotop_component_at_def by (by100 blast)
  have hC_sub: "C \<subseteq> U"
    using hC by (by100 blast)
  have hX_C: "X \<in> C"
    using hC by (by100 blast)
  have hC_conn:
      "top1_connected_on C
        (subspace_topology UNIV geotop_euclidean_topology C)"
    using hC by (by100 blast)
  have hX_cl: "X \<in> closure C"
    using hX_C closure_subset by (by100 blast)
  have hY_cl: "Y \<in> closure C"
    using hY_C closure_subset by (by100 blast)
  show ?thesis
    using hC_sub hC_conn hX_cl hY_cl by (intro exI conjI)
qed

lemma geotop_component_closure_pair_gives_closed_corridor_prefix:
  fixes U C :: "(real^2) set" and X Y :: "real^2"
  assumes hC_comp: "C \<in> components U"
  assumes hX_cl: "X \<in> closure C"
  assumes hY_cl: "Y \<in> closure C"
  shows "\<exists>Z. Z \<subseteq> U
      \<and> top1_connected_on Z
          (subspace_topology UNIV geotop_euclidean_topology Z)
      \<and> X \<in> closure Z
      \<and> Y \<in> closure Z"
  (**
    Moise 4.4 component-frontier bookkeeping: if the two access points are in
    the ordinary closure of one HOL component of the cut-open set, then that
    component is exactly the closed corridor used by the local collar
    reductions. **)
proof -
  have hC_sub: "C \<subseteq> U"
    by (rule in_components_subset[OF hC_comp])
  have hC_conn_HOL: "connected C"
    by (rule in_components_connected[OF hC_comp])
  have hC_conn:
      "top1_connected_on C
        (subspace_topology UNIV geotop_euclidean_topology C)"
    by (rule iffD2[OF top1_connected_on_geotop_iff_connected hC_conn_HOL])
  show ?thesis
    using hC_sub hC_conn hX_cl hY_cl by (intro exI conjI)
qed

lemma geotop_component_at_closure_gives_component_closure_pair_prefix:
  fixes U :: "(real^2) set" and X Y :: "real^2"
  assumes hXU: "X \<in> U"
  assumes hY_cl:
    "Y \<in> closure
      (geotop_component_at UNIV geotop_euclidean_topology U X)"
  shows "\<exists>C. C \<in> components U
      \<and> X \<in> closure C
      \<and> Y \<in> closure C"
  (**
    Fixed-component version of the D44 component-frontier bookkeeping.  Once
    the adjacent outside component is identified as the component at the lower
    access point, ordinary closure at the upper access point gives Moise's
    "same component frontier" form. **)
proof -
  let ?C = "connected_component_set U X"
  have hC_comp: "?C \<in> components U"
    by (rule componentsI[OF hXU])
  have hcomponent_eq:
      "geotop_component_at UNIV geotop_euclidean_topology U X = ?C"
    by (rule geotop_component_at_UNIV_eq_connected_component_set)
  have hX_C: "X \<in> ?C"
    using hXU connected_component_refl by (by100 simp)
  have hX_cl: "X \<in> closure ?C"
    using hX_C closure_subset by (by100 blast)
  have hY_cl_C: "Y \<in> closure ?C"
    using hY_cl hcomponent_eq by (by100 simp)
  show ?thesis
    using hC_comp hX_cl hY_cl_C by (intro exI conjI)
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

lemma geotop_polygon_cyclic_order_QS_split_opposite_arc_prefix:
  assumes hcyc: "geotop_polygon_cyclic_order J P Q R S"
  assumes hP_F\<^sub>1: "P \<in> geotop_arc_interior F\<^sub>1 {Q, S}"
  assumes hsplit: "J = F\<^sub>1 \<union> F\<^sub>2"
  assumes hF\<^sub>1E: "geotop_arc_endpoints F\<^sub>1 {Q, S}"
  assumes hF\<^sub>2E: "geotop_arc_endpoints F\<^sub>2 {Q, S}"
  assumes hdisj:
    "geotop_arc_interior F\<^sub>1 {Q, S} \<inter>
      geotop_arc_interior F\<^sub>2 {Q, S} = {}"
  shows "R \<notin> geotop_arc_interior F\<^sub>1 {Q, S}"
  (**
    D42/D44 cyclic-order transfer: for a Q-S split of the polygon boundary,
    if the P-side is F\<^sub>1, then the cyclically opposite point R lies on the
    other Q-S side.  This is the exact book step used when transferring the
    regular-neighborhood route from the lower boundary side to the upper one. **)
  using hcyc hP_F\<^sub>1 hsplit hF\<^sub>1E hF\<^sub>2E hdisj
  by (by100 blast)

lemma geotop_polygon_two_endpoint_arcs_regular_neighborhood_frontier_component_package_prefix:
  fixes J A1 A2 N N\<^sub>I FrN\<^sub>I J\<^sub>N :: "(real^2) set"
    and K K\<^sub>N BdK\<^sub>N BdJ\<^sub>N :: "(real^2) set set"
    and P Q R S Q1 S1 :: "real^2"
    and m :: nat
    and r :: real
  assumes hJ: "geotop_is_polygon J"
  assumes hP: "P \<in> J" and hQ: "Q \<in> J" and hR: "R \<in> J" and hS: "S \<in> J"
  assumes hcyc: "geotop_polygon_cyclic_order J P Q R S"
  assumes hcard: "card {P, Q, R, S} = 4"
  assumes hA1: "geotop_is_arc A1 (subspace_topology UNIV geotop_euclidean_topology A1)"
  assumes hA2: "geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2)"
  assumes hA12: "A1 \<inter> A2 = {}"
  assumes hA1_sub:
    "A1 \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hA2_sub:
    "A2 \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hA1J: "A1 \<inter> J = {P}"
  assumes hA2J: "A2 \<inter> J = {R}"
  assumes hK_complex: "geotop_is_complex K"
  assumes hK_fin: "finite K"
  assumes hK_poly:
    "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hN_def:
    "N = (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}})"
  assumes hA1_N: "A1 \<subseteq> N"
  assumes hN_avoid: "N \<inter> (A2 \<union> {Q, S}) = {}"
  assumes hr: "0 < r"
  assumes hball_Q_N: "ball Q r \<inter> N = {}"
  assumes hball_S_N: "ball S r \<inter> N = {}"
  assumes hQ1_ball: "Q1 \<in> ball Q r"
  assumes hS1_ball: "S1 \<in> ball S r"
  assumes hQ1_Ncut: "Q1 \<in> geotop_polygon_interior J - (N \<union> A2)"
  assumes hS1_Ncut: "S1 \<in> geotop_polygon_interior J - (N \<union> A2)"
  assumes hN\<^sub>I_def:
    "N\<^sub>I =
      N \<inter> closure_on UNIV geotop_euclidean_topology
        (geotop_polygon_interior J)"
  assumes hFrN\<^sub>I_def:
    "FrN\<^sub>I = geotop_frontier UNIV geotop_euclidean_topology N\<^sub>I"
  assumes hJ\<^sub>N_def:
    "J\<^sub>N = geotop_component_at UNIV geotop_euclidean_topology FrN\<^sub>I P"
  assumes hK\<^sub>N_def: "K\<^sub>N = {\<sigma>\<in>geotop_iterated_Sd m K. \<sigma> \<subseteq> N}"
  assumes hBdK\<^sub>N_def: "BdK\<^sub>N = geotop_comb_boundary K\<^sub>N 2"
  assumes hBdJ\<^sub>N_def: "BdJ\<^sub>N = {\<rho>\<in>BdK\<^sub>N. \<rho> \<subseteq> J\<^sub>N}"
  shows
    "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2)
     \<and> (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        \<not> geotop_graph_endpoint BdJ\<^sub>N w)
     \<and> (\<exists>Z. Z \<subseteq> geotop_polygon_interior J - (N \<union> A2)
        \<and> top1_connected_on Z
            (subspace_topology UNIV geotop_euclidean_topology Z)
        \<and> Q1 \<in> closure Z
        \<and> S1 \<in> closure Z)"
  (**
    The remaining literal Moise 4.4 regular-neighborhood package.  For the
    chosen fine carrier of \<open>A1\<close>, the component of the carrier frontier through
    \<open>P\<close> is the book's polygonal 1-sphere: its boundary graph has local valence
    at most two and no endpoints.  The complementary frontier arc has one
    adjacent outside component of \<open>I - (N \<union> A2)\<close> whose closure contains the
    lower and upper access witnesses.  The surrounding proof turns this package
    into the lower-to-upper broken-line route and then into the final component
    transfer for Theorem 4.4. **)
proof -
  let ?Ncut = "geotop_polygon_interior J - (N \<union> A2)"
  have hP_in_A1: "P \<in> A1"
    using hA1J by (by100 blast)
  have hR_in_A2: "R \<in> A2"
    using hA2J by (by100 blast)
  have hSd_sub: "geotop_is_subdivision (geotop_iterated_Sd m K) K"
    by (rule geotop_iterated_Sd_is_subdivision[OF hK_complex hK_fin])
  have hSd_complex: "geotop_is_complex (geotop_iterated_Sd m K)"
    using hSd_sub unfolding geotop_is_subdivision_def by (by100 blast)
  have hSd_fin: "finite (geotop_iterated_Sd m K)"
    by (rule geotop_subdivision_of_finite_is_finite[OF hK_fin hSd_sub])
  have hSd_poly:
      "geotop_polyhedron (geotop_iterated_Sd m K) = geotop_polyhedron K"
    using hSd_sub unfolding geotop_is_subdivision_def by (by100 blast)
  have hP_N: "P \<in> N"
    using hP_in_A1 hA1_N by (by100 blast)
  have hN_compact: "compact N"
    by (rule geotop_iterated_Sd_selected_arc_carrier_compact_prefix
        [OF hK_complex hK_fin hN_def])
  have hN_closed: "closed N"
    by (rule geotop_iterated_Sd_selected_arc_carrier_closed_prefix
        [OF hK_complex hK_fin hN_def])
  have hN_sub_disk:
      "N \<subseteq> closure_on UNIV geotop_euclidean_topology
        (geotop_polygon_interior J)"
    by (rule geotop_polygon_iterated_Sd_selected_arc_carrier_subset_closed_disk_prefix
        [OF hK_complex hK_fin hK_poly hN_def])
  have hN_sub_Sd_poly: "N \<subseteq> geotop_polyhedron (geotop_iterated_Sd m K)"
    unfolding hN_def geotop_polyhedron_def by (by100 blast)
  have hN\<^sub>I_eq_N: "N\<^sub>I = N"
    by (rule
        geotop_polygon_iterated_Sd_selected_arc_carrier_closed_disk_restrict_eq_prefix
          [OF hK_complex hK_fin hK_poly hN_def hN\<^sub>I_def])
  have hP_N\<^sub>I: "P \<in> N\<^sub>I"
    using hP_N hN\<^sub>I_eq_N by (by100 simp)
  have hN\<^sub>I_compact: "compact N\<^sub>I"
    using hN\<^sub>I_eq_N hN_compact by (by100 simp)
  have hN\<^sub>I_closed: "closed N\<^sub>I"
    using hN\<^sub>I_eq_N hN_closed by (by100 simp)
  have hNcut_open: "?Ncut \<in> geotop_euclidean_topology"
    by (rule geotop_polygon_iterated_Sd_selected_arc_carrier_cut_open_prefix
        [OF hJ hA2 hK_complex hK_fin hN_def])
  have hFrN\<^sub>I_HOL: "FrN\<^sub>I = frontier N\<^sub>I"
    unfolding hFrN\<^sub>I_def by (rule geotop_frontier_UNIV_eq_frontier)
  have hFrN\<^sub>I_sub_N\<^sub>I: "FrN\<^sub>I \<subseteq> N\<^sub>I"
    using hFrN\<^sub>I_HOL frontier_subset_closed[OF hN\<^sub>I_closed] by (by100 simp)
  have hFrN\<^sub>I_sub_N: "FrN\<^sub>I \<subseteq> N"
    using hFrN\<^sub>I_sub_N\<^sub>I hN\<^sub>I_eq_N by (by100 simp)
  have hFrN\<^sub>I_closed: "closed FrN\<^sub>I"
    using hFrN\<^sub>I_HOL frontier_closed by (by100 simp)
  have hFrN\<^sub>I_compact: "compact FrN\<^sub>I"
    by (rule closed_subset_compact
        [OF hN\<^sub>I_compact hFrN\<^sub>I_closed hFrN\<^sub>I_sub_N\<^sub>I])
  have hFrN\<^sub>I_A2_QS_disj: "FrN\<^sub>I \<inter> (A2 \<union> {Q, S}) = {}"
    using hFrN\<^sub>I_sub_N hN_avoid by (by100 blast)
  have hR_not_FrN\<^sub>I: "R \<notin> FrN\<^sub>I"
    using hR_in_A2 hFrN\<^sub>I_A2_QS_disj by (by100 blast)
  have hP_FrN\<^sub>I: "P \<in> FrN\<^sub>I"
  proof -
    have hN\<^sub>I_sub_K_poly: "N\<^sub>I \<subseteq> geotop_polyhedron K"
      using hN\<^sub>I_eq_N hN_sub_disk hK_poly by (by100 simp)
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
    have hP_cl: "P \<in> closure N\<^sub>I"
      using hP_N\<^sub>I closure_subset by (by100 blast)
    have hP_front: "P \<in> frontier N\<^sub>I"
      using hP_cl hP_not_int_N\<^sub>I
      unfolding Elementary_Topology.frontier_def by (by100 blast)
    show ?thesis
      using hFrN\<^sub>I_HOL hP_front by (by100 simp)
  qed
  have hP_J\<^sub>N: "P \<in> J\<^sub>N"
  proof -
    have hTU: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
      by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
    have hP_singleton_conn:
        "top1_connected_on {P}
          (subspace_topology UNIV geotop_euclidean_topology {P})"
      by (rule top1_connected_on_singleton[OF hTU], simp)
    show ?thesis
      unfolding hJ\<^sub>N_def
      by (rule geotop_self_in_component_at[OF hP_FrN\<^sub>I hP_singleton_conn])
  qed
  have hJ\<^sub>N_sub_FrN\<^sub>I: "J\<^sub>N \<subseteq> FrN\<^sub>I"
    unfolding hJ\<^sub>N_def geotop_component_at_def by (by100 blast)
  have hJ\<^sub>N_sub_N: "J\<^sub>N \<subseteq> N"
    using hJ\<^sub>N_sub_FrN\<^sub>I hFrN\<^sub>I_sub_N by (by100 blast)
  have hJ\<^sub>N_A2_QS_disj: "J\<^sub>N \<inter> (A2 \<union> {Q, S}) = {}"
    using hJ\<^sub>N_sub_N hN_avoid by (by100 blast)
  have hR_not_J\<^sub>N: "R \<notin> J\<^sub>N"
    using hR_in_A2 hJ\<^sub>N_A2_QS_disj by (by100 blast)
  have hJ\<^sub>N_eq_connected_component:
      "J\<^sub>N = connected_component_set FrN\<^sub>I P"
    unfolding hJ\<^sub>N_def by (rule geotop_component_at_UNIV_eq_connected_component_set)
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
  have hK\<^sub>N_complex: "geotop_is_complex K\<^sub>N"
    unfolding hK\<^sub>N_def
    by (rule geotop_complex_restrict_subset_is_complex[OF hSd_complex])
  have hK\<^sub>N_fin: "finite K\<^sub>N"
    unfolding hK\<^sub>N_def using hSd_fin by (by100 simp)
  have hK\<^sub>N_poly: "geotop_polyhedron K\<^sub>N = N"
  proof -
    have hK\<^sub>N_poly_sub_N: "geotop_polyhedron K\<^sub>N \<subseteq> N"
      unfolding hK\<^sub>N_def geotop_polyhedron_def by (by100 blast)
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
        unfolding hK\<^sub>N_def by (by100 simp)
    qed
    show ?thesis
      using hK\<^sub>N_poly_sub_N hN_sub_K\<^sub>N_poly by (by100 blast)
  qed
  have hFrN\<^sub>I_frontier_K\<^sub>N_poly:
      "FrN\<^sub>I = frontier (geotop_polyhedron K\<^sub>N)"
    using hFrN\<^sub>I_HOL hN\<^sub>I_eq_N hK\<^sub>N_poly by (by100 simp)
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
  have hK\<^sub>N_edge_owned_by_Sd_2simplex:
      "\<And>e. e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
        \<exists>\<sigma>\<in>geotop_iterated_Sd m K.
          geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  proof -
    fix e
    assume heK\<^sub>N: "e \<in> K\<^sub>N"
      and hedge: "geotop_is_edge e"
    have heSd: "e \<in> geotop_iterated_Sd m K"
      using heK\<^sub>N unfolding hK\<^sub>N_def by (by100 simp)
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
      unfolding hK\<^sub>N_def using h\<sigma>Sd h\<sigma>subN by (by100 simp)
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
      using heK\<^sub>N unfolding hK\<^sub>N_def by (by100 simp)
    have he_sub_N: "e \<subseteq> N"
      using heK\<^sub>N unfolding hK\<^sub>N_def by (by100 simp)
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
      by (rule
          geotop_complex_two_2simplex_shared_edge_rel_interior_subset_HOL_interior_union_prefix
            [OF hK\<^sub>N_complex h\<sigma>K h\<tau>K h\<sigma>2 h\<tau>2 h\<sigma>\<tau>
              h\<sigma>face h\<tau>face hedge])
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
      have "p \<in> rel_interior e \<inter> FrN\<^sub>I"
        using hp_rel hp_Fr by (by100 blast)
      thus False
        using hdisj by (by100 blast)
    qed
  qed
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
      using h\<rho> unfolding hBdK\<^sub>N_def geotop_comb_boundary_def by (by100 simp)
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
      using h\<sigma>Bd unfolding hBdK\<^sub>N_def geotop_comb_boundary_def by (by100 simp)
    show "\<tau> \<in> BdK\<^sub>N"
    proof (rule UnE[OF h\<sigma>_cases])
      assume h\<sigma>S: "\<sigma> \<in> ?S"
      have "\<tau> \<in> {\<rho>. \<exists>\<eta>\<in>?S. geotop_is_face \<rho> \<eta>}"
        using h\<sigma>S h\<tau>\<sigma> by (by100 blast)
      thus "\<tau> \<in> BdK\<^sub>N"
        unfolding hBdK\<^sub>N_def geotop_comb_boundary_def by (by100 simp)
    next
      assume "\<sigma> \<in> {\<rho>. \<exists>\<eta>\<in>?S. geotop_is_face \<rho> \<eta>}"
      then obtain \<eta> where h\<eta>S: "\<eta> \<in> ?S" and h\<sigma>\<eta>: "geotop_is_face \<sigma> \<eta>"
        by (by100 blast)
      have h\<tau>\<eta>: "geotop_is_face \<tau> \<eta>"
        by (rule geotop_is_face_trans_prefix[OF h\<tau>\<sigma> h\<sigma>\<eta>])
      have "\<tau> \<in> {\<rho>. \<exists>\<eta>\<in>?S. geotop_is_face \<rho> \<eta>}"
        using h\<eta>S h\<tau>\<eta> by (by100 blast)
      thus "\<tau> \<in> BdK\<^sub>N"
        unfolding hBdK\<^sub>N_def geotop_comb_boundary_def by (by100 simp)
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
        using h\<rho>Bd unfolding hBdK\<^sub>N_def geotop_comb_boundary_def by (by100 simp)
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
      using heBd unfolding hBdK\<^sub>N_def geotop_comb_boundary_def by (by100 simp)
    show "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
    proof (rule UnE[OF he_cases])
      assume heS: "e \<in> ?S"
      thus "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
        by (by100 simp)
    next
      assume "e \<in> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
      then obtain \<tau> where h\<tau>S: "\<tau> \<in> ?S" and heface\<tau>: "geotop_is_face e \<tau>"
        by (by100 blast)
      have h\<tau>1: "geotop_simplex_dim \<tau> 1"
        using h\<tau>S by (by100 simp)
      have he1: "geotop_simplex_dim e 1"
        using hedge unfolding geotop_is_edge_def by (by100 simp)
      obtain k where hk_le: "k \<le> 1" and hek: "geotop_simplex_dim e k"
        using geotop_face_dim_le_prefix[OF h\<tau>1 heface\<tau>] by (by100 blast)
      have hk1: "k = 1"
        by (rule geotop_simplex_dim_unique[OF hek he1])
      have h\<tau>edge: "geotop_is_edge \<tau>"
        using h\<tau>1 unfolding geotop_is_edge_def by (by100 simp)
      have he_eq_\<tau>: "e = \<tau>"
        by (rule geotop_edge_face_of_edge_eq_prefix[OF hedge h\<tau>edge heface\<tau>])
      show "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
        using h\<tau>S he_eq_\<tau> by (by100 simp)
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
      unfolding hBdK\<^sub>N_def geotop_comb_boundary_def using heS by (by100 simp)
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
      using h\<rho>Bd unfolding hBdK\<^sub>N_def geotop_comb_boundary_def by (by100 simp)
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
  have hBdJ\<^sub>N_sub_BdK\<^sub>N: "BdJ\<^sub>N \<subseteq> BdK\<^sub>N"
    unfolding hBdJ\<^sub>N_def by (by100 blast)
  have hBdJ\<^sub>N_fin: "finite BdJ\<^sub>N"
    by (rule finite_subset[OF hBdJ\<^sub>N_sub_BdK\<^sub>N hBdK\<^sub>N_fin])
  have hBdJ\<^sub>N_face_closed:
      "\<forall>\<sigma>\<in>BdJ\<^sub>N. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> BdJ\<^sub>N"
  proof (intro ballI allI impI)
    fix \<sigma> \<tau>
    assume h\<sigma>BdJ: "\<sigma> \<in> BdJ\<^sub>N"
      and h\<tau>\<sigma>: "geotop_is_face \<tau> \<sigma>"
    have h\<sigma>Bd: "\<sigma> \<in> BdK\<^sub>N"
      using h\<sigma>BdJ unfolding hBdJ\<^sub>N_def by (by100 simp)
    have h\<sigma>J: "\<sigma> \<subseteq> J\<^sub>N"
      using h\<sigma>BdJ unfolding hBdJ\<^sub>N_def by (by100 simp)
    have h\<tau>Bd: "\<tau> \<in> BdK\<^sub>N"
      using hBdK\<^sub>N_face_closed h\<sigma>Bd h\<tau>\<sigma> by (by100 blast)
    have h\<tau>sub\<sigma>: "\<tau> \<subseteq> \<sigma>"
      by (rule geotop_is_face_imp_subset_prefix[OF h\<tau>\<sigma>])
    have h\<tau>J: "\<tau> \<subseteq> J\<^sub>N"
      using h\<tau>sub\<sigma> h\<sigma>J by (by100 blast)
    show "\<tau> \<in> BdJ\<^sub>N"
      unfolding hBdJ\<^sub>N_def using h\<tau>Bd h\<tau>J by (by100 simp)
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
  have hBdJ\<^sub>N_poly_compact: "compact (geotop_polyhedron BdJ\<^sub>N)"
    by (rule geotop_complex_polyhedron_compact
        [OF hBdJ\<^sub>N_complex hBdJ\<^sub>N_fin])
  have hBdJ\<^sub>N_poly_closed: "closed (geotop_polyhedron BdJ\<^sub>N)"
    by (rule geotop_complex_polyhedron_closed
        [OF hBdJ\<^sub>N_complex hBdJ\<^sub>N_fin])
  have hBdJ\<^sub>N_poly_sub_J\<^sub>N: "geotop_polyhedron BdJ\<^sub>N \<subseteq> J\<^sub>N"
    unfolding hBdJ\<^sub>N_def geotop_polyhedron_def by (by100 blast)
  have hBdJ\<^sub>N_poly_sub_FrN\<^sub>I: "geotop_polyhedron BdJ\<^sub>N \<subseteq> FrN\<^sub>I"
    using hBdJ\<^sub>N_poly_sub_J\<^sub>N hJ\<^sub>N_sub_FrN\<^sub>I by (by100 blast)
  have hBdJ\<^sub>N_edge_sub_J\<^sub>N:
      "\<And>e. e \<in> BdJ\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> e \<subseteq> J\<^sub>N"
    unfolding hBdJ\<^sub>N_def by (by100 simp)
  have hBdJ\<^sub>N_edge_sub_FrN\<^sub>I:
      "\<And>e. e \<in> BdJ\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> e \<subseteq> FrN\<^sub>I"
  proof -
    fix e
    assume heBdJ: "e \<in> BdJ\<^sub>N" and hedge: "geotop_is_edge e"
    have heJ: "e \<subseteq> J\<^sub>N"
      by (rule hBdJ\<^sub>N_edge_sub_J\<^sub>N[OF heBdJ hedge])
    show "e \<subseteq> FrN\<^sub>I"
      using heJ hJ\<^sub>N_sub_FrN\<^sub>I by (by100 blast)
  qed
  have hBdJ\<^sub>N_edge_member_incident_count_one:
      "\<And>e. e \<in> BdJ\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
        card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
  proof -
    fix e
    assume heBdJ: "e \<in> BdJ\<^sub>N" and hedge: "geotop_is_edge e"
    have heBdK: "e \<in> BdK\<^sub>N"
      using heBdJ unfolding hBdJ\<^sub>N_def by (by100 simp)
    show "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
      by (rule hBdK\<^sub>N_edge_member_incident_count_one[OF heBdK hedge])
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
  have hBdK\<^sub>N_edge_meets_J\<^sub>N_in_BdJ\<^sub>N:
      "\<And>e. e \<in> BdK\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
        e \<inter> J\<^sub>N \<noteq> {} \<Longrightarrow> e \<in> BdJ\<^sub>N"
    unfolding hBdJ\<^sub>N_def
    using hBdK\<^sub>N_edge_meets_J\<^sub>N_subset_J\<^sub>N by (by100 blast)
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
  have hD44_regular_neighborhood_frontier_component_book_step: ?thesis
    (**
      Remaining Moise 4.4 content after the carrier restriction setup:
      prove that the frontier component of \<open>N\<^sub>I = N \<inter> cl I\<close> through \<open>P\<close>
      is the polygonal regular-neighborhood boundary component, with the
      restricted boundary graph locally valence at most two and no endpoints,
      and prove that the complementary frontier arc has an adjacent connected
      outside corridor in \<open>?Ncut\<close> whose closure contains \<open>Q1\<close> and \<open>S1\<close>. **)
    sorry
  show ?thesis
    by (rule hD44_regular_neighborhood_frontier_component_book_step)
qed

lemma geotop_polygon_two_endpoint_arcs_fine_carrier_broken_line_access_crossings_prefix:
  fixes J A1 A2 N :: "(real^2) set"
    and K :: "(real^2) set set"
    and P Q R S Q1 S1 :: "real^2"
    and m :: nat
    and r :: real
  assumes hJ: "geotop_is_polygon J"
  assumes hP: "P \<in> J" and hQ: "Q \<in> J" and hR: "R \<in> J" and hS: "S \<in> J"
  assumes hcyc: "geotop_polygon_cyclic_order J P Q R S"
  assumes hcard: "card {P, Q, R, S} = 4"
  assumes hA1: "geotop_is_arc A1 (subspace_topology UNIV geotop_euclidean_topology A1)"
  assumes hA2: "geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2)"
  assumes hA12: "A1 \<inter> A2 = {}"
  assumes hA1_sub:
    "A1 \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hA2_sub:
    "A2 \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hA1J: "A1 \<inter> J = {P}"
  assumes hA2J: "A2 \<inter> J = {R}"
  assumes hK_complex: "geotop_is_complex K"
  assumes hK_fin: "finite K"
  assumes hK_poly:
    "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hN_def:
    "N = (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}})"
  assumes hA1_N: "A1 \<subseteq> N"
  assumes hN_avoid: "N \<inter> (A2 \<union> {Q, S}) = {}"
  assumes hr: "0 < r"
  assumes hball_Q_N: "ball Q r \<inter> N = {}"
  assumes hball_S_N: "ball S r \<inter> N = {}"
  assumes hQ1_ball: "Q1 \<in> ball Q r"
  assumes hS1_ball: "S1 \<in> ball S r"
  assumes hQ1_Ncut: "Q1 \<in> geotop_polygon_interior J - (N \<union> A2)"
  assumes hS1_Ncut: "S1 \<in> geotop_polygon_interior J - (N \<union> A2)"
  shows
    "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
      \<exists>B. geotop_is_broken_line B
        \<and> B \<subseteq> geotop_polygon_interior J - (N \<union> A2)
        \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
        \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
  (**
    Named Moise 4.4 regular-neighborhood construction.  This is the remaining
    book step in its most literal useful form: choose the fine carrier of
    \<open>A1\<close>, restrict it to the closed polygonal disk, analyze the frontier
    component through \<open>P\<close> as a polygonal 1-sphere, split it into the boundary
    arc and complementary frontier arc, choose the lower-to-upper broken-line
    subarc, and show that the adjacent outside side supplies broken-line
    crossings of every prescribed pair of access collars around \<open>Q1\<close> and
    \<open>S1\<close>. **)
proof -
  let ?Ncut = "geotop_polygon_interior J - (N \<union> A2)"
  have hP_in_A1: "P \<in> A1"
    using hA1J by (by100 blast)
  have hR_in_A2: "R \<in> A2"
    using hA2J by (by100 blast)
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
    by (rule geotop_polygon_iterated_Sd_selected_arc_carrier_subset_closed_disk_prefix
        [OF hK_complex hK_fin hK_poly hN_def])
  have hN_compact: "compact N"
    by (rule geotop_iterated_Sd_selected_arc_carrier_compact_prefix
        [OF hK_complex hK_fin hN_def])
  have hN_closed: "closed N"
    by (rule geotop_iterated_Sd_selected_arc_carrier_closed_prefix
        [OF hK_complex hK_fin hN_def])
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
  have hA2_closed: "closed A2"
    using geotop_two_arcs_compact_closed_prefix[OF hA1 hA2] by (by100 blast)
  have hI_open_HOL: "open (geotop_polygon_interior J)"
    by (rule polygon_interior_open[OF hJ])
  have hN_A2_closed: "closed (N \<union> A2)"
    by (rule closed_Un[OF hN_closed hA2_closed])
  have hNcut_open_HOL: "open ?Ncut"
    by (rule open_Diff[OF hI_open_HOL hN_A2_closed])
  have hNcut_open: "?Ncut \<in> geotop_euclidean_topology"
    using hNcut_open_HOL
    unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have hQ1_local_Ncut_ball:
      "\<exists>\<epsilon>>0. ball Q1 \<epsilon> \<subseteq> ?Ncut"
    using hNcut_open_HOL hQ1_Ncut open_contains_ball by (by100 blast)
  have hS1_local_Ncut_ball:
      "\<exists>\<epsilon>>0. ball S1 \<epsilon> \<subseteq> ?Ncut"
    using hNcut_open_HOL hS1_Ncut open_contains_ball by (by100 blast)
  define N\<^sub>I where
      "N\<^sub>I = N \<inter> closure_on UNIV geotop_euclidean_topology
        (geotop_polygon_interior J)"
  have hN\<^sub>I_eq_N: "N\<^sub>I = N"
    by (rule
        geotop_polygon_iterated_Sd_selected_arc_carrier_closed_disk_restrict_eq_prefix
          [OF hK_complex hK_fin hK_poly hN_def N\<^sub>I_def])
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
  have hFrN\<^sub>I_sub_N\<^sub>I: "FrN\<^sub>I \<subseteq> N\<^sub>I"
    using hFrN\<^sub>I_HOL frontier_subset_closed[OF hN\<^sub>I_closed] by (by100 simp)
  have hFrN\<^sub>I_sub_N: "FrN\<^sub>I \<subseteq> N"
    using hFrN\<^sub>I_sub_N\<^sub>I hN\<^sub>I_eq_N by (by100 simp)
  have hFrN\<^sub>I_closed: "closed FrN\<^sub>I"
    using hFrN\<^sub>I_HOL frontier_closed by (by100 simp)
  have hFrN\<^sub>I_compact: "compact FrN\<^sub>I"
    by (rule closed_subset_compact[OF hN\<^sub>I_compact hFrN\<^sub>I_closed hFrN\<^sub>I_sub_N\<^sub>I])
  have hFrN\<^sub>I_A2_QS_disj: "FrN\<^sub>I \<inter> (A2 \<union> {Q, S}) = {}"
    using hFrN\<^sub>I_sub_N hN_avoid by (by100 blast)
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
    using hJ\<^sub>N_sub_N hN_avoid by (by100 blast)
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
      thus "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
        by (by100 simp)
    next
      assume "e \<in> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
      then obtain \<tau> where h\<tau>S: "\<tau> \<in> ?S" and heface\<tau>: "geotop_is_face e \<tau>"
        by (by100 blast)
      have h\<tau>1: "geotop_simplex_dim \<tau> 1"
        using h\<tau>S by (by100 simp)
      have he1: "geotop_simplex_dim e 1"
        using hedge unfolding geotop_is_edge_def by (by100 simp)
      obtain k where hk_le: "k \<le> 1" and hek: "geotop_simplex_dim e k"
        using geotop_face_dim_le_prefix[OF h\<tau>1 heface\<tau>] by (by100 blast)
      have hk1: "k = 1"
        by (rule geotop_simplex_dim_unique[OF hek he1])
      have hsame_dim: "geotop_simplex_dim e 1"
        using hek hk1 by (by100 simp)
      have h\<tau>edge: "geotop_is_edge \<tau>"
        using h\<tau>1 unfolding geotop_is_edge_def by (by100 simp)
      have he_eq_\<tau>: "e = \<tau>"
        by (rule geotop_edge_face_of_edge_eq_prefix[OF hedge h\<tau>edge heface\<tau>])
      show "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
        using h\<tau>S he_eq_\<tau> by (by100 simp)
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
  have hBdJ\<^sub>N_poly_compact: "compact (geotop_polyhedron BdJ\<^sub>N)"
    by (rule geotop_complex_polyhedron_compact
        [OF hBdJ\<^sub>N_complex hBdJ\<^sub>N_fin])
  have hBdJ\<^sub>N_poly_closed: "closed (geotop_polyhedron BdJ\<^sub>N)"
    by (rule geotop_complex_polyhedron_closed
        [OF hBdJ\<^sub>N_complex hBdJ\<^sub>N_fin])
  have hBdJ\<^sub>N_poly_sub_J\<^sub>N: "geotop_polyhedron BdJ\<^sub>N \<subseteq> J\<^sub>N"
    unfolding BdJ\<^sub>N_def geotop_polyhedron_def by (by100 blast)
  have hBdJ\<^sub>N_poly_sub_FrN\<^sub>I: "geotop_polyhedron BdJ\<^sub>N \<subseteq> FrN\<^sub>I"
    using hBdJ\<^sub>N_poly_sub_J\<^sub>N hJ\<^sub>N_sub_FrN\<^sub>I by (by100 blast)
  have hBdJ\<^sub>N_edge_sub_J\<^sub>N:
      "\<And>e. e \<in> BdJ\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> e \<subseteq> J\<^sub>N"
    unfolding BdJ\<^sub>N_def by (by100 simp)
  have hBdJ\<^sub>N_edge_sub_FrN\<^sub>I:
      "\<And>e. e \<in> BdJ\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> e \<subseteq> FrN\<^sub>I"
  proof -
    fix e
    assume heBdJ: "e \<in> BdJ\<^sub>N" and hedge: "geotop_is_edge e"
    have heJ: "e \<subseteq> J\<^sub>N"
      by (rule hBdJ\<^sub>N_edge_sub_J\<^sub>N[OF heBdJ hedge])
    show "e \<subseteq> FrN\<^sub>I"
      using heJ hJ\<^sub>N_sub_FrN\<^sub>I by (by100 blast)
  qed
  have hBdJ\<^sub>N_edge_member_incident_count_one:
      "\<And>e. e \<in> BdJ\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
        card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
  proof -
    fix e
    assume heBdJ: "e \<in> BdJ\<^sub>N" and hedge: "geotop_is_edge e"
    have heBdK: "e \<in> BdK\<^sub>N"
      using heBdJ unfolding BdJ\<^sub>N_def by (by100 simp)
    show "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
      by (rule hBdK\<^sub>N_edge_member_incident_count_one[OF heBdK hedge])
  qed
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
  have hJ\<^sub>N_uncovered_openin:
      "openin (top_of_set J\<^sub>N)
        (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N)"
    using hBdJ\<^sub>N_poly_closedin_J\<^sub>N
    unfolding closedin_def by (by100 simp)
  have hJ\<^sub>N_uncovered_closed:
      "closed (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N)"
    using hJ\<^sub>N_uncovered_finite by (rule finite_imp_closed)
  have hJ\<^sub>N_uncovered_closedin:
      "closedin (top_of_set J\<^sub>N)
        (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N)"
  proof -
    have hclosedin_int:
        "closedin (top_of_set J\<^sub>N)
          (J\<^sub>N \<inter> (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N))"
      using hJ\<^sub>N_uncovered_closed by (rule closedin_closed_Int)
    have heq:
        "J\<^sub>N \<inter> (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N) =
          J\<^sub>N - geotop_polyhedron BdJ\<^sub>N"
      by (by100 blast)
    show ?thesis
      using hclosedin_int heq by (by100 simp)
  qed
  have hJ\<^sub>N_uncovered_empty_or_all:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = {}
        \<or> J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    using connected_clopen[THEN iffD1, OF hJ\<^sub>N_connected_HOL]
      hJ\<^sub>N_uncovered_openin hJ\<^sub>N_uncovered_closedin
    by (by100 blast)
  have hJ\<^sub>N_uncovered_all_imp_finite:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow> finite J\<^sub>N"
    using hJ\<^sub>N_uncovered_finite by (by100 simp)
  have hJ\<^sub>N_uncovered_all_imp_singleton:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow> \<exists>x. J\<^sub>N = {x}"
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    have hfin: "finite J\<^sub>N"
      by (rule hJ\<^sub>N_uncovered_all_imp_finite[OF hall])
    have hcases: "J\<^sub>N = {} \<or> (\<exists>x. J\<^sub>N = {x})"
      using connected_finite_iff_sing[OF hJ\<^sub>N_connected_HOL] hfin by (by100 blast)
    show "\<exists>x. J\<^sub>N = {x}"
      using hcases hJ\<^sub>N_nonempty by (by100 blast)
  qed
  have hJ\<^sub>N_uncovered_all_imp_eq_P:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow> J\<^sub>N = {P}"
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    obtain x where hx: "J\<^sub>N = {x}"
      using hJ\<^sub>N_uncovered_all_imp_singleton[OF hall] by (by100 blast)
    have hxP: "x = P"
      using hx hP_J\<^sub>N by (by100 blast)
    show "J\<^sub>N = {P}"
      using hx hxP by (by100 simp)
  qed
  have hJ\<^sub>N_uncovered_all_imp_P_uncovered:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N
        \<Longrightarrow> P \<in> J\<^sub>N - geotop_polyhedron BdJ\<^sub>N"
    using hP_J\<^sub>N by (by100 simp)
  have hJ\<^sub>N_uncovered_all_imp_P_not_BdJ:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N
        \<Longrightarrow> P \<notin> geotop_polyhedron BdJ\<^sub>N"
    using hJ\<^sub>N_uncovered_all_imp_P_uncovered by (by100 blast)
  have hJ\<^sub>N_uncovered_all_imp_P_vertex:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N
        \<Longrightarrow> P \<in> geotop_complex_vertices K\<^sub>N"
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    have hP_unc: "P \<in> J\<^sub>N - geotop_polyhedron BdJ\<^sub>N"
      by (rule hJ\<^sub>N_uncovered_all_imp_P_uncovered[OF hall])
    show "P \<in> geotop_complex_vertices K\<^sub>N"
      by (rule subsetD[OF hJ\<^sub>N_uncovered_sub_vertices hP_unc])
  qed
  have hJ\<^sub>N_uncovered_all_imp_P_carrier_dim0:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N
        \<Longrightarrow> geotop_simplex_dim (geotop_K_carrier K\<^sub>N P) 0"
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    obtain n where hn_le: "n \<le> 1"
      and hdim: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N P) n"
      using hJ\<^sub>N_carrier_dim_le1[OF hP_J\<^sub>N] by (by100 blast)
    have hn_not1: "n \<noteq> 1"
    proof
      assume hn1: "n = 1"
      have hdim1: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N P) 1"
        using hdim hn1 by (by100 simp)
      have hP_BdJ: "P \<in> geotop_polyhedron BdJ\<^sub>N"
        by (rule hJ\<^sub>N_carrier_edge_point_in_BdJ\<^sub>N_poly[OF hP_J\<^sub>N hdim1])
      have hP_not_BdJ: "P \<notin> geotop_polyhedron BdJ\<^sub>N"
        by (rule hJ\<^sub>N_uncovered_all_imp_P_not_BdJ[OF hall])
      show False
        using hP_BdJ hP_not_BdJ by (by100 blast)
    qed
    have hn0: "n = 0"
      using hn_le hn_not1 by (by100 linarith)
    show "geotop_simplex_dim (geotop_K_carrier K\<^sub>N P) 0"
      using hdim hn0 by (by100 simp)
  qed
  have hJ\<^sub>N_uncovered_all_imp_P_incident_edge:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N
        \<Longrightarrow> \<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> P \<in> e"
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    have hdim0: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N P) 0"
      by (rule hJ\<^sub>N_uncovered_all_imp_P_carrier_dim0[OF hall])
    show "\<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> P \<in> e"
      by (rule hJ\<^sub>N_carrier_dim0_incident_edge[OF hP_J\<^sub>N hdim0])
  qed
  have hJ\<^sub>N_uncovered_all_imp_incident_edge_not_one:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow>
        e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> P \<in> e \<Longrightarrow>
        card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} \<noteq> 1"
    for e
  proof
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
      and heK: "e \<in> K\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      and hcard1:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} = 1"
    have heBdK: "e \<in> BdK\<^sub>N"
      by (rule hK\<^sub>N_one_incident_edge_member_BdK\<^sub>N
          [OF heK hedge hcard1])
    have hmeet: "e \<inter> J\<^sub>N \<noteq> {}"
      using hP_e hP_J\<^sub>N by (by100 blast)
    have heBdJ: "e \<in> BdJ\<^sub>N"
      by (rule hBdK\<^sub>N_edge_meets_J\<^sub>N_in_BdJ\<^sub>N[OF heBdK hedge hmeet])
    have hP_BdJ: "P \<in> geotop_polyhedron BdJ\<^sub>N"
      unfolding geotop_polyhedron_def using heBdJ hP_e by (by100 blast)
    have hP_not_BdJ: "P \<notin> geotop_polyhedron BdJ\<^sub>N"
      by (rule hJ\<^sub>N_uncovered_all_imp_P_not_BdJ[OF hall])
    show False
      using hP_BdJ hP_not_BdJ by (by100 blast)
  qed
  have hJ\<^sub>N_uncovered_all_imp_incident_edge_two:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow>
        e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> P \<in> e \<Longrightarrow>
        card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} = 2"
    for e
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
      and heK: "e \<in> K\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
    have he_simplex: "geotop_is_simplex e"
      using hedge unfolding geotop_is_edge_def
      by (rule geotop_simplex_dim_imp_is_simplex)
    obtain q where hq_rel: "q \<in> rel_interior e"
      using geotop_simplex_rel_interior_nonempty[OF he_simplex] by (by100 blast)
    have hge1:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} \<ge> 1"
      by (rule hK\<^sub>N_edge_rel_interior_incident_count_ge1
          [OF heK hedge hq_rel])
    have hle2:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} \<le> 2"
      by (rule hK\<^sub>N_edge_incident_2faces_card_le2[OF heK hedge])
    have hnot1:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} \<noteq> 1"
      by (rule hJ\<^sub>N_uncovered_all_imp_incident_edge_not_one
          [OF hall heK hedge hP_e])
    show ?thesis
      using hge1 hle2 hnot1 by (by100 linarith)
  qed
  have hJ\<^sub>N_uncovered_all_imp_P_two_incident_edge:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow>
        \<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> P \<in> e
          \<and> card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} = 2"
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    obtain e where heK: "e \<in> K\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      using hJ\<^sub>N_uncovered_all_imp_P_incident_edge[OF hall]
      by (by100 blast)
    have htwo:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} = 2"
      by (rule hJ\<^sub>N_uncovered_all_imp_incident_edge_two
          [OF hall heK hedge hP_e])
    show ?thesis
      using heK hedge hP_e htwo by (intro bexI[where x=e] conjI)
  qed
  have hJ\<^sub>N_uncovered_all_imp_P_all_incident_edges_two:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow>
        \<forall>e\<in>K\<^sub>N. geotop_is_edge e \<and> P \<in> e \<longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} = 2"
  proof (intro ballI impI)
    fix e
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
      and heK: "e \<in> K\<^sub>N"
      and hcond: "geotop_is_edge e \<and> P \<in> e"
    have hedge: "geotop_is_edge e"
      using hcond by (by100 simp)
    have hP_e: "P \<in> e"
      using hcond by (by100 simp)
    show "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} = 2"
      by (rule hJ\<^sub>N_uncovered_all_imp_incident_edge_two
          [OF hall heK hedge hP_e])
  qed
  have hP_boundary_K\<^sub>N_one_incident_edge:
      "\<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> P \<in> e
        \<and> card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} = 1"
  proof -
    have hSd_poly_disk:
        "geotop_polyhedron (geotop_iterated_Sd m K) =
          closure_on UNIV geotop_euclidean_topology
            (geotop_polygon_interior J)"
      using hSd_poly hK_poly by (by100 simp)
    have hboundary_cover:
        "J \<subseteq> \<Union>{e\<in>geotop_iterated_Sd m K.
          geotop_is_edge e \<and> e \<subseteq> J}"
      by (rule geotop_polygon_disk_boundary_subset_selected_edges_prefix
          [OF hJ hSd_complex hSd_poly_disk])
    have hP_cover:
        "P \<in> \<Union>{e\<in>geotop_iterated_Sd m K.
          geotop_is_edge e \<and> e \<subseteq> J}"
      using hboundary_cover hP by (by100 blast)
    obtain e where he_sel:
        "e \<in> {e\<in>geotop_iterated_Sd m K. geotop_is_edge e \<and> e \<subseteq> J}"
      and hP_e: "P \<in> e"
      using hP_cover by (by100 blast)
    have heSd: "e \<in> geotop_iterated_Sd m K"
      using he_sel by (by100 simp)
    have hedge: "geotop_is_edge e"
      using he_sel by (by100 simp)
    have heJ: "e \<subseteq> J"
      using he_sel by (by100 simp)
    have heA1: "e \<inter> A1 \<noteq> {}"
      using hP_e hP_in_A1 by (by100 blast)
    have he_sub_N: "e \<subseteq> N"
      unfolding hN_def using heSd heA1 by (by100 blast)
    have heK\<^sub>N: "e \<in> K\<^sub>N"
      unfolding K\<^sub>N_def using heSd he_sub_N by (by100 simp)
    obtain \<sigma> where h\<sigma>Sd: "\<sigma> \<in> geotop_iterated_Sd m K"
      and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
      and heface\<sigma>: "geotop_is_face e \<sigma>"
      using geotop_polygon_disk_boundary_edge_owned_by_2simplex_prefix
        [OF hJ hSd_complex hSd_poly_disk heSd hedge heJ]
      by (elim bexE conjE)
    have hfaces_Sd:
        "{\<rho>\<in>geotop_iterated_Sd m K.
            geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>}"
      by (rule geotop_polygon_disk_boundary_edge_unique_incident_2simplex_prefix
          [OF hJ hSd_complex hSd_poly_disk heSd hedge h\<sigma>Sd h\<sigma>2 heface\<sigma> heJ])
    have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
      by (rule geotop_is_face_imp_subset_prefix[OF heface\<sigma>])
    have hP_\<sigma>: "P \<in> \<sigma>"
      using hP_e he_sub_\<sigma> by (by100 blast)
    have h\<sigma>A1: "\<sigma> \<inter> A1 \<noteq> {}"
      using hP_\<sigma> hP_in_A1 by (by100 blast)
    have h\<sigma>subN: "\<sigma> \<subseteq> N"
      unfolding hN_def using h\<sigma>Sd h\<sigma>A1 by (by100 blast)
    have h\<sigma>K\<^sub>N: "\<sigma> \<in> K\<^sub>N"
      unfolding K\<^sub>N_def using h\<sigma>Sd h\<sigma>subN by (by100 simp)
    let ?F = "{\<rho>\<in>K\<^sub>N. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
    have hF_eq: "?F = {\<sigma>}"
    proof
      show "?F \<subseteq> {\<sigma>}"
      proof
        fix \<rho>
        assume h\<rho>F: "\<rho> \<in> ?F"
        have h\<rho>Sd: "\<rho> \<in> geotop_iterated_Sd m K"
          using h\<rho>F unfolding K\<^sub>N_def by (by100 simp)
        have h\<rho>2: "geotop_simplex_dim \<rho> 2"
          using h\<rho>F by (by100 simp)
        have h\<rho>face: "geotop_is_face e \<rho>"
          using h\<rho>F by (by100 simp)
        have h\<rho>full:
            "\<rho> \<in> {\<rho>\<in>geotop_iterated_Sd m K.
              geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
          using h\<rho>Sd h\<rho>2 h\<rho>face by (by100 simp)
        show "\<rho> \<in> {\<sigma>}"
          using hfaces_Sd h\<rho>full by (by100 simp)
      qed
      show "{\<sigma>} \<subseteq> ?F"
        using h\<sigma>K\<^sub>N h\<sigma>2 heface\<sigma> by (by100 simp)
    qed
    have hcard1: "card ?F = 1"
      using hF_eq by (by100 simp)
    show ?thesis
      using heK\<^sub>N hedge hP_e hcard1 by (intro bexI[where x=e] conjI)
  qed
  have hJ\<^sub>N_uncovered_all_false:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow> False"
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    obtain e where heK: "e \<in> K\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      and hcard1:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} = 1"
      using hP_boundary_K\<^sub>N_one_incident_edge by (by100 blast)
    have hnot1:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} \<noteq> 1"
      by (rule hJ\<^sub>N_uncovered_all_imp_incident_edge_not_one
          [OF hall heK hedge hP_e])
    show False
      using hcard1 hnot1 by (by100 blast)
  qed
  have hJ\<^sub>N_uncovered_empty:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = {}"
    using hJ\<^sub>N_uncovered_empty_or_all hJ\<^sub>N_uncovered_all_false
    by (by100 blast)
  have hJ\<^sub>N_eq_BdJ\<^sub>N_poly:
      "J\<^sub>N = geotop_polyhedron BdJ\<^sub>N"
    using hJ\<^sub>N_uncovered_empty hBdJ\<^sub>N_poly_sub_J\<^sub>N by (by100 blast)
  have hBdJ\<^sub>N_poly_connected_HOL:
      "connected (geotop_polyhedron BdJ\<^sub>N)"
    using hJ\<^sub>N_connected_HOL hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
  have hBdJ\<^sub>N_poly_connected:
      "top1_connected_on (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N))"
    using hBdJ\<^sub>N_poly_connected_HOL top1_connected_on_geotop_iff_connected
    by (by100 blast)
  have hBdJ\<^sub>N_poly_path_connected:
      "top1_path_connected_on (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N))"
    by (rule iffD2[OF Theorem_GT_1_12(2)[OF hBdJ\<^sub>N_complex]
          hBdJ\<^sub>N_poly_connected])
  have hBdJ\<^sub>N_connected: "geotop_complex_connected BdJ\<^sub>N"
    by (rule iffD2[OF Theorem_GT_1_12(1)[OF hBdJ\<^sub>N_complex]
          hBdJ\<^sub>N_poly_path_connected])
  have hBdJ\<^sub>N_poly_nonempty: "geotop_polyhedron BdJ\<^sub>N \<noteq> {}"
    using hP_J\<^sub>N hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 blast)
  have hBdJ\<^sub>N_nonempty: "BdJ\<^sub>N \<noteq> {}"
    using hBdJ\<^sub>N_poly_nonempty unfolding geotop_polyhedron_def by (by100 blast)
  have hP_BdJ\<^sub>N_poly: "P \<in> geotop_polyhedron BdJ\<^sub>N"
    using hP_J\<^sub>N hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
  have hBdJ\<^sub>N_P_incident_edge:
      "\<exists>e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> P \<in> e"
  proof -
    obtain e where heK: "e \<in> K\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      and hcard1:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} = 1"
      using hP_boundary_K\<^sub>N_one_incident_edge by (by100 blast)
    have heBdK: "e \<in> BdK\<^sub>N"
      by (rule hK\<^sub>N_one_incident_edge_member_BdK\<^sub>N
          [OF heK hedge hcard1])
    have hmeet: "e \<inter> J\<^sub>N \<noteq> {}"
      using hP_e hP_J\<^sub>N by (by100 blast)
    have heBdJ: "e \<in> BdJ\<^sub>N"
      by (rule hBdK\<^sub>N_edge_meets_J\<^sub>N_in_BdJ\<^sub>N[OF heBdK hedge hmeet])
    show ?thesis
      using heBdJ hedge hP_e by (intro bexI[where x=e] conjI)
  qed
  have hBdJ\<^sub>N_P_boundary_edge:
      "\<exists>e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> P \<in> e \<and> e \<subseteq> J"
    (**
      Book B1 start: the frontier component through \<open>P\<close> contains the
      actual fine-subdivision boundary edge of the polygonal disk through
      \<open>P\<close>, not merely an abstract incident edge of the extracted graph. **)
  proof -
    have hSd_poly_disk:
        "geotop_polyhedron (geotop_iterated_Sd m K) =
          closure_on UNIV geotop_euclidean_topology
            (geotop_polygon_interior J)"
      using hSd_poly hK_poly by (by100 simp)
    have hboundary_cover:
        "J \<subseteq> \<Union>{e\<in>geotop_iterated_Sd m K.
          geotop_is_edge e \<and> e \<subseteq> J}"
      by (rule geotop_polygon_disk_boundary_subset_selected_edges_prefix
          [OF hJ hSd_complex hSd_poly_disk])
    have hP_cover:
        "P \<in> \<Union>{e\<in>geotop_iterated_Sd m K.
          geotop_is_edge e \<and> e \<subseteq> J}"
      using hboundary_cover hP by (by100 blast)
    obtain e where he_sel:
        "e \<in> {e\<in>geotop_iterated_Sd m K. geotop_is_edge e \<and> e \<subseteq> J}"
      and hP_e: "P \<in> e"
      using hP_cover by (by100 blast)
    have heSd: "e \<in> geotop_iterated_Sd m K"
      using he_sel by (by100 simp)
    have hedge: "geotop_is_edge e"
      using he_sel by (by100 simp)
    have heJ: "e \<subseteq> J"
      using he_sel by (by100 simp)
    have heA1: "e \<inter> A1 \<noteq> {}"
      using hP_e hP_in_A1 by (by100 blast)
    have he_sub_N: "e \<subseteq> N"
      unfolding hN_def using heSd heA1 by (by100 blast)
    have heK\<^sub>N: "e \<in> K\<^sub>N"
      unfolding K\<^sub>N_def using heSd he_sub_N by (by100 simp)
    obtain \<sigma> where h\<sigma>Sd: "\<sigma> \<in> geotop_iterated_Sd m K"
      and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
      and heface\<sigma>: "geotop_is_face e \<sigma>"
      using geotop_polygon_disk_boundary_edge_owned_by_2simplex_prefix
        [OF hJ hSd_complex hSd_poly_disk heSd hedge heJ]
      by (elim bexE conjE)
    have hfaces_Sd:
        "{\<rho>\<in>geotop_iterated_Sd m K.
            geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>}"
      by (rule geotop_polygon_disk_boundary_edge_unique_incident_2simplex_prefix
          [OF hJ hSd_complex hSd_poly_disk heSd hedge h\<sigma>Sd h\<sigma>2 heface\<sigma> heJ])
    have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
      by (rule geotop_is_face_imp_subset_prefix[OF heface\<sigma>])
    have hP_\<sigma>: "P \<in> \<sigma>"
      using hP_e he_sub_\<sigma> by (by100 blast)
    have h\<sigma>A1: "\<sigma> \<inter> A1 \<noteq> {}"
      using hP_\<sigma> hP_in_A1 by (by100 blast)
    have h\<sigma>subN: "\<sigma> \<subseteq> N"
      unfolding hN_def using h\<sigma>Sd h\<sigma>A1 by (by100 blast)
    have h\<sigma>K\<^sub>N: "\<sigma> \<in> K\<^sub>N"
      unfolding K\<^sub>N_def using h\<sigma>Sd h\<sigma>subN by (by100 simp)
    let ?F = "{\<rho>\<in>K\<^sub>N. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
    have hF_eq: "?F = {\<sigma>}"
    proof
      show "?F \<subseteq> {\<sigma>}"
      proof
        fix \<rho>
        assume h\<rho>F: "\<rho> \<in> ?F"
        have h\<rho>Sd: "\<rho> \<in> geotop_iterated_Sd m K"
          using h\<rho>F unfolding K\<^sub>N_def by (by100 simp)
        have h\<rho>2: "geotop_simplex_dim \<rho> 2"
          using h\<rho>F by (by100 simp)
        have h\<rho>face: "geotop_is_face e \<rho>"
          using h\<rho>F by (by100 simp)
        have h\<rho>full:
            "\<rho> \<in> {\<rho>\<in>geotop_iterated_Sd m K.
              geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
          using h\<rho>Sd h\<rho>2 h\<rho>face by (by100 simp)
        show "\<rho> \<in> {\<sigma>}"
          using hfaces_Sd h\<rho>full by (by100 simp)
      qed
      show "{\<sigma>} \<subseteq> ?F"
        using h\<sigma>K\<^sub>N h\<sigma>2 heface\<sigma> by (by100 simp)
    qed
    have hcard1: "card ?F = 1"
      using hF_eq by (by100 simp)
    have heBdK: "e \<in> BdK\<^sub>N"
      by (rule hK\<^sub>N_one_incident_edge_member_BdK\<^sub>N
          [OF heK\<^sub>N hedge hcard1])
    have hmeet: "e \<inter> J\<^sub>N \<noteq> {}"
      using hP_e hP_J\<^sub>N by (by100 blast)
    have heBdJ: "e \<in> BdJ\<^sub>N"
      by (rule hBdK\<^sub>N_edge_meets_J\<^sub>N_in_BdJ\<^sub>N[OF heBdK hedge hmeet])
    show ?thesis
      using heBdJ hedge hP_e heJ by (intro bexI[where x=e] conjI)
  qed
  have hBdJ\<^sub>N_poly_not_singleton:
      "\<And>w. geotop_polyhedron BdJ\<^sub>N \<noteq> {w}"
  proof
    fix w
    assume hpoly_single: "geotop_polyhedron BdJ\<^sub>N = {w}"
    obtain e where heBdJ: "e \<in> BdJ\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      using hBdJ\<^sub>N_P_incident_edge by (by100 blast)
    have he_sub_poly: "e \<subseteq> geotop_polyhedron BdJ\<^sub>N"
      unfolding geotop_polyhedron_def using heBdJ by (by100 blast)
    have hP_w: "P = w"
      using hP_e he_sub_poly hpoly_single by (by100 blast)
    have he_sub_singleP: "e \<subseteq> {P}"
      using he_sub_poly hpoly_single hP_w by (by100 simp)
    have he_eq_singleP: "e = {P}"
      using hP_e he_sub_singleP by (by100 blast)
    have "geotop_is_edge {P}"
      using hedge he_eq_singleP by (by100 simp)
    thus False
      using geotop_singleton_not_edge_prefix by (by100 blast)
  qed
  have hBdJ\<^sub>N_vertex_incident_edge:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        \<exists>e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e"
  proof (rule ccontr)
    fix w
    assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
      and hno: "\<not> (\<exists>e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e)"
    have hw_vertex: "w \<in> geotop_complex_vertices BdJ\<^sub>N"
      using geotop_complex_vertices_eq_0_simplexes[OF hBdJ\<^sub>N_complex] hwBdJ
      by (by100 blast)
    have hsingle_top:
        "{w} \<in>
          subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron BdJ\<^sub>N)"
      by (rule geotop_complex_no_incident_edge_vertex_open_singleton_prefix
          [OF hBdJ\<^sub>N_complex hw_vertex hno])
    obtain U where hsingle_eq:
        "{w} = geotop_polyhedron BdJ\<^sub>N \<inter> U"
      and hU_top: "U \<in> geotop_euclidean_topology"
      using hsingle_top unfolding subspace_topology_def by (by100 blast)
    have hU_open: "open U"
      using hU_top unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    have hsingle_openin:
        "openin (top_of_set (geotop_polyhedron BdJ\<^sub>N)) {w}"
      unfolding openin_open
      using hU_open hsingle_eq by (by100 blast)
    have hw_poly: "w \<in> geotop_polyhedron BdJ\<^sub>N"
      unfolding geotop_polyhedron_def using hwBdJ by (by100 blast)
    have hsingle_closedin:
        "closedin (top_of_set (geotop_polyhedron BdJ\<^sub>N)) {w}"
    proof -
      have hclosed_single: "closed {w}"
        by (by100 simp)
      have hsingle_eq_poly:
          "{w} = geotop_polyhedron BdJ\<^sub>N \<inter> {w}"
        using hw_poly by (by100 blast)
      show ?thesis
        unfolding closedin_closed
        using hclosed_single hsingle_eq_poly by (by100 blast)
    qed
    have hsingle_cases:
        "{w} = {} \<or> {w} = geotop_polyhedron BdJ\<^sub>N"
      using connected_clopen[THEN iffD1, OF hBdJ\<^sub>N_poly_connected_HOL]
        hsingle_openin hsingle_closedin by (by100 blast)
    have hpoly_single: "geotop_polyhedron BdJ\<^sub>N = {w}"
      using hsingle_cases by (by100 blast)
    show False
      using hBdJ\<^sub>N_poly_not_singleton[of w] hpoly_single by (by100 blast)
  qed
  have hBdJ\<^sub>N_vertex_incident_edge_card_ge1:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 1"
  proof -
    fix w
    assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
    obtain e where heBdJ: "e \<in> BdJ\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hw_e: "w \<in> e"
      using hBdJ\<^sub>N_vertex_incident_edge[OF hwBdJ] by (by100 blast)
    let ?E = "{e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e}"
    have hE_fin: "finite ?E"
      by (rule finite_subset[OF _ hBdJ\<^sub>N_fin]) (by100 blast)
    have heE: "e \<in> ?E"
      using heBdJ hedge hw_e by (by100 simp)
    have hE_ne: "?E \<noteq> {}"
      using heE by (by100 blast)
    have hcard_pos: "0 < card ?E"
    proof -
      have hiff: "(0 < card ?E) = (?E \<noteq> {} \<and> finite ?E)"
        by (rule card_gt_0_iff)
      show ?thesis
        using hiff hE_ne hE_fin by (by100 blast)
    qed
    show "card ?E \<ge> 1"
      using hcard_pos by (by100 linarith)
  qed
  have hBdJ\<^sub>N_vertex_degree_one_or_two_from_card_le2:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        \<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 1
          \<or> card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
  proof (intro allI impI)
    fix w
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
    have hge1:
      "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 1"
      by (rule hBdJ\<^sub>N_vertex_incident_edge_card_ge1[OF hwBdJ])
    have hle:
      "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
      by (rule hle2[OF hwBdJ])
    show "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 1
        \<or> card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      using hge1 hle by (by100 linarith)
  qed
  have hBdJ\<^sub>N_vertex_degree_two_from_card_le2_no_endpoint:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
      (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
    \<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
      card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hnoend:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
    have hdegree12:
        "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 1
          \<or> card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule hBdJ\<^sub>N_vertex_degree_one_or_two_from_card_le2[OF hle2])
    show "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule geotop_degree_one_or_two_no_endpoint_degree_two_prefix
          [OF hBdJ\<^sub>N_linear_graph hdegree12 hnoend])
  qed
  have hBdJ\<^sub>N_vertex_no_endpoint_from_card_ge2:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2) \<Longrightarrow>
        \<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
  proof (intro allI impI)
    fix w
    assume hge2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
    assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
    show "\<not> geotop_graph_endpoint BdJ\<^sub>N w"
    proof
      assume hend: "geotop_graph_endpoint BdJ\<^sub>N w"
      have hcard1:
          "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 1"
        using geotop_graph_endpoint_singleton_and_card_one_prefix
          [OF hBdJ\<^sub>N_linear_graph hend]
        by (by100 blast)
      have hcard_ge2:
          "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
        by (rule hge2[OF hwBdJ])
      show False
        using hcard1 hcard_ge2 by (by100 linarith)
    qed
  qed
  have hBdJ\<^sub>N_vertex_card_ge2_from_no_endpoint:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
        \<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
  proof (intro allI impI)
    fix w
    assume hnoend:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
    assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
    have hge1:
      "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 1"
      by (rule hBdJ\<^sub>N_vertex_incident_edge_card_ge1[OF hwBdJ])
    show "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
    proof (rule ccontr)
      assume hnot_ge2:
        "\<not> 2 \<le> card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e}"
      have hcard1:
          "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 1"
        using hge1 hnot_ge2 by (by100 linarith)
      have hend: "geotop_graph_endpoint BdJ\<^sub>N w"
        by (rule geotop_degree_one_vertex_graph_endpoint_prefix
            [OF hBdJ\<^sub>N_linear_graph hwBdJ hcard1])
      have hnot: "\<not> geotop_graph_endpoint BdJ\<^sub>N w"
        using hnoend hwBdJ by (by100 blast)
      show False
        using hend hnot by (by100 blast)
    qed
  qed
  have hBdJ\<^sub>N_vertex_degree_two_from_card_bounds:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
      (\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2) \<Longrightarrow>
        \<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
  proof (intro allI impI)
    fix w
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hge2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
    assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
    have hle:
      "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
      by (rule hle2[OF hwBdJ])
    have hge:
      "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
      by (rule hge2[OF hwBdJ])
    show "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      using hle hge by (by100 linarith)
  qed
  have hBdJ\<^sub>N_two_distinct_vertices:
      "\<exists>u v. {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v"
  proof -
    obtain e where heBdJ: "e \<in> BdJ\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      using hBdJ\<^sub>N_P_incident_edge by (by100 blast)
    have he_dim: "geotop_simplex_dim e 1"
      using hedge unfolding geotop_is_edge_def by (by100 simp)
    obtain V m where hV_fin: "finite V"
      and hV_card: "card V = 1 + 1"
      and h1_le_m: "1 \<le> m"
      and hgp_V: "geotop_general_position V m"
      and he_eq: "e = geotop_convex_hull V"
      using he_dim unfolding geotop_simplex_dim_def by (by100 blast)
    have heV: "geotop_simplex_vertices e V"
      unfolding geotop_simplex_vertices_def
      using hV_fin hV_card h1_le_m hgp_V he_eq by (by100 blast)
    have hV_card2: "card V = 2"
      using hV_card by (by100 simp)
    have hV_pair_ex:
        "\<exists>u v. V = {u, v} \<and> u \<noteq> v"
      by (rule iffD1[OF card_2_iff hV_card2])
    obtain u v where hV_eq: "V = {u, v}"
      and huv: "u \<noteq> v"
      using hV_pair_ex by (elim exE conjE)
    have huv_BdJ:
        "{u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N"
      by (fact geotop_subdivide_edge_vertices_in_K
          [where K=BdJ\<^sub>N and e=e and V=V and v\<^sub>0=u and v\<^sub>1=v,
           OF hBdJ\<^sub>N_complex heBdJ heV hV_eq])
    show ?thesis
      using huv_BdJ huv by (by100 blast)
  qed
  have hBdJ\<^sub>N_cycle_split_from_degree_two:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2) \<Longrightarrow>
        \<exists>u v C\<^sub>1 C\<^sub>2.
          {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
          \<and> geotop_is_broken_line C\<^sub>1
          \<and> geotop_is_broken_line C\<^sub>2
          \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
          \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
          \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
              geotop_arc_interior C\<^sub>2 {u, v} = {}"
  proof -
    assume hdegree:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
    obtain u v where huBdJ: "{u} \<in> BdJ\<^sub>N"
      and hvBdJ: "{v} \<in> BdJ\<^sub>N"
      and huv: "u \<noteq> v"
      using hBdJ\<^sub>N_two_distinct_vertices by (by100 blast)
    obtain C\<^sub>1 C\<^sub>2 where hsplit:
        "geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
        \<and> geotop_is_broken_line C\<^sub>1
        \<and> geotop_is_broken_line C\<^sub>2
        \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
        \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
        \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
            geotop_arc_interior C\<^sub>2 {u, v} = {}"
      using geotop_finite_connected_degree_two_linear_graph_two_vertex_boundary_split_prefix
        [OF hBdJ\<^sub>N_linear_graph hBdJ\<^sub>N_fin hBdJ\<^sub>N_connected
          hdegree huBdJ hvBdJ huv]
      by (by100 blast)
    show ?thesis
      using huBdJ hvBdJ huv hsplit by (by100 blast)
  qed
  have hBdJ\<^sub>N_polygon_from_degree_two:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2) \<Longrightarrow>
        geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
  proof -
    assume hdegree:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
    obtain u v C\<^sub>1 C\<^sub>2 where huBdJ: "{u} \<in> BdJ\<^sub>N"
      and hvBdJ: "{v} \<in> BdJ\<^sub>N"
      and huv: "u \<noteq> v"
      and hpoly_eq: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2"
      and hC\<^sub>1_bl: "geotop_is_broken_line C\<^sub>1"
      and hC\<^sub>2_bl: "geotop_is_broken_line C\<^sub>2"
      and hC\<^sub>1_end: "geotop_arc_endpoints C\<^sub>1 {u, v}"
      and hC\<^sub>2_end: "geotop_arc_endpoints C\<^sub>2 {u, v}"
      and hdisj: "geotop_arc_interior C\<^sub>1 {u, v} \<inter>
          geotop_arc_interior C\<^sub>2 {u, v} = {}"
      using hBdJ\<^sub>N_cycle_split_from_degree_two[OF hdegree]
      by (by100 blast)
    have hpolygon_C: "geotop_is_polygon (C\<^sub>1 \<union> C\<^sub>2)"
      by (rule pair_of_arcs_is_polygon
          [OF hC\<^sub>1_bl hC\<^sub>2_bl hC\<^sub>1_end hC\<^sub>2_end hdisj])
    show ?thesis
      using hpolygon_C hpoly_eq by (by100 simp)
  qed
  have hBdJ\<^sub>N_polygon_from_card_bounds:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
      (\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2) \<Longrightarrow>
        geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hge2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
    have hdegree:
        "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule hBdJ\<^sub>N_vertex_degree_two_from_card_bounds[OF hle2 hge2])
    show ?thesis
      by (rule hBdJ\<^sub>N_polygon_from_degree_two[OF hdegree])
  qed
  have hBdJ\<^sub>N_polygon_from_card_le2_no_endpoint:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
      (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
        geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hnoend:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
    have hdegree:
        "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule hBdJ\<^sub>N_vertex_degree_two_from_card_le2_no_endpoint
          [OF hle2 hnoend])
    show ?thesis
      by (rule hBdJ\<^sub>N_polygon_from_degree_two[OF hdegree])
  qed
  have hBdJ\<^sub>N_polygon_from_simple_closed_curve:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
        (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
  proof -
    let ?C = "geotop_polyhedron BdJ\<^sub>N"
    let ?TC = "subspace_topology UNIV geotop_euclidean_topology ?C"
    let ?S = "(geotop_std_sphere::(real^2) set)"
    let ?TS = "subspace_topology UNIV geotop_euclidean_topology ?S"
    assume hSCC:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology ?C"
    obtain f where hf_cont_UNIV:
        "top1_continuous_map_on top1_S1 top1_S1_topology
          UNIV geotop_euclidean_topology f"
      and hfinj: "inj_on f top1_S1"
      and hf_img: "f ` top1_S1 = ?C"
      using hSCC unfolding top1_simple_closed_curve_on_def
      by (by100 blast)
    have hf_cont_C:
        "top1_continuous_map_on top1_S1 top1_S1_topology ?C ?TC f"
    proof -
      have hf_img_sub: "f ` top1_S1 \<subseteq> ?C"
        using hf_img by (by100 simp)
      show ?thesis
        by (rule top1_continuous_map_on_codomain_shrink
            [OF hf_cont_UNIV hf_img_sub subset_UNIV])
    qed
    have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
      using S1_compact by (rule compact_is_topology)
    have hUNIV_top:
        "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
      unfolding geotop_euclidean_topology_eq_open_sets
      using top1_open_sets_is_topology_on_UNIV by (by100 simp)
    have hC_top: "is_topology_on ?C ?TC"
      by (rule subspace_topology_is_topology_on[OF hUNIV_top subset_UNIV])
    have hC_haus: "is_hausdorff_on ?C ?TC"
      by (rule hausdorff_subspace
          [OF geotop_euclidean_topology_UNIV_hausdorff subset_UNIV])
    have hf_bij: "bij_betw f top1_S1 ?C"
      using hfinj hf_img unfolding bij_betw_def by (by100 blast)
    have hS1_C: "top1_homeomorphism_on top1_S1 top1_S1_topology ?C ?TC f"
      by (rule Theorem_26_6
          [OF hS1_top hC_top S1_compact hC_haus hf_cont_C hf_bij])
    have hC_S1: "top1_homeomorphism_on ?C ?TC top1_S1 top1_S1_topology
        (inv_into top1_S1 f)"
      by (rule top1_homeomorphism_on_sym[OF hS1_C])
    have hS1_std: "top1_homeomorphism_on top1_S1 top1_S1_topology ?S ?TS
        (inv_into ?S R2_to_pair)"
      by (rule top1_homeomorphism_on_sym
          [OF R2_pair_top1_homeomorphism_std_sphere_prefix])
    have hC_std: "top1_homeomorphism_on ?C ?TC ?S ?TS
        (inv_into ?S R2_to_pair \<circ> inv_into top1_S1 f)"
      by (rule top1_homeomorphism_on_comp[OF hC_S1 hS1_std])
    have hC_sphere: "geotop_is_n_sphere ?C ?TC 1"
      unfolding geotop_is_n_sphere_def
      using hC_top hC_std by (by100 blast)
    show "geotop_is_polygon ?C"
      unfolding geotop_is_polygon_def
      using hBdJ\<^sub>N_complex hC_sphere by (by100 blast)
  qed
  have hBdJ\<^sub>N_cycle_split_from_polygon:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>u v C\<^sub>1 C\<^sub>2.
          {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
          \<and> geotop_is_broken_line C\<^sub>1
          \<and> geotop_is_broken_line C\<^sub>2
          \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
          \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
          \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
              geotop_arc_interior C\<^sub>2 {u, v} = {}"
  proof -
    assume hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    obtain u v where huBdJ: "{u} \<in> BdJ\<^sub>N"
      and hvBdJ: "{v} \<in> BdJ\<^sub>N"
      and huv: "u \<noteq> v"
      using hBdJ\<^sub>N_two_distinct_vertices by (by100 blast)
    obtain C\<^sub>1 C\<^sub>2 where hsplit:
        "geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
        \<and> geotop_is_broken_line C\<^sub>1
        \<and> geotop_is_broken_line C\<^sub>2
        \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
        \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
        \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
            geotop_arc_interior C\<^sub>2 {u, v} = {}"
      using geotop_polygon_finite_linear_graph_two_vertex_boundary_split_prefix
        [OF hBdJ\<^sub>N_linear_graph hBdJ\<^sub>N_fin hBdJ\<^sub>N_connected
          hpolygon huBdJ hvBdJ huv]
      by (by100 blast)
    show ?thesis
      using huBdJ hvBdJ huv hsplit by (by100 blast)
  qed
  have hBdJ\<^sub>N_cycle_split_from_card_bounds:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
      (\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2) \<Longrightarrow>
        \<exists>u v C\<^sub>1 C\<^sub>2.
          {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
          \<and> geotop_is_broken_line C\<^sub>1
          \<and> geotop_is_broken_line C\<^sub>2
          \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
          \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
          \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
              geotop_arc_interior C\<^sub>2 {u, v} = {}"
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hge2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_card_bounds[OF hle2 hge2])
    show ?thesis
      by (rule hBdJ\<^sub>N_cycle_split_from_polygon[OF hpolygon])
  qed
  have hBdJ\<^sub>N_cycle_split_from_card_le2_no_endpoint:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
      (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
        \<exists>u v C\<^sub>1 C\<^sub>2.
          {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
          \<and> geotop_is_broken_line C\<^sub>1
          \<and> geotop_is_broken_line C\<^sub>2
          \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
          \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
          \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
              geotop_arc_interior C\<^sub>2 {u, v} = {}"
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hnoend:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_card_le2_no_endpoint[OF hle2 hnoend])
    show ?thesis
      by (rule hBdJ\<^sub>N_cycle_split_from_polygon[OF hpolygon])
  qed
  have hBdJ\<^sub>N_cycle_split_from_simple_closed_curve:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
        (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>u v C\<^sub>1 C\<^sub>2.
          {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
          \<and> geotop_is_broken_line C\<^sub>1
          \<and> geotop_is_broken_line C\<^sub>2
          \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
          \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
          \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
              geotop_arc_interior C\<^sub>2 {u, v} = {}"
  proof -
    assume hSCC:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
        (geotop_polyhedron BdJ\<^sub>N)"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_simple_closed_curve[OF hSCC])
    show ?thesis
      by (rule hBdJ\<^sub>N_cycle_split_from_polygon[OF hpolygon])
  qed
  have hBdJ\<^sub>N_poly_A2_QS_disj:
      "geotop_polyhedron BdJ\<^sub>N \<inter> (A2 \<union> {Q, S}) = {}"
    using hBdJ\<^sub>N_poly_sub_J\<^sub>N hJ\<^sub>N_A2_QS_disj by (by100 blast)
  have hball_Q_FrN\<^sub>I_disj: "ball Q r \<inter> FrN\<^sub>I = {}"
    using hball_Q_N hFrN\<^sub>I_sub_N by (by100 blast)
  have hball_S_FrN\<^sub>I_disj: "ball S r \<inter> FrN\<^sub>I = {}"
    using hball_S_N hFrN\<^sub>I_sub_N by (by100 blast)
  have hball_Q_J\<^sub>N_disj: "ball Q r \<inter> J\<^sub>N = {}"
    using hball_Q_N hJ\<^sub>N_sub_N by (by100 blast)
  have hball_S_J\<^sub>N_disj: "ball S r \<inter> J\<^sub>N = {}"
    using hball_S_N hJ\<^sub>N_sub_N by (by100 blast)
  have hball_Q_BdJ\<^sub>N_poly_disj:
      "ball Q r \<inter> geotop_polyhedron BdJ\<^sub>N = {}"
    using hball_Q_J\<^sub>N_disj hBdJ\<^sub>N_poly_sub_J\<^sub>N by (by100 blast)
  have hball_S_BdJ\<^sub>N_poly_disj:
      "ball S r \<inter> geotop_polyhedron BdJ\<^sub>N = {}"
    using hball_S_J\<^sub>N_disj hBdJ\<^sub>N_poly_sub_J\<^sub>N by (by100 blast)
  have hQ_not_BdJ\<^sub>N_poly: "Q \<notin> geotop_polyhedron BdJ\<^sub>N"
    using hBdJ\<^sub>N_poly_A2_QS_disj by (by100 blast)
  have hS_not_BdJ\<^sub>N_poly: "S \<notin> geotop_polyhedron BdJ\<^sub>N"
    using hBdJ\<^sub>N_poly_A2_QS_disj by (by100 blast)
  have hR_not_BdJ\<^sub>N_poly: "R \<notin> geotop_polyhedron BdJ\<^sub>N"
    using hR_in_A2 hBdJ\<^sub>N_poly_A2_QS_disj by (by100 blast)
  have hBdK\<^sub>N_poly_A2_QS_disj:
      "geotop_polyhedron BdK\<^sub>N \<inter> (A2 \<union> {Q, S}) = {}"
    using hBdK\<^sub>N_poly_sub_N hN_avoid by (by100 blast)
  have hQ_not_BdK\<^sub>N_poly: "Q \<notin> geotop_polyhedron BdK\<^sub>N"
    using hBdK\<^sub>N_poly_A2_QS_disj by (by100 blast)
  have hS_not_BdK\<^sub>N_poly: "S \<notin> geotop_polyhedron BdK\<^sub>N"
    using hBdK\<^sub>N_poly_A2_QS_disj by (by100 blast)
  have hR_not_BdK\<^sub>N_poly: "R \<notin> geotop_polyhedron BdK\<^sub>N"
    using hR_in_A2 hBdK\<^sub>N_poly_A2_QS_disj by (by100 blast)
  have hQ1_not_N: "Q1 \<notin> N"
    using hQ1_Ncut by (by100 blast)
  have hS1_not_N: "S1 \<notin> N"
    using hS1_Ncut by (by100 blast)
  have hQ1_not_A2: "Q1 \<notin> A2"
    using hQ1_Ncut by (by100 blast)
  have hS1_not_A2: "S1 \<notin> A2"
    using hS1_Ncut by (by100 blast)
  have hQ1_I: "Q1 \<in> geotop_polygon_interior J"
    using hQ1_Ncut by (by100 blast)
  have hS1_I: "S1 \<in> geotop_polygon_interior J"
    using hS1_Ncut by (by100 blast)
  have hQ1_not_FrN\<^sub>I: "Q1 \<notin> FrN\<^sub>I"
    using hQ1_not_N hFrN\<^sub>I_sub_N by (by100 blast)
  have hS1_not_FrN\<^sub>I: "S1 \<notin> FrN\<^sub>I"
    using hS1_not_N hFrN\<^sub>I_sub_N by (by100 blast)
  have hQ1_not_J\<^sub>N: "Q1 \<notin> J\<^sub>N"
    using hQ1_not_N hJ\<^sub>N_sub_N by (by100 blast)
  have hS1_not_J\<^sub>N: "S1 \<notin> J\<^sub>N"
    using hS1_not_N hJ\<^sub>N_sub_N by (by100 blast)
  have hQ1_not_A1: "Q1 \<notin> A1"
    using hQ1_not_N hA1_N by (by100 blast)
  have hS1_not_A1: "S1 \<notin> A1"
    using hS1_not_N hA1_N by (by100 blast)
  have hQ1_not_K\<^sub>N_poly: "Q1 \<notin> geotop_polyhedron K\<^sub>N"
    using hQ1_not_N hK\<^sub>N_poly_N\<^sub>I hN\<^sub>I_eq_N by (by100 simp)
  have hS1_not_K\<^sub>N_poly: "S1 \<notin> geotop_polyhedron K\<^sub>N"
    using hS1_not_N hK\<^sub>N_poly_N\<^sub>I hN\<^sub>I_eq_N by (by100 simp)
  have hQ1_not_BdK\<^sub>N_poly: "Q1 \<notin> geotop_polyhedron BdK\<^sub>N"
    using hQ1_not_N hBdK\<^sub>N_poly_sub_N by (by100 blast)
  have hS1_not_BdK\<^sub>N_poly: "S1 \<notin> geotop_polyhedron BdK\<^sub>N"
    using hS1_not_N hBdK\<^sub>N_poly_sub_N by (by100 blast)
  have hNcut_N_disj: "?Ncut \<inter> N = {}"
    by (by100 blast)
  have hNcut_FrN\<^sub>I_disj: "?Ncut \<inter> FrN\<^sub>I = {}"
    using hFrN\<^sub>I_sub_N by (by100 blast)
  have hNcut_J\<^sub>N_disj: "?Ncut \<inter> J\<^sub>N = {}"
    using hJ\<^sub>N_sub_N by (by100 blast)
  have hNcut_BdJ\<^sub>N_poly_disj:
      "?Ncut \<inter> geotop_polyhedron BdJ\<^sub>N = {}"
    using hBdJ\<^sub>N_poly_sub_J\<^sub>N hNcut_J\<^sub>N_disj by (by100 blast)
  have hQ1_not_BdJ\<^sub>N_poly:
      "Q1 \<notin> geotop_polyhedron BdJ\<^sub>N"
    using hQ1_Ncut hNcut_BdJ\<^sub>N_poly_disj by (by100 blast)
  have hS1_not_BdJ\<^sub>N_poly:
      "S1 \<notin> geotop_polyhedron BdJ\<^sub>N"
    using hS1_Ncut hNcut_BdJ\<^sub>N_poly_disj by (by100 blast)
  have hQ_ne_S: "Q \<noteq> S"
  proof
    assume hQS: "Q = S"
    have "card {P, Q, R, S} \<le> 3"
      by (simp add: hQS card_insert_if)
    thus False
      using hcard by (by100 simp)
  qed
  have hQ_ne_PR: "Q \<noteq> P \<and> Q \<noteq> R"
  proof
    show "Q \<noteq> P"
    proof
      assume hQP: "Q = P"
      have "card {P, Q, R, S} \<le> 3"
        by (simp add: hQP card_insert_if)
      thus False
        using hcard by (by100 simp)
    qed
    show "Q \<noteq> R"
    proof
      assume hQR: "Q = R"
      have "card {P, Q, R, S} \<le> 3"
        by (simp add: hQR card_insert_if)
      thus False
        using hcard by (by100 simp)
    qed
  qed
  have hS_ne_PR: "S \<noteq> P \<and> S \<noteq> R"
  proof
    show "S \<noteq> P"
    proof
      assume hSP: "S = P"
      have "card {P, Q, R, S} \<le> 3"
        by (simp add: hSP card_insert_if)
      thus False
        using hcard by (by100 simp)
    qed
    show "S \<noteq> R"
    proof
      assume hSR: "S = R"
      have "card {P, Q, R, S} \<le> 3"
        by (simp add: hSR card_insert_if)
      thus False
        using hcard by (by100 simp)
    qed
  qed
  have hD44_QS_broken_boundary_arc_split:
      "\<exists>F\<^sub>1 F\<^sub>2.
        J = F\<^sub>1 \<union> F\<^sub>2
        \<and> geotop_is_broken_line F\<^sub>1
        \<and> geotop_is_broken_line F\<^sub>2
        \<and> geotop_arc_endpoints F\<^sub>1 {Q, S}
        \<and> geotop_arc_endpoints F\<^sub>2 {Q, S}
        \<and> geotop_arc_interior F\<^sub>1 {Q, S} \<inter>
            geotop_arc_interior F\<^sub>2 {Q, S} = {}
        \<and> P \<in> geotop_arc_interior F\<^sub>1 {Q, S}"
  proof -
    obtain L where hL_linear: "geotop_is_linear_graph L"
      and hL_fin: "finite L"
      and hL_conn: "geotop_complex_connected L"
      and hL_poly: "geotop_polyhedron L = J"
      and hQL: "{Q} \<in> L"
      and hSL: "{S} \<in> L"
      using geotop_polygon_finite_connected_linear_graph_with_two_vertices_prefix
        [OF hJ hQ hS]
      by (by100 blast)
    have hL_polygon: "geotop_is_polygon (geotop_polyhedron L)"
      using hJ hL_poly by (by100 simp)
    have hP_not_QS: "P \<notin> {Q, S}"
      using hQ_ne_PR hS_ne_PR by (by100 blast)
    have hP_poly_L: "P \<in> geotop_polyhedron L"
      using hP hL_poly by (by100 simp)
    obtain F\<^sub>1 F\<^sub>2 where hsplit:
        "geotop_polyhedron L = F\<^sub>1 \<union> F\<^sub>2
        \<and> geotop_is_broken_line F\<^sub>1
        \<and> geotop_is_broken_line F\<^sub>2
        \<and> geotop_arc_endpoints F\<^sub>1 {Q, S}
        \<and> geotop_arc_endpoints F\<^sub>2 {Q, S}
        \<and> geotop_arc_interior F\<^sub>1 {Q, S} \<inter>
            geotop_arc_interior F\<^sub>2 {Q, S} = {}
        \<and> P \<in> geotop_arc_interior F\<^sub>1 {Q, S}"
      using geotop_polygon_finite_linear_graph_two_vertex_boundary_split_through_point_prefix
        [OF hL_linear hL_fin hL_conn hL_polygon hQL hSL hQ_ne_S hP_poly_L hP_not_QS]
      by (by100 blast)
    show ?thesis
      using hsplit hL_poly by (by100 blast)
  qed
  obtain F\<^sub>1 F\<^sub>2 where hD44_F_J_split: "J = F\<^sub>1 \<union> F\<^sub>2"
    and hD44_F\<^sub>1_bl: "geotop_is_broken_line F\<^sub>1"
    and hD44_F\<^sub>2_bl: "geotop_is_broken_line F\<^sub>2"
    and hD44_F\<^sub>1E: "geotop_arc_endpoints F\<^sub>1 {Q, S}"
    and hD44_F\<^sub>2E: "geotop_arc_endpoints F\<^sub>2 {Q, S}"
    and hD44_F\<^sub>1F\<^sub>2_int_disj:
      "geotop_arc_interior F\<^sub>1 {Q, S} \<inter>
        geotop_arc_interior F\<^sub>2 {Q, S} = {}"
    and hD44_P_F\<^sub>1:
      "P \<in> geotop_arc_interior F\<^sub>1 {Q, S}"
    using hD44_QS_broken_boundary_arc_split
    by (elim exE conjE)
  have hD44_F\<^sub>1F\<^sub>2_inter: "F\<^sub>1 \<inter> F\<^sub>2 = {Q, S}"
    by (rule geotop_same_endpoint_arcs_inter_eq_prefix
        [OF hD44_F\<^sub>1E hD44_F\<^sub>2E hD44_F\<^sub>1F\<^sub>2_int_disj])
  have hD44_PR_on_QS_boundary_arc_interiors:
      "(P \<in> geotop_arc_interior F\<^sub>1 {Q, S}
          \<or> P \<in> geotop_arc_interior F\<^sub>2 {Q, S})
        \<and> (R \<in> geotop_arc_interior F\<^sub>1 {Q, S}
          \<or> R \<in> geotop_arc_interior F\<^sub>2 {Q, S})"
    using hD44_F_J_split hP hR hQ_ne_PR hS_ne_PR
    unfolding geotop_arc_interior_def by (by100 blast)
  have hD44_PR_unique_QS_boundary_arc_interiors:
      "((P \<in> geotop_arc_interior F\<^sub>1 {Q, S}
          \<and> P \<notin> geotop_arc_interior F\<^sub>2 {Q, S})
        \<or> (P \<in> geotop_arc_interior F\<^sub>2 {Q, S}
          \<and> P \<notin> geotop_arc_interior F\<^sub>1 {Q, S}))
        \<and> ((R \<in> geotop_arc_interior F\<^sub>1 {Q, S}
          \<and> R \<notin> geotop_arc_interior F\<^sub>2 {Q, S})
        \<or> (R \<in> geotop_arc_interior F\<^sub>2 {Q, S}
          \<and> R \<notin> geotop_arc_interior F\<^sub>1 {Q, S}))"
    using hD44_PR_on_QS_boundary_arc_interiors hD44_F\<^sub>1F\<^sub>2_int_disj
    by (by100 blast)
  have hD44_P_not_F\<^sub>2:
      "P \<notin> geotop_arc_interior F\<^sub>2 {Q, S}"
    using hD44_F\<^sub>1F\<^sub>2_int_disj hD44_P_F\<^sub>1
    by (by100 blast)
  have hD44_R_on_QS_boundary_arc:
      "R \<in> geotop_arc_interior F\<^sub>1 {Q, S}
        \<or> R \<in> geotop_arc_interior F\<^sub>2 {Q, S}"
    using hD44_PR_on_QS_boundary_arc_interiors
    by (by100 blast)
  have hD44_R_F\<^sub>2_if_not_F\<^sub>1:
      "R \<notin> geotop_arc_interior F\<^sub>1 {Q, S} \<Longrightarrow>
        R \<in> geotop_arc_interior F\<^sub>2 {Q, S}"
    using hD44_R_on_QS_boundary_arc
    by (by100 blast)
  have hD44_R_not_F\<^sub>1_from_cyclic:
      "R \<notin> geotop_arc_interior F\<^sub>1 {Q, S}"
    by (rule geotop_polygon_cyclic_order_QS_split_opposite_arc_prefix
        [OF hcyc hD44_P_F\<^sub>1 hD44_F_J_split hD44_F\<^sub>1E hD44_F\<^sub>2E
          hD44_F\<^sub>1F\<^sub>2_int_disj])
  have hD44_R_F\<^sub>2: "R \<in> geotop_arc_interior F\<^sub>2 {Q, S}"
    by (rule hD44_R_F\<^sub>2_if_not_F\<^sub>1[OF hD44_R_not_F\<^sub>1_from_cyclic])
  have hD44_F\<^sub>1_sub_J: "F\<^sub>1 \<subseteq> J"
    using hD44_F_J_split by (by100 blast)
  have hD44_F\<^sub>2_sub_J: "F\<^sub>2 \<subseteq> J"
    using hD44_F_J_split by (by100 blast)
  have hD44_R_not_F\<^sub>1: "R \<notin> F\<^sub>1"
    using hD44_R_not_F\<^sub>1_from_cyclic hD44_R_F\<^sub>2 hD44_F\<^sub>1F\<^sub>2_inter
    unfolding geotop_arc_interior_def by (by100 blast)
  have hD44_P_not_F\<^sub>2_set: "P \<notin> F\<^sub>2"
    using hD44_P_not_F\<^sub>2 hD44_P_F\<^sub>1 hD44_F\<^sub>1F\<^sub>2_inter
    unfolding geotop_arc_interior_def by (by100 blast)
  have hD44_A1_F\<^sub>2_disj: "A1 \<inter> F\<^sub>2 = {}"
  proof (rule equals0I)
    fix x
    assume hx: "x \<in> A1 \<inter> F\<^sub>2"
    have hxA1J: "x \<in> A1 \<inter> J"
      using hx hD44_F\<^sub>2_sub_J by (by100 blast)
    have hxP: "x = P"
      using hxA1J hA1J by (by100 blast)
    have "P \<in> F\<^sub>2"
      using hx hxP by (by100 blast)
    thus False
      using hD44_P_not_F\<^sub>2_set by (by100 blast)
  qed
  have hD44_A1_F\<^sub>1_inter: "A1 \<inter> F\<^sub>1 = {P}"
  proof
    show "A1 \<inter> F\<^sub>1 \<subseteq> {P}"
    proof
      fix x
      assume hx: "x \<in> A1 \<inter> F\<^sub>1"
      have hxA1J: "x \<in> A1 \<inter> J"
        using hx hD44_F\<^sub>1_sub_J by (by100 blast)
      show "x \<in> {P}"
        using hxA1J hA1J by (by100 blast)
    qed
    show "{P} \<subseteq> A1 \<inter> F\<^sub>1"
      using hP_in_A1 hD44_P_F\<^sub>1
      unfolding geotop_arc_interior_def by (by100 blast)
  qed
  have hD44_A2_F\<^sub>1_disj: "A2 \<inter> F\<^sub>1 = {}"
  proof (rule equals0I)
    fix x
    assume hx: "x \<in> A2 \<inter> F\<^sub>1"
    have hxA2J: "x \<in> A2 \<inter> J"
      using hx hD44_F\<^sub>1_sub_J by (by100 blast)
    have hxR: "x = R"
      using hxA2J hA2J by (by100 blast)
    have "R \<in> F\<^sub>1"
      using hx hxR by (by100 blast)
    thus False
      using hD44_R_not_F\<^sub>1 by (by100 blast)
  qed
  have hD44_A2_F\<^sub>2_inter: "A2 \<inter> F\<^sub>2 = {R}"
  proof
    show "A2 \<inter> F\<^sub>2 \<subseteq> {R}"
    proof
      fix x
      assume hx: "x \<in> A2 \<inter> F\<^sub>2"
      have hxA2J: "x \<in> A2 \<inter> J"
        using hx hD44_F\<^sub>2_sub_J by (by100 blast)
      show "x \<in> {R}"
        using hxA2J hA2J by (by100 blast)
    qed
    show "{R} \<subseteq> A2 \<inter> F\<^sub>2"
      using hR_in_A2 hD44_R_F\<^sub>2
      unfolding geotop_arc_interior_def by (by100 blast)
  qed
  have hD44_P_not_Ncut: "P \<notin> ?Ncut"
    using hP_in_A1 hA1_N by (by100 blast)
  have hD44_Q_not_Ncut: "Q \<notin> ?Ncut"
  proof
    assume hQcut: "Q \<in> ?Ncut"
    have hQint: "Q \<in> geotop_polygon_interior J"
      using hQcut by (by100 blast)
    have "Q \<notin> geotop_polygon_interior J"
      using hQ polygon_interior_disjoint_polygon[OF hJ] by (by100 blast)
    thus False
      using hQint by (by100 blast)
  qed
  have hD44_R_not_Ncut: "R \<notin> ?Ncut"
    using hR_in_A2 by (by100 blast)
  have hD44_S_not_Ncut: "S \<notin> ?Ncut"
  proof
    assume hScut: "S \<in> ?Ncut"
    have hSint: "S \<in> geotop_polygon_interior J"
      using hScut by (by100 blast)
    have "S \<notin> geotop_polygon_interior J"
      using hS polygon_interior_disjoint_polygon[OF hJ] by (by100 blast)
    thus False
      using hSint by (by100 blast)
  qed
  have hD44_F\<^sub>1_Ncut_disj: "F\<^sub>1 \<inter> ?Ncut = {}"
  proof (rule equals0I)
    fix x
    assume hx: "x \<in> F\<^sub>1 \<inter> ?Ncut"
    have hxJ: "x \<in> J"
      using hx hD44_F\<^sub>1_sub_J by (by100 blast)
    have hxI: "x \<in> geotop_polygon_interior J"
      using hx by (by100 blast)
    have "x \<notin> geotop_polygon_interior J"
      using hxJ polygon_interior_disjoint_polygon[OF hJ] by (by100 blast)
    thus False
      using hxI by (by100 blast)
  qed
  have hD44_F\<^sub>2_Ncut_disj: "F\<^sub>2 \<inter> ?Ncut = {}"
  proof (rule equals0I)
    fix x
    assume hx: "x \<in> F\<^sub>2 \<inter> ?Ncut"
    have hxJ: "x \<in> J"
      using hx hD44_F\<^sub>2_sub_J by (by100 blast)
    have hxI: "x \<in> geotop_polygon_interior J"
      using hx by (by100 blast)
    have "x \<notin> geotop_polygon_interior J"
      using hxJ polygon_interior_disjoint_polygon[OF hJ] by (by100 blast)
    thus False
      using hxI by (by100 blast)
  qed
  let ?B\<^sub>1 = "geotop_polyhedron BdJ\<^sub>N \<inter> J"
  have hD44_B\<^sub>1_eq_J\<^sub>N_boundary: "?B\<^sub>1 = J\<^sub>N \<inter> J"
    using hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
  have hD44_P_BdJ\<^sub>N_F\<^sub>1:
      "P \<in> geotop_polyhedron BdJ\<^sub>N \<inter> F\<^sub>1"
    using hP_BdJ\<^sub>N_poly hD44_P_F\<^sub>1
    unfolding geotop_arc_interior_def by (by100 blast)
  have hD44_P_B\<^sub>1: "P \<in> ?B\<^sub>1"
    using hP_BdJ\<^sub>N_poly hP by (by100 blast)
  have hD44_B\<^sub>1_nonempty: "?B\<^sub>1 \<noteq> {}"
    using hD44_P_B\<^sub>1 by (by100 blast)
  have hD44_B\<^sub>1_sub_boundary_arcs:
      "?B\<^sub>1 \<subseteq> F\<^sub>1 \<union> F\<^sub>2"
    using hD44_F_J_split by (by100 blast)
  have hD44_B\<^sub>1_A2_QS_disj:
      "?B\<^sub>1 \<inter> (A2 \<union> {Q, S}) = {}"
    using hBdJ\<^sub>N_poly_A2_QS_disj by (by100 blast)
  have hD44_B\<^sub>1_R_notin: "R \<notin> ?B\<^sub>1"
    using hD44_B\<^sub>1_A2_QS_disj hR_in_A2 by (by100 blast)
  have hD44_B\<^sub>1_Q_notin: "Q \<notin> ?B\<^sub>1"
    using hD44_B\<^sub>1_A2_QS_disj by (by100 blast)
  have hD44_B\<^sub>1_S_notin: "S \<notin> ?B\<^sub>1"
    using hD44_B\<^sub>1_A2_QS_disj by (by100 blast)
  have hD44_B\<^sub>1_Ncut_disj: "?B\<^sub>1 \<inter> ?Ncut = {}"
    using hNcut_BdJ\<^sub>N_poly_disj by (by100 blast)
  have hD44_B\<^sub>1_sub_J\<^sub>N: "?B\<^sub>1 \<subseteq> J\<^sub>N"
    using hD44_B\<^sub>1_eq_J\<^sub>N_boundary by (by100 blast)
  have hD44_J_closed: "closed J"
    by (rule polygon_closed[OF hJ])
  have hD44_B\<^sub>1_closed: "closed ?B\<^sub>1"
    by (rule closed_Int[OF hBdJ\<^sub>N_poly_closed hD44_J_closed])
  have hD44_B\<^sub>1_compact: "compact ?B\<^sub>1"
    using hBdJ\<^sub>N_poly_compact hD44_J_closed by (rule compact_Int_closed)
  let ?B1P = "geotop_component_at UNIV geotop_euclidean_topology ?B\<^sub>1 P"
  have hD44_B1P_eq_J\<^sub>N_boundary_component:
      "?B1P =
        geotop_component_at UNIV geotop_euclidean_topology (J\<^sub>N \<inter> J) P"
    using hD44_B\<^sub>1_eq_J\<^sub>N_boundary by (by100 simp)
  have hD44_B1P_sub_B\<^sub>1: "?B1P \<subseteq> ?B\<^sub>1"
  proof -
    have hB1P_eq:
        "?B1P = connected_component_set ?B\<^sub>1 P"
      by (rule geotop_component_at_UNIV_eq_connected_component_set)
    have hcc_sub:
        "connected_component_set ?B\<^sub>1 P \<subseteq> ?B\<^sub>1"
      by (rule connected_component_subset)
    show ?thesis
      using hB1P_eq hcc_sub by (by100 blast)
  qed
  have hD44_B1P_sub_J\<^sub>N: "?B1P \<subseteq> J\<^sub>N"
    using hD44_B1P_sub_B\<^sub>1 hD44_B\<^sub>1_sub_J\<^sub>N by (by100 blast)
  have hD44_B1P_sub_FrN\<^sub>I: "?B1P \<subseteq> FrN\<^sub>I"
    using hD44_B1P_sub_J\<^sub>N hJ\<^sub>N_sub_FrN\<^sub>I by (by100 blast)
  have hD44_B1P_conn:
      "top1_connected_on ?B1P
        (subspace_topology UNIV geotop_euclidean_topology ?B1P)"
  proof -
    have hB1P_eq:
        "?B1P = connected_component_set ?B\<^sub>1 P"
      by (rule geotop_component_at_UNIV_eq_connected_component_set)
    have hB1P_conn_HOL: "connected ?B1P"
      using hB1P_eq connected_connected_component by (by100 simp)
    show ?thesis
      using hB1P_conn_HOL top1_connected_on_geotop_iff_connected by (by100 blast)
  qed
  have hD44_P_B1P: "P \<in> ?B1P"
    using hD44_P_B\<^sub>1
      geotop_component_at_UNIV_eq_connected_component_set[of ?B\<^sub>1 P]
    by (by100 simp)
  have hD44_P_boundary_edge_sub_B1P:
      "\<exists>e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> P \<in> e \<and> e \<subseteq> J \<and> e \<subseteq> ?B1P"
  proof -
    obtain e where heBdJ: "e \<in> BdJ\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      and heJ: "e \<subseteq> J"
      using hBdJ\<^sub>N_P_boundary_edge by (by100 blast)
    have he_sub_B\<^sub>1: "e \<subseteq> ?B\<^sub>1"
      unfolding geotop_polyhedron_def using heBdJ heJ by (by100 blast)
    have he_simplex: "geotop_is_simplex e"
      using hedge unfolding geotop_is_edge_def
      by (rule geotop_simplex_dim_imp_is_simplex)
    have he_path_connected:
        "top1_path_connected_on e
          (subspace_topology UNIV geotop_euclidean_topology e)"
      by (rule Theorem_GT_1_3[OF he_simplex])
    have he_connected:
        "top1_connected_on e
          (subspace_topology UNIV geotop_euclidean_topology e)"
      by (rule top1_path_connected_on_geotop_imp_connected[OF he_path_connected])
    have he_witness:
        "e \<in> {C. C \<subseteq> ?B\<^sub>1 \<and> P \<in> C \<and>
          top1_connected_on C
            (subspace_topology UNIV geotop_euclidean_topology C)}"
      using he_sub_B\<^sub>1 hP_e he_connected by (by100 simp)
    have he_sub_B1P: "e \<subseteq> ?B1P"
    proof
      fix x
      assume hx: "x \<in> e"
      show "x \<in> ?B1P"
        unfolding geotop_component_at_def
        using he_witness hx by (by100 blast)
    qed
    show ?thesis
      using heBdJ hedge hP_e heJ he_sub_B1P
      by (intro bexI[where x=e] conjI)
  qed
  have hD44_B1P_nontrivial: "\<exists>x\<in>?B1P. x \<noteq> P"
  proof -
    obtain e where hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      and he_sub_B1P: "e \<subseteq> ?B1P"
      using hD44_P_boundary_edge_sub_B1P by (by100 blast)
    have hex_other: "\<exists>x\<in>e. x \<noteq> P"
    proof (rule ccontr)
      assume hnot: "\<not> (\<exists>x\<in>e. x \<noteq> P)"
      have he_sub_single: "e \<subseteq> {P}"
        using hnot by (by100 blast)
      have he_eq_single: "e = {P}"
        using hP_e he_sub_single by (by100 blast)
      have "geotop_is_edge {P}"
        using hedge he_eq_single by (by100 simp)
      thus False
        using geotop_singleton_not_edge_prefix by (by100 blast)
    qed
    obtain x where hx_e: "x \<in> e" and hx_ne: "x \<noteq> P"
      using hex_other by (by100 blast)
    have hx_B1P: "x \<in> ?B1P"
      using he_sub_B1P hx_e by (by100 blast)
    show ?thesis
      using hx_B1P hx_ne by (by100 blast)
  qed
  have hD44_B1P_eq_connected_component:
      "?B1P = connected_component_set ?B\<^sub>1 P"
    by (rule geotop_component_at_UNIV_eq_connected_component_set)
  have hD44_B1P_closed: "closed ?B1P"
    unfolding hD44_B1P_eq_connected_component
    by (rule closed_connected_component[OF hD44_B\<^sub>1_closed])
  have hD44_B1P_component: "?B1P \<in> components ?B\<^sub>1"
    using hD44_B1P_eq_connected_component componentsI[OF hD44_P_B\<^sub>1]
    by (by100 simp)
  have hD44_B1P_compact: "compact ?B1P"
    by (rule compact_components[OF hD44_B\<^sub>1_compact hD44_B1P_component])
  have hD44_B1P_sub_boundary_arcs:
      "?B1P \<subseteq> F\<^sub>1 \<union> F\<^sub>2"
    using hD44_B1P_sub_B\<^sub>1 hD44_B\<^sub>1_sub_boundary_arcs by (by100 blast)
  have hD44_B1P_A2_QS_disj:
      "?B1P \<inter> (A2 \<union> {Q, S}) = {}"
    using hD44_B1P_sub_B\<^sub>1 hD44_B\<^sub>1_A2_QS_disj by (by100 blast)
  have hD44_B1P_Ncut_disj: "?B1P \<inter> ?Ncut = {}"
    using hD44_B1P_sub_B\<^sub>1 hD44_B\<^sub>1_Ncut_disj by (by100 blast)
  have hD44_B1P_R_notin: "R \<notin> ?B1P"
    using hD44_B1P_A2_QS_disj hR_in_A2 by (by100 blast)
  have hD44_B1P_Q_notin: "Q \<notin> ?B1P"
    using hD44_B1P_A2_QS_disj by (by100 blast)
  have hD44_B1P_S_notin: "S \<notin> ?B1P"
    using hD44_B1P_A2_QS_disj by (by100 blast)
  have hD44_F\<^sub>1_closed: "closed F\<^sub>1"
    by (rule broken_line_closed[OF hD44_F\<^sub>1E])
  have hD44_F\<^sub>2_closed: "closed F\<^sub>2"
    by (rule broken_line_closed[OF hD44_F\<^sub>2E])
  have hD44_F\<^sub>2_nonempty: "F\<^sub>2 \<noteq> {}"
    using hD44_F\<^sub>2E unfolding geotop_arc_endpoints_def by (by100 blast)
  have hD44_UNIV_top:
      "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets
        top1_open_sets_is_topology_on_UNIV)
  let ?F1o = "F\<^sub>1 - {Q, S}"
  let ?F2o = "F\<^sub>2 - {Q, S}"
  have hD44_F1o_F2o_separated:
      "geotop_separated UNIV geotop_euclidean_topology ?F1o ?F2o"
  proof -
    have hF1o_closedin:
        "closedin_on UNIV geotop_euclidean_topology F\<^sub>1"
      using hD44_F\<^sub>1_closed closedin_on_geotop_UNIV_iff_closed by (by100 blast)
    have hF2o_closedin:
        "closedin_on UNIV geotop_euclidean_topology F\<^sub>2"
      using hD44_F\<^sub>2_closed closedin_on_geotop_UNIV_iff_closed by (by100 blast)
    have hcl_F1o_sub_F1:
        "closure_on UNIV geotop_euclidean_topology ?F1o \<subseteq> F\<^sub>1"
      by (rule closure_on_subset_of_closed[OF hF1o_closedin]) (by100 blast)
    have hcl_F2o_sub_F2:
        "closure_on UNIV geotop_euclidean_topology ?F2o \<subseteq> F\<^sub>2"
      by (rule closure_on_subset_of_closed[OF hF2o_closedin]) (by100 blast)
    have hcl_F1o_F2o_disj:
        "closure_on UNIV geotop_euclidean_topology ?F1o \<inter> ?F2o = {}"
      using hcl_F1o_sub_F1 hD44_F\<^sub>1F\<^sub>2_inter by (by100 blast)
    have hF1o_cl_F2o_disj:
        "?F1o \<inter> closure_on UNIV geotop_euclidean_topology ?F2o = {}"
      using hcl_F2o_sub_F2 hD44_F\<^sub>1F\<^sub>2_inter by (by100 blast)
    show ?thesis
      unfolding geotop_separated_def
      using hcl_F1o_F2o_disj hF1o_cl_F2o_disj by (by100 simp)
  qed
  have hD44_B1P_sub_F1_or_F2:
      "?B1P \<subseteq> ?F1o \<or> ?B1P \<subseteq> ?F2o"
  proof -
    have hB1P_sub_F1oF2o: "?B1P \<subseteq> ?F1o \<union> ?F2o"
      using hD44_B1P_sub_boundary_arcs hD44_B1P_Q_notin hD44_B1P_S_notin
      by (by100 blast)
    show ?thesis
      by (rule Theorem_GT_1_10
          [OF hD44_UNIV_top hD44_F1o_F2o_separated
            hB1P_sub_F1oF2o hD44_B1P_conn])
  qed
  have hD44_P_F1o: "P \<in> ?F1o"
    using hD44_P_F\<^sub>1 unfolding geotop_arc_interior_def by (by100 blast)
  have hD44_P_not_F2o: "P \<notin> ?F2o"
    using hD44_P_not_F\<^sub>2_set by (by100 blast)
  have hD44_B1P_sub_F1o: "?B1P \<subseteq> ?F1o"
  proof (rule ccontr)
    assume hnot: "\<not> ?B1P \<subseteq> ?F1o"
    have hsub_F2o: "?B1P \<subseteq> ?F2o"
      using hD44_B1P_sub_F1_or_F2 hnot by (by100 blast)
    have "P \<in> ?F2o"
      using hsub_F2o hD44_P_B1P by (by100 blast)
    thus False
      using hD44_P_not_F2o by (by100 blast)
  qed
  have hD44_B1P_sub_F\<^sub>1_arc_interior:
      "?B1P \<subseteq> geotop_arc_interior F\<^sub>1 {Q, S}"
    using hD44_B1P_sub_F1o unfolding geotop_arc_interior_def by (by100 simp)
  have hD44_B1P_sub_F\<^sub>1: "?B1P \<subseteq> F\<^sub>1"
    using hD44_B1P_sub_F1o by (by100 blast)
  have hD44_B1P_inter_F\<^sub>1: "?B1P \<inter> F\<^sub>1 = ?B1P"
    using hD44_B1P_sub_F\<^sub>1 by (by100 blast)
  have hD44_B1P_F\<^sub>2_disj: "?B1P \<inter> F\<^sub>2 = {}"
    using hD44_B1P_sub_F1o hD44_F\<^sub>1F\<^sub>2_inter by (by100 blast)
  have hD44_B1P_other_F\<^sub>1_arc_interior:
      "\<exists>X. X \<in> ?B1P
        \<and> X \<in> geotop_arc_interior F\<^sub>1 {Q, S}
        \<and> X \<noteq> P"
  proof -
    obtain X where hX_B1P: "X \<in> ?B1P" and hX_ne: "X \<noteq> P"
      using hD44_B1P_nontrivial by (by100 blast)
    have hX_F1int: "X \<in> geotop_arc_interior F\<^sub>1 {Q, S}"
      using hD44_B1P_sub_F\<^sub>1_arc_interior hX_B1P by (by100 blast)
    show ?thesis
      using hX_B1P hX_F1int hX_ne by (intro exI conjI)
  qed
  have hD44_F\<^sub>1_boundary_subarc_from_P_to_B1P:
      "\<exists>X C. X \<in> ?B1P
        \<and> X \<noteq> P
        \<and> geotop_is_broken_line C
        \<and> C \<subseteq> F\<^sub>1
        \<and> P \<in> C
        \<and> X \<in> C
        \<and> geotop_arc_endpoints C {P, X}"
  proof -
    obtain X where hX_B1P: "X \<in> ?B1P"
      and hX_F1int: "X \<in> geotop_arc_interior F\<^sub>1 {Q, S}"
      and hX_ne: "X \<noteq> P"
      using hD44_B1P_other_F\<^sub>1_arc_interior by (elim exE conjE)
    have hP_F1: "P \<in> F\<^sub>1"
      using hD44_P_F\<^sub>1 unfolding geotop_arc_interior_def by (by100 blast)
    have hX_F1: "X \<in> F\<^sub>1"
      using hX_F1int unfolding geotop_arc_interior_def by (by100 blast)
    have hP_ne_X: "P \<noteq> X"
      using hX_ne by (by100 blast)
    obtain C where hC_bl: "geotop_is_broken_line C"
      and hC_sub: "C \<subseteq> F\<^sub>1"
      and hP_C: "P \<in> C"
      and hX_C: "X \<in> C"
      and hC_end: "geotop_arc_endpoints C {P, X}"
      using geotop_broken_line_subarc_with_endpoints_prefix
        [OF hD44_F\<^sub>1_bl hP_F1 hX_F1 hP_ne_X]
      by (by100 blast)
    show ?thesis
      using hX_B1P hX_ne hC_bl hC_sub hP_C hX_C hC_end
      by (intro exI conjI)
  qed
  have hD44_B1P_boundary_subarc_inside_B1P:
      "\<exists>X C. X \<in> ?B1P
        \<and> X \<noteq> P
        \<and> geotop_is_broken_line C
        \<and> C \<subseteq> ?B1P
        \<and> P \<in> C
        \<and> X \<in> C
        \<and> geotop_arc_endpoints C {P, X}"
  proof -
    obtain X where hX_B1P: "X \<in> ?B1P"
      and hX_F1int: "X \<in> geotop_arc_interior F\<^sub>1 {Q, S}"
      and hX_ne: "X \<noteq> P"
      using hD44_B1P_other_F\<^sub>1_arc_interior by (elim exE conjE)
    have hB1P_conn_HOL: "connected ?B1P"
      using hD44_B1P_conn top1_connected_on_geotop_iff_connected
      by (by100 blast)
    have hP_ne_X: "P \<noteq> X"
      using hX_ne by (by100 blast)
    obtain C where hC_bl: "geotop_is_broken_line C"
      and hC_sub: "C \<subseteq> ?B1P"
      and hP_C: "P \<in> C"
      and hX_C: "X \<in> C"
      and hC_end: "geotop_arc_endpoints C {P, X}"
      using geotop_connected_subset_broken_line_subarc_with_endpoints_prefix
          [OF hD44_F\<^sub>1_bl hD44_B1P_sub_F\<^sub>1 hB1P_conn_HOL
            hD44_P_B1P hX_B1P hP_ne_X]
      by (by100 blast)
    show ?thesis
      using hX_B1P hX_ne hC_bl hC_sub hP_C hX_C hC_end
      by (intro exI conjI)
  qed
  have hD44_F\<^sub>1_boundary_subarc_vertex_refinement_from_P_to_B1P:
      "\<exists>X C L. X \<in> ?B1P
        \<and> X \<noteq> P
        \<and> geotop_is_broken_line C
        \<and> C \<subseteq> ?B1P
        \<and> C \<subseteq> F\<^sub>1
        \<and> P \<in> C
        \<and> X \<in> C
        \<and> geotop_arc_endpoints C {P, X}
        \<and> connected (geotop_arc_interior C {P, X})
        \<and> geotop_arc_interior C {P, X} \<noteq> {}
        \<and> geotop_is_complex L
        \<and> geotop_complex_is_1dim L
        \<and> finite L
        \<and> geotop_polyhedron L = C
        \<and> {P} \<in> L
        \<and> {X} \<in> L"
  proof -
    obtain X C where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hC_bl: "geotop_is_broken_line C"
      and hP_C: "P \<in> C"
      and hX_C: "X \<in> C"
      and hC_end: "geotop_arc_endpoints C {P, X}"
      and hC_sub_B1P: "C \<subseteq> ?B1P"
      using hD44_B1P_boundary_subarc_inside_B1P by (elim exE conjE)
    have hC_sub_F1: "C \<subseteq> F\<^sub>1"
      using hC_sub_B1P hD44_B1P_sub_F\<^sub>1 by (by100 blast)
    obtain L0 where hL0_complex: "geotop_is_complex L0"
      and hL0_1dim: "geotop_complex_is_1dim L0"
      and hL0_poly: "geotop_polyhedron L0 = C"
      and hP_L0: "{P} \<in> L0"
      and hL0_fin: "finite L0"
      using geotop_broken_line_vertex_at[OF hC_bl hP_C] by (by100 blast)
    have hX_poly_L0: "X \<in> geotop_polyhedron L0"
      using hX_C hL0_poly by (by100 simp)
    obtain L where hL_complex: "geotop_is_complex L"
      and hL_1dim: "geotop_complex_is_1dim L"
      and hL_poly: "geotop_polyhedron L = geotop_polyhedron L0"
      and hX_L: "{X} \<in> L"
      and hvertices_preserved: "\<forall>v. {v} \<in> L0 \<longrightarrow> {v} \<in> L"
      and hL_fin_if: "finite L0 \<longrightarrow> finite L"
      using geotop_complex_subdivide_at
        [OF hL0_complex hL0_1dim hX_poly_L0]
      by (by100 blast)
    have hP_L: "{P} \<in> L"
      using hvertices_preserved hP_L0 by (by100 blast)
    have hL_fin: "finite L"
      using hL_fin_if hL0_fin by (by100 blast)
    have hL_poly_C: "geotop_polyhedron L = C"
      using hL_poly hL0_poly by (by100 simp)
    have hC_int_connected: "connected (geotop_arc_interior C {P, X})"
      by (rule arc_interior_connected[OF hC_end])
    have hC_int_nonempty: "geotop_arc_interior C {P, X} \<noteq> {}"
      by (rule arc_interior_nonempty[OF hC_end])
    show ?thesis
      using hX_B1P hX_ne hC_bl hC_sub_B1P hC_sub_F1 hP_C hX_C hC_end
        hC_int_connected hC_int_nonempty
        hL_complex hL_1dim hL_fin hL_poly_C hP_L hX_L
      by (intro exI conjI)
  qed
  have hD44_B1P_boundary_subarc_frontier_package:
      "\<exists>X C L. X \<in> ?B1P
        \<and> X \<noteq> P
        \<and> geotop_is_broken_line C
        \<and> C \<subseteq> ?B1P
        \<and> C \<subseteq> F\<^sub>1
        \<and> C \<subseteq> J\<^sub>N
        \<and> C \<subseteq> FrN\<^sub>I
        \<and> C \<inter> F\<^sub>2 = {}
        \<and> C \<inter> (A2 \<union> {Q, S}) = {}
        \<and> C \<inter> ?Ncut = {}
        \<and> P \<in> C
        \<and> X \<in> C
        \<and> geotop_arc_endpoints C {P, X}
        \<and> connected (geotop_arc_interior C {P, X})
        \<and> geotop_arc_interior C {P, X} \<noteq> {}
        \<and> geotop_is_complex L
        \<and> geotop_complex_is_1dim L
        \<and> finite L
        \<and> geotop_polyhedron L = C
        \<and> {P} \<in> L
        \<and> {X} \<in> L"
  proof -
    obtain X C L where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hC_bl: "geotop_is_broken_line C"
      and hC_sub_B1P: "C \<subseteq> ?B1P"
      and hC_sub_F1: "C \<subseteq> F\<^sub>1"
      and hP_C: "P \<in> C"
      and hX_C: "X \<in> C"
      and hC_end: "geotop_arc_endpoints C {P, X}"
      and hC_int_connected: "connected (geotop_arc_interior C {P, X})"
      and hC_int_nonempty: "geotop_arc_interior C {P, X} \<noteq> {}"
      and hL_complex: "geotop_is_complex L"
      and hL_1dim: "geotop_complex_is_1dim L"
      and hL_fin: "finite L"
      and hL_poly_C: "geotop_polyhedron L = C"
      and hP_L: "{P} \<in> L"
      and hX_L: "{X} \<in> L"
      using hD44_F\<^sub>1_boundary_subarc_vertex_refinement_from_P_to_B1P
      by (elim exE conjE)
    have hC_sub_J\<^sub>N: "C \<subseteq> J\<^sub>N"
      using hC_sub_B1P hD44_B1P_sub_J\<^sub>N by (by100 blast)
    have hC_sub_FrN\<^sub>I: "C \<subseteq> FrN\<^sub>I"
      using hC_sub_B1P hD44_B1P_sub_FrN\<^sub>I by (by100 blast)
    have hC_F\<^sub>2_disj: "C \<inter> F\<^sub>2 = {}"
      using hC_sub_B1P hD44_B1P_F\<^sub>2_disj by (by100 blast)
    have hC_A2_QS_disj: "C \<inter> (A2 \<union> {Q, S}) = {}"
      using hC_sub_B1P hD44_B1P_A2_QS_disj by (by100 blast)
    have hC_Ncut_disj: "C \<inter> ?Ncut = {}"
      using hC_sub_B1P hD44_B1P_Ncut_disj by (by100 blast)
    show ?thesis
      using hX_B1P hX_ne hC_bl hC_sub_B1P hC_sub_F1 hC_sub_J\<^sub>N
        hC_sub_FrN\<^sub>I hC_F\<^sub>2_disj hC_A2_QS_disj hC_Ncut_disj
        hP_C hX_C hC_end hC_int_connected hC_int_nonempty
        hL_complex hL_1dim hL_fin hL_poly_C hP_L hX_L
      by (intro exI conjI)
  qed
  have hD44_BdJ\<^sub>N_polygon_split_at_B1P_endpoint:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>X C L C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_is_broken_line C
          \<and> C \<subseteq> ?B1P
          \<and> C \<subseteq> F\<^sub>1
          \<and> C \<subseteq> J\<^sub>N
          \<and> C \<subseteq> FrN\<^sub>I
          \<and> C \<inter> F\<^sub>2 = {}
          \<and> C \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C \<inter> ?Ncut = {}
          \<and> P \<in> C
          \<and> X \<in> C
          \<and> geotop_arc_endpoints C {P, X}
          \<and> connected (geotop_arc_interior C {P, X})
          \<and> geotop_arc_interior C {P, X} \<noteq> {}
          \<and> geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> {P} \<in> L
          \<and> {X} \<in> L
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}
          \<and> C\<^sub>B \<inter> C\<^sub>O = {P, X}
          \<and> P \<in> C\<^sub>B
          \<and> X \<in> C\<^sub>B
          \<and> P \<in> C\<^sub>O
          \<and> X \<in> C\<^sub>O
          \<and> C \<subseteq> C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_arc_interior C {P, X} \<subseteq>
              geotop_arc_interior C\<^sub>B {P, X} \<union>
              geotop_arc_interior C\<^sub>O {P, X}
          \<and> (geotop_arc_interior C {P, X} \<subseteq>
                geotop_arc_interior C\<^sub>B {P, X}
              \<or> geotop_arc_interior C {P, X} \<subseteq>
                geotop_arc_interior C\<^sub>O {P, X})
          \<and> (C = C\<^sub>B \<or> C = C\<^sub>O)"
  proof -
    assume hpolygon:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    obtain X C L where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hC_bl: "geotop_is_broken_line C"
      and hC_sub_B1P: "C \<subseteq> ?B1P"
      and hC_sub_F1: "C \<subseteq> F\<^sub>1"
      and hC_sub_J\<^sub>N: "C \<subseteq> J\<^sub>N"
      and hC_sub_FrN\<^sub>I: "C \<subseteq> FrN\<^sub>I"
      and hC_F\<^sub>2_disj: "C \<inter> F\<^sub>2 = {}"
      and hC_A2_QS_disj: "C \<inter> (A2 \<union> {Q, S}) = {}"
      and hC_Ncut_disj: "C \<inter> ?Ncut = {}"
      and hP_C: "P \<in> C"
      and hX_C: "X \<in> C"
      and hC_end: "geotop_arc_endpoints C {P, X}"
      and hC_int_connected: "connected (geotop_arc_interior C {P, X})"
      and hC_int_nonempty: "geotop_arc_interior C {P, X} \<noteq> {}"
      and hL_complex: "geotop_is_complex L"
      and hL_1dim: "geotop_complex_is_1dim L"
      and hL_fin: "finite L"
      and hL_poly_C: "geotop_polyhedron L = C"
      and hP_L: "{P} \<in> L"
      and hX_L: "{X} \<in> L"
      using hD44_B1P_boundary_subarc_frontier_package
      by (elim exE conjE)
    have hX_BdJ_poly: "X \<in> geotop_polyhedron BdJ\<^sub>N"
      using hX_B1P hD44_B1P_sub_B\<^sub>1 by (by100 blast)
    obtain LJ where hLJ_linear: "geotop_is_linear_graph LJ"
      and hLJ_fin: "finite LJ"
      and hLJ_conn: "geotop_complex_connected LJ"
      and hLJ_poly: "geotop_polyhedron LJ = geotop_polyhedron BdJ\<^sub>N"
      and hP_LJ: "{P} \<in> LJ"
      and hX_LJ: "{X} \<in> LJ"
      using geotop_polygon_finite_connected_linear_graph_with_two_vertices_prefix
        [OF hpolygon hP_BdJ\<^sub>N_poly hX_BdJ_poly]
      by (elim exE conjE)
    have hLJ_polygon: "geotop_is_polygon (geotop_polyhedron LJ)"
      using hpolygon hLJ_poly by (by100 simp)
    have hP_ne_X: "P \<noteq> X"
      using hX_ne by (by100 blast)
    obtain C\<^sub>B C\<^sub>O where hsplit:
        "geotop_polyhedron LJ = C\<^sub>B \<union> C\<^sub>O
        \<and> geotop_is_broken_line C\<^sub>B
        \<and> geotop_is_broken_line C\<^sub>O
        \<and> geotop_arc_endpoints C\<^sub>B {P, X}
        \<and> geotop_arc_endpoints C\<^sub>O {P, X}
        \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
            geotop_arc_interior C\<^sub>O {P, X} = {}"
      using geotop_polygon_finite_linear_graph_two_vertex_boundary_split_prefix
        [OF hLJ_linear hLJ_fin hLJ_conn hLJ_polygon hP_LJ hX_LJ hP_ne_X]
      by (by100 blast)
    have hC\<^sub>B_end_split: "geotop_arc_endpoints C\<^sub>B {P, X}"
      using hsplit by (by100 blast)
    have hC\<^sub>O_end_split: "geotop_arc_endpoints C\<^sub>O {P, X}"
      using hsplit by (by100 blast)
    have hC_int_disj_split:
        "geotop_arc_interior C\<^sub>B {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
      using hsplit by (by100 blast)
    have hC_inter: "C\<^sub>B \<inter> C\<^sub>O = {P, X}"
      by (rule geotop_same_endpoint_arcs_inter_eq_prefix
          [OF hC\<^sub>B_end_split hC\<^sub>O_end_split hC_int_disj_split])
    have hP_C\<^sub>B_split: "P \<in> C\<^sub>B"
      using hC\<^sub>B_end_split unfolding geotop_arc_endpoints_def by (by100 blast)
    have hX_C\<^sub>B_split: "X \<in> C\<^sub>B"
      using hC\<^sub>B_end_split unfolding geotop_arc_endpoints_def by (by100 blast)
    have hP_C\<^sub>O_split: "P \<in> C\<^sub>O"
      using hC\<^sub>O_end_split unfolding geotop_arc_endpoints_def by (by100 blast)
    have hX_C\<^sub>O_split: "X \<in> C\<^sub>O"
      using hC\<^sub>O_end_split unfolding geotop_arc_endpoints_def by (by100 blast)
    have hsplit_BdJ:
        "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
        \<and> geotop_is_broken_line C\<^sub>B
        \<and> geotop_is_broken_line C\<^sub>O
        \<and> geotop_arc_endpoints C\<^sub>B {P, X}
        \<and> geotop_arc_endpoints C\<^sub>O {P, X}
        \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
            geotop_arc_interior C\<^sub>O {P, X} = {}
        \<and> C\<^sub>B \<inter> C\<^sub>O = {P, X}
        \<and> P \<in> C\<^sub>B
        \<and> X \<in> C\<^sub>B
        \<and> P \<in> C\<^sub>O
        \<and> X \<in> C\<^sub>O"
      using hsplit hLJ_poly hC_inter hP_C\<^sub>B_split hX_C\<^sub>B_split
        hP_C\<^sub>O_split hX_C\<^sub>O_split
      by (by100 simp)
    have hBdJ_poly_split: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O"
      using hsplit_BdJ by (by100 blast)
    have hC_sub_BdJ_poly: "C \<subseteq> geotop_polyhedron BdJ\<^sub>N"
    proof
      fix y
      assume hyC: "y \<in> C"
      have hyJ\<^sub>N: "y \<in> J\<^sub>N"
        using hC_sub_J\<^sub>N hyC by (by100 blast)
      show "y \<in> geotop_polyhedron BdJ\<^sub>N"
        using hyJ\<^sub>N hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
    qed
    have hC_sub_split: "C \<subseteq> C\<^sub>B \<union> C\<^sub>O"
    proof
      fix y
      assume hyC: "y \<in> C"
      have hyBdJ: "y \<in> geotop_polyhedron BdJ\<^sub>N"
        using hC_sub_BdJ_poly hyC by (by100 blast)
      show "y \<in> C\<^sub>B \<union> C\<^sub>O"
        using hyBdJ hBdJ_poly_split by (by100 simp)
    qed
    have hC_int_sub_split_int:
        "geotop_arc_interior C {P, X} \<subseteq>
          geotop_arc_interior C\<^sub>B {P, X} \<union>
          geotop_arc_interior C\<^sub>O {P, X}"
    proof
      fix y
      assume hy: "y \<in> geotop_arc_interior C {P, X}"
      have hyC: "y \<in> C"
        using hy unfolding geotop_arc_interior_def by (by100 blast)
      have hynot: "y \<notin> {P, X}"
        using hy unfolding geotop_arc_interior_def by (by100 blast)
      have hysplit: "y \<in> C\<^sub>B \<union> C\<^sub>O"
        using hC_sub_split hyC by (by100 blast)
      show "y \<in> geotop_arc_interior C\<^sub>B {P, X} \<union>
          geotop_arc_interior C\<^sub>O {P, X}"
      proof (rule UnE[OF hysplit])
        assume hyB: "y \<in> C\<^sub>B"
        have "y \<in> geotop_arc_interior C\<^sub>B {P, X}"
          using hyB hynot unfolding geotop_arc_interior_def by (by100 blast)
        thus ?thesis by (by100 blast)
      next
        assume hyO: "y \<in> C\<^sub>O"
        have "y \<in> geotop_arc_interior C\<^sub>O {P, X}"
          using hyO hynot unfolding geotop_arc_interior_def by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
    qed
    have hC_int_one_side_split:
        "geotop_arc_interior C {P, X} \<subseteq>
            geotop_arc_interior C\<^sub>B {P, X}
          \<or> geotop_arc_interior C {P, X} \<subseteq>
            geotop_arc_interior C\<^sub>O {P, X}"
    proof (rule ccontr)
      let ?Y = "geotop_arc_interior C {P, X}"
      let ?IB = "geotop_arc_interior C\<^sub>B {P, X}"
      let ?IO = "geotop_arc_interior C\<^sub>O {P, X}"
      assume hnot: "\<not> (?Y \<subseteq> ?IB \<or> ?Y \<subseteq> ?IO)"
      have hnot_IB: "\<not> ?Y \<subseteq> ?IB"
        using hnot by (by100 blast)
      have hnot_IO: "\<not> ?Y \<subseteq> ?IO"
        using hnot by (by100 blast)
      have hYIB_ne: "?Y \<inter> ?IB \<noteq> {}"
      proof -
        obtain y where hyY: "y \<in> ?Y" and hy_not_IO: "y \<notin> ?IO"
          using hnot_IO by (by100 blast)
        have "y \<in> ?IB"
          using hC_int_sub_split_int hyY hy_not_IO by (by100 blast)
        thus ?thesis
          using hyY by (by100 blast)
      qed
      have hYIO_ne: "?Y \<inter> ?IO \<noteq> {}"
      proof -
        obtain y where hyY: "y \<in> ?Y" and hy_not_IB: "y \<notin> ?IB"
          using hnot_IB by (by100 blast)
        have "y \<in> ?IO"
          using hC_int_sub_split_int hyY hy_not_IB by (by100 blast)
        thus ?thesis
          using hyY by (by100 blast)
      qed
      have hY_union: "(?Y \<inter> ?IB) \<union> (?Y \<inter> ?IO) = ?Y"
        using hC_int_sub_split_int by (by100 blast)
      have hY_disj: "(?Y \<inter> ?IB) \<inter> (?Y \<inter> ?IO) = {}"
        using hC_int_disj_split by (by100 blast)
      have hC\<^sub>B_closed: "closed C\<^sub>B"
        by (rule broken_line_closed[OF hC\<^sub>B_end_split])
      have hC\<^sub>O_closed: "closed C\<^sub>O"
        by (rule broken_line_closed[OF hC\<^sub>O_end_split])
      have hYIB_eq: "?Y \<inter> ?IB = ?Y \<inter> C\<^sub>B"
        unfolding geotop_arc_interior_def by (by100 blast)
      have hYIO_eq: "?Y \<inter> ?IO = ?Y \<inter> C\<^sub>O"
        unfolding geotop_arc_interior_def by (by100 blast)
      have hYIB_closed: "closedin (top_of_set ?Y) (?Y \<inter> ?IB)"
      proof -
        have "closedin (top_of_set ?Y) (?Y \<inter> C\<^sub>B)"
          by (rule closedin_closed_Int[OF hC\<^sub>B_closed])
        thus ?thesis
          using hYIB_eq by (by100 simp)
      qed
      have hYIO_closed: "closedin (top_of_set ?Y) (?Y \<inter> ?IO)"
      proof -
        have "closedin (top_of_set ?Y) (?Y \<inter> C\<^sub>O)"
          by (rule closedin_closed_Int[OF hC\<^sub>O_closed])
        thus ?thesis
          using hYIO_eq by (by100 simp)
      qed
      have hNoClosedSep:
          "\<nexists>E\<^sub>1 E\<^sub>2.
            closedin (top_of_set ?Y) E\<^sub>1
            \<and> closedin (top_of_set ?Y) E\<^sub>2
            \<and> E\<^sub>1 \<union> E\<^sub>2 = ?Y
            \<and> E\<^sub>1 \<inter> E\<^sub>2 = {}
            \<and> E\<^sub>1 \<noteq> {}
            \<and> E\<^sub>2 \<noteq> {}"
        using hC_int_connected
        unfolding connected_closedin_eq
        by (by100 blast)
      show False
        using hNoClosedSep hYIB_closed hYIO_closed hY_union hY_disj
          hYIB_ne hYIO_ne
        by (by100 blast)
    qed
    have hC_eq_one_split: "C = C\<^sub>B \<or> C = C\<^sub>O"
    proof (rule disjE[OF hC_int_one_side_split])
      assume hC_int_sub_B:
          "geotop_arc_interior C {P, X} \<subseteq>
            geotop_arc_interior C\<^sub>B {P, X}"
      have hC_sub_B: "C \<subseteq> C\<^sub>B"
      proof
        fix y
        assume hyC: "y \<in> C"
        show "y \<in> C\<^sub>B"
        proof (cases "y \<in> {P, X}")
          case True
          thus ?thesis
            using hP_C\<^sub>B_split hX_C\<^sub>B_split by (by100 blast)
        next
          case False
          have "y \<in> geotop_arc_interior C {P, X}"
            using hyC False unfolding geotop_arc_interior_def by (by100 blast)
          hence "y \<in> geotop_arc_interior C\<^sub>B {P, X}"
            using hC_int_sub_B by (by100 blast)
          thus ?thesis
            unfolding geotop_arc_interior_def by (by100 blast)
        qed
      qed
      have "C = C\<^sub>B"
        by (rule geotop_same_endpoint_arc_subset_eq_prefix
            [OF hC_end hC\<^sub>B_end_split hC_sub_B])
      thus "C = C\<^sub>B \<or> C = C\<^sub>O"
        by (by100 blast)
    next
      assume hC_int_sub_O:
          "geotop_arc_interior C {P, X} \<subseteq>
            geotop_arc_interior C\<^sub>O {P, X}"
      have hC_sub_O: "C \<subseteq> C\<^sub>O"
      proof
        fix y
        assume hyC: "y \<in> C"
        show "y \<in> C\<^sub>O"
        proof (cases "y \<in> {P, X}")
          case True
          thus ?thesis
            using hP_C\<^sub>O_split hX_C\<^sub>O_split by (by100 blast)
        next
          case False
          have "y \<in> geotop_arc_interior C {P, X}"
            using hyC False unfolding geotop_arc_interior_def by (by100 blast)
          hence "y \<in> geotop_arc_interior C\<^sub>O {P, X}"
            using hC_int_sub_O by (by100 blast)
          thus ?thesis
            unfolding geotop_arc_interior_def by (by100 blast)
        qed
      qed
      have "C = C\<^sub>O"
        by (rule geotop_same_endpoint_arc_subset_eq_prefix
            [OF hC_end hC\<^sub>O_end_split hC_sub_O])
      thus "C = C\<^sub>B \<or> C = C\<^sub>O"
        by (by100 blast)
    qed
    show ?thesis
      apply (rule exI[where x=X])
      apply (rule exI[where x=C])
      apply (rule exI[where x=L])
      apply (rule exI[where x=C\<^sub>B])
      apply (rule exI[where x=C\<^sub>O])
      using hX_B1P hX_ne hC_bl hC_sub_B1P hC_sub_F1 hC_sub_J\<^sub>N
        hC_sub_FrN\<^sub>I hC_F\<^sub>2_disj hC_A2_QS_disj hC_Ncut_disj
        hP_C hX_C hC_end hC_int_connected hC_int_nonempty
        hL_complex hL_1dim hL_fin hL_poly_C hP_L hX_L
        hsplit_BdJ hC_inter hP_C\<^sub>B_split hX_C\<^sub>B_split
        hP_C\<^sub>O_split hX_C\<^sub>O_split hC_sub_split hC_int_sub_split_int
        hC_int_one_side_split
        hC_eq_one_split
      apply (intro conjI)
      by (by100 blast)+
  qed
  have hD44_BdJ\<^sub>N_polygon_boundary_subarc_complement_split:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>X C L C\<^sub>F. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_is_broken_line C
          \<and> C \<subseteq> ?B1P
          \<and> C \<subseteq> F\<^sub>1
          \<and> C \<subseteq> J\<^sub>N
          \<and> C \<subseteq> FrN\<^sub>I
          \<and> C \<inter> F\<^sub>2 = {}
          \<and> C \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C \<inter> ?Ncut = {}
          \<and> P \<in> C
          \<and> X \<in> C
          \<and> geotop_arc_endpoints C {P, X}
          \<and> connected (geotop_arc_interior C {P, X})
          \<and> geotop_arc_interior C {P, X} \<noteq> {}
          \<and> geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> {P} \<in> L
          \<and> {X} \<in> L
          \<and> geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>F
          \<and> geotop_is_broken_line C\<^sub>F
          \<and> geotop_arc_endpoints C\<^sub>F {P, X}
          \<and> geotop_arc_interior C {P, X} \<inter>
              geotop_arc_interior C\<^sub>F {P, X} = {}
          \<and> C \<inter> C\<^sub>F = {P, X}
          \<and> P \<in> C\<^sub>F
          \<and> X \<in> C\<^sub>F
          \<and> C\<^sub>F \<subseteq> J\<^sub>N
          \<and> C\<^sub>F \<subseteq> FrN\<^sub>I
          \<and> C\<^sub>F \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C\<^sub>F \<inter> ?Ncut = {}"
  proof -
    assume hpolygon:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    obtain X C L C\<^sub>B C\<^sub>O where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hC_bl: "geotop_is_broken_line C"
      and hC_sub_B1P: "C \<subseteq> ?B1P"
      and hC_sub_F1: "C \<subseteq> F\<^sub>1"
      and hC_sub_J\<^sub>N: "C \<subseteq> J\<^sub>N"
      and hC_sub_FrN\<^sub>I: "C \<subseteq> FrN\<^sub>I"
      and hC_F\<^sub>2_disj: "C \<inter> F\<^sub>2 = {}"
      and hC_A2_QS_disj: "C \<inter> (A2 \<union> {Q, S}) = {}"
      and hC_Ncut_disj: "C \<inter> ?Ncut = {}"
      and hP_C: "P \<in> C"
      and hX_C: "X \<in> C"
      and hC_end: "geotop_arc_endpoints C {P, X}"
      and hC_int_connected: "connected (geotop_arc_interior C {P, X})"
      and hC_int_nonempty: "geotop_arc_interior C {P, X} \<noteq> {}"
      and hL_complex: "geotop_is_complex L"
      and hL_1dim: "geotop_complex_is_1dim L"
      and hL_fin: "finite L"
      and hL_poly_C: "geotop_polyhedron L = C"
      and hP_L: "{P} \<in> L"
      and hX_L: "{X} \<in> L"
      and hBdJ_split: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O"
      and hC\<^sub>B_bl: "geotop_is_broken_line C\<^sub>B"
      and hC\<^sub>O_bl: "geotop_is_broken_line C\<^sub>O"
      and hC\<^sub>B_end: "geotop_arc_endpoints C\<^sub>B {P, X}"
      and hC\<^sub>O_end: "geotop_arc_endpoints C\<^sub>O {P, X}"
      and hC_int_disj:
        "geotop_arc_interior C\<^sub>B {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
      and hC_inter: "C\<^sub>B \<inter> C\<^sub>O = {P, X}"
      and hP_C\<^sub>B: "P \<in> C\<^sub>B"
      and hX_C\<^sub>B: "X \<in> C\<^sub>B"
      and hP_C\<^sub>O: "P \<in> C\<^sub>O"
      and hX_C\<^sub>O: "X \<in> C\<^sub>O"
      and hC_eq_one: "C = C\<^sub>B \<or> C = C\<^sub>O"
      using hD44_BdJ\<^sub>N_polygon_split_at_B1P_endpoint[OF hpolygon]
      by (elim exE conjE)
    show ?thesis
    proof (rule disjE[OF hC_eq_one])
      assume hC_eq_B: "C = C\<^sub>B"
      have hBdJ_split_C\<^sub>F: "geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>O"
        using hBdJ_split hC_eq_B by (by100 simp)
      have hC_int_disj_C\<^sub>F:
        "geotop_arc_interior C {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
        using hC_int_disj hC_eq_B by (by100 simp)
      have hC_inter_C\<^sub>F: "C \<inter> C\<^sub>O = {P, X}"
        using hC_inter hC_eq_B by (by100 simp)
      have hC\<^sub>F_sub_BdJ: "C\<^sub>O \<subseteq> geotop_polyhedron BdJ\<^sub>N"
      proof
        fix y
        assume hy: "y \<in> C\<^sub>O"
        have "y \<in> C\<^sub>B \<union> C\<^sub>O"
          using hy by (by100 simp)
        thus "y \<in> geotop_polyhedron BdJ\<^sub>N"
          using hBdJ_split by (by100 simp)
      qed
      have hC\<^sub>F_sub_J\<^sub>N: "C\<^sub>O \<subseteq> J\<^sub>N"
        by (rule subset_trans[OF hC\<^sub>F_sub_BdJ hBdJ\<^sub>N_poly_sub_J\<^sub>N])
      have hC\<^sub>F_sub_FrN\<^sub>I: "C\<^sub>O \<subseteq> FrN\<^sub>I"
        by (rule subset_trans[OF hC\<^sub>F_sub_BdJ hBdJ\<^sub>N_poly_sub_FrN\<^sub>I])
      have hC\<^sub>F_A2_QS_disj: "C\<^sub>O \<inter> (A2 \<union> {Q, S}) = {}"
      proof -
        have "C\<^sub>O \<inter> (A2 \<union> {Q, S}) \<subseteq>
            geotop_polyhedron BdJ\<^sub>N \<inter> (A2 \<union> {Q, S})"
          using hC\<^sub>F_sub_BdJ by (by100 blast)
        thus ?thesis
          using hBdJ\<^sub>N_poly_A2_QS_disj by (by100 blast)
      qed
      have hC\<^sub>F_Ncut_disj: "C\<^sub>O \<inter> ?Ncut = {}"
      proof -
        have "C\<^sub>O \<inter> ?Ncut \<subseteq> geotop_polyhedron BdJ\<^sub>N \<inter> ?Ncut"
          using hC\<^sub>F_sub_BdJ by (by100 blast)
        thus ?thesis
          using hNcut_BdJ\<^sub>N_poly_disj by (by100 blast)
      qed
      show ?thesis
        apply (rule exI[where x=X])
        apply (rule exI[where x=C])
        apply (rule exI[where x=L])
        apply (rule exI[where x=C\<^sub>O])
        using hX_B1P hX_ne hC_bl hC_sub_B1P hC_sub_F1 hC_sub_J\<^sub>N
          hC_sub_FrN\<^sub>I hC_F\<^sub>2_disj hC_A2_QS_disj hC_Ncut_disj
          hP_C hX_C hC_end hC_int_connected hC_int_nonempty
          hL_complex hL_1dim hL_fin hL_poly_C hP_L hX_L
          hBdJ_split_C\<^sub>F hC\<^sub>O_bl hC\<^sub>O_end hC_int_disj_C\<^sub>F
          hC_inter_C\<^sub>F hP_C\<^sub>O hX_C\<^sub>O hC\<^sub>F_sub_J\<^sub>N
          hC\<^sub>F_sub_FrN\<^sub>I hC\<^sub>F_A2_QS_disj hC\<^sub>F_Ncut_disj
        by (intro conjI)
    next
      assume hC_eq_O: "C = C\<^sub>O"
      have hBdJ_split_C\<^sub>F: "geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>B"
        using hBdJ_split hC_eq_O by (by100 auto)
      have hC_int_disj_C\<^sub>F:
        "geotop_arc_interior C {P, X} \<inter>
          geotop_arc_interior C\<^sub>B {P, X} = {}"
        using hC_int_disj hC_eq_O by (by100 auto)
      have hC_inter_C\<^sub>F: "C \<inter> C\<^sub>B = {P, X}"
        using hC_inter hC_eq_O by (by100 auto)
      have hC\<^sub>F_sub_BdJ: "C\<^sub>B \<subseteq> geotop_polyhedron BdJ\<^sub>N"
      proof
        fix y
        assume hy: "y \<in> C\<^sub>B"
        have "y \<in> C\<^sub>B \<union> C\<^sub>O"
          using hy by (by100 simp)
        thus "y \<in> geotop_polyhedron BdJ\<^sub>N"
          using hBdJ_split by (by100 simp)
      qed
      have hC\<^sub>F_sub_J\<^sub>N: "C\<^sub>B \<subseteq> J\<^sub>N"
        by (rule subset_trans[OF hC\<^sub>F_sub_BdJ hBdJ\<^sub>N_poly_sub_J\<^sub>N])
      have hC\<^sub>F_sub_FrN\<^sub>I: "C\<^sub>B \<subseteq> FrN\<^sub>I"
        by (rule subset_trans[OF hC\<^sub>F_sub_BdJ hBdJ\<^sub>N_poly_sub_FrN\<^sub>I])
      have hC\<^sub>F_A2_QS_disj: "C\<^sub>B \<inter> (A2 \<union> {Q, S}) = {}"
      proof -
        have "C\<^sub>B \<inter> (A2 \<union> {Q, S}) \<subseteq>
            geotop_polyhedron BdJ\<^sub>N \<inter> (A2 \<union> {Q, S})"
          using hC\<^sub>F_sub_BdJ by (by100 blast)
        thus ?thesis
          using hBdJ\<^sub>N_poly_A2_QS_disj by (by100 blast)
      qed
      have hC\<^sub>F_Ncut_disj: "C\<^sub>B \<inter> ?Ncut = {}"
      proof -
        have "C\<^sub>B \<inter> ?Ncut \<subseteq> geotop_polyhedron BdJ\<^sub>N \<inter> ?Ncut"
          using hC\<^sub>F_sub_BdJ by (by100 blast)
        thus ?thesis
          using hNcut_BdJ\<^sub>N_poly_disj by (by100 blast)
      qed
      show ?thesis
        apply (rule exI[where x=X])
        apply (rule exI[where x=C])
        apply (rule exI[where x=L])
        apply (rule exI[where x=C\<^sub>B])
        using hX_B1P hX_ne hC_bl hC_sub_B1P hC_sub_F1 hC_sub_J\<^sub>N
          hC_sub_FrN\<^sub>I hC_F\<^sub>2_disj hC_A2_QS_disj hC_Ncut_disj
          hP_C hX_C hC_end hC_int_connected hC_int_nonempty
          hL_complex hL_1dim hL_fin hL_poly_C hP_L hX_L
          hBdJ_split_C\<^sub>F hC\<^sub>B_bl hC\<^sub>B_end hC_int_disj_C\<^sub>F
          hC_inter_C\<^sub>F hP_C\<^sub>B hX_C\<^sub>B hC\<^sub>F_sub_J\<^sub>N
          hC\<^sub>F_sub_FrN\<^sub>I hC\<^sub>F_A2_QS_disj hC\<^sub>F_Ncut_disj
        by (intro conjI)
    qed
  qed
  have hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}"
    (**
      Book split package for the regular-neighborhood frontier component:
      after the missing no-endpoint step proves the component polygonal,
      the frontier through \<open>P\<close> supplies the two broken-line arcs that Moise
      denotes by the boundary piece and the complementary piece. **)
  proof -
    assume hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    obtain X C L C\<^sub>B C\<^sub>O where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hBdJ_split: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O"
      and hC\<^sub>B_bl: "geotop_is_broken_line C\<^sub>B"
      and hC\<^sub>O_bl: "geotop_is_broken_line C\<^sub>O"
      and hC\<^sub>B_end: "geotop_arc_endpoints C\<^sub>B {P, X}"
      and hC\<^sub>O_end: "geotop_arc_endpoints C\<^sub>O {P, X}"
      and hC_int_disj:
        "geotop_arc_interior C\<^sub>B {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
      using hD44_BdJ\<^sub>N_polygon_split_at_B1P_endpoint[OF hpolygon]
      by (elim exE conjE)
    show ?thesis
      apply (rule exI[where x=X])
      apply (rule exI[where x=C\<^sub>B])
      apply (rule exI[where x=C\<^sub>O])
      using hX_B1P hX_ne hBdJ_split hC\<^sub>B_bl hC\<^sub>O_bl
        hC\<^sub>B_end hC\<^sub>O_end hC_int_disj
      apply (intro conjI)
      by (by100 blast)+
  qed
  have hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split_with_endpoint_members:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}
          \<and> P \<in> C\<^sub>B
          \<and> X \<in> C\<^sub>B
          \<and> P \<in> C\<^sub>O
          \<and> X \<in> C\<^sub>O"
    (**
      Endpoint-explicit form of the same Moise two-arc split.  The later
      lower-to-upper route bookkeeping needs the fact that both broken arcs
      really contain the two cut endpoints, not just the endpoint predicate. **)
  proof -
    assume hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    obtain X C\<^sub>B C\<^sub>O where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hBdJ_split: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O"
      and hC\<^sub>B_bl: "geotop_is_broken_line C\<^sub>B"
      and hC\<^sub>O_bl: "geotop_is_broken_line C\<^sub>O"
      and hC\<^sub>B_end: "geotop_arc_endpoints C\<^sub>B {P, X}"
      and hC\<^sub>O_end: "geotop_arc_endpoints C\<^sub>O {P, X}"
      and hC_int_disj:
        "geotop_arc_interior C\<^sub>B {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
      using hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split[OF hpolygon]
      by (elim exE conjE)
    have hP_C\<^sub>B: "P \<in> C\<^sub>B"
      using hC\<^sub>B_end unfolding geotop_arc_endpoints_def by (by100 blast)
    have hX_C\<^sub>B: "X \<in> C\<^sub>B"
      using hC\<^sub>B_end unfolding geotop_arc_endpoints_def by (by100 blast)
    have hP_C\<^sub>O: "P \<in> C\<^sub>O"
      using hC\<^sub>O_end unfolding geotop_arc_endpoints_def by (by100 blast)
    have hX_C\<^sub>O: "X \<in> C\<^sub>O"
      using hC\<^sub>O_end unfolding geotop_arc_endpoints_def by (by100 blast)
    show ?thesis
      apply (rule exI[where x=X])
      apply (rule exI[where x=C\<^sub>B])
      apply (rule exI[where x=C\<^sub>O])
      using hX_B1P hX_ne hBdJ_split hC\<^sub>B_bl hC\<^sub>O_bl hC\<^sub>B_end
        hC\<^sub>O_end hC_int_disj hP_C\<^sub>B hX_C\<^sub>B hP_C\<^sub>O hX_C\<^sub>O
      apply (intro conjI)
      by (by100 blast)+
  qed
  have hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split_with_endpoint_inter:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}
          \<and> C\<^sub>B \<inter> C\<^sub>O = {P, X}
          \<and> P \<in> C\<^sub>B
          \<and> X \<in> C\<^sub>B
          \<and> P \<in> C\<^sub>O
          \<and> X \<in> C\<^sub>O"
    (**
      Polygonal-frontier version of the endpoint-intersection package.  This
      keeps the "frontier is already a polygon" path and the later exact-two
      incidence path aligned: both expose the fact that Moise's two arcs meet
      exactly at \<open>P\<close> and the chosen boundary endpoint \<open>X\<close>.
    **)
  proof -
    assume hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    obtain X C\<^sub>B C\<^sub>O where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hBdJ_split: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O"
      and hC\<^sub>B_bl: "geotop_is_broken_line C\<^sub>B"
      and hC\<^sub>O_bl: "geotop_is_broken_line C\<^sub>O"
      and hC\<^sub>B_end: "geotop_arc_endpoints C\<^sub>B {P, X}"
      and hC\<^sub>O_end: "geotop_arc_endpoints C\<^sub>O {P, X}"
      and hC_int_disj:
        "geotop_arc_interior C\<^sub>B {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
      and hP_C\<^sub>B: "P \<in> C\<^sub>B"
      and hX_C\<^sub>B: "X \<in> C\<^sub>B"
      and hP_C\<^sub>O: "P \<in> C\<^sub>O"
      and hX_C\<^sub>O: "X \<in> C\<^sub>O"
      using hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split_with_endpoint_members[OF hpolygon]
      by (elim exE conjE)
    have hC_inter: "C\<^sub>B \<inter> C\<^sub>O = {P, X}"
      by (rule geotop_same_endpoint_arcs_inter_eq_prefix
          [OF hC\<^sub>B_end hC\<^sub>O_end hC_int_disj])
    show ?thesis
      apply (rule exI[where x=X])
      apply (rule exI[where x=C\<^sub>B])
      apply (rule exI[where x=C\<^sub>O])
      using hX_B1P hX_ne hBdJ_split hC\<^sub>B_bl hC\<^sub>O_bl hC\<^sub>B_end
        hC\<^sub>O_end hC_int_disj hC_inter hP_C\<^sub>B hX_C\<^sub>B hP_C\<^sub>O hX_C\<^sub>O
      apply (intro conjI)
      by (by100 blast)+
  qed
  have hD44_BdJ\<^sub>N_card_le2_no_endpoint_has_book_two_arc_split:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}"
    (**
      Exact graph-theoretic reduction for Moise's assertion that the frontier
      component is a 1-sphere: local valence at most two plus absence of a
      graph endpoint yields polygonality, hence the book two-arc split. **)
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hnoend:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_card_le2_no_endpoint[OF hle2 hnoend])
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split[OF hpolygon])
  qed
  have hD44_BdJ\<^sub>N_simple_closed_curve_has_book_two_arc_split:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}"
    (**
      Direct formal form of Moise's sentence "Then J is a 1-sphere" for the
      extracted frontier graph: a simple closed curve carrier is enough to
      recover the two broken-line arcs used by the book proof. **)
  proof -
    assume hSCC:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
        (geotop_polyhedron BdJ\<^sub>N)"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_simple_closed_curve[OF hSCC])
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split[OF hpolygon])
  qed
  have hD44_BdJ\<^sub>N_1sphere_has_book_two_arc_split:
      "geotop_is_n_sphere (geotop_polyhedron BdJ\<^sub>N)
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron BdJ\<^sub>N)) 1 \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}"
    (**
      Literal formal version of Moise's sentence "Then J is a 1-sphere":
      because \<open>BdJ\<^sub>N\<close> is already a finite complex, the 1-sphere carrier
      statement is exactly the missing input needed for polygonality and the
      book's two broken-line arcs. **)
  proof -
    assume hsphere:
      "geotop_is_n_sphere (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N)) 1"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      unfolding geotop_is_polygon_def
      using hBdJ\<^sub>N_complex hsphere by (intro exI[where x=BdJ\<^sub>N] conjI) (by100 simp)+
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split[OF hpolygon])
  qed
  have hD44_J\<^sub>N_1sphere_has_book_two_arc_split:
      "geotop_is_n_sphere J\<^sub>N
          (subspace_topology UNIV geotop_euclidean_topology J\<^sub>N) 1 \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}"
    (**
      Book statement bridge: Moise names the frontier component through \<open>P\<close>
      as \<open>J\<close> and proves it is a 1-sphere.  Since the preceding finite-complex
      analysis has already identified that component with \<open>geotop_polyhedron
      BdJ\<^sub>N\<close>, this is the literal route from the book's 1-sphere sentence to
      the two broken-line arcs used below. **)
  proof -
    assume hsphere:
      "geotop_is_n_sphere J\<^sub>N
        (subspace_topology UNIV geotop_euclidean_topology J\<^sub>N) 1"
    have hsphere_BdJ:
      "geotop_is_n_sphere (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N)) 1"
      using hsphere hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_1sphere_has_book_two_arc_split[OF hsphere_BdJ])
  qed
  have hD44_BdJ\<^sub>N_card_le2_no_endpoint_imp_J\<^sub>N_1sphere:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
        geotop_is_n_sphere J\<^sub>N
          (subspace_topology UNIV geotop_euclidean_topology J\<^sub>N) 1"
    (**
      Precise remaining regular-neighborhood graph target.  Once the frontier
      component graph has valence at most two and no endpoints, the already
      proved finite-graph classifier makes its carrier polygonal; the equality
      \<open>J\<^sub>N = geotop_polyhedron BdJ\<^sub>N\<close> then turns that into Moise's
      "then \<open>J\<close> is a 1-sphere" statement for the actual frontier component. **)
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hnoend:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_card_le2_no_endpoint[OF hle2 hnoend])
    have hsphere_BdJ:
      "geotop_is_n_sphere (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N)) 1"
      using hpolygon unfolding geotop_is_polygon_def by (by100 blast)
    show ?thesis
      using hsphere_BdJ hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
  qed
  have hD44_BdJ\<^sub>N_exact_two_incident_edges_imp_J\<^sub>N_1sphere:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))) \<Longrightarrow>
        geotop_is_n_sphere J\<^sub>N
          (subspace_topology UNIV geotop_euclidean_topology J\<^sub>N) 1"
    (**
      Link/local-star version of the same book target.  Existing link
      component facts naturally produce an exact-two incident-edge witness at
      every vertex.  This bridge records that such a local 1-manifold statement
      is strong enough to recover Moise's frontier-component 1-sphere. **)
  proof -
    assume htwo:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))"
    have hdegree:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
    proof (intro allI impI)
      fix w
      assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
      have htwo_w:
        "\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2)"
      proof -
        have hspec:
          "{w} \<in> BdJ\<^sub>N \<longrightarrow>
            (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
              geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
              \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
              \<and> e\<^sub>1 \<noteq> e\<^sub>2
              \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
                  \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))"
          using htwo by (rule spec)
        show ?thesis
          using hspec hwBdJ by (by100 simp)
      qed
      obtain e\<^sub>1 e\<^sub>2 where he\<^sub>1BdJ: "e\<^sub>1 \<in> BdJ\<^sub>N"
        and he\<^sub>2BdJ: "e\<^sub>2 \<in> BdJ\<^sub>N"
        and he\<^sub>1edge: "geotop_is_edge e\<^sub>1"
        and hwe\<^sub>1: "w \<in> e\<^sub>1"
        and he\<^sub>2edge: "geotop_is_edge e\<^sub>2"
        and hwe\<^sub>2: "w \<in> e\<^sub>2"
        and he12: "e\<^sub>1 \<noteq> e\<^sub>2"
        and hexhaust:
          "\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
            \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2"
        using htwo_w by (elim bexE exE conjE)
      let ?E = "{e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e}"
      have hE_eq: "?E = {e\<^sub>1, e\<^sub>2}"
      proof
        show "?E \<subseteq> {e\<^sub>1, e\<^sub>2}"
        proof
          fix e
          assume heE: "e \<in> ?E"
          have heprops: "e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e"
            using heE by (by100 simp)
          have hexhaust_e:
            "e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2"
            using hexhaust by (rule spec)
          have he_cases: "e = e\<^sub>1 \<or> e = e\<^sub>2"
            using hexhaust_e heprops by (by100 simp)
          show "e \<in> {e\<^sub>1, e\<^sub>2}"
            using he_cases by (by100 simp)
        qed
        show "{e\<^sub>1, e\<^sub>2} \<subseteq> ?E"
        proof
          fix e
          assume he_pair: "e \<in> {e\<^sub>1, e\<^sub>2}"
          have he_cases: "e = e\<^sub>1 \<or> e = e\<^sub>2"
            using he_pair by (by100 simp)
          show "e \<in> ?E"
          proof (rule disjE[OF he_cases])
            assume he: "e = e\<^sub>1"
            show "e \<in> ?E"
              using he he\<^sub>1BdJ he\<^sub>1edge hwe\<^sub>1 by (by100 simp)
          next
            assume he: "e = e\<^sub>2"
            show "e \<in> ?E"
              using he he\<^sub>2BdJ he\<^sub>2edge hwe\<^sub>2 by (by100 simp)
          qed
        qed
      qed
      show "card ?E = 2"
        using hE_eq he12 by (by100 simp)
    qed
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_degree_two[OF hdegree])
    have hsphere_BdJ:
      "geotop_is_n_sphere (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N)) 1"
      using hpolygon unfolding geotop_is_polygon_def by (by100 blast)
    show ?thesis
      using hsphere_BdJ hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
  qed
  have hD44_BdJ\<^sub>N_exact_two_boundary_subarc_complement_split:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))) \<Longrightarrow>
        \<exists>X C L C\<^sub>F. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_is_broken_line C
          \<and> C \<subseteq> ?B1P
          \<and> C \<subseteq> F\<^sub>1
          \<and> C \<subseteq> J\<^sub>N
          \<and> C \<subseteq> FrN\<^sub>I
          \<and> C \<inter> F\<^sub>2 = {}
          \<and> C \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C \<inter> ?Ncut = {}
          \<and> P \<in> C
          \<and> X \<in> C
          \<and> geotop_arc_endpoints C {P, X}
          \<and> connected (geotop_arc_interior C {P, X})
          \<and> geotop_arc_interior C {P, X} \<noteq> {}
          \<and> geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> {P} \<in> L
          \<and> {X} \<in> L
          \<and> geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>F
          \<and> geotop_is_broken_line C\<^sub>F
          \<and> geotop_arc_endpoints C\<^sub>F {P, X}
          \<and> geotop_arc_interior C {P, X} \<inter>
              geotop_arc_interior C\<^sub>F {P, X} = {}
          \<and> C \<inter> C\<^sub>F = {P, X}
          \<and> P \<in> C\<^sub>F
          \<and> X \<in> C\<^sub>F
          \<and> C\<^sub>F \<subseteq> J\<^sub>N
          \<and> C\<^sub>F \<subseteq> FrN\<^sub>I
          \<and> C\<^sub>F \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C\<^sub>F \<inter> ?Ncut = {}"
    (**
      Exact-two incidence form of the oriented Moise frontier split.  This is
      the bridge from the local regular-neighborhood graph statement to the
      already oriented boundary subarc plus complementary frontier arc package.
    **)
  proof -
    assume htwo:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))"
    have hsphere:
        "geotop_is_n_sphere J\<^sub>N
          (subspace_topology UNIV geotop_euclidean_topology J\<^sub>N) 1"
      by (rule hD44_BdJ\<^sub>N_exact_two_incident_edges_imp_J\<^sub>N_1sphere[OF htwo])
    have hsphere_BdJ:
      "geotop_is_n_sphere (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N)) 1"
      using hsphere hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      unfolding geotop_is_polygon_def
    proof (intro exI[where x=BdJ\<^sub>N] conjI)
      show "geotop_is_complex BdJ\<^sub>N"
        by (rule hBdJ\<^sub>N_complex)
      show "geotop_polyhedron BdJ\<^sub>N = geotop_polyhedron BdJ\<^sub>N"
        by (by100 simp)
      show "geotop_is_n_sphere (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N)) 1"
        by (rule hsphere_BdJ)
    qed
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_polygon_boundary_subarc_complement_split[OF hpolygon])
  qed
  have hD44_BdJ\<^sub>N_degree_two_exact_two_incident_edges:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2) \<Longrightarrow>
      (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2)))"
    (**
      Degree-two form of the local regular-neighborhood incidence statement.
      Several earlier graph packages naturally produce cardinality two at each
      frontier vertex; the complementary frontier split wants the explicit two
      incident edges and their exhaustion property. **)
  proof (intro allI impI)
    assume hdegree:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
    fix w
    assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
    obtain e\<^sub>1 e\<^sub>2 where he\<^sub>1BdJ: "e\<^sub>1 \<in> BdJ\<^sub>N"
      and he\<^sub>2BdJ: "e\<^sub>2 \<in> BdJ\<^sub>N"
      and he\<^sub>1edge: "geotop_is_edge e\<^sub>1"
      and he\<^sub>2edge: "geotop_is_edge e\<^sub>2"
      and hwe\<^sub>1: "w \<in> e\<^sub>1"
      and hwe\<^sub>2: "w \<in> e\<^sub>2"
      and he12: "e\<^sub>1 \<noteq> e\<^sub>2"
      and hE_eq:
        "{e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = {e\<^sub>1, e\<^sub>2}"
      using geotop_degree_two_vertex_two_distinct_incident_edges_prefix
        [OF hdegree hwBdJ]
      by (elim exE conjE)
    have hexhaust:
        "\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
          \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2"
    proof (intro allI impI)
      fix e
      assume he: "e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e"
      have "e \<in> {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e}"
        using he by (by100 simp)
      hence "e \<in> {e\<^sub>1, e\<^sub>2}"
        using hE_eq by (by100 simp)
      thus "e = e\<^sub>1 \<or> e = e\<^sub>2"
        by (by100 simp)
    qed
    show "\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
        geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
        \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
        \<and> e\<^sub>1 \<noteq> e\<^sub>2
        \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
            \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2)"
      using he\<^sub>1BdJ he\<^sub>2BdJ he\<^sub>1edge he\<^sub>2edge hwe\<^sub>1 hwe\<^sub>2 he12 hexhaust
      by (by100 blast)
  qed
  have hD44_BdJ\<^sub>N_degree_two_boundary_subarc_complement_split:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2) \<Longrightarrow>
        \<exists>X C L C\<^sub>F. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_is_broken_line C
          \<and> C \<subseteq> ?B1P
          \<and> C \<subseteq> F\<^sub>1
          \<and> C \<subseteq> J\<^sub>N
          \<and> C \<subseteq> FrN\<^sub>I
          \<and> C \<inter> F\<^sub>2 = {}
          \<and> C \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C \<inter> ?Ncut = {}
          \<and> P \<in> C
          \<and> X \<in> C
          \<and> geotop_arc_endpoints C {P, X}
          \<and> connected (geotop_arc_interior C {P, X})
          \<and> geotop_arc_interior C {P, X} \<noteq> {}
          \<and> geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> {P} \<in> L
          \<and> {X} \<in> L
          \<and> geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>F
          \<and> geotop_is_broken_line C\<^sub>F
          \<and> geotop_arc_endpoints C\<^sub>F {P, X}
          \<and> geotop_arc_interior C {P, X} \<inter>
              geotop_arc_interior C\<^sub>F {P, X} = {}
          \<and> C \<inter> C\<^sub>F = {P, X}
          \<and> P \<in> C\<^sub>F
          \<and> X \<in> C\<^sub>F
          \<and> C\<^sub>F \<subseteq> J\<^sub>N
          \<and> C\<^sub>F \<subseteq> FrN\<^sub>I
          \<and> C\<^sub>F \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C\<^sub>F \<inter> ?Ncut = {}"
    (**
      Same Moise frontier split, but keyed by the degree-two statement that the
      local frontier graph analysis is expected to establish. **)
  proof -
    assume hdegree:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
    have htwo:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))"
      by (rule hD44_BdJ\<^sub>N_degree_two_exact_two_incident_edges[OF hdegree])
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_exact_two_boundary_subarc_complement_split[OF htwo])
  qed
  have hD44_BdJ\<^sub>N_card_bounds_boundary_subarc_complement_split:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        (\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2) \<Longrightarrow>
        \<exists>X C L C\<^sub>F. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_is_broken_line C
          \<and> C \<subseteq> ?B1P
          \<and> C \<subseteq> F\<^sub>1
          \<and> C \<subseteq> J\<^sub>N
          \<and> C \<subseteq> FrN\<^sub>I
          \<and> C \<inter> F\<^sub>2 = {}
          \<and> C \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C \<inter> ?Ncut = {}
          \<and> P \<in> C
          \<and> X \<in> C
          \<and> geotop_arc_endpoints C {P, X}
          \<and> connected (geotop_arc_interior C {P, X})
          \<and> geotop_arc_interior C {P, X} \<noteq> {}
          \<and> geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> {P} \<in> L
          \<and> {X} \<in> L
          \<and> geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>F
          \<and> geotop_is_broken_line C\<^sub>F
          \<and> geotop_arc_endpoints C\<^sub>F {P, X}
          \<and> geotop_arc_interior C {P, X} \<inter>
              geotop_arc_interior C\<^sub>F {P, X} = {}
          \<and> C \<inter> C\<^sub>F = {P, X}
          \<and> P \<in> C\<^sub>F
          \<and> X \<in> C\<^sub>F
          \<and> C\<^sub>F \<subseteq> J\<^sub>N
          \<and> C\<^sub>F \<subseteq> FrN\<^sub>I
          \<and> C\<^sub>F \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C\<^sub>F \<inter> ?Ncut = {}"
    (**
      Book-aligned incidence entry point for the frontier split.  The next
      D44 graph task can now target the literal local regular-neighborhood
      bounds at each vertex of the frontier component: at most two boundary
      edges and at least two boundary edges.  Those bounds give degree two,
      and the already-proved degree-two package gives Moise's boundary arc
      and complementary frontier arc \<open>C\<^sub>F\<close>. **)
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hge2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
    have hdegree:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule hBdJ\<^sub>N_vertex_degree_two_from_card_bounds[OF hle2 hge2])
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_degree_two_boundary_subarc_complement_split
          [OF hdegree])
  qed
  have hD44_BdJ\<^sub>N_card_le2_no_endpoint_boundary_subarc_complement_split:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
        \<exists>X C L C\<^sub>F. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_is_broken_line C
          \<and> C \<subseteq> ?B1P
          \<and> C \<subseteq> F\<^sub>1
          \<and> C \<subseteq> J\<^sub>N
          \<and> C \<subseteq> FrN\<^sub>I
          \<and> C \<inter> F\<^sub>2 = {}
          \<and> C \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C \<inter> ?Ncut = {}
          \<and> P \<in> C
          \<and> X \<in> C
          \<and> geotop_arc_endpoints C {P, X}
          \<and> connected (geotop_arc_interior C {P, X})
          \<and> geotop_arc_interior C {P, X} \<noteq> {}
          \<and> geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> {P} \<in> L
          \<and> {X} \<in> L
          \<and> geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>F
          \<and> geotop_is_broken_line C\<^sub>F
          \<and> geotop_arc_endpoints C\<^sub>F {P, X}
          \<and> geotop_arc_interior C {P, X} \<inter>
              geotop_arc_interior C\<^sub>F {P, X} = {}
          \<and> C \<inter> C\<^sub>F = {P, X}
          \<and> P \<in> C\<^sub>F
          \<and> X \<in> C\<^sub>F
          \<and> C\<^sub>F \<subseteq> J\<^sub>N
          \<and> C\<^sub>F \<subseteq> FrN\<^sub>I
          \<and> C\<^sub>F \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C\<^sub>F \<inter> ?Ncut = {}"
    (**
      Older frontier graph target, connected to the stronger C/C_F output:
      valence at most two plus no endpoints makes every vertex degree two, and
      the degree-two package supplies the book's selected boundary arc and
      complementary frontier arc. **)
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hnoend:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
    have hdegree:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule hBdJ\<^sub>N_vertex_degree_two_from_card_le2_no_endpoint
          [OF hle2 hnoend])
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_degree_two_boundary_subarc_complement_split
          [OF hdegree])
  qed
  have hD44_BdJ\<^sub>N_simple_closed_curve_boundary_subarc_complement_split:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>X C L C\<^sub>F. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_is_broken_line C
          \<and> C \<subseteq> ?B1P
          \<and> C \<subseteq> F\<^sub>1
          \<and> C \<subseteq> J\<^sub>N
          \<and> C \<subseteq> FrN\<^sub>I
          \<and> C \<inter> F\<^sub>2 = {}
          \<and> C \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C \<inter> ?Ncut = {}
          \<and> P \<in> C
          \<and> X \<in> C
          \<and> geotop_arc_endpoints C {P, X}
          \<and> connected (geotop_arc_interior C {P, X})
          \<and> geotop_arc_interior C {P, X} \<noteq> {}
          \<and> geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> {P} \<in> L
          \<and> {X} \<in> L
          \<and> geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>F
          \<and> geotop_is_broken_line C\<^sub>F
          \<and> geotop_arc_endpoints C\<^sub>F {P, X}
          \<and> geotop_arc_interior C {P, X} \<inter>
              geotop_arc_interior C\<^sub>F {P, X} = {}
          \<and> C \<inter> C\<^sub>F = {P, X}
          \<and> P \<in> C\<^sub>F
          \<and> X \<in> C\<^sub>F
          \<and> C\<^sub>F \<subseteq> J\<^sub>N
          \<and> C\<^sub>F \<subseteq> FrN\<^sub>I
          \<and> C\<^sub>F \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C\<^sub>F \<inter> ?Ncut = {}"
    (**
      Direct simple-closed-curve entry point for the same Moise frontier split.
      If the frontier component is proved as a simple closed curve first, the
      existing polygon conversion immediately gives the C/C_F package. **)
  proof -
    assume hSCC:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
        (geotop_polyhedron BdJ\<^sub>N)"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_simple_closed_curve[OF hSCC])
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_polygon_boundary_subarc_complement_split
          [OF hpolygon])
  qed
  have hD44_BdJ\<^sub>N_exact_two_has_book_two_arc_split:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}"
    (**
      Direct book-route package from the local regular-neighborhood incidence
      statement to Moise's two frontier arcs.  The remaining geometric work can
      now target exact-two boundary incidence and then immediately recover the
      split of the frontier component through \<open>P\<close>. **)
  proof -
    assume htwo:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))"
    have hsphere:
        "geotop_is_n_sphere J\<^sub>N
          (subspace_topology UNIV geotop_euclidean_topology J\<^sub>N) 1"
      by (rule hD44_BdJ\<^sub>N_exact_two_incident_edges_imp_J\<^sub>N_1sphere[OF htwo])
    show ?thesis
      by (rule hD44_J\<^sub>N_1sphere_has_book_two_arc_split[OF hsphere])
  qed
  have hD44_BdJ\<^sub>N_exact_two_has_book_two_arc_split_with_endpoint_members:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}
          \<and> P \<in> C\<^sub>B
          \<and> X \<in> C\<^sub>B
          \<and> P \<in> C\<^sub>O
          \<and> X \<in> C\<^sub>O"
    (**
      Endpoint-explicit exact-two incidence package.  This is the expected
      formal output of the local regular-neighborhood graph step: exact two
      incident boundary edges at every frontier vertex give the two Moise arcs,
      with their shared endpoints available as ordinary membership facts. **)
  proof -
    assume htwo:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))"
    obtain X C\<^sub>B C\<^sub>O where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hBdJ_split: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O"
      and hC\<^sub>B_bl: "geotop_is_broken_line C\<^sub>B"
      and hC\<^sub>O_bl: "geotop_is_broken_line C\<^sub>O"
      and hC\<^sub>B_end: "geotop_arc_endpoints C\<^sub>B {P, X}"
      and hC\<^sub>O_end: "geotop_arc_endpoints C\<^sub>O {P, X}"
      and hC_int_disj:
        "geotop_arc_interior C\<^sub>B {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
      using hD44_BdJ\<^sub>N_exact_two_has_book_two_arc_split[OF htwo]
      by (elim exE conjE)
    have hP_C\<^sub>B: "P \<in> C\<^sub>B"
      using hC\<^sub>B_end unfolding geotop_arc_endpoints_def by (by100 blast)
    have hX_C\<^sub>B: "X \<in> C\<^sub>B"
      using hC\<^sub>B_end unfolding geotop_arc_endpoints_def by (by100 blast)
    have hP_C\<^sub>O: "P \<in> C\<^sub>O"
      using hC\<^sub>O_end unfolding geotop_arc_endpoints_def by (by100 blast)
    have hX_C\<^sub>O: "X \<in> C\<^sub>O"
      using hC\<^sub>O_end unfolding geotop_arc_endpoints_def by (by100 blast)
    show ?thesis
      apply (rule exI[where x=X])
      apply (rule exI[where x=C\<^sub>B])
      apply (rule exI[where x=C\<^sub>O])
      using hX_B1P hX_ne hBdJ_split hC\<^sub>B_bl hC\<^sub>O_bl hC\<^sub>B_end
        hC\<^sub>O_end hC_int_disj hP_C\<^sub>B hX_C\<^sub>B hP_C\<^sub>O hX_C\<^sub>O
      apply (intro conjI)
      by (by100 blast)+
  qed
  have hD44_BdJ\<^sub>N_exact_two_has_book_two_arc_split_with_endpoint_inter:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}
          \<and> C\<^sub>B \<inter> C\<^sub>O = {P, X}
          \<and> P \<in> C\<^sub>B
          \<and> X \<in> C\<^sub>B
          \<and> P \<in> C\<^sub>O
          \<and> X \<in> C\<^sub>O"
    (**
      Endpoint-intersection form of the exact-two frontier split.  Moise's
      later "other arc" choice uses that the two arcs through \<open>P\<close> and \<open>X\<close>
      meet only at their endpoints, so record that consequence next to the
      endpoint-explicit split rather than reproving it at each orientation use.
    **)
  proof -
    assume htwo:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))"
    obtain X C\<^sub>B C\<^sub>O where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hBdJ_split: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O"
      and hC\<^sub>B_bl: "geotop_is_broken_line C\<^sub>B"
      and hC\<^sub>O_bl: "geotop_is_broken_line C\<^sub>O"
      and hC\<^sub>B_end: "geotop_arc_endpoints C\<^sub>B {P, X}"
      and hC\<^sub>O_end: "geotop_arc_endpoints C\<^sub>O {P, X}"
      and hC_int_disj:
        "geotop_arc_interior C\<^sub>B {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
      and hP_C\<^sub>B: "P \<in> C\<^sub>B"
      and hX_C\<^sub>B: "X \<in> C\<^sub>B"
      and hP_C\<^sub>O: "P \<in> C\<^sub>O"
      and hX_C\<^sub>O: "X \<in> C\<^sub>O"
      using hD44_BdJ\<^sub>N_exact_two_has_book_two_arc_split_with_endpoint_members[OF htwo]
      by (elim exE conjE)
    have hC_inter: "C\<^sub>B \<inter> C\<^sub>O = {P, X}"
      by (rule geotop_same_endpoint_arcs_inter_eq_prefix
          [OF hC\<^sub>B_end hC\<^sub>O_end hC_int_disj])
    show ?thesis
      apply (rule exI[where x=X])
      apply (rule exI[where x=C\<^sub>B])
      apply (rule exI[where x=C\<^sub>O])
      using hX_B1P hX_ne hBdJ_split hC\<^sub>B_bl hC\<^sub>O_bl hC\<^sub>B_end
        hC\<^sub>O_end hC_int_disj hC_inter hP_C\<^sub>B hX_C\<^sub>B hP_C\<^sub>O hX_C\<^sub>O
      apply (intro conjI)
      by (by100 blast)+
  qed
  have hD44_B1P_F\<^sub>2_setdist_pos: "0 < setdist ?B1P F\<^sub>2"
  proof -
    have hsd_iff:
        "(0 < setdist ?B1P F\<^sub>2) =
          (?B1P \<noteq> {} \<and> F\<^sub>2 \<noteq> {} \<and> ?B1P \<inter> F\<^sub>2 = {})"
      by (rule setdist_gt_0_compact_closed
          [OF hD44_B1P_compact hD44_F\<^sub>2_closed])
    show ?thesis
      using hsd_iff hD44_P_B1P hD44_F\<^sub>2_nonempty hD44_B1P_F\<^sub>2_disj
      by (by100 blast)
  qed
  have hD44_B1P_inter_J: "?B1P \<inter> J = ?B1P"
    using hD44_B1P_sub_B\<^sub>1 by (by100 blast)
  have hD44_A2_QS_closed: "closed (A2 \<union> {Q, S})"
    using hA2_closed by (by100 simp)
  have hD44_A2_QS_nonempty: "A2 \<union> {Q, S} \<noteq> {}"
    by (by100 blast)
  have hD44_B1P_forbidden_setdist_pos:
      "0 < setdist ?B1P (A2 \<union> {Q, S})"
  proof -
    have hsd_iff:
        "(0 < setdist ?B1P (A2 \<union> {Q, S})) =
          (?B1P \<noteq> {} \<and> A2 \<union> {Q, S} \<noteq> {}
            \<and> ?B1P \<inter> (A2 \<union> {Q, S}) = {})"
      by (rule setdist_gt_0_compact_closed
          [OF hD44_B1P_compact hD44_A2_QS_closed])
    show ?thesis
      using hsd_iff hD44_P_B1P hD44_A2_QS_nonempty hD44_B1P_A2_QS_disj
      by (by100 blast)
  qed
  have hD44_same_component_in_Ncut_suffices:
      "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<Longrightarrow> \<exists>B. geotop_is_broken_line B
          \<and> B \<subseteq> ?Ncut
          \<and> Q1 \<in> B
          \<and> S1 \<in> B"
  proof -
    assume hS1_comp:
      "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    show ?thesis
      by (rule geotop_open_component_broken_line_between_prefix
          [OF hNcut_open hQ1_Ncut hS1_comp])
  qed
  have hD44_connected_route_component_suffices:
      "\<And>W. W \<subseteq> ?Ncut \<Longrightarrow> Q1 \<in> W \<Longrightarrow> S1 \<in> W \<Longrightarrow>
        top1_connected_on W
          (subspace_topology UNIV geotop_euclidean_topology W) \<Longrightarrow>
        S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    (**
      Pure component bookkeeping for Moise's frontier route: once the
      regular-neighborhood boundary analysis supplies a connected witness in
      \<open>I - (N \<union> A2)\<close> through the two local access endpoints, the endpoints are
      in the same ambient component. **)
    by (rule geotop_connected_witness_component_at_intro_prefix)
  have hD44_broken_line_route_component_suffices:
      "\<exists>B. geotop_is_broken_line B
        \<and> B \<subseteq> ?Ncut
        \<and> Q1 \<in> B
        \<and> S1 \<in> B
        \<Longrightarrow> S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut Q1"
    (**
      Direct Moise-form reduction: the remaining frontier analysis may now
      target exactly the book's broken line \<open>B\<close> in
      \<open>I - (N \<union> A2)\<close>.  Once such a broken line is constructed, connectedness
      of broken lines supplies the component relation. **)
  proof -
    assume hB_ex:
      "\<exists>B. geotop_is_broken_line B
        \<and> B \<subseteq> ?Ncut
        \<and> Q1 \<in> B
        \<and> S1 \<in> B"
    obtain B where hB_bl: "geotop_is_broken_line B"
      and hB_sub: "B \<subseteq> ?Ncut"
      and hQ1_B: "Q1 \<in> B"
      and hS1_B: "S1 \<in> B"
      using hB_ex by (elim exE conjE)
    have hB_conn:
        "top1_connected_on B
          (subspace_topology UNIV geotop_euclidean_topology B)"
      by (rule geotop_broken_line_connected_on_prefix[OF hB_bl])
    show "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
        ?Ncut Q1"
      by (rule hD44_connected_route_component_suffices
          [OF hB_sub hQ1_B hS1_B hB_conn])
  qed
  have hD44_Q1_Ncut_component_package:
      "\<exists>C. C = geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut Q1
        \<and> C \<subseteq> ?Ncut
        \<and> Q1 \<in> C
        \<and> C \<in> geotop_euclidean_topology
        \<and> top1_connected_on C
            (subspace_topology UNIV geotop_euclidean_topology C)"
    (**
      Names the outside-carrier component that Moise's lower-to-upper
      frontier subarc must enter.  The final book step is now precisely to
      show that the access point near \<open>S\<close> lies in this open connected
      component of \<open>I - (N \<union> A2)\<close>. **)
  proof -
    let ?C = "geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    have hC_open: "?C \<in> geotop_euclidean_topology"
      by (rule geotop_component_at_open_in_euclidean[OF hNcut_open hQ1_Ncut])
    have hC_eq: "?C = connected_component_set ?Ncut Q1"
      by (rule geotop_component_at_UNIV_eq_connected_component_set)
    have hC_sub: "?C \<subseteq> ?Ncut"
      using hC_eq connected_component_subset by (by100 simp)
    have hQ1_C: "Q1 \<in> ?C"
      using hC_eq hQ1_Ncut connected_component_refl by (by100 simp)
    have hC_conn_HOL: "connected ?C"
      using hC_eq connected_connected_component by (by100 simp)
    have hC_conn:
        "top1_connected_on ?C
          (subspace_topology UNIV geotop_euclidean_topology ?C)"
      using hC_conn_HOL top1_connected_on_geotop_iff_connected by (by100 blast)
    show ?thesis
    proof (rule exI[where x="?C"], intro conjI)
      show "?C = geotop_component_at UNIV geotop_euclidean_topology
          ?Ncut Q1"
        by (by100 simp)
      show "?C \<subseteq> ?Ncut" by (rule hC_sub)
      show "Q1 \<in> ?C" by (rule hQ1_C)
      show "?C \<in> geotop_euclidean_topology" by (rule hC_open)
      show "top1_connected_on ?C
          (subspace_topology UNIV geotop_euclidean_topology ?C)"
        by (rule hC_conn)
    qed
  qed
  have hD44_same_component_gives_closed_corridor:
      "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<Longrightarrow> \<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Q1 \<in> closure Z
          \<and> S1 \<in> closure Z"
    (**
      Converts Moise's final same-component statement into the closed-corridor
      form used by the collar machinery below.  The corridor is simply the
      \<open>Q1\<close>-component of \<open>I - (N \<union> A2)\<close>; once \<open>S1\<close> lies in it, both access
      points lie in its ordinary closure. **)
    by (rule geotop_component_member_gives_closed_corridor_prefix)
  have hD44_Ncut_open_split_if_not_same_component:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<Longrightarrow> ?Ncut =
          geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1 \<union>
          (?Ncut - geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1)
        \<and> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1 \<inter>
          (?Ncut - geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1) = {}
        \<and> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
          \<in> geotop_euclidean_topology
        \<and> ?Ncut - geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
          \<in> geotop_euclidean_topology
        \<and> Q1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<and> S1 \<in> ?Ncut -
          geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    (**
      Contradiction setup for the remaining Moise step.  If the lower-to-upper
      frontier route did not put \<open>S1\<close> in the \<open>Q1\<close> outside-carrier component,
      the open set \<open>I - (N \<union> A2)\<close> would split into the \<open>Q1\<close> component and its
      complementary open side containing \<open>S1\<close>.  The unfinished book argument
      must rule out exactly this split using the frontier component through
      \<open>P\<close>. **)
  proof -
    assume hnot:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    let ?CQ = "geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    let ?CS = "geotop_component_at UNIV geotop_euclidean_topology ?Ncut S1"
    have hTU: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
      by (metis geotop_euclidean_topology_eq_open_sets
          top1_open_sets_is_topology_on_UNIV)
    have hS1_sing_conn:
        "top1_connected_on {S1}
          (subspace_topology UNIV geotop_euclidean_topology {S1})"
      by (rule top1_connected_on_singleton[OF hTU], simp)
    have hS1_CS: "S1 \<in> ?CS"
      by (rule geotop_self_in_component_at[OF hS1_Ncut hS1_sing_conn])
    have hcomp_neq: "?CQ \<noteq> ?CS"
    proof
      assume heq: "?CQ = ?CS"
      have "S1 \<in> ?CQ"
        using heq hS1_CS by (by100 simp)
      thus False
        using hnot by (by100 blast)
    qed
    show ?thesis
      by (rule geotop_open_component_complement_split_prefix
          [OF hNcut_open hQ1_Ncut hS1_Ncut hcomp_neq])
  qed
  have hD44_Ncut_open_split_access_balls_if_not_same_component:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<Longrightarrow> \<exists>\<epsilon>\<^sub>Q>0. \<exists>\<epsilon>\<^sub>S>0.
          ball Q1 \<epsilon>\<^sub>Q \<subseteq>
            geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
          \<and> ball S1 \<epsilon>\<^sub>S \<subseteq>
            ?Ncut - geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    (**
      Local-collar version of the contradiction split.  If \<open>Q1\<close> and \<open>S1\<close>
      were on different outside-carrier components, then the two sides of the
      split would contain genuine Euclidean balls around the access points.
      These are the open collars that the final frontier subarc must connect
      through Moise's lower-to-upper construction. **)
  proof -
    assume hnot:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    let ?CQ = "geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    let ?W = "?Ncut - ?CQ"
    have hsplit:
        "?Ncut = ?CQ \<union> ?W
        \<and> ?CQ \<inter> ?W = {}
        \<and> ?CQ \<in> geotop_euclidean_topology
        \<and> ?W \<in> geotop_euclidean_topology
        \<and> Q1 \<in> ?CQ
        \<and> S1 \<in> ?W"
      by (rule hD44_Ncut_open_split_if_not_same_component[OF hnot])
    have hCQ_open_top: "?CQ \<in> geotop_euclidean_topology"
      using hsplit by (by100 blast)
    have hW_open_top: "?W \<in> geotop_euclidean_topology"
      using hsplit by (by100 blast)
    have hQ1_CQ: "Q1 \<in> ?CQ"
      using hsplit by (by100 blast)
    have hS1_W: "S1 \<in> ?W"
      using hsplit by (by100 blast)
    have hCQ_open_HOL: "open ?CQ"
      by (metis hCQ_open_top geotop_euclidean_topology_eq_open_sets
          mem_Collect_eq top1_open_sets_def)
    have hW_open_HOL: "open ?W"
      by (metis hW_open_top geotop_euclidean_topology_eq_open_sets
          mem_Collect_eq top1_open_sets_def)
    have hQ_ball_ex: "\<exists>\<epsilon>>0. ball Q1 \<epsilon> \<subseteq> ?CQ"
      using hCQ_open_HOL hQ1_CQ unfolding open_contains_ball by (by100 simp)
    have hS_ball_ex: "\<exists>\<epsilon>>0. ball S1 \<epsilon> \<subseteq> ?W"
      using hW_open_HOL hS1_W unfolding open_contains_ball by (by100 simp)
    obtain \<epsilon>\<^sub>Q where h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
      and hball_Q1_CQ: "ball Q1 \<epsilon>\<^sub>Q \<subseteq> ?CQ"
      using hQ_ball_ex by (elim exE conjE)
    obtain \<epsilon>\<^sub>S where h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
      and hball_S1_W: "ball S1 \<epsilon>\<^sub>S \<subseteq> ?W"
      using hS_ball_ex by (elim exE conjE)
    show ?thesis
    proof (rule exI[where x=\<epsilon>\<^sub>Q], intro conjI)
      show "0 < \<epsilon>\<^sub>Q" by (rule h\<epsilon>\<^sub>Q_pos)
      show "\<exists>\<epsilon>\<^sub>S>0.
          ball Q1 \<epsilon>\<^sub>Q \<subseteq> ?CQ \<and> ball S1 \<epsilon>\<^sub>S \<subseteq> ?W"
      proof (rule exI[where x=\<epsilon>\<^sub>S], intro conjI)
        show "0 < \<epsilon>\<^sub>S" by (rule h\<epsilon>\<^sub>S_pos)
        show "ball Q1 \<epsilon>\<^sub>Q \<subseteq> ?CQ" by (rule hball_Q1_CQ)
        show "ball S1 \<epsilon>\<^sub>S \<subseteq> ?W" by (rule hball_S1_W)
      qed
    qed
  qed
  have hD44_Ncut_open_split_forbids_connected_crossing:
      "\<And>Z. S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<Longrightarrow> Z \<subseteq> ?Ncut
        \<Longrightarrow> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
        \<Longrightarrow> Z \<inter> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1 \<noteq> {}
        \<Longrightarrow> Z \<inter>
              (?Ncut - geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1)
              \<noteq> {}
        \<Longrightarrow> False"
    (**
      Separation form of the remaining contradiction.  Once the negation of the
      desired component relation has split \<open>Ncut\<close>, no connected set contained
      in \<open>Ncut\<close> can meet both the \<open>Q1\<close> side and the complementary \<open>S1\<close> side.
      The unfinished Moise frontier subarc should supply exactly such a
      connected crossing, thereby closing the central route step. **)
  proof -
    fix Z
    assume hnot:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    assume hZ_sub: "Z \<subseteq> ?Ncut"
    assume hZ_conn:
      "top1_connected_on Z
        (subspace_topology UNIV geotop_euclidean_topology Z)"
    assume hZ_CQ:
      "Z \<inter> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1 \<noteq> {}"
    assume hZ_rest:
      "Z \<inter>
        (?Ncut - geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1)
        \<noteq> {}"
    let ?CQ = "geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    let ?R = "?Ncut - ?CQ"
    have hsplit:
        "?Ncut = ?CQ \<union> ?R
        \<and> ?CQ \<inter> ?R = {}
        \<and> ?CQ \<in> geotop_euclidean_topology
        \<and> ?R \<in> geotop_euclidean_topology
        \<and> Q1 \<in> ?CQ
        \<and> S1 \<in> ?R"
      by (rule hD44_Ncut_open_split_if_not_same_component[OF hnot])
    have hNcut_union: "?Ncut = ?CQ \<union> ?R"
    proof -
      from hsplit show ?thesis
        apply (elim conjE)
        apply assumption
        done
    qed
    have hdisj: "?CQ \<inter> ?R = {}"
    proof -
      from hsplit show ?thesis
        apply (elim conjE)
        apply assumption
        done
    qed
    have hCQ_open_top: "?CQ \<in> geotop_euclidean_topology"
    proof -
      from hsplit show ?thesis
        apply (elim conjE)
        apply assumption
        done
    qed
    have hR_open_top: "?R \<in> geotop_euclidean_topology"
    proof -
      from hsplit show ?thesis
        apply (elim conjE)
        apply assumption
        done
    qed
    have hQ1_CQ: "Q1 \<in> ?CQ"
    proof -
      from hsplit show ?thesis
        apply (elim conjE)
        apply assumption
        done
    qed
    have hS1_R: "S1 \<in> ?R"
      by (rule DiffI[OF hS1_Ncut hnot])
    have hCQ_sub_Ncut: "?CQ \<subseteq> ?Ncut"
    proof
      fix x
      assume hx: "x \<in> ?CQ"
      let ?F = "{C. C \<subseteq> ?Ncut \<and> Q1 \<in> C
        \<and> top1_connected_on C
            (subspace_topology UNIV geotop_euclidean_topology C)}"
      have hxU: "x \<in> \<Union>?F"
        using hx unfolding geotop_component_at_def .
      obtain C where hxC: "x \<in> C" and hCF: "C \<in> ?F"
        using hxU by (rule UnionE)
      have hC_all:
          "C \<subseteq> ?Ncut \<and> Q1 \<in> C
            \<and> top1_connected_on C
              (subspace_topology UNIV geotop_euclidean_topology C)"
        using hCF by (rule CollectD)
      have hC_sub: "C \<subseteq> ?Ncut"
        using hC_all by (rule conjunct1)
      show "x \<in> ?Ncut"
        by (rule hC_sub[THEN subsetD, OF hxC])
    qed
    have hR_sub_Ncut: "?R \<subseteq> ?Ncut"
      by (rule Diff_subset)
    have hCQ_inter_eq: "?Ncut \<inter> ?CQ = ?CQ"
    proof (rule antisym)
      show "?Ncut \<inter> ?CQ \<subseteq> ?CQ"
        by (rule Int_lower2)
      show "?CQ \<subseteq> ?Ncut \<inter> ?CQ"
      proof
        fix x
        assume hx: "x \<in> ?CQ"
        have hxN: "x \<in> ?Ncut"
          by (rule hCQ_sub_Ncut[THEN subsetD, OF hx])
        show "x \<in> ?Ncut \<inter> ?CQ"
          by (rule IntI[OF hxN hx])
      qed
    qed
    have hR_inter_eq: "?Ncut \<inter> ?R = ?R"
    proof (rule antisym)
      show "?Ncut \<inter> ?R \<subseteq> ?R"
        by (rule Int_lower2)
      show "?R \<subseteq> ?Ncut \<inter> ?R"
      proof
        fix x
        assume hx: "x \<in> ?R"
        have hxN: "x \<in> ?Ncut"
          by (rule hR_sub_Ncut[THEN subsetD, OF hx])
        show "x \<in> ?Ncut \<inter> ?R"
          by (rule IntI[OF hxN hx])
      qed
    qed
    have hCQ_open_sub:
        "?CQ \<in> subspace_topology UNIV geotop_euclidean_topology ?Ncut"
      unfolding subspace_topology_def
    proof (rule CollectI)
      show "\<exists>U. ?CQ = ?Ncut \<inter> U \<and> U \<in> geotop_euclidean_topology"
      proof (rule exI[where x = ?CQ], intro conjI)
        show "?CQ = ?Ncut \<inter> ?CQ"
          by (rule hCQ_inter_eq[symmetric])
        show "?CQ \<in> geotop_euclidean_topology"
          by (rule hCQ_open_top)
      qed
    qed
    have hR_open_sub:
        "?R \<in> subspace_topology UNIV geotop_euclidean_topology ?Ncut"
      unfolding subspace_topology_def
    proof (rule CollectI)
      show "\<exists>U. ?R = ?Ncut \<inter> U \<and> U \<in> geotop_euclidean_topology"
      proof (rule exI[where x = ?R], intro conjI)
        show "?R = ?Ncut \<inter> ?R"
          by (rule hR_inter_eq[symmetric])
        show "?R \<in> geotop_euclidean_topology"
          by (rule hR_open_top)
      qed
    qed
    have hsep:
        "top1_is_separation_on ?Ncut
          (subspace_topology UNIV geotop_euclidean_topology ?Ncut) ?CQ ?R"
      unfolding top1_is_separation_on_def
    proof (intro conjI)
      show "?CQ \<in> subspace_topology UNIV geotop_euclidean_topology ?Ncut"
        by (rule hCQ_open_sub)
      show "?R \<in> subspace_topology UNIV geotop_euclidean_topology ?Ncut"
        by (rule hR_open_sub)
      show "?CQ \<noteq> {}"
      proof
        assume hCQ_empty: "?CQ = {}"
        have "Q1 \<in> {}"
          by (subst hCQ_empty[symmetric], rule hQ1_CQ)
        thus False
          by (rule emptyE)
      qed
      show "?R \<noteq> {}"
      proof
        assume hR_empty: "?R = {}"
        have "S1 \<in> {}"
          by (subst hR_empty[symmetric], rule hS1_R)
        thus False
          by (rule emptyE)
      qed
      show "?CQ \<inter> ?R = {}"
        by (rule hdisj)
      show "?CQ \<union> ?R = ?Ncut"
        by (rule hNcut_union[symmetric])
    qed
    have hUNIV_top:
        "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
      by (metis geotop_euclidean_topology_eq_open_sets
          top1_open_sets_is_topology_on_UNIV)
    have htop_Ncut:
        "is_topology_on ?Ncut
          (subspace_topology UNIV geotop_euclidean_topology ?Ncut)"
      by (rule subspace_topology_is_topology_on[OF hUNIV_top subset_UNIV])
    have hZ_subspace:
        "subspace_topology ?Ncut
          (subspace_topology UNIV geotop_euclidean_topology ?Ncut) Z =
         subspace_topology UNIV geotop_euclidean_topology Z"
      by (rule subspace_topology_trans[OF hZ_sub])
    have hZ_conn_Ncut:
        "top1_connected_on Z
          (subspace_topology ?Ncut
            (subspace_topology UNIV geotop_euclidean_topology ?Ncut) Z)"
      by (subst hZ_subspace, rule hZ_conn)
    have hZ_side: "Z \<subseteq> ?CQ \<or> Z \<subseteq> ?R"
      by (rule Lemma_23_2[OF htop_Ncut hsep hZ_sub hZ_conn_Ncut])
    from hZ_side show False
    proof
      assume hZ_CQ_sub: "Z \<subseteq> ?CQ"
      have hZ_rest_ex: "\<exists>x. x \<in> Z \<inter> ?R"
        unfolding ex_in_conv by (rule hZ_rest)
      obtain x where hxZR: "x \<in> Z \<inter> ?R"
        using hZ_rest_ex by (elim exE)
      have hxZ: "x \<in> Z"
        by (rule IntD1[OF hxZR])
      have hxR: "x \<in> ?R"
        by (rule IntD2[OF hxZR])
      have hxCQ: "x \<in> ?CQ"
        by (rule hZ_CQ_sub[THEN subsetD, OF hxZ])
      have hxCQR: "x \<in> ?CQ \<inter> ?R"
        by (rule IntI[OF hxCQ hxR])
      have "x \<in> {}"
        by (subst hdisj[symmetric], rule hxCQR)
      thus False
        by (rule emptyE)
    next
      assume hZ_R: "Z \<subseteq> ?R"
      have hZ_CQ_ex: "\<exists>x. x \<in> Z \<inter> ?CQ"
        unfolding ex_in_conv by (rule hZ_CQ)
      obtain x where hxZCQ: "x \<in> Z \<inter> ?CQ"
        using hZ_CQ_ex by (elim exE)
      have hxZ: "x \<in> Z"
        by (rule IntD1[OF hxZCQ])
      have hxCQ: "x \<in> ?CQ"
        by (rule IntD2[OF hxZCQ])
      have hxR: "x \<in> ?R"
        by (rule hZ_R[THEN subsetD, OF hxZ])
      have hxCQR: "x \<in> ?CQ \<inter> ?R"
        by (rule IntI[OF hxCQ hxR])
      have "x \<in> {}"
        by (subst hdisj[symmetric], rule hxCQR)
      thus False
        by (rule emptyE)
    qed
  qed
  have hD44_Ncut_open_split_forbids_connected_access_ball_crossing:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<Longrightarrow> \<exists>\<epsilon>\<^sub>Q>0. \<exists>\<epsilon>\<^sub>S>0.
          (\<forall>Z. Z \<subseteq> ?Ncut
            \<longrightarrow> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<longrightarrow> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<longrightarrow> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}
            \<longrightarrow> False)"
    (**
      Access-ball contradiction form of the same split.  After negating the
      desired component relation, choose the component-side collars around
      \<open>Q1\<close> and \<open>S1\<close>.  Any connected subset of \<open>Ncut\<close> meeting both collars
      would cross the open component separation, contradicting the previous
      separation bridge.  This is the exact target for the final Moise
      lower-to-upper frontier witness. **)
  proof -
    assume hnot:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    let ?CQ = "geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    let ?R = "?Ncut - ?CQ"
    obtain \<epsilon>\<^sub>Q \<epsilon>\<^sub>S where h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
      and h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
      and hball_Q_CQ: "ball Q1 \<epsilon>\<^sub>Q \<subseteq> ?CQ"
      and hball_S_R: "ball S1 \<epsilon>\<^sub>S \<subseteq> ?R"
      using hD44_Ncut_open_split_access_balls_if_not_same_component[OF hnot]
      by (elim exE conjE)
    have hall:
        "\<forall>Z. Z \<subseteq> ?Ncut
          \<longrightarrow> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<longrightarrow> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<longrightarrow> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}
          \<longrightarrow> False"
    proof (intro allI impI)
      fix Z
      assume hZ_sub: "Z \<subseteq> ?Ncut"
      assume hZ_conn:
        "top1_connected_on Z
          (subspace_topology UNIV geotop_euclidean_topology Z)"
      assume hZ_Qball: "Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
      assume hZ_Sball: "Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      have hZ_CQ: "Z \<inter> ?CQ \<noteq> {}"
      proof -
        have hZ_Qball_ex: "\<exists>x. x \<in> Z \<inter> ball Q1 \<epsilon>\<^sub>Q"
          unfolding ex_in_conv by (rule hZ_Qball)
        obtain x where hxZQ: "x \<in> Z \<inter> ball Q1 \<epsilon>\<^sub>Q"
          using hZ_Qball_ex by (elim exE)
        have hxZ: "x \<in> Z"
          by (rule IntD1[OF hxZQ])
        have hxball: "x \<in> ball Q1 \<epsilon>\<^sub>Q"
          by (rule IntD2[OF hxZQ])
        have hxCQ: "x \<in> ?CQ"
          by (rule hball_Q_CQ[THEN subsetD, OF hxball])
        have hxZCQ: "x \<in> Z \<inter> ?CQ"
          by (rule IntI[OF hxZ hxCQ])
        show ?thesis
          unfolding ex_in_conv[symmetric] by (rule exI[where x = x], rule hxZCQ)
      qed
      have hZ_R: "Z \<inter> ?R \<noteq> {}"
      proof -
        have hZ_Sball_ex: "\<exists>x. x \<in> Z \<inter> ball S1 \<epsilon>\<^sub>S"
          unfolding ex_in_conv by (rule hZ_Sball)
        obtain x where hxZS: "x \<in> Z \<inter> ball S1 \<epsilon>\<^sub>S"
          using hZ_Sball_ex by (elim exE)
        have hxZ: "x \<in> Z"
          by (rule IntD1[OF hxZS])
        have hxball: "x \<in> ball S1 \<epsilon>\<^sub>S"
          by (rule IntD2[OF hxZS])
        have hxR: "x \<in> ?R"
          by (rule hball_S_R[THEN subsetD, OF hxball])
        have hxZR: "x \<in> Z \<inter> ?R"
          by (rule IntI[OF hxZ hxR])
        show ?thesis
          unfolding ex_in_conv[symmetric] by (rule exI[where x = x], rule hxZR)
      qed
      show False
        by (rule hD44_Ncut_open_split_forbids_connected_crossing
            [OF hnot hZ_sub hZ_conn hZ_CQ hZ_R])
    qed
    show ?thesis
    proof (rule exI[where x=\<epsilon>\<^sub>Q], intro conjI)
      show "0 < \<epsilon>\<^sub>Q" by (rule h\<epsilon>\<^sub>Q_pos)
      show "\<exists>\<epsilon>\<^sub>S>0.
          (\<forall>Z. Z \<subseteq> ?Ncut \<longrightarrow>
            top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z) \<longrightarrow>
            Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {} \<longrightarrow>
            Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {} \<longrightarrow> False)"
      proof (rule exI[where x=\<epsilon>\<^sub>S], intro conjI)
        show "0 < \<epsilon>\<^sub>S" by (rule h\<epsilon>\<^sub>S_pos)
        show "\<forall>Z. Z \<subseteq> ?Ncut \<longrightarrow>
            top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z) \<longrightarrow>
            Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {} \<longrightarrow>
            Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {} \<longrightarrow> False"
          by (rule hall)
      qed
    qed
  qed
  have hD44_arbitrary_access_ball_crossings_suffice:
      "(\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
          \<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})
        \<Longrightarrow> S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut Q1"
    (**
      Final reduction toward Moise's lower-to-upper frontier construction.  To
      prove the desired component relation, it is enough to show that every pair
      of sufficiently small access collars around \<open>Q1\<close> and \<open>S1\<close> is joined by
      some connected subset of \<open>Ncut\<close>.  If the component relation failed, the
      previous split-collar lemma would choose two collars that no connected
      subset of \<open>Ncut\<close> can meet simultaneously. **)
  proof -
    assume hall_crossings:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    show ?thesis
    proof (rule ccontr)
      assume hnotnot:
        "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
      obtain \<epsilon>\<^sub>Q \<epsilon>\<^sub>S where h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
        and h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
        and hforbid:
          "\<forall>Z. Z \<subseteq> ?Ncut
            \<longrightarrow> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<longrightarrow> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<longrightarrow> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}
            \<longrightarrow> False"
        using hD44_Ncut_open_split_forbids_connected_access_ball_crossing
          [OF hnotnot]
        by (elim exE conjE)
      obtain Z where hZ_sub: "Z \<subseteq> ?Ncut"
        and hZ_conn:
          "top1_connected_on Z
            (subspace_topology UNIV geotop_euclidean_topology Z)"
        and hZ_Q: "Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
        and hZ_S: "Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      proof -
        have hQ_spec:
          "\<forall>\<epsilon>\<^sub>S>0. \<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
        proof -
          have hQ_imp:
            "0 < \<epsilon>\<^sub>Q \<longrightarrow> (\<forall>\<epsilon>\<^sub>S>0. \<exists>Z. Z \<subseteq> ?Ncut
              \<and> top1_connected_on Z
                  (subspace_topology UNIV geotop_euclidean_topology Z)
              \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
              \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
            by (rule spec[OF hall_crossings])
          show ?thesis
            by (rule mp[OF hQ_imp h\<epsilon>\<^sub>Q_pos])
        qed
        have hQS_spec:
          "\<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
        proof -
          have hS_imp:
            "0 < \<epsilon>\<^sub>S \<longrightarrow> (\<exists>Z. Z \<subseteq> ?Ncut
              \<and> top1_connected_on Z
                  (subspace_topology UNIV geotop_euclidean_topology Z)
              \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
              \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
            by (rule spec[OF hQ_spec])
          show ?thesis
            by (rule mp[OF hS_imp h\<epsilon>\<^sub>S_pos])
        qed
        then obtain Z where hZ:
          "Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
          by (elim exE)
        have hZ_sub': "Z \<subseteq> ?Ncut"
          by (rule conjunct1[OF hZ])
        have hZ_tail:
            "top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
              \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
              \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
          by (rule conjunct2[OF hZ])
        have hZ_conn':
          "top1_connected_on Z
            (subspace_topology UNIV geotop_euclidean_topology Z)"
          by (rule conjunct1[OF hZ_tail])
        have hZ_tail':
            "Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
              \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
          by (rule conjunct2[OF hZ_tail])
        have hZ_Q': "Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
          by (rule conjunct1[OF hZ_tail'])
        have hZ_S': "Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
          by (rule conjunct2[OF hZ_tail'])
        show ?thesis
          by (rule that[OF hZ_sub' hZ_conn' hZ_Q' hZ_S'])
      qed
      have False
      proof -
        have h1:
          "Z \<subseteq> ?Ncut \<longrightarrow>
            top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z) \<longrightarrow>
            Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {} \<longrightarrow>
            Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {} \<longrightarrow> False"
          by (rule spec[OF hforbid])
        have h2:
          "top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z) \<longrightarrow>
            Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {} \<longrightarrow>
            Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {} \<longrightarrow> False"
          by (rule mp[OF h1 hZ_sub])
        have h3:
          "Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {} \<longrightarrow>
            Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {} \<longrightarrow> False"
          by (rule mp[OF h2 hZ_conn])
        have h4:
          "Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {} \<longrightarrow> False"
          by (rule mp[OF h3 hZ_Q])
        show False
          by (rule mp[OF h4 hZ_S])
      qed
      thus False .
    qed
  qed
  have hD44_arbitrary_access_broken_line_crossings_suffice:
      "(\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
          \<exists>B. geotop_is_broken_line B
            \<and> B \<subseteq> ?Ncut
            \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})
        \<Longrightarrow> S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut Q1"
    (**
      Book-facing version of the previous reduction.  Moise constructs a
      broken-line corridor between arbitrarily small lower and upper access
      collars; since every broken line is connected, such corridors supply the
      connected access-ball crossings needed to force the \<open>Q1\<close> and \<open>S1\<close>
      access points into the same \<open>Ncut\<close> component. **)
  proof -
    assume hall_broken:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>B. geotop_is_broken_line B
          \<and> B \<subseteq> ?Ncut
          \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    have hall_connected:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    proof (intro allI impI)
      fix \<epsilon>\<^sub>Q \<epsilon>\<^sub>S :: real
      assume h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
      assume h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
      have hQ_spec:
        "\<forall>\<epsilon>\<^sub>S>0. \<exists>B. geotop_is_broken_line B
          \<and> B \<subseteq> ?Ncut
          \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      proof -
        have hQ_imp:
          "0 < \<epsilon>\<^sub>Q \<longrightarrow> (\<forall>\<epsilon>\<^sub>S>0. \<exists>B. geotop_is_broken_line B
            \<and> B \<subseteq> ?Ncut
            \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
          by (rule spec[OF hall_broken])
        show ?thesis
          by (rule mp[OF hQ_imp h\<epsilon>\<^sub>Q_pos])
      qed
      have hQS_spec:
        "\<exists>B. geotop_is_broken_line B
          \<and> B \<subseteq> ?Ncut
          \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      proof -
        have hS_imp:
          "0 < \<epsilon>\<^sub>S \<longrightarrow> (\<exists>B. geotop_is_broken_line B
            \<and> B \<subseteq> ?Ncut
            \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
          by (rule spec[OF hQ_spec])
        show ?thesis
          by (rule mp[OF hS_imp h\<epsilon>\<^sub>S_pos])
      qed
      obtain B where hB_bl: "geotop_is_broken_line B"
        and hB_sub: "B \<subseteq> ?Ncut"
        and hB_Q: "B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
        and hB_S: "B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
        using hQS_spec by (elim exE conjE)
      have hB_conn:
        "top1_connected_on B
          (subspace_topology UNIV geotop_euclidean_topology B)"
        by (rule geotop_broken_line_connected_on_prefix[OF hB_bl])
      show "\<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
        using hB_sub hB_conn hB_Q hB_S by (intro exI conjI)
    qed
    show ?thesis
      by (rule hD44_arbitrary_access_ball_crossings_suffice[OF hall_connected])
  qed
  have hD44_moise_broken_line_access_crossings_book_step:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>B. geotop_is_broken_line B
          \<and> B \<subseteq> ?Ncut
          \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    (**
      Remaining Moise 4.4 construction after the routine carrier hygiene
      and frontier-component setup above.  The unproved part is now exactly
      the book's regular-neighborhood frontier analysis from the component
      \<open>J\<^sub>N\<close> and restricted carrier complex \<open>K\<^sub>N\<close>: prove the corresponding
      boundary subcomplex carries the frontier component through \<open>P\<close>, prove
      it is a polygonal 1-sphere, take the complementary lower-to-upper
      frontier subarc, and push it to the adjacent outside side of \<open>?Ncut\<close>
      so it crosses every pair of access collars. **)
  proof -
    have hD44_moise_closed_corridor_book_step:
        "\<exists>C. C \<subseteq> ?Ncut
          \<and> top1_connected_on C
              (subspace_topology UNIV geotop_euclidean_topology C)
          \<and> Q1 \<in> closure C
          \<and> S1 \<in> closure C"
      (**
        Remaining Moise 4.4 frontier construction in its component-frontier
        form.  The book's fine carrier/regular-neighborhood analysis supplies
        the outside component adjacent to the complementary frontier subarc;
        that component lies in \<open>I - (N \<union> A2)\<close>, is connected, and has the
        lower and upper access points in its ordinary Euclidean closure. **)
    proof -
      have hD44_moise_Q1_component_accumulates_at_S1_book_step:
          "S1 \<in> closure
            (geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1)"
      proof -
        have hD44_moise_boundary_subarc_adjacent_corridor_book_step:
            "\<exists>X C L C\<^sub>F Z. X \<in> ?B1P
              \<and> X \<noteq> P
              \<and> geotop_is_broken_line C
              \<and> C \<subseteq> ?B1P
              \<and> C \<subseteq> F\<^sub>1
              \<and> C \<subseteq> J\<^sub>N
              \<and> C \<subseteq> FrN\<^sub>I
              \<and> C \<inter> F\<^sub>2 = {}
              \<and> C \<inter> (A2 \<union> {Q, S}) = {}
              \<and> C \<inter> ?Ncut = {}
              \<and> P \<in> C
              \<and> X \<in> C
              \<and> geotop_arc_endpoints C {P, X}
              \<and> connected (geotop_arc_interior C {P, X})
              \<and> geotop_arc_interior C {P, X} \<noteq> {}
              \<and> geotop_is_complex L
              \<and> geotop_complex_is_1dim L
              \<and> finite L
              \<and> geotop_polyhedron L = C
              \<and> {P} \<in> L
              \<and> {X} \<in> L
              \<and> geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>F
              \<and> geotop_is_broken_line C\<^sub>F
              \<and> geotop_arc_endpoints C\<^sub>F {P, X}
              \<and> geotop_arc_interior C {P, X} \<inter>
                  geotop_arc_interior C\<^sub>F {P, X} = {}
              \<and> C \<inter> C\<^sub>F = {P, X}
              \<and> P \<in> C\<^sub>F
              \<and> X \<in> C\<^sub>F
              \<and> C\<^sub>F \<subseteq> J\<^sub>N
              \<and> C\<^sub>F \<subseteq> FrN\<^sub>I
              \<and> C\<^sub>F \<inter> (A2 \<union> {Q, S}) = {}
              \<and> C\<^sub>F \<inter> ?Ncut = {}
              \<and> Z \<subseteq> ?Ncut
              \<and> top1_connected_on Z
                  (subspace_topology UNIV geotop_euclidean_topology Z)
              \<and> Q1 \<in> closure Z
              \<and> S1 \<in> closure Z"
          (**
            Remaining literal Moise 4.4 step.  First prove the local
            regular-neighborhood frontier component through \<open>P\<close> is a
            polygonal 1-sphere, split it into the boundary subarc \<open>C\<close> and
            complementary frontier arc \<open>C\<^sub>F\<close>, then take the outside component
            of \<open>I - (N \<union> A2)\<close> adjacent to \<open>C\<^sub>F\<close>.  That adjacent component is
            the connected corridor \<open>Z\<close> whose closure contains the two access
            witnesses \<open>Q1\<close> and \<open>S1\<close>. **)
        proof -
          have hD44_moise_vertex_upper_no_endpoint_and_adjacent_corridor_book_step:
              "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
                  card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2)
              \<and> (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
                  \<not> geotop_graph_endpoint BdJ\<^sub>N w)
              \<and> (\<exists>Z. Z \<subseteq> ?Ncut
                \<and> top1_connected_on Z
                    (subspace_topology UNIV geotop_euclidean_topology Z)
                \<and> Q1 \<in> closure Z
                \<and> S1 \<in> closure Z)"
            (**
              Remaining local regular-neighborhood content of Moise 4.4.  The
              frontier component through \<open>P\<close> has local valence at most two,
              no graph endpoints, and an adjacent outside component of
              \<open>I - (N \<union> A2)\<close> whose closure contains the two access witnesses.
              Existing graph helpers then turn this into the book's polygonal
              1-sphere split. **)
            by (rule
              geotop_polygon_two_endpoint_arcs_regular_neighborhood_frontier_component_package_prefix
                [OF hJ hP hQ hR hS hcyc hcard hA1 hA2 hA12 hA1_sub
                  hA2_sub hA1J hA2J hK_complex hK_fin hK_poly hN_def
                  hA1_N hN_avoid hr hball_Q_N hball_S_N hQ1_ball
                  hS1_ball hQ1_Ncut hS1_Ncut N\<^sub>I_def FrN\<^sub>I_def
                  J\<^sub>N_def K\<^sub>N_def BdK\<^sub>N_def BdJ\<^sub>N_def])
          have hle2_all:
              "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
                card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
            using hD44_moise_vertex_upper_no_endpoint_and_adjacent_corridor_book_step
            by (rule conjunct1)
          have htail:
              "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
                  \<not> geotop_graph_endpoint BdJ\<^sub>N w)
              \<and> (\<exists>Z. Z \<subseteq> ?Ncut
                \<and> top1_connected_on Z
                    (subspace_topology UNIV geotop_euclidean_topology Z)
                \<and> Q1 \<in> closure Z
                \<and> S1 \<in> closure Z)"
            using hD44_moise_vertex_upper_no_endpoint_and_adjacent_corridor_book_step
            by (rule conjunct2)
          have hnoend_all:
              "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
                \<not> geotop_graph_endpoint BdJ\<^sub>N w"
            using htail by (rule conjunct1)
          have hZ_ex:
              "\<exists>Z. Z \<subseteq> ?Ncut
                \<and> top1_connected_on Z
                    (subspace_topology UNIV geotop_euclidean_topology Z)
                \<and> Q1 \<in> closure Z
                \<and> S1 \<in> closure Z"
            using htail by (rule conjunct2)
          have hle2:
              "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
                card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
            using hle2_all by (by100 blast)
          have hge2_all:
              "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
                card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
            by (rule hBdJ\<^sub>N_vertex_card_ge2_from_no_endpoint
                [OF hnoend_all])
          have hge2:
              "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
                card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
            using hge2_all by (by100 blast)
          have hdegree:
              "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
                card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
            by (rule hBdJ\<^sub>N_vertex_degree_two_from_card_bounds
                [OF hle2 hge2])
          obtain X C L C\<^sub>F where hsplit:
              "X \<in> ?B1P
                \<and> X \<noteq> P
                \<and> geotop_is_broken_line C
                \<and> C \<subseteq> ?B1P
                \<and> C \<subseteq> F\<^sub>1
                \<and> C \<subseteq> J\<^sub>N
                \<and> C \<subseteq> FrN\<^sub>I
                \<and> C \<inter> F\<^sub>2 = {}
                \<and> C \<inter> (A2 \<union> {Q, S}) = {}
                \<and> C \<inter> ?Ncut = {}
                \<and> P \<in> C
                \<and> X \<in> C
                \<and> geotop_arc_endpoints C {P, X}
                \<and> connected (geotop_arc_interior C {P, X})
                \<and> geotop_arc_interior C {P, X} \<noteq> {}
                \<and> geotop_is_complex L
                \<and> geotop_complex_is_1dim L
                \<and> finite L
                \<and> geotop_polyhedron L = C
                \<and> {P} \<in> L
                \<and> {X} \<in> L
                \<and> geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>F
                \<and> geotop_is_broken_line C\<^sub>F
                \<and> geotop_arc_endpoints C\<^sub>F {P, X}
                \<and> geotop_arc_interior C {P, X} \<inter>
                    geotop_arc_interior C\<^sub>F {P, X} = {}
                \<and> C \<inter> C\<^sub>F = {P, X}
                \<and> P \<in> C\<^sub>F
                \<and> X \<in> C\<^sub>F
                \<and> C\<^sub>F \<subseteq> J\<^sub>N
                \<and> C\<^sub>F \<subseteq> FrN\<^sub>I
                \<and> C\<^sub>F \<inter> (A2 \<union> {Q, S}) = {}
                \<and> C\<^sub>F \<inter> ?Ncut = {}"
            using hD44_BdJ\<^sub>N_degree_two_boundary_subarc_complement_split
              [OF hdegree]
            by (elim exE)
          obtain Z where hZ:
              "Z \<subseteq> ?Ncut
                \<and> top1_connected_on Z
                    (subspace_topology UNIV geotop_euclidean_topology Z)
                \<and> Q1 \<in> closure Z
                \<and> S1 \<in> closure Z"
            using hZ_ex by (elim exE)
          show ?thesis
            using hsplit hZ
            apply (elim conjE)
            apply (rule exI[where x=X])
            apply (rule exI[where x=C])
            apply (rule exI[where x=L])
            apply (rule exI[where x=C\<^sub>F])
            apply (rule exI[where x=Z])
            apply (intro conjI)
            apply assumption+
            done
        qed
        show ?thesis
        proof -
          obtain X C L C\<^sub>F Z where hZ_sub: "Z \<subseteq> ?Ncut"
            and hZ_conn:
              "top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)"
            and hQ1_cl: "Q1 \<in> closure Z"
            and hS1_cl: "S1 \<in> closure Z"
            using hD44_moise_boundary_subarc_adjacent_corridor_book_step
            by (elim exE conjE)
          have hS1_comp:
              "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
                ?Ncut Q1"
            by (rule geotop_connected_closure_corridor_same_component_open_prefix
                [OF hNcut_open hQ1_Ncut hS1_Ncut hZ_sub hZ_conn
                  hQ1_cl hS1_cl])
          show ?thesis
            using hS1_comp closure_subset by (by100 blast)
        qed
      qed
      have hD44_moise_same_component_frontier_book_step:
          "\<exists>C. C \<in> components ?Ncut
            \<and> Q1 \<in> closure C
            \<and> S1 \<in> closure C"
        by (rule geotop_component_at_closure_gives_component_closure_pair_prefix
            [OF hQ1_Ncut hD44_moise_Q1_component_accumulates_at_S1_book_step])
      obtain C where hC_comp: "C \<in> components ?Ncut"
        and hQ1_cl: "Q1 \<in> closure C"
        and hS1_cl: "S1 \<in> closure C"
        using hD44_moise_same_component_frontier_book_step
        by (elim exE conjE)
      show ?thesis
        by (rule geotop_component_closure_pair_gives_closed_corridor_prefix
            [OF hC_comp hQ1_cl hS1_cl])
    qed
    have hD44_moise_same_component_book_step:
        "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    proof -
      obtain C where hC_sub: "C \<subseteq> ?Ncut"
        and hC_conn:
          "top1_connected_on C
            (subspace_topology UNIV geotop_euclidean_topology C)"
        and hQ1_cl: "Q1 \<in> closure C"
        and hS1_cl: "S1 \<in> closure C"
        using hD44_moise_closed_corridor_book_step
        by (elim exE conjE)
      show ?thesis
        by (rule geotop_connected_closure_corridor_same_component_open_prefix
            [OF hNcut_open hQ1_Ncut hS1_Ncut hC_sub hC_conn hQ1_cl hS1_cl])
    qed
    obtain B where hB_bl: "geotop_is_broken_line B"
      and hB_sub: "B \<subseteq> ?Ncut"
      and hQ1_B: "Q1 \<in> B"
      and hS1_B: "S1 \<in> B"
      using hD44_same_component_in_Ncut_suffices
        [OF hD44_moise_same_component_book_step]
      by (elim exE conjE)
    show ?thesis
    proof (intro allI impI)
      fix \<epsilon>\<^sub>Q \<epsilon>\<^sub>S :: real
      assume h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
      assume h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
      have hB_Q: "B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
      proof -
        have hQ_mem: "Q1 \<in> B \<inter> ball Q1 \<epsilon>\<^sub>Q"
          using hQ1_B h\<epsilon>\<^sub>Q_pos by (by100 simp)
        show ?thesis
          unfolding ex_in_conv[symmetric]
          by (rule exI[where x = Q1], rule hQ_mem)
      qed
      have hB_S: "B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      proof -
        have hS_mem: "S1 \<in> B \<inter> ball S1 \<epsilon>\<^sub>S"
          using hS1_B h\<epsilon>\<^sub>S_pos by (by100 simp)
        show ?thesis
          unfolding ex_in_conv[symmetric]
          by (rule exI[where x = S1], rule hS_mem)
      qed
      show "\<exists>B. geotop_is_broken_line B
          \<and> B \<subseteq> ?Ncut
          \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
        using hB_bl hB_sub hB_Q hB_S by (intro exI conjI)
    qed
  qed
  show ?thesis
    by (rule hD44_moise_broken_line_access_crossings_book_step)
qed

lemma geotop_polygon_two_endpoint_arcs_fine_carrier_frontier_route_broken_line_prefix:
  fixes J A1 A2 N :: "(real^2) set"
    and K :: "(real^2) set set"
    and P Q R S Q1 S1 :: "real^2"
    and m :: nat
    and r :: real
  assumes hJ: "geotop_is_polygon J"
  assumes hP: "P \<in> J" and hQ: "Q \<in> J" and hR: "R \<in> J" and hS: "S \<in> J"
  assumes hcyc: "geotop_polygon_cyclic_order J P Q R S"
  assumes hcard: "card {P, Q, R, S} = 4"
  assumes hA1: "geotop_is_arc A1 (subspace_topology UNIV geotop_euclidean_topology A1)"
  assumes hA2: "geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2)"
  assumes hA12: "A1 \<inter> A2 = {}"
  assumes hA1_sub:
    "A1 \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hA2_sub:
    "A2 \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hA1J: "A1 \<inter> J = {P}"
  assumes hA2J: "A2 \<inter> J = {R}"
  assumes hK_complex: "geotop_is_complex K"
  assumes hK_fin: "finite K"
  assumes hK_poly:
    "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hN_def:
    "N = (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}})"
  assumes hA1_N: "A1 \<subseteq> N"
  assumes hN_avoid: "N \<inter> (A2 \<union> {Q, S}) = {}"
  assumes hr: "0 < r"
  assumes hball_Q_N: "ball Q r \<inter> N = {}"
  assumes hball_S_N: "ball S r \<inter> N = {}"
  assumes hQ1_ball: "Q1 \<in> ball Q r"
  assumes hS1_ball: "S1 \<in> ball S r"
  assumes hQ1_Ncut: "Q1 \<in> geotop_polygon_interior J - (N \<union> A2)"
  assumes hS1_Ncut: "S1 \<in> geotop_polygon_interior J - (N \<union> A2)"
  shows "\<exists>B. geotop_is_broken_line B
      \<and> B \<subseteq> geotop_polygon_interior J - (N \<union> A2)
      \<and> Q1 \<in> B
      \<and> S1 \<in> B"
  (**
    Exact remaining Moise 4.4 frontier-route theorem.  Starting from the fine
    subdivided carrier regular neighborhood \<open>N\<close> of \<open>A1\<close>, with \<open>N\<close> avoiding
    \<open>A2\<close> and with the chosen access balls at \<open>Q\<close> and \<open>S\<close> disjoint from
    \<open>N\<close>, analyze the frontier component through \<open>P\<close>.  Moise proves this
    component is a polygonal 1-sphere; its lower-to-upper boundary subarc,
    chosen between the last lower and first upper intersections with \<open>J\<close>, is
    a broken line in \<open>geotop_polygon_interior J - (N \<union> A2)\<close> attaching the
    access positions near \<open>Q\<close> and \<open>S\<close>. **)
proof -
  let ?Ncut = "geotop_polygon_interior J - (N \<union> A2)"
  have hP_in_A1: "P \<in> A1"
    using hA1J by (by100 blast)
  have hR_in_A2: "R \<in> A2"
    using hA2J by (by100 blast)
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
    by (rule geotop_polygon_iterated_Sd_selected_arc_carrier_subset_closed_disk_prefix
        [OF hK_complex hK_fin hK_poly hN_def])
  have hN_compact: "compact N"
    by (rule geotop_iterated_Sd_selected_arc_carrier_compact_prefix
        [OF hK_complex hK_fin hN_def])
  have hN_closed: "closed N"
    by (rule geotop_iterated_Sd_selected_arc_carrier_closed_prefix
        [OF hK_complex hK_fin hN_def])
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
    by (rule
        geotop_polygon_iterated_Sd_selected_arc_carrier_closed_disk_restrict_eq_prefix
          [OF hK_complex hK_fin hK_poly hN_def N\<^sub>I_def])
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
  have hFrN\<^sub>I_sub_N\<^sub>I: "FrN\<^sub>I \<subseteq> N\<^sub>I"
    using hFrN\<^sub>I_HOL frontier_subset_closed[OF hN\<^sub>I_closed] by (by100 simp)
  have hFrN\<^sub>I_sub_N: "FrN\<^sub>I \<subseteq> N"
    using hFrN\<^sub>I_sub_N\<^sub>I hN\<^sub>I_eq_N by (by100 simp)
  have hFrN\<^sub>I_closed: "closed FrN\<^sub>I"
    using hFrN\<^sub>I_HOL frontier_closed by (by100 simp)
  have hFrN\<^sub>I_compact: "compact FrN\<^sub>I"
    by (rule closed_subset_compact[OF hN\<^sub>I_compact hFrN\<^sub>I_closed hFrN\<^sub>I_sub_N\<^sub>I])
  have hFrN\<^sub>I_A2_QS_disj: "FrN\<^sub>I \<inter> (A2 \<union> {Q, S}) = {}"
    using hFrN\<^sub>I_sub_N hN_avoid by (by100 blast)
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
    using hJ\<^sub>N_sub_N hN_avoid by (by100 blast)
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
      thus "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
        by (by100 simp)
    next
      assume "e \<in> {\<rho>. \<exists>\<tau>\<in>?S. geotop_is_face \<rho> \<tau>}"
      then obtain \<tau> where h\<tau>S: "\<tau> \<in> ?S" and heface\<tau>: "geotop_is_face e \<tau>"
        by (by100 blast)
      have h\<tau>1: "geotop_simplex_dim \<tau> 1"
        using h\<tau>S by (by100 simp)
      have he1: "geotop_simplex_dim e 1"
        using hedge unfolding geotop_is_edge_def by (by100 simp)
      obtain k where hk_le: "k \<le> 1" and hek: "geotop_simplex_dim e k"
        using geotop_face_dim_le_prefix[OF h\<tau>1 heface\<tau>] by (by100 blast)
      have hk1: "k = 1"
        by (rule geotop_simplex_dim_unique[OF hek he1])
      have hsame_dim: "geotop_simplex_dim e 1"
        using hek hk1 by (by100 simp)
      have h\<tau>edge: "geotop_is_edge \<tau>"
        using h\<tau>1 unfolding geotop_is_edge_def by (by100 simp)
      have he_eq_\<tau>: "e = \<tau>"
        by (rule geotop_edge_face_of_edge_eq_prefix[OF hedge h\<tau>edge heface\<tau>])
      show "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
        using h\<tau>S he_eq_\<tau> by (by100 simp)
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
  have hBdJ\<^sub>N_poly_compact: "compact (geotop_polyhedron BdJ\<^sub>N)"
    by (rule geotop_complex_polyhedron_compact
        [OF hBdJ\<^sub>N_complex hBdJ\<^sub>N_fin])
  have hBdJ\<^sub>N_poly_closed: "closed (geotop_polyhedron BdJ\<^sub>N)"
    by (rule geotop_complex_polyhedron_closed
        [OF hBdJ\<^sub>N_complex hBdJ\<^sub>N_fin])
  have hBdJ\<^sub>N_poly_sub_J\<^sub>N: "geotop_polyhedron BdJ\<^sub>N \<subseteq> J\<^sub>N"
    unfolding BdJ\<^sub>N_def geotop_polyhedron_def by (by100 blast)
  have hBdJ\<^sub>N_poly_sub_FrN\<^sub>I: "geotop_polyhedron BdJ\<^sub>N \<subseteq> FrN\<^sub>I"
    using hBdJ\<^sub>N_poly_sub_J\<^sub>N hJ\<^sub>N_sub_FrN\<^sub>I by (by100 blast)
  have hBdJ\<^sub>N_edge_sub_J\<^sub>N:
      "\<And>e. e \<in> BdJ\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> e \<subseteq> J\<^sub>N"
    unfolding BdJ\<^sub>N_def by (by100 simp)
  have hBdJ\<^sub>N_edge_sub_FrN\<^sub>I:
      "\<And>e. e \<in> BdJ\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> e \<subseteq> FrN\<^sub>I"
  proof -
    fix e
    assume heBdJ: "e \<in> BdJ\<^sub>N" and hedge: "geotop_is_edge e"
    have heJ: "e \<subseteq> J\<^sub>N"
      by (rule hBdJ\<^sub>N_edge_sub_J\<^sub>N[OF heBdJ hedge])
    show "e \<subseteq> FrN\<^sub>I"
      using heJ hJ\<^sub>N_sub_FrN\<^sub>I by (by100 blast)
  qed
  have hBdJ\<^sub>N_edge_member_incident_count_one:
      "\<And>e. e \<in> BdJ\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
        card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
  proof -
    fix e
    assume heBdJ: "e \<in> BdJ\<^sub>N" and hedge: "geotop_is_edge e"
    have heBdK: "e \<in> BdK\<^sub>N"
      using heBdJ unfolding BdJ\<^sub>N_def by (by100 simp)
    show "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
      by (rule hBdK\<^sub>N_edge_member_incident_count_one[OF heBdK hedge])
  qed
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
  have hJ\<^sub>N_uncovered_openin:
      "openin (top_of_set J\<^sub>N)
        (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N)"
    using hBdJ\<^sub>N_poly_closedin_J\<^sub>N
    unfolding closedin_def by (by100 simp)
  have hJ\<^sub>N_uncovered_closed:
      "closed (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N)"
    using hJ\<^sub>N_uncovered_finite by (rule finite_imp_closed)
  have hJ\<^sub>N_uncovered_closedin:
      "closedin (top_of_set J\<^sub>N)
        (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N)"
  proof -
    have hclosedin_int:
        "closedin (top_of_set J\<^sub>N)
          (J\<^sub>N \<inter> (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N))"
      using hJ\<^sub>N_uncovered_closed by (rule closedin_closed_Int)
    have heq:
        "J\<^sub>N \<inter> (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N) =
          J\<^sub>N - geotop_polyhedron BdJ\<^sub>N"
      by (by100 blast)
    show ?thesis
      using hclosedin_int heq by (by100 simp)
  qed
  have hJ\<^sub>N_uncovered_empty_or_all:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = {}
        \<or> J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    using connected_clopen[THEN iffD1, OF hJ\<^sub>N_connected_HOL]
      hJ\<^sub>N_uncovered_openin hJ\<^sub>N_uncovered_closedin
    by (by100 blast)
  have hJ\<^sub>N_uncovered_all_imp_finite:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow> finite J\<^sub>N"
    using hJ\<^sub>N_uncovered_finite by (by100 simp)
  have hJ\<^sub>N_uncovered_all_imp_singleton:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow> \<exists>x. J\<^sub>N = {x}"
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    have hfin: "finite J\<^sub>N"
      by (rule hJ\<^sub>N_uncovered_all_imp_finite[OF hall])
    have hcases: "J\<^sub>N = {} \<or> (\<exists>x. J\<^sub>N = {x})"
      using connected_finite_iff_sing[OF hJ\<^sub>N_connected_HOL] hfin by (by100 blast)
    show "\<exists>x. J\<^sub>N = {x}"
      using hcases hJ\<^sub>N_nonempty by (by100 blast)
  qed
  have hJ\<^sub>N_uncovered_all_imp_eq_P:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow> J\<^sub>N = {P}"
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    obtain x where hx: "J\<^sub>N = {x}"
      using hJ\<^sub>N_uncovered_all_imp_singleton[OF hall] by (by100 blast)
    have hxP: "x = P"
      using hx hP_J\<^sub>N by (by100 blast)
    show "J\<^sub>N = {P}"
      using hx hxP by (by100 simp)
  qed
  have hJ\<^sub>N_uncovered_all_imp_P_uncovered:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N
        \<Longrightarrow> P \<in> J\<^sub>N - geotop_polyhedron BdJ\<^sub>N"
    using hP_J\<^sub>N by (by100 simp)
  have hJ\<^sub>N_uncovered_all_imp_P_not_BdJ:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N
        \<Longrightarrow> P \<notin> geotop_polyhedron BdJ\<^sub>N"
    using hJ\<^sub>N_uncovered_all_imp_P_uncovered by (by100 blast)
  have hJ\<^sub>N_uncovered_all_imp_P_vertex:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N
        \<Longrightarrow> P \<in> geotop_complex_vertices K\<^sub>N"
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    have hP_unc: "P \<in> J\<^sub>N - geotop_polyhedron BdJ\<^sub>N"
      by (rule hJ\<^sub>N_uncovered_all_imp_P_uncovered[OF hall])
    show "P \<in> geotop_complex_vertices K\<^sub>N"
      by (rule subsetD[OF hJ\<^sub>N_uncovered_sub_vertices hP_unc])
  qed
  have hJ\<^sub>N_uncovered_all_imp_P_carrier_dim0:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N
        \<Longrightarrow> geotop_simplex_dim (geotop_K_carrier K\<^sub>N P) 0"
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    obtain n where hn_le: "n \<le> 1"
      and hdim: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N P) n"
      using hJ\<^sub>N_carrier_dim_le1[OF hP_J\<^sub>N] by (by100 blast)
    have hn_not1: "n \<noteq> 1"
    proof
      assume hn1: "n = 1"
      have hdim1: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N P) 1"
        using hdim hn1 by (by100 simp)
      have hP_BdJ: "P \<in> geotop_polyhedron BdJ\<^sub>N"
        by (rule hJ\<^sub>N_carrier_edge_point_in_BdJ\<^sub>N_poly[OF hP_J\<^sub>N hdim1])
      have hP_not_BdJ: "P \<notin> geotop_polyhedron BdJ\<^sub>N"
        by (rule hJ\<^sub>N_uncovered_all_imp_P_not_BdJ[OF hall])
      show False
        using hP_BdJ hP_not_BdJ by (by100 blast)
    qed
    have hn0: "n = 0"
      using hn_le hn_not1 by (by100 linarith)
    show "geotop_simplex_dim (geotop_K_carrier K\<^sub>N P) 0"
      using hdim hn0 by (by100 simp)
  qed
  have hJ\<^sub>N_uncovered_all_imp_P_incident_edge:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N
        \<Longrightarrow> \<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> P \<in> e"
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    have hdim0: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N P) 0"
      by (rule hJ\<^sub>N_uncovered_all_imp_P_carrier_dim0[OF hall])
    show "\<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> P \<in> e"
      by (rule hJ\<^sub>N_carrier_dim0_incident_edge[OF hP_J\<^sub>N hdim0])
  qed
  have hJ\<^sub>N_uncovered_all_imp_incident_edge_not_one:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow>
        e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> P \<in> e \<Longrightarrow>
        card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} \<noteq> 1"
    for e
  proof
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
      and heK: "e \<in> K\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      and hcard1:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} = 1"
    have heBdK: "e \<in> BdK\<^sub>N"
      by (rule hK\<^sub>N_one_incident_edge_member_BdK\<^sub>N
          [OF heK hedge hcard1])
    have hmeet: "e \<inter> J\<^sub>N \<noteq> {}"
      using hP_e hP_J\<^sub>N by (by100 blast)
    have heBdJ: "e \<in> BdJ\<^sub>N"
      by (rule hBdK\<^sub>N_edge_meets_J\<^sub>N_in_BdJ\<^sub>N[OF heBdK hedge hmeet])
    have hP_BdJ: "P \<in> geotop_polyhedron BdJ\<^sub>N"
      unfolding geotop_polyhedron_def using heBdJ hP_e by (by100 blast)
    have hP_not_BdJ: "P \<notin> geotop_polyhedron BdJ\<^sub>N"
      by (rule hJ\<^sub>N_uncovered_all_imp_P_not_BdJ[OF hall])
    show False
      using hP_BdJ hP_not_BdJ by (by100 blast)
  qed
  have hJ\<^sub>N_uncovered_all_imp_incident_edge_two:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow>
        e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> P \<in> e \<Longrightarrow>
        card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} = 2"
    for e
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
      and heK: "e \<in> K\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
    have he_simplex: "geotop_is_simplex e"
      using hedge unfolding geotop_is_edge_def
      by (rule geotop_simplex_dim_imp_is_simplex)
    obtain q where hq_rel: "q \<in> rel_interior e"
      using geotop_simplex_rel_interior_nonempty[OF he_simplex] by (by100 blast)
    have hge1:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} \<ge> 1"
      by (rule hK\<^sub>N_edge_rel_interior_incident_count_ge1
          [OF heK hedge hq_rel])
    have hle2:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} \<le> 2"
      by (rule hK\<^sub>N_edge_incident_2faces_card_le2[OF heK hedge])
    have hnot1:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} \<noteq> 1"
      by (rule hJ\<^sub>N_uncovered_all_imp_incident_edge_not_one
          [OF hall heK hedge hP_e])
    show ?thesis
      using hge1 hle2 hnot1 by (by100 linarith)
  qed
  have hJ\<^sub>N_uncovered_all_imp_P_two_incident_edge:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow>
        \<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> P \<in> e
          \<and> card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} = 2"
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    obtain e where heK: "e \<in> K\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      using hJ\<^sub>N_uncovered_all_imp_P_incident_edge[OF hall]
      by (by100 blast)
    have htwo:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} = 2"
      by (rule hJ\<^sub>N_uncovered_all_imp_incident_edge_two
          [OF hall heK hedge hP_e])
    show ?thesis
      using heK hedge hP_e htwo by (intro bexI[where x=e] conjI)
  qed
  have hJ\<^sub>N_uncovered_all_imp_P_all_incident_edges_two:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow>
        \<forall>e\<in>K\<^sub>N. geotop_is_edge e \<and> P \<in> e \<longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} = 2"
  proof (intro ballI impI)
    fix e
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
      and heK: "e \<in> K\<^sub>N"
      and he_inc: "geotop_is_edge e \<and> P \<in> e"
    have hedge: "geotop_is_edge e"
      using he_inc by (by100 blast)
    have hP_e: "P \<in> e"
      using he_inc by (by100 blast)
    show "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} = 2"
      by (rule hJ\<^sub>N_uncovered_all_imp_incident_edge_two
          [OF hall heK hedge hP_e])
  qed
  have hP_boundary_K\<^sub>N_one_incident_edge:
      "\<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> P \<in> e
        \<and> card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} = 1"
  proof -
    have hSd_poly_disk:
        "geotop_polyhedron (geotop_iterated_Sd m K) =
          closure_on UNIV geotop_euclidean_topology
            (geotop_polygon_interior J)"
      using hSd_poly hK_poly by (by100 simp)
    have hboundary_cover:
        "J \<subseteq> \<Union>{e\<in>geotop_iterated_Sd m K.
          geotop_is_edge e \<and> e \<subseteq> J}"
      by (rule geotop_polygon_disk_boundary_subset_selected_edges_prefix
          [OF hJ hSd_complex hSd_poly_disk])
    have hP_cover:
        "P \<in> \<Union>{e\<in>geotop_iterated_Sd m K.
          geotop_is_edge e \<and> e \<subseteq> J}"
      using hboundary_cover hP by (by100 blast)
    obtain e where he_sel:
        "e \<in> {e\<in>geotop_iterated_Sd m K. geotop_is_edge e \<and> e \<subseteq> J}"
      and hP_e: "P \<in> e"
      using hP_cover by (by100 blast)
    have heSd: "e \<in> geotop_iterated_Sd m K"
      using he_sel by (by100 simp)
    have hedge: "geotop_is_edge e"
      using he_sel by (by100 simp)
    have heJ: "e \<subseteq> J"
      using he_sel by (by100 simp)
    have heA1: "e \<inter> A1 \<noteq> {}"
      using hP_e hP_in_A1 by (by100 blast)
    have he_sub_N: "e \<subseteq> N"
      unfolding hN_def using heSd heA1 by (by100 blast)
    have heK\<^sub>N: "e \<in> K\<^sub>N"
      unfolding K\<^sub>N_def using heSd he_sub_N by (by100 simp)
    obtain \<sigma> where h\<sigma>Sd: "\<sigma> \<in> geotop_iterated_Sd m K"
      and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
      and heface\<sigma>: "geotop_is_face e \<sigma>"
      using geotop_polygon_disk_boundary_edge_owned_by_2simplex_prefix
        [OF hJ hSd_complex hSd_poly_disk heSd hedge heJ]
      by (elim bexE conjE)
    have hfaces_Sd:
        "{\<rho>\<in>geotop_iterated_Sd m K.
            geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>}"
      by (rule geotop_polygon_disk_boundary_edge_unique_incident_2simplex_prefix
          [OF hJ hSd_complex hSd_poly_disk heSd hedge h\<sigma>Sd h\<sigma>2 heface\<sigma> heJ])
    have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
      by (rule geotop_is_face_imp_subset_prefix[OF heface\<sigma>])
    have hP_\<sigma>: "P \<in> \<sigma>"
      using hP_e he_sub_\<sigma> by (by100 blast)
    have h\<sigma>A1: "\<sigma> \<inter> A1 \<noteq> {}"
      using hP_\<sigma> hP_in_A1 by (by100 blast)
    have h\<sigma>subN: "\<sigma> \<subseteq> N"
      unfolding hN_def using h\<sigma>Sd h\<sigma>A1 by (by100 blast)
    have h\<sigma>K\<^sub>N: "\<sigma> \<in> K\<^sub>N"
      unfolding K\<^sub>N_def using h\<sigma>Sd h\<sigma>subN by (by100 simp)
    let ?F = "{\<rho>\<in>K\<^sub>N. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
    have hF_eq: "?F = {\<sigma>}"
    proof
      show "?F \<subseteq> {\<sigma>}"
      proof
        fix \<rho>
        assume h\<rho>F: "\<rho> \<in> ?F"
        have h\<rho>Sd: "\<rho> \<in> geotop_iterated_Sd m K"
          using h\<rho>F unfolding K\<^sub>N_def by (by100 simp)
        have h\<rho>2: "geotop_simplex_dim \<rho> 2"
          using h\<rho>F by (by100 simp)
        have h\<rho>face: "geotop_is_face e \<rho>"
          using h\<rho>F by (by100 simp)
        have h\<rho>full:
            "\<rho> \<in> {\<rho>\<in>geotop_iterated_Sd m K.
              geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
          using h\<rho>Sd h\<rho>2 h\<rho>face by (by100 simp)
        show "\<rho> \<in> {\<sigma>}"
          using hfaces_Sd h\<rho>full by (by100 simp)
      qed
      show "{\<sigma>} \<subseteq> ?F"
        using h\<sigma>K\<^sub>N h\<sigma>2 heface\<sigma> by (by100 simp)
    qed
    have hcard1: "card ?F = 1"
      using hF_eq by (by100 simp)
    show ?thesis
      using heK\<^sub>N hedge hP_e hcard1 by (intro bexI[where x=e] conjI)
  qed
  have hJ\<^sub>N_uncovered_all_false:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow> False"
  proof -
    assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
    obtain e where heK: "e \<in> K\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      and hcard1:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} = 1"
      using hP_boundary_K\<^sub>N_one_incident_edge by (by100 blast)
    have hnot1:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} \<noteq> 1"
      by (rule hJ\<^sub>N_uncovered_all_imp_incident_edge_not_one
          [OF hall heK hedge hP_e])
    show False
      using hcard1 hnot1 by (by100 blast)
  qed
  have hJ\<^sub>N_uncovered_empty:
      "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = {}"
    using hJ\<^sub>N_uncovered_empty_or_all hJ\<^sub>N_uncovered_all_false
    by (by100 blast)
  have hJ\<^sub>N_eq_BdJ\<^sub>N_poly:
      "J\<^sub>N = geotop_polyhedron BdJ\<^sub>N"
    using hJ\<^sub>N_uncovered_empty hBdJ\<^sub>N_poly_sub_J\<^sub>N by (by100 blast)
  have hBdJ\<^sub>N_poly_connected_HOL:
      "connected (geotop_polyhedron BdJ\<^sub>N)"
    using hJ\<^sub>N_connected_HOL hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
  have hBdJ\<^sub>N_poly_connected:
      "top1_connected_on (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N))"
    using hBdJ\<^sub>N_poly_connected_HOL top1_connected_on_geotop_iff_connected
    by (by100 blast)
  have hBdJ\<^sub>N_poly_path_connected:
      "top1_path_connected_on (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N))"
    by (rule iffD2[OF Theorem_GT_1_12(2)[OF hBdJ\<^sub>N_complex]
          hBdJ\<^sub>N_poly_connected])
  have hBdJ\<^sub>N_connected: "geotop_complex_connected BdJ\<^sub>N"
    by (rule iffD2[OF Theorem_GT_1_12(1)[OF hBdJ\<^sub>N_complex]
          hBdJ\<^sub>N_poly_path_connected])
  have hBdJ\<^sub>N_poly_nonempty: "geotop_polyhedron BdJ\<^sub>N \<noteq> {}"
    using hP_J\<^sub>N hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 blast)
  have hBdJ\<^sub>N_nonempty: "BdJ\<^sub>N \<noteq> {}"
    using hBdJ\<^sub>N_poly_nonempty unfolding geotop_polyhedron_def by (by100 blast)
  have hP_BdJ\<^sub>N_poly: "P \<in> geotop_polyhedron BdJ\<^sub>N"
    using hP_J\<^sub>N hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
  have hBdJ\<^sub>N_P_incident_edge:
      "\<exists>e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> P \<in> e"
  proof -
    obtain e where heK: "e \<in> K\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      and hcard1:
        "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
          \<and> geotop_is_face e \<sigma>} = 1"
      using hP_boundary_K\<^sub>N_one_incident_edge by (by100 blast)
    have heBdK: "e \<in> BdK\<^sub>N"
      by (rule hK\<^sub>N_one_incident_edge_member_BdK\<^sub>N
          [OF heK hedge hcard1])
    have hmeet: "e \<inter> J\<^sub>N \<noteq> {}"
      using hP_e hP_J\<^sub>N by (by100 blast)
    have heBdJ: "e \<in> BdJ\<^sub>N"
      by (rule hBdK\<^sub>N_edge_meets_J\<^sub>N_in_BdJ\<^sub>N[OF heBdK hedge hmeet])
    show ?thesis
      using heBdJ hedge hP_e by (intro bexI[where x=e] conjI)
  qed
  have hBdJ\<^sub>N_P_boundary_edge:
      "\<exists>e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> P \<in> e \<and> e \<subseteq> J"
    (**
      Book B1 start: the frontier component through \<open>P\<close> contains the
      actual fine-subdivision boundary edge of the polygonal disk through
      \<open>P\<close>, not merely an abstract incident edge of the extracted graph. **)
  proof -
    have hSd_poly_disk:
        "geotop_polyhedron (geotop_iterated_Sd m K) =
          closure_on UNIV geotop_euclidean_topology
            (geotop_polygon_interior J)"
      using hSd_poly hK_poly by (by100 simp)
    have hboundary_cover:
        "J \<subseteq> \<Union>{e\<in>geotop_iterated_Sd m K.
          geotop_is_edge e \<and> e \<subseteq> J}"
      by (rule geotop_polygon_disk_boundary_subset_selected_edges_prefix
          [OF hJ hSd_complex hSd_poly_disk])
    have hP_cover:
        "P \<in> \<Union>{e\<in>geotop_iterated_Sd m K.
          geotop_is_edge e \<and> e \<subseteq> J}"
      using hboundary_cover hP by (by100 blast)
    obtain e where he_sel:
        "e \<in> {e\<in>geotop_iterated_Sd m K. geotop_is_edge e \<and> e \<subseteq> J}"
      and hP_e: "P \<in> e"
      using hP_cover by (by100 blast)
    have heSd: "e \<in> geotop_iterated_Sd m K"
      using he_sel by (by100 simp)
    have hedge: "geotop_is_edge e"
      using he_sel by (by100 simp)
    have heJ: "e \<subseteq> J"
      using he_sel by (by100 simp)
    have heA1: "e \<inter> A1 \<noteq> {}"
      using hP_e hP_in_A1 by (by100 blast)
    have he_sub_N: "e \<subseteq> N"
      unfolding hN_def using heSd heA1 by (by100 blast)
    have heK\<^sub>N: "e \<in> K\<^sub>N"
      unfolding K\<^sub>N_def using heSd he_sub_N by (by100 simp)
    obtain \<sigma> where h\<sigma>Sd: "\<sigma> \<in> geotop_iterated_Sd m K"
      and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
      and heface\<sigma>: "geotop_is_face e \<sigma>"
      using geotop_polygon_disk_boundary_edge_owned_by_2simplex_prefix
        [OF hJ hSd_complex hSd_poly_disk heSd hedge heJ]
      by (elim bexE conjE)
    have hfaces_Sd:
        "{\<rho>\<in>geotop_iterated_Sd m K.
            geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>}"
      by (rule geotop_polygon_disk_boundary_edge_unique_incident_2simplex_prefix
          [OF hJ hSd_complex hSd_poly_disk heSd hedge h\<sigma>Sd h\<sigma>2 heface\<sigma> heJ])
    have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
      by (rule geotop_is_face_imp_subset_prefix[OF heface\<sigma>])
    have hP_\<sigma>: "P \<in> \<sigma>"
      using hP_e he_sub_\<sigma> by (by100 blast)
    have h\<sigma>A1: "\<sigma> \<inter> A1 \<noteq> {}"
      using hP_\<sigma> hP_in_A1 by (by100 blast)
    have h\<sigma>subN: "\<sigma> \<subseteq> N"
      unfolding hN_def using h\<sigma>Sd h\<sigma>A1 by (by100 blast)
    have h\<sigma>K\<^sub>N: "\<sigma> \<in> K\<^sub>N"
      unfolding K\<^sub>N_def using h\<sigma>Sd h\<sigma>subN by (by100 simp)
    let ?F = "{\<rho>\<in>K\<^sub>N. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
    have hF_eq: "?F = {\<sigma>}"
    proof
      show "?F \<subseteq> {\<sigma>}"
      proof
        fix \<rho>
        assume h\<rho>F: "\<rho> \<in> ?F"
        have h\<rho>Sd: "\<rho> \<in> geotop_iterated_Sd m K"
          using h\<rho>F unfolding K\<^sub>N_def by (by100 simp)
        have h\<rho>2: "geotop_simplex_dim \<rho> 2"
          using h\<rho>F by (by100 simp)
        have h\<rho>face: "geotop_is_face e \<rho>"
          using h\<rho>F by (by100 simp)
        have h\<rho>full:
            "\<rho> \<in> {\<rho>\<in>geotop_iterated_Sd m K.
              geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
          using h\<rho>Sd h\<rho>2 h\<rho>face by (by100 simp)
        show "\<rho> \<in> {\<sigma>}"
          using hfaces_Sd h\<rho>full by (by100 simp)
      qed
      show "{\<sigma>} \<subseteq> ?F"
        using h\<sigma>K\<^sub>N h\<sigma>2 heface\<sigma> by (by100 simp)
    qed
    have hcard1: "card ?F = 1"
      using hF_eq by (by100 simp)
    have heBdK: "e \<in> BdK\<^sub>N"
      by (rule hK\<^sub>N_one_incident_edge_member_BdK\<^sub>N
          [OF heK\<^sub>N hedge hcard1])
    have hmeet: "e \<inter> J\<^sub>N \<noteq> {}"
      using hP_e hP_J\<^sub>N by (by100 blast)
    have heBdJ: "e \<in> BdJ\<^sub>N"
      by (rule hBdK\<^sub>N_edge_meets_J\<^sub>N_in_BdJ\<^sub>N[OF heBdK hedge hmeet])
    show ?thesis
      using heBdJ hedge hP_e heJ by (intro bexI[where x=e] conjI)
  qed
  have hBdJ\<^sub>N_poly_not_singleton:
      "\<And>w. geotop_polyhedron BdJ\<^sub>N \<noteq> {w}"
  proof
    fix w
    assume hpoly_single: "geotop_polyhedron BdJ\<^sub>N = {w}"
    obtain e where heBdJ: "e \<in> BdJ\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      using hBdJ\<^sub>N_P_incident_edge by (by100 blast)
    have he_sub_poly: "e \<subseteq> geotop_polyhedron BdJ\<^sub>N"
      unfolding geotop_polyhedron_def using heBdJ by (by100 blast)
    have hP_w: "P = w"
      using hP_e he_sub_poly hpoly_single by (by100 blast)
    have he_sub_singleP: "e \<subseteq> {P}"
      using he_sub_poly hpoly_single hP_w by (by100 simp)
    have he_eq_singleP: "e = {P}"
      using hP_e he_sub_singleP by (by100 blast)
    have "geotop_is_edge {P}"
      using hedge he_eq_singleP by (by100 simp)
    thus False
      using geotop_singleton_not_edge_prefix by (by100 blast)
  qed
  have hBdJ\<^sub>N_vertex_incident_edge:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        \<exists>e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e"
  proof (rule ccontr)
    fix w
    assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
      and hno: "\<not> (\<exists>e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e)"
    have hw_vertex: "w \<in> geotop_complex_vertices BdJ\<^sub>N"
      using geotop_complex_vertices_eq_0_simplexes[OF hBdJ\<^sub>N_complex] hwBdJ
      by (by100 blast)
    have hsingle_top:
        "{w} \<in>
          subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron BdJ\<^sub>N)"
      by (rule geotop_complex_no_incident_edge_vertex_open_singleton_prefix
          [OF hBdJ\<^sub>N_complex hw_vertex hno])
    obtain U where hsingle_eq:
        "{w} = geotop_polyhedron BdJ\<^sub>N \<inter> U"
      and hU_top: "U \<in> geotop_euclidean_topology"
      using hsingle_top unfolding subspace_topology_def by (by100 blast)
    have hU_open: "open U"
      using hU_top unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    have hsingle_openin:
        "openin (top_of_set (geotop_polyhedron BdJ\<^sub>N)) {w}"
      unfolding openin_open
      using hU_open hsingle_eq by (by100 blast)
    have hw_poly: "w \<in> geotop_polyhedron BdJ\<^sub>N"
      unfolding geotop_polyhedron_def using hwBdJ by (by100 blast)
    have hsingle_closedin:
        "closedin (top_of_set (geotop_polyhedron BdJ\<^sub>N)) {w}"
    proof -
      have hclosed_single: "closed {w}"
        by (by100 simp)
      have hsingle_eq_poly:
          "{w} = geotop_polyhedron BdJ\<^sub>N \<inter> {w}"
        using hw_poly by (by100 blast)
      show ?thesis
        unfolding closedin_closed
        using hclosed_single hsingle_eq_poly by (by100 blast)
    qed
    have hsingle_cases:
        "{w} = {} \<or> {w} = geotop_polyhedron BdJ\<^sub>N"
      using connected_clopen[THEN iffD1, OF hBdJ\<^sub>N_poly_connected_HOL]
        hsingle_openin hsingle_closedin by (by100 blast)
    have hpoly_single: "geotop_polyhedron BdJ\<^sub>N = {w}"
      using hsingle_cases by (by100 blast)
    show False
      using hBdJ\<^sub>N_poly_not_singleton[of w] hpoly_single by (by100 blast)
  qed
  have hBdJ\<^sub>N_vertex_incident_edge_card_ge1:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 1"
  proof -
    fix w
    assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
    obtain e where heBdJ: "e \<in> BdJ\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hw_e: "w \<in> e"
      using hBdJ\<^sub>N_vertex_incident_edge[OF hwBdJ] by (by100 blast)
    let ?E = "{e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e}"
    have hE_fin: "finite ?E"
      by (rule finite_subset[OF _ hBdJ\<^sub>N_fin]) (by100 blast)
    have heE: "e \<in> ?E"
      using heBdJ hedge hw_e by (by100 simp)
    have hE_ne: "?E \<noteq> {}"
      using heE by (by100 blast)
    have hcard_pos: "0 < card ?E"
    proof -
      have hiff: "(0 < card ?E) = (?E \<noteq> {} \<and> finite ?E)"
        by (rule card_gt_0_iff)
      show ?thesis
        using hiff hE_ne hE_fin by (by100 blast)
    qed
    show "card ?E \<ge> 1"
      using hcard_pos by (by100 linarith)
  qed
  have hBdJ\<^sub>N_vertex_degree_one_or_two_from_card_le2:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        \<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 1
          \<or> card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
  proof (intro allI impI)
    fix w
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
    have hge1:
      "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 1"
      by (rule hBdJ\<^sub>N_vertex_incident_edge_card_ge1[OF hwBdJ])
    have hle:
      "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
      by (rule hle2[OF hwBdJ])
    show "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 1
        \<or> card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      using hge1 hle by (by100 linarith)
  qed
  have hBdJ\<^sub>N_vertex_degree_two_from_card_le2_no_endpoint:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
      (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
    \<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
      card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hnoend:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
    have hdegree12:
        "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 1
          \<or> card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule hBdJ\<^sub>N_vertex_degree_one_or_two_from_card_le2[OF hle2])
    show "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule geotop_degree_one_or_two_no_endpoint_degree_two_prefix
          [OF hBdJ\<^sub>N_linear_graph hdegree12 hnoend])
  qed
  have hBdJ\<^sub>N_vertex_no_endpoint_from_card_ge2:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2) \<Longrightarrow>
        \<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
  proof (intro allI impI)
    fix w
    assume hge2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
    assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
    show "\<not> geotop_graph_endpoint BdJ\<^sub>N w"
    proof
      assume hend: "geotop_graph_endpoint BdJ\<^sub>N w"
      have hcard1:
          "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 1"
        using geotop_graph_endpoint_singleton_and_card_one_prefix
          [OF hBdJ\<^sub>N_linear_graph hend]
        by (by100 blast)
      have hcard_ge2:
          "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
        by (rule hge2[OF hwBdJ])
      show False
        using hcard1 hcard_ge2 by (by100 linarith)
    qed
  qed
  have hBdJ\<^sub>N_vertex_card_ge2_from_no_endpoint:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
        \<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
  proof (intro allI impI)
    fix w
    assume hnoend:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
    assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
    have hge1:
      "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 1"
      by (rule hBdJ\<^sub>N_vertex_incident_edge_card_ge1[OF hwBdJ])
    show "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
    proof (rule ccontr)
      assume hnot_ge2:
        "\<not> 2 \<le> card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e}"
      have hcard1:
          "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 1"
        using hge1 hnot_ge2 by (by100 linarith)
      have hend: "geotop_graph_endpoint BdJ\<^sub>N w"
        by (rule geotop_degree_one_vertex_graph_endpoint_prefix
            [OF hBdJ\<^sub>N_linear_graph hwBdJ hcard1])
      have hnot: "\<not> geotop_graph_endpoint BdJ\<^sub>N w"
        using hnoend hwBdJ by (by100 blast)
      show False
        using hend hnot by (by100 blast)
    qed
  qed
  have hBdJ\<^sub>N_vertex_degree_two_from_card_bounds:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
      (\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2) \<Longrightarrow>
        \<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
  proof (intro allI impI)
    fix w
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hge2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
    assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
    have hle:
      "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
      by (rule hle2[OF hwBdJ])
    have hge:
      "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
      by (rule hge2[OF hwBdJ])
    show "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      using hle hge by (by100 linarith)
  qed
  have hBdJ\<^sub>N_two_distinct_vertices:
      "\<exists>u v. {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v"
  proof -
    obtain e where heBdJ: "e \<in> BdJ\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      using hBdJ\<^sub>N_P_incident_edge by (by100 blast)
    have he_dim: "geotop_simplex_dim e 1"
      using hedge unfolding geotop_is_edge_def by (by100 simp)
    obtain V m where hV_fin: "finite V"
      and hV_card: "card V = 1 + 1"
      and h1_le_m: "1 \<le> m"
      and hgp_V: "geotop_general_position V m"
      and he_eq: "e = geotop_convex_hull V"
      using he_dim unfolding geotop_simplex_dim_def by (by100 blast)
    have heV: "geotop_simplex_vertices e V"
      unfolding geotop_simplex_vertices_def
      using hV_fin hV_card h1_le_m hgp_V he_eq by (by100 blast)
    have hV_card2: "card V = 2"
      using hV_card by (by100 simp)
    have hV_pair_ex:
        "\<exists>u v. V = {u, v} \<and> u \<noteq> v"
      by (rule iffD1[OF card_2_iff hV_card2])
    obtain u v where hV_eq: "V = {u, v}"
      and huv: "u \<noteq> v"
      using hV_pair_ex by (elim exE conjE)
    have huv_BdJ:
        "{u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N"
      by (fact geotop_subdivide_edge_vertices_in_K
          [where K=BdJ\<^sub>N and e=e and V=V and v\<^sub>0=u and v\<^sub>1=v,
           OF hBdJ\<^sub>N_complex heBdJ heV hV_eq])
    show ?thesis
      using huv_BdJ huv by (by100 blast)
  qed
  have hBdJ\<^sub>N_cycle_split_from_degree_two:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2) \<Longrightarrow>
        \<exists>u v C\<^sub>1 C\<^sub>2.
          {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
          \<and> geotop_is_broken_line C\<^sub>1
          \<and> geotop_is_broken_line C\<^sub>2
          \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
          \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
          \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
              geotop_arc_interior C\<^sub>2 {u, v} = {}"
  proof -
    assume hdegree:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
    obtain u v where huBdJ: "{u} \<in> BdJ\<^sub>N"
      and hvBdJ: "{v} \<in> BdJ\<^sub>N"
      and huv: "u \<noteq> v"
      using hBdJ\<^sub>N_two_distinct_vertices by (by100 blast)
    obtain C\<^sub>1 C\<^sub>2 where hsplit:
        "geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
        \<and> geotop_is_broken_line C\<^sub>1
        \<and> geotop_is_broken_line C\<^sub>2
        \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
        \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
        \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
            geotop_arc_interior C\<^sub>2 {u, v} = {}"
      using geotop_finite_connected_degree_two_linear_graph_two_vertex_boundary_split_prefix
        [OF hBdJ\<^sub>N_linear_graph hBdJ\<^sub>N_fin hBdJ\<^sub>N_connected
          hdegree huBdJ hvBdJ huv]
      by (by100 blast)
    show ?thesis
      using huBdJ hvBdJ huv hsplit by (by100 blast)
  qed
  have hBdJ\<^sub>N_polygon_from_degree_two:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2) \<Longrightarrow>
        geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
  proof -
    assume hdegree:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
    obtain u v C\<^sub>1 C\<^sub>2 where huBdJ: "{u} \<in> BdJ\<^sub>N"
      and hvBdJ: "{v} \<in> BdJ\<^sub>N"
      and huv: "u \<noteq> v"
      and hpoly_eq: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2"
      and hC\<^sub>1_bl: "geotop_is_broken_line C\<^sub>1"
      and hC\<^sub>2_bl: "geotop_is_broken_line C\<^sub>2"
      and hC\<^sub>1_end: "geotop_arc_endpoints C\<^sub>1 {u, v}"
      and hC\<^sub>2_end: "geotop_arc_endpoints C\<^sub>2 {u, v}"
      and hdisj: "geotop_arc_interior C\<^sub>1 {u, v} \<inter>
          geotop_arc_interior C\<^sub>2 {u, v} = {}"
      using hBdJ\<^sub>N_cycle_split_from_degree_two[OF hdegree]
      by (by100 blast)
    have hpolygon_C: "geotop_is_polygon (C\<^sub>1 \<union> C\<^sub>2)"
      by (rule pair_of_arcs_is_polygon
          [OF hC\<^sub>1_bl hC\<^sub>2_bl hC\<^sub>1_end hC\<^sub>2_end hdisj])
    show ?thesis
      using hpolygon_C hpoly_eq by (by100 simp)
  qed
  have hBdJ\<^sub>N_polygon_from_card_bounds:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
      (\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2) \<Longrightarrow>
        geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hge2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
    have hdegree:
        "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule hBdJ\<^sub>N_vertex_degree_two_from_card_bounds[OF hle2 hge2])
    show ?thesis
      by (rule hBdJ\<^sub>N_polygon_from_degree_two[OF hdegree])
  qed
  have hBdJ\<^sub>N_polygon_from_card_le2_no_endpoint:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
      (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
        geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hnoend:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
    have hdegree:
        "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule hBdJ\<^sub>N_vertex_degree_two_from_card_le2_no_endpoint
          [OF hle2 hnoend])
    show ?thesis
      by (rule hBdJ\<^sub>N_polygon_from_degree_two[OF hdegree])
  qed
  have hBdJ\<^sub>N_polygon_from_simple_closed_curve:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
        (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
  proof -
    let ?C = "geotop_polyhedron BdJ\<^sub>N"
    let ?TC = "subspace_topology UNIV geotop_euclidean_topology ?C"
    let ?S = "(geotop_std_sphere::(real^2) set)"
    let ?TS = "subspace_topology UNIV geotop_euclidean_topology ?S"
    assume hSCC:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology ?C"
    obtain f where hf_cont_UNIV:
        "top1_continuous_map_on top1_S1 top1_S1_topology
          UNIV geotop_euclidean_topology f"
      and hfinj: "inj_on f top1_S1"
      and hf_img: "f ` top1_S1 = ?C"
      using hSCC unfolding top1_simple_closed_curve_on_def
      by (by100 blast)
    have hf_cont_C:
        "top1_continuous_map_on top1_S1 top1_S1_topology ?C ?TC f"
    proof -
      have hf_img_sub: "f ` top1_S1 \<subseteq> ?C"
        using hf_img by (by100 simp)
      show ?thesis
        by (rule top1_continuous_map_on_codomain_shrink
            [OF hf_cont_UNIV hf_img_sub subset_UNIV])
    qed
    have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
      using S1_compact by (rule compact_is_topology)
    have hUNIV_top:
        "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
      by (metis geotop_euclidean_topology_eq_open_sets
          top1_open_sets_is_topology_on_UNIV)
    have hC_top: "is_topology_on ?C ?TC"
      by (rule subspace_topology_is_topology_on[OF hUNIV_top subset_UNIV])
    have hC_haus: "is_hausdorff_on ?C ?TC"
      by (rule hausdorff_subspace
          [OF geotop_euclidean_topology_UNIV_hausdorff subset_UNIV])
    have hf_bij: "bij_betw f top1_S1 ?C"
      using hfinj hf_img unfolding bij_betw_def by (by100 blast)
    have hS1_C: "top1_homeomorphism_on top1_S1 top1_S1_topology ?C ?TC f"
      by (rule Theorem_26_6
          [OF hS1_top hC_top S1_compact hC_haus hf_cont_C hf_bij])
    have hC_S1: "top1_homeomorphism_on ?C ?TC top1_S1 top1_S1_topology
        (inv_into top1_S1 f)"
      by (rule top1_homeomorphism_on_sym[OF hS1_C])
    have hS1_std: "top1_homeomorphism_on top1_S1 top1_S1_topology ?S ?TS
        (inv_into ?S R2_to_pair)"
      by (rule top1_homeomorphism_on_sym
          [OF R2_pair_top1_homeomorphism_std_sphere_prefix])
    have hC_std: "top1_homeomorphism_on ?C ?TC ?S ?TS
        (inv_into ?S R2_to_pair \<circ> inv_into top1_S1 f)"
      by (rule top1_homeomorphism_on_comp[OF hC_S1 hS1_std])
    have hC_sphere: "geotop_is_n_sphere ?C ?TC 1"
      unfolding geotop_is_n_sphere_def
      using hC_top hC_std by (by100 blast)
    show "geotop_is_polygon ?C"
      unfolding geotop_is_polygon_def
      using hBdJ\<^sub>N_complex hC_sphere by (by100 blast)
  qed
  have hBdJ\<^sub>N_cycle_split_from_polygon:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>u v C\<^sub>1 C\<^sub>2.
          {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
          \<and> geotop_is_broken_line C\<^sub>1
          \<and> geotop_is_broken_line C\<^sub>2
          \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
          \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
          \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
              geotop_arc_interior C\<^sub>2 {u, v} = {}"
  proof -
    assume hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    obtain u v where huBdJ: "{u} \<in> BdJ\<^sub>N"
      and hvBdJ: "{v} \<in> BdJ\<^sub>N"
      and huv: "u \<noteq> v"
      using hBdJ\<^sub>N_two_distinct_vertices by (by100 blast)
    obtain C\<^sub>1 C\<^sub>2 where hsplit:
        "geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
        \<and> geotop_is_broken_line C\<^sub>1
        \<and> geotop_is_broken_line C\<^sub>2
        \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
        \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
        \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
            geotop_arc_interior C\<^sub>2 {u, v} = {}"
      using geotop_polygon_finite_linear_graph_two_vertex_boundary_split_prefix
        [OF hBdJ\<^sub>N_linear_graph hBdJ\<^sub>N_fin hBdJ\<^sub>N_connected
          hpolygon huBdJ hvBdJ huv]
      by (by100 blast)
    show ?thesis
      using huBdJ hvBdJ huv hsplit by (by100 blast)
  qed
  have hBdJ\<^sub>N_cycle_split_from_card_bounds:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
      (\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2) \<Longrightarrow>
        \<exists>u v C\<^sub>1 C\<^sub>2.
          {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
          \<and> geotop_is_broken_line C\<^sub>1
          \<and> geotop_is_broken_line C\<^sub>2
          \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
          \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
          \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
              geotop_arc_interior C\<^sub>2 {u, v} = {}"
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hge2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_card_bounds[OF hle2 hge2])
    show ?thesis
      by (rule hBdJ\<^sub>N_cycle_split_from_polygon[OF hpolygon])
  qed
  have hBdJ\<^sub>N_cycle_split_from_card_le2_no_endpoint:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
      (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
        \<exists>u v C\<^sub>1 C\<^sub>2.
          {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
          \<and> geotop_is_broken_line C\<^sub>1
          \<and> geotop_is_broken_line C\<^sub>2
          \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
          \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
          \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
              geotop_arc_interior C\<^sub>2 {u, v} = {}"
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hnoend:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_card_le2_no_endpoint[OF hle2 hnoend])
    show ?thesis
      by (rule hBdJ\<^sub>N_cycle_split_from_polygon[OF hpolygon])
  qed
  have hBdJ\<^sub>N_cycle_split_from_simple_closed_curve:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
        (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>u v C\<^sub>1 C\<^sub>2.
          {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
          \<and> geotop_is_broken_line C\<^sub>1
          \<and> geotop_is_broken_line C\<^sub>2
          \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
          \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
          \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
              geotop_arc_interior C\<^sub>2 {u, v} = {}"
  proof -
    assume hSCC:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
        (geotop_polyhedron BdJ\<^sub>N)"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_simple_closed_curve[OF hSCC])
    show ?thesis
      by (rule hBdJ\<^sub>N_cycle_split_from_polygon[OF hpolygon])
  qed
  have hBdJ\<^sub>N_poly_A2_QS_disj:
      "geotop_polyhedron BdJ\<^sub>N \<inter> (A2 \<union> {Q, S}) = {}"
    using hBdJ\<^sub>N_poly_sub_J\<^sub>N hJ\<^sub>N_A2_QS_disj by (by100 blast)
  have hball_Q_FrN\<^sub>I_disj: "ball Q r \<inter> FrN\<^sub>I = {}"
    using hball_Q_N hFrN\<^sub>I_sub_N by (by100 blast)
  have hball_S_FrN\<^sub>I_disj: "ball S r \<inter> FrN\<^sub>I = {}"
    using hball_S_N hFrN\<^sub>I_sub_N by (by100 blast)
  have hball_Q_J\<^sub>N_disj: "ball Q r \<inter> J\<^sub>N = {}"
    using hball_Q_N hJ\<^sub>N_sub_N by (by100 blast)
  have hball_S_J\<^sub>N_disj: "ball S r \<inter> J\<^sub>N = {}"
    using hball_S_N hJ\<^sub>N_sub_N by (by100 blast)
  have hball_Q_BdJ\<^sub>N_poly_disj:
      "ball Q r \<inter> geotop_polyhedron BdJ\<^sub>N = {}"
    using hball_Q_J\<^sub>N_disj hBdJ\<^sub>N_poly_sub_J\<^sub>N by (by100 blast)
  have hball_S_BdJ\<^sub>N_poly_disj:
      "ball S r \<inter> geotop_polyhedron BdJ\<^sub>N = {}"
    using hball_S_J\<^sub>N_disj hBdJ\<^sub>N_poly_sub_J\<^sub>N by (by100 blast)
  have hQ_not_BdJ\<^sub>N_poly: "Q \<notin> geotop_polyhedron BdJ\<^sub>N"
    using hBdJ\<^sub>N_poly_A2_QS_disj by (by100 blast)
  have hS_not_BdJ\<^sub>N_poly: "S \<notin> geotop_polyhedron BdJ\<^sub>N"
    using hBdJ\<^sub>N_poly_A2_QS_disj by (by100 blast)
  have hR_not_BdJ\<^sub>N_poly: "R \<notin> geotop_polyhedron BdJ\<^sub>N"
    using hR_in_A2 hBdJ\<^sub>N_poly_A2_QS_disj by (by100 blast)
  have hBdK\<^sub>N_poly_A2_QS_disj:
      "geotop_polyhedron BdK\<^sub>N \<inter> (A2 \<union> {Q, S}) = {}"
    using hBdK\<^sub>N_poly_sub_N hN_avoid by (by100 blast)
  have hQ_not_BdK\<^sub>N_poly: "Q \<notin> geotop_polyhedron BdK\<^sub>N"
    using hBdK\<^sub>N_poly_A2_QS_disj by (by100 blast)
  have hS_not_BdK\<^sub>N_poly: "S \<notin> geotop_polyhedron BdK\<^sub>N"
    using hBdK\<^sub>N_poly_A2_QS_disj by (by100 blast)
  have hR_not_BdK\<^sub>N_poly: "R \<notin> geotop_polyhedron BdK\<^sub>N"
    using hR_in_A2 hBdK\<^sub>N_poly_A2_QS_disj by (by100 blast)
  have hQ1_not_N: "Q1 \<notin> N"
    using hQ1_Ncut by (by100 blast)
  have hS1_not_N: "S1 \<notin> N"
    using hS1_Ncut by (by100 blast)
  have hQ1_not_A2: "Q1 \<notin> A2"
    using hQ1_Ncut by (by100 blast)
  have hS1_not_A2: "S1 \<notin> A2"
    using hS1_Ncut by (by100 blast)
  have hQ1_I: "Q1 \<in> geotop_polygon_interior J"
    using hQ1_Ncut by (by100 blast)
  have hS1_I: "S1 \<in> geotop_polygon_interior J"
    using hS1_Ncut by (by100 blast)
  have hQ1_not_FrN\<^sub>I: "Q1 \<notin> FrN\<^sub>I"
    using hQ1_not_N hFrN\<^sub>I_sub_N by (by100 blast)
  have hS1_not_FrN\<^sub>I: "S1 \<notin> FrN\<^sub>I"
    using hS1_not_N hFrN\<^sub>I_sub_N by (by100 blast)
  have hQ1_not_J\<^sub>N: "Q1 \<notin> J\<^sub>N"
    using hQ1_not_N hJ\<^sub>N_sub_N by (by100 blast)
  have hS1_not_J\<^sub>N: "S1 \<notin> J\<^sub>N"
    using hS1_not_N hJ\<^sub>N_sub_N by (by100 blast)
  have hQ1_not_A1: "Q1 \<notin> A1"
    using hQ1_not_N hA1_N by (by100 blast)
  have hS1_not_A1: "S1 \<notin> A1"
    using hS1_not_N hA1_N by (by100 blast)
  have hQ1_not_K\<^sub>N_poly: "Q1 \<notin> geotop_polyhedron K\<^sub>N"
    using hQ1_not_N hK\<^sub>N_poly_N\<^sub>I hN\<^sub>I_eq_N by (by100 simp)
  have hS1_not_K\<^sub>N_poly: "S1 \<notin> geotop_polyhedron K\<^sub>N"
    using hS1_not_N hK\<^sub>N_poly_N\<^sub>I hN\<^sub>I_eq_N by (by100 simp)
  have hQ1_not_BdK\<^sub>N_poly: "Q1 \<notin> geotop_polyhedron BdK\<^sub>N"
    using hQ1_not_N hBdK\<^sub>N_poly_sub_N by (by100 blast)
  have hS1_not_BdK\<^sub>N_poly: "S1 \<notin> geotop_polyhedron BdK\<^sub>N"
    using hS1_not_N hBdK\<^sub>N_poly_sub_N by (by100 blast)
  have hNcut_N_disj: "?Ncut \<inter> N = {}"
    by (by100 blast)
  have hNcut_FrN\<^sub>I_disj: "?Ncut \<inter> FrN\<^sub>I = {}"
    using hFrN\<^sub>I_sub_N by (by100 blast)
  have hNcut_J\<^sub>N_disj: "?Ncut \<inter> J\<^sub>N = {}"
    using hJ\<^sub>N_sub_N by (by100 blast)
  have hNcut_BdJ\<^sub>N_poly_disj:
      "?Ncut \<inter> geotop_polyhedron BdJ\<^sub>N = {}"
    using hBdJ\<^sub>N_poly_sub_J\<^sub>N hJ\<^sub>N_sub_N by (by100 blast)
  have hQ1_not_BdJ\<^sub>N_poly:
      "Q1 \<notin> geotop_polyhedron BdJ\<^sub>N"
    using hQ1_Ncut hNcut_BdJ\<^sub>N_poly_disj by (by100 blast)
  have hS1_not_BdJ\<^sub>N_poly:
      "S1 \<notin> geotop_polyhedron BdJ\<^sub>N"
    using hS1_Ncut hNcut_BdJ\<^sub>N_poly_disj by (by100 blast)
  have hQ_ne_S: "Q \<noteq> S"
  proof
    assume hQS: "Q = S"
    have "card {P, Q, R, S} \<le> 3"
      by (simp add: hQS card_insert_if)
    thus False
      using hcard by (by100 simp)
  qed
  have hQ_ne_PR: "Q \<noteq> P \<and> Q \<noteq> R"
  proof
    show "Q \<noteq> P"
    proof
      assume hQP: "Q = P"
      have "card {P, Q, R, S} \<le> 3"
        by (simp add: hQP card_insert_if)
      thus False
        using hcard by (by100 simp)
    qed
    show "Q \<noteq> R"
    proof
      assume hQR: "Q = R"
      have "card {P, Q, R, S} \<le> 3"
        by (simp add: hQR card_insert_if)
      thus False
        using hcard by (by100 simp)
    qed
  qed
  have hS_ne_PR: "S \<noteq> P \<and> S \<noteq> R"
  proof
    show "S \<noteq> P"
    proof
      assume hSP: "S = P"
      have "card {P, Q, R, S} \<le> 3"
        by (simp add: hSP card_insert_if)
      thus False
        using hcard by (by100 simp)
    qed
    show "S \<noteq> R"
    proof
      assume hSR: "S = R"
      have "card {P, Q, R, S} \<le> 3"
        by (simp add: hSR card_insert_if)
      thus False
        using hcard by (by100 simp)
    qed
  qed
  have hD44_QS_broken_boundary_arc_split:
      "\<exists>F\<^sub>1 F\<^sub>2.
        J = F\<^sub>1 \<union> F\<^sub>2
        \<and> geotop_is_broken_line F\<^sub>1
        \<and> geotop_is_broken_line F\<^sub>2
        \<and> geotop_arc_endpoints F\<^sub>1 {Q, S}
        \<and> geotop_arc_endpoints F\<^sub>2 {Q, S}
        \<and> geotop_arc_interior F\<^sub>1 {Q, S} \<inter>
            geotop_arc_interior F\<^sub>2 {Q, S} = {}
        \<and> P \<in> geotop_arc_interior F\<^sub>1 {Q, S}"
  proof -
    obtain L where hL_linear: "geotop_is_linear_graph L"
      and hL_fin: "finite L"
      and hL_conn: "geotop_complex_connected L"
      and hL_poly: "geotop_polyhedron L = J"
      and hQL: "{Q} \<in> L"
      and hSL: "{S} \<in> L"
      using geotop_polygon_finite_connected_linear_graph_with_two_vertices_prefix
        [OF hJ hQ hS]
      by (by100 blast)
    have hL_polygon: "geotop_is_polygon (geotop_polyhedron L)"
      using hJ hL_poly by (by100 simp)
    have hP_not_QS: "P \<notin> {Q, S}"
      using hQ_ne_PR hS_ne_PR by (by100 blast)
    have hP_poly_L: "P \<in> geotop_polyhedron L"
      using hP hL_poly by (by100 simp)
    obtain F\<^sub>1 F\<^sub>2 where hsplit:
        "geotop_polyhedron L = F\<^sub>1 \<union> F\<^sub>2
        \<and> geotop_is_broken_line F\<^sub>1
        \<and> geotop_is_broken_line F\<^sub>2
        \<and> geotop_arc_endpoints F\<^sub>1 {Q, S}
        \<and> geotop_arc_endpoints F\<^sub>2 {Q, S}
        \<and> geotop_arc_interior F\<^sub>1 {Q, S} \<inter>
            geotop_arc_interior F\<^sub>2 {Q, S} = {}
        \<and> P \<in> geotop_arc_interior F\<^sub>1 {Q, S}"
      using geotop_polygon_finite_linear_graph_two_vertex_boundary_split_through_point_prefix
        [OF hL_linear hL_fin hL_conn hL_polygon hQL hSL hQ_ne_S hP_poly_L hP_not_QS]
      by (by100 blast)
    show ?thesis
      using hsplit hL_poly by (by100 blast)
  qed
  obtain F\<^sub>1 F\<^sub>2 where hD44_F_J_split: "J = F\<^sub>1 \<union> F\<^sub>2"
    and hD44_F\<^sub>1_bl: "geotop_is_broken_line F\<^sub>1"
    and hD44_F\<^sub>2_bl: "geotop_is_broken_line F\<^sub>2"
    and hD44_F\<^sub>1E: "geotop_arc_endpoints F\<^sub>1 {Q, S}"
    and hD44_F\<^sub>2E: "geotop_arc_endpoints F\<^sub>2 {Q, S}"
    and hD44_F\<^sub>1F\<^sub>2_int_disj:
      "geotop_arc_interior F\<^sub>1 {Q, S} \<inter>
        geotop_arc_interior F\<^sub>2 {Q, S} = {}"
    and hD44_P_F\<^sub>1:
      "P \<in> geotop_arc_interior F\<^sub>1 {Q, S}"
    using hD44_QS_broken_boundary_arc_split
    by (elim exE conjE)
  have hD44_F\<^sub>1F\<^sub>2_inter: "F\<^sub>1 \<inter> F\<^sub>2 = {Q, S}"
    by (rule geotop_same_endpoint_arcs_inter_eq_prefix
        [OF hD44_F\<^sub>1E hD44_F\<^sub>2E hD44_F\<^sub>1F\<^sub>2_int_disj])
  have hD44_PR_on_QS_boundary_arc_interiors:
      "(P \<in> geotop_arc_interior F\<^sub>1 {Q, S}
          \<or> P \<in> geotop_arc_interior F\<^sub>2 {Q, S})
        \<and> (R \<in> geotop_arc_interior F\<^sub>1 {Q, S}
          \<or> R \<in> geotop_arc_interior F\<^sub>2 {Q, S})"
    using hD44_F_J_split hP hR hQ_ne_PR hS_ne_PR
    unfolding geotop_arc_interior_def by (by100 blast)
  have hD44_PR_unique_QS_boundary_arc_interiors:
      "((P \<in> geotop_arc_interior F\<^sub>1 {Q, S}
          \<and> P \<notin> geotop_arc_interior F\<^sub>2 {Q, S})
        \<or> (P \<in> geotop_arc_interior F\<^sub>2 {Q, S}
          \<and> P \<notin> geotop_arc_interior F\<^sub>1 {Q, S}))
        \<and> ((R \<in> geotop_arc_interior F\<^sub>1 {Q, S}
          \<and> R \<notin> geotop_arc_interior F\<^sub>2 {Q, S})
        \<or> (R \<in> geotop_arc_interior F\<^sub>2 {Q, S}
          \<and> R \<notin> geotop_arc_interior F\<^sub>1 {Q, S}))"
    using hD44_PR_on_QS_boundary_arc_interiors hD44_F\<^sub>1F\<^sub>2_int_disj
    by (by100 blast)
  have hD44_P_not_F\<^sub>2:
      "P \<notin> geotop_arc_interior F\<^sub>2 {Q, S}"
    using hD44_F\<^sub>1F\<^sub>2_int_disj hD44_P_F\<^sub>1
    by (by100 blast)
  have hD44_R_on_QS_boundary_arc:
      "R \<in> geotop_arc_interior F\<^sub>1 {Q, S}
        \<or> R \<in> geotop_arc_interior F\<^sub>2 {Q, S}"
    using hD44_PR_on_QS_boundary_arc_interiors
    by (by100 blast)
  have hD44_R_F\<^sub>2_if_not_F\<^sub>1:
      "R \<notin> geotop_arc_interior F\<^sub>1 {Q, S} \<Longrightarrow>
        R \<in> geotop_arc_interior F\<^sub>2 {Q, S}"
    using hD44_R_on_QS_boundary_arc
    by (by100 blast)
  have hD44_R_not_F\<^sub>1_from_cyclic:
      "R \<notin> geotop_arc_interior F\<^sub>1 {Q, S}"
    by (rule geotop_polygon_cyclic_order_QS_split_opposite_arc_prefix
        [OF hcyc hD44_P_F\<^sub>1 hD44_F_J_split hD44_F\<^sub>1E hD44_F\<^sub>2E
          hD44_F\<^sub>1F\<^sub>2_int_disj])
  have hD44_R_F\<^sub>2: "R \<in> geotop_arc_interior F\<^sub>2 {Q, S}"
    by (rule hD44_R_F\<^sub>2_if_not_F\<^sub>1[OF hD44_R_not_F\<^sub>1_from_cyclic])
  have hD44_F\<^sub>1_sub_J: "F\<^sub>1 \<subseteq> J"
    using hD44_F_J_split by (by100 blast)
  have hD44_F\<^sub>2_sub_J: "F\<^sub>2 \<subseteq> J"
    using hD44_F_J_split by (by100 blast)
  have hD44_R_not_F\<^sub>1: "R \<notin> F\<^sub>1"
    using hD44_R_not_F\<^sub>1_from_cyclic hD44_R_F\<^sub>2 hD44_F\<^sub>1F\<^sub>2_inter
    unfolding geotop_arc_interior_def by (by100 blast)
  have hD44_P_not_F\<^sub>2_set: "P \<notin> F\<^sub>2"
    using hD44_P_not_F\<^sub>2 hD44_P_F\<^sub>1 hD44_F\<^sub>1F\<^sub>2_inter
    unfolding geotop_arc_interior_def by (by100 blast)
  have hD44_A1_F\<^sub>2_disj: "A1 \<inter> F\<^sub>2 = {}"
  proof (rule equals0I)
    fix x
    assume hx: "x \<in> A1 \<inter> F\<^sub>2"
    have hxA1J: "x \<in> A1 \<inter> J"
      using hx hD44_F\<^sub>2_sub_J by (by100 blast)
    have hxP: "x = P"
      using hxA1J hA1J by (by100 blast)
    have "P \<in> F\<^sub>2"
      using hx hxP by (by100 blast)
    thus False
      using hD44_P_not_F\<^sub>2_set by (by100 blast)
  qed
  have hD44_A1_F\<^sub>1_inter: "A1 \<inter> F\<^sub>1 = {P}"
  proof
    show "A1 \<inter> F\<^sub>1 \<subseteq> {P}"
    proof
      fix x
      assume hx: "x \<in> A1 \<inter> F\<^sub>1"
      have hxA1J: "x \<in> A1 \<inter> J"
        using hx hD44_F\<^sub>1_sub_J by (by100 blast)
      show "x \<in> {P}"
        using hxA1J hA1J by (by100 blast)
    qed
    show "{P} \<subseteq> A1 \<inter> F\<^sub>1"
      using hP_in_A1 hD44_P_F\<^sub>1
      unfolding geotop_arc_interior_def by (by100 blast)
  qed
  have hD44_A2_F\<^sub>1_disj: "A2 \<inter> F\<^sub>1 = {}"
  proof (rule equals0I)
    fix x
    assume hx: "x \<in> A2 \<inter> F\<^sub>1"
    have hxA2J: "x \<in> A2 \<inter> J"
      using hx hD44_F\<^sub>1_sub_J by (by100 blast)
    have hxR: "x = R"
      using hxA2J hA2J by (by100 blast)
    have "R \<in> F\<^sub>1"
      using hx hxR by (by100 blast)
    thus False
      using hD44_R_not_F\<^sub>1 by (by100 blast)
  qed
  have hD44_A2_F\<^sub>2_inter: "A2 \<inter> F\<^sub>2 = {R}"
  proof
    show "A2 \<inter> F\<^sub>2 \<subseteq> {R}"
    proof
      fix x
      assume hx: "x \<in> A2 \<inter> F\<^sub>2"
      have hxA2J: "x \<in> A2 \<inter> J"
        using hx hD44_F\<^sub>2_sub_J by (by100 blast)
      show "x \<in> {R}"
        using hxA2J hA2J by (by100 blast)
    qed
    show "{R} \<subseteq> A2 \<inter> F\<^sub>2"
      using hR_in_A2 hD44_R_F\<^sub>2
      unfolding geotop_arc_interior_def by (by100 blast)
  qed
  have hD44_P_not_Ncut: "P \<notin> ?Ncut"
    using hP_in_A1 hA1_N by (by100 blast)
  have hD44_Q_not_Ncut: "Q \<notin> ?Ncut"
  proof
    assume hQcut: "Q \<in> ?Ncut"
    have hQint: "Q \<in> geotop_polygon_interior J"
      using hQcut by (by100 blast)
    have "Q \<notin> geotop_polygon_interior J"
      using hQ polygon_interior_disjoint_polygon[OF hJ] by (by100 blast)
    thus False
      using hQint by (by100 blast)
  qed
  have hD44_R_not_Ncut: "R \<notin> ?Ncut"
    using hR_in_A2 by (by100 blast)
  have hD44_S_not_Ncut: "S \<notin> ?Ncut"
  proof
    assume hScut: "S \<in> ?Ncut"
    have hSint: "S \<in> geotop_polygon_interior J"
      using hScut by (by100 blast)
    have "S \<notin> geotop_polygon_interior J"
      using hS polygon_interior_disjoint_polygon[OF hJ] by (by100 blast)
    thus False
      using hSint by (by100 blast)
  qed
  have hD44_F\<^sub>1_Ncut_disj: "F\<^sub>1 \<inter> ?Ncut = {}"
  proof (rule equals0I)
    fix x
    assume hx: "x \<in> F\<^sub>1 \<inter> ?Ncut"
    have hxJ: "x \<in> J"
      using hx hD44_F\<^sub>1_sub_J by (by100 blast)
    have hxI: "x \<in> geotop_polygon_interior J"
      using hx by (by100 blast)
    have "x \<notin> geotop_polygon_interior J"
      using hxJ polygon_interior_disjoint_polygon[OF hJ] by (by100 blast)
    thus False
      using hxI by (by100 blast)
  qed
  have hD44_F\<^sub>2_Ncut_disj: "F\<^sub>2 \<inter> ?Ncut = {}"
  proof (rule equals0I)
    fix x
    assume hx: "x \<in> F\<^sub>2 \<inter> ?Ncut"
    have hxJ: "x \<in> J"
      using hx hD44_F\<^sub>2_sub_J by (by100 blast)
    have hxI: "x \<in> geotop_polygon_interior J"
      using hx by (by100 blast)
    have "x \<notin> geotop_polygon_interior J"
      using hxJ polygon_interior_disjoint_polygon[OF hJ] by (by100 blast)
    thus False
      using hxI by (by100 blast)
  qed
  let ?B\<^sub>1 = "geotop_polyhedron BdJ\<^sub>N \<inter> J"
  have hD44_B\<^sub>1_eq_J\<^sub>N_boundary: "?B\<^sub>1 = J\<^sub>N \<inter> J"
    using hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
  have hD44_P_BdJ\<^sub>N_F\<^sub>1:
      "P \<in> geotop_polyhedron BdJ\<^sub>N \<inter> F\<^sub>1"
    using hP_BdJ\<^sub>N_poly hD44_P_F\<^sub>1
    unfolding geotop_arc_interior_def by (by100 blast)
  have hD44_P_B\<^sub>1: "P \<in> ?B\<^sub>1"
    using hP_BdJ\<^sub>N_poly hP by (by100 blast)
  have hD44_B\<^sub>1_nonempty: "?B\<^sub>1 \<noteq> {}"
    using hD44_P_B\<^sub>1 by (by100 blast)
  have hD44_B\<^sub>1_sub_boundary_arcs:
      "?B\<^sub>1 \<subseteq> F\<^sub>1 \<union> F\<^sub>2"
    using hD44_F_J_split by (by100 blast)
  have hD44_B\<^sub>1_A2_QS_disj:
      "?B\<^sub>1 \<inter> (A2 \<union> {Q, S}) = {}"
    using hBdJ\<^sub>N_poly_A2_QS_disj by (by100 blast)
  have hD44_B\<^sub>1_R_notin: "R \<notin> ?B\<^sub>1"
    using hD44_B\<^sub>1_A2_QS_disj hR_in_A2 by (by100 blast)
  have hD44_B\<^sub>1_Q_notin: "Q \<notin> ?B\<^sub>1"
    using hD44_B\<^sub>1_A2_QS_disj by (by100 blast)
  have hD44_B\<^sub>1_S_notin: "S \<notin> ?B\<^sub>1"
    using hD44_B\<^sub>1_A2_QS_disj by (by100 blast)
  have hD44_B\<^sub>1_Ncut_disj: "?B\<^sub>1 \<inter> ?Ncut = {}"
    using hNcut_BdJ\<^sub>N_poly_disj by (by100 blast)
  have hD44_B\<^sub>1_sub_J\<^sub>N: "?B\<^sub>1 \<subseteq> J\<^sub>N"
    using hD44_B\<^sub>1_eq_J\<^sub>N_boundary by (by100 blast)
  have hD44_J_closed: "closed J"
    by (rule polygon_closed[OF hJ])
  have hD44_B\<^sub>1_closed: "closed ?B\<^sub>1"
    by (rule closed_Int[OF hBdJ\<^sub>N_poly_closed hD44_J_closed])
  have hD44_B\<^sub>1_compact: "compact ?B\<^sub>1"
    using hBdJ\<^sub>N_poly_compact hD44_J_closed by (rule compact_Int_closed)
  let ?B1P = "geotop_component_at UNIV geotop_euclidean_topology ?B\<^sub>1 P"
  have hD44_B1P_eq_J\<^sub>N_boundary_component:
      "?B1P =
        geotop_component_at UNIV geotop_euclidean_topology (J\<^sub>N \<inter> J) P"
    using hD44_B\<^sub>1_eq_J\<^sub>N_boundary by (by100 simp)
  have hD44_B1P_sub_B\<^sub>1: "?B1P \<subseteq> ?B\<^sub>1"
  proof -
    have hB1P_eq:
        "?B1P = connected_component_set ?B\<^sub>1 P"
      by (rule geotop_component_at_UNIV_eq_connected_component_set)
    have hcc_sub:
        "connected_component_set ?B\<^sub>1 P \<subseteq> ?B\<^sub>1"
      by (rule connected_component_subset)
    show ?thesis
      using hB1P_eq hcc_sub by (by100 blast)
  qed
  have hD44_B1P_sub_J\<^sub>N: "?B1P \<subseteq> J\<^sub>N"
    using hD44_B1P_sub_B\<^sub>1 hD44_B\<^sub>1_sub_J\<^sub>N by (by100 blast)
  have hD44_B1P_sub_FrN\<^sub>I: "?B1P \<subseteq> FrN\<^sub>I"
    using hD44_B1P_sub_J\<^sub>N hJ\<^sub>N_sub_FrN\<^sub>I by (by100 blast)
  have hD44_B1P_conn:
      "top1_connected_on ?B1P
        (subspace_topology UNIV geotop_euclidean_topology ?B1P)"
  proof -
    have hB1P_eq:
        "?B1P = connected_component_set ?B\<^sub>1 P"
      by (rule geotop_component_at_UNIV_eq_connected_component_set)
    have hB1P_conn_HOL: "connected ?B1P"
      using hB1P_eq connected_connected_component by (by100 simp)
    show ?thesis
      using hB1P_conn_HOL top1_connected_on_geotop_iff_connected by (by100 blast)
  qed
  have hD44_P_B1P: "P \<in> ?B1P"
    using hD44_P_B\<^sub>1
      geotop_component_at_UNIV_eq_connected_component_set[of ?B\<^sub>1 P]
    by (by100 simp)
  have hD44_P_boundary_edge_sub_B1P:
      "\<exists>e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> P \<in> e \<and> e \<subseteq> J \<and> e \<subseteq> ?B1P"
  proof -
    obtain e where heBdJ: "e \<in> BdJ\<^sub>N"
      and hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      and heJ: "e \<subseteq> J"
      using hBdJ\<^sub>N_P_boundary_edge by (by100 blast)
    have he_sub_B\<^sub>1: "e \<subseteq> ?B\<^sub>1"
      unfolding geotop_polyhedron_def using heBdJ heJ by (by100 blast)
    have he_simplex: "geotop_is_simplex e"
      using hedge unfolding geotop_is_edge_def
      by (rule geotop_simplex_dim_imp_is_simplex)
    have he_path_connected:
        "top1_path_connected_on e
          (subspace_topology UNIV geotop_euclidean_topology e)"
      by (rule Theorem_GT_1_3[OF he_simplex])
    have he_connected:
        "top1_connected_on e
          (subspace_topology UNIV geotop_euclidean_topology e)"
      by (rule top1_path_connected_on_geotop_imp_connected[OF he_path_connected])
    have he_witness:
        "e \<in> {C. C \<subseteq> ?B\<^sub>1 \<and> P \<in> C \<and>
          top1_connected_on C
            (subspace_topology UNIV geotop_euclidean_topology C)}"
      using he_sub_B\<^sub>1 hP_e he_connected by (by100 simp)
    have he_sub_B1P: "e \<subseteq> ?B1P"
    proof
      fix x
      assume hx: "x \<in> e"
      show "x \<in> ?B1P"
        unfolding geotop_component_at_def
        using he_witness hx by (by100 blast)
    qed
    show ?thesis
      using heBdJ hedge hP_e heJ he_sub_B1P
      by (intro bexI[where x=e] conjI)
  qed
  have hD44_B1P_nontrivial: "\<exists>x\<in>?B1P. x \<noteq> P"
  proof -
    obtain e where hedge: "geotop_is_edge e"
      and hP_e: "P \<in> e"
      and he_sub_B1P: "e \<subseteq> ?B1P"
      using hD44_P_boundary_edge_sub_B1P by (by100 blast)
    have hex_other: "\<exists>x\<in>e. x \<noteq> P"
    proof (rule ccontr)
      assume hnot: "\<not> (\<exists>x\<in>e. x \<noteq> P)"
      have he_sub_single: "e \<subseteq> {P}"
        using hnot by (by100 blast)
      have he_eq_single: "e = {P}"
        using hP_e he_sub_single by (by100 blast)
      have "geotop_is_edge {P}"
        using hedge he_eq_single by (by100 simp)
      thus False
        using geotop_singleton_not_edge_prefix by (by100 blast)
    qed
    obtain x where hx_e: "x \<in> e" and hx_ne: "x \<noteq> P"
      using hex_other by (by100 blast)
    have hx_B1P: "x \<in> ?B1P"
      using he_sub_B1P hx_e by (by100 blast)
    show ?thesis
      using hx_B1P hx_ne by (by100 blast)
  qed
  have hD44_B1P_eq_connected_component:
      "?B1P = connected_component_set ?B\<^sub>1 P"
    by (rule geotop_component_at_UNIV_eq_connected_component_set)
  have hD44_B1P_closed: "closed ?B1P"
    unfolding hD44_B1P_eq_connected_component
    by (rule closed_connected_component[OF hD44_B\<^sub>1_closed])
  have hD44_B1P_component: "?B1P \<in> components ?B\<^sub>1"
    using hD44_B1P_eq_connected_component componentsI[OF hD44_P_B\<^sub>1]
    by (by100 simp)
  have hD44_B1P_compact: "compact ?B1P"
    by (rule compact_components[OF hD44_B\<^sub>1_compact hD44_B1P_component])
  have hD44_B1P_sub_boundary_arcs:
      "?B1P \<subseteq> F\<^sub>1 \<union> F\<^sub>2"
    using hD44_B1P_sub_B\<^sub>1 hD44_B\<^sub>1_sub_boundary_arcs by (by100 blast)
  have hD44_B1P_A2_QS_disj:
      "?B1P \<inter> (A2 \<union> {Q, S}) = {}"
    using hD44_B1P_sub_B\<^sub>1 hD44_B\<^sub>1_A2_QS_disj by (by100 blast)
  have hD44_B1P_Ncut_disj: "?B1P \<inter> ?Ncut = {}"
    using hD44_B1P_sub_B\<^sub>1 hD44_B\<^sub>1_Ncut_disj by (by100 blast)
  have hD44_B1P_R_notin: "R \<notin> ?B1P"
    using hD44_B1P_A2_QS_disj hR_in_A2 by (by100 blast)
  have hD44_B1P_Q_notin: "Q \<notin> ?B1P"
    using hD44_B1P_A2_QS_disj by (by100 blast)
  have hD44_B1P_S_notin: "S \<notin> ?B1P"
    using hD44_B1P_A2_QS_disj by (by100 blast)
  have hD44_F\<^sub>1_closed: "closed F\<^sub>1"
    by (rule broken_line_closed[OF hD44_F\<^sub>1E])
  have hD44_F\<^sub>2_closed: "closed F\<^sub>2"
    by (rule broken_line_closed[OF hD44_F\<^sub>2E])
  have hD44_F\<^sub>2_nonempty: "F\<^sub>2 \<noteq> {}"
    using hD44_F\<^sub>2E unfolding geotop_arc_endpoints_def by (by100 blast)
  have hD44_UNIV_top:
      "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets
        top1_open_sets_is_topology_on_UNIV)
  let ?F1o = "F\<^sub>1 - {Q, S}"
  let ?F2o = "F\<^sub>2 - {Q, S}"
  have hD44_F1o_F2o_separated:
      "geotop_separated UNIV geotop_euclidean_topology ?F1o ?F2o"
  proof -
    have hF1o_closedin:
        "closedin_on UNIV geotop_euclidean_topology F\<^sub>1"
      using hD44_F\<^sub>1_closed closedin_on_geotop_UNIV_iff_closed by (by100 blast)
    have hF2o_closedin:
        "closedin_on UNIV geotop_euclidean_topology F\<^sub>2"
      using hD44_F\<^sub>2_closed closedin_on_geotop_UNIV_iff_closed by (by100 blast)
    have hcl_F1o_sub_F1:
        "closure_on UNIV geotop_euclidean_topology ?F1o \<subseteq> F\<^sub>1"
      by (rule closure_on_subset_of_closed[OF hF1o_closedin]) (by100 blast)
    have hcl_F2o_sub_F2:
        "closure_on UNIV geotop_euclidean_topology ?F2o \<subseteq> F\<^sub>2"
      by (rule closure_on_subset_of_closed[OF hF2o_closedin]) (by100 blast)
    have hcl_F1o_F2o_disj:
        "closure_on UNIV geotop_euclidean_topology ?F1o \<inter> ?F2o = {}"
      using hcl_F1o_sub_F1 hD44_F\<^sub>1F\<^sub>2_inter by (by100 blast)
    have hF1o_cl_F2o_disj:
        "?F1o \<inter> closure_on UNIV geotop_euclidean_topology ?F2o = {}"
      using hcl_F2o_sub_F2 hD44_F\<^sub>1F\<^sub>2_inter by (by100 blast)
    show ?thesis
      unfolding geotop_separated_def
      using hcl_F1o_F2o_disj hF1o_cl_F2o_disj by (by100 simp)
  qed
  have hD44_B1P_sub_F1_or_F2:
      "?B1P \<subseteq> ?F1o \<or> ?B1P \<subseteq> ?F2o"
  proof -
    have hB1P_sub_F1oF2o: "?B1P \<subseteq> ?F1o \<union> ?F2o"
      using hD44_B1P_sub_boundary_arcs hD44_B1P_Q_notin hD44_B1P_S_notin
      by (by100 blast)
    show ?thesis
      by (rule Theorem_GT_1_10
          [OF hD44_UNIV_top hD44_F1o_F2o_separated
            hB1P_sub_F1oF2o hD44_B1P_conn])
  qed
  have hD44_P_F1o: "P \<in> ?F1o"
    using hD44_P_F\<^sub>1 unfolding geotop_arc_interior_def by (by100 blast)
  have hD44_P_not_F2o: "P \<notin> ?F2o"
    using hD44_P_not_F\<^sub>2_set by (by100 blast)
  have hD44_B1P_sub_F1o: "?B1P \<subseteq> ?F1o"
  proof (rule ccontr)
    assume hnot: "\<not> ?B1P \<subseteq> ?F1o"
    have hsub_F2o: "?B1P \<subseteq> ?F2o"
      using hD44_B1P_sub_F1_or_F2 hnot by (by100 blast)
    have "P \<in> ?F2o"
      using hsub_F2o hD44_P_B1P by (by100 blast)
    thus False
      using hD44_P_not_F2o by (by100 blast)
  qed
  have hD44_B1P_sub_F\<^sub>1_arc_interior:
      "?B1P \<subseteq> geotop_arc_interior F\<^sub>1 {Q, S}"
    using hD44_B1P_sub_F1o unfolding geotop_arc_interior_def by (by100 simp)
  have hD44_B1P_sub_F\<^sub>1: "?B1P \<subseteq> F\<^sub>1"
    using hD44_B1P_sub_F1o by (by100 blast)
  have hD44_B1P_inter_F\<^sub>1: "?B1P \<inter> F\<^sub>1 = ?B1P"
    using hD44_B1P_sub_F\<^sub>1 by (by100 blast)
  have hD44_B1P_F\<^sub>2_disj: "?B1P \<inter> F\<^sub>2 = {}"
    using hD44_B1P_sub_F1o hD44_F\<^sub>1F\<^sub>2_inter by (by100 blast)
  have hD44_B1P_other_F\<^sub>1_arc_interior:
      "\<exists>X. X \<in> ?B1P
        \<and> X \<in> geotop_arc_interior F\<^sub>1 {Q, S}
        \<and> X \<noteq> P"
  proof -
    obtain X where hX_B1P: "X \<in> ?B1P" and hX_ne: "X \<noteq> P"
      using hD44_B1P_nontrivial by (by100 blast)
    have hX_F1int: "X \<in> geotop_arc_interior F\<^sub>1 {Q, S}"
      using hD44_B1P_sub_F\<^sub>1_arc_interior hX_B1P by (by100 blast)
    show ?thesis
      using hX_B1P hX_F1int hX_ne by (intro exI conjI)
  qed
  have hD44_F\<^sub>1_boundary_subarc_from_P_to_B1P:
      "\<exists>X C. X \<in> ?B1P
        \<and> X \<noteq> P
        \<and> geotop_is_broken_line C
        \<and> C \<subseteq> F\<^sub>1
        \<and> P \<in> C
        \<and> X \<in> C
        \<and> geotop_arc_endpoints C {P, X}"
  proof -
    obtain X where hX_B1P: "X \<in> ?B1P"
      and hX_F1int: "X \<in> geotop_arc_interior F\<^sub>1 {Q, S}"
      and hX_ne: "X \<noteq> P"
      using hD44_B1P_other_F\<^sub>1_arc_interior by (elim exE conjE)
    have hP_F1: "P \<in> F\<^sub>1"
      using hD44_P_F\<^sub>1 unfolding geotop_arc_interior_def by (by100 blast)
    have hX_F1: "X \<in> F\<^sub>1"
      using hX_F1int unfolding geotop_arc_interior_def by (by100 blast)
    have hP_ne_X: "P \<noteq> X"
      using hX_ne by (by100 blast)
    obtain C where hC_bl: "geotop_is_broken_line C"
      and hC_sub: "C \<subseteq> F\<^sub>1"
      and hP_C: "P \<in> C"
      and hX_C: "X \<in> C"
      and hC_end: "geotop_arc_endpoints C {P, X}"
      using geotop_broken_line_subarc_with_endpoints_prefix
        [OF hD44_F\<^sub>1_bl hP_F1 hX_F1 hP_ne_X]
      by (by100 blast)
    show ?thesis
      using hX_B1P hX_ne hC_bl hC_sub hP_C hX_C hC_end
      by (intro exI conjI)
  qed
  have hD44_B1P_boundary_subarc_inside_B1P:
      "\<exists>X C. X \<in> ?B1P
        \<and> X \<noteq> P
        \<and> geotop_is_broken_line C
        \<and> C \<subseteq> ?B1P
        \<and> P \<in> C
        \<and> X \<in> C
        \<and> geotop_arc_endpoints C {P, X}"
  proof -
    obtain X where hX_B1P: "X \<in> ?B1P"
      and hX_F1int: "X \<in> geotop_arc_interior F\<^sub>1 {Q, S}"
      and hX_ne: "X \<noteq> P"
      using hD44_B1P_other_F\<^sub>1_arc_interior by (elim exE conjE)
    have hB1P_conn_HOL: "connected ?B1P"
      using hD44_B1P_conn top1_connected_on_geotop_iff_connected
      by (by100 blast)
    have hP_ne_X: "P \<noteq> X"
      using hX_ne by (by100 blast)
    obtain C where hC_bl: "geotop_is_broken_line C"
      and hC_sub: "C \<subseteq> ?B1P"
      and hP_C: "P \<in> C"
      and hX_C: "X \<in> C"
      and hC_end: "geotop_arc_endpoints C {P, X}"
      using geotop_connected_subset_broken_line_subarc_with_endpoints_prefix
          [OF hD44_F\<^sub>1_bl hD44_B1P_sub_F\<^sub>1 hB1P_conn_HOL
            hD44_P_B1P hX_B1P hP_ne_X]
      by (by100 blast)
    show ?thesis
      using hX_B1P hX_ne hC_bl hC_sub hP_C hX_C hC_end
      by (intro exI conjI)
  qed
  have hD44_F\<^sub>1_boundary_subarc_vertex_refinement_from_P_to_B1P:
      "\<exists>X C L. X \<in> ?B1P
        \<and> X \<noteq> P
        \<and> geotop_is_broken_line C
        \<and> C \<subseteq> ?B1P
        \<and> C \<subseteq> F\<^sub>1
        \<and> P \<in> C
        \<and> X \<in> C
        \<and> geotop_arc_endpoints C {P, X}
        \<and> connected (geotop_arc_interior C {P, X})
        \<and> geotop_arc_interior C {P, X} \<noteq> {}
        \<and> geotop_is_complex L
        \<and> geotop_complex_is_1dim L
        \<and> finite L
        \<and> geotop_polyhedron L = C
        \<and> {P} \<in> L
        \<and> {X} \<in> L"
  proof -
    obtain X C where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hC_bl: "geotop_is_broken_line C"
      and hP_C: "P \<in> C"
      and hX_C: "X \<in> C"
      and hC_end: "geotop_arc_endpoints C {P, X}"
      and hC_sub_B1P: "C \<subseteq> ?B1P"
      using hD44_B1P_boundary_subarc_inside_B1P by (elim exE conjE)
    have hC_sub_F1: "C \<subseteq> F\<^sub>1"
      using hC_sub_B1P hD44_B1P_sub_F\<^sub>1 by (by100 blast)
    obtain L0 where hL0_complex: "geotop_is_complex L0"
      and hL0_1dim: "geotop_complex_is_1dim L0"
      and hL0_poly: "geotop_polyhedron L0 = C"
      and hP_L0: "{P} \<in> L0"
      and hL0_fin: "finite L0"
      using geotop_broken_line_vertex_at[OF hC_bl hP_C] by (by100 blast)
    have hX_poly_L0: "X \<in> geotop_polyhedron L0"
      using hX_C hL0_poly by (by100 simp)
    obtain L where hL_complex: "geotop_is_complex L"
      and hL_1dim: "geotop_complex_is_1dim L"
      and hL_poly: "geotop_polyhedron L = geotop_polyhedron L0"
      and hX_L: "{X} \<in> L"
      and hvertices_preserved: "\<forall>v. {v} \<in> L0 \<longrightarrow> {v} \<in> L"
      and hL_fin_if: "finite L0 \<longrightarrow> finite L"
      using geotop_complex_subdivide_at
        [OF hL0_complex hL0_1dim hX_poly_L0]
      by (by100 blast)
    have hP_L: "{P} \<in> L"
      using hvertices_preserved hP_L0 by (by100 blast)
    have hL_fin: "finite L"
      using hL_fin_if hL0_fin by (by100 blast)
    have hL_poly_C: "geotop_polyhedron L = C"
      using hL_poly hL0_poly by (by100 simp)
    have hC_int_connected: "connected (geotop_arc_interior C {P, X})"
      by (rule arc_interior_connected[OF hC_end])
    have hC_int_nonempty: "geotop_arc_interior C {P, X} \<noteq> {}"
      by (rule arc_interior_nonempty[OF hC_end])
    show ?thesis
      using hX_B1P hX_ne hC_bl hC_sub_B1P hC_sub_F1 hP_C hX_C hC_end
        hC_int_connected hC_int_nonempty
        hL_complex hL_1dim hL_fin hL_poly_C hP_L hX_L
      by (intro exI conjI)
  qed
  have hD44_B1P_boundary_subarc_frontier_package:
      "\<exists>X C L. X \<in> ?B1P
        \<and> X \<noteq> P
        \<and> geotop_is_broken_line C
        \<and> C \<subseteq> ?B1P
        \<and> C \<subseteq> F\<^sub>1
        \<and> C \<subseteq> J\<^sub>N
        \<and> C \<subseteq> FrN\<^sub>I
        \<and> C \<inter> F\<^sub>2 = {}
        \<and> C \<inter> (A2 \<union> {Q, S}) = {}
        \<and> C \<inter> ?Ncut = {}
        \<and> P \<in> C
        \<and> X \<in> C
        \<and> geotop_arc_endpoints C {P, X}
        \<and> connected (geotop_arc_interior C {P, X})
        \<and> geotop_arc_interior C {P, X} \<noteq> {}
        \<and> geotop_is_complex L
        \<and> geotop_complex_is_1dim L
        \<and> finite L
        \<and> geotop_polyhedron L = C
        \<and> {P} \<in> L
        \<and> {X} \<in> L"
  proof -
    obtain X C L where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hC_bl: "geotop_is_broken_line C"
      and hC_sub_B1P: "C \<subseteq> ?B1P"
      and hC_sub_F1: "C \<subseteq> F\<^sub>1"
      and hP_C: "P \<in> C"
      and hX_C: "X \<in> C"
      and hC_end: "geotop_arc_endpoints C {P, X}"
      and hC_int_connected: "connected (geotop_arc_interior C {P, X})"
      and hC_int_nonempty: "geotop_arc_interior C {P, X} \<noteq> {}"
      and hL_complex: "geotop_is_complex L"
      and hL_1dim: "geotop_complex_is_1dim L"
      and hL_fin: "finite L"
      and hL_poly_C: "geotop_polyhedron L = C"
      and hP_L: "{P} \<in> L"
      and hX_L: "{X} \<in> L"
      using hD44_F\<^sub>1_boundary_subarc_vertex_refinement_from_P_to_B1P
      by (elim exE conjE)
    have hC_sub_J\<^sub>N: "C \<subseteq> J\<^sub>N"
      using hC_sub_B1P hD44_B1P_sub_J\<^sub>N by (by100 blast)
    have hC_sub_FrN\<^sub>I: "C \<subseteq> FrN\<^sub>I"
      using hC_sub_B1P hD44_B1P_sub_FrN\<^sub>I by (by100 blast)
    have hC_F\<^sub>2_disj: "C \<inter> F\<^sub>2 = {}"
      using hC_sub_B1P hD44_B1P_F\<^sub>2_disj by (by100 blast)
    have hC_A2_QS_disj: "C \<inter> (A2 \<union> {Q, S}) = {}"
      using hC_sub_B1P hD44_B1P_A2_QS_disj by (by100 blast)
    have hC_Ncut_disj: "C \<inter> ?Ncut = {}"
      using hC_sub_B1P hD44_B1P_Ncut_disj by (by100 blast)
    show ?thesis
      using hX_B1P hX_ne hC_bl hC_sub_B1P hC_sub_F1 hC_sub_J\<^sub>N
        hC_sub_FrN\<^sub>I hC_F\<^sub>2_disj hC_A2_QS_disj hC_Ncut_disj
        hP_C hX_C hC_end hC_int_connected hC_int_nonempty
        hL_complex hL_1dim hL_fin hL_poly_C hP_L hX_L
      by (intro exI conjI)
  qed
  have hD44_BdJ\<^sub>N_polygon_split_at_B1P_endpoint:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>X C L C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_is_broken_line C
          \<and> C \<subseteq> ?B1P
          \<and> C \<subseteq> F\<^sub>1
          \<and> C \<subseteq> J\<^sub>N
          \<and> C \<subseteq> FrN\<^sub>I
          \<and> C \<inter> F\<^sub>2 = {}
          \<and> C \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C \<inter> ?Ncut = {}
          \<and> P \<in> C
          \<and> X \<in> C
          \<and> geotop_arc_endpoints C {P, X}
          \<and> connected (geotop_arc_interior C {P, X})
          \<and> geotop_arc_interior C {P, X} \<noteq> {}
          \<and> geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> {P} \<in> L
          \<and> {X} \<in> L
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}
          \<and> C\<^sub>B \<inter> C\<^sub>O = {P, X}
          \<and> P \<in> C\<^sub>B
          \<and> X \<in> C\<^sub>B
          \<and> P \<in> C\<^sub>O
          \<and> X \<in> C\<^sub>O
          \<and> C \<subseteq> C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_arc_interior C {P, X} \<subseteq>
              geotop_arc_interior C\<^sub>B {P, X} \<union>
              geotop_arc_interior C\<^sub>O {P, X}
          \<and> (geotop_arc_interior C {P, X} \<subseteq>
                geotop_arc_interior C\<^sub>B {P, X}
              \<or> geotop_arc_interior C {P, X} \<subseteq>
                geotop_arc_interior C\<^sub>O {P, X})
          \<and> (C = C\<^sub>B \<or> C = C\<^sub>O)"
  proof -
    assume hpolygon:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    obtain X C L where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hC_bl: "geotop_is_broken_line C"
      and hC_sub_B1P: "C \<subseteq> ?B1P"
      and hC_sub_F1: "C \<subseteq> F\<^sub>1"
      and hC_sub_J\<^sub>N: "C \<subseteq> J\<^sub>N"
      and hC_sub_FrN\<^sub>I: "C \<subseteq> FrN\<^sub>I"
      and hC_F\<^sub>2_disj: "C \<inter> F\<^sub>2 = {}"
      and hC_A2_QS_disj: "C \<inter> (A2 \<union> {Q, S}) = {}"
      and hC_Ncut_disj: "C \<inter> ?Ncut = {}"
      and hP_C: "P \<in> C"
      and hX_C: "X \<in> C"
      and hC_end: "geotop_arc_endpoints C {P, X}"
      and hC_int_connected: "connected (geotop_arc_interior C {P, X})"
      and hC_int_nonempty: "geotop_arc_interior C {P, X} \<noteq> {}"
      and hL_complex: "geotop_is_complex L"
      and hL_1dim: "geotop_complex_is_1dim L"
      and hL_fin: "finite L"
      and hL_poly_C: "geotop_polyhedron L = C"
      and hP_L: "{P} \<in> L"
      and hX_L: "{X} \<in> L"
      using hD44_B1P_boundary_subarc_frontier_package
      by (elim exE conjE)
    have hX_BdJ_poly: "X \<in> geotop_polyhedron BdJ\<^sub>N"
      using hX_B1P hD44_B1P_sub_B\<^sub>1 by (by100 blast)
    obtain LJ where hLJ_linear: "geotop_is_linear_graph LJ"
      and hLJ_fin: "finite LJ"
      and hLJ_conn: "geotop_complex_connected LJ"
      and hLJ_poly: "geotop_polyhedron LJ = geotop_polyhedron BdJ\<^sub>N"
      and hP_LJ: "{P} \<in> LJ"
      and hX_LJ: "{X} \<in> LJ"
      using geotop_polygon_finite_connected_linear_graph_with_two_vertices_prefix
        [OF hpolygon hP_BdJ\<^sub>N_poly hX_BdJ_poly]
      by (elim exE conjE)
    have hLJ_polygon: "geotop_is_polygon (geotop_polyhedron LJ)"
      using hpolygon hLJ_poly by (by100 simp)
    have hP_ne_X: "P \<noteq> X"
      using hX_ne by (by100 blast)
    obtain C\<^sub>B C\<^sub>O where hsplit:
        "geotop_polyhedron LJ = C\<^sub>B \<union> C\<^sub>O
        \<and> geotop_is_broken_line C\<^sub>B
        \<and> geotop_is_broken_line C\<^sub>O
        \<and> geotop_arc_endpoints C\<^sub>B {P, X}
        \<and> geotop_arc_endpoints C\<^sub>O {P, X}
        \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
            geotop_arc_interior C\<^sub>O {P, X} = {}"
      using geotop_polygon_finite_linear_graph_two_vertex_boundary_split_prefix
        [OF hLJ_linear hLJ_fin hLJ_conn hLJ_polygon hP_LJ hX_LJ hP_ne_X]
      by (by100 blast)
    have hC\<^sub>B_end_split: "geotop_arc_endpoints C\<^sub>B {P, X}"
      using hsplit by (by100 blast)
    have hC\<^sub>O_end_split: "geotop_arc_endpoints C\<^sub>O {P, X}"
      using hsplit by (by100 blast)
    have hC_int_disj_split:
        "geotop_arc_interior C\<^sub>B {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
      using hsplit by (by100 blast)
    have hC_inter: "C\<^sub>B \<inter> C\<^sub>O = {P, X}"
      by (rule geotop_same_endpoint_arcs_inter_eq_prefix
          [OF hC\<^sub>B_end_split hC\<^sub>O_end_split hC_int_disj_split])
    have hP_C\<^sub>B_split: "P \<in> C\<^sub>B"
      using hC\<^sub>B_end_split unfolding geotop_arc_endpoints_def by (by100 blast)
    have hX_C\<^sub>B_split: "X \<in> C\<^sub>B"
      using hC\<^sub>B_end_split unfolding geotop_arc_endpoints_def by (by100 blast)
    have hP_C\<^sub>O_split: "P \<in> C\<^sub>O"
      using hC\<^sub>O_end_split unfolding geotop_arc_endpoints_def by (by100 blast)
    have hX_C\<^sub>O_split: "X \<in> C\<^sub>O"
      using hC\<^sub>O_end_split unfolding geotop_arc_endpoints_def by (by100 blast)
    have hsplit_BdJ:
        "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
        \<and> geotop_is_broken_line C\<^sub>B
        \<and> geotop_is_broken_line C\<^sub>O
        \<and> geotop_arc_endpoints C\<^sub>B {P, X}
        \<and> geotop_arc_endpoints C\<^sub>O {P, X}
        \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
            geotop_arc_interior C\<^sub>O {P, X} = {}
        \<and> C\<^sub>B \<inter> C\<^sub>O = {P, X}
        \<and> P \<in> C\<^sub>B
        \<and> X \<in> C\<^sub>B
        \<and> P \<in> C\<^sub>O
        \<and> X \<in> C\<^sub>O"
      using hsplit hLJ_poly hC_inter hP_C\<^sub>B_split hX_C\<^sub>B_split
        hP_C\<^sub>O_split hX_C\<^sub>O_split
      by (by100 simp)
    have hBdJ_poly_split: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O"
      using hsplit_BdJ by (by100 blast)
    have hC_sub_BdJ_poly: "C \<subseteq> geotop_polyhedron BdJ\<^sub>N"
    proof
      fix y
      assume hyC: "y \<in> C"
      have hyJ\<^sub>N: "y \<in> J\<^sub>N"
        using hC_sub_J\<^sub>N hyC by (by100 blast)
      show "y \<in> geotop_polyhedron BdJ\<^sub>N"
        using hyJ\<^sub>N hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
    qed
    have hC_sub_split: "C \<subseteq> C\<^sub>B \<union> C\<^sub>O"
    proof
      fix y
      assume hyC: "y \<in> C"
      have hyBdJ: "y \<in> geotop_polyhedron BdJ\<^sub>N"
        using hC_sub_BdJ_poly hyC by (by100 blast)
      show "y \<in> C\<^sub>B \<union> C\<^sub>O"
        using hyBdJ hBdJ_poly_split by (by100 simp)
    qed
    have hC_int_sub_split_int:
        "geotop_arc_interior C {P, X} \<subseteq>
          geotop_arc_interior C\<^sub>B {P, X} \<union>
          geotop_arc_interior C\<^sub>O {P, X}"
    proof
      fix y
      assume hy: "y \<in> geotop_arc_interior C {P, X}"
      have hyC: "y \<in> C"
        using hy unfolding geotop_arc_interior_def by (by100 blast)
      have hynot: "y \<notin> {P, X}"
        using hy unfolding geotop_arc_interior_def by (by100 blast)
      have hysplit: "y \<in> C\<^sub>B \<union> C\<^sub>O"
        using hC_sub_split hyC by (by100 blast)
      show "y \<in> geotop_arc_interior C\<^sub>B {P, X} \<union>
          geotop_arc_interior C\<^sub>O {P, X}"
      proof (rule UnE[OF hysplit])
        assume hyB: "y \<in> C\<^sub>B"
        have "y \<in> geotop_arc_interior C\<^sub>B {P, X}"
          using hyB hynot unfolding geotop_arc_interior_def by (by100 blast)
        thus ?thesis by (by100 blast)
      next
        assume hyO: "y \<in> C\<^sub>O"
        have "y \<in> geotop_arc_interior C\<^sub>O {P, X}"
          using hyO hynot unfolding geotop_arc_interior_def by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
    qed
    have hC_int_one_side_split:
        "geotop_arc_interior C {P, X} \<subseteq>
            geotop_arc_interior C\<^sub>B {P, X}
          \<or> geotop_arc_interior C {P, X} \<subseteq>
            geotop_arc_interior C\<^sub>O {P, X}"
    proof (rule ccontr)
      let ?Y = "geotop_arc_interior C {P, X}"
      let ?IB = "geotop_arc_interior C\<^sub>B {P, X}"
      let ?IO = "geotop_arc_interior C\<^sub>O {P, X}"
      assume hnot: "\<not> (?Y \<subseteq> ?IB \<or> ?Y \<subseteq> ?IO)"
      have hnot_IB: "\<not> ?Y \<subseteq> ?IB"
        using hnot by (by100 blast)
      have hnot_IO: "\<not> ?Y \<subseteq> ?IO"
        using hnot by (by100 blast)
      have hYIB_ne: "?Y \<inter> ?IB \<noteq> {}"
      proof -
        obtain y where hyY: "y \<in> ?Y" and hy_not_IO: "y \<notin> ?IO"
          using hnot_IO by (by100 blast)
        have "y \<in> ?IB"
          using hC_int_sub_split_int hyY hy_not_IO by (by100 blast)
        thus ?thesis
          using hyY by (by100 blast)
      qed
      have hYIO_ne: "?Y \<inter> ?IO \<noteq> {}"
      proof -
        obtain y where hyY: "y \<in> ?Y" and hy_not_IB: "y \<notin> ?IB"
          using hnot_IB by (by100 blast)
        have "y \<in> ?IO"
          using hC_int_sub_split_int hyY hy_not_IB by (by100 blast)
        thus ?thesis
          using hyY by (by100 blast)
      qed
      have hY_union: "(?Y \<inter> ?IB) \<union> (?Y \<inter> ?IO) = ?Y"
        using hC_int_sub_split_int by (by100 blast)
      have hY_disj: "(?Y \<inter> ?IB) \<inter> (?Y \<inter> ?IO) = {}"
        using hC_int_disj_split by (by100 blast)
      have hC\<^sub>B_closed: "closed C\<^sub>B"
        by (rule broken_line_closed[OF hC\<^sub>B_end_split])
      have hC\<^sub>O_closed: "closed C\<^sub>O"
        by (rule broken_line_closed[OF hC\<^sub>O_end_split])
      have hYIB_eq: "?Y \<inter> ?IB = ?Y \<inter> C\<^sub>B"
        unfolding geotop_arc_interior_def by (by100 blast)
      have hYIO_eq: "?Y \<inter> ?IO = ?Y \<inter> C\<^sub>O"
        unfolding geotop_arc_interior_def by (by100 blast)
      have hYIB_closed: "closedin (top_of_set ?Y) (?Y \<inter> ?IB)"
      proof -
        have "closedin (top_of_set ?Y) (?Y \<inter> C\<^sub>B)"
          by (rule closedin_closed_Int[OF hC\<^sub>B_closed])
        thus ?thesis
          using hYIB_eq by (by100 simp)
      qed
      have hYIO_closed: "closedin (top_of_set ?Y) (?Y \<inter> ?IO)"
      proof -
        have "closedin (top_of_set ?Y) (?Y \<inter> C\<^sub>O)"
          by (rule closedin_closed_Int[OF hC\<^sub>O_closed])
        thus ?thesis
          using hYIO_eq by (by100 simp)
      qed
      have hNoClosedSep:
          "\<nexists>E\<^sub>1 E\<^sub>2.
            closedin (top_of_set ?Y) E\<^sub>1
            \<and> closedin (top_of_set ?Y) E\<^sub>2
            \<and> E\<^sub>1 \<union> E\<^sub>2 = ?Y
            \<and> E\<^sub>1 \<inter> E\<^sub>2 = {}
            \<and> E\<^sub>1 \<noteq> {}
            \<and> E\<^sub>2 \<noteq> {}"
        using hC_int_connected
        unfolding connected_closedin_eq
        by (by100 blast)
      show False
        using hNoClosedSep hYIB_closed hYIO_closed hY_union hY_disj
          hYIB_ne hYIO_ne
        by (by100 blast)
    qed
    have hC_eq_one_split: "C = C\<^sub>B \<or> C = C\<^sub>O"
    proof (rule disjE[OF hC_int_one_side_split])
      assume hC_int_sub_B:
          "geotop_arc_interior C {P, X} \<subseteq>
            geotop_arc_interior C\<^sub>B {P, X}"
      have hC_sub_B: "C \<subseteq> C\<^sub>B"
      proof
        fix y
        assume hyC: "y \<in> C"
        show "y \<in> C\<^sub>B"
        proof (cases "y \<in> {P, X}")
          case True
          thus ?thesis
            using hP_C\<^sub>B_split hX_C\<^sub>B_split by (by100 blast)
        next
          case False
          have "y \<in> geotop_arc_interior C {P, X}"
            using hyC False unfolding geotop_arc_interior_def by (by100 blast)
          hence "y \<in> geotop_arc_interior C\<^sub>B {P, X}"
            using hC_int_sub_B by (by100 blast)
          thus ?thesis
            unfolding geotop_arc_interior_def by (by100 blast)
        qed
      qed
      have "C = C\<^sub>B"
        by (rule geotop_same_endpoint_arc_subset_eq_prefix
            [OF hC_end hC\<^sub>B_end_split hC_sub_B])
      thus "C = C\<^sub>B \<or> C = C\<^sub>O"
        by (by100 blast)
    next
      assume hC_int_sub_O:
          "geotop_arc_interior C {P, X} \<subseteq>
            geotop_arc_interior C\<^sub>O {P, X}"
      have hC_sub_O: "C \<subseteq> C\<^sub>O"
      proof
        fix y
        assume hyC: "y \<in> C"
        show "y \<in> C\<^sub>O"
        proof (cases "y \<in> {P, X}")
          case True
          thus ?thesis
            using hP_C\<^sub>O_split hX_C\<^sub>O_split by (by100 blast)
        next
          case False
          have "y \<in> geotop_arc_interior C {P, X}"
            using hyC False unfolding geotop_arc_interior_def by (by100 blast)
          hence "y \<in> geotop_arc_interior C\<^sub>O {P, X}"
            using hC_int_sub_O by (by100 blast)
          thus ?thesis
            unfolding geotop_arc_interior_def by (by100 blast)
        qed
      qed
      have "C = C\<^sub>O"
        by (rule geotop_same_endpoint_arc_subset_eq_prefix
            [OF hC_end hC\<^sub>O_end_split hC_sub_O])
      thus "C = C\<^sub>B \<or> C = C\<^sub>O"
        by (by100 blast)
    qed
    show ?thesis
      apply (rule exI[where x=X])
      apply (rule exI[where x=C])
      apply (rule exI[where x=L])
      apply (rule exI[where x=C\<^sub>B])
      apply (rule exI[where x=C\<^sub>O])
      using hX_B1P hX_ne hC_bl hC_sub_B1P hC_sub_F1 hC_sub_J\<^sub>N
        hC_sub_FrN\<^sub>I hC_F\<^sub>2_disj hC_A2_QS_disj hC_Ncut_disj
        hP_C hX_C hC_end hC_int_connected hC_int_nonempty
        hL_complex hL_1dim hL_fin hL_poly_C hP_L hX_L
        hsplit_BdJ hC_inter hP_C\<^sub>B_split hX_C\<^sub>B_split
        hP_C\<^sub>O_split hX_C\<^sub>O_split hC_sub_split hC_int_sub_split_int
        hC_int_one_side_split
        hC_eq_one_split
      apply (intro conjI)
      by (by100 blast)+
  qed
  have hD44_BdJ\<^sub>N_polygon_boundary_subarc_complement_split:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>X C L C\<^sub>F. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_is_broken_line C
          \<and> C \<subseteq> ?B1P
          \<and> C \<subseteq> F\<^sub>1
          \<and> C \<subseteq> J\<^sub>N
          \<and> C \<subseteq> FrN\<^sub>I
          \<and> C \<inter> F\<^sub>2 = {}
          \<and> C \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C \<inter> ?Ncut = {}
          \<and> P \<in> C
          \<and> X \<in> C
          \<and> geotop_arc_endpoints C {P, X}
          \<and> connected (geotop_arc_interior C {P, X})
          \<and> geotop_arc_interior C {P, X} \<noteq> {}
          \<and> geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> {P} \<in> L
          \<and> {X} \<in> L
          \<and> geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>F
          \<and> geotop_is_broken_line C\<^sub>F
          \<and> geotop_arc_endpoints C\<^sub>F {P, X}
          \<and> geotop_arc_interior C {P, X} \<inter>
              geotop_arc_interior C\<^sub>F {P, X} = {}
          \<and> C \<inter> C\<^sub>F = {P, X}
          \<and> P \<in> C\<^sub>F
          \<and> X \<in> C\<^sub>F
          \<and> C\<^sub>F \<subseteq> J\<^sub>N
          \<and> C\<^sub>F \<subseteq> FrN\<^sub>I
          \<and> C\<^sub>F \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C\<^sub>F \<inter> ?Ncut = {}"
  proof -
    assume hpolygon:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    obtain X C L C\<^sub>B C\<^sub>O where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hC_bl: "geotop_is_broken_line C"
      and hC_sub_B1P: "C \<subseteq> ?B1P"
      and hC_sub_F1: "C \<subseteq> F\<^sub>1"
      and hC_sub_J\<^sub>N: "C \<subseteq> J\<^sub>N"
      and hC_sub_FrN\<^sub>I: "C \<subseteq> FrN\<^sub>I"
      and hC_F\<^sub>2_disj: "C \<inter> F\<^sub>2 = {}"
      and hC_A2_QS_disj: "C \<inter> (A2 \<union> {Q, S}) = {}"
      and hC_Ncut_disj: "C \<inter> ?Ncut = {}"
      and hP_C: "P \<in> C"
      and hX_C: "X \<in> C"
      and hC_end: "geotop_arc_endpoints C {P, X}"
      and hC_int_connected: "connected (geotop_arc_interior C {P, X})"
      and hC_int_nonempty: "geotop_arc_interior C {P, X} \<noteq> {}"
      and hL_complex: "geotop_is_complex L"
      and hL_1dim: "geotop_complex_is_1dim L"
      and hL_fin: "finite L"
      and hL_poly_C: "geotop_polyhedron L = C"
      and hP_L: "{P} \<in> L"
      and hX_L: "{X} \<in> L"
      and hBdJ_split: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O"
      and hC\<^sub>B_bl: "geotop_is_broken_line C\<^sub>B"
      and hC\<^sub>O_bl: "geotop_is_broken_line C\<^sub>O"
      and hC\<^sub>B_end: "geotop_arc_endpoints C\<^sub>B {P, X}"
      and hC\<^sub>O_end: "geotop_arc_endpoints C\<^sub>O {P, X}"
      and hC_int_disj:
        "geotop_arc_interior C\<^sub>B {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
      and hC_inter: "C\<^sub>B \<inter> C\<^sub>O = {P, X}"
      and hP_C\<^sub>B: "P \<in> C\<^sub>B"
      and hX_C\<^sub>B: "X \<in> C\<^sub>B"
      and hP_C\<^sub>O: "P \<in> C\<^sub>O"
      and hX_C\<^sub>O: "X \<in> C\<^sub>O"
      and hC_eq_one: "C = C\<^sub>B \<or> C = C\<^sub>O"
      using hD44_BdJ\<^sub>N_polygon_split_at_B1P_endpoint[OF hpolygon]
      by (elim exE conjE)
    show ?thesis
    proof (rule disjE[OF hC_eq_one])
      assume hC_eq_B: "C = C\<^sub>B"
      have hBdJ_split_C\<^sub>F: "geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>O"
        using hBdJ_split hC_eq_B by (by100 simp)
      have hC_int_disj_C\<^sub>F:
        "geotop_arc_interior C {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
        using hC_int_disj hC_eq_B by (by100 simp)
      have hC_inter_C\<^sub>F: "C \<inter> C\<^sub>O = {P, X}"
        using hC_inter hC_eq_B by (by100 simp)
      have hC\<^sub>F_sub_BdJ: "C\<^sub>O \<subseteq> geotop_polyhedron BdJ\<^sub>N"
      proof
        fix y
        assume hy: "y \<in> C\<^sub>O"
        have "y \<in> C\<^sub>B \<union> C\<^sub>O"
          using hy by (by100 simp)
        thus "y \<in> geotop_polyhedron BdJ\<^sub>N"
          using hBdJ_split by (by100 simp)
      qed
      have hC\<^sub>F_sub_J\<^sub>N: "C\<^sub>O \<subseteq> J\<^sub>N"
        by (rule subset_trans[OF hC\<^sub>F_sub_BdJ hBdJ\<^sub>N_poly_sub_J\<^sub>N])
      have hC\<^sub>F_sub_FrN\<^sub>I: "C\<^sub>O \<subseteq> FrN\<^sub>I"
        by (rule subset_trans[OF hC\<^sub>F_sub_BdJ hBdJ\<^sub>N_poly_sub_FrN\<^sub>I])
      have hC\<^sub>F_A2_QS_disj: "C\<^sub>O \<inter> (A2 \<union> {Q, S}) = {}"
      proof -
        have "C\<^sub>O \<inter> (A2 \<union> {Q, S}) \<subseteq>
            geotop_polyhedron BdJ\<^sub>N \<inter> (A2 \<union> {Q, S})"
          using hC\<^sub>F_sub_BdJ by (by100 blast)
        thus ?thesis
          using hBdJ\<^sub>N_poly_A2_QS_disj by (by100 blast)
      qed
      have hC\<^sub>F_Ncut_disj: "C\<^sub>O \<inter> ?Ncut = {}"
      proof -
        have "C\<^sub>O \<inter> ?Ncut \<subseteq> geotop_polyhedron BdJ\<^sub>N \<inter> ?Ncut"
          using hC\<^sub>F_sub_BdJ by (by100 blast)
        thus ?thesis
          using hNcut_BdJ\<^sub>N_poly_disj by (by100 blast)
      qed
      show ?thesis
        apply (rule exI[where x=X])
        apply (rule exI[where x=C])
        apply (rule exI[where x=L])
        apply (rule exI[where x=C\<^sub>O])
        using hX_B1P hX_ne hC_bl hC_sub_B1P hC_sub_F1 hC_sub_J\<^sub>N
          hC_sub_FrN\<^sub>I hC_F\<^sub>2_disj hC_A2_QS_disj hC_Ncut_disj
          hP_C hX_C hC_end hC_int_connected hC_int_nonempty
          hL_complex hL_1dim hL_fin hL_poly_C hP_L hX_L
          hBdJ_split_C\<^sub>F hC\<^sub>O_bl hC\<^sub>O_end hC_int_disj_C\<^sub>F
          hC_inter_C\<^sub>F hP_C\<^sub>O hX_C\<^sub>O hC\<^sub>F_sub_J\<^sub>N
          hC\<^sub>F_sub_FrN\<^sub>I hC\<^sub>F_A2_QS_disj hC\<^sub>F_Ncut_disj
        by (intro conjI)
    next
      assume hC_eq_O: "C = C\<^sub>O"
      have hBdJ_split_C\<^sub>F: "geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>B"
        using hBdJ_split hC_eq_O by (by100 auto)
      have hC_int_disj_C\<^sub>F:
        "geotop_arc_interior C {P, X} \<inter>
          geotop_arc_interior C\<^sub>B {P, X} = {}"
        using hC_int_disj hC_eq_O by (by100 auto)
      have hC_inter_C\<^sub>F: "C \<inter> C\<^sub>B = {P, X}"
        using hC_inter hC_eq_O by (by100 auto)
      have hC\<^sub>F_sub_BdJ: "C\<^sub>B \<subseteq> geotop_polyhedron BdJ\<^sub>N"
      proof
        fix y
        assume hy: "y \<in> C\<^sub>B"
        have "y \<in> C\<^sub>B \<union> C\<^sub>O"
          using hy by (by100 simp)
        thus "y \<in> geotop_polyhedron BdJ\<^sub>N"
          using hBdJ_split by (by100 simp)
      qed
      have hC\<^sub>F_sub_J\<^sub>N: "C\<^sub>B \<subseteq> J\<^sub>N"
        by (rule subset_trans[OF hC\<^sub>F_sub_BdJ hBdJ\<^sub>N_poly_sub_J\<^sub>N])
      have hC\<^sub>F_sub_FrN\<^sub>I: "C\<^sub>B \<subseteq> FrN\<^sub>I"
        by (rule subset_trans[OF hC\<^sub>F_sub_BdJ hBdJ\<^sub>N_poly_sub_FrN\<^sub>I])
      have hC\<^sub>F_A2_QS_disj: "C\<^sub>B \<inter> (A2 \<union> {Q, S}) = {}"
      proof -
        have "C\<^sub>B \<inter> (A2 \<union> {Q, S}) \<subseteq>
            geotop_polyhedron BdJ\<^sub>N \<inter> (A2 \<union> {Q, S})"
          using hC\<^sub>F_sub_BdJ by (by100 blast)
        thus ?thesis
          using hBdJ\<^sub>N_poly_A2_QS_disj by (by100 blast)
      qed
      have hC\<^sub>F_Ncut_disj: "C\<^sub>B \<inter> ?Ncut = {}"
      proof -
        have "C\<^sub>B \<inter> ?Ncut \<subseteq> geotop_polyhedron BdJ\<^sub>N \<inter> ?Ncut"
          using hC\<^sub>F_sub_BdJ by (by100 blast)
        thus ?thesis
          using hNcut_BdJ\<^sub>N_poly_disj by (by100 blast)
      qed
      show ?thesis
        apply (rule exI[where x=X])
        apply (rule exI[where x=C])
        apply (rule exI[where x=L])
        apply (rule exI[where x=C\<^sub>B])
        using hX_B1P hX_ne hC_bl hC_sub_B1P hC_sub_F1 hC_sub_J\<^sub>N
          hC_sub_FrN\<^sub>I hC_F\<^sub>2_disj hC_A2_QS_disj hC_Ncut_disj
          hP_C hX_C hC_end hC_int_connected hC_int_nonempty
          hL_complex hL_1dim hL_fin hL_poly_C hP_L hX_L
          hBdJ_split_C\<^sub>F hC\<^sub>B_bl hC\<^sub>B_end hC_int_disj_C\<^sub>F
          hC_inter_C\<^sub>F hP_C\<^sub>B hX_C\<^sub>B hC\<^sub>F_sub_J\<^sub>N
          hC\<^sub>F_sub_FrN\<^sub>I hC\<^sub>F_A2_QS_disj hC\<^sub>F_Ncut_disj
        by (intro conjI)
    qed
  qed
  have hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}"
    (**
      Book split package for the regular-neighborhood frontier component:
      after the missing no-endpoint step proves the component polygonal,
      the frontier through \<open>P\<close> supplies the two broken-line arcs that Moise
      denotes by the boundary piece and the complementary piece. **)
  proof -
    assume hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    obtain X C L C\<^sub>B C\<^sub>O where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hBdJ_split: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O"
      and hC\<^sub>B_bl: "geotop_is_broken_line C\<^sub>B"
      and hC\<^sub>O_bl: "geotop_is_broken_line C\<^sub>O"
      and hC\<^sub>B_end: "geotop_arc_endpoints C\<^sub>B {P, X}"
      and hC\<^sub>O_end: "geotop_arc_endpoints C\<^sub>O {P, X}"
      and hC_int_disj:
        "geotop_arc_interior C\<^sub>B {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
      using hD44_BdJ\<^sub>N_polygon_split_at_B1P_endpoint[OF hpolygon]
      by (elim exE conjE)
    show ?thesis
      apply (rule exI[where x=X])
      apply (rule exI[where x=C\<^sub>B])
      apply (rule exI[where x=C\<^sub>O])
      using hX_B1P hX_ne hBdJ_split hC\<^sub>B_bl hC\<^sub>O_bl
        hC\<^sub>B_end hC\<^sub>O_end hC_int_disj
      apply (intro conjI)
      by (by100 blast)+
  qed
  have hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split_with_endpoint_members:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}
          \<and> P \<in> C\<^sub>B
          \<and> X \<in> C\<^sub>B
          \<and> P \<in> C\<^sub>O
          \<and> X \<in> C\<^sub>O"
    (**
      Endpoint-explicit form of the same Moise two-arc split.  The later
      lower-to-upper route bookkeeping needs the fact that both broken arcs
      really contain the two cut endpoints, not just the endpoint predicate. **)
  proof -
    assume hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    obtain X C\<^sub>B C\<^sub>O where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hBdJ_split: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O"
      and hC\<^sub>B_bl: "geotop_is_broken_line C\<^sub>B"
      and hC\<^sub>O_bl: "geotop_is_broken_line C\<^sub>O"
      and hC\<^sub>B_end: "geotop_arc_endpoints C\<^sub>B {P, X}"
      and hC\<^sub>O_end: "geotop_arc_endpoints C\<^sub>O {P, X}"
      and hC_int_disj:
        "geotop_arc_interior C\<^sub>B {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
      using hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split[OF hpolygon]
      by (elim exE conjE)
    have hP_C\<^sub>B: "P \<in> C\<^sub>B"
      using hC\<^sub>B_end unfolding geotop_arc_endpoints_def by (by100 blast)
    have hX_C\<^sub>B: "X \<in> C\<^sub>B"
      using hC\<^sub>B_end unfolding geotop_arc_endpoints_def by (by100 blast)
    have hP_C\<^sub>O: "P \<in> C\<^sub>O"
      using hC\<^sub>O_end unfolding geotop_arc_endpoints_def by (by100 blast)
    have hX_C\<^sub>O: "X \<in> C\<^sub>O"
      using hC\<^sub>O_end unfolding geotop_arc_endpoints_def by (by100 blast)
    show ?thesis
      apply (rule exI[where x=X])
      apply (rule exI[where x=C\<^sub>B])
      apply (rule exI[where x=C\<^sub>O])
      using hX_B1P hX_ne hBdJ_split hC\<^sub>B_bl hC\<^sub>O_bl hC\<^sub>B_end
        hC\<^sub>O_end hC_int_disj hP_C\<^sub>B hX_C\<^sub>B hP_C\<^sub>O hX_C\<^sub>O
      apply (intro conjI)
      by (by100 blast)+
  qed
  have hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split_with_endpoint_inter:
      "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}
          \<and> C\<^sub>B \<inter> C\<^sub>O = {P, X}
          \<and> P \<in> C\<^sub>B
          \<and> X \<in> C\<^sub>B
          \<and> P \<in> C\<^sub>O
          \<and> X \<in> C\<^sub>O"
    (**
      Polygonal-frontier version of the endpoint-intersection package.  This
      keeps the "frontier is already a polygon" path and the later exact-two
      incidence path aligned: both expose the fact that Moise's two arcs meet
      exactly at \<open>P\<close> and the chosen boundary endpoint \<open>X\<close>.
    **)
  proof -
    assume hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    obtain X C\<^sub>B C\<^sub>O where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hBdJ_split: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O"
      and hC\<^sub>B_bl: "geotop_is_broken_line C\<^sub>B"
      and hC\<^sub>O_bl: "geotop_is_broken_line C\<^sub>O"
      and hC\<^sub>B_end: "geotop_arc_endpoints C\<^sub>B {P, X}"
      and hC\<^sub>O_end: "geotop_arc_endpoints C\<^sub>O {P, X}"
      and hC_int_disj:
        "geotop_arc_interior C\<^sub>B {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
      and hP_C\<^sub>B: "P \<in> C\<^sub>B"
      and hX_C\<^sub>B: "X \<in> C\<^sub>B"
      and hP_C\<^sub>O: "P \<in> C\<^sub>O"
      and hX_C\<^sub>O: "X \<in> C\<^sub>O"
      using hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split_with_endpoint_members[OF hpolygon]
      by (elim exE conjE)
    have hC_inter: "C\<^sub>B \<inter> C\<^sub>O = {P, X}"
      by (rule geotop_same_endpoint_arcs_inter_eq_prefix
          [OF hC\<^sub>B_end hC\<^sub>O_end hC_int_disj])
    show ?thesis
      apply (rule exI[where x=X])
      apply (rule exI[where x=C\<^sub>B])
      apply (rule exI[where x=C\<^sub>O])
      using hX_B1P hX_ne hBdJ_split hC\<^sub>B_bl hC\<^sub>O_bl hC\<^sub>B_end
        hC\<^sub>O_end hC_int_disj hC_inter hP_C\<^sub>B hX_C\<^sub>B hP_C\<^sub>O hX_C\<^sub>O
      apply (intro conjI)
      by (by100 blast)+
  qed
  have hD44_BdJ\<^sub>N_card_le2_no_endpoint_has_book_two_arc_split:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}"
    (**
      Exact graph-theoretic reduction for Moise's assertion that the frontier
      component is a 1-sphere: local valence at most two plus absence of a
      graph endpoint yields polygonality, hence the book two-arc split. **)
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hnoend:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_card_le2_no_endpoint[OF hle2 hnoend])
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split[OF hpolygon])
  qed
  have hD44_BdJ\<^sub>N_simple_closed_curve_has_book_two_arc_split:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}"
    (**
      Direct formal form of Moise's sentence "Then J is a 1-sphere" for the
      extracted frontier graph: a simple closed curve carrier is enough to
      recover the two broken-line arcs used by the book proof. **)
  proof -
    assume hSCC:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
        (geotop_polyhedron BdJ\<^sub>N)"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_simple_closed_curve[OF hSCC])
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split[OF hpolygon])
  qed
  have hD44_BdJ\<^sub>N_1sphere_has_book_two_arc_split:
      "geotop_is_n_sphere (geotop_polyhedron BdJ\<^sub>N)
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron BdJ\<^sub>N)) 1 \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}"
    (**
      Literal formal version of Moise's sentence "Then J is a 1-sphere":
      because \<open>BdJ\<^sub>N\<close> is already a finite complex, the 1-sphere carrier
      statement is exactly the missing input needed for polygonality and the
      book's two broken-line arcs. **)
  proof -
    assume hsphere:
      "geotop_is_n_sphere (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N)) 1"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      unfolding geotop_is_polygon_def
      using hBdJ\<^sub>N_complex hsphere by (intro exI[where x=BdJ\<^sub>N] conjI) (by100 simp)+
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_polygon_has_book_two_arc_split[OF hpolygon])
  qed
  have hD44_J\<^sub>N_1sphere_has_book_two_arc_split:
      "geotop_is_n_sphere J\<^sub>N
          (subspace_topology UNIV geotop_euclidean_topology J\<^sub>N) 1 \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}"
    (**
      Book statement bridge: Moise names the frontier component through \<open>P\<close>
      as \<open>J\<close> and proves it is a 1-sphere.  Since the preceding finite-complex
      analysis has already identified that component with \<open>geotop_polyhedron
      BdJ\<^sub>N\<close>, this is the literal route from the book's 1-sphere sentence to
      the two broken-line arcs used below. **)
  proof -
    assume hsphere:
      "geotop_is_n_sphere J\<^sub>N
        (subspace_topology UNIV geotop_euclidean_topology J\<^sub>N) 1"
    have hsphere_BdJ:
      "geotop_is_n_sphere (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N)) 1"
      using hsphere hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_1sphere_has_book_two_arc_split[OF hsphere_BdJ])
  qed
  have hD44_BdJ\<^sub>N_card_le2_no_endpoint_imp_J\<^sub>N_1sphere:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
        geotop_is_n_sphere J\<^sub>N
          (subspace_topology UNIV geotop_euclidean_topology J\<^sub>N) 1"
    (**
      Precise remaining regular-neighborhood graph target.  Once the frontier
      component graph has valence at most two and no endpoints, the already
      proved finite-graph classifier makes its carrier polygonal; the equality
      \<open>J\<^sub>N = geotop_polyhedron BdJ\<^sub>N\<close> then turns that into Moise's
      "then \<open>J\<close> is a 1-sphere" statement for the actual frontier component. **)
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hnoend:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_card_le2_no_endpoint[OF hle2 hnoend])
    have hsphere_BdJ:
      "geotop_is_n_sphere (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N)) 1"
      using hpolygon unfolding geotop_is_polygon_def by (by100 blast)
    show ?thesis
      using hsphere_BdJ hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
  qed
  have hD44_BdJ\<^sub>N_exact_two_incident_edges_imp_J\<^sub>N_1sphere:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))) \<Longrightarrow>
        geotop_is_n_sphere J\<^sub>N
          (subspace_topology UNIV geotop_euclidean_topology J\<^sub>N) 1"
    (**
      Link/local-star version of the same book target.  Existing link
      component facts naturally produce an exact-two incident-edge witness at
      every vertex.  This bridge records that such a local 1-manifold statement
      is strong enough to recover Moise's frontier-component 1-sphere. **)
  proof -
    assume htwo:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))"
    have hdegree:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
    proof (intro allI impI)
      fix w
      assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
      have htwo_w:
        "\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2)"
      proof -
        have hspec:
          "{w} \<in> BdJ\<^sub>N \<longrightarrow>
            (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
              geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
              \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
              \<and> e\<^sub>1 \<noteq> e\<^sub>2
              \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
                  \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))"
          using htwo by (rule spec)
        show ?thesis
          using hspec hwBdJ by (by100 simp)
      qed
      obtain e\<^sub>1 e\<^sub>2 where he\<^sub>1BdJ: "e\<^sub>1 \<in> BdJ\<^sub>N"
        and he\<^sub>2BdJ: "e\<^sub>2 \<in> BdJ\<^sub>N"
        and he\<^sub>1edge: "geotop_is_edge e\<^sub>1"
        and hwe\<^sub>1: "w \<in> e\<^sub>1"
        and he\<^sub>2edge: "geotop_is_edge e\<^sub>2"
        and hwe\<^sub>2: "w \<in> e\<^sub>2"
        and he12: "e\<^sub>1 \<noteq> e\<^sub>2"
        and hexhaust:
          "\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
            \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2"
        using htwo_w by (elim bexE exE conjE)
      let ?E = "{e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e}"
      have hE_eq: "?E = {e\<^sub>1, e\<^sub>2}"
      proof
        show "?E \<subseteq> {e\<^sub>1, e\<^sub>2}"
        proof
          fix e
          assume heE: "e \<in> ?E"
          have heprops: "e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e"
            using heE by (by100 simp)
          have hexhaust_e:
            "e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2"
            using hexhaust by (rule spec)
          have he_cases: "e = e\<^sub>1 \<or> e = e\<^sub>2"
            using hexhaust_e heprops by (by100 simp)
          show "e \<in> {e\<^sub>1, e\<^sub>2}"
            using he_cases by (by100 simp)
        qed
        show "{e\<^sub>1, e\<^sub>2} \<subseteq> ?E"
        proof
          fix e
          assume he_pair: "e \<in> {e\<^sub>1, e\<^sub>2}"
          have he_cases: "e = e\<^sub>1 \<or> e = e\<^sub>2"
            using he_pair by (by100 simp)
          show "e \<in> ?E"
          proof (rule disjE[OF he_cases])
            assume he: "e = e\<^sub>1"
            show "e \<in> ?E"
              using he he\<^sub>1BdJ he\<^sub>1edge hwe\<^sub>1 by (by100 simp)
          next
            assume he: "e = e\<^sub>2"
            show "e \<in> ?E"
              using he he\<^sub>2BdJ he\<^sub>2edge hwe\<^sub>2 by (by100 simp)
          qed
        qed
      qed
      show "card ?E = 2"
        using hE_eq he12 by (by100 simp)
    qed
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_degree_two[OF hdegree])
    have hsphere_BdJ:
      "geotop_is_n_sphere (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N)) 1"
      using hpolygon unfolding geotop_is_polygon_def by (by100 blast)
    show ?thesis
      using hsphere_BdJ hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
  qed
  have hD44_BdJ\<^sub>N_exact_two_boundary_subarc_complement_split:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))) \<Longrightarrow>
        \<exists>X C L C\<^sub>F. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_is_broken_line C
          \<and> C \<subseteq> ?B1P
          \<and> C \<subseteq> F\<^sub>1
          \<and> C \<subseteq> J\<^sub>N
          \<and> C \<subseteq> FrN\<^sub>I
          \<and> C \<inter> F\<^sub>2 = {}
          \<and> C \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C \<inter> ?Ncut = {}
          \<and> P \<in> C
          \<and> X \<in> C
          \<and> geotop_arc_endpoints C {P, X}
          \<and> connected (geotop_arc_interior C {P, X})
          \<and> geotop_arc_interior C {P, X} \<noteq> {}
          \<and> geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> {P} \<in> L
          \<and> {X} \<in> L
          \<and> geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>F
          \<and> geotop_is_broken_line C\<^sub>F
          \<and> geotop_arc_endpoints C\<^sub>F {P, X}
          \<and> geotop_arc_interior C {P, X} \<inter>
              geotop_arc_interior C\<^sub>F {P, X} = {}
          \<and> C \<inter> C\<^sub>F = {P, X}
          \<and> P \<in> C\<^sub>F
          \<and> X \<in> C\<^sub>F
          \<and> C\<^sub>F \<subseteq> J\<^sub>N
          \<and> C\<^sub>F \<subseteq> FrN\<^sub>I
          \<and> C\<^sub>F \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C\<^sub>F \<inter> ?Ncut = {}"
    (**
      Exact-two incidence form of the oriented Moise frontier split.  This is
      the bridge from the local regular-neighborhood graph statement to the
      already oriented boundary subarc plus complementary frontier arc package.
    **)
  proof -
    assume htwo:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))"
    have hsphere:
        "geotop_is_n_sphere J\<^sub>N
          (subspace_topology UNIV geotop_euclidean_topology J\<^sub>N) 1"
      by (rule hD44_BdJ\<^sub>N_exact_two_incident_edges_imp_J\<^sub>N_1sphere[OF htwo])
    have hsphere_BdJ:
      "geotop_is_n_sphere (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N)) 1"
      using hsphere hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      unfolding geotop_is_polygon_def
    proof (intro exI[where x=BdJ\<^sub>N] conjI)
      show "geotop_is_complex BdJ\<^sub>N"
        by (rule hBdJ\<^sub>N_complex)
      show "geotop_polyhedron BdJ\<^sub>N = geotop_polyhedron BdJ\<^sub>N"
        by (by100 simp)
      show "geotop_is_n_sphere (geotop_polyhedron BdJ\<^sub>N)
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N)) 1"
        by (rule hsphere_BdJ)
    qed
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_polygon_boundary_subarc_complement_split[OF hpolygon])
  qed
  have hD44_BdJ\<^sub>N_degree_two_exact_two_incident_edges:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2) \<Longrightarrow>
      (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2)))"
    (**
      Degree-two form of the local regular-neighborhood incidence statement.
      Several earlier graph packages naturally produce cardinality two at each
      frontier vertex; the complementary frontier split wants the explicit two
      incident edges and their exhaustion property. **)
  proof (intro allI impI)
    assume hdegree:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
    fix w
    assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
    obtain e\<^sub>1 e\<^sub>2 where he\<^sub>1BdJ: "e\<^sub>1 \<in> BdJ\<^sub>N"
      and he\<^sub>2BdJ: "e\<^sub>2 \<in> BdJ\<^sub>N"
      and he\<^sub>1edge: "geotop_is_edge e\<^sub>1"
      and he\<^sub>2edge: "geotop_is_edge e\<^sub>2"
      and hwe\<^sub>1: "w \<in> e\<^sub>1"
      and hwe\<^sub>2: "w \<in> e\<^sub>2"
      and he12: "e\<^sub>1 \<noteq> e\<^sub>2"
      and hE_eq:
        "{e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = {e\<^sub>1, e\<^sub>2}"
      using geotop_degree_two_vertex_two_distinct_incident_edges_prefix
        [OF hdegree hwBdJ]
      by (elim exE conjE)
    have hexhaust:
        "\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
          \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2"
    proof (intro allI impI)
      fix e
      assume he: "e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e"
      have "e \<in> {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e}"
        using he by (by100 simp)
      hence "e \<in> {e\<^sub>1, e\<^sub>2}"
        using hE_eq by (by100 simp)
      thus "e = e\<^sub>1 \<or> e = e\<^sub>2"
        by (by100 simp)
    qed
    show "\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
        geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
        \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
        \<and> e\<^sub>1 \<noteq> e\<^sub>2
        \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
            \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2)"
      using he\<^sub>1BdJ he\<^sub>2BdJ he\<^sub>1edge he\<^sub>2edge hwe\<^sub>1 hwe\<^sub>2 he12 hexhaust
      by (by100 blast)
  qed
  have hD44_BdJ\<^sub>N_degree_two_boundary_subarc_complement_split:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2) \<Longrightarrow>
        \<exists>X C L C\<^sub>F. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_is_broken_line C
          \<and> C \<subseteq> ?B1P
          \<and> C \<subseteq> F\<^sub>1
          \<and> C \<subseteq> J\<^sub>N
          \<and> C \<subseteq> FrN\<^sub>I
          \<and> C \<inter> F\<^sub>2 = {}
          \<and> C \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C \<inter> ?Ncut = {}
          \<and> P \<in> C
          \<and> X \<in> C
          \<and> geotop_arc_endpoints C {P, X}
          \<and> connected (geotop_arc_interior C {P, X})
          \<and> geotop_arc_interior C {P, X} \<noteq> {}
          \<and> geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> {P} \<in> L
          \<and> {X} \<in> L
          \<and> geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>F
          \<and> geotop_is_broken_line C\<^sub>F
          \<and> geotop_arc_endpoints C\<^sub>F {P, X}
          \<and> geotop_arc_interior C {P, X} \<inter>
              geotop_arc_interior C\<^sub>F {P, X} = {}
          \<and> C \<inter> C\<^sub>F = {P, X}
          \<and> P \<in> C\<^sub>F
          \<and> X \<in> C\<^sub>F
          \<and> C\<^sub>F \<subseteq> J\<^sub>N
          \<and> C\<^sub>F \<subseteq> FrN\<^sub>I
          \<and> C\<^sub>F \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C\<^sub>F \<inter> ?Ncut = {}"
    (**
      Same Moise frontier split, but keyed by the degree-two statement that the
      local frontier graph analysis is expected to establish. **)
  proof -
    assume hdegree:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
    have htwo:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))"
      by (rule hD44_BdJ\<^sub>N_degree_two_exact_two_incident_edges[OF hdegree])
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_exact_two_boundary_subarc_complement_split[OF htwo])
  qed
  have hD44_BdJ\<^sub>N_card_bounds_boundary_subarc_complement_split:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        (\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2) \<Longrightarrow>
        \<exists>X C L C\<^sub>F. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_is_broken_line C
          \<and> C \<subseteq> ?B1P
          \<and> C \<subseteq> F\<^sub>1
          \<and> C \<subseteq> J\<^sub>N
          \<and> C \<subseteq> FrN\<^sub>I
          \<and> C \<inter> F\<^sub>2 = {}
          \<and> C \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C \<inter> ?Ncut = {}
          \<and> P \<in> C
          \<and> X \<in> C
          \<and> geotop_arc_endpoints C {P, X}
          \<and> connected (geotop_arc_interior C {P, X})
          \<and> geotop_arc_interior C {P, X} \<noteq> {}
          \<and> geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> {P} \<in> L
          \<and> {X} \<in> L
          \<and> geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>F
          \<and> geotop_is_broken_line C\<^sub>F
          \<and> geotop_arc_endpoints C\<^sub>F {P, X}
          \<and> geotop_arc_interior C {P, X} \<inter>
              geotop_arc_interior C\<^sub>F {P, X} = {}
          \<and> C \<inter> C\<^sub>F = {P, X}
          \<and> P \<in> C\<^sub>F
          \<and> X \<in> C\<^sub>F
          \<and> C\<^sub>F \<subseteq> J\<^sub>N
          \<and> C\<^sub>F \<subseteq> FrN\<^sub>I
          \<and> C\<^sub>F \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C\<^sub>F \<inter> ?Ncut = {}"
    (**
      Book-aligned incidence entry point for the frontier split.  The next
      D44 graph task can now target the literal local regular-neighborhood
      bounds at each vertex of the frontier component: at most two boundary
      edges and at least two boundary edges.  Those bounds give degree two,
      and the already-proved degree-two package gives Moise's boundary arc
      and complementary frontier arc \<open>C\<^sub>F\<close>. **)
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hge2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
    have hdegree:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule hBdJ\<^sub>N_vertex_degree_two_from_card_bounds[OF hle2 hge2])
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_degree_two_boundary_subarc_complement_split
          [OF hdegree])
  qed
  have hD44_BdJ\<^sub>N_card_le2_no_endpoint_boundary_subarc_complement_split:
      "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
        \<exists>X C L C\<^sub>F. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_is_broken_line C
          \<and> C \<subseteq> ?B1P
          \<and> C \<subseteq> F\<^sub>1
          \<and> C \<subseteq> J\<^sub>N
          \<and> C \<subseteq> FrN\<^sub>I
          \<and> C \<inter> F\<^sub>2 = {}
          \<and> C \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C \<inter> ?Ncut = {}
          \<and> P \<in> C
          \<and> X \<in> C
          \<and> geotop_arc_endpoints C {P, X}
          \<and> connected (geotop_arc_interior C {P, X})
          \<and> geotop_arc_interior C {P, X} \<noteq> {}
          \<and> geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> {P} \<in> L
          \<and> {X} \<in> L
          \<and> geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>F
          \<and> geotop_is_broken_line C\<^sub>F
          \<and> geotop_arc_endpoints C\<^sub>F {P, X}
          \<and> geotop_arc_interior C {P, X} \<inter>
              geotop_arc_interior C\<^sub>F {P, X} = {}
          \<and> C \<inter> C\<^sub>F = {P, X}
          \<and> P \<in> C\<^sub>F
          \<and> X \<in> C\<^sub>F
          \<and> C\<^sub>F \<subseteq> J\<^sub>N
          \<and> C\<^sub>F \<subseteq> FrN\<^sub>I
          \<and> C\<^sub>F \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C\<^sub>F \<inter> ?Ncut = {}"
    (**
      Older frontier graph target, connected to the stronger C/C_F output:
      valence at most two plus no endpoints makes every vertex degree two, and
      the degree-two package supplies the book's selected boundary arc and
      complementary frontier arc. **)
  proof -
    assume hle2:
      "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    assume hnoend:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
    have hdegree:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule hBdJ\<^sub>N_vertex_degree_two_from_card_le2_no_endpoint
          [OF hle2 hnoend])
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_degree_two_boundary_subarc_complement_split
          [OF hdegree])
  qed
  have hD44_BdJ\<^sub>N_simple_closed_curve_boundary_subarc_complement_split:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
        \<exists>X C L C\<^sub>F. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_is_broken_line C
          \<and> C \<subseteq> ?B1P
          \<and> C \<subseteq> F\<^sub>1
          \<and> C \<subseteq> J\<^sub>N
          \<and> C \<subseteq> FrN\<^sub>I
          \<and> C \<inter> F\<^sub>2 = {}
          \<and> C \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C \<inter> ?Ncut = {}
          \<and> P \<in> C
          \<and> X \<in> C
          \<and> geotop_arc_endpoints C {P, X}
          \<and> connected (geotop_arc_interior C {P, X})
          \<and> geotop_arc_interior C {P, X} \<noteq> {}
          \<and> geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> {P} \<in> L
          \<and> {X} \<in> L
          \<and> geotop_polyhedron BdJ\<^sub>N = C \<union> C\<^sub>F
          \<and> geotop_is_broken_line C\<^sub>F
          \<and> geotop_arc_endpoints C\<^sub>F {P, X}
          \<and> geotop_arc_interior C {P, X} \<inter>
              geotop_arc_interior C\<^sub>F {P, X} = {}
          \<and> C \<inter> C\<^sub>F = {P, X}
          \<and> P \<in> C\<^sub>F
          \<and> X \<in> C\<^sub>F
          \<and> C\<^sub>F \<subseteq> J\<^sub>N
          \<and> C\<^sub>F \<subseteq> FrN\<^sub>I
          \<and> C\<^sub>F \<inter> (A2 \<union> {Q, S}) = {}
          \<and> C\<^sub>F \<inter> ?Ncut = {}"
    (**
      Direct simple-closed-curve entry point for the same Moise frontier split.
      If the frontier component is proved as a simple closed curve first, the
      existing polygon conversion immediately gives the C/C_F package. **)
  proof -
    assume hSCC:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
        (geotop_polyhedron BdJ\<^sub>N)"
    have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      by (rule hBdJ\<^sub>N_polygon_from_simple_closed_curve[OF hSCC])
    show ?thesis
      by (rule hD44_BdJ\<^sub>N_polygon_boundary_subarc_complement_split
          [OF hpolygon])
  qed
  have hD44_BdJ\<^sub>N_exact_two_has_book_two_arc_split:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}"
    (**
      Direct book-route package from the local regular-neighborhood incidence
      statement to Moise's two frontier arcs.  The remaining geometric work can
      now target exact-two boundary incidence and then immediately recover the
      split of the frontier component through \<open>P\<close>. **)
  proof -
    assume htwo:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))"
    have hsphere:
        "geotop_is_n_sphere J\<^sub>N
          (subspace_topology UNIV geotop_euclidean_topology J\<^sub>N) 1"
      by (rule hD44_BdJ\<^sub>N_exact_two_incident_edges_imp_J\<^sub>N_1sphere[OF htwo])
    show ?thesis
      by (rule hD44_J\<^sub>N_1sphere_has_book_two_arc_split[OF hsphere])
  qed
  have hD44_BdJ\<^sub>N_exact_two_has_book_two_arc_split_with_endpoint_members:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}
          \<and> P \<in> C\<^sub>B
          \<and> X \<in> C\<^sub>B
          \<and> P \<in> C\<^sub>O
          \<and> X \<in> C\<^sub>O"
    (**
      Endpoint-explicit exact-two incidence package.  This is the expected
      formal output of the local regular-neighborhood graph step: exact two
      incident boundary edges at every frontier vertex give the two Moise arcs,
      with their shared endpoints available as ordinary membership facts. **)
  proof -
    assume htwo:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))"
    obtain X C\<^sub>B C\<^sub>O where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hBdJ_split: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O"
      and hC\<^sub>B_bl: "geotop_is_broken_line C\<^sub>B"
      and hC\<^sub>O_bl: "geotop_is_broken_line C\<^sub>O"
      and hC\<^sub>B_end: "geotop_arc_endpoints C\<^sub>B {P, X}"
      and hC\<^sub>O_end: "geotop_arc_endpoints C\<^sub>O {P, X}"
      and hC_int_disj:
        "geotop_arc_interior C\<^sub>B {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
      using hD44_BdJ\<^sub>N_exact_two_has_book_two_arc_split[OF htwo]
      by (elim exE conjE)
    have hP_C\<^sub>B: "P \<in> C\<^sub>B"
      using hC\<^sub>B_end unfolding geotop_arc_endpoints_def by (by100 blast)
    have hX_C\<^sub>B: "X \<in> C\<^sub>B"
      using hC\<^sub>B_end unfolding geotop_arc_endpoints_def by (by100 blast)
    have hP_C\<^sub>O: "P \<in> C\<^sub>O"
      using hC\<^sub>O_end unfolding geotop_arc_endpoints_def by (by100 blast)
    have hX_C\<^sub>O: "X \<in> C\<^sub>O"
      using hC\<^sub>O_end unfolding geotop_arc_endpoints_def by (by100 blast)
    show ?thesis
      apply (rule exI[where x=X])
      apply (rule exI[where x=C\<^sub>B])
      apply (rule exI[where x=C\<^sub>O])
      using hX_B1P hX_ne hBdJ_split hC\<^sub>B_bl hC\<^sub>O_bl hC\<^sub>B_end
        hC\<^sub>O_end hC_int_disj hP_C\<^sub>B hX_C\<^sub>B hP_C\<^sub>O hX_C\<^sub>O
      apply (intro conjI)
      by (by100 blast)+
  qed
  have hD44_BdJ\<^sub>N_exact_two_has_book_two_arc_split_with_endpoint_inter:
      "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))) \<Longrightarrow>
        \<exists>X C\<^sub>B C\<^sub>O. X \<in> ?B1P
          \<and> X \<noteq> P
          \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O
          \<and> geotop_is_broken_line C\<^sub>B
          \<and> geotop_is_broken_line C\<^sub>O
          \<and> geotop_arc_endpoints C\<^sub>B {P, X}
          \<and> geotop_arc_endpoints C\<^sub>O {P, X}
          \<and> geotop_arc_interior C\<^sub>B {P, X} \<inter>
              geotop_arc_interior C\<^sub>O {P, X} = {}
          \<and> C\<^sub>B \<inter> C\<^sub>O = {P, X}
          \<and> P \<in> C\<^sub>B
          \<and> X \<in> C\<^sub>B
          \<and> P \<in> C\<^sub>O
          \<and> X \<in> C\<^sub>O"
    (**
      Endpoint-intersection form of the exact-two frontier split.  Moise's
      later "other arc" choice uses that the two arcs through \<open>P\<close> and \<open>X\<close>
      meet only at their endpoints, so record that consequence next to the
      endpoint-explicit split rather than reproving it at each orientation use.
    **)
  proof -
    assume htwo:
      "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        (\<exists>e\<^sub>1\<in>BdJ\<^sub>N. \<exists>e\<^sub>2\<in>BdJ\<^sub>N.
          geotop_is_edge e\<^sub>1 \<and> w \<in> e\<^sub>1
          \<and> geotop_is_edge e\<^sub>2 \<and> w \<in> e\<^sub>2
          \<and> e\<^sub>1 \<noteq> e\<^sub>2
          \<and> (\<forall>e. e \<in> BdJ\<^sub>N \<and> geotop_is_edge e \<and> w \<in> e
              \<longrightarrow> e = e\<^sub>1 \<or> e = e\<^sub>2))"
    obtain X C\<^sub>B C\<^sub>O where hX_B1P: "X \<in> ?B1P"
      and hX_ne: "X \<noteq> P"
      and hBdJ_split: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>B \<union> C\<^sub>O"
      and hC\<^sub>B_bl: "geotop_is_broken_line C\<^sub>B"
      and hC\<^sub>O_bl: "geotop_is_broken_line C\<^sub>O"
      and hC\<^sub>B_end: "geotop_arc_endpoints C\<^sub>B {P, X}"
      and hC\<^sub>O_end: "geotop_arc_endpoints C\<^sub>O {P, X}"
      and hC_int_disj:
        "geotop_arc_interior C\<^sub>B {P, X} \<inter>
          geotop_arc_interior C\<^sub>O {P, X} = {}"
      and hP_C\<^sub>B: "P \<in> C\<^sub>B"
      and hX_C\<^sub>B: "X \<in> C\<^sub>B"
      and hP_C\<^sub>O: "P \<in> C\<^sub>O"
      and hX_C\<^sub>O: "X \<in> C\<^sub>O"
      using hD44_BdJ\<^sub>N_exact_two_has_book_two_arc_split_with_endpoint_members[OF htwo]
      by (elim exE conjE)
    have hC_inter: "C\<^sub>B \<inter> C\<^sub>O = {P, X}"
      by (rule geotop_same_endpoint_arcs_inter_eq_prefix
          [OF hC\<^sub>B_end hC\<^sub>O_end hC_int_disj])
    show ?thesis
      apply (rule exI[where x=X])
      apply (rule exI[where x=C\<^sub>B])
      apply (rule exI[where x=C\<^sub>O])
      using hX_B1P hX_ne hBdJ_split hC\<^sub>B_bl hC\<^sub>O_bl hC\<^sub>B_end
        hC\<^sub>O_end hC_int_disj hC_inter hP_C\<^sub>B hX_C\<^sub>B hP_C\<^sub>O hX_C\<^sub>O
      apply (intro conjI)
      by (by100 blast)+
  qed
  have hD44_B1P_F\<^sub>2_setdist_pos: "0 < setdist ?B1P F\<^sub>2"
  proof -
    have hsd_iff:
        "(0 < setdist ?B1P F\<^sub>2) =
          (?B1P \<noteq> {} \<and> F\<^sub>2 \<noteq> {} \<and> ?B1P \<inter> F\<^sub>2 = {})"
      by (rule setdist_gt_0_compact_closed
          [OF hD44_B1P_compact hD44_F\<^sub>2_closed])
    show ?thesis
      using hsd_iff hD44_P_B1P hD44_F\<^sub>2_nonempty hD44_B1P_F\<^sub>2_disj
      by (by100 blast)
  qed
  have hD44_B1P_inter_J: "?B1P \<inter> J = ?B1P"
    using hD44_B1P_sub_B\<^sub>1 by (by100 blast)
  have hA2_closed: "closed A2"
    using geotop_two_arcs_compact_closed_prefix[OF hA1 hA2] by (by100 blast)
  have hD44_A2_QS_closed: "closed (A2 \<union> {Q, S})"
    using hA2_closed by (by100 simp)
  have hD44_A2_QS_nonempty: "A2 \<union> {Q, S} \<noteq> {}"
    by (by100 blast)
  have hD44_B1P_forbidden_setdist_pos:
      "0 < setdist ?B1P (A2 \<union> {Q, S})"
  proof -
    have hsd_iff:
        "(0 < setdist ?B1P (A2 \<union> {Q, S})) =
          (?B1P \<noteq> {} \<and> A2 \<union> {Q, S} \<noteq> {}
            \<and> ?B1P \<inter> (A2 \<union> {Q, S}) = {})"
      by (rule setdist_gt_0_compact_closed
          [OF hD44_B1P_compact hD44_A2_QS_closed])
    show ?thesis
      using hsd_iff hD44_P_B1P hD44_A2_QS_nonempty hD44_B1P_A2_QS_disj
      by (by100 blast)
  qed
  have hN_A2_closed: "closed (N \<union> A2)"
    by (rule closed_Un[OF hN_closed hA2_closed])
  have hI_open_HOL: "open (geotop_polygon_interior J)"
    by (rule polygon_interior_open[OF hJ])
  have hNcut_open_HOL: "open ?Ncut"
    by (rule open_Diff[OF hI_open_HOL hN_A2_closed])
  have hNcut_open: "?Ncut \<in> geotop_euclidean_topology"
    using hNcut_open_HOL
    unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have hD44_Q1_local_Ncut_ball:
      "\<exists>\<epsilon>>0. ball Q1 \<epsilon> \<subseteq> ?Ncut"
    (**
      Local access hygiene for the final Moise frontier-route attachment:
      the chosen point near \<open>Q\<close> is not merely in the outside-carrier region;
      it has a genuine Euclidean collar inside
      \<open>geotop_polygon_interior J - (N \<union> A2)\<close>. **)
    using hNcut_open_HOL hQ1_Ncut open_contains_ball by (by100 blast)
  have hD44_S1_local_Ncut_ball:
      "\<exists>\<epsilon>>0. ball S1 \<epsilon> \<subseteq> ?Ncut"
    (**
      Symmetric local access collar near \<open>S\<close>, used to attach the endpoint
      chosen in the small boundary ball to the same outside component once the
      regular-neighborhood frontier subarc has been constructed. **)
    using hNcut_open_HOL hS1_Ncut open_contains_ball by (by100 blast)
  have hD44_same_component_in_Ncut_suffices:
      "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<Longrightarrow> \<exists>B. geotop_is_broken_line B
          \<and> B \<subseteq> ?Ncut
          \<and> Q1 \<in> B
          \<and> S1 \<in> B"
  proof -
    assume hS1_comp:
      "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    show ?thesis
      by (rule geotop_open_component_broken_line_between_prefix
          [OF hNcut_open hQ1_Ncut hS1_comp])
  qed
  have hD44_connected_route_component_suffices:
      "\<And>W. W \<subseteq> ?Ncut \<Longrightarrow> Q1 \<in> W \<Longrightarrow> S1 \<in> W \<Longrightarrow>
        top1_connected_on W
          (subspace_topology UNIV geotop_euclidean_topology W) \<Longrightarrow>
        S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    (**
      Pure component bookkeeping for Moise's frontier route: once the
      regular-neighborhood boundary analysis supplies a connected witness in
      \<open>I - (N \<union> A2)\<close> through the two local access endpoints, the endpoints are
      in the same ambient component. **)
    by (rule geotop_connected_witness_component_at_intro_prefix)
  have hD44_broken_line_route_component_suffices:
      "\<exists>B. geotop_is_broken_line B
        \<and> B \<subseteq> ?Ncut
        \<and> Q1 \<in> B
        \<and> S1 \<in> B
        \<Longrightarrow> S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut Q1"
    (**
      Direct Moise-form reduction: the remaining frontier analysis may now
      target exactly the book's broken line \<open>B\<close> in
      \<open>I - (N \<union> A2)\<close>.  Once such a broken line is constructed, connectedness
      of broken lines supplies the component relation. **)
  proof -
    assume hB_ex:
      "\<exists>B. geotop_is_broken_line B
        \<and> B \<subseteq> ?Ncut
        \<and> Q1 \<in> B
        \<and> S1 \<in> B"
    obtain B where hB_bl: "geotop_is_broken_line B"
      and hB_sub: "B \<subseteq> ?Ncut"
      and hQ1_B: "Q1 \<in> B"
      and hS1_B: "S1 \<in> B"
      using hB_ex by (elim exE conjE)
    have hB_conn:
        "top1_connected_on B
          (subspace_topology UNIV geotop_euclidean_topology B)"
      by (rule geotop_broken_line_connected_on_prefix[OF hB_bl])
    show "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
        ?Ncut Q1"
      by (rule hD44_connected_route_component_suffices
          [OF hB_sub hQ1_B hS1_B hB_conn])
  qed
  have hD44_Q1_Ncut_component_package:
      "\<exists>C. C = geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut Q1
        \<and> C \<subseteq> ?Ncut
        \<and> Q1 \<in> C
        \<and> C \<in> geotop_euclidean_topology
        \<and> top1_connected_on C
            (subspace_topology UNIV geotop_euclidean_topology C)"
    (**
      Names the outside-carrier component that Moise's lower-to-upper
      frontier subarc must enter.  The final book step is now precisely to
      show that the access point near \<open>S\<close> lies in this open connected
      component of \<open>I - (N \<union> A2)\<close>. **)
  proof -
    let ?C = "geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    have hC_open: "?C \<in> geotop_euclidean_topology"
      by (rule geotop_component_at_open_in_euclidean[OF hNcut_open hQ1_Ncut])
    have hC_eq: "?C = connected_component_set ?Ncut Q1"
      by (rule geotop_component_at_UNIV_eq_connected_component_set)
    have hC_sub: "?C \<subseteq> ?Ncut"
      using hC_eq connected_component_subset by (by100 simp)
    have hQ1_C: "Q1 \<in> ?C"
      using hC_eq hQ1_Ncut connected_component_refl by (by100 simp)
    have hC_conn_HOL: "connected ?C"
      using hC_eq connected_connected_component by (by100 simp)
    have hC_conn:
        "top1_connected_on ?C
          (subspace_topology UNIV geotop_euclidean_topology ?C)"
      using hC_conn_HOL top1_connected_on_geotop_iff_connected by (by100 blast)
    show ?thesis
    proof (rule exI[where x="?C"], intro conjI)
      show "?C = geotop_component_at UNIV geotop_euclidean_topology
          ?Ncut Q1"
        by (by100 simp)
      show "?C \<subseteq> ?Ncut" by (rule hC_sub)
      show "Q1 \<in> ?C" by (rule hQ1_C)
      show "?C \<in> geotop_euclidean_topology" by (rule hC_open)
      show "top1_connected_on ?C
          (subspace_topology UNIV geotop_euclidean_topology ?C)"
        by (rule hC_conn)
    qed
  qed
  have hD44_same_component_gives_closed_corridor:
      "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<Longrightarrow> \<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Q1 \<in> closure Z
          \<and> S1 \<in> closure Z"
    (**
      Converts Moise's final same-component statement into the closed-corridor
      form used by the collar machinery below.  The corridor is simply the
      \<open>Q1\<close>-component of \<open>I - (N \<union> A2)\<close>; once \<open>S1\<close> lies in it, both access
      points lie in its ordinary closure. **)
    by (rule geotop_component_member_gives_closed_corridor_prefix)
  have hD44_Ncut_open_split_if_not_same_component:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<Longrightarrow> ?Ncut =
          geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1 \<union>
          (?Ncut - geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1)
        \<and> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1 \<inter>
          (?Ncut - geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1) = {}
        \<and> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
          \<in> geotop_euclidean_topology
        \<and> ?Ncut - geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
          \<in> geotop_euclidean_topology
        \<and> Q1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<and> S1 \<in> ?Ncut -
          geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    (**
      Contradiction setup for the remaining Moise step.  If the lower-to-upper
      frontier route did not put \<open>S1\<close> in the \<open>Q1\<close> outside-carrier component,
      the open set \<open>I - (N \<union> A2)\<close> would split into the \<open>Q1\<close> component and its
      complementary open side containing \<open>S1\<close>.  The unfinished book argument
      must rule out exactly this split using the frontier component through
      \<open>P\<close>. **)
  proof -
    assume hnot:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    let ?CQ = "geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    let ?CS = "geotop_component_at UNIV geotop_euclidean_topology ?Ncut S1"
    have hTU: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
      by (metis geotop_euclidean_topology_eq_open_sets
          top1_open_sets_is_topology_on_UNIV)
    have hS1_sing_conn:
        "top1_connected_on {S1}
          (subspace_topology UNIV geotop_euclidean_topology {S1})"
      by (rule top1_connected_on_singleton[OF hTU], simp)
    have hS1_CS: "S1 \<in> ?CS"
      by (rule geotop_self_in_component_at[OF hS1_Ncut hS1_sing_conn])
    have hcomp_neq: "?CQ \<noteq> ?CS"
    proof
      assume heq: "?CQ = ?CS"
      have "S1 \<in> ?CQ"
        using heq hS1_CS by (by100 simp)
      thus False
        using hnot by (by100 blast)
    qed
    show ?thesis
      by (rule geotop_open_component_complement_split_prefix
          [OF hNcut_open hQ1_Ncut hS1_Ncut hcomp_neq])
  qed
  have hD44_Ncut_open_split_access_balls_if_not_same_component:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<Longrightarrow> \<exists>\<epsilon>\<^sub>Q>0. \<exists>\<epsilon>\<^sub>S>0.
          ball Q1 \<epsilon>\<^sub>Q \<subseteq>
            geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
          \<and> ball S1 \<epsilon>\<^sub>S \<subseteq>
            ?Ncut - geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    (**
      Local-collar version of the contradiction split.  If \<open>Q1\<close> and \<open>S1\<close>
      were on different outside-carrier components, then the two sides of the
      split would contain genuine Euclidean balls around the access points.
      These are the open collars that the final frontier subarc must connect
      through Moise's lower-to-upper construction. **)
  proof -
    assume hnot:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    let ?CQ = "geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    let ?W = "?Ncut - ?CQ"
    have hsplit:
        "?Ncut = ?CQ \<union> ?W
        \<and> ?CQ \<inter> ?W = {}
        \<and> ?CQ \<in> geotop_euclidean_topology
        \<and> ?W \<in> geotop_euclidean_topology
        \<and> Q1 \<in> ?CQ
        \<and> S1 \<in> ?W"
      by (rule hD44_Ncut_open_split_if_not_same_component[OF hnot])
    have hCQ_open_top: "?CQ \<in> geotop_euclidean_topology"
      using hsplit by (by100 blast)
    have hW_open_top: "?W \<in> geotop_euclidean_topology"
      using hsplit by (by100 blast)
    have hQ1_CQ: "Q1 \<in> ?CQ"
      using hsplit by (by100 blast)
    have hS1_W: "S1 \<in> ?W"
      using hsplit by (by100 blast)
    have hCQ_open_HOL: "open ?CQ"
      by (metis hCQ_open_top geotop_euclidean_topology_eq_open_sets
          mem_Collect_eq top1_open_sets_def)
    have hW_open_HOL: "open ?W"
      by (metis hW_open_top geotop_euclidean_topology_eq_open_sets
          mem_Collect_eq top1_open_sets_def)
    have hQ_ball_ex: "\<exists>\<epsilon>>0. ball Q1 \<epsilon> \<subseteq> ?CQ"
      using hCQ_open_HOL hQ1_CQ unfolding open_contains_ball by (by100 simp)
    have hS_ball_ex: "\<exists>\<epsilon>>0. ball S1 \<epsilon> \<subseteq> ?W"
      using hW_open_HOL hS1_W unfolding open_contains_ball by (by100 simp)
    obtain \<epsilon>\<^sub>Q where h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
      and hball_Q1_CQ: "ball Q1 \<epsilon>\<^sub>Q \<subseteq> ?CQ"
      using hQ_ball_ex by (elim exE conjE)
    obtain \<epsilon>\<^sub>S where h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
      and hball_S1_W: "ball S1 \<epsilon>\<^sub>S \<subseteq> ?W"
      using hS_ball_ex by (elim exE conjE)
    show ?thesis
    proof (rule exI[where x=\<epsilon>\<^sub>Q], intro conjI)
      show "0 < \<epsilon>\<^sub>Q" by (rule h\<epsilon>\<^sub>Q_pos)
      show "\<exists>\<epsilon>\<^sub>S>0.
          ball Q1 \<epsilon>\<^sub>Q \<subseteq> ?CQ \<and> ball S1 \<epsilon>\<^sub>S \<subseteq> ?W"
      proof (rule exI[where x=\<epsilon>\<^sub>S], intro conjI)
        show "0 < \<epsilon>\<^sub>S" by (rule h\<epsilon>\<^sub>S_pos)
        show "ball Q1 \<epsilon>\<^sub>Q \<subseteq> ?CQ" by (rule hball_Q1_CQ)
        show "ball S1 \<epsilon>\<^sub>S \<subseteq> ?W" by (rule hball_S1_W)
      qed
    qed
  qed
  have hD44_Ncut_open_split_forbids_connected_crossing:
      "\<And>Z. S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<Longrightarrow> Z \<subseteq> ?Ncut
        \<Longrightarrow> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
        \<Longrightarrow> Z \<inter> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1 \<noteq> {}
        \<Longrightarrow> Z \<inter>
              (?Ncut - geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1)
              \<noteq> {}
        \<Longrightarrow> False"
    (**
      Separation form of the remaining contradiction.  Once the negation of the
      desired component relation has split \<open>Ncut\<close>, no connected set contained
      in \<open>Ncut\<close> can meet both the \<open>Q1\<close> side and the complementary \<open>S1\<close> side.
      The unfinished Moise frontier subarc should supply exactly such a
      connected crossing, thereby closing the central route step. **)
  proof -
    fix Z
    assume hnot:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    assume hZ_sub: "Z \<subseteq> ?Ncut"
    assume hZ_conn:
      "top1_connected_on Z
        (subspace_topology UNIV geotop_euclidean_topology Z)"
    assume hZ_CQ:
      "Z \<inter> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1 \<noteq> {}"
    assume hZ_rest:
      "Z \<inter>
        (?Ncut - geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1)
        \<noteq> {}"
    let ?CQ = "geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    let ?R = "?Ncut - ?CQ"
    have hsplit:
        "?Ncut = ?CQ \<union> ?R
        \<and> ?CQ \<inter> ?R = {}
        \<and> ?CQ \<in> geotop_euclidean_topology
        \<and> ?R \<in> geotop_euclidean_topology
        \<and> Q1 \<in> ?CQ
        \<and> S1 \<in> ?R"
      by (rule hD44_Ncut_open_split_if_not_same_component[OF hnot])
    have hNcut_union: "?Ncut = ?CQ \<union> ?R"
    proof -
      from hsplit show ?thesis
        apply (elim conjE)
        apply assumption
        done
    qed
    have hdisj: "?CQ \<inter> ?R = {}"
    proof -
      from hsplit show ?thesis
        apply (elim conjE)
        apply assumption
        done
    qed
    have hCQ_open_top: "?CQ \<in> geotop_euclidean_topology"
    proof -
      from hsplit show ?thesis
        apply (elim conjE)
        apply assumption
        done
    qed
    have hR_open_top: "?R \<in> geotop_euclidean_topology"
    proof -
      from hsplit show ?thesis
        apply (elim conjE)
        apply assumption
        done
    qed
    have hQ1_CQ: "Q1 \<in> ?CQ"
    proof -
      from hsplit show ?thesis
        apply (elim conjE)
        apply assumption
        done
    qed
    have hS1_R: "S1 \<in> ?R"
      by (rule DiffI[OF hS1_Ncut hnot])
    have hCQ_sub_Ncut: "?CQ \<subseteq> ?Ncut"
    proof
      fix x
      assume hx: "x \<in> ?CQ"
      let ?F = "{C. C \<subseteq> ?Ncut \<and> Q1 \<in> C
        \<and> top1_connected_on C
            (subspace_topology UNIV geotop_euclidean_topology C)}"
      have hxU: "x \<in> \<Union>?F"
        using hx unfolding geotop_component_at_def .
      obtain C where hxC: "x \<in> C" and hCF: "C \<in> ?F"
        using hxU by (rule UnionE)
      have hC_all:
          "C \<subseteq> ?Ncut \<and> Q1 \<in> C
            \<and> top1_connected_on C
              (subspace_topology UNIV geotop_euclidean_topology C)"
        using hCF by (rule CollectD)
      have hC_sub: "C \<subseteq> ?Ncut"
        using hC_all by (rule conjunct1)
      show "x \<in> ?Ncut"
        by (rule hC_sub[THEN subsetD, OF hxC])
    qed
    have hR_sub_Ncut: "?R \<subseteq> ?Ncut"
      by (rule Diff_subset)
    have hCQ_inter_eq: "?Ncut \<inter> ?CQ = ?CQ"
    proof (rule antisym)
      show "?Ncut \<inter> ?CQ \<subseteq> ?CQ"
        by (rule Int_lower2)
      show "?CQ \<subseteq> ?Ncut \<inter> ?CQ"
      proof
        fix x
        assume hx: "x \<in> ?CQ"
        have hxN: "x \<in> ?Ncut"
          by (rule hCQ_sub_Ncut[THEN subsetD, OF hx])
        show "x \<in> ?Ncut \<inter> ?CQ"
          by (rule IntI[OF hxN hx])
      qed
    qed
    have hR_inter_eq: "?Ncut \<inter> ?R = ?R"
    proof (rule antisym)
      show "?Ncut \<inter> ?R \<subseteq> ?R"
        by (rule Int_lower2)
      show "?R \<subseteq> ?Ncut \<inter> ?R"
      proof
        fix x
        assume hx: "x \<in> ?R"
        have hxN: "x \<in> ?Ncut"
          by (rule hR_sub_Ncut[THEN subsetD, OF hx])
        show "x \<in> ?Ncut \<inter> ?R"
          by (rule IntI[OF hxN hx])
      qed
    qed
    have hCQ_open_sub:
        "?CQ \<in> subspace_topology UNIV geotop_euclidean_topology ?Ncut"
      unfolding subspace_topology_def
    proof (rule CollectI)
      show "\<exists>U. ?CQ = ?Ncut \<inter> U \<and> U \<in> geotop_euclidean_topology"
      proof (rule exI[where x = ?CQ], intro conjI)
        show "?CQ = ?Ncut \<inter> ?CQ"
          by (rule hCQ_inter_eq[symmetric])
        show "?CQ \<in> geotop_euclidean_topology"
          by (rule hCQ_open_top)
      qed
    qed
    have hR_open_sub:
        "?R \<in> subspace_topology UNIV geotop_euclidean_topology ?Ncut"
      unfolding subspace_topology_def
    proof (rule CollectI)
      show "\<exists>U. ?R = ?Ncut \<inter> U \<and> U \<in> geotop_euclidean_topology"
      proof (rule exI[where x = ?R], intro conjI)
        show "?R = ?Ncut \<inter> ?R"
          by (rule hR_inter_eq[symmetric])
        show "?R \<in> geotop_euclidean_topology"
          by (rule hR_open_top)
      qed
    qed
    have hsep:
        "top1_is_separation_on ?Ncut
          (subspace_topology UNIV geotop_euclidean_topology ?Ncut) ?CQ ?R"
      unfolding top1_is_separation_on_def
    proof (intro conjI)
      show "?CQ \<in> subspace_topology UNIV geotop_euclidean_topology ?Ncut"
        by (rule hCQ_open_sub)
      show "?R \<in> subspace_topology UNIV geotop_euclidean_topology ?Ncut"
        by (rule hR_open_sub)
      show "?CQ \<noteq> {}"
      proof
        assume hCQ_empty: "?CQ = {}"
        have "Q1 \<in> {}"
          by (subst hCQ_empty[symmetric], rule hQ1_CQ)
        thus False
          by (rule emptyE)
      qed
      show "?R \<noteq> {}"
      proof
        assume hR_empty: "?R = {}"
        have "S1 \<in> {}"
          by (subst hR_empty[symmetric], rule hS1_R)
        thus False
          by (rule emptyE)
      qed
      show "?CQ \<inter> ?R = {}"
        by (rule hdisj)
      show "?CQ \<union> ?R = ?Ncut"
        by (rule hNcut_union[symmetric])
    qed
    have hUNIV_top:
        "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
      by (metis geotop_euclidean_topology_eq_open_sets
          top1_open_sets_is_topology_on_UNIV)
    have htop_Ncut:
        "is_topology_on ?Ncut
          (subspace_topology UNIV geotop_euclidean_topology ?Ncut)"
      by (rule subspace_topology_is_topology_on[OF hUNIV_top subset_UNIV])
    have hZ_subspace:
        "subspace_topology ?Ncut
          (subspace_topology UNIV geotop_euclidean_topology ?Ncut) Z =
         subspace_topology UNIV geotop_euclidean_topology Z"
      by (rule subspace_topology_trans[OF hZ_sub])
    have hZ_conn_Ncut:
        "top1_connected_on Z
          (subspace_topology ?Ncut
            (subspace_topology UNIV geotop_euclidean_topology ?Ncut) Z)"
      by (subst hZ_subspace, rule hZ_conn)
    have hZ_side: "Z \<subseteq> ?CQ \<or> Z \<subseteq> ?R"
      by (rule Lemma_23_2[OF htop_Ncut hsep hZ_sub hZ_conn_Ncut])
    from hZ_side show False
    proof
      assume hZ_CQ_sub: "Z \<subseteq> ?CQ"
      have hZ_rest_ex: "\<exists>x. x \<in> Z \<inter> ?R"
        unfolding ex_in_conv by (rule hZ_rest)
      obtain x where hxZR: "x \<in> Z \<inter> ?R"
        using hZ_rest_ex by (elim exE)
      have hxZ: "x \<in> Z"
        by (rule IntD1[OF hxZR])
      have hxR: "x \<in> ?R"
        by (rule IntD2[OF hxZR])
      have hxCQ: "x \<in> ?CQ"
        by (rule hZ_CQ_sub[THEN subsetD, OF hxZ])
      have hxCQR: "x \<in> ?CQ \<inter> ?R"
        by (rule IntI[OF hxCQ hxR])
      have "x \<in> {}"
        by (subst hdisj[symmetric], rule hxCQR)
      thus False
        by (rule emptyE)
    next
      assume hZ_R: "Z \<subseteq> ?R"
      have hZ_CQ_ex: "\<exists>x. x \<in> Z \<inter> ?CQ"
        unfolding ex_in_conv by (rule hZ_CQ)
      obtain x where hxZCQ: "x \<in> Z \<inter> ?CQ"
        using hZ_CQ_ex by (elim exE)
      have hxZ: "x \<in> Z"
        by (rule IntD1[OF hxZCQ])
      have hxCQ: "x \<in> ?CQ"
        by (rule IntD2[OF hxZCQ])
      have hxR: "x \<in> ?R"
        by (rule hZ_R[THEN subsetD, OF hxZ])
      have hxCQR: "x \<in> ?CQ \<inter> ?R"
        by (rule IntI[OF hxCQ hxR])
      have "x \<in> {}"
        by (subst hdisj[symmetric], rule hxCQR)
      thus False
        by (rule emptyE)
    qed
  qed
  have hD44_Ncut_open_split_forbids_connected_access_ball_crossing:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<Longrightarrow> \<exists>\<epsilon>\<^sub>Q>0. \<exists>\<epsilon>\<^sub>S>0.
          (\<forall>Z. Z \<subseteq> ?Ncut
            \<longrightarrow> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<longrightarrow> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<longrightarrow> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}
            \<longrightarrow> False)"
    (**
      Access-ball contradiction form of the same split.  After negating the
      desired component relation, choose the component-side collars around
      \<open>Q1\<close> and \<open>S1\<close>.  Any connected subset of \<open>Ncut\<close> meeting both collars
      would cross the open component separation, contradicting the previous
      separation bridge.  This is the exact target for the final Moise
      lower-to-upper frontier witness. **)
  proof -
    assume hnot:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    let ?CQ = "geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    let ?R = "?Ncut - ?CQ"
    obtain \<epsilon>\<^sub>Q \<epsilon>\<^sub>S where h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
      and h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
      and hball_Q_CQ: "ball Q1 \<epsilon>\<^sub>Q \<subseteq> ?CQ"
      and hball_S_R: "ball S1 \<epsilon>\<^sub>S \<subseteq> ?R"
      using hD44_Ncut_open_split_access_balls_if_not_same_component[OF hnot]
      by (elim exE conjE)
    have hall:
        "\<forall>Z. Z \<subseteq> ?Ncut
          \<longrightarrow> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<longrightarrow> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<longrightarrow> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}
          \<longrightarrow> False"
    proof (intro allI impI)
      fix Z
      assume hZ_sub: "Z \<subseteq> ?Ncut"
      assume hZ_conn:
        "top1_connected_on Z
          (subspace_topology UNIV geotop_euclidean_topology Z)"
      assume hZ_Qball: "Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
      assume hZ_Sball: "Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      have hZ_CQ: "Z \<inter> ?CQ \<noteq> {}"
      proof -
        have hZ_Qball_ex: "\<exists>x. x \<in> Z \<inter> ball Q1 \<epsilon>\<^sub>Q"
          unfolding ex_in_conv by (rule hZ_Qball)
        obtain x where hxZQ: "x \<in> Z \<inter> ball Q1 \<epsilon>\<^sub>Q"
          using hZ_Qball_ex by (elim exE)
        have hxZ: "x \<in> Z"
          by (rule IntD1[OF hxZQ])
        have hxball: "x \<in> ball Q1 \<epsilon>\<^sub>Q"
          by (rule IntD2[OF hxZQ])
        have hxCQ: "x \<in> ?CQ"
          by (rule hball_Q_CQ[THEN subsetD, OF hxball])
        have hxZCQ: "x \<in> Z \<inter> ?CQ"
          by (rule IntI[OF hxZ hxCQ])
        show ?thesis
          unfolding ex_in_conv[symmetric] by (rule exI[where x = x], rule hxZCQ)
      qed
      have hZ_R: "Z \<inter> ?R \<noteq> {}"
      proof -
        have hZ_Sball_ex: "\<exists>x. x \<in> Z \<inter> ball S1 \<epsilon>\<^sub>S"
          unfolding ex_in_conv by (rule hZ_Sball)
        obtain x where hxZS: "x \<in> Z \<inter> ball S1 \<epsilon>\<^sub>S"
          using hZ_Sball_ex by (elim exE)
        have hxZ: "x \<in> Z"
          by (rule IntD1[OF hxZS])
        have hxball: "x \<in> ball S1 \<epsilon>\<^sub>S"
          by (rule IntD2[OF hxZS])
        have hxR: "x \<in> ?R"
          by (rule hball_S_R[THEN subsetD, OF hxball])
        have hxZR: "x \<in> Z \<inter> ?R"
          by (rule IntI[OF hxZ hxR])
        show ?thesis
          unfolding ex_in_conv[symmetric] by (rule exI[where x = x], rule hxZR)
      qed
      show False
        by (rule hD44_Ncut_open_split_forbids_connected_crossing
            [OF hnot hZ_sub hZ_conn hZ_CQ hZ_R])
    qed
    show ?thesis
    proof (rule exI[where x=\<epsilon>\<^sub>Q], intro conjI)
      show "0 < \<epsilon>\<^sub>Q" by (rule h\<epsilon>\<^sub>Q_pos)
      show "\<exists>\<epsilon>\<^sub>S>0.
          (\<forall>Z. Z \<subseteq> ?Ncut \<longrightarrow>
            top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z) \<longrightarrow>
            Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {} \<longrightarrow>
            Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {} \<longrightarrow> False)"
      proof (rule exI[where x=\<epsilon>\<^sub>S], intro conjI)
        show "0 < \<epsilon>\<^sub>S" by (rule h\<epsilon>\<^sub>S_pos)
        show "\<forall>Z. Z \<subseteq> ?Ncut \<longrightarrow>
            top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z) \<longrightarrow>
            Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {} \<longrightarrow>
            Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {} \<longrightarrow> False"
          by (rule hall)
      qed
    qed
  qed
  have hD44_arbitrary_access_ball_crossings_suffice:
      "(\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
          \<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})
        \<Longrightarrow> S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut Q1"
    (**
      Final reduction toward Moise's lower-to-upper frontier construction.  To
      prove the desired component relation, it is enough to show that every pair
      of sufficiently small access collars around \<open>Q1\<close> and \<open>S1\<close> is joined by
      some connected subset of \<open>Ncut\<close>.  If the component relation failed, the
      previous split-collar lemma would choose two collars that no connected
      subset of \<open>Ncut\<close> can meet simultaneously. **)
  proof -
    assume hall_crossings:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    show ?thesis
    proof (rule ccontr)
      assume hnotnot:
        "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
      obtain \<epsilon>\<^sub>Q \<epsilon>\<^sub>S where h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
        and h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
        and hforbid:
          "\<forall>Z. Z \<subseteq> ?Ncut
            \<longrightarrow> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<longrightarrow> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<longrightarrow> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}
            \<longrightarrow> False"
        using hD44_Ncut_open_split_forbids_connected_access_ball_crossing
          [OF hnotnot]
        by (elim exE conjE)
      obtain Z where hZ_sub: "Z \<subseteq> ?Ncut"
        and hZ_conn:
          "top1_connected_on Z
            (subspace_topology UNIV geotop_euclidean_topology Z)"
        and hZ_Q: "Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
        and hZ_S: "Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      proof -
        have hQ_spec:
          "\<forall>\<epsilon>\<^sub>S>0. \<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
        proof -
          have hQ_imp:
            "0 < \<epsilon>\<^sub>Q \<longrightarrow> (\<forall>\<epsilon>\<^sub>S>0. \<exists>Z. Z \<subseteq> ?Ncut
              \<and> top1_connected_on Z
                  (subspace_topology UNIV geotop_euclidean_topology Z)
              \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
              \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
            by (rule spec[OF hall_crossings])
          show ?thesis
            by (rule mp[OF hQ_imp h\<epsilon>\<^sub>Q_pos])
        qed
        have hQS_spec:
          "\<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
        proof -
          have hS_imp:
            "0 < \<epsilon>\<^sub>S \<longrightarrow> (\<exists>Z. Z \<subseteq> ?Ncut
              \<and> top1_connected_on Z
                  (subspace_topology UNIV geotop_euclidean_topology Z)
              \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
              \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
            by (rule spec[OF hQ_spec])
          show ?thesis
            by (rule mp[OF hS_imp h\<epsilon>\<^sub>S_pos])
        qed
        then obtain Z where hZ:
          "Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
          by (elim exE)
        have hZ_sub': "Z \<subseteq> ?Ncut"
          by (rule conjunct1[OF hZ])
        have hZ_tail:
            "top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
              \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
              \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
          by (rule conjunct2[OF hZ])
        have hZ_conn':
          "top1_connected_on Z
            (subspace_topology UNIV geotop_euclidean_topology Z)"
          by (rule conjunct1[OF hZ_tail])
        have hZ_tail':
            "Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
              \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
          by (rule conjunct2[OF hZ_tail])
        have hZ_Q': "Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
          by (rule conjunct1[OF hZ_tail'])
        have hZ_S': "Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
          by (rule conjunct2[OF hZ_tail'])
        show ?thesis
          by (rule that[OF hZ_sub' hZ_conn' hZ_Q' hZ_S'])
      qed
      have False
      proof -
        have h1:
          "Z \<subseteq> ?Ncut \<longrightarrow>
            top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z) \<longrightarrow>
            Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {} \<longrightarrow>
            Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {} \<longrightarrow> False"
          by (rule spec[OF hforbid])
        have h2:
          "top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z) \<longrightarrow>
            Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {} \<longrightarrow>
            Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {} \<longrightarrow> False"
          by (rule mp[OF h1 hZ_sub])
        have h3:
          "Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {} \<longrightarrow>
            Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {} \<longrightarrow> False"
          by (rule mp[OF h2 hZ_conn])
        have h4:
          "Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {} \<longrightarrow> False"
          by (rule mp[OF h3 hZ_Q])
        show False
          by (rule mp[OF h4 hZ_S])
      qed
      thus False .
    qed
  qed
  have hD44_arbitrary_access_broken_line_crossings_suffice:
      "(\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
          \<exists>B. geotop_is_broken_line B
            \<and> B \<subseteq> ?Ncut
            \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})
        \<Longrightarrow> S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut Q1"
    (**
      Book-facing version of the previous reduction.  Moise constructs a
      broken-line corridor between arbitrarily small lower and upper access
      collars; since every broken line is connected, such corridors supply the
      connected access-ball crossings needed to force the \<open>Q1\<close> and \<open>S1\<close>
      access points into the same \<open>Ncut\<close> component. **)
  proof -
    assume hall_broken:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>B. geotop_is_broken_line B
          \<and> B \<subseteq> ?Ncut
          \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    have hall_connected:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    proof (intro allI impI)
      fix \<epsilon>\<^sub>Q \<epsilon>\<^sub>S :: real
      assume h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
      assume h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
      have hQ_spec:
        "\<forall>\<epsilon>\<^sub>S>0. \<exists>B. geotop_is_broken_line B
          \<and> B \<subseteq> ?Ncut
          \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      proof -
        have hQ_imp:
          "0 < \<epsilon>\<^sub>Q \<longrightarrow> (\<forall>\<epsilon>\<^sub>S>0. \<exists>B. geotop_is_broken_line B
            \<and> B \<subseteq> ?Ncut
            \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
          by (rule spec[OF hall_broken])
        show ?thesis
          by (rule mp[OF hQ_imp h\<epsilon>\<^sub>Q_pos])
      qed
      have hQS_spec:
        "\<exists>B. geotop_is_broken_line B
          \<and> B \<subseteq> ?Ncut
          \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      proof -
        have hS_imp:
          "0 < \<epsilon>\<^sub>S \<longrightarrow> (\<exists>B. geotop_is_broken_line B
            \<and> B \<subseteq> ?Ncut
            \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
          by (rule spec[OF hQ_spec])
        show ?thesis
          by (rule mp[OF hS_imp h\<epsilon>\<^sub>S_pos])
      qed
      obtain B where hB_bl: "geotop_is_broken_line B"
        and hB_sub: "B \<subseteq> ?Ncut"
        and hB_Q: "B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
        and hB_S: "B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
        using hQS_spec by (elim exE conjE)
      have hB_conn:
        "top1_connected_on B
          (subspace_topology UNIV geotop_euclidean_topology B)"
        by (rule geotop_broken_line_connected_on_prefix[OF hB_bl])
      show "\<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
        using hB_sub hB_conn hB_Q hB_S by (intro exI conjI)
    qed
    show ?thesis
      by (rule hD44_arbitrary_access_ball_crossings_suffice[OF hall_connected])
  qed
  have hD44_arbitrary_access_component_witnesses_suffice:
      "(\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
          \<exists>X Y. X \<in> ?Ncut
            \<and> X \<in> ball Q1 \<epsilon>\<^sub>Q
            \<and> Y \<in> ?Ncut
            \<and> Y \<in> ball S1 \<epsilon>\<^sub>S
            \<and> Y \<in> geotop_component_at UNIV geotop_euclidean_topology
                ?Ncut X)
        \<Longrightarrow> S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut Q1"
    (**
      Component-witness form of the remaining Moise sentence.  If every pair
      of access collars contains points in one component of the open outside
      carrier \<open>Ncut\<close>, then the open-component broken-line lemma turns those
      points into the broken-line collar crossings required above. **)
  proof -
    assume hall_components:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>X Y. X \<in> ?Ncut
          \<and> X \<in> ball Q1 \<epsilon>\<^sub>Q
          \<and> Y \<in> ?Ncut
          \<and> Y \<in> ball S1 \<epsilon>\<^sub>S
          \<and> Y \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut X"
    have hall_broken:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>B. geotop_is_broken_line B
          \<and> B \<subseteq> ?Ncut
          \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    proof (intro allI impI)
      fix \<epsilon>\<^sub>Q \<epsilon>\<^sub>S :: real
      assume h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
      assume h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
      have hQ_spec:
        "\<forall>\<epsilon>\<^sub>S>0. \<exists>X Y. X \<in> ?Ncut
          \<and> X \<in> ball Q1 \<epsilon>\<^sub>Q
          \<and> Y \<in> ?Ncut
          \<and> Y \<in> ball S1 \<epsilon>\<^sub>S
          \<and> Y \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut X"
      proof -
        have hQ_imp:
          "0 < \<epsilon>\<^sub>Q \<longrightarrow> (\<forall>\<epsilon>\<^sub>S>0. \<exists>X Y. X \<in> ?Ncut
            \<and> X \<in> ball Q1 \<epsilon>\<^sub>Q
            \<and> Y \<in> ?Ncut
            \<and> Y \<in> ball S1 \<epsilon>\<^sub>S
            \<and> Y \<in> geotop_component_at UNIV geotop_euclidean_topology
                ?Ncut X)"
          by (rule spec[OF hall_components])
        show ?thesis
          by (rule mp[OF hQ_imp h\<epsilon>\<^sub>Q_pos])
      qed
      have hQS_spec:
        "\<exists>X Y. X \<in> ?Ncut
          \<and> X \<in> ball Q1 \<epsilon>\<^sub>Q
          \<and> Y \<in> ?Ncut
          \<and> Y \<in> ball S1 \<epsilon>\<^sub>S
          \<and> Y \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut X"
      proof -
        have hS_imp:
          "0 < \<epsilon>\<^sub>S \<longrightarrow> (\<exists>X Y. X \<in> ?Ncut
            \<and> X \<in> ball Q1 \<epsilon>\<^sub>Q
            \<and> Y \<in> ?Ncut
            \<and> Y \<in> ball S1 \<epsilon>\<^sub>S
            \<and> Y \<in> geotop_component_at UNIV geotop_euclidean_topology
                ?Ncut X)"
          by (rule spec[OF hQ_spec])
        show ?thesis
          by (rule mp[OF hS_imp h\<epsilon>\<^sub>S_pos])
      qed
      obtain X Y where hX_Ncut: "X \<in> ?Ncut"
        and hX_ball: "X \<in> ball Q1 \<epsilon>\<^sub>Q"
        and hY_Ncut: "Y \<in> ?Ncut"
        and hY_ball: "Y \<in> ball S1 \<epsilon>\<^sub>S"
        and hY_comp:
          "Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut X"
        using hQS_spec by (elim exE conjE)
      have hB_exists:
        "\<exists>B. geotop_is_broken_line B \<and> B \<subseteq> ?Ncut
          \<and> X \<in> B \<and> Y \<in> B"
        by (rule geotop_open_component_broken_line_between_prefix
            [OF hNcut_open hX_Ncut hY_comp])
      obtain B where hB_bl: "geotop_is_broken_line B"
        and hB_sub: "B \<subseteq> ?Ncut"
        and hX_B: "X \<in> B"
        and hY_B: "Y \<in> B"
        using hB_exists by (elim exE conjE)
      have hB_Q: "B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
      proof -
        have "X \<in> B \<inter> ball Q1 \<epsilon>\<^sub>Q"
          by (rule IntI[OF hX_B hX_ball])
        thus ?thesis
          unfolding ex_in_conv[symmetric] by (rule exI[where x = X])
      qed
      have hB_S: "B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      proof -
        have "Y \<in> B \<inter> ball S1 \<epsilon>\<^sub>S"
          by (rule IntI[OF hY_B hY_ball])
        thus ?thesis
          unfolding ex_in_conv[symmetric] by (rule exI[where x = Y])
      qed
      show "\<exists>B. geotop_is_broken_line B
          \<and> B \<subseteq> ?Ncut
          \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
        using hB_bl hB_sub hB_Q hB_S by (intro exI conjI)
    qed
    show ?thesis
      by (rule hD44_arbitrary_access_broken_line_crossings_suffice
          [OF hall_broken])
  qed
  have hD44_accumulating_connected_corridor_suffices:
      "(\<exists>C. C \<subseteq> ?Ncut
          \<and> top1_connected_on C
              (subspace_topology UNIV geotop_euclidean_topology C)
          \<and> (\<forall>\<epsilon>\<^sub>Q>0. C \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {})
          \<and> (\<forall>\<epsilon>\<^sub>S>0. C \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}))
        \<Longrightarrow> S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut Q1"
    (**
      Single-corridor version of Moise's final sentence.  If the adjacent
      outside component/corridor inside \<open>Ncut\<close> has points arbitrarily close to
      both access positions, then any chosen pair of collars contains two
      points of one connected subset of \<open>Ncut\<close>, hence two points in the same
      \<open>Ncut\<close> component. **)
  proof -
    assume hex_corridor:
      "\<exists>C. C \<subseteq> ?Ncut
        \<and> top1_connected_on C
            (subspace_topology UNIV geotop_euclidean_topology C)
        \<and> (\<forall>\<epsilon>\<^sub>Q>0. C \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {})
        \<and> (\<forall>\<epsilon>\<^sub>S>0. C \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
    obtain C where hC_sub: "C \<subseteq> ?Ncut"
      and hC_conn:
        "top1_connected_on C
          (subspace_topology UNIV geotop_euclidean_topology C)"
      and hC_Q_all: "\<forall>\<epsilon>\<^sub>Q>0. C \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
      and hC_S_all: "\<forall>\<epsilon>\<^sub>S>0. C \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      using hex_corridor by (elim exE conjE)
    have hall_components:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>X Y. X \<in> ?Ncut
          \<and> X \<in> ball Q1 \<epsilon>\<^sub>Q
          \<and> Y \<in> ?Ncut
          \<and> Y \<in> ball S1 \<epsilon>\<^sub>S
          \<and> Y \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut X"
    proof (intro allI impI)
      fix \<epsilon>\<^sub>Q \<epsilon>\<^sub>S :: real
      assume h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
      assume h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
      have hC_Q: "C \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
      proof -
        have hQ_imp: "0 < \<epsilon>\<^sub>Q \<longrightarrow> C \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
          by (rule spec[OF hC_Q_all])
        show ?thesis
          by (rule mp[OF hQ_imp h\<epsilon>\<^sub>Q_pos])
      qed
      have hC_S: "C \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      proof -
        have hS_imp: "0 < \<epsilon>\<^sub>S \<longrightarrow> C \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
          by (rule spec[OF hC_S_all])
        show ?thesis
          by (rule mp[OF hS_imp h\<epsilon>\<^sub>S_pos])
      qed
      have hC_Q_ex: "\<exists>X. X \<in> C \<inter> ball Q1 \<epsilon>\<^sub>Q"
        unfolding ex_in_conv by (rule hC_Q)
      obtain X where hX_C: "X \<in> C"
        and hX_ball: "X \<in> ball Q1 \<epsilon>\<^sub>Q"
      proof -
        obtain X where hX: "X \<in> C \<inter> ball Q1 \<epsilon>\<^sub>Q"
          using hC_Q_ex by (elim exE)
        show ?thesis
          by (rule that[OF IntD1[OF hX] IntD2[OF hX]])
      qed
      have hC_S_ex: "\<exists>Y. Y \<in> C \<inter> ball S1 \<epsilon>\<^sub>S"
        unfolding ex_in_conv by (rule hC_S)
      obtain Y where hY_C: "Y \<in> C"
        and hY_ball: "Y \<in> ball S1 \<epsilon>\<^sub>S"
      proof -
        obtain Y where hY: "Y \<in> C \<inter> ball S1 \<epsilon>\<^sub>S"
          using hC_S_ex by (elim exE)
        show ?thesis
          by (rule that[OF IntD1[OF hY] IntD2[OF hY]])
      qed
      have hX_Ncut: "X \<in> ?Ncut"
        by (rule hC_sub[THEN subsetD, OF hX_C])
      have hY_Ncut: "Y \<in> ?Ncut"
        by (rule hC_sub[THEN subsetD, OF hY_C])
      have hY_comp:
        "Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut X"
        by (rule geotop_connected_witness_component_at_intro_prefix
            [OF hC_sub hX_C hY_C hC_conn])
      show "\<exists>X Y. X \<in> ?Ncut
          \<and> X \<in> ball Q1 \<epsilon>\<^sub>Q
          \<and> Y \<in> ?Ncut
          \<and> Y \<in> ball S1 \<epsilon>\<^sub>S
          \<and> Y \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut X"
        using hX_Ncut hX_ball hY_Ncut hY_ball hY_comp by (intro exI conjI)
    qed
    show ?thesis
      by (rule hD44_arbitrary_access_component_witnesses_suffice
          [OF hall_components])
  qed
  have hD44_closed_corridor_suffices:
      "(\<exists>C. C \<subseteq> ?Ncut
          \<and> top1_connected_on C
              (subspace_topology UNIV geotop_euclidean_topology C)
          \<and> Q1 \<in> closure C
          \<and> S1 \<in> closure C)
        \<Longrightarrow> S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut Q1"
    (**
      Frontier/closure form of the same Moise corridor step.  The book says
      the boundary points lie in the frontier of one complementary component;
      for the access points it is enough to produce a connected corridor in
      \<open>Ncut\<close> whose ordinary Euclidean closure contains both access witnesses.
      The existing accumulating-collar bridge then supplies the collar
      intersections. **)
  proof -
    assume hex_corridor:
      "\<exists>C. C \<subseteq> ?Ncut
        \<and> top1_connected_on C
            (subspace_topology UNIV geotop_euclidean_topology C)
        \<and> Q1 \<in> closure C
        \<and> S1 \<in> closure C"
    obtain C where hC_sub: "C \<subseteq> ?Ncut"
      and hC_conn:
        "top1_connected_on C
          (subspace_topology UNIV geotop_euclidean_topology C)"
      and hQ1_cl: "Q1 \<in> closure C"
      and hS1_cl: "S1 \<in> closure C"
      using hex_corridor by (elim exE conjE)
    show ?thesis
      by (rule geotop_connected_closure_corridor_same_component_open_prefix
          [OF hNcut_open hQ1_Ncut hS1_Ncut hC_sub hC_conn hQ1_cl hS1_cl])
  qed
  have hD44_component_closure_at_S1_suffices:
      "S1 \<in> closure
          (geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1)
        \<Longrightarrow> S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut Q1"
    (**
      Access-collar closure bridge.  If Moise's outside component containing
      the \<open>Q1\<close> access point accumulates at \<open>S1\<close>, then the local \<open>Ncut\<close> ball
      around \<open>S1\<close> intersects that component.  The union of the component with
      this small ball is connected and lies in \<open>Ncut\<close>, so it is an actual
      connected witness through \<open>Q1\<close> and \<open>S1\<close>. **)
  proof -
    assume hS1_cl:
      "S1 \<in> closure
        (geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1)"
    let ?CQ = "geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    obtain \<epsilon> where h\<epsilon>_pos: "0 < \<epsilon>"
      and hball_sub: "ball S1 \<epsilon> \<subseteq> ?Ncut"
      using hD44_S1_local_Ncut_ball by (elim exE conjE)
    have hCQ_eq: "?CQ = connected_component_set ?Ncut Q1"
      by (rule geotop_component_at_UNIV_eq_connected_component_set)
    have hCQ_sub: "?CQ \<subseteq> ?Ncut"
    proof -
      have hcc_sub: "connected_component_set ?Ncut Q1 \<subseteq> ?Ncut"
        by (rule connected_component_subset)
      show ?thesis
        by (subst hCQ_eq, rule hcc_sub)
    qed
    have hQ1_CQ: "Q1 \<in> ?CQ"
    proof -
      have hTU: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
        by (metis geotop_euclidean_topology_eq_open_sets
            top1_open_sets_is_topology_on_UNIV)
      have hQ1_sing_conn:
          "top1_connected_on {Q1}
            (subspace_topology UNIV geotop_euclidean_topology {Q1})"
        by (rule top1_connected_on_singleton[OF hTU], simp)
      show ?thesis
        by (rule geotop_self_in_component_at[OF hQ1_Ncut hQ1_sing_conn])
    qed
    have hCQ_conn_HOL: "connected ?CQ"
    proof -
      have hcc_conn: "connected (connected_component_set ?Ncut Q1)"
        by (rule connected_connected_component)
      show ?thesis
        by (subst hCQ_eq, rule hcc_conn)
    qed
    have hmeet: "?CQ \<inter> ball S1 \<epsilon> \<noteq> {}"
      by (rule geotop_closure_point_meets_centered_ball_prefix
          [OF hS1_cl h\<epsilon>_pos])
    have hball_conn_HOL: "connected (ball S1 \<epsilon>)"
      by (rule connected_ball)
    have hW_conn_HOL: "connected (?CQ \<union> ball S1 \<epsilon>)"
      by (rule connected_Un[OF hCQ_conn_HOL hball_conn_HOL hmeet])
    have hW_conn:
        "top1_connected_on (?CQ \<union> ball S1 \<epsilon>)
          (subspace_topology UNIV geotop_euclidean_topology
            (?CQ \<union> ball S1 \<epsilon>))"
      by (rule iffD2[OF top1_connected_on_geotop_iff_connected hW_conn_HOL])
    have hW_sub: "?CQ \<union> ball S1 \<epsilon> \<subseteq> ?Ncut"
      by (rule Un_least[OF hCQ_sub hball_sub])
    have hQ1_W: "Q1 \<in> ?CQ \<union> ball S1 \<epsilon>"
      by (rule UnI1[OF hQ1_CQ])
    have hS1_ball: "S1 \<in> ball S1 \<epsilon>"
      using h\<epsilon>_pos by simp
    have hS1_W: "S1 \<in> ?CQ \<union> ball S1 \<epsilon>"
      by (rule UnI2[OF hS1_ball])
    show ?thesis
      by (rule hD44_connected_route_component_suffices
          [OF hW_sub hQ1_W hS1_W hW_conn])
  qed
  have hD44_component_points_accumulate_at_S1_suffices:
      "(\<forall>\<epsilon>>0. \<exists>Y.
          Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
          \<and> Y \<in> ball S1 \<epsilon>)
        \<Longrightarrow> S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut Q1"
    (**
      Ball-witness form of the same access closure.  This is the form expected
      from the final regular-neighborhood argument: every upper access collar
      around \<open>S1\<close> must meet the outside component already containing \<open>Q1\<close>. **)
  proof -
    assume hall:
      "\<forall>\<epsilon>>0. \<exists>Y.
        Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<and> Y \<in> ball S1 \<epsilon>"
    have hS1_cl:
        "S1 \<in> closure
          (geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1)"
      unfolding closure_approachable
    proof (intro allI impI)
      fix \<epsilon> :: real
      assume h\<epsilon>_pos: "0 < \<epsilon>"
      have h\<epsilon>_imp:
        "0 < \<epsilon> \<longrightarrow> (\<exists>Y.
          Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
          \<and> Y \<in> ball S1 \<epsilon>)"
        by (rule spec[OF hall])
      have hY_ex:
        "\<exists>Y. Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
          \<and> Y \<in> ball S1 \<epsilon>"
        by (rule mp[OF h\<epsilon>_imp h\<epsilon>_pos])
      obtain Y where hY_comp:
          "Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
        and hY_ball: "Y \<in> ball S1 \<epsilon>"
        using hY_ex by (elim exE conjE)
      have hdist: "dist Y S1 < \<epsilon>"
      proof -
        have "dist S1 Y < \<epsilon>"
          using hY_ball unfolding ball_def by simp
        thus ?thesis
          by (simp add: dist_commute)
      qed
      show "\<exists>y\<in>geotop_component_at UNIV geotop_euclidean_topology
          ?Ncut Q1. dist y S1 < \<epsilon>"
        using hY_comp hdist by (intro bexI)
    qed
    show ?thesis
      by (rule hD44_component_closure_at_S1_suffices[OF hS1_cl])
  qed
  have hD44_connected_S1_collar_crossings_suffice:
      "(\<forall>\<epsilon>>0. \<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter>
              geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
              \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {})
        \<Longrightarrow> S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut Q1"
    (**
      Connected crossing form of the remaining collar target.  A Moise
      lower-to-upper outside corridor need not contain \<open>Q1\<close> itself: it is
      enough that it touches the \<open>Q1\<close>-component and then reaches every upper
      access collar.  Unioning that corridor with the \<open>Q1\<close>-component gives
      the actual component witness for the collar point. **)
  proof -
    assume hall:
      "\<forall>\<epsilon>>0. \<exists>Z. Z \<subseteq> ?Ncut
        \<and> top1_connected_on Z
            (subspace_topology UNIV geotop_euclidean_topology Z)
        \<and> Z \<inter>
            geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
            \<noteq> {}
        \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {}"
    let ?CQ = "geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    have hCQ_eq: "?CQ = connected_component_set ?Ncut Q1"
      by (rule geotop_component_at_UNIV_eq_connected_component_set)
    have hCQ_sub: "?CQ \<subseteq> ?Ncut"
    proof -
      have hcc_sub: "connected_component_set ?Ncut Q1 \<subseteq> ?Ncut"
        by (rule connected_component_subset)
      show ?thesis
        by (subst hCQ_eq, rule hcc_sub)
    qed
    have hQ1_CQ: "Q1 \<in> ?CQ"
    proof -
      have hTU: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
        by (metis geotop_euclidean_topology_eq_open_sets
            top1_open_sets_is_topology_on_UNIV)
      have hQ1_sing_conn:
          "top1_connected_on {Q1}
            (subspace_topology UNIV geotop_euclidean_topology {Q1})"
        by (rule top1_connected_on_singleton[OF hTU], simp)
      show ?thesis
        by (rule geotop_self_in_component_at[OF hQ1_Ncut hQ1_sing_conn])
    qed
    have hCQ_conn_HOL: "connected ?CQ"
    proof -
      have hcc_conn: "connected (connected_component_set ?Ncut Q1)"
        by (rule connected_connected_component)
      show ?thesis
        by (subst hCQ_eq, rule hcc_conn)
    qed
    have hall_points:
        "\<forall>\<epsilon>>0. \<exists>Y. Y \<in> ?CQ \<and> Y \<in> ball S1 \<epsilon>"
    proof (intro allI impI)
      fix \<epsilon> :: real
      assume h\<epsilon>_pos: "0 < \<epsilon>"
      have hZ_ex:
          "\<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ?CQ \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {}"
      proof -
        have h\<epsilon>_imp:
          "0 < \<epsilon> \<longrightarrow> (\<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ?CQ \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {})"
          by (rule spec[OF hall])
        show ?thesis
          by (rule mp[OF h\<epsilon>_imp h\<epsilon>_pos])
      qed
      obtain Z where hZ_all:
          "Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ?CQ \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {}"
        using hZ_ex by (elim exE)
      have hZ_sub: "Z \<subseteq> ?Ncut"
        by (rule conjunct1[OF hZ_all])
      have hZ_tail:
          "top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ?CQ \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {}"
        by (rule conjunct2[OF hZ_all])
      have hZ_conn:
          "top1_connected_on Z
            (subspace_topology UNIV geotop_euclidean_topology Z)"
        by (rule conjunct1[OF hZ_tail])
      have hZ_tail':
          "Z \<inter> ?CQ \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {}"
        by (rule conjunct2[OF hZ_tail])
      have hZ_CQ: "Z \<inter> ?CQ \<noteq> {}"
        by (rule conjunct1[OF hZ_tail'])
      have hZ_S: "Z \<inter> ball S1 \<epsilon> \<noteq> {}"
        by (rule conjunct2[OF hZ_tail'])
      have hZ_S_ex: "\<exists>Y. Y \<in> Z \<inter> ball S1 \<epsilon>"
        unfolding ex_in_conv by (rule hZ_S)
      obtain Y where hY_Z: "Y \<in> Z"
        and hY_ball: "Y \<in> ball S1 \<epsilon>"
      proof -
        obtain Y where hY: "Y \<in> Z \<inter> ball S1 \<epsilon>"
          using hZ_S_ex by (elim exE)
        show ?thesis
          by (rule that[OF IntD1[OF hY] IntD2[OF hY]])
      qed
      have hZ_conn_HOL: "connected Z"
        by (rule iffD1[OF top1_connected_on_geotop_iff_connected hZ_conn])
      have hCQ_Z_meet: "?CQ \<inter> Z \<noteq> {}"
      proof -
        have hZ_CQ_ex: "\<exists>x. x \<in> Z \<inter> ?CQ"
          unfolding ex_in_conv by (rule hZ_CQ)
        obtain x where hx: "x \<in> Z \<inter> ?CQ"
          using hZ_CQ_ex by (elim exE)
        have "x \<in> ?CQ \<inter> Z"
          by (rule IntI[OF IntD2[OF hx] IntD1[OF hx]])
        thus ?thesis
          unfolding ex_in_conv[symmetric] by (rule exI[where x = x])
      qed
      have hW_conn_HOL: "connected (?CQ \<union> Z)"
        by (rule connected_Un[OF hCQ_conn_HOL hZ_conn_HOL hCQ_Z_meet])
      have hW_conn:
          "top1_connected_on (?CQ \<union> Z)
            (subspace_topology UNIV geotop_euclidean_topology (?CQ \<union> Z))"
        by (rule iffD2[OF top1_connected_on_geotop_iff_connected hW_conn_HOL])
      have hW_sub: "?CQ \<union> Z \<subseteq> ?Ncut"
        by (rule Un_least[OF hCQ_sub hZ_sub])
      have hQ1_W: "Q1 \<in> ?CQ \<union> Z"
        by (rule UnI1[OF hQ1_CQ])
      have hY_W: "Y \<in> ?CQ \<union> Z"
        by (rule UnI2[OF hY_Z])
      have hY_CQ: "Y \<in> ?CQ"
        by (rule geotop_connected_witness_component_at_intro_prefix
            [OF hW_sub hQ1_W hY_W hW_conn])
      show "\<exists>Y. Y \<in> ?CQ \<and> Y \<in> ball S1 \<epsilon>"
        using hY_CQ hY_ball by (intro exI conjI)
    qed
    show ?thesis
      by (rule hD44_component_points_accumulate_at_S1_suffices
          [OF hall_points])
  qed
  have hD44_arbitrary_access_ball_crossings_give_S1_collar_crossings:
      "(\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
          \<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})
        \<Longrightarrow> (\<forall>\<epsilon>>0. \<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter>
              geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
              \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {})"
    (**
      Converts the symmetric lower-to-upper collar crossing supplied by the
      book into the one-sided component-collar form.  The \<open>Q1\<close> component is
      open in \<open>Ncut\<close>, so a small ball around \<open>Q1\<close> lies in that component;
      any connected corridor meeting that ball already touches the component. **)
  proof -
    assume hall:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    let ?CQ = "geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    have hCQ_open_top: "?CQ \<in> geotop_euclidean_topology"
      by (rule geotop_component_at_open_in_euclidean[OF hNcut_open hQ1_Ncut])
    have hCQ_open_HOL: "open ?CQ"
      using hCQ_open_top
      unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by simp
    have hQ1_CQ: "Q1 \<in> ?CQ"
    proof -
      have hTU: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
        by (metis geotop_euclidean_topology_eq_open_sets
            top1_open_sets_is_topology_on_UNIV)
      have hQ1_sing_conn:
          "top1_connected_on {Q1}
            (subspace_topology UNIV geotop_euclidean_topology {Q1})"
        by (rule top1_connected_on_singleton[OF hTU], simp)
      show ?thesis
        by (rule geotop_self_in_component_at[OF hQ1_Ncut hQ1_sing_conn])
    qed
    have hCQ_ball_all:
        "\<forall>x\<in>?CQ. \<exists>e>0. ball x e \<subseteq> ?CQ"
      by (rule iffD1[OF open_contains_ball hCQ_open_HOL])
    have hQ1_ball_ex: "\<exists>e>0. ball Q1 e \<subseteq> ?CQ"
      by (rule bspec[OF hCQ_ball_all hQ1_CQ])
    obtain \<epsilon>\<^sub>Q where h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
      and hball_Q_CQ: "ball Q1 \<epsilon>\<^sub>Q \<subseteq> ?CQ"
      using hQ1_ball_ex by (elim exE conjE)
    show "\<forall>\<epsilon>>0. \<exists>Z. Z \<subseteq> ?Ncut
        \<and> top1_connected_on Z
            (subspace_topology UNIV geotop_euclidean_topology Z)
        \<and> Z \<inter> ?CQ \<noteq> {}
        \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {}"
    proof (intro allI impI)
      fix \<epsilon> :: real
      assume h\<epsilon>_pos: "0 < \<epsilon>"
      have hQ_spec:
          "\<forall>\<epsilon>\<^sub>S>0. \<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      proof -
        have hQ_imp:
          "0 < \<epsilon>\<^sub>Q \<longrightarrow> (\<forall>\<epsilon>\<^sub>S>0. \<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
          by (rule spec[OF hall])
        show ?thesis
          by (rule mp[OF hQ_imp h\<epsilon>\<^sub>Q_pos])
      qed
      have hZ_ex:
          "\<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {}"
      proof -
        have hS_imp:
          "0 < \<epsilon> \<longrightarrow> (\<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {})"
          by (rule spec[OF hQ_spec])
        show ?thesis
          by (rule mp[OF hS_imp h\<epsilon>_pos])
      qed
      obtain Z where hZ_all:
          "Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {}"
        using hZ_ex by (elim exE)
      have hZ_sub: "Z \<subseteq> ?Ncut"
        by (rule conjunct1[OF hZ_all])
      have hZ_tail:
          "top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {}"
        by (rule conjunct2[OF hZ_all])
      have hZ_conn:
          "top1_connected_on Z
            (subspace_topology UNIV geotop_euclidean_topology Z)"
        by (rule conjunct1[OF hZ_tail])
      have hZ_tail':
          "Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {}"
        by (rule conjunct2[OF hZ_tail])
      have hZ_Qball: "Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
        by (rule conjunct1[OF hZ_tail'])
      have hZ_Sball: "Z \<inter> ball S1 \<epsilon> \<noteq> {}"
        by (rule conjunct2[OF hZ_tail'])
      have hZ_CQ: "Z \<inter> ?CQ \<noteq> {}"
      proof -
        have hZ_Qball_ex: "\<exists>x. x \<in> Z \<inter> ball Q1 \<epsilon>\<^sub>Q"
          unfolding ex_in_conv by (rule hZ_Qball)
        obtain x where hxZQ: "x \<in> Z \<inter> ball Q1 \<epsilon>\<^sub>Q"
          using hZ_Qball_ex by (elim exE)
        have hxZ: "x \<in> Z"
          by (rule IntD1[OF hxZQ])
        have hxball: "x \<in> ball Q1 \<epsilon>\<^sub>Q"
          by (rule IntD2[OF hxZQ])
        have hxCQ: "x \<in> ?CQ"
          by (rule hball_Q_CQ[THEN subsetD, OF hxball])
        have hxZCQ: "x \<in> Z \<inter> ?CQ"
          by (rule IntI[OF hxZ hxCQ])
        show ?thesis
          unfolding ex_in_conv[symmetric] by (rule exI[where x = x], rule hxZCQ)
      qed
      show "\<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter> ?CQ \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {}"
        using hZ_sub hZ_conn hZ_CQ hZ_Sball by (intro exI conjI)
    qed
  qed
  have hD44_arbitrary_access_ball_crossings_give_S1_ball_witnesses:
      "(\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
          \<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})
        \<Longrightarrow> (\<forall>\<epsilon>>0. \<exists>Y.
          Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
          \<and> Y \<in> ball S1 \<epsilon>)"
    (**
      Bookkeeping reduction for the last D44 step.  Once Moise's
      lower-to-upper frontier corridor supplies connected crossings between
      arbitrary access collars, the already-proved component-splitting bridge
      puts \<open>S1\<close> itself in the \<open>Q1\<close> component; this immediately yields the
      upper-collar point witnesses. **)
  proof -
    assume hall:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    have hcollar:
        "\<forall>\<epsilon>>0. \<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter>
              geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
              \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon> \<noteq> {}"
      by (rule hD44_arbitrary_access_ball_crossings_give_S1_collar_crossings
          [OF hall])
    have hS1_comp:
        "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
      by (rule hD44_connected_S1_collar_crossings_suffice[OF hcollar])
    show "\<forall>\<epsilon>>0. \<exists>Y.
        Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<and> Y \<in> ball S1 \<epsilon>"
    proof (intro allI impI)
      fix \<epsilon> :: real
      assume h\<epsilon>_pos: "0 < \<epsilon>"
      have hS1_ball: "S1 \<in> ball S1 \<epsilon>"
        using h\<epsilon>_pos by (by100 simp)
      show "\<exists>Y.
          Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
          \<and> Y \<in> ball S1 \<epsilon>"
        using hS1_comp hS1_ball by (intro exI[where x=S1] conjI)
    qed
  qed
  have hD44_closed_corridor_gives_arbitrary_access_ball_crossings:
      "(\<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Q1 \<in> closure Z
          \<and> S1 \<in> closure Z)
        \<Longrightarrow> (\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
          \<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
    (**
      Collar extraction from Moise's component-frontier sentence.  If the
      adjacent outside corridor is connected inside \<open>Ncut\<close> and its closure
      contains both access points, then every prescribed pair of access collars
      meets that same connected corridor. **)
  proof -
    assume hex_corridor:
      "\<exists>Z. Z \<subseteq> ?Ncut
        \<and> top1_connected_on Z
            (subspace_topology UNIV geotop_euclidean_topology Z)
        \<and> Q1 \<in> closure Z
        \<and> S1 \<in> closure Z"
    obtain Z where hZ_sub: "Z \<subseteq> ?Ncut"
      and hZ_conn:
        "top1_connected_on Z
          (subspace_topology UNIV geotop_euclidean_topology Z)"
      and hQ1_cl: "Q1 \<in> closure Z"
      and hS1_cl: "S1 \<in> closure Z"
      using hex_corridor by (elim exE conjE)
    show "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    proof (intro allI impI)
      fix \<epsilon>\<^sub>Q \<epsilon>\<^sub>S :: real
      assume hQpos: "0 < \<epsilon>\<^sub>Q"
      assume hSpos: "0 < \<epsilon>\<^sub>S"
      have hQmeet: "Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
        by (rule geotop_closure_point_meets_centered_ball_prefix
            [OF hQ1_cl hQpos])
      have hSmeet: "Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
        by (rule geotop_closure_point_meets_centered_ball_prefix
            [OF hS1_cl hSpos])
      show "\<exists>Z. Z \<subseteq> ?Ncut
        \<and> top1_connected_on Z
            (subspace_topology UNIV geotop_euclidean_topology Z)
        \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
        \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      using hZ_sub hZ_conn hQmeet hSmeet by (intro exI conjI)
    qed
  qed
  have hD44_moise_boundary_arc_closed_corridor_book_step:
      "\<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Q1 \<in> closure Z
          \<and> S1 \<in> closure Z"
    (**
      Literal remaining Moise 4.4 frontier-corridor target.  After the fine
      carrier is restricted to the closed disk, the book analyzes the frontier
      component through \<open>P\<close>, proves it is the relevant polygonal 1-sphere,
      splits it into the boundary arc and the complementary frontier arc, and
      takes the adjacent outside component of \<open>I - (N \<union> A2)\<close>.  Formally, the
      missing construction is one connected subset of
      \<open>geotop_polygon_interior J - (N \<union> A2)\<close> whose closure contains the two
      access witnesses near \<open>Q\<close> and \<open>S\<close>. **)
  proof -
    have hD44_moise_same_component_frontier_book_step:
        "\<exists>C. C \<in> components ?Ncut
          \<and> Q1 \<in> closure C
          \<and> S1 \<in> closure C"
      (**
        Literal Moise 4.4 component-frontier sentence.  After splitting the
        frontier component of the fine carrier neighborhood, the book takes
        the outside component adjacent to the complementary frontier subarc;
        the lower and upper access points lie in the frontier, hence in the
        closure, of that one component. **)
    proof -
      have hD44_moise_Q1_component_accumulates_at_S1_book_step:
          "S1 \<in> closure
            (geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1)"
        (**
          Consequence of the literal Moise collar-crossing step.  The
          complementary frontier subarc supplies connected lower-to-upper
          crossings in \<open>I - (N \<union> A2)\<close>; the existing collar/component bridge
          converts those crossings into accumulation of the lower access
          component at the upper access point. **)
      proof -
        have hD44_moise_boundary_arc_access_ball_crossings_book_step:
            "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
              \<exists>Z. Z \<subseteq> ?Ncut
                \<and> top1_connected_on Z
                    (subspace_topology UNIV geotop_euclidean_topology Z)
                \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
                \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
          (**
            Connected-set consequence of Moise's literal broken-line
            construction.  The book constructs the broken line \<open>B\<close> between
            the last lower and first upper boundary hits on the complementary
            frontier arc; broken-line connectedness then gives the connected
            crossing needed by the component/collar bridge. **)
        proof (intro allI impI)
          fix \<epsilon>\<^sub>Q \<epsilon>\<^sub>S :: real
          assume h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
          assume h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
          have hD44_moise_boundary_arc_broken_line_access_crossings_book_step:
              "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
                \<exists>B. geotop_is_broken_line B
                  \<and> B \<subseteq> ?Ncut
                  \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
                  \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
            (**
              Literal Moise 4.4 broken-line construction.  After the fine
              carrier of \<open>A1\<close> is chosen, the book restricts it to the closed
              disk, analyzes the frontier component through \<open>P\<close>, splits that
              polygonal 1-sphere into the boundary arc and complementary
              frontier arc, chooses the lower-to-upper subarc \<open>B\<close>, and shows
              that this subarc lies in \<open>I - (N \<union> A2)\<close> while meeting every
              prescribed pair of access collars around \<open>Q1\<close> and \<open>S1\<close>. **)
            by (rule geotop_polygon_two_endpoint_arcs_fine_carrier_broken_line_access_crossings_prefix
                [OF hJ hP hQ hR hS hcyc hcard hA1 hA2 hA12 hA1_sub hA2_sub
                  hA1J hA2J hK_complex hK_fin hK_poly hN_def hA1_N hN_avoid
                  hr hball_Q_N hball_S_N hQ1_ball hS1_ball hQ1_Ncut hS1_Ncut])
          have hQ_spec:
              "\<forall>\<epsilon>\<^sub>S>0. \<exists>B. geotop_is_broken_line B
                \<and> B \<subseteq> ?Ncut
                \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
                \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
          proof -
            have hQ_imp:
                "0 < \<epsilon>\<^sub>Q \<longrightarrow> (\<forall>\<epsilon>\<^sub>S>0.
                  \<exists>B. geotop_is_broken_line B
                    \<and> B \<subseteq> ?Ncut
                    \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
                    \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
              by (rule spec[OF hD44_moise_boundary_arc_broken_line_access_crossings_book_step])
            show ?thesis
              by (rule mp[OF hQ_imp h\<epsilon>\<^sub>Q_pos])
          qed
          have hB_ex:
              "\<exists>B. geotop_is_broken_line B
                \<and> B \<subseteq> ?Ncut
                \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
                \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
          proof -
            have hS_imp:
                "0 < \<epsilon>\<^sub>S \<longrightarrow> (\<exists>B. geotop_is_broken_line B
                  \<and> B \<subseteq> ?Ncut
                  \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
                  \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
              by (rule spec[OF hQ_spec])
            show ?thesis
              by (rule mp[OF hS_imp h\<epsilon>\<^sub>S_pos])
          qed
          obtain B where hB_bl: "geotop_is_broken_line B"
            and hB_sub: "B \<subseteq> ?Ncut"
            and hB_Q: "B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
            and hB_S: "B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
            using hB_ex by (elim exE conjE)
          have hB_conn:
              "top1_connected_on B
                (subspace_topology UNIV geotop_euclidean_topology B)"
            by (rule geotop_broken_line_connected_on_prefix[OF hB_bl])
          show "\<exists>Z. Z \<subseteq> ?Ncut
              \<and> top1_connected_on Z
                  (subspace_topology UNIV geotop_euclidean_topology Z)
              \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
              \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
            using hB_sub hB_conn hB_Q hB_S by (intro exI conjI)
        qed
        have hS1_witnesses:
            "\<forall>\<epsilon>>0. \<exists>Y.
              Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
              \<and> Y \<in> ball S1 \<epsilon>"
          by (rule hD44_arbitrary_access_ball_crossings_give_S1_ball_witnesses
              [OF hD44_moise_boundary_arc_access_ball_crossings_book_step])
        have hS1_comp:
            "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
          by (rule hD44_component_points_accumulate_at_S1_suffices
              [OF hS1_witnesses])
        show ?thesis
          using hS1_comp closure_subset by (by100 blast)
      qed
      show ?thesis
        by (rule geotop_component_at_closure_gives_component_closure_pair_prefix
            [OF hQ1_Ncut hD44_moise_Q1_component_accumulates_at_S1_book_step])
    qed
    obtain C where hC_comp: "C \<in> components ?Ncut"
      and hQ1_cl: "Q1 \<in> closure C"
      and hS1_cl: "S1 \<in> closure C"
      using hD44_moise_same_component_frontier_book_step
      by (elim exE conjE)
    show ?thesis
      by (rule geotop_component_closure_pair_gives_closed_corridor_prefix
          [OF hC_comp hQ1_cl hS1_cl])
  qed
  have hD44_moise_same_component_book_step:
      "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    (**
      Component consequence of the actual Moise corridor.  The book gives the
      adjacent outside component whose closure contains both access points; the
      local openness of \<open>?Ncut\<close> attaches those access points to that component
      inside \<open>?Ncut\<close>. **)
  proof -
    obtain Z where hZ_sub: "Z \<subseteq> ?Ncut"
      and hZ_conn:
        "top1_connected_on Z
          (subspace_topology UNIV geotop_euclidean_topology Z)"
      and hQ1_cl: "Q1 \<in> closure Z"
      and hS1_cl: "S1 \<in> closure Z"
      using hD44_moise_boundary_arc_closed_corridor_book_step
      by (elim exE conjE)
    show ?thesis
      by (rule geotop_connected_closure_corridor_same_component_open_prefix
          [OF hNcut_open hQ1_Ncut hS1_Ncut hZ_sub hZ_conn hQ1_cl hS1_cl])
  qed
  have hD44_moise_boundary_arc_access_ball_crossings_core:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    (**
      Direct Moise 4.4 lower-to-upper crossing target.  After the fine carrier
      of \<open>A1\<close> is chosen, the book analyzes the frontier component through
      \<open>P\<close>, proves it is the required 1-sphere/frontier broken line, and takes
      the complementary outside corridor.  In formal terms the needed output is
      that every pair of small access collars around \<open>Q1\<close> and \<open>S1\<close> is met by
      one connected subset of \<open>geotop_polygon_interior J - (N \<union> A2)\<close>. **)
    by (rule hD44_closed_corridor_gives_arbitrary_access_ball_crossings
        [OF hD44_moise_boundary_arc_closed_corridor_book_step])
  have hD44_moise_regular_neighborhood_component_core:
      "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    (**
      Component form of the lower-to-upper crossing target.  The existing
      open-split contradiction package says that arbitrary connected crossings
      of the two access collars force the access points to lie in one
      outside-carrier component. **)
    by (rule hD44_arbitrary_access_ball_crossings_suffice
        [OF hD44_moise_boundary_arc_access_ball_crossings_core])
  have hD44_moise_boundary_arc_closed_corridor_core:
      "\<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Q1 \<in> closure Z
          \<and> S1 \<in> closure Z"
    (**
      Named closed-corridor form of the direct Moise target.  The remaining
      regular-neighborhood construction already produces the connected adjacent
      outside corridor whose closure contains both access points. **)
    by (rule hD44_moise_boundary_arc_closed_corridor_book_step)
  have hD44_moise_boundary_arc_same_component_core:
      "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    (**
      Same-component form of the Moise adjacent-corridor target. **)
    by (rule hD44_moise_regular_neighborhood_component_core)
  have hD44_moise_Q1_component_accumulates_core:
      "S1 \<in> closure
        (geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1)"
    (**
      Component-closure consequence of the direct Moise frontier-route target.
      The connected lower-to-upper collar crossings force every upper collar to
      meet the \<open>Q1\<close>-component, hence \<open>S1\<close> is in its closure. **)
  proof -
    have hS1_witnesses:
        "\<forall>\<epsilon>>0. \<exists>Y.
          Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
          \<and> Y \<in> ball S1 \<epsilon>"
      by (rule hD44_arbitrary_access_ball_crossings_give_S1_ball_witnesses
          [OF hD44_moise_boundary_arc_access_ball_crossings_core])
    have hS1_comp:
        "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
      by (rule hD44_component_points_accumulate_at_S1_suffices
          [OF hS1_witnesses])
    show ?thesis
      using hS1_comp closure_subset by (by100 blast)
  qed
  have hD44_moise_closed_corridor_core:
      "\<exists>C. C \<subseteq> ?Ncut
        \<and> top1_connected_on C
            (subspace_topology UNIV geotop_euclidean_topology C)
        \<and> Q1 \<in> closure C
        \<and> S1 \<in> closure C"
    (**
      Closure form of the Moise adjacent-corridor step.  The outside component
      next to the complementary frontier arc \<open>C\<^sub>F\<close> / book \<open>B\<^sub>2\<close> lies in
      \<open>I - (N \<union> A2)\<close> and has the lower and upper access points in its closure. **)
    by (rule hD44_moise_boundary_arc_closed_corridor_core)
  have hD44_moise_accumulating_connected_corridor_core:
      "\<exists>C. C \<subseteq> ?Ncut
        \<and> top1_connected_on C
            (subspace_topology UNIV geotop_euclidean_topology C)
        \<and> (\<forall>\<epsilon>\<^sub>Q>0. C \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {})
        \<and> (\<forall>\<epsilon>\<^sub>S>0. C \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
    (**
      Single adjacent-corridor form of Moise's book step.  The component of
      \<open>I - (N \<union> A2)\<close> next to the complementary frontier arc \<open>C\<^sub>F\<close> / book
      \<open>B\<^sub>2\<close> is connected and has both access points in its closure. **)
  proof -
    obtain C where hC_sub: "C \<subseteq> ?Ncut"
      and hC_conn:
        "top1_connected_on C
          (subspace_topology UNIV geotop_euclidean_topology C)"
      and hQ1_cl: "Q1 \<in> closure C"
      and hS1_cl: "S1 \<in> closure C"
      using hD44_moise_closed_corridor_core
      by (elim exE conjE)
    have hC_Q_all: "\<forall>\<epsilon>\<^sub>Q>0. C \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
    proof (intro allI impI)
      fix \<epsilon>\<^sub>Q :: real
      assume h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
      show "C \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
        by (rule geotop_closure_point_meets_centered_ball_prefix
            [OF hQ1_cl h\<epsilon>\<^sub>Q_pos])
    qed
    have hC_S_all: "\<forall>\<epsilon>\<^sub>S>0. C \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    proof (intro allI impI)
      fix \<epsilon>\<^sub>S :: real
      assume h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
      show "C \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
        by (rule geotop_closure_point_meets_centered_ball_prefix
            [OF hS1_cl h\<epsilon>\<^sub>S_pos])
    qed
    show ?thesis
      using hC_sub hC_conn hC_Q_all hC_S_all by (intro exI conjI)
  qed
  have hD44_moise_arbitrary_access_component_witnesses_core:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>X Y. X \<in> ?Ncut
          \<and> X \<in> ball Q1 \<epsilon>\<^sub>Q
          \<and> Y \<in> ?Ncut
          \<and> Y \<in> ball S1 \<epsilon>\<^sub>S
          \<and> Y \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut X"
    (**
      Adjacent-component form of Moise's corridor.  The outside component lying
      beside the complementary frontier arc \<open>C\<^sub>F\<close> / book \<open>B\<^sub>2\<close> has closure
      meeting both access points, so every prescribed pair of access collars
      contains two points in one component of \<open>?Ncut\<close>. **)
  proof (intro allI impI)
    fix \<epsilon>\<^sub>Q \<epsilon>\<^sub>S :: real
    assume h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
    assume h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
    obtain C where hC_sub: "C \<subseteq> ?Ncut"
      and hC_conn:
        "top1_connected_on C
          (subspace_topology UNIV geotop_euclidean_topology C)"
      and hC_Q_all: "\<forall>\<epsilon>\<^sub>Q>0. C \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
      and hC_S_all: "\<forall>\<epsilon>\<^sub>S>0. C \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      using hD44_moise_accumulating_connected_corridor_core
      by (elim exE conjE)
    have hC_Q: "C \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
    proof -
      have hQ_imp: "0 < \<epsilon>\<^sub>Q \<longrightarrow> C \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
        by (rule spec[OF hC_Q_all])
      show ?thesis
        by (rule mp[OF hQ_imp h\<epsilon>\<^sub>Q_pos])
    qed
    have hC_S: "C \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    proof -
      have hS_imp: "0 < \<epsilon>\<^sub>S \<longrightarrow> C \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
        by (rule spec[OF hC_S_all])
      show ?thesis
        by (rule mp[OF hS_imp h\<epsilon>\<^sub>S_pos])
    qed
    obtain X where hX_C: "X \<in> C" and hX_ball: "X \<in> ball Q1 \<epsilon>\<^sub>Q"
    proof -
      have hX_ex: "\<exists>X. X \<in> C \<inter> ball Q1 \<epsilon>\<^sub>Q"
        unfolding ex_in_conv by (rule hC_Q)
      obtain X where hX: "X \<in> C \<inter> ball Q1 \<epsilon>\<^sub>Q"
        using hX_ex by (elim exE)
      show ?thesis
        by (rule that[of X], rule IntD1[OF hX], rule IntD2[OF hX])
    qed
    obtain Y where hY_C: "Y \<in> C" and hY_ball: "Y \<in> ball S1 \<epsilon>\<^sub>S"
    proof -
      have hY_ex: "\<exists>Y. Y \<in> C \<inter> ball S1 \<epsilon>\<^sub>S"
        unfolding ex_in_conv by (rule hC_S)
      obtain Y where hY: "Y \<in> C \<inter> ball S1 \<epsilon>\<^sub>S"
        using hY_ex by (elim exE)
      show ?thesis
        by (rule that[of Y], rule IntD1[OF hY], rule IntD2[OF hY])
    qed
    have hX_Ncut: "X \<in> ?Ncut"
      by (rule hC_sub[THEN subsetD, OF hX_C])
    have hY_Ncut: "Y \<in> ?Ncut"
      by (rule hC_sub[THEN subsetD, OF hY_C])
    have hY_comp:
        "Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut X"
      by (rule geotop_connected_witness_component_at_intro_prefix
          [OF hC_sub hX_C hY_C hC_conn])
    show "\<exists>X Y. X \<in> ?Ncut
        \<and> X \<in> ball Q1 \<epsilon>\<^sub>Q
        \<and> Y \<in> ?Ncut
        \<and> Y \<in> ball S1 \<epsilon>\<^sub>S
        \<and> Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut X"
      using hX_Ncut hX_ball hY_Ncut hY_ball hY_comp by (intro exI conjI)
  qed
  have hD44_moise_arbitrary_access_broken_line_crossings_core:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>B. geotop_is_broken_line B
          \<and> B \<subseteq> ?Ncut
          \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    (**
      Literal Moise frontier-subarc target.  For every pair of lower and upper
      access collars, the complementary frontier arc \<open>C\<^sub>F\<close> / book \<open>B\<^sub>2\<close>
      should yield a broken-line subarc inside \<open>?Ncut\<close> meeting both collars. **)
  proof (intro allI impI)
    fix \<epsilon>\<^sub>Q \<epsilon>\<^sub>S :: real
    assume h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
    assume h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
    have hQ_spec:
      "\<forall>\<epsilon>\<^sub>S>0. \<exists>X Y. X \<in> ?Ncut
        \<and> X \<in> ball Q1 \<epsilon>\<^sub>Q
        \<and> Y \<in> ?Ncut
        \<and> Y \<in> ball S1 \<epsilon>\<^sub>S
        \<and> Y \<in> geotop_component_at UNIV geotop_euclidean_topology
            ?Ncut X"
    proof -
      have hQ_imp:
        "0 < \<epsilon>\<^sub>Q \<longrightarrow> (\<forall>\<epsilon>\<^sub>S>0. \<exists>X Y. X \<in> ?Ncut
          \<and> X \<in> ball Q1 \<epsilon>\<^sub>Q
          \<and> Y \<in> ?Ncut
          \<and> Y \<in> ball S1 \<epsilon>\<^sub>S
          \<and> Y \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut X)"
        by (rule spec[OF hD44_moise_arbitrary_access_component_witnesses_core])
      show ?thesis
        by (rule mp[OF hQ_imp h\<epsilon>\<^sub>Q_pos])
    qed
    have hQS_spec:
      "\<exists>X Y. X \<in> ?Ncut
        \<and> X \<in> ball Q1 \<epsilon>\<^sub>Q
        \<and> Y \<in> ?Ncut
        \<and> Y \<in> ball S1 \<epsilon>\<^sub>S
        \<and> Y \<in> geotop_component_at UNIV geotop_euclidean_topology
            ?Ncut X"
    proof -
      have hS_imp:
        "0 < \<epsilon>\<^sub>S \<longrightarrow> (\<exists>X Y. X \<in> ?Ncut
          \<and> X \<in> ball Q1 \<epsilon>\<^sub>Q
          \<and> Y \<in> ?Ncut
          \<and> Y \<in> ball S1 \<epsilon>\<^sub>S
          \<and> Y \<in> geotop_component_at UNIV geotop_euclidean_topology
              ?Ncut X)"
        by (rule spec[OF hQ_spec])
      show ?thesis
        by (rule mp[OF hS_imp h\<epsilon>\<^sub>S_pos])
    qed
    obtain X Y where hX_Ncut: "X \<in> ?Ncut"
      and hX_ball: "X \<in> ball Q1 \<epsilon>\<^sub>Q"
      and hY_Ncut: "Y \<in> ?Ncut"
      and hY_ball: "Y \<in> ball S1 \<epsilon>\<^sub>S"
      and hY_comp:
        "Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut X"
      using hQS_spec by (elim exE conjE)
    have hB_exists:
      "\<exists>B. geotop_is_broken_line B \<and> B \<subseteq> ?Ncut
        \<and> X \<in> B \<and> Y \<in> B"
      by (rule geotop_open_component_broken_line_between_prefix
          [OF hNcut_open hX_Ncut hY_comp])
    obtain B where hB_bl: "geotop_is_broken_line B"
      and hB_sub: "B \<subseteq> ?Ncut"
      and hX_B: "X \<in> B"
      and hY_B: "Y \<in> B"
      using hB_exists by (elim exE conjE)
    have hB_Q: "B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
    proof -
      have "X \<in> B \<inter> ball Q1 \<epsilon>\<^sub>Q"
        by (rule IntI[OF hX_B hX_ball])
      thus ?thesis
        unfolding ex_in_conv[symmetric] by (rule exI[where x = X])
    qed
    have hB_S: "B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    proof -
      have "Y \<in> B \<inter> ball S1 \<epsilon>\<^sub>S"
        by (rule IntI[OF hY_B hY_ball])
      thus ?thesis
        unfolding ex_in_conv[symmetric] by (rule exI[where x = Y])
    qed
    show "\<exists>B. geotop_is_broken_line B
        \<and> B \<subseteq> ?Ncut
        \<and> B \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
        \<and> B \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      using hB_bl hB_sub hB_Q hB_S by (intro exI conjI)
  qed
  have hD44_moise_arbitrary_access_ball_crossings_core:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    (**
      Named copy of the direct Moise corridor target for the already-staged split
      contradiction below. **)
    by (rule hD44_moise_boundary_arc_access_ball_crossings_core)
  have hD44_frontier_component_forbids_Ncut_split:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
        \<Longrightarrow> False"
    (**
      Final Moise split contradiction.  If the lower and upper access points
      were in different components of \<open>?Ncut\<close>, the already proved open
      component split of \<open>?Ncut\<close> would separate the lower and upper collars.
      The frontier component through \<open>P\<close>, split into the boundary arc and the
      complementary \<open>C\<^sub>F\<close> / book \<open>B\<^sub>2\<close> arc, supplies the crossing that
      contradicts that separation. **)
  proof -
    assume hnot:
      "S1 \<notin> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    obtain \<epsilon>\<^sub>Q \<epsilon>\<^sub>S where h\<epsilon>\<^sub>Q_pos: "0 < \<epsilon>\<^sub>Q"
      and h\<epsilon>\<^sub>S_pos: "0 < \<epsilon>\<^sub>S"
      and hforbid:
        "\<forall>Z. Z \<subseteq> ?Ncut
          \<longrightarrow> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<longrightarrow> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<longrightarrow> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}
          \<longrightarrow> False"
      using hD44_Ncut_open_split_forbids_connected_access_ball_crossing[OF hnot]
      by (elim exE conjE)
    have hZ_ex:
        "\<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    proof -
      have hQ_spec:
          "\<forall>\<epsilon>\<^sub>S>0. \<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      proof -
        have hQ_imp:
            "0 < \<epsilon>\<^sub>Q \<longrightarrow> (\<forall>\<epsilon>\<^sub>S>0. \<exists>Z. Z \<subseteq> ?Ncut
              \<and> top1_connected_on Z
                  (subspace_topology UNIV geotop_euclidean_topology Z)
              \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
              \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
          by (rule spec[OF hD44_moise_arbitrary_access_ball_crossings_core])
        show ?thesis
          by (rule mp[OF hQ_imp h\<epsilon>\<^sub>Q_pos])
      qed
      have hS_imp:
          "0 < \<epsilon>\<^sub>S \<longrightarrow> (\<exists>Z. Z \<subseteq> ?Ncut
            \<and> top1_connected_on Z
                (subspace_topology UNIV geotop_euclidean_topology Z)
            \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
            \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {})"
        by (rule spec[OF hQ_spec])
      show ?thesis
        by (rule mp[OF hS_imp h\<epsilon>\<^sub>S_pos])
    qed
    obtain Z where hZ_sub: "Z \<subseteq> ?Ncut"
      and hZ_conn:
        "top1_connected_on Z
          (subspace_topology UNIV geotop_euclidean_topology Z)"
      and hZ_Q: "Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}"
      and hZ_S: "Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
      using hZ_ex by (elim exE conjE)
    have hZ_forbid:
        "Z \<subseteq> ?Ncut
          \<longrightarrow> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<longrightarrow> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<longrightarrow> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}
          \<longrightarrow> False"
      by (rule spec[OF hforbid])
    show False
      using hZ_forbid hZ_sub hZ_conn hZ_Q hZ_S by (by100 blast)
  qed
  have hD44_moise_same_component_direct:
      "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    (**
      Final literal Moise component step.  The complementary frontier arc
      \<open>C\<^sub>F\<close> is the book's \<open>B\<^sub>2\<close>; the adjacent component of
      \<open>I - (N \<union> A2)\<close> along that arc contains the lower and upper access
      points in the same outside-carrier component. **)
    by (rule hD44_moise_boundary_arc_same_component_core)
  have hD44_moise_closed_corridor:
      "\<exists>Z. Z \<subseteq> ?Ncut
        \<and> top1_connected_on Z
            (subspace_topology UNIV geotop_euclidean_topology Z)
        \<and> Q1 \<in> closure Z
        \<and> S1 \<in> closure Z"
    (**
      Final literal Moise corridor in component-frontier form.  The
      complementary frontier arc \<open>C\<^sub>F\<close> is the book's \<open>B\<^sub>2\<close>; the adjacent
      component of \<open>I - (N \<union> A2)\<close> along that arc is connected, lies in
      \<open>Ncut\<close>, and has both lower and upper access points in its closure. **)
    by (rule hD44_moise_closed_corridor_core)
  have hD44_moise_arbitrary_access_ball_crossings:
      "\<forall>\<epsilon>\<^sub>Q>0. \<forall>\<epsilon>\<^sub>S>0.
        \<exists>Z. Z \<subseteq> ?Ncut
          \<and> top1_connected_on Z
              (subspace_topology UNIV geotop_euclidean_topology Z)
          \<and> Z \<inter> ball Q1 \<epsilon>\<^sub>Q \<noteq> {}
          \<and> Z \<inter> ball S1 \<epsilon>\<^sub>S \<noteq> {}"
    (**
      Final literal Moise corridor construction.  The complementary frontier
      arc \<open>C\<^sub>F\<close> is the book's \<open>B\<^sub>2\<close> arc after removing the boundary component
      through \<open>P\<close>; the adjacent outside component of
      \<open>I - (N \<union> A2)\<close> supplies a connected lower-to-upper crossing for every
      prescribed pair of access collars. **)
    by (rule hD44_closed_corridor_gives_arbitrary_access_ball_crossings
        [OF hD44_moise_closed_corridor])
  have hD44_moise_Q1_component_has_S1_ball_witnesses:
      "\<forall>\<epsilon>>0. \<exists>Y.
          Y \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1
          \<and> Y \<in> ball S1 \<epsilon>"
    (**
      Consequence of the literal connected-corridor crossing form. **)
    by (rule hD44_arbitrary_access_ball_crossings_give_S1_ball_witnesses
        [OF hD44_moise_arbitrary_access_ball_crossings])
  have hD44_moise_Q1_component_accumulates_at_S1:
      "S1 \<in> closure
        (geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1)"
    (**
      Conversion from Moise's collar formulation to ordinary Euclidean
      closure. **)
    by (rule hD44_moise_Q1_component_accumulates_core)
  have hD44_central_same_component_in_Ncut_book_step:
      "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    (**
      Remaining Moise frontier-component extraction, now in the component form
      used by the downstream D44 package.  The book proves this by taking the
      component of the frontier of the fine carrier neighborhood through
      \<open>P\<close>, splitting that 1-sphere into the boundary arc on \<open>J\<close> and the
      complementary frontier arc, then using the lower-to-upper subarc outside
      \<open>N \<union> A2\<close> to put the access positions \<open>Q1,S1\<close> in the same component of
      \<open>I - (N \<union> A2)\<close>. **)
    by (rule hD44_component_closure_at_S1_suffices
        [OF hD44_moise_Q1_component_accumulates_at_S1])
  have hD44_frontier_component_route:
      "\<exists>B. geotop_is_broken_line B
        \<and> B \<subseteq> ?Ncut
        \<and> Q1 \<in> B
        \<and> S1 \<in> B"
    (**
      Broken-line extraction from the component form of Moise's frontier route.
      The set \<open>?Ncut\<close> is open, so the Section 1 broken-line-connectedness
      bridge turns the same-component statement into the literal broken line
      route used by the theorem statement. **)
    by (rule hD44_same_component_in_Ncut_suffices
        [OF hD44_central_same_component_in_Ncut_book_step])
  have hD44_Q1S1_same_component_in_Ncut:
      "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
    (**
      Component-form consequence of the Moise frontier route: once the
      regular-neighborhood analysis has produced the broken line in
      \<open>I - (N \<union> A2)\<close> through the access points, connectedness of broken
      lines puts \<open>Q1\<close> and \<open>S1\<close> in the same component. **)
    by (rule hD44_broken_line_route_component_suffices
        [OF hD44_frontier_component_route])
  show ?thesis
    using hD44_frontier_component_route .
qed

lemma geotop_polygon_two_endpoint_arcs_fine_carrier_access_component_transfer_prefix:
  fixes J A1 A2 N :: "(real^2) set"
    and K :: "(real^2) set set"
    and P Q R S Q1 S1 :: "real^2"
    and m :: nat
    and r :: real
  assumes hJ: "geotop_is_polygon J"
  assumes hP: "P \<in> J" and hQ: "Q \<in> J" and hR: "R \<in> J" and hS: "S \<in> J"
  assumes hcyc: "geotop_polygon_cyclic_order J P Q R S"
  assumes hcard: "card {P, Q, R, S} = 4"
  assumes hA1: "geotop_is_arc A1 (subspace_topology UNIV geotop_euclidean_topology A1)"
  assumes hA2: "geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2)"
  assumes hA12: "A1 \<inter> A2 = {}"
  assumes hA1_sub:
    "A1 \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hA2_sub:
    "A2 \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hA1J: "A1 \<inter> J = {P}"
  assumes hA2J: "A2 \<inter> J = {R}"
  assumes hK_complex: "geotop_is_complex K"
  assumes hK_fin: "finite K"
  assumes hK_poly:
    "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hN_def:
    "N = (\<Union>{B\<in>geotop_iterated_Sd m K. B \<inter> A1 \<noteq> {}})"
  assumes hA1_N: "A1 \<subseteq> N"
  assumes hN_avoid: "N \<inter> (A2 \<union> {Q, S}) = {}"
  assumes hr: "0 < r"
  assumes hball_Q_N: "ball Q r \<inter> N = {}"
  assumes hball_S_N: "ball S r \<inter> N = {}"
  assumes hQ1_ball: "Q1 \<in> ball Q r"
  assumes hS1_ball: "S1 \<in> ball S r"
  assumes hQ1_Ncut: "Q1 \<in> geotop_polygon_interior J - (N \<union> A2)"
  assumes hS1_Ncut: "S1 \<in> geotop_polygon_interior J - (N \<union> A2)"
  shows
    "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology
       (geotop_polygon_interior J - (N \<union> A2)) Q1"
  (**
    Named form of the remaining Moise 4.4 regular-neighborhood transfer.
    The hypotheses are the book setup after choosing the fine carrier
    neighborhood of \<open>A1\<close>: the carrier comes from a sufficiently fine
    subdivision of the closed polygonal disk, contains \<open>A1\<close>, avoids
    \<open>A2\<close>, and the two local access balls near \<open>Q,S\<close> are disjoint from the
    carrier so the access points lie in the outside-carrier complement.

    The proof follows Moise's brick-neighborhood paragraph: restrict the
    carrier to the closed disk, take the frontier component through \<open>P\<close>,
    read it as a polygonal 1-sphere, extract the lower-to-upper broken-line
    subarc outside \<open>N \<union> A2\<close>, and use cyclic order together with the closed
    D42 separation package to put the two access points in one component. **)
proof -
  let ?Ncut = "geotop_polygon_interior J - (N \<union> A2)"
  have hNcut_open: "?Ncut \<in> geotop_euclidean_topology"
    by (rule geotop_polygon_iterated_Sd_selected_arc_carrier_cut_open_prefix
        [OF hJ hA2 hK_complex hK_fin hN_def])
  have hQ1_I: "Q1 \<in> geotop_polygon_interior J"
    using hQ1_Ncut by (by100 blast)
  have hS1_I: "S1 \<in> geotop_polygon_interior J"
    using hS1_Ncut by (by100 blast)
  have hQ1_not_N: "Q1 \<notin> N"
    using hQ1_Ncut by (by100 blast)
  have hS1_not_N: "S1 \<notin> N"
    using hS1_Ncut by (by100 blast)
  have hQ1_not_A1: "Q1 \<notin> A1"
    using hQ1_not_N hA1_N by (by100 blast)
  have hS1_not_A1: "S1 \<notin> A1"
    using hS1_not_N hA1_N by (by100 blast)
  have hD44_frontier_route_broken_line_exists:
      "\<exists>B. geotop_is_broken_line B
        \<and> B \<subseteq> ?Ncut
        \<and> Q1 \<in> B
        \<and> S1 \<in> B"
    (**
      Remaining Moise 4.4 frontier-route step.  From the fine carrier
      neighborhood \<open>N\<close> of \<open>A1\<close>, analyze the frontier component through
      \<open>P\<close> as the polygonal 1-sphere supplied by the regular-neighborhood
      construction.  Its lower-to-upper subarc outside \<open>N \<union> A2\<close>, together
      with the local access positions of \<open>Q1\<close> and \<open>S1\<close>, gives this broken
      line in \<open>geotop_polygon_interior J - (N \<union> A2)\<close>. **)
    by (rule geotop_polygon_two_endpoint_arcs_fine_carrier_frontier_route_broken_line_prefix
        [OF hJ hP hQ hR hS hcyc hcard hA1 hA2 hA12 hA1_sub hA2_sub
          hA1J hA2J hK_complex hK_fin hK_poly hN_def hA1_N hN_avoid
          hr hball_Q_N hball_S_N hQ1_ball hS1_ball hQ1_Ncut hS1_Ncut])
  obtain B where hB_bl: "geotop_is_broken_line B"
    and hB_Ncut: "B \<subseteq> ?Ncut"
    and hQ1_B: "Q1 \<in> B"
    and hS1_B: "S1 \<in> B"
    using hD44_frontier_route_broken_line_exists by (elim exE conjE)
  have hB_conn:
      "top1_connected_on B
        (subspace_topology UNIV geotop_euclidean_topology B)"
    by (rule geotop_broken_line_connected_on_prefix[OF hB_bl])
  have hB_witness:
      "B \<in> {C. C \<subseteq> ?Ncut \<and> Q1 \<in> C \<and>
        top1_connected_on C
          (subspace_topology UNIV geotop_euclidean_topology C)}"
    using hB_Ncut hQ1_B hB_conn by (by100 simp)
  show ?thesis
    unfolding geotop_component_at_def
    using hB_witness hS1_B by (by100 blast)
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
      by (rule geotop_polygon_iterated_Sd_selected_arc_carrier_subset_closed_disk_prefix
          [OF hK_complex hK_fin hK_poly hN_def])
    have hN_compact: "compact N"
      by (rule geotop_iterated_Sd_selected_arc_carrier_compact_prefix
          [OF hK_complex hK_fin hN_def])
    have hN_closed: "closed N"
      by (rule geotop_iterated_Sd_selected_arc_carrier_closed_prefix
          [OF hK_complex hK_fin hN_def])
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
      by (rule
          geotop_polygon_iterated_Sd_selected_arc_carrier_closed_disk_restrict_eq_prefix
            [OF hK_complex hK_fin hK_poly hN_def N\<^sub>I_def])
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
    have hBdJ\<^sub>N_poly_compact: "compact (geotop_polyhedron BdJ\<^sub>N)"
      by (rule geotop_complex_polyhedron_compact
          [OF hBdJ\<^sub>N_complex hBdJ\<^sub>N_fin])
    have hBdJ\<^sub>N_poly_closed: "closed (geotop_polyhedron BdJ\<^sub>N)"
      by (rule geotop_complex_polyhedron_closed
          [OF hBdJ\<^sub>N_complex hBdJ\<^sub>N_fin])
    have hBdJ\<^sub>N_poly_sub_J\<^sub>N: "geotop_polyhedron BdJ\<^sub>N \<subseteq> J\<^sub>N"
      unfolding BdJ\<^sub>N_def geotop_polyhedron_def by (by100 blast)
    have hBdJ\<^sub>N_poly_sub_FrN\<^sub>I: "geotop_polyhedron BdJ\<^sub>N \<subseteq> FrN\<^sub>I"
      using hBdJ\<^sub>N_poly_sub_J\<^sub>N hJ\<^sub>N_sub_FrN\<^sub>I by (by100 blast)
    have hBdJ\<^sub>N_edge_sub_J\<^sub>N:
        "\<And>e. e \<in> BdJ\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> e \<subseteq> J\<^sub>N"
      unfolding BdJ\<^sub>N_def by (by100 simp)
    have hBdJ\<^sub>N_edge_sub_FrN\<^sub>I:
        "\<And>e. e \<in> BdJ\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> e \<subseteq> FrN\<^sub>I"
    proof -
      fix e
      assume heBdJ: "e \<in> BdJ\<^sub>N" and hedge: "geotop_is_edge e"
      have heJ: "e \<subseteq> J\<^sub>N"
        by (rule hBdJ\<^sub>N_edge_sub_J\<^sub>N[OF heBdJ hedge])
      show "e \<subseteq> FrN\<^sub>I"
        using heJ hJ\<^sub>N_sub_FrN\<^sub>I by (by100 blast)
    qed
    have hBdJ\<^sub>N_edge_member_incident_count_one:
        "\<And>e. e \<in> BdJ\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and>
            geotop_is_face e \<sigma>} = 1"
    proof -
      fix e
      assume heBdJ: "e \<in> BdJ\<^sub>N" and hedge: "geotop_is_edge e"
      have heBdK: "e \<in> BdK\<^sub>N"
        using heBdJ unfolding BdJ\<^sub>N_def by (by100 simp)
      show "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2 \<and>
          geotop_is_face e \<sigma>} = 1"
        by (rule hBdK\<^sub>N_edge_member_incident_count_one[OF heBdK hedge])
    qed
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
    have hJ\<^sub>N_uncovered_openin:
        "openin (top_of_set J\<^sub>N)
          (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N)"
      using hBdJ\<^sub>N_poly_closedin_J\<^sub>N
      unfolding closedin_def by (by100 simp)
    have hJ\<^sub>N_uncovered_closed:
        "closed (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N)"
      using hJ\<^sub>N_uncovered_finite by (rule finite_imp_closed)
    have hJ\<^sub>N_uncovered_closedin:
        "closedin (top_of_set J\<^sub>N)
          (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N)"
    proof -
      have hclosedin_int:
          "closedin (top_of_set J\<^sub>N)
            (J\<^sub>N \<inter> (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N))"
        using hJ\<^sub>N_uncovered_closed by (rule closedin_closed_Int)
      have heq:
          "J\<^sub>N \<inter> (J\<^sub>N - geotop_polyhedron BdJ\<^sub>N) =
            J\<^sub>N - geotop_polyhedron BdJ\<^sub>N"
        by (by100 blast)
      show ?thesis
        using hclosedin_int heq by (by100 simp)
    qed
    have hJ\<^sub>N_uncovered_empty_or_all:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = {}
          \<or> J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
      using connected_clopen[THEN iffD1, OF hJ\<^sub>N_connected_HOL]
        hJ\<^sub>N_uncovered_openin hJ\<^sub>N_uncovered_closedin
      by (by100 blast)
    have hJ\<^sub>N_uncovered_all_imp_finite:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow> finite J\<^sub>N"
      using hJ\<^sub>N_uncovered_finite by (by100 simp)
    have hJ\<^sub>N_uncovered_all_imp_singleton:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow> \<exists>x. J\<^sub>N = {x}"
    proof -
      assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
      have hfin: "finite J\<^sub>N"
        by (rule hJ\<^sub>N_uncovered_all_imp_finite[OF hall])
      have hcases: "J\<^sub>N = {} \<or> (\<exists>x. J\<^sub>N = {x})"
        using connected_finite_iff_sing[OF hJ\<^sub>N_connected_HOL] hfin by (by100 blast)
      show "\<exists>x. J\<^sub>N = {x}"
        using hcases hJ\<^sub>N_nonempty by (by100 blast)
    qed
    have hJ\<^sub>N_uncovered_all_imp_eq_P:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow> J\<^sub>N = {P}"
    proof -
      assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
      obtain x where hx: "J\<^sub>N = {x}"
        using hJ\<^sub>N_uncovered_all_imp_singleton[OF hall] by (by100 blast)
      have hxP: "x = P"
        using hx hP_J\<^sub>N by (by100 blast)
      show "J\<^sub>N = {P}"
        using hx hxP by (by100 simp)
    qed
    have hJ\<^sub>N_uncovered_all_imp_P_uncovered:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N
          \<Longrightarrow> P \<in> J\<^sub>N - geotop_polyhedron BdJ\<^sub>N"
      using hP_J\<^sub>N by (by100 simp)
    have hJ\<^sub>N_uncovered_all_imp_P_not_BdJ:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N
          \<Longrightarrow> P \<notin> geotop_polyhedron BdJ\<^sub>N"
      using hJ\<^sub>N_uncovered_all_imp_P_uncovered by (by100 blast)
    have hJ\<^sub>N_uncovered_all_imp_P_vertex:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N
          \<Longrightarrow> P \<in> geotop_complex_vertices K\<^sub>N"
    proof -
      assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
      have hP_unc: "P \<in> J\<^sub>N - geotop_polyhedron BdJ\<^sub>N"
        by (rule hJ\<^sub>N_uncovered_all_imp_P_uncovered[OF hall])
      show "P \<in> geotop_complex_vertices K\<^sub>N"
        by (rule subsetD[OF hJ\<^sub>N_uncovered_sub_vertices hP_unc])
    qed
    have hJ\<^sub>N_uncovered_all_imp_P_carrier_dim0:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N
          \<Longrightarrow> geotop_simplex_dim (geotop_K_carrier K\<^sub>N P) 0"
    proof -
      assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
      obtain n where hn_le: "n \<le> 1"
        and hdim: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N P) n"
        using hJ\<^sub>N_carrier_dim_le1[OF hP_J\<^sub>N] by (by100 blast)
      have hn_not1: "n \<noteq> 1"
      proof
        assume hn1: "n = 1"
        have hdim1: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N P) 1"
          using hdim hn1 by (by100 simp)
        have hP_BdJ: "P \<in> geotop_polyhedron BdJ\<^sub>N"
          by (rule hJ\<^sub>N_carrier_edge_point_in_BdJ\<^sub>N_poly[OF hP_J\<^sub>N hdim1])
        have hP_not_BdJ: "P \<notin> geotop_polyhedron BdJ\<^sub>N"
          by (rule hJ\<^sub>N_uncovered_all_imp_P_not_BdJ[OF hall])
        show False
          using hP_BdJ hP_not_BdJ by (by100 blast)
      qed
      have hn0: "n = 0"
        using hn_le hn_not1 by (by100 linarith)
      show "geotop_simplex_dim (geotop_K_carrier K\<^sub>N P) 0"
        using hdim hn0 by (by100 simp)
    qed
    have hJ\<^sub>N_uncovered_all_imp_P_incident_edge:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N
          \<Longrightarrow> \<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> P \<in> e"
    proof -
      assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
      have hdim0: "geotop_simplex_dim (geotop_K_carrier K\<^sub>N P) 0"
        by (rule hJ\<^sub>N_uncovered_all_imp_P_carrier_dim0[OF hall])
      show "\<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> P \<in> e"
        by (rule hJ\<^sub>N_carrier_dim0_incident_edge[OF hP_J\<^sub>N hdim0])
    qed
    have hJ\<^sub>N_uncovered_all_imp_incident_edge_not_one:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow>
          e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> P \<in> e \<Longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} \<noteq> 1"
      for e
    proof
      assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
        and heK: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hP_e: "P \<in> e"
        and hcard1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} = 1"
      have heBdK: "e \<in> BdK\<^sub>N"
        by (rule hK\<^sub>N_one_incident_edge_member_BdK\<^sub>N
            [OF heK hedge hcard1])
      have hmeet: "e \<inter> J\<^sub>N \<noteq> {}"
        using hP_e hP_J\<^sub>N by (by100 blast)
      have heBdJ: "e \<in> BdJ\<^sub>N"
        by (rule hBdK\<^sub>N_edge_meets_J\<^sub>N_in_BdJ\<^sub>N[OF heBdK hedge hmeet])
      have hP_BdJ: "P \<in> geotop_polyhedron BdJ\<^sub>N"
        unfolding geotop_polyhedron_def using heBdJ hP_e by (by100 blast)
      have hP_not_BdJ: "P \<notin> geotop_polyhedron BdJ\<^sub>N"
        by (rule hJ\<^sub>N_uncovered_all_imp_P_not_BdJ[OF hall])
      show False
        using hP_BdJ hP_not_BdJ by (by100 blast)
    qed
    have hJ\<^sub>N_uncovered_all_imp_incident_edge_two:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow>
          e \<in> K\<^sub>N \<Longrightarrow> geotop_is_edge e \<Longrightarrow> P \<in> e \<Longrightarrow>
          card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} = 2"
      for e
    proof -
      assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
        and heK: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hP_e: "P \<in> e"
      have he_simplex: "geotop_is_simplex e"
        using hedge unfolding geotop_is_edge_def
        by (rule geotop_simplex_dim_imp_is_simplex)
      obtain q where hq_rel: "q \<in> rel_interior e"
        using geotop_simplex_rel_interior_nonempty[OF he_simplex] by (by100 blast)
      have hge1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} \<ge> 1"
        by (rule hK\<^sub>N_edge_rel_interior_incident_count_ge1
            [OF heK hedge hq_rel])
      have hle2:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} \<le> 2"
        by (rule hK\<^sub>N_edge_incident_2faces_card_le2[OF heK hedge])
      have hnot1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} \<noteq> 1"
        by (rule hJ\<^sub>N_uncovered_all_imp_incident_edge_not_one
            [OF hall heK hedge hP_e])
      show ?thesis
        using hge1 hle2 hnot1 by (by100 linarith)
    qed
    have hJ\<^sub>N_uncovered_all_imp_P_two_incident_edge:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow>
          \<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> P \<in> e
            \<and> card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
              \<and> geotop_is_face e \<sigma>} = 2"
    proof -
      assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
      obtain e where heK: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hP_e: "P \<in> e"
        using hJ\<^sub>N_uncovered_all_imp_P_incident_edge[OF hall]
        by (by100 blast)
      have htwo:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} = 2"
        by (rule hJ\<^sub>N_uncovered_all_imp_incident_edge_two
            [OF hall heK hedge hP_e])
      show ?thesis
        using heK hedge hP_e htwo by (intro bexI[where x=e] conjI)
    qed
    have hJ\<^sub>N_uncovered_all_imp_P_all_incident_edges_two:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow>
          \<forall>e\<in>K\<^sub>N. geotop_is_edge e \<and> P \<in> e \<longrightarrow>
            card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
              \<and> geotop_is_face e \<sigma>} = 2"
    proof (intro ballI impI)
      fix e
      assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
        and heK: "e \<in> K\<^sub>N"
        and he_inc: "geotop_is_edge e \<and> P \<in> e"
      have hedge: "geotop_is_edge e"
        using he_inc by (by100 blast)
      have hP_e: "P \<in> e"
        using he_inc by (by100 blast)
      show "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
              \<and> geotop_is_face e \<sigma>} = 2"
        by (rule hJ\<^sub>N_uncovered_all_imp_incident_edge_two
            [OF hall heK hedge hP_e])
    qed
    have hP_boundary_K\<^sub>N_one_incident_edge:
        "\<exists>e\<in>K\<^sub>N. geotop_is_edge e \<and> P \<in> e
          \<and> card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} = 1"
    proof -
      have hSd_poly_disk:
          "geotop_polyhedron (geotop_iterated_Sd m K) =
            closure_on UNIV geotop_euclidean_topology
              (geotop_polygon_interior J)"
        using hSd_poly hK_poly by (by100 simp)
      have hboundary_cover:
          "J \<subseteq> \<Union>{e\<in>geotop_iterated_Sd m K.
            geotop_is_edge e \<and> e \<subseteq> J}"
        by (rule geotop_polygon_disk_boundary_subset_selected_edges_prefix
            [OF hJ hSd_complex hSd_poly_disk])
      have hP_cover:
          "P \<in> \<Union>{e\<in>geotop_iterated_Sd m K.
            geotop_is_edge e \<and> e \<subseteq> J}"
        using hboundary_cover hP by (by100 blast)
      obtain e where he_sel:
          "e \<in> {e\<in>geotop_iterated_Sd m K. geotop_is_edge e \<and> e \<subseteq> J}"
        and hP_e: "P \<in> e"
        using hP_cover by (by100 blast)
      have heSd: "e \<in> geotop_iterated_Sd m K"
        using he_sel by (by100 simp)
      have hedge: "geotop_is_edge e"
        using he_sel by (by100 simp)
      have heJ: "e \<subseteq> J"
        using he_sel by (by100 simp)
      have heA1: "e \<inter> A1 \<noteq> {}"
        using hP_e hP_in_A1 by (by100 blast)
      have he_sub_N: "e \<subseteq> N"
        unfolding hN_def using heSd heA1 by (by100 blast)
      have heK\<^sub>N: "e \<in> K\<^sub>N"
        unfolding K\<^sub>N_def using heSd he_sub_N by (by100 simp)
      obtain \<sigma> where h\<sigma>Sd: "\<sigma> \<in> geotop_iterated_Sd m K"
        and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
        and heface\<sigma>: "geotop_is_face e \<sigma>"
        using geotop_polygon_disk_boundary_edge_owned_by_2simplex_prefix
          [OF hJ hSd_complex hSd_poly_disk heSd hedge heJ]
        by (elim bexE conjE)
      have hfaces_Sd:
          "{\<rho>\<in>geotop_iterated_Sd m K.
              geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>}"
        by (rule geotop_polygon_disk_boundary_edge_unique_incident_2simplex_prefix
            [OF hJ hSd_complex hSd_poly_disk heSd hedge h\<sigma>Sd h\<sigma>2 heface\<sigma> heJ])
      have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
        by (rule geotop_is_face_imp_subset_prefix[OF heface\<sigma>])
      have hP_\<sigma>: "P \<in> \<sigma>"
        using hP_e he_sub_\<sigma> by (by100 blast)
      have h\<sigma>A1: "\<sigma> \<inter> A1 \<noteq> {}"
        using hP_\<sigma> hP_in_A1 by (by100 blast)
      have h\<sigma>subN: "\<sigma> \<subseteq> N"
        unfolding hN_def using h\<sigma>Sd h\<sigma>A1 by (by100 blast)
      have h\<sigma>K\<^sub>N: "\<sigma> \<in> K\<^sub>N"
        unfolding K\<^sub>N_def using h\<sigma>Sd h\<sigma>subN by (by100 simp)
      let ?F = "{\<rho>\<in>K\<^sub>N. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
      have hF_eq: "?F = {\<sigma>}"
      proof
        show "?F \<subseteq> {\<sigma>}"
        proof
          fix \<rho>
          assume h\<rho>F: "\<rho> \<in> ?F"
          have h\<rho>Sd: "\<rho> \<in> geotop_iterated_Sd m K"
            using h\<rho>F unfolding K\<^sub>N_def by (by100 simp)
          have h\<rho>2: "geotop_simplex_dim \<rho> 2"
            using h\<rho>F by (by100 simp)
          have h\<rho>face: "geotop_is_face e \<rho>"
            using h\<rho>F by (by100 simp)
          have h\<rho>full:
              "\<rho> \<in> {\<rho>\<in>geotop_iterated_Sd m K.
                geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
            using h\<rho>Sd h\<rho>2 h\<rho>face by (by100 simp)
          show "\<rho> \<in> {\<sigma>}"
            using hfaces_Sd h\<rho>full by (by100 simp)
        qed
        show "{\<sigma>} \<subseteq> ?F"
          using h\<sigma>K\<^sub>N h\<sigma>2 heface\<sigma> by (by100 simp)
      qed
      have hcard1: "card ?F = 1"
        using hF_eq by (by100 simp)
      show ?thesis
        using heK\<^sub>N hedge hP_e hcard1 by (intro bexI[where x=e] conjI)
    qed
    have hJ\<^sub>N_uncovered_all_false:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N \<Longrightarrow> False"
    proof -
      assume hall: "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = J\<^sub>N"
      obtain e where heK: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hP_e: "P \<in> e"
        and hcard1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} = 1"
        using hP_boundary_K\<^sub>N_one_incident_edge by (by100 blast)
      have hnot1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} \<noteq> 1"
        by (rule hJ\<^sub>N_uncovered_all_imp_incident_edge_not_one
            [OF hall heK hedge hP_e])
      show False
        using hcard1 hnot1 by (by100 blast)
    qed
    have hJ\<^sub>N_uncovered_empty:
        "J\<^sub>N - geotop_polyhedron BdJ\<^sub>N = {}"
      using hJ\<^sub>N_uncovered_empty_or_all hJ\<^sub>N_uncovered_all_false
      by (by100 blast)
    have hJ\<^sub>N_eq_BdJ\<^sub>N_poly:
        "J\<^sub>N = geotop_polyhedron BdJ\<^sub>N"
      using hJ\<^sub>N_uncovered_empty hBdJ\<^sub>N_poly_sub_J\<^sub>N by (by100 blast)
    have hBdJ\<^sub>N_poly_connected_HOL:
        "connected (geotop_polyhedron BdJ\<^sub>N)"
      using hJ\<^sub>N_connected_HOL hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
    have hBdJ\<^sub>N_poly_connected:
        "top1_connected_on (geotop_polyhedron BdJ\<^sub>N)
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron BdJ\<^sub>N))"
      using hBdJ\<^sub>N_poly_connected_HOL top1_connected_on_geotop_iff_connected
      by (by100 blast)
    have hBdJ\<^sub>N_poly_path_connected:
        "top1_path_connected_on (geotop_polyhedron BdJ\<^sub>N)
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron BdJ\<^sub>N))"
      by (rule iffD2[OF Theorem_GT_1_12(2)[OF hBdJ\<^sub>N_complex]
            hBdJ\<^sub>N_poly_connected])
    have hBdJ\<^sub>N_connected: "geotop_complex_connected BdJ\<^sub>N"
      by (rule iffD2[OF Theorem_GT_1_12(1)[OF hBdJ\<^sub>N_complex]
            hBdJ\<^sub>N_poly_path_connected])
    have hBdJ\<^sub>N_poly_nonempty: "geotop_polyhedron BdJ\<^sub>N \<noteq> {}"
      using hP_J\<^sub>N hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 blast)
    have hBdJ\<^sub>N_nonempty: "BdJ\<^sub>N \<noteq> {}"
      using hBdJ\<^sub>N_poly_nonempty unfolding geotop_polyhedron_def by (by100 blast)
    have hP_BdJ\<^sub>N_poly: "P \<in> geotop_polyhedron BdJ\<^sub>N"
      using hP_J\<^sub>N hJ\<^sub>N_eq_BdJ\<^sub>N_poly by (by100 simp)
    have hBdJ\<^sub>N_P_incident_edge:
        "\<exists>e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> P \<in> e"
    proof -
      obtain e where heK: "e \<in> K\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hP_e: "P \<in> e"
        and hcard1:
          "card {\<sigma>\<in>K\<^sub>N. geotop_simplex_dim \<sigma> 2
            \<and> geotop_is_face e \<sigma>} = 1"
        using hP_boundary_K\<^sub>N_one_incident_edge by (by100 blast)
      have heBdK: "e \<in> BdK\<^sub>N"
        by (rule hK\<^sub>N_one_incident_edge_member_BdK\<^sub>N
            [OF heK hedge hcard1])
      have hmeet: "e \<inter> J\<^sub>N \<noteq> {}"
        using hP_e hP_J\<^sub>N by (by100 blast)
      have heBdJ: "e \<in> BdJ\<^sub>N"
        by (rule hBdK\<^sub>N_edge_meets_J\<^sub>N_in_BdJ\<^sub>N[OF heBdK hedge hmeet])
      show ?thesis
        using heBdJ hedge hP_e by (intro bexI[where x=e] conjI)
    qed
    have hBdJ\<^sub>N_poly_not_singleton:
        "\<And>w. geotop_polyhedron BdJ\<^sub>N \<noteq> {w}"
    proof
      fix w
      assume hpoly_single: "geotop_polyhedron BdJ\<^sub>N = {w}"
      obtain e where heBdJ: "e \<in> BdJ\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hP_e: "P \<in> e"
        using hBdJ\<^sub>N_P_incident_edge by (by100 blast)
      have he_sub_poly: "e \<subseteq> geotop_polyhedron BdJ\<^sub>N"
        unfolding geotop_polyhedron_def using heBdJ by (by100 blast)
      have hP_w: "P = w"
        using hP_e he_sub_poly hpoly_single by (by100 blast)
      have he_sub_singleP: "e \<subseteq> {P}"
        using he_sub_poly hpoly_single hP_w by (by100 simp)
      have he_eq_singleP: "e = {P}"
        using hP_e he_sub_singleP by (by100 blast)
      have "geotop_is_edge {P}"
        using hedge he_eq_singleP by (by100 simp)
      thus False
        using geotop_singleton_not_edge_prefix by (by100 blast)
    qed
    have hBdJ\<^sub>N_vertex_incident_edge:
        "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          \<exists>e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e"
    proof (rule ccontr)
      fix w
      assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
        and hno: "\<not> (\<exists>e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e)"
      have hw_vertex: "w \<in> geotop_complex_vertices BdJ\<^sub>N"
        using geotop_complex_vertices_eq_0_simplexes[OF hBdJ\<^sub>N_complex] hwBdJ
        by (by100 blast)
      have hsingle_top:
          "{w} \<in>
            subspace_topology UNIV geotop_euclidean_topology
              (geotop_polyhedron BdJ\<^sub>N)"
        by (rule geotop_complex_no_incident_edge_vertex_open_singleton_prefix
            [OF hBdJ\<^sub>N_complex hw_vertex hno])
      obtain U where hsingle_eq:
          "{w} = geotop_polyhedron BdJ\<^sub>N \<inter> U"
        and hU_top: "U \<in> geotop_euclidean_topology"
        using hsingle_top unfolding subspace_topology_def by (by100 blast)
      have hU_open: "open U"
        using hU_top unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
        by (by100 simp)
      have hsingle_openin:
          "openin (top_of_set (geotop_polyhedron BdJ\<^sub>N)) {w}"
        unfolding openin_open
        using hU_open hsingle_eq by (by100 blast)
      have hw_poly: "w \<in> geotop_polyhedron BdJ\<^sub>N"
        unfolding geotop_polyhedron_def using hwBdJ by (by100 blast)
      have hsingle_closedin:
          "closedin (top_of_set (geotop_polyhedron BdJ\<^sub>N)) {w}"
      proof -
        have hclosed_single: "closed {w}"
          by (by100 simp)
        have hsingle_eq_poly:
            "{w} = geotop_polyhedron BdJ\<^sub>N \<inter> {w}"
          using hw_poly by (by100 blast)
        show ?thesis
          unfolding closedin_closed
          using hclosed_single hsingle_eq_poly by (by100 blast)
      qed
      have hsingle_cases:
          "{w} = {} \<or> {w} = geotop_polyhedron BdJ\<^sub>N"
        using connected_clopen[THEN iffD1, OF hBdJ\<^sub>N_poly_connected_HOL]
          hsingle_openin hsingle_closedin by (by100 blast)
      have hpoly_single: "geotop_polyhedron BdJ\<^sub>N = {w}"
        using hsingle_cases by (by100 blast)
      show False
        using hBdJ\<^sub>N_poly_not_singleton[of w] hpoly_single by (by100 blast)
    qed
    have hBdJ\<^sub>N_vertex_incident_edge_card_ge1:
        "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 1"
    proof -
      fix w
      assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
      obtain e where heBdJ: "e \<in> BdJ\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hw_e: "w \<in> e"
        using hBdJ\<^sub>N_vertex_incident_edge[OF hwBdJ] by (by100 blast)
      let ?E = "{e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e}"
      have hE_fin: "finite ?E"
        by (rule finite_subset[OF _ hBdJ\<^sub>N_fin]) (by100 blast)
      have heE: "e \<in> ?E"
        using heBdJ hedge hw_e by (by100 simp)
      have hE_ne: "?E \<noteq> {}"
        using heE by (by100 blast)
      have hcard_pos: "0 < card ?E"
      proof -
        have hiff: "(0 < card ?E) = (?E \<noteq> {} \<and> finite ?E)"
          by (rule card_gt_0_iff)
        show ?thesis
          using hiff hE_ne hE_fin by (by100 blast)
      qed
      show "card ?E \<ge> 1"
        using hcard_pos by (by100 linarith)
    qed
    have hBdJ\<^sub>N_vertex_degree_one_or_two_from_card_le2:
        "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
          \<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
            card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 1
            \<or> card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
    proof (intro allI impI)
      fix w
      assume hle2:
        "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
      assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
      have hge1:
        "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 1"
        by (rule hBdJ\<^sub>N_vertex_incident_edge_card_ge1[OF hwBdJ])
      have hle:
        "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
        by (rule hle2[OF hwBdJ])
      show "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 1
          \<or> card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
        using hge1 hle by (by100 linarith)
    qed
    have hBdJ\<^sub>N_vertex_degree_two_from_card_le2_no_endpoint:
        "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
      \<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
        card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
    proof -
      assume hle2:
        "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
      assume hnoend:
        "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
      have hdegree12:
          "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
            card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 1
            \<or> card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
        by (rule hBdJ\<^sub>N_vertex_degree_one_or_two_from_card_le2[OF hle2])
      show "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
        by (rule geotop_degree_one_or_two_no_endpoint_degree_two_prefix
            [OF hBdJ\<^sub>N_linear_graph hdegree12 hnoend])
    qed
    have hBdJ\<^sub>N_vertex_no_endpoint_from_card_ge2:
        "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2) \<Longrightarrow>
          \<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
    proof (intro allI impI)
      fix w
      assume hge2:
        "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
      assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
      show "\<not> geotop_graph_endpoint BdJ\<^sub>N w"
      proof
        assume hend: "geotop_graph_endpoint BdJ\<^sub>N w"
        have hcard1:
            "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 1"
          using geotop_graph_endpoint_singleton_and_card_one_prefix
            [OF hBdJ\<^sub>N_linear_graph hend]
          by (by100 blast)
        have hcard_ge2:
            "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
          by (rule hge2[OF hwBdJ])
        show False
          using hcard1 hcard_ge2 by (by100 linarith)
      qed
    qed
    have hBdJ\<^sub>N_vertex_card_ge2_from_no_endpoint:
        "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
          \<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
            card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
    proof (intro allI impI)
      fix w
      assume hnoend:
        "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
      assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
      have hge1:
        "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 1"
        by (rule hBdJ\<^sub>N_vertex_incident_edge_card_ge1[OF hwBdJ])
      show "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
      proof (rule ccontr)
        assume hnot_ge2:
          "\<not> 2 \<le> card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e}"
        have hcard1:
            "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 1"
          using hge1 hnot_ge2 by (by100 linarith)
        have hend: "geotop_graph_endpoint BdJ\<^sub>N w"
          by (rule geotop_degree_one_vertex_graph_endpoint_prefix
              [OF hBdJ\<^sub>N_linear_graph hwBdJ hcard1])
        have hnot: "\<not> geotop_graph_endpoint BdJ\<^sub>N w"
          using hnoend hwBdJ by (by100 blast)
        show False
          using hend hnot by (by100 blast)
      qed
    qed
    have hBdJ\<^sub>N_vertex_degree_two_from_card_bounds:
        "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        (\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2) \<Longrightarrow>
          \<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
            card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
    proof (intro allI impI)
      fix w
      assume hle2:
        "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
      assume hge2:
        "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
      assume hwBdJ: "{w} \<in> BdJ\<^sub>N"
      have hle:
        "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
        by (rule hle2[OF hwBdJ])
      have hge:
        "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
        by (rule hge2[OF hwBdJ])
      show "card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
        using hle hge by (by100 linarith)
    qed
    have hBdJ\<^sub>N_two_distinct_vertices:
        "\<exists>u v. {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v"
    proof -
      obtain e where heBdJ: "e \<in> BdJ\<^sub>N"
        and hedge: "geotop_is_edge e"
        and hP_e: "P \<in> e"
        using hBdJ\<^sub>N_P_incident_edge by (by100 blast)
      have he_dim: "geotop_simplex_dim e 1"
        using hedge unfolding geotop_is_edge_def by (by100 simp)
      obtain V m where hV_fin: "finite V"
        and hV_card: "card V = 1 + 1"
        and h1_le_m: "1 \<le> m"
        and hgp_V: "geotop_general_position V m"
        and he_eq: "e = geotop_convex_hull V"
        using he_dim unfolding geotop_simplex_dim_def by (by100 blast)
      have heV: "geotop_simplex_vertices e V"
        unfolding geotop_simplex_vertices_def
        using hV_fin hV_card h1_le_m hgp_V he_eq by (by100 blast)
      have hV_card2: "card V = 2"
        using hV_card by (by100 simp)
      have hV_pair_ex:
          "\<exists>u v. V = {u, v} \<and> u \<noteq> v"
        by (rule iffD1[OF card_2_iff hV_card2])
      obtain u v where hV_eq: "V = {u, v}"
        and huv: "u \<noteq> v"
        using hV_pair_ex by (elim exE conjE)
      have huv_BdJ:
          "{u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N"
        by (fact geotop_subdivide_edge_vertices_in_K
            [where K=BdJ\<^sub>N and e=e and V=V and v\<^sub>0=u and v\<^sub>1=v,
             OF hBdJ\<^sub>N_complex heBdJ heV hV_eq])
      show ?thesis
        using huv_BdJ huv by (by100 blast)
    qed
    have hBdJ\<^sub>N_cycle_split_from_degree_two:
        "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2) \<Longrightarrow>
          \<exists>u v C\<^sub>1 C\<^sub>2.
            {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v
            \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
            \<and> geotop_is_broken_line C\<^sub>1
            \<and> geotop_is_broken_line C\<^sub>2
            \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
            \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
            \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
                geotop_arc_interior C\<^sub>2 {u, v} = {}"
    proof -
      assume hdegree:
        "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      obtain u v where huBdJ: "{u} \<in> BdJ\<^sub>N"
        and hvBdJ: "{v} \<in> BdJ\<^sub>N"
        and huv: "u \<noteq> v"
        using hBdJ\<^sub>N_two_distinct_vertices by (by100 blast)
      obtain C\<^sub>1 C\<^sub>2 where hsplit:
          "geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
          \<and> geotop_is_broken_line C\<^sub>1
          \<and> geotop_is_broken_line C\<^sub>2
          \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
          \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
          \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
              geotop_arc_interior C\<^sub>2 {u, v} = {}"
        using geotop_finite_connected_degree_two_linear_graph_two_vertex_boundary_split_prefix
          [OF hBdJ\<^sub>N_linear_graph hBdJ\<^sub>N_fin hBdJ\<^sub>N_connected
            hdegree huBdJ hvBdJ huv]
        by (by100 blast)
      show ?thesis
        using huBdJ hvBdJ huv hsplit by (by100 blast)
    qed
    have hBdJ\<^sub>N_polygon_from_degree_two:
        "(\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2) \<Longrightarrow>
          geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    proof -
      assume hdegree:
        "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
      obtain u v C\<^sub>1 C\<^sub>2 where huBdJ: "{u} \<in> BdJ\<^sub>N"
        and hvBdJ: "{v} \<in> BdJ\<^sub>N"
        and huv: "u \<noteq> v"
        and hpoly_eq: "geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2"
        and hC\<^sub>1_bl: "geotop_is_broken_line C\<^sub>1"
        and hC\<^sub>2_bl: "geotop_is_broken_line C\<^sub>2"
        and hC\<^sub>1_end: "geotop_arc_endpoints C\<^sub>1 {u, v}"
        and hC\<^sub>2_end: "geotop_arc_endpoints C\<^sub>2 {u, v}"
        and hdisj: "geotop_arc_interior C\<^sub>1 {u, v} \<inter>
            geotop_arc_interior C\<^sub>2 {u, v} = {}"
        using hBdJ\<^sub>N_cycle_split_from_degree_two[OF hdegree]
        by (by100 blast)
      have hpolygon_C: "geotop_is_polygon (C\<^sub>1 \<union> C\<^sub>2)"
        by (rule pair_of_arcs_is_polygon
            [OF hC\<^sub>1_bl hC\<^sub>2_bl hC\<^sub>1_end hC\<^sub>2_end hdisj])
      show ?thesis
        using hpolygon_C hpoly_eq by (by100 simp)
    qed
    have hBdJ\<^sub>N_polygon_from_card_bounds:
        "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        (\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2) \<Longrightarrow>
          geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    proof -
      assume hle2:
        "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
      assume hge2:
        "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
      have hdegree:
          "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
            card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
        by (rule hBdJ\<^sub>N_vertex_degree_two_from_card_bounds[OF hle2 hge2])
      show ?thesis
        by (rule hBdJ\<^sub>N_polygon_from_degree_two[OF hdegree])
    qed
    have hBdJ\<^sub>N_polygon_from_card_le2_no_endpoint:
        "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
          geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    proof -
      assume hle2:
        "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
      assume hnoend:
        "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
      have hdegree:
          "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow>
            card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} = 2"
        by (rule hBdJ\<^sub>N_vertex_degree_two_from_card_le2_no_endpoint
            [OF hle2 hnoend])
      show ?thesis
        by (rule hBdJ\<^sub>N_polygon_from_degree_two[OF hdegree])
    qed
    have hBdJ\<^sub>N_polygon_from_simple_closed_curve:
        "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
          geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
    proof -
      let ?C = "geotop_polyhedron BdJ\<^sub>N"
      let ?TC = "subspace_topology UNIV geotop_euclidean_topology ?C"
      let ?S = "(geotop_std_sphere::(real^2) set)"
      let ?TS = "subspace_topology UNIV geotop_euclidean_topology ?S"
      assume hSCC:
        "top1_simple_closed_curve_on UNIV geotop_euclidean_topology ?C"
      obtain f where hf_cont_UNIV:
          "top1_continuous_map_on top1_S1 top1_S1_topology
            UNIV geotop_euclidean_topology f"
        and hfinj: "inj_on f top1_S1"
        and hf_img: "f ` top1_S1 = ?C"
        using hSCC unfolding top1_simple_closed_curve_on_def
        by (by100 blast)
      have hf_cont_C:
          "top1_continuous_map_on top1_S1 top1_S1_topology ?C ?TC f"
      proof -
        have hf_img_sub: "f ` top1_S1 \<subseteq> ?C"
          using hf_img by (by100 simp)
        show ?thesis
          by (rule top1_continuous_map_on_codomain_shrink
              [OF hf_cont_UNIV hf_img_sub subset_UNIV])
      qed
      have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
        using S1_compact by (rule compact_is_topology)
      have hUNIV_top:
          "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
        by (metis geotop_euclidean_topology_eq_open_sets
            top1_open_sets_is_topology_on_UNIV)
      have hC_top: "is_topology_on ?C ?TC"
        by (rule subspace_topology_is_topology_on[OF hUNIV_top subset_UNIV])
      have hC_haus: "is_hausdorff_on ?C ?TC"
        by (rule hausdorff_subspace
            [OF geotop_euclidean_topology_UNIV_hausdorff subset_UNIV])
      have hf_bij: "bij_betw f top1_S1 ?C"
        using hfinj hf_img unfolding bij_betw_def by (by100 blast)
      have hS1_C: "top1_homeomorphism_on top1_S1 top1_S1_topology ?C ?TC f"
        by (rule Theorem_26_6
            [OF hS1_top hC_top S1_compact hC_haus hf_cont_C hf_bij])
      have hC_S1: "top1_homeomorphism_on ?C ?TC top1_S1 top1_S1_topology
          (inv_into top1_S1 f)"
        by (rule top1_homeomorphism_on_sym[OF hS1_C])
      have hS1_std: "top1_homeomorphism_on top1_S1 top1_S1_topology ?S ?TS
          (inv_into ?S R2_to_pair)"
        by (rule top1_homeomorphism_on_sym
            [OF R2_pair_top1_homeomorphism_std_sphere_prefix])
      have hC_std: "top1_homeomorphism_on ?C ?TC ?S ?TS
          (inv_into ?S R2_to_pair \<circ> inv_into top1_S1 f)"
        by (rule top1_homeomorphism_on_comp[OF hC_S1 hS1_std])
      have hC_sphere: "geotop_is_n_sphere ?C ?TC 1"
        unfolding geotop_is_n_sphere_def
        using hC_top hC_std by (by100 blast)
      show "geotop_is_polygon ?C"
        unfolding geotop_is_polygon_def
        using hBdJ\<^sub>N_complex hC_sphere by (by100 blast)
    qed
    have hBdJ\<^sub>N_cycle_split_from_polygon:
        "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
          \<exists>u v C\<^sub>1 C\<^sub>2.
            {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v
            \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
            \<and> geotop_is_broken_line C\<^sub>1
            \<and> geotop_is_broken_line C\<^sub>2
            \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
            \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
            \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
                geotop_arc_interior C\<^sub>2 {u, v} = {}"
    proof -
      assume hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
      obtain u v where huBdJ: "{u} \<in> BdJ\<^sub>N"
        and hvBdJ: "{v} \<in> BdJ\<^sub>N"
        and huv: "u \<noteq> v"
        using hBdJ\<^sub>N_two_distinct_vertices by (by100 blast)
      obtain C\<^sub>1 C\<^sub>2 where hsplit:
          "geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
          \<and> geotop_is_broken_line C\<^sub>1
          \<and> geotop_is_broken_line C\<^sub>2
          \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
          \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
          \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
              geotop_arc_interior C\<^sub>2 {u, v} = {}"
        using geotop_polygon_finite_linear_graph_two_vertex_boundary_split_prefix
          [OF hBdJ\<^sub>N_linear_graph hBdJ\<^sub>N_fin hBdJ\<^sub>N_connected
            hpolygon huBdJ hvBdJ huv]
        by (by100 blast)
      show ?thesis
        using huBdJ hvBdJ huv hsplit by (by100 blast)
    qed
    have hBdJ\<^sub>N_cycle_split_from_card_bounds:
        "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        (\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2) \<Longrightarrow>
          \<exists>u v C\<^sub>1 C\<^sub>2.
            {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v
            \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
            \<and> geotop_is_broken_line C\<^sub>1
            \<and> geotop_is_broken_line C\<^sub>2
            \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
            \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
            \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
                geotop_arc_interior C\<^sub>2 {u, v} = {}"
    proof -
      assume hle2:
        "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
      assume hge2:
        "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<ge> 2"
      have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
        by (rule hBdJ\<^sub>N_polygon_from_card_bounds[OF hle2 hge2])
      show ?thesis
        by (rule hBdJ\<^sub>N_cycle_split_from_polygon[OF hpolygon])
    qed
    have hBdJ\<^sub>N_cycle_split_from_card_le2_no_endpoint:
        "(\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2) \<Longrightarrow>
        (\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w) \<Longrightarrow>
          \<exists>u v C\<^sub>1 C\<^sub>2.
            {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v
            \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
            \<and> geotop_is_broken_line C\<^sub>1
            \<and> geotop_is_broken_line C\<^sub>2
            \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
            \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
            \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
                geotop_arc_interior C\<^sub>2 {u, v} = {}"
    proof -
      assume hle2:
        "\<And>w. {w} \<in> BdJ\<^sub>N \<Longrightarrow>
          card {e\<in>BdJ\<^sub>N. geotop_is_edge e \<and> w \<in> e} \<le> 2"
      assume hnoend:
        "\<forall>w. {w} \<in> BdJ\<^sub>N \<longrightarrow> \<not> geotop_graph_endpoint BdJ\<^sub>N w"
      have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
        by (rule hBdJ\<^sub>N_polygon_from_card_le2_no_endpoint[OF hle2 hnoend])
      show ?thesis
        by (rule hBdJ\<^sub>N_cycle_split_from_polygon[OF hpolygon])
    qed
    have hBdJ\<^sub>N_cycle_split_from_simple_closed_curve:
        "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N) \<Longrightarrow>
          \<exists>u v C\<^sub>1 C\<^sub>2.
            {u} \<in> BdJ\<^sub>N \<and> {v} \<in> BdJ\<^sub>N \<and> u \<noteq> v
            \<and> geotop_polyhedron BdJ\<^sub>N = C\<^sub>1 \<union> C\<^sub>2
            \<and> geotop_is_broken_line C\<^sub>1
            \<and> geotop_is_broken_line C\<^sub>2
            \<and> geotop_arc_endpoints C\<^sub>1 {u, v}
            \<and> geotop_arc_endpoints C\<^sub>2 {u, v}
            \<and> geotop_arc_interior C\<^sub>1 {u, v} \<inter>
                geotop_arc_interior C\<^sub>2 {u, v} = {}"
    proof -
      assume hSCC:
        "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
          (geotop_polyhedron BdJ\<^sub>N)"
      have hpolygon: "geotop_is_polygon (geotop_polyhedron BdJ\<^sub>N)"
        by (rule hBdJ\<^sub>N_polygon_from_simple_closed_curve[OF hSCC])
      show ?thesis
        by (rule hBdJ\<^sub>N_cycle_split_from_polygon[OF hpolygon])
    qed
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
          \<and> ball Q r \<inter> N = {}
          \<and> ball S r \<inter> N = {}
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
          hball_Q_r_N hball_S_r_N hQ_front hS_front
          hQ'_U\<^sub>Q hS'_U\<^sub>S hQ'_cut hS'_cut hU_disj
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
        and hball_Q_r_N: "ball Q r \<inter> N = {}"
        and hball_S_r_N: "ball S r \<inter> N = {}"
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
      have hNcut_N_disj: "?Ncut \<inter> N = {}"
        by (by100 blast)
      have hNcut_FrN\<^sub>I_disj: "?Ncut \<inter> FrN\<^sub>I = {}"
        using hFrN\<^sub>I_sub_N by (by100 blast)
      have hNcut_J\<^sub>N_disj: "?Ncut \<inter> J\<^sub>N = {}"
        using hJ\<^sub>N_sub_N by (by100 blast)
      have hNcut_BdJ\<^sub>N_poly_disj:
          "?Ncut \<inter> geotop_polyhedron BdJ\<^sub>N = {}"
        using hBdJ\<^sub>N_poly_sub_J\<^sub>N hJ\<^sub>N_sub_N by (by100 blast)
      have hQ1_not_BdJ\<^sub>N_poly:
          "Q1 \<notin> geotop_polyhedron BdJ\<^sub>N"
        using hQ1_Ncut hNcut_BdJ\<^sub>N_poly_disj by (by100 blast)
      have hS1_not_BdJ\<^sub>N_poly:
          "S1 \<notin> geotop_polyhedron BdJ\<^sub>N"
        using hS1_Ncut hNcut_BdJ\<^sub>N_poly_disj by (by100 blast)
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
        by (rule geotop_connected_witness_component_at_intro_prefix)
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
      have hD44_central_same_component_in_Ncut_book_step:
          "S1 \<in> geotop_component_at UNIV geotop_euclidean_topology ?Ncut Q1"
        (**
          Instantiation of the named regular-neighborhood transfer package for
          the fine carrier \<open>N\<close> and the local access points \<open>Q1,S1\<close>. **)
        by (rule geotop_polygon_two_endpoint_arcs_fine_carrier_access_component_transfer_prefix
            [OF hJ hP hQ hR hS hcyc hcard hA1 hA2 hA12 hA1_sub hA2_sub
              hA1J hA2J hK_complex hK_fin hK_poly hN_def hA1_N hN_A2_QS
              hr_pos hball_Q_r_N hball_S_r_N hQ1_ball hS1_ball
              hQ1_Ncut hS1_Ncut])
      have hD44_central_frontier_broken_line_route_exists:
          "\<exists>B\<^sub>c. geotop_is_broken_line B\<^sub>c
            \<and> B\<^sub>c \<subseteq> ?Ncut
            \<and> Q1 \<in> B\<^sub>c
            \<and> S1 \<in> B\<^sub>c"
        (**
          Broken-line extraction from the component form of Moise's
          frontier-route step.  The set \<open>?Ncut\<close> is open, so the established
          Section 1/D42 broken-line-connectedness bridge turns same-component
          membership into the literal broken line used by the surrounding
          component bookkeeping. **)
        by (rule geotop_open_component_broken_line_between_prefix
            [OF hNcut_open hQ1_Ncut hD44_central_same_component_in_Ncut_book_step])
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
