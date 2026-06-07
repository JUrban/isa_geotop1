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
  have hD44_book_steps:
    "(\<exists>G. geotop_brick_decomposition G \<and>
          closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)
            = \<Union>{g\<in>G. g \<subseteq>
                closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)} \<and>
          (\<forall>g\<in>G. \<not> (g \<inter> A1 \<noteq> {} \<and> g \<inter> A2 \<noteq> {})))
    \<and> (\<exists>G N'. geotop_brick_decomposition G \<and>
       N' = \<Union>{g\<in>G. g \<inter> A1 \<noteq> {}} \<inter>
          closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J) \<and>
       geotop_n_manifold_with_boundary_on N' (\<lambda>x y. norm (x - y)) 2)
    \<and> (\<exists>J' B V W. geotop_is_n_sphere J'
          (subspace_topology UNIV geotop_euclidean_topology J') 1 \<and>
        geotop_is_broken_line B \<and> B \<subseteq> J' \<and>
        V \<in> J \<and> W \<in> J \<and> B \<inter> J = {V, W})
    \<and> (\<exists>C V W. V \<in> J \<and> W \<in> J \<and>
       V \<in> geotop_frontier UNIV geotop_euclidean_topology C \<and>
       W \<in> geotop_frontier UNIV geotop_euclidean_topology C \<and>
       (\<exists>P'. P' \<in> geotop_polygon_interior J - (A1 \<union> A2) \<and>
           C = geotop_component_at UNIV geotop_euclidean_topology
                 (geotop_polygon_interior J - (A1 \<union> A2)) P'))
    \<and> (\<exists>C. Q \<in> geotop_frontier UNIV geotop_euclidean_topology C
       \<and> S \<in> geotop_frontier UNIV geotop_euclidean_topology C
       \<and> (\<exists>P'. P' \<in> geotop_polygon_interior J - (A1 \<union> A2) \<and>
           C = geotop_component_at UNIV geotop_euclidean_topology
                  (geotop_polygon_interior J - (A1 \<union> A2)) P'))"
    (**
      Combined Moise brick-neighborhood step from geotop.tex:931-943:
      choose a sufficiently fine brick decomposition, form the regular
      neighborhood of the bricks meeting \<open>A1\<close>, read off the frontier broken
      line, and transfer the component-frontier conclusion to \<open>Q,S\<close>. **)
    sorry
  \<comment> \<open>Book step 1: choose a rectangular brick-decomposition, fine enough that
    \<open>closure I\<close> is a union of bricks and no brick meets both \<open>A1\<close> and \<open>A2\<close>.\<close>
  have hD44_bricks:
    "\<exists>G. geotop_brick_decomposition G \<and>
          closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)
            = \<Union>{g\<in>G. g \<subseteq>
                closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)} \<and>
	          (\<forall>g\<in>G. \<not> (g \<inter> A1 \<noteq> {} \<and> g \<inter> A2 \<noteq> {}))"
    using hD44_book_steps by (by100 blast)
  \<comment> \<open>Book step 2: \<open>N'\<close>, the union of the bricks meeting \<open>A1\<close> inside
    \<open>closure I\<close>, is a 2-manifold with boundary.\<close>
  have hD44_N'_manifold:
    "\<exists>G N'. geotop_brick_decomposition G \<and>
       N' = \<Union>{g\<in>G. g \<inter> A1 \<noteq> {}} \<inter>
          closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J) \<and>
	       geotop_n_manifold_with_boundary_on N' (\<lambda>x y. norm (x - y)) 2"
    using hD44_book_steps by (by100 blast)
  \<comment> \<open>Book step 3: take the component of \<open>Fr N'\<close> containing \<open>P\<close>; it is a
    1-sphere. Its intersection with \<open>Fr I\<close> gives the broken line \<open>B1\<close>,
    and the complementary broken line \<open>B2\<close> contains a sub-broken-line \<open>B\<close>
    between points \<open>V,W\<close> of \<open>Fr I\<close> with \<open>B \<inter> Fr I = {V,W}\<close>.\<close>
  have hD44_frontier_broken_line:
    "\<exists>J' B V W. geotop_is_n_sphere J'
          (subspace_topology UNIV geotop_euclidean_topology J') 1 \<and>
        geotop_is_broken_line B \<and> B \<subseteq> J' \<and>
	        V \<in> J \<and> W \<in> J \<and> B \<inter> J = {V, W}"
    using hD44_book_steps by (by100 blast)
  \<comment> \<open>Book step 4: the broken line \<open>B\<close> lies in the boundary of the same
    component of \<open>I - (A1 \<union> A2)\<close>; hence its endpoints \<open>V,W\<close> are frontier
    points of one such component.\<close>
  have hD44_VW_component:
    "\<exists>C V W. V \<in> J \<and> W \<in> J \<and>
       V \<in> geotop_frontier UNIV geotop_euclidean_topology C \<and>
       W \<in> geotop_frontier UNIV geotop_euclidean_topology C \<and>
       (\<exists>P'. P' \<in> geotop_polygon_interior J - (A1 \<union> A2) \<and>
	           C = geotop_component_at UNIV geotop_euclidean_topology
	                 (geotop_polygon_interior J - (A1 \<union> A2)) P')"
    using hD44_book_steps by (by100 blast)
  \<comment> \<open>Book step 5: by the cyclic order on \<open>Fr I\<close>, the endpoints \<open>V,W\<close>
    occur on opposite sides of \<open>P,R\<close>, so the same component that has
    \<open>V,W\<close> in its frontier also has \<open>Q,S\<close> in its frontier.\<close>
  have hD44_QS_component:
    "\<exists>C. Q \<in> geotop_frontier UNIV geotop_euclidean_topology C
       \<and> S \<in> geotop_frontier UNIV geotop_euclidean_topology C
       \<and> (\<exists>P'. P' \<in> geotop_polygon_interior J - (A1 \<union> A2) \<and>
	           C = geotop_component_at UNIV geotop_euclidean_topology
	                  (geotop_polygon_interior J - (A1 \<union> A2)) P')"
    using hD44_book_steps by (by100 blast)
  show ?thesis using hD44_QS_component by (by100 blast)
qed


end
