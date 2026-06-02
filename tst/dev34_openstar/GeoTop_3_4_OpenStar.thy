theory GeoTop_3_4_OpenStar
  imports "GeoTop34GraphWorkDirty.GeoTop_3_4_GraphWork"
begin

lemma geotop_open_star_subset_star_polyhedron_dev34:
  fixes K :: "(real^2) set set"
  shows "geotop_open_star K v \<subseteq> \<Union>(geotop_star K v)"
proof
  fix x assume hx: "x \<in> geotop_open_star K v"
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K" and hv\<sigma>: "v \<in> \<sigma>" and hxri: "x \<in> rel_interior \<sigma>"
    using hx unfolding geotop_open_star_def by (by100 blast)
  have h\<sigma>star: "\<sigma> \<in> geotop_star K v"
    unfolding geotop_star_def using h\<sigma>K hv\<sigma> by (by100 blast)
  have hx\<sigma>: "x \<in> \<sigma>"
    using hxri rel_interior_subset by (by100 blast)
  show "x \<in> \<Union>(geotop_star K v)"
    using h\<sigma>star hx\<sigma> by (by100 blast)
qed

lemma geotop_complex_vertex_in_open_star_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "v \<in> geotop_open_star K v"
proof -
  have hvK: "{v} \<in> K"
    using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
  have hvri: "v \<in> rel_interior {v}"
    by (by100 simp)
  show ?thesis
    unfolding geotop_open_star_def using hvK hvri by (by100 blast)
qed

lemma geotop_open_star_open_in_subspace_locally_finite_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_open_star K v
           \<in> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
proof -
  let ?X = "geotop_polyhedron K"
  let ?TX = "subspace_topology UNIV geotop_euclidean_topology ?X"
  let ?F = "{\<tau> \<in> K. v \<notin> \<tau>}"
  let ?C = "\<Union>?F"
  have hTopX: "is_topology_on ?X ?TX"
  proof -
    have hTop_UNIV: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
      unfolding geotop_euclidean_topology_eq_open_sets
      by (rule top1_open_sets_is_topology_on_UNIV)
    show ?thesis
      by (rule subspace_topology_is_topology_on[OF hTop_UNIV]) (by100 blast)
  qed
  have hF_subX: "\<forall>C\<in>?F. C \<subseteq> ?X"
    unfolding geotop_polyhedron_def by (by100 blast)
  have hF_closed: "\<forall>C\<in>?F. closedin_on ?X ?TX C"
  proof
    fix C assume hC: "C \<in> ?F"
    have hCK: "C \<in> K"
      using hC by (by100 blast)
    have hC_subX: "C \<subseteq> ?X"
      using hF_subX hC by (by100 blast)
    have hC_closed_HOL: "closed C"
      by (rule geotop_complex_simplex_closed[OF hK hCK])
    have hC_closed_UNIV: "closedin_on UNIV geotop_euclidean_topology C"
      using hC_closed_HOL closedin_on_geotop_UNIV_iff_closed by (by100 blast)
    have hsub: "?X \<subseteq> (UNIV::(real^2) set)"
      by (by100 blast)
    have hclosed_iff:
      "closedin_on ?X ?TX C \<longleftrightarrow>
        (\<exists>D. closedin_on UNIV geotop_euclidean_topology D \<and> C = D \<inter> ?X)"
      by (rule Theorem_17_2[OF _ hsub])
        (unfold geotop_euclidean_topology_eq_open_sets,
          rule top1_open_sets_is_topology_on_UNIV)
    show "closedin_on ?X ?TX C"
      using hclosed_iff hC_closed_UNIV hC_subX by (by100 blast)
  qed
  have hF_locally_finite: "top1_locally_finite_family_on ?X ?TX ?F"
  proof -
    have hK_local:
      "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      by (rule geotop_is_complex_locally_finite[OF hK])
    show ?thesis
      unfolding top1_locally_finite_family_on_def
    proof
      fix x assume hxX: "x \<in> ?X"
      obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K" and hx\<sigma>: "x \<in> \<sigma>"
        using hxX unfolding geotop_polyhedron_def by (by100 blast)
      have hlocal_\<sigma>: "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
        by (rule bspec[OF hK_local h\<sigma>K])
      obtain U where hUopen: "open U" and h\<sigma>U: "\<sigma> \<subseteq> U"
        and hUfin: "finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
        using hlocal_\<sigma> by (by100 blast)
      have hUtop: "U \<in> geotop_euclidean_topology"
        using hUopen unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
        by (by100 blast)
      have hXUtop: "?X \<inter> U \<in> ?TX"
        unfolding subspace_topology_def using hUtop by (by100 blast)
      have hxXU: "x \<in> ?X \<inter> U"
        using hxX hx\<sigma> h\<sigma>U by (by100 blast)
      have hfinite_sub:
        "{A \<in> ?F. intersects A (?X \<inter> U)} \<subseteq> {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
        unfolding intersects_def by (by100 blast)
      have hfinite: "finite {A \<in> ?F. intersects A (?X \<inter> U)}"
        by (rule finite_subset[OF hfinite_sub hUfin])
      show "\<exists>U\<in>?TX. x \<in> U \<and> finite {A \<in> ?F. intersects A U}"
      proof (intro bexI[where x = "?X \<inter> U"] conjI)
        show "x \<in> ?X \<inter> U"
          by (rule hxXU)
        show "finite {A \<in> ?F. intersects A (?X \<inter> U)}"
          by (rule hfinite)
        show "?X \<inter> U \<in> ?TX"
          by (rule hXUtop)
      qed
    qed
  qed
  have hC_closed: "closedin_on ?X ?TX ?C"
    by (rule top1_closedin_Union_locally_finite
        [OF hTopX hF_subX hF_closed hF_locally_finite])
  have hC_eq: "?C = ?X - geotop_open_star K v"
    using geotop_open_star_complement[OF hK, of v] by (by100 simp)
  show ?thesis
  proof -
    have hXmC_open: "?X - ?C \<in> ?TX"
      using hC_closed unfolding closedin_on_def by (by100 blast)
    have hstar_subX: "geotop_open_star K v \<subseteq> ?X"
      by (rule geotop_open_star_subset)
    have hstar_eq: "geotop_open_star K v = ?X - ?C"
      using hC_eq hstar_subX by (by100 blast)
    show ?thesis
      using hXmC_open hstar_eq by (by100 simp)
  qed
qed

lemma geotop_complex_vertex_star_neighborhood_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "\<exists>U. U \<in> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)
       \<and> v \<in> U \<and> U \<subseteq> \<Union>(geotop_star K v)"
proof (intro exI[where x = "geotop_open_star K v"] conjI)
  show "geotop_open_star K v
      \<in> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
    by (rule geotop_open_star_open_in_subspace_locally_finite_dev34[OF hK])
  show "v \<in> geotop_open_star K v"
    by (rule geotop_complex_vertex_in_open_star_dev34[OF hK hv])
  show "geotop_open_star K v \<subseteq> \<Union>(geotop_star K v)"
    by (rule geotop_open_star_subset_star_polyhedron_dev34)
qed

end
