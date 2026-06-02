theory GeoTop_3_4
  imports "GeoTop34FactsDirty.GeoTop_3_4_Facts"
begin

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
        sorry
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
            sorry
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
	                  (\<Union>(geotop_link K v)))" sorry
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
		    have hlocal_polygon_components:
		      "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
		             C = geotop_component_at UNIV geotop_euclidean_topology
	                   (\<Union>(geotop_link K v)) P)
          \<longrightarrow> geotop_is_polygon C"
      sorry
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
    have hstar_complex: "geotop_is_complex (geotop_star K v)"
      by (rule geotop_star_is_complex[OF hK])
    have hcone_equiv:
      "\<exists>L \<sigma>. L = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
          \<and> geotop_simplex_dim \<sigma> 2
          \<and> geotop_comb_equiv (geotop_star K v) L"
      sorry
    show ?thesis
      unfolding geotop_comb_n_cell_def using hstar_complex hcone_equiv by (by100 blast)
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
            obtain J where hJlocal: "J \<subseteq> closure_on ?M ?TM U"
              and hJsphere: "geotop_is_n_sphere J
                  (subspace_topology UNIV geotop_euclidean_topology J) 1"
              and hJ_contradiction: "False"
              sorry
            show False
              using hJ_contradiction .
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
                    (\<Union>(geotop_link K v)))" sorry
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
      have hlocal_line_or_polygon_components:
        "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
               C = geotop_component_at UNIV geotop_euclidean_topology
                     (\<Union>(geotop_link K v)) P)
            \<longrightarrow> geotop_is_broken_line C \<or> geotop_is_polygon C"
        sorry
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
      have hstar_complex: "geotop_is_complex (geotop_star K v)"
        by (rule geotop_star_is_complex[OF hK])
      have hboundary_cone_equiv:
        "\<exists>L \<sigma>. L = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
            \<and> geotop_simplex_dim \<sigma> 2
            \<and> geotop_comb_equiv (geotop_star K v) L"
        sorry
      show ?thesis
        unfolding geotop_comb_n_cell_def using hstar_complex hboundary_cone_equiv
        by (by100 blast)
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
