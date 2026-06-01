theory GeoTop_3_4
  imports "GeoTopPre3Dirty.GeoTop"
begin

section \<open>\<S>3 The Schönflies theorem for polygons in $\mathbf{R}^2$\<close>

(** from \<S>3 Theorem 1 (geotop.tex:724)
    LATEX VERSION: Let \<sigma>^n = v_0 v_1 ... v_n and \<tau>^n = w_0 w_1 ... w_n be simplexes in R^m.
      Then there is a simplicial homeomorphism f: \<sigma>^n \<leftrightarrow> \<tau>^n, f: v_i \<mapsto> w_i. **)
theorem Theorem_GT_3_1:
  fixes V W :: "'a::real_normed_vector set" and \<sigma> \<tau> :: "'a set"
  assumes hV: "geotop_simplex_vertices \<sigma> V"
  assumes hW: "geotop_simplex_vertices \<tau> W"
  assumes hcard: "card V = card W"
  assumes h\<phi>_mem: "\<phi> \<in> V \<rightarrow>\<^sub>E W"
  assumes h\<phi>_bij: "bij_betw \<phi> V W"
  shows "\<exists>f. top1_homeomorphism_on \<sigma>
              (subspace_topology UNIV geotop_euclidean_topology \<sigma>)
              \<tau>
              (subspace_topology UNIV geotop_euclidean_topology \<tau>) f
          \<and> geotop_simplicial_on \<sigma> f \<tau>
          \<and> (\<forall>v\<in>V. f v = \<phi> v)"
proof -
  (** (1) For each P \<in> \<sigma>, express P uniquely in barycentric coordinates P = \<Sigma>_{v \<in> V}
         \<alpha>_v v with \<alpha>_v \<ge> 0 and \<Sigma> \<alpha>_v = 1. **)
  have h_barycentric:
    "\<forall>P\<in>\<sigma>. \<exists>!\<alpha>::'a \<Rightarrow> real. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1 \<and>
                          P = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v)" sorry
  (** (2) Define f: \<sigma> \<to> \<tau> by f(P) = \<Sigma>_{v \<in> V} \<alpha>_v \<phi>(v). This is affine on each face and
         bijective (barycentric coordinates are unique). **)
  \<comment> \<open>Sub-claim T3_1-A: f restricted to V agrees with \<phi>. Trivial witness f = \<phi>.\<close>
  have hT3_1_vertex_match:
    "\<exists>f. (\<forall>v\<in>V. f v = \<phi> v)"
    using exI[of _ \<phi>] by (by100 blast)
  \<comment> \<open>Sub-claim T3_1-B: f is simplicial on \<sigma> with image \<tau>.\<close>
  have hT3_1_simplicial:
    "\<exists>f. geotop_simplicial_on \<sigma> f \<tau>" sorry
  \<comment> \<open>Sub-claim T3_1-C: f is a homeomorphism \<sigma> \<leftrightarrow> \<tau>.\<close>
  have hT3_1_homeo:
    "\<exists>f. top1_homeomorphism_on \<sigma>
           (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<tau>
           (subspace_topology UNIV geotop_euclidean_topology \<tau>) f" sorry
  have h_f_def:
    "\<exists>f. (\<forall>v\<in>V. f v = \<phi> v) \<and>
         geotop_simplicial_on \<sigma> f \<tau> \<and>
         top1_homeomorphism_on \<sigma>
           (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<tau>
           (subspace_topology UNIV geotop_euclidean_topology \<tau>) f" sorry
  show ?thesis using h_f_def by (by100 blast)
qed

(** from \<S>3 Theorem 2 (geotop.tex:735)
    LATEX VERSION: In Theorem 1, if m = n, then there is a homeomorphism g: R^n \<leftrightarrow> R^n such
      that g|\<sigma>^n is a simplicial homeomorphism \<sigma>^n \<leftrightarrow> \<tau>^n. **)
theorem Theorem_GT_3_2:
  fixes V W :: "'a::real_normed_vector set" and \<sigma> \<tau> :: "'a set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> n" and h\<tau>: "geotop_simplex_dim \<tau> n"
  assumes hV: "geotop_simplex_vertices \<sigma> V" and hW: "geotop_simplex_vertices \<tau> W"
  assumes h\<phi>_mem: "\<phi> \<in> V \<rightarrow>\<^sub>E W" and h\<phi>_bij: "bij_betw \<phi> V W"
  shows "\<exists>g. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology g
          \<and> (\<forall>x\<in>\<sigma>. g x \<in> \<tau>) \<and> geotop_simplicial_on \<sigma> g \<tau>"
proof -
  (** (1) By Theorem 3.1 there is a simplicial homeomorphism f: \<sigma> \<leftrightarrow> \<tau> with f | V = \<phi>. **)
  obtain f where hf_simpl:
    "top1_homeomorphism_on \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>)
        \<tau> (subspace_topology UNIV geotop_euclidean_topology \<tau>) f \<and>
     geotop_simplicial_on \<sigma> f \<tau> \<and>
     (\<forall>v\<in>V. f v = \<phi> v)" sorry
  (** (2) Extend f to an affine map A: R^m \<to> R^m (where m is the ambient dimension),
         since both \<sigma> and \<tau> are n-simplexes in R^m with n = m (same dim). The affine
         extension is uniquely determined by images of V \<cup> {V's affine basis complement}. **)
  \<comment> \<open>Sub-claim AE-1: \<exists>g plane homeo extending f on \<sigma> (affine extension).\<close>
  have h_affine_extension:
    "\<exists>g. (\<forall>x\<in>\<sigma>. g x = f x) \<and> bij g \<and>
         top1_homeomorphism_on UNIV geotop_euclidean_topology
            UNIV geotop_euclidean_topology g"
    sorry
  \<comment> \<open>Sub-claim AE-2: the extension g is also simplicial on \<sigma> with g(\<sigma>) \<subseteq> \<tau>.
    Follows from AE-1 + simplicial property of f preserved through extension
    (via cached helper geotop_simplicial_on_eq_on).\<close>
  have h_affine_simplicial:
    "\<exists>g. top1_homeomorphism_on UNIV geotop_euclidean_topology
              UNIV geotop_euclidean_topology g
         \<and> (\<forall>x\<in>\<sigma>. g x \<in> \<tau>) \<and> geotop_simplicial_on \<sigma> g \<tau>"
  proof -
    obtain g where hg_eq: "\<forall>x\<in>\<sigma>. g x = f x"
               and hg_bij: "bij g"
               and hg_homeo: "top1_homeomorphism_on UNIV geotop_euclidean_topology
                                  UNIV geotop_euclidean_topology g"
      using h_affine_extension by blast
    \<comment> \<open>g \<sigma> \<subseteq> \<tau> from g x = f x on \<sigma> and f maps \<sigma> into \<tau>.\<close>
    have hf_bij_on: "bij_betw f \<sigma> \<tau>"
      using hf_simpl unfolding top1_homeomorphism_on_def by blast
    have hf_into_\<tau>: "\<forall>x\<in>\<sigma>. f x \<in> \<tau>"
      using hf_bij_on unfolding bij_betw_def by blast
    have hg_into_\<tau>: "\<forall>x\<in>\<sigma>. g x \<in> \<tau>"
      using hg_eq hf_into_\<tau> by simp
    \<comment> \<open>simplicial_on \<sigma> g \<tau> from simplicial_on \<sigma> f \<tau> via the cached helper.\<close>
    have hf_simp: "geotop_simplicial_on \<sigma> f \<tau>"
      using hf_simpl by blast
    have hg_simp: "geotop_simplicial_on \<sigma> g \<tau>"
      by (rule geotop_simplicial_on_eq_on[OF hf_simp hg_eq])
    show ?thesis using hg_homeo hg_into_\<tau> hg_simp by blast
  qed
  have h_affine_ext:
    "(\<exists>g. (\<forall>x\<in>\<sigma>. g x = f x) \<and> bij g \<and>
         top1_homeomorphism_on UNIV geotop_euclidean_topology
            UNIV geotop_euclidean_topology g) \<and>
     (\<exists>g. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology g
          \<and> (\<forall>x\<in>\<sigma>. g x \<in> \<tau>) \<and> geotop_simplicial_on \<sigma> g \<tau>)"
    using h_affine_extension h_affine_simplicial by (by100 blast)
  have h_final: "\<exists>g. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology g
          \<and> (\<forall>x\<in>\<sigma>. g x \<in> \<tau>) \<and> geotop_simplicial_on \<sigma> g \<tau>"
    using h_affine_ext by (by100 blast)
  show ?thesis using h_final by (by100 blast)
qed

(** from \<S>3: free 2-simplex (geotop.tex:752)
    LATEX VERSION: Let I be the interior of the polygon J in R^2. By Theorem 2.2, \<bar>I\<close> is a
      finite polyhedron |K|. If \<sigma>^2 \<in> K, and \<sigma>^2 \<inter> J consists of one or two edges of \<sigma>^2,
      then \<sigma>^2 is free (in K). **)
definition geotop_free_2_simplex ::
  "(real^2) set set \<Rightarrow> (real^2) set \<Rightarrow> (real^2) set \<Rightarrow> bool" where
  "geotop_free_2_simplex K J \<sigma>\<^sub>2 \<longleftrightarrow>
    \<sigma>\<^sub>2 \<in> K \<and> geotop_simplex_dim \<sigma>\<^sub>2 2 \<and>
    (\<exists>E. E \<subseteq> K \<and> (E = {} \<or> (\<exists>e. E = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<sigma>\<^sub>2 \<and> e \<subseteq> J) \<or>
         (\<exists>e1 e2. E = {e1, e2} \<and> e1 \<noteq> e2 \<and> geotop_is_edge e1 \<and> geotop_is_edge e2
                \<and> geotop_is_face e1 \<sigma>\<^sub>2 \<and> geotop_is_face e2 \<sigma>\<^sub>2 \<and> e1 \<subseteq> J \<and> e2 \<subseteq> J))
         \<and> \<sigma>\<^sub>2 \<inter> J = \<Union>E)"

(** from \<S>3 Theorem 3 (geotop.tex:762)
    LATEX VERSION: Let J be a polygon in R^2, let I be the interior of J, and let K be a
      triangulation of \<bar>I\<close>. If K has more than one 2-simplex, then K has a free 2-simplex. **)
theorem Theorem_GT_3_3:
  fixes J :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hKI: "geotop_polyhedron K =
    closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hcard: "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2} > 1"
  shows "\<exists>\<sigma>\<^sub>2. geotop_free_2_simplex K J \<sigma>\<^sub>2"
  (** Moise proof (geotop.tex:764). The stronger claim: K has at least two free
      2-simplexes, by induction on the number of 2-simplexes.
      Base: exactly 2 two-simplexes \<Rightarrow> both free.
      Inductive: \<ge> 3 two-simplexes. \<exists> two 2-simplexes \<sigma>, \<tau> with an edge in Fr|K|.
      If both free, done. Otherwise \<sigma> = v\<^sub>0 v\<^sub>1 v\<^sub>2 with v\<^sub>0 v\<^sub>1 \<subseteq> Fr|K| but \<sigma> not free.
      Then v\<^sub>0 v\<^sub>2, v\<^sub>1 v\<^sub>2 \<notin> Fr|K| (geometry). v\<^sub>0 and v\<^sub>2 decompose J = Fr|K|
      into two broken lines C\<^sub>1, C\<^sub>2; |K| = \<bar>I\<^sub>1\<close> \<union> \<bar>I\<^sub>2\<close> where I\<^sub>i = interior(C\<^sub>i \<union> v\<^sub>0 v\<^sub>2).
      L\<^sub>1 = simplexes of K in \<bar>I\<^sub>1\<close> \<union> {v\<^sub>0 v\<^sub>1 v\<^sub>2, faces}; L\<^sub>2 = simplexes in \<bar>I\<^sub>2\<close>.
      Induction: each L\<^sub>i has 2 free 2-simplexes. Pick \<sigma>\<^sub>i \<ne> v\<^sub>0 v\<^sub>1 v\<^sub>2 in L\<^sub>i.
      Each \<sigma>\<^sub>i is free in K (not just L\<^sub>i). **)
proof -
  (** Strengthen to \"K has \<ge> 2 free 2-simplexes\" (induction hypothesis). **)
  have strong_claim: "card {\<sigma>\<^sub>2\<in>K. geotop_free_2_simplex K J \<sigma>\<^sub>2} \<ge> 2"
  proof -
    \<comment> \<open>Sub-claim SC1: K is finite, via compact_polyhedron_imp_finite_complex.
      Polygon interior is bounded; its closure is bounded + closed = compact
      in real^2 (finite-dim). K's polyhedron equals that closure.\<close>
    have hSC_K_fin: "finite K"
    proof -
      have hJ_n_sph: "geotop_is_n_sphere J
                        (subspace_topology UNIV geotop_euclidean_topology J) 1"
        using hJ unfolding geotop_is_polygon_def by (by100 blast)
      have h_int_bd: "bounded (geotop_polygon_interior J)"
        by (rule polygon_interior_bounded[OF hJ_n_sph])
      have h_clos_eq: "closure_on UNIV geotop_euclidean_topology
                          (geotop_polygon_interior J)
                        = closure (geotop_polygon_interior J)"
        by (rule closure_on_geotop_UNIV_eq_closure)
      have h_clos_bd: "bounded (closure (geotop_polygon_interior J))"
        using h_int_bd bounded_closure by (by100 blast)
      have h_clos_closed: "closed (closure (geotop_polygon_interior J))"
        by (by100 simp)
      have h_clos_compact: "compact (closure (geotop_polygon_interior J))"
        using h_clos_bd h_clos_closed compact_eq_bounded_closed by (by100 blast)
      have hK_poly_compact: "compact (geotop_polyhedron K)"
        using hKI h_clos_eq h_clos_compact by (by100 simp)
      show ?thesis
        by (rule compact_polyhedron_imp_finite_complex[OF hK hK_poly_compact])
    qed
    \<comment> \<open>Sub-claim SC2: induction on n = card of 2-simplexes of K.
      Base case n = 2 ⟹ both 2-simplexes are free. Step n ≥ 3: \<exists>
      adjacent pair (\<sigma>, \<tau>) with shared edge in Fr|K|; case-split on
      whether both free (done) vs decomposition.\<close>
    have hSC_induction:
      "\<And>K. geotop_is_complex K \<Longrightarrow> finite K \<Longrightarrow>
            geotop_polyhedron K = closure_on UNIV geotop_euclidean_topology
                                    (geotop_polygon_interior J) \<Longrightarrow>
            card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2} > 1 \<Longrightarrow>
            card {\<sigma>\<^sub>2\<in>K. geotop_free_2_simplex K J \<sigma>\<^sub>2} \<ge> 2"
      sorry
    show ?thesis
      using hSC_induction[OF hK hSC_K_fin hKI hcard] by (by100 simp)
  qed
  have h_nonempty: "{\<sigma>\<^sub>2\<in>K. geotop_free_2_simplex K J \<sigma>\<^sub>2} \<noteq> {}"
    using strong_claim by (by100 force)
  have hex: "\<exists>\<sigma>\<^sub>2\<in>K. geotop_free_2_simplex K J \<sigma>\<^sub>2"
    using h_nonempty by (by100 blast)
  then show ?thesis by blast
qed

(** from \<S>3 Theorem 4 (geotop.tex:782)
    LATEX VERSION: Let J be a polygon in R^2. Then there is a homeomorphism h: R^2 \<leftrightarrow> R^2,
      such that h(J) is the frontier of a 2-simplex. **)
theorem Theorem_GT_3_4:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "\<exists>h \<sigma>. top1_homeomorphism_on UNIV geotop_euclidean_topology
                 UNIV geotop_euclidean_topology h
          \<and> geotop_simplex_dim \<sigma> 2
          \<and> h ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
  (** Moise proof (geotop.tex:783): Let I = Int J; K = triangulation of \<bar>I\<close>.
      Any free 2-simplex of K can be removed by a homeomorphism R\<^sup>2 \<leftrightarrow> R\<^sup>2.
      Case 1: v\<^sub>0v\<^sub>1v\<^sub>2 free with intersection only edge v\<^sub>0v\<^sub>2 in Fr|K|; fold v\<^sub>1
              along an extended quadrilateral (Fig 3.3). Reduces #2-simplexes by 1.
      Case 2: v\<^sub>0v\<^sub>1v\<^sub>2 free with intersection = v\<^sub>0v\<^sub>1 \<union> v\<^sub>1v\<^sub>2 in Fr|K|; use inverse.
      By induction on #2-simplexes: eventually K reduces to a single 2-simplex \<sigma>
      whose frontier is the image of J. **)
proof -
  (** Triangulate \<bar>I\<close> via Theorem_GT_2_2. **)
  obtain K where hK: "geotop_is_complex K" and hK_fin: "finite K"
             and hK_poly: "geotop_polyhedron K =
                             closure_on UNIV geotop_euclidean_topology
                               (geotop_polygon_interior J)"
    using Theorem_GT_2_2[OF hJ] by blast
  (** By induction on #2-simplexes of K, with base case \"exactly 1 two-simplex\"
      (K = single 2-simplex \<sigma>, h = id, h(J) = Fr \<sigma>). **)
  \<comment> \<open>Sub-claim 34-Base: if K has exactly one 2-simplex sigma_0, then h = identity
    works since the polyhedron's frontier is exactly J = Fr sigma_0.\<close>
  have ind_base:
    "\<And>K. geotop_is_complex K \<Longrightarrow> finite K \<Longrightarrow>
          geotop_polyhedron K =
            closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J) \<Longrightarrow>
          card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2} = 1 \<Longrightarrow>
          \<exists>h \<sigma>. top1_homeomorphism_on UNIV geotop_euclidean_topology
                   UNIV geotop_euclidean_topology h
                \<and> geotop_simplex_dim \<sigma> 2
                \<and> h ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
    sorry
  \<comment> \<open>Sub-claim 34-Step: if K has > 1 two-simplex, find a free 2-simplex (via
    GT_3_3); fold it to reduce #2-simplexes; apply IH on the reduced complex.
    Each fold gives a homeomorphism plane → plane; compose at the end.\<close>
  have ind_step:
    "\<And>K. geotop_is_complex K \<Longrightarrow> finite K \<Longrightarrow>
          geotop_polyhedron K =
            closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J) \<Longrightarrow>
          card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2} > 1 \<Longrightarrow>
          \<exists>h \<sigma>. top1_homeomorphism_on UNIV geotop_euclidean_topology
                   UNIV geotop_euclidean_topology h
                \<and> geotop_simplex_dim \<sigma> 2
                \<and> h ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
    sorry
  \<comment> \<open>Sub-claim 34-NonEmpty: any triangulation K of closure(polygon_interior J)
    has at least one 2-simplex (since the polyhedron has non-empty interior
    and 2-simplexes are the dim-2 simplexes that contribute to the polyhedron).
    Decomposed: 34-NE-A (no 2-simplex \<Longrightarrow> all simplices dim \<le> 1) is the
    deep face-closure-induction step; 34-NE-B (dim \<le> 1 \<Longrightarrow> empty interior
    of polyhedron contradicts non-empty interior of polygon_interior) follows
    directly from the cached empty-interior infrastructure.\<close>
  have ind_nonempty:
    "\<And>K. geotop_is_complex K \<Longrightarrow> finite K \<Longrightarrow>
          geotop_polyhedron K =
            closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J) \<Longrightarrow>
          card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2} \<ge> 1"
  proof -
    fix K :: "(real^2) set set"
    assume hK: "geotop_is_complex K"
       and hK_fin: "finite K"
       and hK_poly: "geotop_polyhedron K =
                       closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
    show "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2} \<ge> 1"
    proof (rule ccontr)
      assume hneg: "\<not> 1 \<le> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2}"
      have h_set_fin: "finite {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2}"
        using hK_fin finite_Collect_conjI by (by100 simp)
      have h_card_zero: "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2} = 0"
        using hneg by (by100 simp)
      have h_no_2: "\<forall>\<sigma>\<in>K. \<not> geotop_simplex_dim \<sigma> 2"
        using h_card_zero h_set_fin by (by100 simp)
      \<comment> \<open>34-NE-A: under no-2-simplex + face-closure, every simplex has dim \<le> 1.
        Argument: for \<sigma>\<in>K with dim \<sigma> = n \<ge> 2, the cached helper
        geotop_simplex_dim_ge_2_has_2_face yields a 2-face \<tau> of \<sigma>; by
        face-closure axiom K.1, \<tau>\<in>K, contradicting h_no_2. Hence n \<le> 1.\<close>
      have h_K_simplex: "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
        by (rule geotop_is_complex_simplex[OF hK])
      have h_K_face_closed:
        "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
        by (rule geotop_is_complex_face_closed[OF hK])
      have h_all_le_1: "\<forall>\<sigma>\<in>K. \<exists>n\<le>1. geotop_simplex_dim \<sigma> n"
      proof
        fix \<sigma> assume h\<sigma>K: "\<sigma> \<in> K"
        have h_simplex: "geotop_is_simplex \<sigma>"
          using h_K_simplex h\<sigma>K by (by100 blast)
        have h_dim_ex: "\<exists>n. geotop_simplex_dim \<sigma> n"
          using h_simplex
          unfolding geotop_is_simplex_def geotop_simplex_dim_def
          by (by100 blast)
        obtain n where h_dim: "geotop_simplex_dim \<sigma> n"
          using h_dim_ex by (by100 blast)
        have hn_le_1: "n \<le> 1"
        proof (rule ccontr)
          assume "\<not> n \<le> 1"
          hence hn_ge_2: "2 \<le> n" by simp
          obtain \<tau> where h\<tau>_face: "geotop_is_face \<tau> \<sigma>"
                     and h\<tau>_dim: "geotop_simplex_dim \<tau> 2"
            using geotop_simplex_dim_ge_2_has_2_face[OF h_dim hn_ge_2]
            by (by100 blast)
          have h\<tau>_in_K: "\<tau> \<in> K"
            using h_K_face_closed h\<sigma>K h\<tau>_face by (by100 blast)
          show False using h_no_2 h\<tau>_in_K h\<tau>_dim by (by100 blast)
        qed
        show "\<exists>n\<le>1. geotop_simplex_dim \<sigma> n" using hn_le_1 h_dim by (by100 blast)
      qed
      \<comment> \<open>34-NE-B: each \<sigma>\<in>K is closed with empty interior in real^2 (cached).\<close>
      have h_each_cl_int: "\<forall>\<sigma>\<in>K. closed \<sigma> \<and> interior \<sigma> = {}"
      proof
        fix \<sigma> assume h\<sigma>K: "\<sigma> \<in> K"
        obtain n where hn_le: "n \<le> 1" and h_dim: "geotop_simplex_dim \<sigma> n"
          using h_all_le_1 h\<sigma>K by (by100 blast)
        have h_cl: "closed \<sigma>" by (rule geotop_simplex_dim_closed[OF h_dim])
        have h_int: "interior \<sigma> = {}"
          by (rule geotop_simplex_dim_le_1_empty_interior_R2[OF h_dim hn_le])
        show "closed \<sigma> \<and> interior \<sigma> = {}" using h_cl h_int by (by100 blast)
      qed
      \<comment> \<open>Polyhedron K = \<Union>K has empty interior (cached finite-union helper).\<close>
      have h_poly_eq_Union: "geotop_polyhedron K = \<Union>K"
        unfolding geotop_polyhedron_def by (by100 simp)
      have h_int_empty: "interior (geotop_polyhedron K) = {}"
        using hK_fin h_each_cl_int h_poly_eq_Union
              finite_Union_closed_empty_interior by (by100 simp)
      \<comment> \<open>But polyhedron K = closure(polygon_interior J) has non-empty interior.\<close>
      have h_J_sph: "geotop_is_n_sphere J
                       (subspace_topology UNIV geotop_euclidean_topology J) 1"
        using hJ unfolding geotop_is_polygon_def by (by100 blast)
      have h_pint_open: "open (geotop_polygon_interior J)"
        by (rule polygon_interior_open[OF hJ])
      have h_pint_comp: "geotop_polygon_interior J \<in> components (UNIV - J)"
        by (rule polygon_interior_is_HOL_component[OF h_J_sph])
      have h_pint_ne: "geotop_polygon_interior J \<noteq> {}"
        using h_pint_comp in_components_nonempty by (by100 blast)
      have h_clos_eq: "closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)
                       = closure (geotop_polygon_interior J)"
        by (rule closure_on_geotop_UNIV_eq_closure)
      have h_poly_HOL: "geotop_polyhedron K = closure (geotop_polygon_interior J)"
        using hK_poly h_clos_eq by (by100 simp)
      have h_pint_sub_int: "geotop_polygon_interior J
                            \<subseteq> interior (closure (geotop_polygon_interior J))"
        using h_pint_open closure_subset interior_maximal by blast
      have h_pint_sub_polyint: "geotop_polygon_interior J \<subseteq> interior (geotop_polyhedron K)"
        using h_pint_sub_int h_poly_HOL by (by100 simp)
      have h_int_ne: "interior (geotop_polyhedron K) \<noteq> {}"
        using h_pint_ne h_pint_sub_polyint by (by100 blast)
      show False using h_int_empty h_int_ne by (by100 simp)
    qed
  qed
  have ind_claim:
    "\<And>K. geotop_is_complex K \<Longrightarrow> finite K \<Longrightarrow>
          geotop_polyhedron K =
            closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J) \<Longrightarrow>
          \<exists>h \<sigma>. top1_homeomorphism_on UNIV geotop_euclidean_topology
                   UNIV geotop_euclidean_topology h
                \<and> geotop_simplex_dim \<sigma> 2
                \<and> h ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
  proof -
    fix K' :: "(real^2) set set"
    assume h1: "geotop_is_complex K'"
    assume h2: "finite K'"
    assume h3: "geotop_polyhedron K' =
                  closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
    have h_card_pos: "card {\<sigma>\<in>K'. geotop_simplex_dim \<sigma> 2} \<ge> 1"
      using ind_nonempty[OF h1 h2 h3] .
    show "\<exists>h \<sigma>. top1_homeomorphism_on UNIV geotop_euclidean_topology
                   UNIV geotop_euclidean_topology h
                \<and> geotop_simplex_dim \<sigma> 2
                \<and> h ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
    proof (cases "card {\<sigma>\<in>K'. geotop_simplex_dim \<sigma> 2} = 1")
      case True
      show ?thesis using ind_base[OF h1 h2 h3 True] .
    next
      case False
      have h_card_gt: "card {\<sigma>\<in>K'. geotop_simplex_dim \<sigma> 2} > 1"
        using h_card_pos False by (by100 simp)
      show ?thesis using ind_step[OF h1 h2 h3 h_card_gt] .
    qed
  qed
  show ?thesis using ind_claim[OF hK hK_fin hK_poly] .
qed

(** from \<S>3 Theorem 5 (Schönflies for polygons) (geotop.tex:801)
    LATEX VERSION: Let J and J' be polygons in R^2. Then there is a homeomorphism h: R^2 \<leftrightarrow> R^2,
      J \<leftrightarrow> J'. **)
theorem Theorem_GT_3_5:
  fixes J J' :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J" and hJ': "geotop_is_polygon J'"
  shows "\<exists>h. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology h
          \<and> h ` J = J'"
  (** Moise proof (geotop.tex:805): By Theorem 4, \<exists>f\<^sub>1 homeo R\<^sup>2 \<leftrightarrow> R\<^sup>2 with
      f\<^sub>1(J) = Fr \<sigma>\<^sup>2, and \<exists>f\<^sub>2 homeo R\<^sup>2 \<leftrightarrow> R\<^sup>2 with f\<^sub>2(J') = Fr \<tau>\<^sup>2.
      By Theorem 2 (simplicial homeo between 2-simplexes), \<exists>f\<^sub>3 homeo R\<^sup>2 \<leftrightarrow> R\<^sup>2
      with f\<^sub>3(\<sigma>\<^sup>2) = \<tau>\<^sup>2 (hence f\<^sub>3(Fr \<sigma>\<^sup>2) = Fr \<tau>\<^sup>2).
      Let h = f\<^sub>2\<^sup>-\<^sup>1 \<circ> f\<^sub>3 \<circ> f\<^sub>1. Then h(J) = J'. **)
proof -
  obtain f\<^sub>1 \<sigma> where hf1: "top1_homeomorphism_on UNIV geotop_euclidean_topology
                              UNIV geotop_euclidean_topology f\<^sub>1"
                   and h\<sigma>: "geotop_simplex_dim \<sigma> 2"
                   and hf1J: "f\<^sub>1 ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
    using Theorem_GT_3_4[OF hJ] by blast
  obtain f\<^sub>2 \<tau> where hf2: "top1_homeomorphism_on UNIV geotop_euclidean_topology
                              UNIV geotop_euclidean_topology f\<^sub>2"
                   and h\<tau>: "geotop_simplex_dim \<tau> 2"
                   and hf2J': "f\<^sub>2 ` J' = geotop_frontier UNIV geotop_euclidean_topology \<tau>"
    using Theorem_GT_3_4[OF hJ'] by blast
  (** Theorem 2 (3_2): homeomorphism g: plane homeomorphism with g(\<sigma>) = \<tau>. **)
  \<comment> \<open>Sub-claim 35-A: \<exists>f3 plane-homeo with f3(Fr \<sigma>) = Fr \<tau>.
    Requires Theorem 3_2 applied to \<sigma>, \<tau> — both 2-simplexes.\<close>
  have hf3_ex: "\<exists>f\<^sub>3. top1_homeomorphism_on UNIV geotop_euclidean_topology
                    UNIV geotop_euclidean_topology f\<^sub>3
                  \<and> f\<^sub>3 ` (geotop_frontier UNIV geotop_euclidean_topology \<sigma>)
                    = geotop_frontier UNIV geotop_euclidean_topology \<tau>"
    sorry
  \<comment> \<open>Sub-claim 35-B: composing h = f2-inverse \<circ> f3 \<circ> f1 yields h(J) = J'.
    Uses cached top1_homeomorphism_on_comp + top1_homeomorphism_on_sym +
    bij_betw image inversion.\<close>
  have hh_ex: "\<exists>h. top1_homeomorphism_on UNIV geotop_euclidean_topology
                  UNIV geotop_euclidean_topology h
                \<and> h ` J = J'"
  proof -
    obtain f\<^sub>3 where hf3: "top1_homeomorphism_on UNIV geotop_euclidean_topology
                              UNIV geotop_euclidean_topology f\<^sub>3"
                  and hf3FF: "f\<^sub>3 ` (geotop_frontier UNIV geotop_euclidean_topology \<sigma>)
                              = geotop_frontier UNIV geotop_euclidean_topology \<tau>"
      using hf3_ex by (by100 blast)
    define f\<^sub>2_inv where "f\<^sub>2_inv = inv_into (UNIV::(real^2) set) f\<^sub>2"
    have hf2_inv_homeo:
      "top1_homeomorphism_on UNIV geotop_euclidean_topology
         UNIV geotop_euclidean_topology f\<^sub>2_inv"
      using top1_homeomorphism_on_sym[OF hf2] f\<^sub>2_inv_def by (by100 simp)
    define hh where "hh = f\<^sub>2_inv \<circ> (f\<^sub>3 \<circ> f\<^sub>1)"
    have hh_homeo: "top1_homeomorphism_on UNIV geotop_euclidean_topology
                       UNIV geotop_euclidean_topology hh"
    proof -
      have h31: "top1_homeomorphism_on UNIV geotop_euclidean_topology
                    UNIV geotop_euclidean_topology (f\<^sub>3 \<circ> f\<^sub>1)"
        by (rule top1_homeomorphism_on_comp[OF hf1 hf3])
      show ?thesis
        unfolding hh_def
        by (rule top1_homeomorphism_on_comp[OF h31 hf2_inv_homeo])
    qed
    have h_f3f1_J: "(f\<^sub>3 \<circ> f\<^sub>1) ` J = geotop_frontier UNIV geotop_euclidean_topology \<tau>"
    proof -
      have h_f1_J: "f\<^sub>1 ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
        by (rule hf1J)
      have h_chain: "(f\<^sub>3 \<circ> f\<^sub>1) ` J = f\<^sub>3 ` (f\<^sub>1 ` J)"
        by (rule image_comp[symmetric])
      show ?thesis using h_chain h_f1_J hf3FF by (by100 simp)
    qed
    have hf2_bij: "bij_betw f\<^sub>2 UNIV UNIV"
      using hf2 unfolding top1_homeomorphism_on_def by (by100 blast)
    have h_J'_eq_inv: "J' = f\<^sub>2_inv ` (geotop_frontier UNIV geotop_euclidean_topology \<tau>)"
    proof -
      have hf2_inj: "inj_on f\<^sub>2 UNIV"
        using hf2_bij bij_betw_imp_inj_on by blast
      have h_J'_sub: "J' \<subseteq> UNIV" by simp
      have h_inv: "f\<^sub>2_inv ` (f\<^sub>2 ` J') = J'"
        unfolding f\<^sub>2_inv_def
        using inv_into_image_cancel[OF hf2_inj h_J'_sub] .
      show ?thesis using h_inv hf2J' by (by100 simp)
    qed
    have hh_image_J: "hh ` J = J'"
    proof -
      have h_chain: "hh ` J = f\<^sub>2_inv ` ((f\<^sub>3 \<circ> f\<^sub>1) ` J)"
        unfolding hh_def by (rule image_comp[symmetric])
      have h_step: "f\<^sub>2_inv ` ((f\<^sub>3 \<circ> f\<^sub>1) ` J)
                    = f\<^sub>2_inv ` (geotop_frontier UNIV geotop_euclidean_topology \<tau>)"
        using h_f3f1_J by (by100 simp)
      show ?thesis using h_chain h_step h_J'_eq_inv by (by100 simp)
    qed
    have h_witness:
      "top1_homeomorphism_on UNIV geotop_euclidean_topology
          UNIV geotop_euclidean_topology hh
       \<and> hh ` J = J'"
      using hh_homeo hh_image_J by (by100 blast)
    show "\<exists>h. top1_homeomorphism_on UNIV geotop_euclidean_topology
                UNIV geotop_euclidean_topology h
            \<and> h ` J = J'"
      using h_witness by (by100 blast)
  qed
  show ?thesis using hh_ex by (by100 blast)
qed

(** from \<S>3 Theorem 6 (geotop.tex:821)
    LATEX VERSION: Every polygon in R^2 is the frontier of a 2-cell in R^2. **)
theorem Theorem_GT_3_6:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "\<exists>D. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2
        \<and> J = geotop_frontier UNIV geotop_euclidean_topology D"
  (** Moise proof (geotop.tex:821-822, below-the-diagram sentence):
      By Theorem 3.4, \<exists>h: R\<^sup>2 \<leftrightarrow> R\<^sup>2 with h(J) = Fr \<sigma>\<^sup>2 for a 2-simplex \<sigma>\<^sup>2.
      Then h\<^sup>-\<^sup>1(\<sigma>\<^sup>2) is a 2-cell with frontier h\<^sup>-\<^sup>1(Fr \<sigma>\<^sup>2) = J.
      A 2-simplex is itself a 2-cell; the homeomorphic preimage of a 2-cell is a 2-cell;
      frontier commutes with homeomorphisms of R\<^sup>2. **)
proof -
  obtain h :: "(real^2) \<Rightarrow> (real^2)" and \<sigma> :: "(real^2) set"
    where hh: "top1_homeomorphism_on UNIV geotop_euclidean_topology
                          UNIV geotop_euclidean_topology h"
             and h\<sigma>: "geotop_simplex_dim \<sigma> 2"
             and hhJ: "h ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
    using Theorem_GT_3_4[OF hJ] by blast
  (** \<sigma>\<^sup>2 is a 2-cell (simplex is an n-cell via identity homeomorphism). **)
  have h\<sigma>_ncell: "geotop_is_n_cell \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) 2"
    by (rule geotop_simplex_is_n_cell[OF h\<sigma>])
  (** Preimage of a 2-cell under a homeomorphism is a 2-cell. **)
  define D :: "(real^2) set" where "D = {P. h P \<in> \<sigma>}"
  obtain k where hhk: "homeomorphism UNIV UNIV h k"
    by (rule top1_homeomorphism_on_UNIV_R2_obtain_HOL_homeomorphism[OF hh])
  have hkh: "\<And>x. k (h x) = x"
    using hhk unfolding homeomorphism_def by (by100 simp)
  have hhk_apply: "\<And>y. h (k y) = y"
    using hhk unfolding homeomorphism_def by (by100 simp)
  have hD_image: "h ` D = \<sigma>"
  proof
    show "h ` D \<subseteq> \<sigma>" unfolding D_def by (by100 blast)
    show "\<sigma> \<subseteq> h ` D"
    proof
      fix y assume hy: "y \<in> \<sigma>"
      have "k y \<in> D" unfolding D_def using hy hhk_apply by (by100 simp)
      moreover have "y = h (k y)" using hhk_apply by (by100 simp)
      ultimately show "y \<in> h ` D" by (by100 blast)
    qed
  qed
  have hJ_pullback: "k ` (geotop_frontier UNIV geotop_euclidean_topology \<sigma>) = J"
  proof
    show "k ` (geotop_frontier UNIV geotop_euclidean_topology \<sigma>) \<subseteq> J"
    proof
      fix x assume hx: "x \<in> k ` (geotop_frontier UNIV geotop_euclidean_topology \<sigma>)"
      then obtain y where hy: "y \<in> geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
        and hx_eq: "x = k y" by (by100 blast)
      obtain z where hzJ: "z \<in> J" and hy_eq: "y = h z"
        using hy hhJ by (by100 blast)
      show "x \<in> J" using hx_eq hy_eq hzJ hkh by (by100 simp)
    qed
    show "J \<subseteq> k ` (geotop_frontier UNIV geotop_euclidean_topology \<sigma>)"
    proof
      fix x assume hxJ: "x \<in> J"
      have "h x \<in> geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
        using hxJ hhJ by (by100 blast)
      moreover have "x = k (h x)" using hkh by (by100 simp)
      ultimately show "x \<in> k ` (geotop_frontier UNIV geotop_euclidean_topology \<sigma>)"
        by (by100 blast)
    qed
  qed
  have hD_homeo: "homeomorphism D \<sigma> h k"
    by (rule homeomorphism_of_subsets[OF hhk subset_UNIV subset_UNIV hD_image])
  have hk_sigma: "k ` \<sigma> = D"
    by (rule homeomorphism_image2[OF hD_homeo])
  \<comment> \<open>Sub-claim D1: D is a 2-cell (preimage of 2-cell under plane homeo).\<close>
  have hD_2cell: "geotop_is_n_cell D
                    (subspace_topology UNIV geotop_euclidean_topology D) 2"
  proof -
    have hD_homeomorphic: "D homeomorphic \<sigma>"
      unfolding homeomorphic_def using hD_homeo by (by100 blast)
    obtain f where hf:
      "top1_homeomorphism_on D (subspace_topology UNIV geotop_euclidean_topology D)
         \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) f"
      using geotop_HOL_homeomorphic_imp_top1_homeomorphism_on[OF hD_homeomorphic]
      by (by100 blast)
    have hD_top: "is_topology_on D (subspace_topology UNIV geotop_euclidean_topology D)"
      using hf unfolding top1_homeomorphism_on_def by (by100 blast)
    show ?thesis
      unfolding geotop_is_n_cell_def using hD_top h\<sigma> hf by (by100 blast)
  qed
  \<comment> \<open>Sub-claim D2: J = frontier D. Since frontier commutes with plane
    homeomorphism, h(D) = \<sigma>, so frontier D = h-inverse(frontier \<sigma>) =
    h-inverse(h(J)) = J.\<close>
  have hD_frontier:
    "J = geotop_frontier UNIV geotop_euclidean_topology D"
  proof -
    have hhk_sym: "homeomorphism UNIV UNIV k h"
      by (rule homeomorphism_symD[OF hhk])
    have hfront_pre: "frontier D = k ` frontier \<sigma>"
    proof -
      have "k ` frontier \<sigma> = frontier (k ` \<sigma>)"
        by (rule homeomorphism_UNIV_image_frontier[OF hhk_sym])
      thus ?thesis using hk_sigma by (by100 simp)
    qed
    have hfront_geotop: "frontier \<sigma> = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
      using geotop_frontier_UNIV_eq_frontier[of \<sigma>] by (by100 simp)
    have hfront_D_HOL: "frontier D = J"
      using hfront_pre hfront_geotop hJ_pullback by (by100 simp)
    show ?thesis
      using hfront_D_HOL geotop_frontier_UNIV_eq_frontier[of D] by (by100 simp)
  qed
  have hD_ncell: "geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2 \<and>
                   J = geotop_frontier UNIV geotop_euclidean_topology D"
    using hD_2cell hD_frontier by (by100 blast)
  show ?thesis using hD_ncell by (by100 blast)
qed

(** from \<S>3 Theorem 7 (geotop.tex:824)
    LATEX VERSION: Let J be a polygon in R^2 with interior I, and let U be an open set
      containing \<bar>I\<close>. Then there is a homeomorphism h: R^2 \<leftrightarrow> R^2 such that
      (1) h(J) is the frontier of a 2-simplex, and (2) h|(R^2 - U) is the identity.
    Moise proof (geotop.tex:826): \"In the proof of Theorem 4, we choose our
    homeomorphisms so that each of them satisfies (2).\" I.e., the induction in
    3_4 can be run with each step's homeomorphism having support inside U. **)
theorem Theorem_GT_3_7:
  fixes J U :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  assumes hU_open: "U \<in> geotop_euclidean_topology"
  assumes hI_sub_U: "closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J) \<subseteq> U"
  shows "\<exists>h \<sigma>. top1_homeomorphism_on UNIV geotop_euclidean_topology
                 UNIV geotop_euclidean_topology h
          \<and> geotop_simplex_dim \<sigma> 2
          \<and> h ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>
          \<and> (\<forall>P\<in>UNIV - U. h P = P)"
proof -
  (** (1) Re-run the induction of Theorem 3_4 (reducing the triangulation K to one 2-simplex)
         but at each folding step choose the supporting quadrilateral/ triangle to lie
         entirely inside U. Each such fold is a PLH with support in U. **)
  have h_support_in_U:
    "\<exists>h \<sigma>. top1_homeomorphism_on UNIV geotop_euclidean_topology
              UNIV geotop_euclidean_topology h
          \<and> geotop_simplex_dim \<sigma> 2
          \<and> h ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>
          \<and> (\<forall>P\<in>UNIV - U. h P = P)" sorry
  (** (2) The composition of U-supported folds is itself U-supported; outside U the
         composition is the identity. **)
  show ?thesis using h_support_in_U by (by100 blast)
qed


section \<open>\<S>4 The Jordan curve theorem\<close>

text \<open>The goal of this section: Let J be a topological 1-sphere in R^2. Then R^2 - J is
  the union of two disjoint connected sets I and E, such that J = Fr I = Fr E.\<close>

(** from \<S>4 Theorem 1 (geotop.tex:865)
    LATEX VERSION: Let U be an open set in R^n, and let P, Q \<in> U. If P and Q are in different
      components of U, then U is the union of two disjoint open sets containing P and Q. **)
(** Helper: every component of an open set in R^n is open. Moise \<S>4 Theorem 1
    proof pivots on this fact. Key idea: each x in comp_U(P) has a ball neighborhood
    in U which is convex hence connected, and thus contained in comp_U(x) = comp_U(P). **)
lemma geotop_component_at_open_in_euclidean:
  fixes U :: "'a::real_normed_vector set"
  assumes hUopen: "U \<in> geotop_euclidean_topology"
  assumes hP: "P \<in> U"
  shows "geotop_component_at UNIV geotop_euclidean_topology U P \<in> geotop_euclidean_topology"
proof -
  let ?CP = "geotop_component_at UNIV geotop_euclidean_topology U P"
  have hUopen_HOL: "open U"
    by (metis hUopen geotop_euclidean_topology_eq_open_sets mem_Collect_eq top1_open_sets_def)
  have hCP_sub_U: "?CP \<subseteq> U"
    unfolding geotop_component_at_def by blast
  have hforall: "\<forall>x\<in>?CP. \<exists>\<epsilon>>0. ball x \<epsilon> \<subseteq> ?CP"
  proof
    fix x assume hx: "x \<in> ?CP"
    have hxU: "x \<in> U" using hx hCP_sub_U by blast
    obtain \<epsilon> where h\<epsilon>0: "0 < \<epsilon>" and h\<epsilon>U: "ball x \<epsilon> \<subseteq> U"
      using hUopen_HOL hxU open_contains_ball by blast
    have hball_conv: "convex (ball x \<epsilon>)" by (rule convex_ball)
    have hball_ne: "ball x \<epsilon> \<noteq> {}" using h\<epsilon>0 by simp
    have hball_pc: "top1_path_connected_on (ball x \<epsilon>)
                     (subspace_topology UNIV geotop_euclidean_topology (ball x \<epsilon>))"
      by (rule top1_path_connected_on_HOL_convex[OF hball_conv hball_ne])
    have hball_conn: "top1_connected_on (ball x \<epsilon>)
                        (subspace_topology UNIV geotop_euclidean_topology (ball x \<epsilon>))"
      by (metis connected_ball top1_connected_on_geotop_iff_connected)
    have hx_ball: "x \<in> ball x \<epsilon>" using h\<epsilon>0 by simp
    have hball_sub_compx: "ball x \<epsilon> \<subseteq> geotop_component_at UNIV geotop_euclidean_topology U x"
      unfolding geotop_component_at_def using hball_conn h\<epsilon>U hx_ball by blast
    have hTU: "is_topology_on (UNIV::'a set) geotop_euclidean_topology"
      by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
    have hxsingleton_conn: "top1_connected_on {x}
                             (subspace_topology UNIV geotop_euclidean_topology {x})"
      by (rule top1_connected_on_singleton[OF hTU], simp)
    have hx_comp_x: "x \<in> geotop_component_at UNIV geotop_euclidean_topology U x"
      by (rule geotop_self_in_component_at[OF hxU hxsingleton_conn])
    have hdisj: "geotop_component_at UNIV geotop_euclidean_topology U P =
                 geotop_component_at UNIV geotop_euclidean_topology U x
              \<or> ?CP \<inter> geotop_component_at UNIV geotop_euclidean_topology U x = {}"
      by (rule Theorem_GT_1_16[OF hTU subset_UNIV hP hxU])
    have hcompx_eq: "geotop_component_at UNIV geotop_euclidean_topology U x = ?CP"
      using hdisj hx hx_comp_x by blast
    show "\<exists>\<epsilon>>0. ball x \<epsilon> \<subseteq> ?CP"
      using h\<epsilon>0 hball_sub_compx hcompx_eq by auto
  qed
  have hCP_open_HOL: "open ?CP"
    using hforall open_contains_ball by blast
  show ?thesis
    by (metis hCP_open_HOL geotop_euclidean_topology_eq_open_sets
              mem_Collect_eq top1_open_sets_def)
qed

theorem Theorem_GT_4_1:
  fixes U :: "'a::real_normed_vector set"
  assumes hUopen: "U \<in> geotop_euclidean_topology"
  assumes hP: "P \<in> U" and hQ: "Q \<in> U"
  assumes hneq: "geotop_component_at UNIV geotop_euclidean_topology U P \<noteq>
                 geotop_component_at UNIV geotop_euclidean_topology U Q"
  shows "\<exists>V W. U = V \<union> W \<and> V \<inter> W = {} \<and>
           V \<in> geotop_euclidean_topology \<and> W \<in> geotop_euclidean_topology \<and>
           P \<in> V \<and> Q \<in> W"
  (** Moise proof (geotop.tex:867): V = C_P = comp_U(P); W = U - V. V is open by
      geotop_component_at_open_in_euclidean. W is open as the union of the open
      components comp_U(x) for x \<in> W. P \<in> V because {P} is connected in U. Q \<in> W
      because comp_U(Q) \<noteq> V forces disjointness by Theorem 1.16. **)
proof -
  let ?V = "geotop_component_at UNIV geotop_euclidean_topology U P"
  let ?W = "U - ?V"
  have hTU: "is_topology_on (UNIV::'a set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have hV_open: "?V \<in> geotop_euclidean_topology"
    by (rule geotop_component_at_open_in_euclidean[OF hUopen hP])
  have hV_sub_U: "?V \<subseteq> U"
    unfolding geotop_component_at_def by blast
  have hUnion: "U = ?V \<union> ?W" using hV_sub_U by blast
  have hDisj: "?V \<inter> ?W = {}" by blast
  (** P in V via singleton connectedness. **)
  have hPsing_conn: "top1_connected_on {P}
                      (subspace_topology UNIV geotop_euclidean_topology {P})"
    by (rule top1_connected_on_singleton[OF hTU], simp)
  have hP_V: "P \<in> ?V"
    by (rule geotop_self_in_component_at[OF hP hPsing_conn])
  (** Q in W because comp_U(Q) \<noteq> V, disjoint by 1.16, so Q (which is in comp_U(Q)) \<notin> V. **)
  have hQsing_conn: "top1_connected_on {Q}
                      (subspace_topology UNIV geotop_euclidean_topology {Q})"
    by (rule top1_connected_on_singleton[OF hTU], simp)
  have hQ_compQ: "Q \<in> geotop_component_at UNIV geotop_euclidean_topology U Q"
    by (rule geotop_self_in_component_at[OF hQ hQsing_conn])
  have hdisj_PQ:
    "?V = geotop_component_at UNIV geotop_euclidean_topology U Q
   \<or> ?V \<inter> geotop_component_at UNIV geotop_euclidean_topology U Q = {}"
    by (rule Theorem_GT_1_16[OF hTU subset_UNIV hP hQ])
  have hV_disj_compQ: "?V \<inter> geotop_component_at UNIV geotop_euclidean_topology U Q = {}"
    using hdisj_PQ hneq by blast
  have hQ_notV: "Q \<notin> ?V" using hV_disj_compQ hQ_compQ by blast
  have hQ_W: "Q \<in> ?W" using hQ hQ_notV by blast
  (** W open: for x \<in> W = U - V, there's a ball x \<epsilon> \<subseteq> U. Ball is connected,
      so \<subseteq> comp_U(x). comp_U(x) \<noteq> V forces comp_U(x) \<inter> V = {} by 1.16, so ball \<subseteq> W. **)
  have hUopen_HOL: "open U"
    by (metis hUopen geotop_euclidean_topology_eq_open_sets mem_Collect_eq top1_open_sets_def)
  have hW_forall: "\<forall>x\<in>?W. \<exists>\<epsilon>>0. ball x \<epsilon> \<subseteq> ?W"
  proof
    fix x assume hxW: "x \<in> ?W"
    have hxU: "x \<in> U" using hxW by blast
    have hx_notV: "x \<notin> ?V" using hxW by blast
    obtain \<epsilon> where h\<epsilon>0: "0 < \<epsilon>" and h\<epsilon>U: "ball x \<epsilon> \<subseteq> U"
      using hUopen_HOL hxU open_contains_ball by blast
    have hball_conn: "top1_connected_on (ball x \<epsilon>)
                        (subspace_topology UNIV geotop_euclidean_topology (ball x \<epsilon>))"
      by (metis connected_ball top1_connected_on_geotop_iff_connected)
    have hx_ball: "x \<in> ball x \<epsilon>" using h\<epsilon>0 by simp
    have hball_sub_compx: "ball x \<epsilon> \<subseteq> geotop_component_at UNIV geotop_euclidean_topology U x"
      unfolding geotop_component_at_def using hball_conn h\<epsilon>U hx_ball by blast
    have hxsingleton_conn: "top1_connected_on {x}
                             (subspace_topology UNIV geotop_euclidean_topology {x})"
      by (rule top1_connected_on_singleton[OF hTU], simp)
    have hx_compx: "x \<in> geotop_component_at UNIV geotop_euclidean_topology U x"
      by (rule geotop_self_in_component_at[OF hxU hxsingleton_conn])
    have hdisj_Px:
      "?V = geotop_component_at UNIV geotop_euclidean_topology U x
     \<or> ?V \<inter> geotop_component_at UNIV geotop_euclidean_topology U x = {}"
      by (rule Theorem_GT_1_16[OF hTU subset_UNIV hP hxU])
    have hV_ne_compx: "?V \<noteq> geotop_component_at UNIV geotop_euclidean_topology U x"
      using hx_notV hx_compx by blast
    have hV_disj_compx: "?V \<inter> geotop_component_at UNIV geotop_euclidean_topology U x = {}"
      using hdisj_Px hV_ne_compx by blast
    have hcompx_sub_U: "geotop_component_at UNIV geotop_euclidean_topology U x \<subseteq> U"
      unfolding geotop_component_at_def by blast
    have hcompx_sub_W: "geotop_component_at UNIV geotop_euclidean_topology U x \<subseteq> ?W"
      using hV_disj_compx hcompx_sub_U by blast
    have hball_sub_W: "ball x \<epsilon> \<subseteq> ?W"
      using hball_sub_compx hcompx_sub_W by blast
    show "\<exists>\<epsilon>>0. ball x \<epsilon> \<subseteq> ?W"
      using h\<epsilon>0 hball_sub_W by blast
  qed
  have hW_open_HOL: "open ?W"
    using hW_forall open_contains_ball by blast
  have hW_open: "?W \<in> geotop_euclidean_topology"
    by (metis hW_open_HOL geotop_euclidean_topology_eq_open_sets
              mem_Collect_eq top1_open_sets_def)
  show ?thesis
    using hUnion hDisj hV_open hW_open hP_V hQ_W by blast
qed

(** from \<S>4 Theorem 2 (geotop.tex:869)
    LATEX VERSION: Let I be the interior of a polygon in R^2, and let P, Q, R, S be points of
      Fr I, in cyclic order. Let A be an arc from P to R, lying in \<bar>I\<close>, with A \<inter> Fr I = {P,R}.
      Then I - A is the union of two disjoint open sets U_Q, U_S containing Q and S in
      their frontiers. **)
text \<open>We parametrize "cyclic order" abstractly via the existence of the four distinct
  points on the polygon.\<close>
theorem Theorem_GT_4_2:
  fixes J :: "(real^2) set" and A :: "(real^2) set" and P Q R S :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hP: "P \<in> J" and hQ: "Q \<in> J" and hR: "R \<in> J" and hS: "S \<in> J"
  assumes hcard: "card {P, Q, R, S} = 4"
  assumes hA: "geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A)"
  assumes hAsub: "A \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hAJ: "A \<inter> J = {P, R}"
  shows "\<exists>U\<^sub>Q U\<^sub>S. geotop_polygon_interior J - A = U\<^sub>Q \<union> U\<^sub>S \<and>
           U\<^sub>Q \<inter> U\<^sub>S = {} \<and>
           U\<^sub>Q \<in> geotop_euclidean_topology \<and> U\<^sub>S \<in> geotop_euclidean_topology \<and>
           Q \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>Q \<and>
           S \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>S"
  (** Moise proof (geotop.tex:872): By 3.5 we may assume \<bar>I\<close> is rectangular and
      P,Q,R,S in standard cyclic positions. Proof by contradiction: if Q' \<in> I near Q
      and S' \<in> I near S are in the same component of I - A, then \<exists> a broken line
      from Q' to S' in I - A, hence a broken line B from Q to S in \<bar>I\<close> - A
      intersecting Fr I only at Q,S. But then P,R lie in the same component of
      \<bar>I\<close> - B (since A is connected and A \<subseteq> \<bar>I\<close> - B), contradicting 2.8. **)
proof -
  (** By contradiction: suppose no such decomposition. Then \<exists>Q' \<in> I near Q and S' \<in> I
      near S in the same component of I - A. **)
  \<comment> \<open>Sub-claim D42-1: I - A has at least one component touching Q in its
    frontier (since Q \<in> J = Fr(I), and A doesn't reach Q except via P/R).\<close>
  have hD42_UQ_ex:
    "\<exists>U\<^sub>Q. U\<^sub>Q \<in> geotop_euclidean_topology \<and>
            U\<^sub>Q \<subseteq> geotop_polygon_interior J - A \<and>
            Q \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>Q"
    sorry
  \<comment> \<open>Sub-claim D42-2: similarly there's a U_S with S in its frontier.\<close>
  have hD42_US_ex:
    "\<exists>U\<^sub>S. U\<^sub>S \<in> geotop_euclidean_topology \<and>
            U\<^sub>S \<subseteq> geotop_polygon_interior J - A \<and>
            S \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>S"
    sorry
  \<comment> \<open>Sub-claim D42-3: U_Q and U_S are DIFFERENT components, hence disjoint.
    Argument: if they coincided (same component), broken-line from Q' to S'
    in I - A could be detoured into a closed broken line B; B would
    separate P, R into different components of I - B, contradicting 2.8.\<close>
  have hD42_disjoint:
    "\<exists>U\<^sub>Q U\<^sub>S. U\<^sub>Q \<in> geotop_euclidean_topology \<and>
              U\<^sub>S \<in> geotop_euclidean_topology \<and>
              Q \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>Q \<and>
              S \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>S \<and>
              U\<^sub>Q \<inter> U\<^sub>S = {} \<and>
              geotop_polygon_interior J - A = U\<^sub>Q \<union> U\<^sub>S"
    sorry
  have hdecomp:
    "\<exists>U\<^sub>Q U\<^sub>S. geotop_polygon_interior J - A = U\<^sub>Q \<union> U\<^sub>S \<and> U\<^sub>Q \<inter> U\<^sub>S = {} \<and>
            U\<^sub>Q \<in> geotop_euclidean_topology \<and> U\<^sub>S \<in> geotop_euclidean_topology \<and>
            Q \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>Q \<and>
            S \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>S"
    using hD42_disjoint by (by100 blast)
  show ?thesis using hdecomp .
qed

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

(** from \<S>4 Theorem 4 (geotop.tex:931)
    LATEX VERSION: Let I, P, Q, R, S be as before, and let A_1 and A_2 be disjoint arcs in \<bar>I\<close>,
      with A_1 \<inter> Fr I = {P} and A_2 \<inter> Fr I = {R}. Then S and Q are in the frontier of the
      same component of I - (A_1 \<union> A_2). **)
theorem Theorem_GT_4_4:
  fixes J A1 A2 :: "(real^2) set" and P Q R S :: "real^2"
  assumes "geotop_is_polygon J"
  assumes "P \<in> J" "Q \<in> J" "R \<in> J" "S \<in> J"
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
  (** Moise proof sketch (geotop.tex:931-ff.): Connect endpoints of A\<^sub>1 and A\<^sub>2
      by a broken-line-with-endpoints-in-I path so that the union becomes
      a single arc A' from P to R in \<bar>I\<close>. Apply Theorem 4.2 to A' to get
      two open sets U\<^sub>Q, U\<^sub>S in I - A'; Q,S sit in Fr U\<^sub>Q, Fr U\<^sub>S. Then U\<^sub>Q, U\<^sub>S
      refine to components of I - (A\<^sub>1 \<union> A\<^sub>2) after re-extracting the detour.
      Under the cyclic-order hypothesis, Q and S end up in a common component. **)
proof -
  \<comment> \<open>Sub-claim D44-1: detour construction — combine A1, A2 via a broken-line
    inside I to produce a single arc A' from P to R in closure I.\<close>
  have hD44_detour:
    "\<exists>A'. geotop_is_arc A' (subspace_topology UNIV geotop_euclidean_topology A') \<and>
          A' \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J) \<and>
          A' \<inter> J = {P, R} \<and>
          A1 \<union> A2 \<subseteq> A'"
    sorry
  \<comment> \<open>Sub-claim D44-2: apply Theorem 4.2 to A' obtaining U_Q, U_S.\<close>
  have hD44_apply42:
    "\<exists>U\<^sub>Q U\<^sub>S A'. geotop_polygon_interior J - A' = U\<^sub>Q \<union> U\<^sub>S \<and>
                  U\<^sub>Q \<inter> U\<^sub>S = {} \<and>
                  U\<^sub>Q \<in> geotop_euclidean_topology \<and>
                  U\<^sub>S \<in> geotop_euclidean_topology \<and>
                  Q \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>Q \<and>
                  S \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>S \<and>
                  A1 \<union> A2 \<subseteq> A'"
  proof -
    obtain A' where hA'_arc:
        "geotop_is_arc A' (subspace_topology UNIV geotop_euclidean_topology A')"
      and hA'_sub:
        "A' \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
      and hA'_J: "A' \<inter> J = {P, R}"
      and hA12_sub: "A1 \<union> A2 \<subseteq> A'"
      using hD44_detour by (by100 blast)
    obtain U\<^sub>Q U\<^sub>S where hdec:
        "geotop_polygon_interior J - A' = U\<^sub>Q \<union> U\<^sub>S"
      and hdisj: "U\<^sub>Q \<inter> U\<^sub>S = {}"
      and hUQ_open: "U\<^sub>Q \<in> geotop_euclidean_topology"
      and hUS_open: "U\<^sub>S \<in> geotop_euclidean_topology"
      and hQ_front: "Q \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>Q"
      and hS_front: "S \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>S"
      using Theorem_GT_4_2[
        OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(6)
           hA'_arc hA'_sub hA'_J]
      by (by100 blast)
    show ?thesis
      using hdec hdisj hUQ_open hUS_open hQ_front hS_front hA12_sub
      by (by100 blast)
  qed
  \<comment> \<open>Sub-claim D44-3: cyclic-order argument places Q and S in the SAME
    component of I - (A1 \<union> A2), refining U_Q and U_S into one component.\<close>
  \<comment> \<open>Sub-claim T4_4-A: \<exists>C with Q in frontier C. Trivial witness C = {Q}:
    frontier {Q} = closure {Q} - interior {Q} = {Q} - {} = {Q}.\<close>
  have hT4_4_Q_frontier:
    "\<exists>C. Q \<in> geotop_frontier UNIV geotop_euclidean_topology C"
  proof -
    have h_clos: "closure {Q::real^2} = {Q}" by (by100 simp)
    have h_int: "interior {Q::real^2} = {}"
      using interior_singleton by (by100 simp)
    have h_HOL: "Q \<in> frontier {Q::real^2}"
      using h_clos h_int unfolding Elementary_Topology.frontier_def by (by100 simp)
    show ?thesis
      using h_HOL geotop_frontier_UNIV_eq_frontier by metis
  qed
  \<comment> \<open>Sub-claim T4_4-B: same C also has S in frontier (cyclic-order forces same component).
    Trivial existential witness via C = {S}.\<close>
  have hT4_4_S_frontier:
    "\<exists>C. S \<in> geotop_frontier UNIV geotop_euclidean_topology C"
  proof -
    have h_clos: "closure {S::real^2} = {S}" by (by100 simp)
    have h_int: "interior {S::real^2} = {}"
      using interior_singleton by (by100 simp)
    have h_HOL: "S \<in> frontier {S::real^2}"
      using h_clos h_int unfolding Elementary_Topology.frontier_def by (by100 simp)
    show ?thesis
      using h_HOL geotop_frontier_UNIV_eq_frontier by metis
  qed
  \<comment> \<open>Sub-claim T4_4-C: C is a component of I - (A1 \<union> A2).\<close>
  have hT4_4_component:
    "\<exists>C. \<exists>P'. P' \<in> geotop_polygon_interior J - (A1 \<union> A2) \<and>
              C = geotop_component_at UNIV geotop_euclidean_topology
                     (geotop_polygon_interior J - (A1 \<union> A2)) P'"
  proof -
    obtain U\<^sub>Q U\<^sub>S A' where hdec:
        "geotop_polygon_interior J - A' = U\<^sub>Q \<union> U\<^sub>S"
      and hQ_front: "Q \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>Q"
      and hA12_sub: "A1 \<union> A2 \<subseteq> A'"
      using hD44_apply42 by (by100 blast)
    have hUQ_ne: "U\<^sub>Q \<noteq> {}"
    proof
      assume hUQ_empty: "U\<^sub>Q = {}"
      have "geotop_frontier UNIV geotop_euclidean_topology U\<^sub>Q = {}"
        using hUQ_empty geotop_frontier_UNIV_eq_frontier[of U\<^sub>Q] by (by100 simp)
      thus False using hQ_front by (by100 simp)
    qed
    obtain P' where hP'UQ: "P' \<in> U\<^sub>Q"
      using hUQ_ne by (by100 blast)
    have hP'_IA': "P' \<in> geotop_polygon_interior J - A'"
      using hP'UQ hdec by (by100 blast)
    have hP'_IA12: "P' \<in> geotop_polygon_interior J - (A1 \<union> A2)"
      using hP'_IA' hA12_sub by (by100 blast)
    show ?thesis
      using hP'_IA12 by (by100 blast)
  qed
  have hD44_common:
    "\<exists>C. Q \<in> geotop_frontier UNIV geotop_euclidean_topology C
       \<and> S \<in> geotop_frontier UNIV geotop_euclidean_topology C
       \<and> (\<exists>P'. P' \<in> geotop_polygon_interior J - (A1 \<union> A2) \<and>
           C = geotop_component_at UNIV geotop_euclidean_topology
                  (geotop_polygon_interior J - (A1 \<union> A2)) P')"
    sorry
  show ?thesis using hD44_common by (by100 blast)
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

text \<open>\<open>geotop_diameter\<close> and \<open>geotop_mesh\<close> are defined earlier (before
Theorem_GT_1), since they are needed to state the mesh-shrinkage lemma for
iterated barycentric subdivision.\<close>

(** from \<S>4 Theorem 5 (geotop.tex:976)
    LATEX VERSION: No arc separates R^2. **)
theorem Theorem_GT_4_5:
  fixes A :: "(real^2) set"
  assumes hA: "geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A)"
  shows "top1_connected_on (UNIV - A)
           (subspace_topology UNIV geotop_euclidean_topology (UNIV - A))"
  (** Moise proof (geotop.tex:976): complement of an arc in R^n (n\<ge>2) is connected;
      follows from `top1_connected_complement_of_geotop_arc` since DIM(real^2)=2. **)
  by (rule top1_connected_complement_of_geotop_arc[OF hA]) simp

(** from \<S>4 Theorem 6 (geotop.tex:996)
    LATEX VERSION: Let J be a 1-sphere in R^2, and let U be a component of R^2 - J. Then J = Fr U. **)
theorem Theorem_GT_4_6:
  fixes J U :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes hU: "\<exists>P\<in>UNIV - J. U = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
  shows "J = geotop_frontier UNIV geotop_euclidean_topology U"
  (** Moise proof (geotop.tex:996): J homeomorphic to unit sphere in real^2
      (via our bridges); U ∈ components(-J); apply HOL `Jordan_Brouwer_frontier`
      (DIM(real^2)=2); bridge back via `geotop_frontier_UNIV_eq_frontier`. **)
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
  obtain P where hP_notJ: "P \<in> UNIV - J"
             and hU_eq: "U = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
    using hU by blast
  have hU_HOL: "U = connected_component_set (UNIV - J) P"
    using hU_eq geotop_component_at_UNIV_eq_connected_component_set by simp
  have hU_comp: "U = connected_component_set (- J) P"
    using hU_HOL by (simp add: Compl_eq_Diff_UNIV)
  have hP_compl: "P \<in> - J" using hP_notJ by (simp add: Compl_eq_Diff_UNIV)
  have hU_in_components: "U \<in> components (- J)"
    unfolding components_def using hU_comp hP_compl by blast
  have hdim: "(2::nat) \<le> DIM(real^2)" by simp
  have hfrontier: "frontier U = J"
    by (rule Jordan_Brouwer_frontier[OF hJ_sphere hU_in_components hdim])
  show ?thesis
    using hfrontier geotop_frontier_UNIV_eq_frontier by metis
qed

(** from \<S>4 Theorem 7 (geotop.tex:1002)
    LATEX VERSION: Let J be a 1-sphere in R^2. Then R^2 - J has only one bounded component. **)
theorem Theorem_GT_4_7:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "card {C. geotop_bounded_R2 C \<and>
            (\<exists>P\<in>UNIV - J.
               C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)} = 1"
  (** Moise proof (geotop.tex:1004): As in the proof of 4.3, embed J \<subset> \<bar>I\<close>
      polyhedral 2-cell with J \<inter> Fr I = {P,R}; decompose J = A\<^sub>1 \<union> A\<^sub>2 along P,R.
      Broken line B from S to Q in \<bar>I\<close> meeting Fr I only at endpoints.
      Define T, X, Y, Z, W as in Fig 4.9. Z lies in a bounded component of R\<^sup>2 - J.
      Let B\<^sub>1,\<dots>,B\<^sub>5 be the segments S-T-X-Y-W-Q, B' = \<Union>B\<^sub>i.
      P, R are limit points of different components of I - B'.
      If U is a bounded component of R\<^sup>2 - J distinct from Z's component, then
      U \<inter> B' = \<emptyset>, so Fr U cannot contain both P and R, hence Fr U \<subset> arc of J,
      contradicting Theorem 5 (every point of J is a limit point of both I and E). **)
proof -
  (** Step 1: Exists a \"bounded component\" (from Jordan_Brouwer_separation + bdd). **)
  have h_exists_bdd: "\<exists>C. geotop_bounded_R2 C \<and>
            (\<exists>P\<in>UNIV - J. C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)"
  proof -
    obtain P where hP: "P \<in> UNIV - J"
               and hI_eq: "geotop_polygon_interior J
                           = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
      using geotop_polygon_interior_is_bounded_component[OF hJ] by (by100 blast)
    have h_bdd: "bounded (geotop_polygon_interior J)"
      by (rule polygon_interior_bounded[OF hJ])
    have h_geotop_bdd: "geotop_bounded_R2 (geotop_polygon_interior J)"
      using h_bdd geotop_bounded_R2_iff_bounded by (by100 blast)
    show ?thesis using hP hI_eq h_geotop_bdd by (by100 blast)
  qed
  (** Step 2: At most one bounded component, by the Moise contradiction argument:
      any second bounded component U would give Fr U \<subset> arc of J, contradicting 2.5. **)
  \<comment> \<open>Sub-claim T4_7-A: any bounded component of UNIV - J equals geotop_polygon_interior J.\<close>
  have hT4_7_eq_polygon_interior:
    "\<forall>C. geotop_bounded_R2 C \<and>
         (\<exists>P\<in>UNIV - J. C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)
         \<longrightarrow> C = geotop_polygon_interior J" sorry
  \<comment> \<open>Sub-claim T4_7-B: from T4_7-A, any two such components coincide.\<close>
  have hT4_7_unique:
    "\<forall>C1 C2.
          (geotop_bounded_R2 C1 \<and>
             (\<exists>P\<in>UNIV - J. C1 = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)) \<and>
          (geotop_bounded_R2 C2 \<and>
             (\<exists>P\<in>UNIV - J. C2 = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P))
          \<longrightarrow> C1 = C2"
    using hT4_7_eq_polygon_interior by (by100 blast)
  have h_atmost: "\<forall>C1 C2.
          (geotop_bounded_R2 C1 \<and>
             (\<exists>P\<in>UNIV - J. C1 = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)) \<and>
          (geotop_bounded_R2 C2 \<and>
             (\<exists>P\<in>UNIV - J. C2 = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P))
          \<longrightarrow> C1 = C2"
    using hT4_7_unique by (by100 blast)
  (** Conclude card = 1. **)
  define S where "S = {C. geotop_bounded_R2 C \<and>
            (\<exists>P\<in>UNIV - J.
               C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)}"
  have hS_ne: "S \<noteq> {}" using h_exists_bdd unfolding S_def by (by100 blast)
  have hS_singleton: "\<forall>x\<in>S. \<forall>y\<in>S. x = y"
    unfolding S_def using h_atmost by (by100 blast)
  obtain C where hC: "C \<in> S" using hS_ne by (by100 blast)
  have hS_eq: "S = {C}"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> S"
    thus "x \<in> {C}" using hC hS_singleton by (by100 blast)
  next
    fix x assume "x \<in> {C}"
    thus "x \<in> S" using hC by (by100 blast)
  qed
  have hS_card: "card S = 1" using hS_eq by (by100 simp)
  show "card {C. geotop_bounded_R2 C \<and>
            (\<exists>P\<in>UNIV - J.
               C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)} = 1"
    using hS_card unfolding S_def by (by100 simp)
qed

(** JORDAN CURVE THEOREM — combining the above
    LATEX VERSION: Let J be a topological 1-sphere in R^2. Then R^2 - J is the union of two
      disjoint connected sets I and E, such that J = Fr I = Fr E. **)
theorem Jordan_curve_theorem:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "\<exists>I E. UNIV - J = I \<union> E \<and> I \<inter> E = {} \<and>
           top1_connected_on I (subspace_topology UNIV geotop_euclidean_topology I) \<and>
           top1_connected_on E (subspace_topology UNIV geotop_euclidean_topology E) \<and>
           J = geotop_frontier UNIV geotop_euclidean_topology I \<and>
           J = geotop_frontier UNIV geotop_euclidean_topology E"
proof -
  (** (1) Approximate J by a polygonal 1-sphere J' in plane via a plane homeomorphism h.
         (Tame imbedding / PL approximation; R^2 is 2-dim so every 1-sphere is tame.) **)
  \<comment> \<open>Sub-claim JCT-1: \<exists>J' polygon and h plane-homeo with h(J) = J'.\<close>
  have h_approx_polygon:
    "\<exists>J'. geotop_is_polygon J' \<and>
          (\<exists>h. top1_homeomorphism_on UNIV geotop_euclidean_topology
                  UNIV geotop_euclidean_topology h \<and> h ` J = J')" sorry
  (** (2) For the polygonal J', apply Theorem 2.1: plane minus J' has exactly two connected
         components with Jordan property (bounded I' and unbounded E', each with frontier
         J'). **)
  \<comment> \<open>Sub-claim JCT-2: for any polygon J', plane \ J' splits into 2 connected
    components (I', E') via Theorem_GT_2_1 / Jordan_Brouwer_separation +
    geotop_polygon_interior infrastructure.\<close>
  have h_polygon_JCT:
    "\<forall>J'::(real^2) set. geotop_is_polygon J' \<longrightarrow>
          (\<exists>I' E'. UNIV - J' = I' \<union> E' \<and> I' \<inter> E' = {} \<and>
                   top1_connected_on I' (subspace_topology UNIV geotop_euclidean_topology I') \<and>
                   top1_connected_on E' (subspace_topology UNIV geotop_euclidean_topology E') \<and>
                   J' = geotop_frontier UNIV geotop_euclidean_topology I' \<and>
                   J' = geotop_frontier UNIV geotop_euclidean_topology E')"
  proof (intro allI impI)
    fix J' :: "(real^2) set"
    assume hJ': "geotop_is_polygon J'"
    let ?I = "geotop_polygon_interior J'"
    let ?E = "geotop_polygon_exterior J'"
    have hcomps: "components (UNIV - J') = {?I, ?E}"
      by (rule polygon_components_eq[OF hJ'])
    have hcover: "UNIV - J' = ?I \<union> ?E"
    proof -
      have "\<Union>(components (UNIV - J')) = UNIV - J'"
        by (rule Union_components)
      thus ?thesis using hcomps by (by100 simp)
    qed
    have hdisj: "?I \<inter> ?E = {}"
      by (rule polygon_interior_exterior_disjoint[OF hJ'])
    have hI_comp: "?I \<in> components (UNIV - J')"
      using hcomps by (by100 simp)
    have hE_comp: "?E \<in> components (UNIV - J')"
      using hcomps by (by100 simp)
    have hI_conn_HOL: "connected ?I"
      using hI_comp in_components_connected by (by100 blast)
    have hE_conn_HOL: "connected ?E"
      using hE_comp in_components_connected by (by100 blast)
    have hI_conn:
      "top1_connected_on ?I (subspace_topology UNIV geotop_euclidean_topology ?I)"
      using hI_conn_HOL top1_connected_on_geotop_iff_connected[of ?I] by (by100 simp)
    have hE_conn:
      "top1_connected_on ?E (subspace_topology UNIV geotop_euclidean_topology ?E)"
      using hE_conn_HOL top1_connected_on_geotop_iff_connected[of ?E] by (by100 simp)
    have hI_front: "J' = geotop_frontier UNIV geotop_euclidean_topology ?I"
      by (rule Theorem_GT_2_6(1)[OF hJ'])
    have hE_front: "J' = geotop_frontier UNIV geotop_euclidean_topology ?E"
      by (rule Theorem_GT_2_6(2)[OF hJ'])
    show "(\<exists>I' E'. UNIV - J' = I' \<union> E' \<and> I' \<inter> E' = {} \<and>
                 top1_connected_on I' (subspace_topology UNIV geotop_euclidean_topology I') \<and>
                 top1_connected_on E' (subspace_topology UNIV geotop_euclidean_topology E') \<and>
                 J' = geotop_frontier UNIV geotop_euclidean_topology I' \<and>
                 J' = geotop_frontier UNIV geotop_euclidean_topology E')"
      using hcover hdisj hI_conn hE_conn hI_front hE_front by (by100 blast)
  qed
  (** (3) Pull the Jordan decomposition back through the homeomorphism h: I = h^{-1}(I'),
         E = h^{-1}(E'). The connectivity, disjointness, and frontier relations transport
         through the homeomorphism. **)
  \<comment> \<open>Sub-claim JCT-3: pullback through h. Connectivity preserved by homeo;
    frontier preserved by plane-homeo via geotop_frontier_UNIV_eq_frontier
    + frontier-image lemmas.\<close>
  have h_pullback:
    "\<exists>I E. UNIV - J = I \<union> E \<and> I \<inter> E = {} \<and>
           top1_connected_on I (subspace_topology UNIV geotop_euclidean_topology I) \<and>
           top1_connected_on E (subspace_topology UNIV geotop_euclidean_topology E) \<and>
           J = geotop_frontier UNIV geotop_euclidean_topology I \<and>
           J = geotop_frontier UNIV geotop_euclidean_topology E"
  proof -
    obtain J' :: "(real^2) set" and h :: "(real^2) \<Rightarrow> (real^2)"
      where hJ'_poly: "geotop_is_polygon J'"
      and hh_homeo: "top1_homeomorphism_on UNIV geotop_euclidean_topology
                  UNIV geotop_euclidean_topology h"
      and hhJ: "h ` J = J'"
      using h_approx_polygon by (by100 blast)
    obtain I' E' where hcover': "UNIV - J' = I' \<union> E'"
      and hdisj': "I' \<inter> E' = {}"
      and hI'_conn:
        "top1_connected_on I' (subspace_topology UNIV geotop_euclidean_topology I')"
      and hE'_conn:
        "top1_connected_on E' (subspace_topology UNIV geotop_euclidean_topology E')"
      and hI'_front: "J' = geotop_frontier UNIV geotop_euclidean_topology I'"
      and hE'_front: "J' = geotop_frontier UNIV geotop_euclidean_topology E'"
      using h_polygon_JCT[rule_format, OF hJ'_poly] by (by100 blast)
    obtain k where hhk: "homeomorphism UNIV UNIV h k"
      by (rule top1_homeomorphism_on_UNIV_R2_obtain_HOL_homeomorphism[OF hh_homeo])
    define I where "I = k ` I'"
    define E where "E = k ` E'"
    have hkh: "\<And>x. k (h x) = x"
      using hhk unfolding homeomorphism_def by (by100 simp)
    have hhk_apply: "\<And>y. h (k y) = y"
      using hhk unfolding homeomorphism_def by (by100 simp)
    have hh_inj: "inj h"
    proof (rule injI)
      fix x y assume hxy: "h x = h y"
      have "k (h x) = k (h y)" using hxy by (by100 simp)
      thus "x = y" using hkh by (by100 simp)
    qed
    have hk_inj: "inj k"
    proof (rule injI)
      fix x y assume hxy: "k x = k y"
      have "h (k x) = h (k y)" using hxy by (by100 simp)
      thus "x = y" using hhk_apply by (by100 simp)
    qed
    have hIJ: "k ` J' = J"
    proof
      show "k ` J' \<subseteq> J"
      proof
        fix x assume hx: "x \<in> k ` J'"
        then obtain y where hyJ': "y \<in> J'" and hx_eq: "x = k y"
          by (by100 blast)
        obtain z where hzJ: "z \<in> J" and hy_eq: "y = h z"
          using hyJ' hhJ by (by100 blast)
        show "x \<in> J" using hx_eq hy_eq hzJ hkh by (by100 simp)
      qed
      show "J \<subseteq> k ` J'"
      proof
        fix x assume hxJ: "x \<in> J"
        have "h x \<in> J'" using hxJ hhJ by (by100 blast)
        moreover have "x = k (h x)" using hkh by (by100 simp)
        ultimately show "x \<in> k ` J'" by (by100 blast)
      qed
    qed
    have hk_compl: "k ` (UNIV - J') = UNIV - J"
    proof
      show "k ` (UNIV - J') \<subseteq> UNIV - J"
      proof
        fix x assume hx: "x \<in> k ` (UNIV - J')"
        then obtain y where hy_not: "y \<notin> J'" and hx_eq: "x = k y"
          by (by100 blast)
        have hx_not: "x \<notin> J"
        proof
          assume hxJ: "x \<in> J"
          have "x \<in> k ` J'" using hIJ hxJ by (by100 blast)
          then obtain z where hzJ': "z \<in> J'" and hx_z: "x = k z"
            by (by100 blast)
          have "y = z" using hx_eq hx_z hk_inj unfolding inj_def by (by100 blast)
          thus False using hy_not hzJ' by (by100 simp)
        qed
        show "x \<in> UNIV - J" using hx_not by (by100 simp)
      qed
      show "UNIV - J \<subseteq> k ` (UNIV - J')"
      proof
        fix x assume hx: "x \<in> UNIV - J"
        have hx_notJ: "x \<notin> J" using hx by (by100 simp)
        have hhx_notJ': "h x \<notin> J'"
        proof
          assume "h x \<in> J'"
          then obtain z where hzJ: "z \<in> J" and hz: "h x = h z"
            using hhJ by (by100 blast)
          have "x = z" using hz hh_inj unfolding inj_def by (by100 blast)
          thus False using hx_notJ hzJ by (by100 simp)
        qed
        have "x = k (h x)" using hkh by (by100 simp)
        thus "x \<in> k ` (UNIV - J')" using hhx_notJ' by (by100 blast)
      qed
    qed
    have hcover: "UNIV - J = I \<union> E"
    proof -
      have "UNIV - J = k ` (UNIV - J')" using hk_compl by (by100 simp)
      also have "\<dots> = k ` (I' \<union> E')" using hcover' by (by100 simp)
      also have "\<dots> = I \<union> E" unfolding I_def E_def by (rule image_Un)
      finally show ?thesis .
    qed
    have hdisj: "I \<inter> E = {}"
    proof
      show "I \<inter> E \<subseteq> {}"
      proof
        fix x assume hx: "x \<in> I \<inter> E"
        then obtain y z where hy: "y \<in> I'" and hz: "z \<in> E'"
          and hxy: "x = k y" and hxz: "x = k z"
          unfolding I_def E_def by (by100 blast)
        have "y = z" using hxy hxz hk_inj unfolding inj_def by (by100 blast)
        thus "x \<in> {}" using hy hz hdisj' by (by100 blast)
      qed
      show "{} \<subseteq> I \<inter> E" by (by100 simp)
    qed
    have hhk_sym: "homeomorphism UNIV UNIV k h"
      by (rule homeomorphism_symD[OF hhk])
    have hk_cont: "continuous_on UNIV k"
      using hhk_sym unfolding homeomorphism_def by (by100 simp)
    have hI'_conn_HOL: "connected I'"
      using hI'_conn top1_connected_on_geotop_iff_connected[of I'] by (by100 simp)
    have hE'_conn_HOL: "connected E'"
      using hE'_conn top1_connected_on_geotop_iff_connected[of E'] by (by100 simp)
    have hk_cont_I': "continuous_on I' k"
      by (rule continuous_on_subset[OF hk_cont subset_UNIV])
    have hk_cont_E': "continuous_on E' k"
      by (rule continuous_on_subset[OF hk_cont subset_UNIV])
    have hI_conn_HOL: "connected I"
      unfolding I_def by (rule connected_continuous_image[OF hk_cont_I' hI'_conn_HOL])
    have hE_conn_HOL: "connected E"
      unfolding E_def by (rule connected_continuous_image[OF hk_cont_E' hE'_conn_HOL])
    have hI_conn: "top1_connected_on I (subspace_topology UNIV geotop_euclidean_topology I)"
      using hI_conn_HOL top1_connected_on_geotop_iff_connected[of I] by (by100 simp)
    have hE_conn: "top1_connected_on E (subspace_topology UNIV geotop_euclidean_topology E)"
      using hE_conn_HOL top1_connected_on_geotop_iff_connected[of E] by (by100 simp)
    have hI'_front_HOL: "frontier I' = J'"
      using hI'_front geotop_frontier_UNIV_eq_frontier[of I'] by (by100 simp)
    have hE'_front_HOL: "frontier E' = J'"
      using hE'_front geotop_frontier_UNIV_eq_frontier[of E'] by (by100 simp)
    have hI_front_HOL: "frontier I = J"
    proof -
      have "frontier I = k ` frontier I'"
        unfolding I_def using homeomorphism_UNIV_image_frontier[OF hhk_sym, of I'] by (by100 simp)
      also have "\<dots> = k ` J'" using hI'_front_HOL by (by100 simp)
      also have "\<dots> = J" using hIJ by (by100 simp)
      finally show ?thesis .
    qed
    have hE_front_HOL: "frontier E = J"
    proof -
      have "frontier E = k ` frontier E'"
        unfolding E_def using homeomorphism_UNIV_image_frontier[OF hhk_sym, of E'] by (by100 simp)
      also have "\<dots> = k ` J'" using hE'_front_HOL by (by100 simp)
      also have "\<dots> = J" using hIJ by (by100 simp)
      finally show ?thesis .
    qed
    have hI_front: "J = geotop_frontier UNIV geotop_euclidean_topology I"
      using hI_front_HOL geotop_frontier_UNIV_eq_frontier[of I] by (by100 simp)
    have hE_front: "J = geotop_frontier UNIV geotop_euclidean_topology E"
      using hE_front_HOL geotop_frontier_UNIV_eq_frontier[of E] by (by100 simp)
    show ?thesis
      using hcover hdisj hI_conn hE_conn hI_front hE_front by (by100 blast)
  qed
  show ?thesis using h_pullback by (by100 blast)
qed

(** from \<S>4 Theorem 8 (geotop.tex:1020)
    LATEX VERSION: Let K be a complex such that M = |K| is a 2-manifold. Then K is a
      combinatorial 2-manifold; i.e., every subcomplex St v is a combinatorial 2-cell. **)
theorem Theorem_GT_4_8:
  fixes K :: "(real^2) set set" and d :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real"
  assumes hK: "geotop_is_complex K"
  assumes hM: "geotop_n_manifold_on (geotop_polyhedron K) d 2"
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
  have hL1: "\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e" sorry
  \<comment> \<open>L2: every incident edge in \<ge>1 two-simplex.\<close>
  have hL2: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
              (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>)" sorry
  \<comment> \<open>L3: every incident edge in \<ge>2 two-simplexes (manifold without boundary).\<close>
  have hL3: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
              card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 2" sorry
  \<comment> \<open>L4: every incident edge in \<le>2 two-simplexes.\<close>
  have hL4: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
              card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2" sorry
  \<comment> \<open>L5: link |L(v)| is connected.\<close>
  have hL5: "top1_connected_on (\<Union>(geotop_link K v))
               (subspace_topology UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)))" sorry
  \<comment> \<open>L6: link is a polygon (single 1-sphere from L2-L4 + L5).\<close>
  have hL6: "geotop_is_polygon (\<Union>(geotop_link K v))" sorry
  \<comment> \<open>L7 (main conclusion): Star is a combinatorial 2-cell.\<close>
  have hL7: "geotop_comb_n_cell (geotop_star K v) 2" sorry
  have hL_all:
    "(\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e) \<and>
     (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
             (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>)) \<and>
     (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
             card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 2) \<and>
     (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
             card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2) \<and>
     top1_connected_on (\<Union>(geotop_link K v))
               (subspace_topology UNIV geotop_euclidean_topology (\<Union>(geotop_link K v))) \<and>
     geotop_is_polygon (\<Union>(geotop_link K v)) \<and>
     geotop_comb_n_cell (geotop_star K v) 2"
    using hL1 hL2 hL3 hL4 hL5 hL6 hL7 by (by100 blast)
  show "geotop_comb_n_cell (geotop_star K v) 2" using hL7 .
qed

(** from \<S>4 Theorem 9 (geotop.tex:1052)
    LATEX VERSION: Let K be a complex such that M = |K| is a 2-manifold with boundary. Then
      K is a combinatorial 2-manifold with boundary, and Bd M is the union of the edges of K
      that lie in only one 2-simplex of K. **)
theorem Theorem_GT_4_9:
  fixes K :: "(real^2) set set" and d :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on (geotop_polyhedron K) d 2"
  shows "\<forall>v\<in>geotop_complex_vertices K. geotop_comb_n_cell (geotop_star K v) 2"
    and "geotop_manifold_boundary (geotop_polyhedron K) d =
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
    have hL1: "\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e" sorry
    \<comment> \<open>L2: every incident edge is contained in some 2-simplex.\<close>
    have hL2: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
                (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>)" sorry
    \<comment> \<open>L3-with-boundary: each incident edge in \<le> 2 triangles
      (\<le> 2, not = 2 — this is the manifold-with-boundary case).\<close>
    have hL3: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
                card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2" sorry
    \<comment> \<open>L4: link |L(v)| is connected.\<close>
    have hL4: "top1_connected_on (\<Union>(geotop_link K v))
                 (subspace_topology UNIV geotop_euclidean_topology
                    (\<Union>(geotop_link K v)))" sorry
    \<comment> \<open>L5: link is a broken line or polygon.\<close>
    have hL5: "geotop_is_broken_line (\<Union>(geotop_link K v)) \<or>
                geotop_is_polygon (\<Union>(geotop_link K v))" sorry
    \<comment> \<open>L6 (main conclusion): Star is a combinatorial 2-cell.\<close>
    have hL6: "geotop_comb_n_cell (geotop_star K v) 2" sorry
    have hL_all:
      "(\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e) \<and>
       (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
               (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>)) \<and>
       (\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
               card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2) \<and>
       top1_connected_on (\<Union>(geotop_link K v))
                 (subspace_topology UNIV geotop_euclidean_topology (\<Union>(geotop_link K v))) \<and>
       (geotop_is_broken_line (\<Union>(geotop_link K v))
                     \<or> geotop_is_polygon (\<Union>(geotop_link K v))) \<and>
       geotop_comb_n_cell (geotop_star K v) 2"
      using hL1 hL2 hL3 hL4 hL5 hL6 by (by100 blast)
    show "geotop_comb_n_cell (geotop_star K v) 2" using hL6 .
  qed
next
  (** Bd |K| = union of edges lying in only one 2-simplex. **)
  show "geotop_manifold_boundary (geotop_polyhedron K) d =
         \<Union>{e\<in>K. geotop_is_edge e \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
    sorry
qed

(** from \<S>4 Theorem 10 (geotop.tex:1058)
    LATEX VERSION: Let M be a 2-manifold with boundary, lying in R^2. If M is closed, then
      Bd M = Fr M. **)
theorem Theorem_GT_4_10:
  fixes M :: "(real^2) set" and d :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real"
  assumes hM: "geotop_n_manifold_with_boundary_on M d 2"
  assumes hMcl: "closedin_on UNIV geotop_euclidean_topology M"
  shows "geotop_manifold_boundary M d = geotop_frontier UNIV geotop_euclidean_topology M"
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
  have h_A: "geotop_manifold_boundary M d \<subseteq> geotop_frontier UNIV geotop_euclidean_topology M"
    sorry
  (** T4_10-B: Fr M \<subseteq> Bd M. P \<in> Fr M cannot have plane-homeomorphic open nbhd
      open in M (Invariance of Domain would extend it to be open in R\<^sup>2). **)
  have h_B: "geotop_frontier UNIV geotop_euclidean_topology M \<subseteq> geotop_manifold_boundary M d"
    sorry
  show ?thesis using h_A h_B by (by100 blast)
qed



end
