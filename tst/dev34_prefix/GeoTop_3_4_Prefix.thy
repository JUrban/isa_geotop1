theory GeoTop_3_4_Prefix
  imports "GeoTopPre3Dirty.GeoTop"
begin

section \<open>\<S>3 The Schönflies theorem for polygons in $\mathbf{R}^2$\<close>

lemma geotop_HOL_homeomorphism_imp_top1_homeomorphism_on:
  fixes X Y :: "'a::real_normed_vector set"
  assumes hfg: "homeomorphism X Y f g"
  shows "top1_homeomorphism_on X
              (subspace_topology UNIV geotop_euclidean_topology X)
              Y (subspace_topology UNIV geotop_euclidean_topology Y) f"
proof -
  have hf_cont_HOL: "continuous_on X f"
    using hfg unfolding homeomorphism_def by (by100 blast)
  have hg_cont_HOL: "continuous_on Y g"
    using hfg unfolding homeomorphism_def by (by100 blast)
  have hf_img_eq: "f ` X = Y"
    using hfg unfolding homeomorphism_def by (by100 blast)
  have hg_img_eq: "g ` Y = X"
    using hfg unfolding homeomorphism_def by (by100 blast)
  have hfg_id: "\<forall>x\<in>X. g (f x) = x"
    using hfg unfolding homeomorphism_def by (by100 blast)
  have hgf_id: "\<forall>y\<in>Y. f (g y) = y"
    using hfg unfolding homeomorphism_def by (by100 blast)
  have hf_img: "f ` X \<subseteq> Y" using hf_img_eq by (by100 simp)
  have hg_img: "g ` Y \<subseteq> X" using hg_img_eq by (by100 simp)
  have hf_top1: "top1_continuous_map_on X
                    (subspace_topology UNIV geotop_euclidean_topology X)
                    Y (subspace_topology UNIV geotop_euclidean_topology Y) f"
    by (rule geotop_continuous_on_imp_top1_continuous_map_on[OF hf_cont_HOL hf_img])
  have hg_top1: "top1_continuous_map_on Y
                    (subspace_topology UNIV geotop_euclidean_topology Y)
                    X (subspace_topology UNIV geotop_euclidean_topology X) g"
    by (rule geotop_continuous_on_imp_top1_continuous_map_on[OF hg_cont_HOL hg_img])
  have hf_bij: "bij_betw f X Y"
    by (rule bij_betw_byWitness[where f' = g, OF hfg_id hgf_id hf_img hg_img])
  have hf_inj: "inj_on f X" using hf_bij unfolding bij_betw_def by (by100 blast)
  have hg_eq_inv: "\<forall>y\<in>Y. g y = inv_into X f y"
  proof
    fix y assume hy: "y \<in> Y"
    have hgy_in_X: "g y \<in> X" using hg_img_eq hy by (by100 blast)
    have hfgy: "f (g y) = y" using hgf_id hy by (by100 blast)
    have "inv_into X f y = g y" by (rule inv_into_f_eq[OF hf_inj hgy_in_X hfgy])
    thus "g y = inv_into X f y" by (by100 simp)
  qed
  have h_invf_top1: "top1_continuous_map_on Y
                    (subspace_topology UNIV geotop_euclidean_topology Y)
                    X (subspace_topology UNIV geotop_euclidean_topology X)
                    (inv_into X f)"
    using hg_top1 top1_continuous_map_on_cong[OF hg_eq_inv] by (by100 blast)
  have h_Teucl: "is_topology_on (UNIV::'a set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have hTX: "is_topology_on X (subspace_topology UNIV geotop_euclidean_topology X)"
    by (rule subspace_topology_is_topology_on[OF h_Teucl subset_UNIV])
  have hTY: "is_topology_on Y (subspace_topology UNIV geotop_euclidean_topology Y)"
    by (rule subspace_topology_is_topology_on[OF h_Teucl subset_UNIV])
  show ?thesis
    unfolding top1_homeomorphism_on_def
    using hTX hTY hf_bij hf_top1 h_invf_top1 by (by100 blast)
qed

lemma geotop_affine_linear_homeomorphism_UNIV:
  fixes A :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes hlin: "linear A" and hinj: "inj A"
  shows "top1_homeomorphism_on UNIV geotop_euclidean_topology
            UNIV geotop_euclidean_topology (\<lambda>x. b + A (x - a))"
proof -
  obtain Ainv where hA_img_homeo: "homeomorphism (A ` UNIV) UNIV Ainv A"
    by (rule linear_homeomorphism_image[OF hlin hinj])
  have hA_surj: "surj A"
    by (rule linear_inj_imp_surj[OF hlin hinj])
  have hA_image: "A ` UNIV = UNIV"
    using hA_surj by (by100 blast)
  have hA_homeo: "homeomorphism UNIV UNIV A Ainv"
    using homeomorphism_symD[OF hA_img_homeo] hA_image by (by100 simp)
  have hminus: "homeomorphism UNIV UNIV ((+) (- a)) ((+) a)"
  proof -
    have "homeomorphism ((+) a ` UNIV) UNIV ((+) (- a)) ((+) a)"
      by (rule homeomorphism_translation[of a UNIV])
    thus ?thesis by (by100 simp)
  qed
  have hplus: "homeomorphism UNIV UNIV ((+) b) ((+) (- b))"
  proof -
    have hb: "homeomorphism ((+) b ` UNIV) UNIV ((+) (- b)) ((+) b)"
      by (rule homeomorphism_translation[of b UNIV])
    have "homeomorphism UNIV ((+) b ` UNIV) ((+) b) ((+) (- b))"
      by (rule homeomorphism_symD[OF hb])
    thus ?thesis by (by100 simp)
  qed
  have hA_minus: "homeomorphism UNIV UNIV (A \<circ> ((+) (- a))) (((+) a) \<circ> Ainv)"
    by (rule Elementary_Topology.homeomorphism_compose[OF hminus hA_homeo])
  have hcomp:
    "homeomorphism UNIV UNIV (((+) b) \<circ> (A \<circ> ((+) (- a))))
       ((((+) a) \<circ> Ainv) \<circ> ((+) (- b)))"
    by (rule Elementary_Topology.homeomorphism_compose[OF hA_minus hplus])
  have htarget:
    "homeomorphism UNIV UNIV (\<lambda>x. b + A (x - a))
       ((((+) a) \<circ> Ainv) \<circ> ((+) (- b)))"
    using hcomp by (simp add: o_def algebra_simps)
  have htop1:
    "top1_homeomorphism_on UNIV
       (subspace_topology UNIV geotop_euclidean_topology UNIV)
       UNIV (subspace_topology UNIV geotop_euclidean_topology UNIV)
       (\<lambda>x. b + A (x - a))"
    by (rule geotop_HOL_homeomorphism_imp_top1_homeomorphism_on[OF htarget])
  show ?thesis
    using htop1 by (simp add: subspace_topology_UNIV_UNIV)
qed

lemma geotop_UNIV_homeomorphism_restrict:
  fixes h :: "'a::real_normed_vector \<Rightarrow> 'a"
  assumes hhomeo: "top1_homeomorphism_on UNIV geotop_euclidean_topology
                    UNIV geotop_euclidean_topology h"
  assumes hXY: "h ` X = Y"
  shows "top1_homeomorphism_on X
          (subspace_topology UNIV geotop_euclidean_topology X)
          Y (subspace_topology UNIV geotop_euclidean_topology Y) h"
proof -
  obtain k where hk: "homeomorphism UNIV UNIV h k"
    by (rule top1_homeomorphism_on_UNIV_obtain_HOL_homeomorphism[OF hhomeo])
  have hsub: "homeomorphism X Y h k"
    by (rule homeomorphism_of_subsets[OF hk subset_UNIV subset_UNIV hXY])
  show ?thesis
    by (rule geotop_HOL_homeomorphism_imp_top1_homeomorphism_on[OF hsub])
qed

lemma geotop_linear_on_eq_vertices:
  fixes f g :: "'a::euclidean_space \<Rightarrow> 'b::real_vector"
  assumes hV: "geotop_simplex_vertices \<sigma> V"
  assumes hf: "geotop_linear_on \<sigma> f"
  assumes hg: "geotop_linear_on \<sigma> g"
  assumes hfgV: "\<forall>v\<in>V. f v = g v"
  shows "\<forall>x\<in>\<sigma>. f x = g x"
proof
  fix x assume hx\<sigma>: "x \<in> \<sigma>"
  have hV_fin: "finite V"
    using hV unfolding geotop_simplex_vertices_def by (by100 blast)
  have h\<sigma>_HOL: "\<sigma> = convex hull V"
  proof -
    have "\<sigma> = geotop_convex_hull V"
      using hV unfolding geotop_simplex_vertices_def by (by100 blast)
    thus ?thesis using geotop_convex_hull_eq_HOL by (by100 simp)
  qed
  obtain Vf where hVf: "geotop_simplex_vertices \<sigma> Vf"
      and hf_prop: "\<forall>\<alpha>. (\<forall>v\<in>Vf. 0 \<le> \<alpha> v) \<and> sum \<alpha> Vf = 1 \<longrightarrow>
          f (\<Sum>v\<in>Vf. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>Vf. \<alpha> v *\<^sub>R f v)"
    using hf unfolding geotop_linear_on_def by (by100 blast)
  obtain Vg where hVg: "geotop_simplex_vertices \<sigma> Vg"
      and hg_prop: "\<forall>\<alpha>. (\<forall>v\<in>Vg. 0 \<le> \<alpha> v) \<and> sum \<alpha> Vg = 1 \<longrightarrow>
          g (\<Sum>v\<in>Vg. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>Vg. \<alpha> v *\<^sub>R g v)"
    using hg unfolding geotop_linear_on_def by (by100 blast)
  have hVf_eq: "Vf = V"
    using geotop_simplex_vertices_unique[OF hVf hV] .
  have hVg_eq: "Vg = V"
    using geotop_simplex_vertices_unique[OF hVg hV] .
  have hx_hull: "x \<in> convex hull V"
    using hx\<sigma> h\<sigma>_HOL by (by100 simp)
  have h_hull_char:
    "convex hull V =
      {y. \<exists>\<alpha>::'a \<Rightarrow> real. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1 \<and>
            (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = y}"
    by (rule convex_hull_finite[OF hV_fin])
  obtain \<alpha> :: "'a \<Rightarrow> real"
    where h\<alpha>_nn: "\<forall>v\<in>V. 0 \<le> \<alpha> v"
      and h\<alpha>_sum: "sum \<alpha> V = 1"
      and h\<alpha>_x: "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = x"
    using hx_hull h_hull_char by (by100 blast)
  have hf_x: "f x = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
  proof -
    have "f (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
      using hf_prop hVf_eq h\<alpha>_nn h\<alpha>_sum by (by100 blast)
    thus ?thesis using h\<alpha>_x by (by100 simp)
  qed
  have hg_x: "g x = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R g v)"
  proof -
    have "g (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R g v)"
      using hg_prop hVg_eq h\<alpha>_nn h\<alpha>_sum by (by100 blast)
    thus ?thesis using h\<alpha>_x by (by100 simp)
  qed
  have hsum_eq: "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R g v)"
    using hfgV by (by100 simp)
  show "f x = g x"
    using hf_x hg_x hsum_eq by (by100 simp)
qed

lemma geotop_simplex_vertex_bijection_affine_extension:
  fixes V W :: "'a::euclidean_space set" and \<sigma> \<tau> :: "'a set"
  assumes hV: "geotop_simplex_vertices \<sigma> V"
  assumes hW: "geotop_simplex_vertices \<tau> W"
  assumes h\<phi>_bij: "bij_betw \<phi> V W"
  shows "\<exists>g. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology g
          \<and> g ` \<sigma> = \<tau>
          \<and> geotop_simplicial_on \<sigma> g \<tau>
          \<and> (\<forall>v\<in>V. g v = \<phi> v)"
proof -
  have hV_fin: "finite V"
    using hV unfolding geotop_simplex_vertices_def by (by100 blast)
  have hW_fin: "finite W"
    using hW unfolding geotop_simplex_vertices_def by (by100 blast)
  have h\<sigma>_HOL: "\<sigma> = convex hull V"
  proof -
    have "\<sigma> = geotop_convex_hull V"
      using hV unfolding geotop_simplex_vertices_def by (by100 blast)
    thus ?thesis using geotop_convex_hull_eq_HOL by (by100 simp)
  qed
  have h\<tau>_HOL: "\<tau> = convex hull W"
  proof -
    have "\<tau> = geotop_convex_hull W"
      using hW unfolding geotop_simplex_vertices_def by (by100 blast)
    thus ?thesis using geotop_convex_hull_eq_HOL by (by100 simp)
  qed
  have hV_ai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF hV])
  have hW_ai: "\<not> affine_dependent W"
    by (rule geotop_general_position_imp_aff_indep[OF hW])
  have hV_ne: "V \<noteq> {}"
  proof -
    obtain n m where hcard: "card V = n + 1"
      using hV unfolding geotop_simplex_vertices_def by (by100 blast)
    have hcard_pos: "card V > 0" using hcard by (by100 simp)
    have hiff: "(0 < card V) = (V \<noteq> {} \<and> finite V)"
      by (rule card_gt_0_iff)
    show ?thesis using hiff hcard_pos hV_fin by (by100 blast)
  qed
  obtain a where haV: "a \<in> V"
    using hV_ne by (by100 blast)
  define b where "b = \<phi> a"
  have hbW: "b \<in> W"
    using h\<phi>_bij haV unfolding b_def bij_betw_def by (by100 blast)
  define B where "B = ((+) (- a)) ` (V - {a})"
  define F where "F x = \<phi> (a + x) - b" for x
  have h\<phi>_inj: "inj_on \<phi> V"
    using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
  have h\<phi>_image: "\<phi> ` V = W"
    using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
  have h\<phi>_minus: "\<phi> ` (V - {a}) = W - {b}"
  proof
    show "\<phi> ` (V - {a}) \<subseteq> W - {b}"
    proof
      fix y assume hy: "y \<in> \<phi> ` (V - {a})"
      obtain v where hvV: "v \<in> V" and hva: "v \<noteq> a" and hy_eq: "y = \<phi> v"
        using hy by (by100 blast)
      have hyW: "y \<in> W" using hvV hy_eq h\<phi>_image by (by100 blast)
      have hy_ne_b: "y \<noteq> b"
      proof
        assume "y = b"
        hence "\<phi> v = \<phi> a" using hy_eq b_def by (by100 simp)
        hence "v = a"
          using h\<phi>_inj hvV haV unfolding inj_on_def by (by100 blast)
        thus False using hva by (by100 simp)
      qed
      show "y \<in> W - {b}" using hyW hy_ne_b by (by100 blast)
    qed
    show "W - {b} \<subseteq> \<phi> ` (V - {a})"
    proof
      fix y assume hy: "y \<in> W - {b}"
      have hyW: "y \<in> W" and hyb: "y \<noteq> b" using hy by (by100 blast)+
      obtain v where hvV: "v \<in> V" and hy_eq: "y = \<phi> v"
        using hyW h\<phi>_image by (by100 blast)
      have hva: "v \<noteq> a"
      proof
        assume "v = a"
        hence "y = b" using hy_eq b_def by (by100 simp)
        thus False using hyb by (by100 simp)
      qed
      show "y \<in> \<phi> ` (V - {a})" using hvV hva hy_eq by (by100 blast)
    qed
  qed
  have hB_indep: "independent B"
  proof -
    have "affine_dependent V \<longleftrightarrow> dependent B"
      unfolding B_def by (rule affine_dependent_iff_dependent2[OF haV])
    thus ?thesis using hV_ai by (by100 simp)
  qed
  have hFB_eq: "F ` B = ((+) (- b)) ` (W - {b})"
  proof
    show "F ` B \<subseteq> ((+) (- b)) ` (W - {b})"
    proof
      fix y assume hy: "y \<in> F ` B"
      obtain x where hxB: "x \<in> B" and hy_eq: "y = F x"
        using hy by (by100 blast)
      obtain v where hv: "v \<in> V - {a}" and hx_eq: "x = - a + v"
        using hxB unfolding B_def by (by100 blast)
      have "y = - b + \<phi> v"
        using hy_eq hx_eq unfolding F_def by (simp add: algebra_simps)
      thus "y \<in> ((+) (- b)) ` (W - {b})"
        using hv h\<phi>_minus by (by100 blast)
    qed
    show "((+) (- b)) ` (W - {b}) \<subseteq> F ` B"
    proof
      fix y assume hy: "y \<in> ((+) (- b)) ` (W - {b})"
      obtain w where hw: "w \<in> W - {b}" and hy_eq: "y = - b + w"
        using hy by (by100 blast)
      have hw_phi: "w \<in> \<phi> ` (V - {a})"
        using hw h\<phi>_minus by (by100 simp)
      obtain v where hv: "v \<in> V - {a}" and hw_eq: "w = \<phi> v"
        using hw_phi by (by100 blast)
      define x where "x = - a + v"
      have hxB: "x \<in> B" unfolding x_def B_def using hv by (by100 blast)
      have "F x = y"
        using hy_eq hw_eq unfolding F_def x_def by (simp add: algebra_simps)
      thus "y \<in> F ` B" using hxB by (by100 blast)
    qed
  qed
  have hFB_indep: "independent (F ` B)"
  proof -
    have "affine_dependent W \<longleftrightarrow> dependent (((+) (- b)) ` (W - {b}))"
      by (rule affine_dependent_iff_dependent2[OF hbW])
    hence "\<not> dependent (((+) (- b)) ` (W - {b}))"
      using hW_ai by (by100 blast)
    thus ?thesis using hFB_eq by (by100 simp)
  qed
  have hF_inj: "inj_on F B"
  proof (rule inj_onI)
    fix x y
    assume hxB: "x \<in> B" and hyB: "y \<in> B" and hFxy: "F x = F y"
    obtain vx where hvx: "vx \<in> V - {a}" and hx_eq: "x = - a + vx"
      using hxB unfolding B_def by (by100 blast)
    obtain vy where hvy: "vy \<in> V - {a}" and hy_eq: "y = - a + vy"
      using hyB unfolding B_def by (by100 blast)
    have hvxV: "vx \<in> V" and hvyV: "vy \<in> V"
      using hvx hvy by (by100 blast)+
    have "\<phi> vx = \<phi> vy"
      using hFxy hx_eq hy_eq unfolding F_def by (simp add: algebra_simps)
    hence "vx = vy"
      using h\<phi>_inj hvxV hvyV unfolding inj_on_def by (by100 blast)
    thus "x = y" using hx_eq hy_eq by (by100 simp)
  qed
  obtain A :: "'a \<Rightarrow> 'a" where hA_lin: "linear A"
      and hA_inj: "inj A"
      and hA_B: "\<forall>x\<in>B. A x = F x"
    using linear_independent_extend_inj[OF hB_indep hFB_indep hF_inj] by (by100 blast)
  define g where "g x = b + A (x - a)" for x
  have hg_homeo: "top1_homeomorphism_on UNIV geotop_euclidean_topology
                    UNIV geotop_euclidean_topology g"
    unfolding g_def by (rule geotop_affine_linear_homeomorphism_UNIV[OF hA_lin hA_inj])
  have hg_vertex: "\<forall>v\<in>V. g v = \<phi> v"
  proof
    fix v assume hvV: "v \<in> V"
    show "g v = \<phi> v"
    proof (cases "v = a")
      case True
      have "A 0 = 0"
        using hA_lin linear_0 by (by100 blast)
      thus ?thesis using True unfolding g_def b_def by (by100 simp)
    next
      case False
      have hvB: "- a + v \<in> B"
        unfolding B_def using hvV False by (by100 blast)
      have hA: "A (- a + v) = F (- a + v)"
        using hA_B hvB by (by100 blast)
      have hF: "F (- a + v) = \<phi> v - b"
        unfolding F_def by (simp add: algebra_simps)
      show ?thesis
        unfolding g_def using hA hF by (simp add: algebra_simps)
    qed
  qed
  have hg_vertices_image: "g ` V = W"
  proof -
    have "g ` V = \<phi> ` V"
      using hg_vertex by (by100 force)
    thus ?thesis using h\<phi>_image by (by100 simp)
  qed
  have hg_hull_image: "g ` (convex hull V) = convex hull W"
  proof -
    have "g ` (convex hull V) = convex hull (g ` V)"
    proof -
      have hminus_image:
        "((\<lambda>x. x - a) ` (convex hull V)) = convex hull ((\<lambda>x. x - a) ` V)"
      proof -
        have "convex hull (((+) (- a)) ` V) = ((+) (- a)) ` (convex hull V)"
          by (rule convex_hull_translation)
        thus ?thesis by (simp add: algebra_simps)
      qed
      have hA_image:
        "A ` ((\<lambda>x. x - a) ` (convex hull V)) =
          convex hull (A ` ((\<lambda>x. x - a) ` V))"
        using convex_hull_linear_image[OF hA_lin, of "((\<lambda>x. x - a) ` V)"] hminus_image
        by (by100 simp)
      have hplus_image:
        "((+) b) ` (convex hull (A ` ((\<lambda>x. x - a) ` V))) =
          convex hull (((+) b) ` (A ` ((\<lambda>x. x - a) ` V)))"
      proof -
        have "convex hull (((+) b) ` (A ` ((\<lambda>x. x - a) ` V))) =
          ((+) b) ` (convex hull (A ` ((\<lambda>x. x - a) ` V)))"
          by (rule convex_hull_translation)
        thus ?thesis by (by100 simp)
      qed
      have "g ` (convex hull V) =
          ((+) b) ` (A ` ((\<lambda>x. x - a) ` (convex hull V)))"
        unfolding g_def by (simp add: image_image)
      also have "\<dots> = ((+) b) ` (convex hull (A ` ((\<lambda>x. x - a) ` V)))"
        using hA_image by (by100 simp)
      also have "\<dots> = convex hull (((+) b) ` (A ` ((\<lambda>x. x - a) ` V)))"
        using hplus_image by (by100 simp)
      also have "\<dots> = convex hull (g ` V)"
        unfolding g_def by (simp add: image_image)
      finally show ?thesis .
    qed
    also have "\<dots> = convex hull W"
      using hg_vertices_image by (by100 simp)
    finally show ?thesis .
  qed
  have hg_image: "g ` \<sigma> = \<tau>"
    using h\<sigma>_HOL h\<tau>_HOL hg_hull_image by (by100 simp)
  have hg_linear: "geotop_linear_on \<sigma> g"
  proof -
    have hprop: "\<forall>\<alpha>. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1 \<longrightarrow>
          g (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R g v)"
    proof (intro allI impI)
      fix \<alpha> :: "'a \<Rightarrow> real"
      assume h\<alpha>: "(\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1"
      have hsum: "sum \<alpha> V = 1"
        using h\<alpha> by (by100 blast)
      have hsum_a: "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R a) = a"
      proof -
        have "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R a) = (sum \<alpha> V) *\<^sub>R a"
          by (rule scaleR_left.sum[symmetric])
        thus ?thesis using hsum by (by100 simp)
      qed
      have hsum_b: "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R b) = b"
      proof -
        have "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R b) = (sum \<alpha> V) *\<^sub>R b"
          by (rule scaleR_left.sum[symmetric])
        thus ?thesis using hsum by (by100 simp)
      qed
      have hdiff_sum:
        "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) - a = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R (v - a))"
      proof -
        have "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R (v - a)) =
            (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) - (\<Sum>v\<in>V. \<alpha> v *\<^sub>R a)"
          by (simp add: scaleR_diff_right sum_subtractf)
        also have "\<dots> = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) - a"
          using hsum_a by (by100 simp)
        finally show ?thesis by (by100 simp)
      qed
      have hA_sum:
        "A ((\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) - a) =
          (\<Sum>v\<in>V. \<alpha> v *\<^sub>R A (v - a))"
      proof -
        have "A ((\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) - a) =
            A (\<Sum>v\<in>V. \<alpha> v *\<^sub>R (v - a))"
          using hdiff_sum by (by100 simp)
        also have "\<dots> = (\<Sum>v\<in>V. A (\<alpha> v *\<^sub>R (v - a)))"
          by (rule linear_sum[OF hA_lin])
        also have "\<dots> = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R A (v - a))"
          using hA_lin by (simp add: linear_scale)
        finally show ?thesis .
      qed
      have hlhs:
        "g (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) =
          b + (\<Sum>v\<in>V. \<alpha> v *\<^sub>R A (v - a))"
        unfolding g_def using hA_sum by (by100 simp)
      have hrhs:
        "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R g v) =
          b + (\<Sum>v\<in>V. \<alpha> v *\<^sub>R A (v - a))"
      proof -
        have "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R g v) =
            (\<Sum>v\<in>V. \<alpha> v *\<^sub>R (b + A (v - a)))"
          unfolding g_def by (by100 simp)
        also have "\<dots> =
            (\<Sum>v\<in>V. \<alpha> v *\<^sub>R b) +
            (\<Sum>v\<in>V. \<alpha> v *\<^sub>R A (v - a))"
          by (simp add: scaleR_right_distrib sum.distrib)
        also have "\<dots> =
            b + (\<Sum>v\<in>V. \<alpha> v *\<^sub>R A (v - a))"
          using hsum_b by (by100 simp)
        finally show ?thesis .
      qed
      show "g (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R g v)"
        using hlhs hrhs by (by100 simp)
    qed
    show ?thesis
      unfolding geotop_linear_on_def using hV hprop by (by100 blast)
  qed
  have hg_simplicial: "geotop_simplicial_on \<sigma> g \<tau>"
  proof -
    have hvertex_into: "\<forall>v\<in>V. g v \<in> W"
      using hg_vertex h\<phi>_image by (by100 blast)
    show ?thesis
      unfolding geotop_simplicial_on_def
      using hV hW hvertex_into hg_linear by (by100 blast)
  qed
  show ?thesis
    using hg_homeo hg_image hg_simplicial hg_vertex by (by100 blast)
qed

(** from \<S>3 Theorem 1 (geotop.tex:724)
    LATEX VERSION: Let \<sigma>^n = v_0 v_1 ... v_n and \<tau>^n = w_0 w_1 ... w_n be simplexes in R^m.
      Then there is a simplicial homeomorphism f: \<sigma>^n \<leftrightarrow> \<tau>^n, f: v_i \<mapsto> w_i. **)
theorem Theorem_GT_3_1:
  fixes V W :: "'a::euclidean_space set" and \<sigma> \<tau> :: "'a set"
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
  (** (1) For each P \<in> \<sigma>, express P in barycentric coordinates P = \<Sigma>_{v \<in> V}
         \<alpha>_v v with \<alpha>_v \<ge> 0 and \<Sigma> \<alpha>_v = 1, using the zero extension off V. **)
  have h_barycentric:
    "\<forall>P\<in>\<sigma>. \<exists>\<alpha>::'a \<Rightarrow> real. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1 \<and>
                          (\<forall>v. v \<notin> V \<longrightarrow> \<alpha> v = 0) \<and>
                          P = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v)"
  proof
    fix P
    assume hP: "P \<in> \<sigma>"
    have hV_fin: "finite V"
      using hV unfolding geotop_simplex_vertices_def by (by100 blast)
    have h\<sigma>_hull: "\<sigma> = geotop_convex_hull V"
      using hV unfolding geotop_simplex_vertices_def by (by100 blast)
    have h\<sigma>_HOL: "\<sigma> = convex hull V"
      using h\<sigma>_hull geotop_convex_hull_eq_HOL by (by100 simp)
    have hP_hull: "P \<in> convex hull V"
      using hP h\<sigma>_HOL by (by100 simp)
    have h_hull_char:
      "convex hull V =
        {x. \<exists>\<alpha>::'a \<Rightarrow> real. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1 \<and>
              (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = x}"
      by (rule convex_hull_finite[OF hV_fin])
    obtain \<beta> :: "'a \<Rightarrow> real"
      where h\<beta>_nn: "\<forall>v\<in>V. 0 \<le> \<beta> v"
        and h\<beta>_sum: "sum \<beta> V = 1"
        and h\<beta>_P: "(\<Sum>v\<in>V. \<beta> v *\<^sub>R v) = P"
      using hP_hull h_hull_char by (by100 blast)
    define \<alpha> :: "'a \<Rightarrow> real" where "\<alpha> v = (if v \<in> V then \<beta> v else 0)" for v
    have h\<alpha>_nn: "\<forall>v\<in>V. 0 \<le> \<alpha> v"
      unfolding \<alpha>_def using h\<beta>_nn by (by100 simp)
    have h\<alpha>_sum: "sum \<alpha> V = 1"
      unfolding \<alpha>_def using h\<beta>_sum by (by100 simp)
    have h\<alpha>_zero: "\<forall>v. v \<notin> V \<longrightarrow> \<alpha> v = 0"
      unfolding \<alpha>_def by (by100 simp)
    have h\<alpha>_P: "P = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v)"
      unfolding \<alpha>_def using h\<beta>_P by (by100 simp)
    show "\<exists>\<alpha>::'a \<Rightarrow> real. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1 \<and>
          (\<forall>v. v \<notin> V \<longrightarrow> \<alpha> v = 0) \<and> P = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v)"
      using h\<alpha>_nn h\<alpha>_sum h\<alpha>_zero h\<alpha>_P by (by100 blast)
  qed
  (** (2) Define f: \<sigma> \<to> \<tau> by f(P) = \<Sigma>_{v \<in> V} \<alpha>_v \<phi>(v). This is affine on each face and
         bijective (barycentric coordinates are unique). **)
  \<comment> \<open>Sub-claim T3_1-A: f restricted to V agrees with \<phi>. Trivial witness f = \<phi>.\<close>
  have hT3_1_vertex_match:
    "\<exists>f. (\<forall>v\<in>V. f v = \<phi> v)"
    using exI[of _ \<phi>] by (by100 blast)
  \<comment> \<open>Sub-claim T3_1-B: there is a simplicial map \<sigma> into \<tau>.
    The full vertex-matching simplicial homeomorphism remains the combined
    barycentric-extension claim below.\<close>
  have hT3_1_simplicial:
    "\<exists>f. geotop_simplicial_on \<sigma> f \<tau>"
  proof -
    have hW_ne: "W \<noteq> {}"
    proof -
      obtain m n where hW_fin: "finite W" and hW_card: "card W = n + 1"
        using hW unfolding geotop_simplex_vertices_def by (by100 blast)
      show ?thesis using hW_fin hW_card by (by100 fastforce)
    qed
    obtain w where hwW: "w \<in> W"
      using hW_ne by (by100 blast)
    have h_const_linear: "geotop_linear_on \<sigma> (\<lambda>_. w)"
    proof -
      have h_prop: "\<forall>\<alpha>. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1 \<longrightarrow>
            (\<lambda>_. w) (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R ((\<lambda>_. w) v))"
      proof (intro allI impI)
        fix \<alpha> :: "'a \<Rightarrow> real"
        assume h\<alpha>: "(\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1"
        have hsum: "sum \<alpha> V = 1" using h\<alpha> by (by100 blast)
        have "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R w) = (sum \<alpha> V) *\<^sub>R w"
          by (rule scaleR_left.sum[symmetric])
        also have "\<dots> = w"
          using hsum by (by100 simp)
        finally show "(\<lambda>_. w) (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) =
            (\<Sum>v\<in>V. \<alpha> v *\<^sub>R ((\<lambda>_. w) v))"
          by (by100 simp)
      qed
      show ?thesis
        unfolding geotop_linear_on_def using hV h_prop by (by100 blast)
    qed
    have h_const_simp: "geotop_simplicial_on \<sigma> (\<lambda>_. w) \<tau>"
      unfolding geotop_simplicial_on_def
      using hV hW hwW h_const_linear by (by100 blast)
    show ?thesis using h_const_simp by (by100 blast)
  qed
  \<comment> \<open>Sub-claim T3_1-C: f is a homeomorphism \<sigma> \<leftrightarrow> \<tau>.\<close>
  have hT3_1_homeo:
    "\<exists>f. top1_homeomorphism_on \<sigma>
           (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<tau>
           (subspace_topology UNIV geotop_euclidean_topology \<tau>) f"
  proof -
    have hV_fin: "finite V"
      using hV unfolding geotop_simplex_vertices_def by (by100 blast)
    have hW_fin: "finite W"
      using hW unfolding geotop_simplex_vertices_def by (by100 blast)
    have h\<sigma>_hull: "\<sigma> = geotop_convex_hull V"
      using hV unfolding geotop_simplex_vertices_def by (by100 blast)
    have h\<tau>_hull: "\<tau> = geotop_convex_hull W"
      using hW unfolding geotop_simplex_vertices_def by (by100 blast)
    have h\<sigma>_HOL: "\<sigma> = convex hull V"
      using h\<sigma>_hull geotop_convex_hull_eq_HOL by (by100 simp)
    have h\<tau>_HOL: "\<tau> = convex hull W"
      using h\<tau>_hull geotop_convex_hull_eq_HOL by (by100 simp)
    have h\<sigma>_conv: "convex \<sigma>"
      using h\<sigma>_HOL by (by100 simp)
    have h\<tau>_conv: "convex \<tau>"
      using h\<tau>_HOL by (by100 simp)
    have h\<sigma>_compact: "compact \<sigma>"
      using h\<sigma>_HOL hV_fin finite_imp_compact_convex_hull by (by100 blast)
    have h\<tau>_compact: "compact \<tau>"
      using h\<tau>_HOL hW_fin finite_imp_compact_convex_hull by (by100 blast)
    have hV_ai: "\<not> affine_dependent V"
      by (rule geotop_general_position_imp_aff_indep[OF hV])
    have hW_ai: "\<not> affine_dependent W"
      by (rule geotop_general_position_imp_aff_indep[OF hW])
    have hV_aff: "aff_dim V = int (card V) - 1"
      using hV_ai affine_independent_iff_card hV_fin by (by100 blast)
    have hW_aff: "aff_dim W = int (card W) - 1"
      using hW_ai affine_independent_iff_card hW_fin by (by100 blast)
    have h\<sigma>_aff: "aff_dim \<sigma> = int (card V) - 1"
      using h\<sigma>_HOL hV_aff aff_dim_convex_hull[of V] by (by100 simp)
    have h\<tau>_aff: "aff_dim \<tau> = int (card W) - 1"
      using h\<tau>_HOL hW_aff aff_dim_convex_hull[of W] by (by100 simp)
    have h_aff_eq: "aff_dim \<sigma> = aff_dim \<tau>"
      using h\<sigma>_aff h\<tau>_aff hcard by (by100 simp)
    have h_HOL_homeo: "\<sigma> homeomorphic \<tau>"
      by (rule homeomorphic_convex_compact_sets
            [OF h\<sigma>_conv h\<sigma>_compact h\<tau>_conv h\<tau>_compact h_aff_eq])
    show ?thesis
      by (rule geotop_HOL_homeomorphic_imp_top1_homeomorphism_on[OF h_HOL_homeo])
  qed
  have h_f_def:
    "\<exists>f. (\<forall>v\<in>V. f v = \<phi> v) \<and>
         geotop_simplicial_on \<sigma> f \<tau> \<and>
         top1_homeomorphism_on \<sigma>
           (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<tau>
           (subspace_topology UNIV geotop_euclidean_topology \<tau>) f"
  proof -
    obtain g where hg_homeo: "top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology g"
        and hg_image: "g ` \<sigma> = \<tau>"
        and hg_simp: "geotop_simplicial_on \<sigma> g \<tau>"
        and hg_vertex: "\<forall>v\<in>V. g v = \<phi> v"
      using geotop_simplex_vertex_bijection_affine_extension[OF hV hW h\<phi>_bij]
      by (by100 blast)
    have hg_sub: "top1_homeomorphism_on \<sigma>
            (subspace_topology UNIV geotop_euclidean_topology \<sigma>) \<tau>
            (subspace_topology UNIV geotop_euclidean_topology \<tau>) g"
      by (rule geotop_UNIV_homeomorphism_restrict[OF hg_homeo hg_image])
    show ?thesis using hg_vertex hg_simp hg_sub by (by100 blast)
  qed
  show ?thesis using h_f_def by (by100 blast)
qed

(** from \<S>3 Theorem 2 (geotop.tex:735)
    LATEX VERSION: In Theorem 1, if m = n, then there is a homeomorphism g: R^n \<leftrightarrow> R^n such
      that g|\<sigma>^n is a simplicial homeomorphism \<sigma>^n \<leftrightarrow> \<tau>^n. **)
theorem Theorem_GT_3_2:
  fixes V W :: "'a::euclidean_space set" and \<sigma> \<tau> :: "'a set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> n" and h\<tau>: "geotop_simplex_dim \<tau> n"
  assumes hV: "geotop_simplex_vertices \<sigma> V" and hW: "geotop_simplex_vertices \<tau> W"
  assumes h\<phi>_mem: "\<phi> \<in> V \<rightarrow>\<^sub>E W" and h\<phi>_bij: "bij_betw \<phi> V W"
  shows "\<exists>g. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology g
          \<and> g ` \<sigma> = \<tau>
          \<and> (\<forall>x\<in>\<sigma>. g x \<in> \<tau>) \<and> geotop_simplicial_on \<sigma> g \<tau>"
proof -
  (** (1) By Theorem 3.1 there is a simplicial homeomorphism f: \<sigma> \<leftrightarrow> \<tau> with f | V = \<phi>. **)
  obtain f where hf_simpl:
    "top1_homeomorphism_on \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>)
        \<tau> (subspace_topology UNIV geotop_euclidean_topology \<tau>) f \<and>
     geotop_simplicial_on \<sigma> f \<tau> \<and>
     (\<forall>v\<in>V. f v = \<phi> v)"
  proof -
    have hV_fin: "finite V"
      using hV unfolding geotop_simplex_vertices_def by (by100 blast)
    have hcard: "card V = card W"
      using h\<phi>_bij hV_fin bij_betw_same_card by (by100 blast)
    show ?thesis
      using Theorem_GT_3_1[OF hV hW hcard h\<phi>_mem h\<phi>_bij] that by (by100 blast)
  qed
  (** (2) Extend f to an affine map A: R^m \<to> R^m (where m is the ambient dimension),
         since both \<sigma> and \<tau> are n-simplexes in R^m with n = m (same dim). The affine
         extension is uniquely determined by images of V \<cup> {V's affine basis complement}. **)
  \<comment> \<open>Sub-claim AE-1: \<exists>g plane homeo extending f on \<sigma> (affine extension).\<close>
  have h_affine_extension:
    "\<exists>g. (\<forall>x\<in>\<sigma>. g x = f x) \<and> bij g \<and>
         top1_homeomorphism_on UNIV geotop_euclidean_topology
            UNIV geotop_euclidean_topology g"
  proof -
    obtain g where hg_homeo: "top1_homeomorphism_on UNIV geotop_euclidean_topology
              UNIV geotop_euclidean_topology g"
        and hg_image: "g ` \<sigma> = \<tau>"
        and hg_simp: "geotop_simplicial_on \<sigma> g \<tau>"
        and hg_vertex: "\<forall>v\<in>V. g v = \<phi> v"
      using geotop_simplex_vertex_bijection_affine_extension[OF hV hW h\<phi>_bij]
      by (by100 blast)
    have hf_simp: "geotop_simplicial_on \<sigma> f \<tau>"
      using hf_simpl by (by100 blast)
    have hf_vertex: "\<forall>v\<in>V. f v = \<phi> v"
      using hf_simpl by (by100 blast)
    have hf_lin: "geotop_linear_on \<sigma> f"
      using hf_simp unfolding geotop_simplicial_on_def by (by100 blast)
    have hg_lin: "geotop_linear_on \<sigma> g"
      using hg_simp unfolding geotop_simplicial_on_def by (by100 blast)
    have hfg_vertex: "\<forall>v\<in>V. f v = g v"
      using hf_vertex hg_vertex by (by100 simp)
    have hfg_eq: "\<forall>x\<in>\<sigma>. f x = g x"
      by (rule geotop_linear_on_eq_vertices[OF hV hf_lin hg_lin hfg_vertex])
    have hg_eq: "\<forall>x\<in>\<sigma>. g x = f x"
      using hfg_eq by (by100 simp)
    have hg_bij: "bij g"
      using top1_homeomorphism_on_imp_bij[OF hg_homeo]
      by (simp add: bij_betw_def bij_def)
    show ?thesis using hg_eq hg_bij hg_homeo by (by100 blast)
  qed
  \<comment> \<open>Sub-claim AE-2: the extension g is also simplicial on \<sigma> with g(\<sigma>) \<subseteq> \<tau>.
    Follows from AE-1 + simplicial property of f preserved through extension
    (via cached helper geotop_simplicial_on_eq_on).\<close>
  have h_affine_simplicial:
    "\<exists>g. top1_homeomorphism_on UNIV geotop_euclidean_topology
              UNIV geotop_euclidean_topology g
         \<and> g ` \<sigma> = \<tau>
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
    have hf_image: "f ` \<sigma> = \<tau>"
      using hf_bij_on unfolding bij_betw_def by (by100 blast)
    have hg_image: "g ` \<sigma> = \<tau>"
      using hg_eq hf_image by (by100 force)
    \<comment> \<open>simplicial_on \<sigma> g \<tau> from simplicial_on \<sigma> f \<tau> via the cached helper.\<close>
    have hf_simp: "geotop_simplicial_on \<sigma> f \<tau>"
      using hf_simpl by blast
    have hg_simp: "geotop_simplicial_on \<sigma> g \<tau>"
      by (rule geotop_simplicial_on_eq_on[OF hf_simp hg_eq])
    show ?thesis using hg_homeo hg_image hg_into_\<tau> hg_simp by blast
  qed
  have h_affine_ext:
    "(\<exists>g. (\<forall>x\<in>\<sigma>. g x = f x) \<and> bij g \<and>
         top1_homeomorphism_on UNIV geotop_euclidean_topology
            UNIV geotop_euclidean_topology g) \<and>
     (\<exists>g. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology g
          \<and> g ` \<sigma> = \<tau>
          \<and> (\<forall>x\<in>\<sigma>. g x \<in> \<tau>) \<and> geotop_simplicial_on \<sigma> g \<tau>)"
    using h_affine_extension h_affine_simplicial by (by100 blast)
  have h_final: "\<exists>g. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology g
          \<and> g ` \<sigma> = \<tau>
          \<and> (\<forall>x\<in>\<sigma>. g x \<in> \<tau>) \<and> geotop_simplicial_on \<sigma> g \<tau>"
    using h_affine_ext by (by100 blast)
  show ?thesis using h_final by (by100 blast)
qed

lemma interior_Un_subset_closed_left_if_right_empty:
  fixes A B :: "'a::topological_space set"
  assumes hA: "closed A"
      and hB: "interior B = {}"
  shows "interior (A \<union> B) \<subseteq> A"
proof
  fix x
  assume hx: "x \<in> interior (A \<union> B)"
  show "x \<in> A"
  proof (rule ccontr)
    assume hx_not_A: "x \<notin> A"
    have hopen_A: "open (- A)"
      using hA unfolding closed_def by (by100 simp)
    have hopen_int: "open (interior (A \<union> B))"
      by (rule open_interior)
    have hopen: "open (interior (A \<union> B) \<inter> - A)"
      by (rule open_Int[OF hopen_int hopen_A])
    have hx_open: "x \<in> interior (A \<union> B) \<inter> - A"
      using hx hx_not_A by (by100 simp)
    have hsub_B: "interior (A \<union> B) \<inter> - A \<subseteq> B"
    proof
      fix y
      assume hy: "y \<in> interior (A \<union> B) \<inter> - A"
      have hy_union: "y \<in> A \<union> B"
        using hy interior_subset by (by100 blast)
      have hy_not_A: "y \<notin> A"
        using hy by (by100 simp)
      show "y \<in> B"
        using hy_union hy_not_A by (by100 blast)
    qed
    have "x \<in> interior B"
      using hopen hx_open hsub_B interior_maximal by (by100 blast)
    thus False
      using hB by (by100 simp)
  qed
qed

lemma geotop_simplex_dim_le_2_R2_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> n"
  shows "n \<le> 2"
proof -
  obtain V m where hVfin: "finite V"
    and hVcard: "card V = n + 1"
    and hnm: "n \<le> m"
    and hVgp: "geotop_general_position V m"
    and h\<sigma>eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma> unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    unfolding geotop_simplex_vertices_def
    using hVfin hVcard hnm hVgp h\<sigma>eq by (by100 blast)
  have hVai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF h\<sigma>V])
  have h_aff_V: "aff_dim V = int (card V) - 1"
    using hVai affine_independent_iff_card hVfin by (by100 blast)
  have h_aff_le: "aff_dim V \<le> int (DIM(real^2))"
    by (rule aff_dim_le_DIM)
  have hDIM: "DIM(real^2) = 2"
    by (by100 simp)
  have "int n \<le> (2::int)"
    using h_aff_V h_aff_le hDIM hVcard by (by100 linarith)
  show ?thesis
    using \<open>int n \<le> (2::int)\<close> by (by100 linarith)
qed

lemma geotop_face_witness_simplex_vertices_prefix:
  fixes \<tau> \<sigma> :: "(real^2) set"
  assumes hface: "geotop_is_face \<tau> \<sigma>"
  obtains V W where "geotop_simplex_vertices \<sigma> V"
    and "W \<noteq> {}" and "W \<subseteq> V"
    and "\<tau> = geotop_convex_hull W"
    and "geotop_simplex_vertices \<tau> W"
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}" and hW_sub: "W \<subseteq> V"
    and h\<tau>_eq: "\<tau> = geotop_convex_hull W"
    using hface unfolding geotop_is_face_def by (by100 blast)
  obtain m n where hV_fin: "finite V"
    and hV_card: "card V = n + 1"
    and hn_le_m: "n \<le> m"
    and hgp: "geotop_general_position V m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hW_fin: "finite W"
    using hW_sub hV_fin by (rule finite_subset)
  have hW_card_pos: "0 < card W"
    using hW_fin hW_ne by (by100 force)
  have hW_card_eq: "card W = (card W - 1) + 1"
    using hW_card_pos by (by100 simp)
  have hW_card_le: "card W \<le> card V"
    by (rule card_mono[OF hV_fin hW_sub])
  have hW_dim_le_m: "card W - 1 \<le> m"
    using hW_card_le hV_card hn_le_m by (by100 linarith)
  have hgp_W: "geotop_general_position W m"
    by (rule geotop_general_position_subset[OF hgp hW_sub])
  have h\<tau>W: "geotop_simplex_vertices \<tau> W"
    unfolding geotop_simplex_vertices_def
    using hW_fin hW_card_eq hW_dim_le_m hgp_W h\<tau>_eq by (by100 blast)
  show ?thesis
    by (rule that[OF h\<sigma>V hW_ne hW_sub h\<tau>_eq h\<tau>W])
qed

lemma geotop_edge_face_witness_card_two_prefix:
  fixes e \<sigma> :: "(real^2) set"
  assumes hedge: "geotop_is_edge e"
  assumes hface: "geotop_is_face e \<sigma>"
  obtains V W where "geotop_simplex_vertices \<sigma> V"
    and "W \<noteq> {}" and "W \<subseteq> V"
    and "e = geotop_convex_hull W"
    and "geotop_simplex_vertices e W"
    and "card W = 2"
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}" and hW_sub: "W \<subseteq> V"
    and he_eq: "e = geotop_convex_hull W"
    and heW: "geotop_simplex_vertices e W"
    by (rule geotop_face_witness_simplex_vertices_prefix[OF hface])
  have he_dim: "geotop_simplex_dim e 1"
    using hedge unfolding geotop_is_edge_def by (by100 simp)
  obtain V\<^sub>e m where hVe_fin: "finite V\<^sub>e"
    and hVe_card: "card V\<^sub>e = 1 + 1"
    and h1_le_m: "1 \<le> m"
    and hgp_Ve: "geotop_general_position V\<^sub>e m"
    and he_Ve: "e = geotop_convex_hull V\<^sub>e"
    using he_dim unfolding geotop_simplex_dim_def by (by100 blast)
  have heVe: "geotop_simplex_vertices e V\<^sub>e"
    unfolding geotop_simplex_vertices_def
    using hVe_fin hVe_card h1_le_m hgp_Ve he_Ve by (by100 blast)
  have hW_eq: "W = V\<^sub>e"
    by (rule geotop_simplex_vertices_unique[OF heW heVe])
  have hW_card: "card W = 2"
    using hW_eq hVe_card by (by100 simp)
  show ?thesis
    by (rule that[OF h\<sigma>V hW_ne hW_sub he_eq heW hW_card])
qed

lemma geotop_is_face_imp_subset_prefix:
  fixes \<tau> \<sigma> :: "(real^2) set"
  assumes hface: "geotop_is_face \<tau> \<sigma>"
  shows "\<tau> \<subseteq> \<sigma>"
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_sub: "W \<subseteq> V"
    and h\<tau>_eq: "\<tau> = geotop_convex_hull W"
    using hface unfolding geotop_is_face_def by (by100 blast)
  obtain m n where h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hmono: "convex hull W \<subseteq> convex hull V"
    by (rule hull_mono[OF hW_sub])
  show ?thesis
    using hmono h\<tau>_eq h\<sigma>_eq geotop_convex_hull_eq_HOL[of W]
      geotop_convex_hull_eq_HOL[of V]
    by (by100 simp)
qed

lemma geotop_2simplex_edge_faces_card_le3_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  shows "finite {e. geotop_is_edge e \<and> geotop_is_face e \<sigma>}
      \<and> card {e. geotop_is_edge e \<and> geotop_is_face e \<sigma>} \<le> 3"
proof -
  let ?E = "{e. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
  obtain V m where hV_fin: "finite V"
    and hV_card: "card V = 2 + 1"
    and h2_le_m: "2 \<le> m"
    and hgp: "geotop_general_position V m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma> unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    unfolding geotop_simplex_vertices_def
    using hV_fin hV_card h2_le_m hgp h\<sigma>_eq by (by100 blast)
  have hV_card3: "card V = 3"
    using hV_card by (by100 simp)
  have hV_three:
    "\<exists>a b c. V = {a, b, c} \<and> a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c"
    using hV_card3 card_3_iff by (by100 metis)
  obtain a b c where hV_eq: "V = {a, b, c}"
    and hab: "a \<noteq> b" and hbc: "b \<noteq> c" and hac: "a \<noteq> c"
    using hV_three by (by100 blast)
  let ?Pairs =
    "{geotop_convex_hull {a, b}, geotop_convex_hull {a, c},
      geotop_convex_hull {b, c}}"
  have hE_sub: "?E \<subseteq> ?Pairs"
  proof
    fix e
    assume heE: "e \<in> ?E"
    have hedge: "geotop_is_edge e"
      using heE by (by100 simp)
    have hface: "geotop_is_face e \<sigma>"
      using heE by (by100 simp)
    obtain V' W where h\<sigma>V': "geotop_simplex_vertices \<sigma> V'"
      and hW_sub: "W \<subseteq> V'"
      and he_eq: "e = geotop_convex_hull W"
      and hW_card: "card W = 2"
      by (metis geotop_edge_face_witness_card_two_prefix[OF hedge hface])
    have hV'_eq: "V' = V"
      by (rule geotop_simplex_vertices_unique[OF h\<sigma>V' h\<sigma>V])
    have hW_subV: "W \<subseteq> V"
      using hW_sub hV'_eq by (by100 simp)
    have hW_cases: "W = {a, b} \<or> W = {a, c} \<or> W = {b, c}"
    proof -
      have hW_pair: "\<exists>x y. W = {x, y} \<and> x \<noteq> y"
        using hW_card card_2_iff[of W] by (by100 simp)
      obtain x y where hW_eq: "W = {x, y}" and hxy: "x \<noteq> y"
        using hW_pair by (by100 blast)
      have hx_cases: "x = a \<or> x = b \<or> x = c"
        using hW_eq hW_subV hV_eq by (by100 blast)
      have hy_cases: "y = a \<or> y = b \<or> y = c"
        using hW_eq hW_subV hV_eq by (by100 blast)
      show ?thesis
      proof (cases "x = a")
        assume hx_a: "x = a"
        show ?thesis
        proof (cases "y = a")
          assume hy_a: "y = a"
          thus ?thesis using hx_a hxy by (by100 simp)
        next
          assume hy_not_a: "y \<noteq> a"
          show ?thesis
          proof (cases "y = b")
            assume hy_b: "y = b"
            thus ?thesis using hx_a hW_eq by (by100 simp)
          next
            assume hy_not_b: "y \<noteq> b"
            have "y = c"
              using hy_cases hy_not_a hy_not_b by (by100 blast)
            thus ?thesis using hx_a hW_eq by (by100 simp)
          qed
        qed
      next
        assume hx_not_a: "x \<noteq> a"
        show ?thesis
        proof (cases "x = b")
          assume hx_b: "x = b"
          show ?thesis
          proof (cases "y = a")
            assume hy_a: "y = a"
            have hW_ba: "W = {b, a}"
              using hx_b hy_a hW_eq by (by100 simp)
            have hba_ab: "{b, a} = {a, b}"
              by (rule insert_commute)
            show ?thesis
              using hW_ba hba_ab by (by100 simp)
          next
            assume hy_not_a: "y \<noteq> a"
            show ?thesis
            proof (cases "y = b")
              assume hy_b: "y = b"
              thus ?thesis using hx_b hxy by (by100 simp)
            next
              assume hy_not_b: "y \<noteq> b"
              have "y = c"
                using hy_cases hy_not_a hy_not_b by (by100 blast)
              thus ?thesis using hx_b hW_eq by (by100 simp)
            qed
          qed
        next
          assume hx_not_b: "x \<noteq> b"
          have hx_c: "x = c"
            using hx_cases hx_not_a hx_not_b by (by100 blast)
          show ?thesis
          proof (cases "y = a")
            assume hy_a: "y = a"
            have hW_ca: "W = {c, a}"
              using hx_c hy_a hW_eq by (by100 simp)
            have hca_ac: "{c, a} = {a, c}"
              by (rule insert_commute)
            show ?thesis
              using hW_ca hca_ac by (by100 simp)
          next
            assume hy_not_a: "y \<noteq> a"
            show ?thesis
            proof (cases "y = b")
              assume hy_b: "y = b"
              have hW_cb: "W = {c, b}"
                using hx_c hy_b hW_eq by (by100 simp)
              have hcb_bc: "{c, b} = {b, c}"
                by (rule insert_commute)
              show ?thesis
                using hW_cb hcb_bc by (by100 simp)
            next
              assume hy_not_b: "y \<noteq> b"
              have "y = c"
                using hy_cases hy_not_a hy_not_b by (by100 blast)
              thus ?thesis using hx_c hxy by (by100 simp)
            qed
          qed
        qed
      qed
    qed
    show "e \<in> ?Pairs"
      using he_eq hW_cases by (by100 auto)
  qed
  have hPairs_fin: "finite ?Pairs"
    by (by100 simp)
  have hE_fin: "finite ?E"
    by (rule finite_subset[OF hE_sub hPairs_fin])
  have hcard_le_pairs: "card ?E \<le> card ?Pairs"
    by (rule card_mono[OF hPairs_fin hE_sub])
  have hPairs_card: "card ?Pairs \<le> 3"
    by (rule card_three_le)
  have hE_card: "card ?E \<le> 3"
    using hcard_le_pairs hPairs_card by (by100 linarith)
  show ?thesis
    using hE_fin hE_card by (by100 blast)
qed

lemma geotop_2simplex_complex_edge_faces_card_le3_prefix:
  fixes K :: "(real^2) set set" and \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  shows "finite {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma>}
      \<and> card {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma>} \<le> 3"
proof -
  let ?E = "{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
  let ?A = "{e. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
  have hA: "finite ?A \<and> card ?A \<le> 3"
    by (rule geotop_2simplex_edge_faces_card_le3_prefix[OF h\<sigma>])
  have hA_fin: "finite ?A"
    using hA by (by100 blast)
  have hA_card: "card ?A \<le> 3"
    using hA by (by100 blast)
  have hE_sub_A: "?E \<subseteq> ?A"
    by (by100 blast)
  have hE_fin: "finite ?E"
    by (rule finite_subset[OF hE_sub_A hA_fin])
  have hE_card_le_A: "card ?E \<le> card ?A"
    by (rule card_mono[OF hA_fin hE_sub_A])
  have hE_card: "card ?E \<le> 3"
    using hE_card_le_A hA_card by (by100 linarith)
  show ?thesis
    using hE_fin hE_card by (by100 blast)
qed

lemma geotop_2simplex_three_selected_edge_faces_all_prefix:
  fixes K :: "(real^2) set set" and J \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hcard: "card {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J} = 3"
  shows "{e. geotop_is_edge e \<and> geotop_is_face e \<sigma>}
      = {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J}"
proof -
  let ?A = "{e. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
  let ?E = "{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J}"
  have hA: "finite ?A \<and> card ?A \<le> 3"
    by (rule geotop_2simplex_edge_faces_card_le3_prefix[OF h\<sigma>])
  have hA_fin: "finite ?A"
    using hA by (by100 blast)
  have hA_card_le3: "card ?A \<le> 3"
    using hA by (by100 blast)
  have hE_sub_A: "?E \<subseteq> ?A"
    by (by100 blast)
  have hE_card_le_A: "card ?E \<le> card ?A"
    by (rule card_mono[OF hA_fin hE_sub_A])
  have hA_card_ge3: "3 \<le> card ?A"
    using hcard hE_card_le_A by (by100 linarith)
  have hA_card_eq: "card ?A = 3"
    using hA_card_ge3 hA_card_le3 by (by100 linarith)
  have hcard_eq: "card ?E = card ?A"
    using hcard hA_card_eq by (by100 simp)
  have hE_eq_A: "?E = ?A"
    by (rule card_subset_eq[OF hA_fin hE_sub_A hcard_eq])
  show ?thesis
    using hE_eq_A by (by100 simp)
qed

lemma geotop_2simplex_frontier_eq_edge_faces_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  shows "frontier \<sigma> = \<Union>{e. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
  (**
    Book base-case geometry: the boundary of a planar 2-simplex is exactly
    the union of its three edge faces. **)
proof -
  let ?E = "{e. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
  obtain V m where hV_fin: "finite V"
    and hV_card: "card V = 2 + 1"
    and h2_le_m: "2 \<le> m"
    and hgp: "geotop_general_position V m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma> unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    unfolding geotop_simplex_vertices_def
    using hV_fin hV_card h2_le_m hgp h\<sigma>_eq by (by100 blast)
  have hV_three:
    "\<exists>a b c. V = {a, b, c} \<and> a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c"
  proof -
    have hV_card3: "card V = 3"
      using hV_card by (by100 simp)
    show ?thesis
      by (rule iffD1[OF card_3_iff hV_card3])
  qed
  obtain a b c where hV_eq: "V = {a, b, c}"
    and hab: "a \<noteq> b" and hbc: "b \<noteq> c" and hac: "a \<noteq> c"
    using hV_three by (by100 blast)
  let ?ab = "geotop_convex_hull {a, b}"
  let ?ac = "geotop_convex_hull {a, c}"
  let ?bc = "geotop_convex_hull {b, c}"
  let ?Pairs = "{?ab, ?ac, ?bc}"
  have hE_sub: "?E \<subseteq> ?Pairs"
  proof
    fix e
    assume heE: "e \<in> ?E"
    have hedge: "geotop_is_edge e"
      using heE by (by100 simp)
    have hface: "geotop_is_face e \<sigma>"
      using heE by (by100 simp)
    obtain V' W where h\<sigma>V': "geotop_simplex_vertices \<sigma> V'"
      and hW_sub: "W \<subseteq> V'"
      and he_eq: "e = geotop_convex_hull W"
      and hW_card: "card W = 2"
      by (metis geotop_edge_face_witness_card_two_prefix[OF hedge hface])
    have hV'_eq: "V' = V"
      by (rule geotop_simplex_vertices_unique[OF h\<sigma>V' h\<sigma>V])
    have hW_subV: "W \<subseteq> V"
      using hW_sub hV'_eq by (by100 simp)
    have hW_pair: "\<exists>x y. W = {x, y} \<and> x \<noteq> y"
      using hW_card card_2_iff[of W] by (by100 simp)
    obtain x y where hW_eq: "W = {x, y}" and hxy: "x \<noteq> y"
      using hW_pair by (by100 blast)
    have hx_cases: "x = a \<or> x = b \<or> x = c"
      using hW_eq hW_subV hV_eq by (by100 blast)
    have hy_cases: "y = a \<or> y = b \<or> y = c"
      using hW_eq hW_subV hV_eq by (by100 blast)
    have hW_cases: "W = {a, b} \<or> W = {a, c} \<or> W = {b, c}"
      using hx_cases hy_cases hW_eq hxy by (by100 auto)
    show "e \<in> ?Pairs"
      using he_eq hW_cases by (by100 auto)
  qed
  have h1_le_m: "1 \<le> m"
    using h2_le_m by (by100 linarith)
  have h_ab_sub: "{a, b} \<subseteq> V"
    using hV_eq by (by100 simp)
  have h_ac_sub: "{a, c} \<subseteq> V"
    using hV_eq by (by100 simp)
  have h_bc_sub: "{b, c} \<subseteq> V"
    using hV_eq by (by100 simp)
  have hgp_ab: "geotop_general_position {a, b} m"
    by (rule geotop_general_position_subset[OF hgp h_ab_sub])
  have hgp_ac: "geotop_general_position {a, c} m"
    by (rule geotop_general_position_subset[OF hgp h_ac_sub])
  have hgp_bc: "geotop_general_position {b, c} m"
    by (rule geotop_general_position_subset[OF hgp h_bc_sub])
  have h_ab_dim: "geotop_simplex_dim ?ab 1"
    unfolding geotop_simplex_dim_def
  proof (rule exI[where x = "{a, b}"], rule exI[where x = m], intro conjI)
    show "finite {a, b}" by (by100 simp)
    show "card {a, b} = 1 + 1" using hab by (by100 simp)
    show "1 \<le> m" by (rule h1_le_m)
    show "geotop_general_position {a, b} m" by (rule hgp_ab)
    show "?ab = geotop_convex_hull {a, b}" by (by100 simp)
  qed
  have h_ac_dim: "geotop_simplex_dim ?ac 1"
    unfolding geotop_simplex_dim_def
  proof (rule exI[where x = "{a, c}"], rule exI[where x = m], intro conjI)
    show "finite {a, c}" by (by100 simp)
    show "card {a, c} = 1 + 1" using hac by (by100 simp)
    show "1 \<le> m" by (rule h1_le_m)
    show "geotop_general_position {a, c} m" by (rule hgp_ac)
    show "?ac = geotop_convex_hull {a, c}" by (by100 simp)
  qed
  have h_bc_dim: "geotop_simplex_dim ?bc 1"
    unfolding geotop_simplex_dim_def
  proof (rule exI[where x = "{b, c}"], rule exI[where x = m], intro conjI)
    show "finite {b, c}" by (by100 simp)
    show "card {b, c} = 1 + 1" using hbc by (by100 simp)
    show "1 \<le> m" by (rule h1_le_m)
    show "geotop_general_position {b, c} m" by (rule hgp_bc)
    show "?bc = geotop_convex_hull {b, c}" by (by100 simp)
  qed
  have h_ab_edge: "geotop_is_edge ?ab"
    unfolding geotop_is_edge_def
    using h_ab_dim by (by100 simp)
  have h_ac_edge: "geotop_is_edge ?ac"
    unfolding geotop_is_edge_def
    using h_ac_dim by (by100 simp)
  have h_bc_edge: "geotop_is_edge ?bc"
    unfolding geotop_is_edge_def
    using h_bc_dim by (by100 simp)
  have h_ab_face: "geotop_is_face ?ab \<sigma>"
    unfolding geotop_is_face_def
  proof (rule exI[where x = V], rule exI[where x = "{a, b}"], intro conjI)
    show "geotop_simplex_vertices \<sigma> V" by (rule h\<sigma>V)
    show "{a, b} \<noteq> {}" by (by100 simp)
    show "{a, b} \<subseteq> V" by (rule h_ab_sub)
    show "?ab = geotop_convex_hull {a, b}" by (by100 simp)
  qed
  have h_ac_face: "geotop_is_face ?ac \<sigma>"
    unfolding geotop_is_face_def
  proof (rule exI[where x = V], rule exI[where x = "{a, c}"], intro conjI)
    show "geotop_simplex_vertices \<sigma> V" by (rule h\<sigma>V)
    show "{a, c} \<noteq> {}" by (by100 simp)
    show "{a, c} \<subseteq> V" by (rule h_ac_sub)
    show "?ac = geotop_convex_hull {a, c}" by (by100 simp)
  qed
  have h_bc_face: "geotop_is_face ?bc \<sigma>"
    unfolding geotop_is_face_def
  proof (rule exI[where x = V], rule exI[where x = "{b, c}"], intro conjI)
    show "geotop_simplex_vertices \<sigma> V" by (rule h\<sigma>V)
    show "{b, c} \<noteq> {}" by (by100 simp)
    show "{b, c} \<subseteq> V" by (rule h_bc_sub)
    show "?bc = geotop_convex_hull {b, c}" by (by100 simp)
  qed
  have hPairs_sub_E: "?Pairs \<subseteq> ?E"
    using h_ab_edge h_ac_edge h_bc_edge h_ab_face h_ac_face h_bc_face by (by100 blast)
  have hE_eq: "?E = ?Pairs"
    using hE_sub hPairs_sub_E by (by100 blast)
  have h\<sigma>_HOL: "\<sigma> = convex hull {a, b, c}"
    using h\<sigma>_eq hV_eq geotop_convex_hull_eq_HOL by (by100 simp)
  have hfront:
    "frontier \<sigma> = closed_segment a b \<union> closed_segment b c \<union> closed_segment c a"
    using frontier_of_triangle[where a = a and b = b and c = c]
      h\<sigma>_HOL by (by100 simp)
  have h_ab_HOL: "?ab = convex hull {a, b}"
    using geotop_convex_hull_eq_HOL[of "{a, b}"] by (by100 simp)
  have h_bc_HOL: "?bc = convex hull {b, c}"
    using geotop_convex_hull_eq_HOL[of "{b, c}"] by (by100 simp)
  have h_ca_set: "{c, a} = {a, c}"
    by (rule insert_commute)
  have h_ca_HOL: "?ac = convex hull {c, a}"
    using geotop_convex_hull_eq_HOL[of "{c, a}"] h_ca_set by (by100 simp)
  have h_ab_segment: "closed_segment a b = ?ab"
    using h_ab_HOL segment_convex_hull[of a b] by (by100 simp)
  have h_bc_segment: "closed_segment b c = ?bc"
    using h_bc_HOL segment_convex_hull[of b c] by (by100 simp)
  have h_ca_segment: "closed_segment c a = ?ac"
    using h_ca_HOL segment_convex_hull[of c a] by (by100 simp)
  have "frontier \<sigma> = ?ab \<union> ?bc \<union> ?ac"
    using hfront h_ab_segment h_bc_segment h_ca_segment by (by100 simp)
  also have "... = \<Union>?Pairs"
    by (by100 auto)
  also have "... = \<Union>?E"
    using hE_eq by (by100 simp)
  finally show ?thesis .
qed

lemma geotop_2simplex_frontier_subset_complex_edge_faces_prefix:
  fixes K :: "(real^2) set set" and \<sigma> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  shows "frontier \<sigma> \<subseteq> \<Union>{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
  (**
    Complex form of the triangle-frontier fact: every boundary point of a
    2-simplex in a complex lies on one of the edge faces of that same complex. **)
proof
  fix x
  assume hx: "x \<in> frontier \<sigma>"
  have hx_edges: "x \<in> \<Union>{e. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
    using geotop_2simplex_frontier_eq_edge_faces_prefix[OF h\<sigma>] hx
    by (by100 simp)
  obtain e where he_edge: "geotop_is_edge e"
    and he_face: "geotop_is_face e \<sigma>"
    and hxe: "x \<in> e"
    using hx_edges by (by100 blast)
  have hface_closed: "\<forall>\<rho>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<rho> \<longrightarrow> \<tau> \<in> K"
    by (rule geotop_is_complex_face_closed[OF hK])
  have heK: "e \<in> K"
    using hface_closed h\<sigma>K he_face by (by100 blast)
  show "x \<in> \<Union>{e \<in> K. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
    using heK he_edge he_face hxe by (by100 blast)
qed

lemma geotop_polygon_interior_regular_closed_prefix:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "interior (closure (geotop_polygon_interior J)) =
      geotop_polygon_interior J"
  (**
    Named form of the book fact used in the Schoenflies base case: the
    polygonal disk closure has ordinary interior equal to the polygon interior. **)
proof
  let ?I = "geotop_polygon_interior J"
  let ?E = "geotop_polygon_exterior J"
  show "?I \<subseteq> interior (closure ?I)"
  proof -
    have hI_open: "open ?I"
      by (rule polygon_interior_open[OF hJ])
    show ?thesis
      by (rule interior_maximal[OF closure_subset hI_open])
  qed
  show "interior (closure ?I) \<subseteq> ?I"
  proof
    fix x
    assume hx_int: "x \<in> interior (closure ?I)"
    have hx_closure: "x \<in> closure ?I"
      using hx_int interior_subset by (by100 blast)
    have hclosure: "closure ?I = ?I \<union> J"
      by (rule polygon_interior_closure_eq[OF hJ])
    have hx_I_or_J: "x \<in> ?I \<or> x \<in> J"
      using hx_closure hclosure by (by100 blast)
    show "x \<in> ?I"
    proof (cases "x \<in> ?I")
      case True
      show ?thesis by (rule True)
    next
      case False
      have hxJ: "x \<in> J"
        using hx_I_or_J False by (by100 blast)
      have hE_front_HOL: "frontier ?E = J"
      proof -
        have hE_front_geo:
          "J = geotop_frontier UNIV geotop_euclidean_topology ?E"
          using Theorem_GT_2_6(2)[OF hJ] by (by100 simp)
        have hfront_eq:
          "geotop_frontier UNIV geotop_euclidean_topology ?E = frontier ?E"
          by (rule geotop_frontier_UNIV_eq_frontier)
        show ?thesis
          using hE_front_geo hfront_eq by (by100 simp)
      qed
      have hI_E: "?I \<inter> ?E = {}"
        by (rule polygon_interior_exterior_disjoint[OF hJ])
      have hE_J: "?E \<inter> J = {}"
        by (rule polygon_exterior_disjoint_polygon[OF hJ])
      have hE_disj_closure: "?E \<inter> closure ?I = {}"
        using hclosure hI_E hE_J by (by100 blast)
      have hxFrontE: "x \<in> frontier ?E"
        using hE_front_HOL hxJ by (by100 simp)
      have hxClosureE: "x \<in> closure ?E"
        using hxFrontE unfolding Elementary_Topology.frontier_def by (by100 simp)
      have hx_not_E: "x \<notin> ?E"
        using hE_disj_closure hx_closure by (by100 blast)
      have hxLimE: "x islimpt ?E"
        using hxClosureE hx_not_E unfolding closure_def by (by100 blast)
      obtain U where hUopen: "open U" and hxU: "x \<in> U" and hUsub: "U \<subseteq> closure ?I"
        using hx_int unfolding interior_def by (by100 blast)
      obtain y where hyE: "y \<in> ?E" and hyU: "y \<in> U" and "y \<noteq> x"
        by (rule islimptE[OF hxLimE hxU hUopen])
      have hy_closure: "y \<in> closure ?I"
        using hUsub hyU by (by100 blast)
      have False
        using hE_disj_closure hyE hy_closure by (by100 blast)
      then show ?thesis
        by (by100 blast)
    qed
  qed
qed

lemma geotop_polygon_boundary_point_in_simplex_not_in_interior_prefix:
  fixes J \<sigma> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hx\<sigma>: "x \<in> \<sigma>"
  assumes hxJ: "x \<in> J"
  shows "x \<notin> interior \<sigma>"
  (**
    Boundary points of the polygonal disk cannot be ordinary interior points
    of a simplex lying in the triangulation of the disk closure. **)
proof
  assume hxint: "x \<in> interior \<sigma>"
  have h\<sigma>_sub_poly: "\<sigma> \<subseteq> geotop_polyhedron K"
    using h\<sigma>K unfolding geotop_polyhedron_def by (by100 blast)
  have hclos_on: "closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)
      = closure (geotop_polygon_interior J)"
    by (rule closure_on_geotop_UNIV_eq_closure)
  have h\<sigma>_sub_closure: "\<sigma> \<subseteq> closure (geotop_polygon_interior J)"
    using h\<sigma>_sub_poly hK_poly hclos_on by (by100 simp)
  have hint_sub_closure: "interior \<sigma> \<subseteq> closure (geotop_polygon_interior J)"
    using h\<sigma>_sub_closure interior_subset by (by100 blast)
  have hregular: "interior (closure (geotop_polygon_interior J)) =
      geotop_polygon_interior J"
    by (rule geotop_polygon_interior_regular_closed_prefix[OF hJ])
  have h_x_in_I: "x \<in> geotop_polygon_interior J"
  proof -
    have h_int_open: "open (interior \<sigma>)"
      by (rule open_interior)
    have "interior \<sigma> \<subseteq> interior (closure (geotop_polygon_interior J))"
      by (rule interior_maximal[OF hint_sub_closure h_int_open])
    thus ?thesis
      using hxint hregular by (by100 blast)
  qed
  have hI_disj_J: "geotop_polygon_interior J \<inter> J = {}"
    by (rule polygon_interior_disjoint_polygon[OF hJ])
  show False
    using hI_disj_J h_x_in_I hxJ by (by100 blast)
qed

lemma geotop_polygon_boundary_point_in_2simplex_frontier_prefix:
  fixes J \<sigma> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hx\<sigma>: "x \<in> \<sigma>"
  assumes hxJ: "x \<in> J"
  shows "x \<in> frontier \<sigma>"
  (**
    Same bridge in frontier form, for the 2-simplex case used in the
    Theorem 3.3 base case. **)
proof -
  have hx_not_int: "x \<notin> interior \<sigma>"
    by (rule geotop_polygon_boundary_point_in_simplex_not_in_interior_prefix
        [OF hJ h\<sigma>K hK_poly hx\<sigma> hxJ])
  have h\<sigma>closed: "closed \<sigma>"
    by (rule geotop_simplex_dim_closed[OF h\<sigma>2])
  have hx_closure: "x \<in> closure \<sigma>"
    using h\<sigma>closed hx\<sigma> by (by100 simp)
  show ?thesis
    unfolding Elementary_Topology.frontier_def
    using hx_closure hx_not_int by (by100 simp)
qed

lemma geotop_2simplex_polygon_boundary_inter_subset_complex_edge_faces_prefix:
  fixes J \<sigma> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  shows "\<sigma> \<inter> J \<subseteq> \<Union>{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
  (**
    First formal half of the base-case boundary-contact argument: a polygon
    boundary point lying in a 2-simplex lies on one of that simplex's complex
    edge faces. **)
proof
  fix x
  assume hx: "x \<in> \<sigma> \<inter> J"
  have hx\<sigma>: "x \<in> \<sigma>"
    using hx by (by100 simp)
  have hxJ: "x \<in> J"
    using hx by (by100 simp)
  have hx_frontier: "x \<in> frontier \<sigma>"
    by (rule geotop_polygon_boundary_point_in_2simplex_frontier_prefix
        [OF hJ h\<sigma>K h\<sigma>2 hK_poly hx\<sigma> hxJ])
  have hfront_sub:
      "frontier \<sigma> \<subseteq> \<Union>{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
    by (rule geotop_2simplex_frontier_subset_complex_edge_faces_prefix
        [OF hK h\<sigma>K h\<sigma>2])
  show "x \<in> \<Union>{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
    using hfront_sub hx_frontier by (by100 blast)
qed

lemma geotop_polygon_disk_polyhedron_connected_prefix:
  fixes J :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  shows "connected (geotop_polyhedron K)"
  (**
    The disk carrier used in Theorem 3.3 is connected: the polygon interior is
    a connected component of the complement of the polygon, and taking closure
    preserves connectedness. **)
proof -
  have hJ_sph: "geotop_is_n_sphere J
      (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ unfolding geotop_is_polygon_def by (by100 blast)
  have hI_comp: "geotop_polygon_interior J \<in> components (UNIV - J)"
    by (rule polygon_interior_is_HOL_component[OF hJ_sph])
  have hI_conn: "connected (geotop_polygon_interior J)"
    using hI_comp in_components_connected by (by100 blast)
  have hclosure_conn: "connected (closure (geotop_polygon_interior J))"
    by (rule connected_imp_connected_closure[OF hI_conn])
  have hclos_on: "closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)
      = closure (geotop_polygon_interior J)"
    by (rule closure_on_geotop_UNIV_eq_closure)
  show ?thesis
    using hK_poly hclos_on hclosure_conn by (by100 simp)
qed

lemma geotop_polygon_disk_polyhedron_top1_connected_prefix:
  fixes J :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  shows "top1_connected_on (geotop_polyhedron K)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
  (**
    Topological-form wrapper for the connected disk carrier. **)
proof -
  have hconn: "connected (geotop_polyhedron K)"
    by (rule geotop_polygon_disk_polyhedron_connected_prefix[OF hJ hK_poly])
  show ?thesis
    using hconn top1_connected_on_geotop_iff_connected by (by100 blast)
qed

lemma geotop_polygon_disk_complex_connected_prefix:
  fixes J :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  shows "geotop_complex_connected K"
  (**
    The disk triangulation is connected as a complex, not only as its carrier.
    This is the combinatorial connectedness form used when the two-triangle
    base case says the second triangle must attach to the first. **)
proof -
  have hconn: "top1_connected_on (geotop_polyhedron K)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
    by (rule geotop_polygon_disk_polyhedron_top1_connected_prefix[OF hJ hK_poly])
  have hpath: "top1_path_connected_on (geotop_polyhedron K)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
    using Theorem_GT_1_12(2)[OF hK] hconn by (by100 blast)
  show ?thesis
    using Theorem_GT_1_12(1)[OF hK] hpath by (by100 blast)
qed

lemma geotop_polygon_disk_polyhedron_frontier_prefix:
  fixes J :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  shows "frontier (geotop_polyhedron K) = J"
  (**
    Book identity for Theorem 3.3: the frontier of the triangulated disk
    carrier is the original polygon. **)
proof -
  let ?I = "geotop_polygon_interior J"
  have hclos_on: "closure_on UNIV geotop_euclidean_topology ?I = closure ?I"
    by (rule closure_on_geotop_UNIV_eq_closure)
  have hpoly_HOL: "geotop_polyhedron K = closure ?I"
    using hK_poly hclos_on by (by100 simp)
  have hclosure: "closure ?I = ?I \<union> J"
    by (rule polygon_interior_closure_eq[OF hJ])
  have hregular: "interior (closure ?I) = ?I"
    by (rule geotop_polygon_interior_regular_closed_prefix[OF hJ])
  have hdisj: "?I \<inter> J = {}"
    by (rule polygon_interior_disjoint_polygon[OF hJ])
  have hfront: "frontier (closure ?I) = J"
  proof -
    have "frontier (closure ?I) = closure (closure ?I) - interior (closure ?I)"
      unfolding Elementary_Topology.frontier_def by (by100 simp)
    also have "... = closure ?I - ?I"
      using hregular by (by100 simp)
    also have "... = J"
      using hclosure hdisj by (by100 blast)
    finally show ?thesis .
  qed
  show ?thesis
    using hpoly_HOL hfront by (by100 simp)
qed

lemma geotop_polygon_disk_polyhedron_geotop_frontier_prefix:
  fixes J :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  shows "geotop_frontier UNIV geotop_euclidean_topology (geotop_polyhedron K) = J"
  (**
    Geotop-frontier form of the same disk-carrier boundary identity. **)
proof -
  have hfront: "frontier (geotop_polyhedron K) = J"
    by (rule geotop_polygon_disk_polyhedron_frontier_prefix[OF hJ hK_poly])
  show ?thesis
    using hfront geotop_frontier_UNIV_eq_frontier[of "geotop_polyhedron K"]
    by (by100 simp)
qed

lemma geotop_two_triangle_boundary_contact_edges_cover_prefix:
  fixes J \<sigma> \<tau> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hT_eq: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2} = {\<sigma>, \<tau>}"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  shows "\<sigma> \<inter> J \<subseteq> \<Union>{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J}"
  (**
    Book base case, exactly two 2-simplexes: the part of a triangle on the
    polygon boundary is a union of whole edge faces of that triangle.  This is
    the strengthened form of the preceding frontier-cover lemma needed to make
    the definition of free 2-simplex literal. **)
  sorry

lemma geotop_two_triangle_not_all_boundary_edges_prefix:
  fixes J \<sigma> \<tau> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hT_eq: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2} = {\<sigma>, \<tau>}"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  shows "card {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J} \<noteq> 3"
  (**
    Book base case, exactly two 2-simplexes: one triangle cannot have all
    three edge faces lying on the polygon boundary, since the second
    2-simplex must attach across some edge in the disk triangulation. **)
  sorry

lemma geotop_polygon_disk_two_boundary_2simplexes_prefix:
  fixes J :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hT_gt2: "card {\<rho>\<in>K. geotop_simplex_dim \<rho> 2} > 2"
  shows "\<exists>\<sigma> \<tau> e\<^sub>\<sigma> e\<^sub>\<tau>. \<sigma> \<in> K \<and> \<tau> \<in> K \<and> \<sigma> \<noteq> \<tau>
     \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_simplex_dim \<tau> 2
     \<and> geotop_is_edge e\<^sub>\<sigma> \<and> geotop_is_face e\<^sub>\<sigma> \<sigma>
     \<and> e\<^sub>\<sigma> \<subseteq> geotop_frontier UNIV geotop_euclidean_topology
          (geotop_polyhedron K)
     \<and> geotop_is_edge e\<^sub>\<tau> \<and> geotop_is_face e\<^sub>\<tau> \<tau>
     \<and> e\<^sub>\<tau> \<subseteq> geotop_frontier UNIV geotop_euclidean_topology
          (geotop_polyhedron K)"
  (**
    Book induction step in Theorem 3.3: when the disk triangulation has more
    than two 2-simplexes, at least two 2-simplexes each have an edge in
    \<open>Fr |K|\<close>.  The book does not require these two simplexes to share that
    boundary edge. **)
  sorry

lemma geotop_polygon_disk_frontier_edge_subset_polygon_prefix:
  fixes J e :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes he_front: "e \<subseteq> geotop_frontier UNIV geotop_euclidean_topology
      (geotop_polyhedron K)"
  shows "e \<subseteq> J"
  (**
    Rewriting form of the disk-carrier identity \<open>Fr |K| = J\<close>, used when
    the book says a simplex has an edge in \<open>Fr |K|\<close>. **)
proof -
  have hfront: "geotop_frontier UNIV geotop_euclidean_topology
      (geotop_polyhedron K) = J"
    by (rule geotop_polygon_disk_polyhedron_geotop_frontier_prefix[OF hJ hK_poly])
  show ?thesis
    using he_front hfront by (by100 simp)
qed

lemma geotop_polygon_disk_boundary_edge_in_selected_edges_prefix:
  fixes J e \<sigma> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hface: "geotop_is_face e \<sigma>"
  assumes he_front: "e \<subseteq> geotop_frontier UNIV geotop_euclidean_topology
      (geotop_polyhedron K)"
  shows "e \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J}"
  (**
    If the book's chosen boundary edge is a face of \<open>\<sigma>\<close>, then it is one
    of the selected boundary edges used in the formal free-simplex predicate. **)
proof -
  have heK: "e \<in> K"
    using geotop_is_complex_face_closed[OF hK] h\<sigma>K hface by (by100 blast)
  have heJ: "e \<subseteq> J"
    by (rule geotop_polygon_disk_frontier_edge_subset_polygon_prefix
        [OF hJ hK_poly he_front])
  show ?thesis
    using heK hedge hface heJ by (by100 simp)
qed

lemma geotop_polygon_disk_two_selected_boundary_2simplexes_prefix:
  fixes J :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hT_gt2: "card {\<rho>\<in>K. geotop_simplex_dim \<rho> 2} > 2"
  shows "\<exists>\<sigma> \<tau> e\<^sub>\<sigma> e\<^sub>\<tau>. \<sigma> \<in> K \<and> \<tau> \<in> K \<and> \<sigma> \<noteq> \<tau>
     \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_simplex_dim \<tau> 2
     \<and> e\<^sub>\<sigma> \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J}
     \<and> e\<^sub>\<tau> \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J}"
  (**
    Formal set-membership version of the book's two boundary-simplex step,
    ready for the free-simplex edge-set bookkeeping. **)
proof -
  obtain \<sigma> \<tau> e\<^sub>\<sigma> e\<^sub>\<tau>
    where h\<sigma>K: "\<sigma> \<in> K" and h\<tau>K: "\<tau> \<in> K" and h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
      and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
      and h\<tau>2: "geotop_simplex_dim \<tau> 2"
      and he\<sigma>edge: "geotop_is_edge e\<^sub>\<sigma>"
      and he\<sigma>face: "geotop_is_face e\<^sub>\<sigma> \<sigma>"
      and he\<sigma>front: "e\<^sub>\<sigma> \<subseteq> geotop_frontier UNIV geotop_euclidean_topology
          (geotop_polyhedron K)"
      and he\<tau>edge: "geotop_is_edge e\<^sub>\<tau>"
      and he\<tau>face: "geotop_is_face e\<^sub>\<tau> \<tau>"
      and he\<tau>front: "e\<^sub>\<tau> \<subseteq> geotop_frontier UNIV geotop_euclidean_topology
          (geotop_polyhedron K)"
    using geotop_polygon_disk_two_boundary_2simplexes_prefix
        [OF hJ hK hK_poly hT_gt2]
    by (by100 blast)
  have he\<sigma>sel:
      "e\<^sub>\<sigma> \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J}"
    by (rule geotop_polygon_disk_boundary_edge_in_selected_edges_prefix
        [OF hJ hK hK_poly h\<sigma>K he\<sigma>edge he\<sigma>face he\<sigma>front])
  have he\<tau>sel:
      "e\<^sub>\<tau> \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J}"
    by (rule geotop_polygon_disk_boundary_edge_in_selected_edges_prefix
        [OF hJ hK hK_poly h\<tau>K he\<tau>edge he\<tau>face he\<tau>front])
  show ?thesis
  proof (rule exI[where x = \<sigma>])
    show "\<exists>\<tau> e\<^sub>\<sigma> e\<^sub>\<tau>. \<sigma> \<in> K \<and> \<tau> \<in> K \<and> \<sigma> \<noteq> \<tau> \<and>
        geotop_simplex_dim \<sigma> 2 \<and> geotop_simplex_dim \<tau> 2 \<and>
        e\<^sub>\<sigma> \<in> {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} \<and>
        e\<^sub>\<tau> \<in> {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J}"
    proof (rule exI[where x = \<tau>])
      show "\<exists>e\<^sub>\<sigma> e\<^sub>\<tau>. \<sigma> \<in> K \<and> \<tau> \<in> K \<and> \<sigma> \<noteq> \<tau> \<and>
          geotop_simplex_dim \<sigma> 2 \<and> geotop_simplex_dim \<tau> 2 \<and>
          e\<^sub>\<sigma> \<in> {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} \<and>
          e\<^sub>\<tau> \<in> {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J}"
      proof (rule exI[where x = e\<^sub>\<sigma>])
        show "\<exists>e\<^sub>\<tau>. \<sigma> \<in> K \<and> \<tau> \<in> K \<and> \<sigma> \<noteq> \<tau> \<and>
            geotop_simplex_dim \<sigma> 2 \<and> geotop_simplex_dim \<tau> 2 \<and>
            e\<^sub>\<sigma> \<in> {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} \<and>
            e\<^sub>\<tau> \<in> {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J}"
        proof (rule exI[where x = e\<^sub>\<tau>])
          show "\<sigma> \<in> K \<and> \<tau> \<in> K \<and> \<sigma> \<noteq> \<tau> \<and>
              geotop_simplex_dim \<sigma> 2 \<and> geotop_simplex_dim \<tau> 2 \<and>
              e\<^sub>\<sigma> \<in> {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} \<and>
              e\<^sub>\<tau> \<in> {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J}"
            by (intro conjI h\<sigma>K h\<tau>K h\<sigma>\<tau> h\<sigma>2 h\<tau>2 he\<sigma>sel he\<tau>sel)
        qed
      qed
    qed
  qed
qed

lemma geotop_polygon_disk_two_nonempty_boundary_edge_sets_prefix:
  fixes J :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hT_gt2: "card {\<rho>\<in>K. geotop_simplex_dim \<rho> 2} > 2"
  shows "\<exists>\<sigma> \<tau>. \<sigma> \<in> K \<and> \<tau> \<in> K \<and> \<sigma> \<noteq> \<tau>
     \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_simplex_dim \<tau> 2
     \<and> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} \<noteq> {}
     \<and> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J} \<noteq> {}"
  (**
    Nonempty-edge-set form of the same book step: the two boundary 2-simplexes
    each contribute at least one selected boundary edge. **)
proof -
  have hselected:
    "\<exists>\<sigma> \<tau> e\<^sub>\<sigma> e\<^sub>\<tau>. \<sigma> \<in> K \<and> \<tau> \<in> K \<and> \<sigma> \<noteq> \<tau>
     \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_simplex_dim \<tau> 2
     \<and> e\<^sub>\<sigma> \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J}
     \<and> e\<^sub>\<tau> \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J}"
    by (rule geotop_polygon_disk_two_selected_boundary_2simplexes_prefix
        [OF hJ hK hK_poly hT_gt2])
  obtain \<sigma> \<tau> e\<^sub>\<sigma> e\<^sub>\<tau>
    where h\<sigma>K: "\<sigma> \<in> K" and h\<tau>K: "\<tau> \<in> K" and h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
      and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
      and h\<tau>2: "geotop_simplex_dim \<tau> 2"
      and he\<sigma>sel:
        "e\<^sub>\<sigma> \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J}"
      and he\<tau>sel:
        "e\<^sub>\<tau> \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J}"
    using hselected by (elim exE conjE)
  have hE\<sigma>ne: "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} \<noteq> {}"
  proof
    assume hempty: "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} = {}"
    show False
      using he\<sigma>sel hempty by (by100 simp)
  qed
  have hE\<tau>ne: "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J} \<noteq> {}"
  proof
    assume hempty: "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J} = {}"
    show False
      using he\<tau>sel hempty by (by100 simp)
  qed
  show ?thesis
  proof (rule exI[where x = \<sigma>])
    show "\<exists>\<tau>. \<sigma> \<in> K \<and> \<tau> \<in> K \<and> \<sigma> \<noteq> \<tau> \<and>
        geotop_simplex_dim \<sigma> 2 \<and> geotop_simplex_dim \<tau> 2 \<and>
        {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} \<noteq> {} \<and>
        {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J} \<noteq> {}"
    proof (rule exI[where x = \<tau>])
      show "\<sigma> \<in> K \<and> \<tau> \<in> K \<and> \<sigma> \<noteq> \<tau> \<and>
          geotop_simplex_dim \<sigma> 2 \<and> geotop_simplex_dim \<tau> 2 \<and>
          {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} \<noteq> {} \<and>
          {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J} \<noteq> {}"
        by (intro conjI h\<sigma>K h\<tau>K h\<sigma>\<tau> h\<sigma>2 h\<tau>2 hE\<sigma>ne hE\<tau>ne)
    qed
  qed
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
    have hSC_induction_general:
      "\<And>J' K. geotop_is_polygon J' \<Longrightarrow>
            geotop_is_complex K \<Longrightarrow> finite K \<Longrightarrow>
            geotop_polyhedron K = closure_on UNIV geotop_euclidean_topology
                                    (geotop_polygon_interior J') \<Longrightarrow>
            card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2} > 1 \<Longrightarrow>
            card {\<sigma>\<^sub>2\<in>K. geotop_free_2_simplex K J' \<sigma>\<^sub>2} \<ge> 2"
    proof -
      fix J' :: "(real^2) set" and K :: "(real^2) set set"
      assume hJ': "geotop_is_polygon J'"
      assume hK': "geotop_is_complex K"
      assume hK_fin': "finite K"
      assume hK_poly': "geotop_polyhedron K = closure_on UNIV geotop_euclidean_topology
                                    (geotop_polygon_interior J')"
      assume hcard': "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2} > 1"
      let ?T = "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2}"
      let ?F = "{\<sigma>\<^sub>2\<in>K. geotop_free_2_simplex K J' \<sigma>\<^sub>2}"
      have hT_fin: "finite ?T"
        using hK_fin' by (by100 simp)
      have hbase_two:
        "card ?T = 2 \<Longrightarrow> card ?F \<ge> 2"
      proof -
        assume hT_card2: "card ?T = 2"
        have hT_obtain:
          "\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau> \<and> ?T = {\<sigma>, \<tau>}"
        proof -
          have "\<exists>\<sigma> \<tau>. ?T = {\<sigma>, \<tau>} \<and> \<sigma> \<noteq> \<tau>"
            using hT_card2 card_2_iff[of ?T] by (by100 simp)
          then obtain \<sigma> \<tau> where hT: "?T = {\<sigma>, \<tau>}" and hneq: "\<sigma> \<noteq> \<tau>"
            by (elim exE conjE)
          show ?thesis
            using hT hneq by (by100 blast)
        qed
        obtain \<sigma> \<tau> where hpair: "\<sigma> \<noteq> \<tau> \<and> ?T = {\<sigma>, \<tau>}"
          using hT_obtain by (elim exE)
        have h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
          using hpair by (by100 simp)
        have hT_eq: "?T = {\<sigma>, \<tau>}"
          using hpair by (by100 simp)
        have hpair_swap_eq: "{\<sigma>, \<tau>} = {\<tau>, \<sigma>}"
          by (rule insert_commute)
        have hT_eq_swap: "?T = {\<tau>, \<sigma>}"
          using hT_eq hpair_swap_eq by (by100 simp)
        have h\<sigma>T: "\<sigma> \<in> ?T"
          using hT_eq by (by100 simp)
        have h\<tau>T: "\<tau> \<in> ?T"
          using hT_eq by (by100 simp)
        have h\<tau>\<sigma>: "\<tau> \<noteq> \<sigma>"
          using h\<sigma>\<tau> by (by100 simp)
        \<comment> \<open>Book base case: with exactly two 2-simplexes, each has all of its
          boundary contact with \<open>J'\<close> in one or two edge faces, so both are free.\<close>
        have h\<sigma>free: "geotop_free_2_simplex K J' \<sigma>"
        proof -
          have h\<sigma>K: "\<sigma> \<in> K"
            using h\<sigma>T by (by100 simp)
          have h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
            using h\<sigma>T by (by100 simp)
          have h\<sigma>contact:
            "\<exists>E. E \<subseteq> K \<and>
              (E = {} \<or>
               (\<exists>e. E = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J') \<or>
               (\<exists>e1 e2. E = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                  geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                  geotop_is_face e1 \<sigma> \<and> geotop_is_face e2 \<sigma> \<and>
                  e1 \<subseteq> J' \<and> e2 \<subseteq> J')) \<and>
              \<sigma> \<inter> J' = \<Union>E"
          proof -
            let ?E\<sigma> = "{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J'}"
            have hE\<sigma>_subset: "?E\<sigma> \<subseteq> K"
              by (by100 simp)
            have hE\<sigma>_fin: "finite ?E\<sigma>"
              using hK_fin' by (by100 simp)
            have hE\<sigma>_card_le2: "card ?E\<sigma> \<le> 2"
            proof -
              have hE\<sigma>_card_le3: "card ?E\<sigma> \<le> 3"
              proof -
                let ?A = "{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
                have hA: "finite ?A \<and> card ?A \<le> 3"
                  by (rule geotop_2simplex_complex_edge_faces_card_le3_prefix[OF h\<sigma>2])
                have hA_fin: "finite ?A"
                  using hA by (by100 blast)
                have hA_card: "card ?A \<le> 3"
                  using hA by (by100 blast)
                have hE_sub_A: "?E\<sigma> \<subseteq> ?A"
                  by (by100 blast)
                have "card ?E\<sigma> \<le> card ?A"
                  by (rule card_mono[OF hA_fin hE_sub_A])
                thus ?thesis
                  using hA_card by (by100 linarith)
              qed
              have hE\<sigma>_card_ne3: "card ?E\<sigma> \<noteq> 3"
              proof
                assume hE\<sigma>_card3: "card ?E\<sigma> = 3"
                have hE\<sigma>_all_boundary:
                    "{e. geotop_is_edge e \<and> geotop_is_face e \<sigma>} = ?E\<sigma>"
                  by (rule geotop_2simplex_three_selected_edge_faces_all_prefix
                      [OF h\<sigma>2 hE\<sigma>_card3])
                have hE\<sigma>_not3: "card ?E\<sigma> \<noteq> 3"
                  by (rule geotop_two_triangle_not_all_boundary_edges_prefix
                      [OF hJ' hK' hK_poly' hT_eq h\<sigma>K h\<sigma>2 h\<sigma>\<tau>])
                show False
                  using hE\<sigma>_not3 hE\<sigma>_card3 by (by100 blast)
              qed
              show ?thesis
                using hE\<sigma>_card_le3 hE\<sigma>_card_ne3 by (by100 linarith)
            qed
            have hE\<sigma>_allowed:
              "?E\<sigma> = {} \<or>
               (\<exists>e. ?E\<sigma> = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J') \<or>
               (\<exists>e1 e2. ?E\<sigma> = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                  geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                  geotop_is_face e1 \<sigma> \<and> geotop_is_face e2 \<sigma> \<and>
                  e1 \<subseteq> J' \<and> e2 \<subseteq> J')"
            proof -
              have hcases: "card ?E\<sigma> = 0 \<or> card ?E\<sigma> = 1 \<or> card ?E\<sigma> = 2"
                using hE\<sigma>_card_le2 by (by100 linarith)
              show ?thesis
              proof (cases "card ?E\<sigma> = 0")
                case True
                have "?E\<sigma> = {}"
                  using hE\<sigma>_fin True by (by100 simp)
                thus ?thesis by (by100 simp)
              next
                case False
                show ?thesis
                proof (cases "card ?E\<sigma> = 1")
                  case True
                  have hsingle: "\<exists>e. ?E\<sigma> = {e}"
                    using True card_1_singleton_iff[of ?E\<sigma>] by (by100 simp)
                  obtain e where hE: "?E\<sigma> = {e}"
                    using hsingle by (elim exE)
                  have he: "e \<in> ?E\<sigma>"
                    using hE by (by100 simp)
                  have hedge: "geotop_is_edge e"
                    using he by (by100 simp)
                  have hface: "geotop_is_face e \<sigma>"
                    using he by (by100 simp)
                  have hsub: "e \<subseteq> J'"
                    using he by (by100 simp)
                  show ?thesis
                  proof (rule disjI2)
                    show "(\<exists>e. ?E\<sigma> = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J') \<or>
                      (\<exists>e1 e2. ?E\<sigma> = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                         geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                         geotop_is_face e1 \<sigma> \<and> geotop_is_face e2 \<sigma> \<and>
                         e1 \<subseteq> J' \<and> e2 \<subseteq> J')"
                    proof (rule disjI1)
                      show "\<exists>e. ?E\<sigma> = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J'"
                      proof (rule exI[where x = e])
                        show "?E\<sigma> = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J'"
                          by (intro conjI hE hedge hface hsub)
                      qed
                    qed
                  qed
                next
                  case False
                  have hcard2: "card ?E\<sigma> = 2"
                    using hcases \<open>card ?E\<sigma> \<noteq> 0\<close> False by (by100 simp)
                  have hdouble: "\<exists>e1 e2. ?E\<sigma> = {e1, e2} \<and> e1 \<noteq> e2"
                    using hcard2 card_2_iff[of ?E\<sigma>] by (by100 simp)
                  obtain e1 e2 where hE: "?E\<sigma> = {e1, e2}" and hneq: "e1 \<noteq> e2"
                    using hdouble by (elim exE conjE)
                  have he1: "e1 \<in> ?E\<sigma>"
                    using hE by (by100 simp)
                  have he2: "e2 \<in> ?E\<sigma>"
                    using hE by (by100 simp)
                  have he1_edge: "geotop_is_edge e1"
                    using he1 by (by100 simp)
                  have he2_edge: "geotop_is_edge e2"
                    using he2 by (by100 simp)
                  have he1_face: "geotop_is_face e1 \<sigma>"
                    using he1 by (by100 simp)
                  have he2_face: "geotop_is_face e2 \<sigma>"
                    using he2 by (by100 simp)
                  have he1_sub: "e1 \<subseteq> J'"
                    using he1 by (by100 simp)
                  have he2_sub: "e2 \<subseteq> J'"
                    using he2 by (by100 simp)
                  show ?thesis
                  proof (rule disjI2)
                    show "(\<exists>e. ?E\<sigma> = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J') \<or>
                      (\<exists>e1 e2. ?E\<sigma> = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                         geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                         geotop_is_face e1 \<sigma> \<and> geotop_is_face e2 \<sigma> \<and>
                         e1 \<subseteq> J' \<and> e2 \<subseteq> J')"
                    proof (rule disjI2)
                      show "\<exists>e1 e2. ?E\<sigma> = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                        geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                        geotop_is_face e1 \<sigma> \<and> geotop_is_face e2 \<sigma> \<and>
                        e1 \<subseteq> J' \<and> e2 \<subseteq> J'"
                      proof (rule exI[where x = e1], rule exI[where x = e2])
                        show "?E\<sigma> = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                          geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                          geotop_is_face e1 \<sigma> \<and> geotop_is_face e2 \<sigma> \<and>
                          e1 \<subseteq> J' \<and> e2 \<subseteq> J'"
                          by (intro conjI hE hneq he1_edge he2_edge he1_face he2_face he1_sub he2_sub)
                      qed
                    qed
                  qed
                qed
              qed
            qed
            have h\<sigma>J_eq: "\<sigma> \<inter> J' = \<Union>?E\<sigma>"
            proof
              show "\<sigma> \<inter> J' \<subseteq> \<Union>?E\<sigma>"
                by (rule geotop_two_triangle_boundary_contact_edges_cover_prefix
                    [OF hJ' hK' hK_poly' hT_eq h\<sigma>K h\<sigma>2 h\<sigma>\<tau>])
              show "\<Union>?E\<sigma> \<subseteq> \<sigma> \<inter> J'"
              proof
                fix x
                assume hx: "x \<in> \<Union>?E\<sigma>"
                then obtain e where heE: "e \<in> ?E\<sigma>" and hxe: "x \<in> e"
                  by (by100 blast)
                have hface: "geotop_is_face e \<sigma>"
                  using heE by (by100 simp)
                have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
                  by (rule geotop_is_face_imp_subset_prefix[OF hface])
                have he_sub_J: "e \<subseteq> J'"
                  using heE by (by100 simp)
                show "x \<in> \<sigma> \<inter> J'"
                  using hxe he_sub_\<sigma> he_sub_J by (by100 blast)
              qed
            qed
            show ?thesis
            proof (rule exI[where x = ?E\<sigma>])
              show "?E\<sigma> \<subseteq> K \<and>
                (?E\<sigma> = {} \<or>
                 (\<exists>e. ?E\<sigma> = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J') \<or>
                 (\<exists>e1 e2. ?E\<sigma> = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                    geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                    geotop_is_face e1 \<sigma> \<and> geotop_is_face e2 \<sigma> \<and>
                    e1 \<subseteq> J' \<and> e2 \<subseteq> J')) \<and>
                \<sigma> \<inter> J' = \<Union>?E\<sigma>"
                by (intro conjI hE\<sigma>_subset hE\<sigma>_allowed h\<sigma>J_eq)
            qed
          qed
          show ?thesis
            unfolding geotop_free_2_simplex_def
            by (intro conjI h\<sigma>K h\<sigma>2 h\<sigma>contact)
        qed
        have h\<tau>free: "geotop_free_2_simplex K J' \<tau>"
        proof -
          have h\<tau>K: "\<tau> \<in> K"
            using h\<tau>T by (by100 simp)
          have h\<tau>2: "geotop_simplex_dim \<tau> 2"
            using h\<tau>T by (by100 simp)
          have h\<tau>contact:
            "\<exists>E. E \<subseteq> K \<and>
              (E = {} \<or>
               (\<exists>e. E = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<tau> \<and> e \<subseteq> J') \<or>
               (\<exists>e1 e2. E = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                  geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                  geotop_is_face e1 \<tau> \<and> geotop_is_face e2 \<tau> \<and>
                  e1 \<subseteq> J' \<and> e2 \<subseteq> J')) \<and>
              \<tau> \<inter> J' = \<Union>E"
          proof -
            let ?E\<tau> = "{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<tau> \<and> e \<subseteq> J'}"
            have hE\<tau>_subset: "?E\<tau> \<subseteq> K"
              by (by100 simp)
            have hE\<tau>_fin: "finite ?E\<tau>"
              using hK_fin' by (by100 simp)
            have hE\<tau>_card_le2: "card ?E\<tau> \<le> 2"
            proof -
              have hE\<tau>_card_le3: "card ?E\<tau> \<le> 3"
              proof -
                let ?A = "{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<tau>}"
                have hA: "finite ?A \<and> card ?A \<le> 3"
                  by (rule geotop_2simplex_complex_edge_faces_card_le3_prefix[OF h\<tau>2])
                have hA_fin: "finite ?A"
                  using hA by (by100 blast)
                have hA_card: "card ?A \<le> 3"
                  using hA by (by100 blast)
                have hE_sub_A: "?E\<tau> \<subseteq> ?A"
                  by (by100 blast)
                have "card ?E\<tau> \<le> card ?A"
                  by (rule card_mono[OF hA_fin hE_sub_A])
                thus ?thesis
                  using hA_card by (by100 linarith)
              qed
              have hE\<tau>_card_ne3: "card ?E\<tau> \<noteq> 3"
              proof
                assume hE\<tau>_card3: "card ?E\<tau> = 3"
                have hE\<tau>_all_boundary:
                    "{e. geotop_is_edge e \<and> geotop_is_face e \<tau>} = ?E\<tau>"
                  by (rule geotop_2simplex_three_selected_edge_faces_all_prefix
                      [OF h\<tau>2 hE\<tau>_card3])
                have hE\<tau>_not3: "card ?E\<tau> \<noteq> 3"
                  by (rule geotop_two_triangle_not_all_boundary_edges_prefix
                      [OF hJ' hK' hK_poly' hT_eq_swap h\<tau>K h\<tau>2 h\<tau>\<sigma>])
                show False
                  using hE\<tau>_not3 hE\<tau>_card3 by (by100 blast)
              qed
              show ?thesis
                using hE\<tau>_card_le3 hE\<tau>_card_ne3 by (by100 linarith)
            qed
            have hE\<tau>_allowed:
              "?E\<tau> = {} \<or>
               (\<exists>e. ?E\<tau> = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<tau> \<and> e \<subseteq> J') \<or>
               (\<exists>e1 e2. ?E\<tau> = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                  geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                  geotop_is_face e1 \<tau> \<and> geotop_is_face e2 \<tau> \<and>
                  e1 \<subseteq> J' \<and> e2 \<subseteq> J')"
            proof -
              have hcases: "card ?E\<tau> = 0 \<or> card ?E\<tau> = 1 \<or> card ?E\<tau> = 2"
                using hE\<tau>_card_le2 by (by100 linarith)
              show ?thesis
              proof (cases "card ?E\<tau> = 0")
                case True
                have "?E\<tau> = {}"
                  using hE\<tau>_fin True by (by100 simp)
                thus ?thesis by (by100 simp)
              next
                case False
                show ?thesis
                proof (cases "card ?E\<tau> = 1")
                  case True
                  have hsingle: "\<exists>e. ?E\<tau> = {e}"
                    using True card_1_singleton_iff[of ?E\<tau>] by (by100 simp)
                  obtain e where hE: "?E\<tau> = {e}"
                    using hsingle by (elim exE)
                  have he: "e \<in> ?E\<tau>"
                    using hE by (by100 simp)
                  have hedge: "geotop_is_edge e"
                    using he by (by100 simp)
                  have hface: "geotop_is_face e \<tau>"
                    using he by (by100 simp)
                  have hsub: "e \<subseteq> J'"
                    using he by (by100 simp)
                  show ?thesis
                  proof (rule disjI2)
                    show "(\<exists>e. ?E\<tau> = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<tau> \<and> e \<subseteq> J') \<or>
                      (\<exists>e1 e2. ?E\<tau> = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                         geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                         geotop_is_face e1 \<tau> \<and> geotop_is_face e2 \<tau> \<and>
                         e1 \<subseteq> J' \<and> e2 \<subseteq> J')"
                    proof (rule disjI1)
                      show "\<exists>e. ?E\<tau> = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<tau> \<and> e \<subseteq> J'"
                      proof (rule exI[where x = e])
                        show "?E\<tau> = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<tau> \<and> e \<subseteq> J'"
                          by (intro conjI hE hedge hface hsub)
                      qed
                    qed
                  qed
                next
                  case False
                  have hcard2: "card ?E\<tau> = 2"
                    using hcases \<open>card ?E\<tau> \<noteq> 0\<close> False by (by100 simp)
                  have hdouble: "\<exists>e1 e2. ?E\<tau> = {e1, e2} \<and> e1 \<noteq> e2"
                    using hcard2 card_2_iff[of ?E\<tau>] by (by100 simp)
                  obtain e1 e2 where hE: "?E\<tau> = {e1, e2}" and hneq: "e1 \<noteq> e2"
                    using hdouble by (elim exE conjE)
                  have he1: "e1 \<in> ?E\<tau>"
                    using hE by (by100 simp)
                  have he2: "e2 \<in> ?E\<tau>"
                    using hE by (by100 simp)
                  have he1_edge: "geotop_is_edge e1"
                    using he1 by (by100 simp)
                  have he2_edge: "geotop_is_edge e2"
                    using he2 by (by100 simp)
                  have he1_face: "geotop_is_face e1 \<tau>"
                    using he1 by (by100 simp)
                  have he2_face: "geotop_is_face e2 \<tau>"
                    using he2 by (by100 simp)
                  have he1_sub: "e1 \<subseteq> J'"
                    using he1 by (by100 simp)
                  have he2_sub: "e2 \<subseteq> J'"
                    using he2 by (by100 simp)
                  show ?thesis
                  proof (rule disjI2)
                    show "(\<exists>e. ?E\<tau> = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<tau> \<and> e \<subseteq> J') \<or>
                      (\<exists>e1 e2. ?E\<tau> = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                         geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                         geotop_is_face e1 \<tau> \<and> geotop_is_face e2 \<tau> \<and>
                         e1 \<subseteq> J' \<and> e2 \<subseteq> J')"
                    proof (rule disjI2)
                      show "\<exists>e1 e2. ?E\<tau> = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                        geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                        geotop_is_face e1 \<tau> \<and> geotop_is_face e2 \<tau> \<and>
                        e1 \<subseteq> J' \<and> e2 \<subseteq> J'"
                      proof (rule exI[where x = e1], rule exI[where x = e2])
                        show "?E\<tau> = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                          geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                          geotop_is_face e1 \<tau> \<and> geotop_is_face e2 \<tau> \<and>
                          e1 \<subseteq> J' \<and> e2 \<subseteq> J'"
                          by (intro conjI hE hneq he1_edge he2_edge he1_face he2_face he1_sub he2_sub)
                      qed
                    qed
                  qed
                qed
              qed
            qed
            have h\<tau>J_eq: "\<tau> \<inter> J' = \<Union>?E\<tau>"
            proof
              show "\<tau> \<inter> J' \<subseteq> \<Union>?E\<tau>"
                by (rule geotop_two_triangle_boundary_contact_edges_cover_prefix
                    [OF hJ' hK' hK_poly' hT_eq_swap h\<tau>K h\<tau>2 h\<tau>\<sigma>])
              show "\<Union>?E\<tau> \<subseteq> \<tau> \<inter> J'"
              proof
                fix x
                assume hx: "x \<in> \<Union>?E\<tau>"
                then obtain e where heE: "e \<in> ?E\<tau>" and hxe: "x \<in> e"
                  by (by100 blast)
                have hface: "geotop_is_face e \<tau>"
                  using heE by (by100 simp)
                have he_sub_\<tau>: "e \<subseteq> \<tau>"
                  by (rule geotop_is_face_imp_subset_prefix[OF hface])
                have he_sub_J: "e \<subseteq> J'"
                  using heE by (by100 simp)
                show "x \<in> \<tau> \<inter> J'"
                  using hxe he_sub_\<tau> he_sub_J by (by100 blast)
              qed
            qed
            show ?thesis
            proof (rule exI[where x = ?E\<tau>])
              show "?E\<tau> \<subseteq> K \<and>
                (?E\<tau> = {} \<or>
                 (\<exists>e. ?E\<tau> = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<tau> \<and> e \<subseteq> J') \<or>
                 (\<exists>e1 e2. ?E\<tau> = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                    geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                    geotop_is_face e1 \<tau> \<and> geotop_is_face e2 \<tau> \<and>
                    e1 \<subseteq> J' \<and> e2 \<subseteq> J')) \<and>
                \<tau> \<inter> J' = \<Union>?E\<tau>"
                by (intro conjI hE\<tau>_subset hE\<tau>_allowed h\<tau>J_eq)
            qed
          qed
          show ?thesis
            unfolding geotop_free_2_simplex_def
            by (intro conjI h\<tau>K h\<tau>2 h\<tau>contact)
        qed
        have hF_fin: "finite ?F"
          using hK_fin' by (by100 simp)
        have hpair_sub: "{\<sigma>, \<tau>} \<subseteq> ?F"
          using h\<sigma>T h\<tau>T h\<sigma>free h\<tau>free by (by100 blast)
        have hpair_card: "card {\<sigma>, \<tau>} = 2"
          using h\<sigma>\<tau> by (by100 simp)
        have "card {\<sigma>, \<tau>} \<le> card ?F"
          by (rule card_mono[OF hF_fin hpair_sub])
        thus "card ?F \<ge> 2"
          using hpair_card by (by100 simp)
      qed
      have hstep_more_than_two:
        "card ?T > 2 \<Longrightarrow> card ?F \<ge> 2"
      proof -
        assume hT_gt2: "card ?T > 2"
        \<comment> \<open>Book step: choose two 2-simplexes with an edge in \<open>Fr |K|\<close>.\<close>
        have hboundary_pair:
          "\<exists>\<sigma> \<tau> e\<^sub>\<sigma> e\<^sub>\<tau>. \<sigma> \<in> K \<and> \<tau> \<in> K \<and> \<sigma> \<noteq> \<tau>
             \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_simplex_dim \<tau> 2
             \<and> geotop_is_edge e\<^sub>\<sigma> \<and> geotop_is_face e\<^sub>\<sigma> \<sigma>
             \<and> e\<^sub>\<sigma> \<subseteq> geotop_frontier UNIV geotop_euclidean_topology
                    (geotop_polyhedron K)
             \<and> geotop_is_edge e\<^sub>\<tau> \<and> geotop_is_face e\<^sub>\<tau> \<tau>
             \<and> e\<^sub>\<tau> \<subseteq> geotop_frontier UNIV geotop_euclidean_topology
                    (geotop_polyhedron K)"
          by (rule geotop_polygon_disk_two_boundary_2simplexes_prefix
              [OF hJ' hK' hK_poly' hT_gt2])
        have hboundary_edge_sets:
          "\<exists>\<sigma> \<tau>. \<sigma> \<in> K \<and> \<tau> \<in> K \<and> \<sigma> \<noteq> \<tau>
             \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_simplex_dim \<tau> 2
             \<and> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J'} \<noteq> {}
             \<and> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J'} \<noteq> {}"
          by (rule geotop_polygon_disk_two_nonempty_boundary_edge_sets_prefix
              [OF hJ' hK' hK_poly' hT_gt2])
        \<comment> \<open>If both boundary simplexes are free, the two free simplexes are already found.\<close>
        have hboth_free_case:
          "\<And>\<sigma> \<tau>. \<sigma> \<in> K \<Longrightarrow> \<tau> \<in> K \<Longrightarrow> \<sigma> \<noteq> \<tau> \<Longrightarrow>
             geotop_free_2_simplex K J' \<sigma> \<Longrightarrow>
             geotop_free_2_simplex K J' \<tau> \<Longrightarrow>
             card ?F \<ge> 2"
        proof -
          fix \<sigma> \<tau>
          assume h\<sigma>K: "\<sigma> \<in> K"
          assume h\<tau>K: "\<tau> \<in> K"
          assume h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
          assume h\<sigma>free: "geotop_free_2_simplex K J' \<sigma>"
          assume h\<tau>free: "geotop_free_2_simplex K J' \<tau>"
          have hF_fin: "finite ?F"
            using hK_fin' by (by100 simp)
          have hpair_sub: "{\<sigma>, \<tau>} \<subseteq> ?F"
            using h\<sigma>K h\<tau>K h\<sigma>free h\<tau>free by (by100 blast)
          have hpair_card: "card {\<sigma>, \<tau>} = 2"
            using h\<sigma>\<tau> by (by100 simp)
          have "card {\<sigma>, \<tau>} \<le> card ?F"
            by (rule card_mono[OF hF_fin hpair_sub])
          thus "card ?F \<ge> 2"
            using hpair_card by (by100 simp)
        qed
        \<comment> \<open>Otherwise decompose \<open>J'\<close> at the opposite vertices into two polygonal
          regions, apply the induction hypothesis to the two subcomplexes
          \<open>L\<^sub>1\<close> and \<open>L\<^sub>2\<close>, and transfer the resulting free simplexes back to \<open>K\<close>.\<close>
        have hdecomposition_case:
          "card ?F \<ge> 2"
          sorry
        show ?thesis
          using hdecomposition_case .
      qed
      show "card ?F \<ge> 2"
      proof (cases "card ?T = 2")
        case True
        show ?thesis
          by (rule hbase_two[OF True])
      next
        case False
        have "card ?T > 2"
          using hcard' False by (by100 simp)
        show ?thesis
          by (rule hstep_more_than_two[OF \<open>card ?T > 2\<close>])
      qed
    qed
    have hSC_induction:
      "\<And>K. geotop_is_complex K \<Longrightarrow> finite K \<Longrightarrow>
            geotop_polyhedron K = closure_on UNIV geotop_euclidean_topology
                                    (geotop_polygon_interior J) \<Longrightarrow>
            card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2} > 1 \<Longrightarrow>
            card {\<sigma>\<^sub>2\<in>K. geotop_free_2_simplex K J \<sigma>\<^sub>2} \<ge> 2"
    proof -
      fix K :: "(real^2) set set"
      assume hK': "geotop_is_complex K"
      assume hK_fin': "finite K"
      assume hK_poly': "geotop_polyhedron K = closure_on UNIV geotop_euclidean_topology
                                    (geotop_polygon_interior J)"
      assume hcard': "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2} > 1"
      show "card {\<sigma>\<^sub>2 \<in> K. geotop_free_2_simplex K J \<sigma>\<^sub>2} \<ge> 2"
        by (rule hSC_induction_general[OF hJ hK' hK_fin' hK_poly' hcard'])
    qed
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
  shows "\<exists>(h :: real^2 \<Rightarrow> real^2) (\<sigma> :: (real^2) set).
                 top1_homeomorphism_on UNIV geotop_euclidean_topology
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
          \<exists>(h :: real^2 \<Rightarrow> real^2) (\<sigma> :: (real^2) set).
              top1_homeomorphism_on UNIV geotop_euclidean_topology
                   UNIV geotop_euclidean_topology h
                \<and> geotop_simplex_dim \<sigma> 2
                \<and> h ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
  proof -
    fix K :: "(real^2) set set"
    assume hK: "geotop_is_complex K"
      and hK_fin: "finite K"
      and hK_poly:
        "geotop_polyhedron K =
          closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
      and hcard_one: "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2} = 1"
    obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
      and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
      and hunique2: "\<And>\<tau>. \<tau> \<in> K \<Longrightarrow> geotop_simplex_dim \<tau> 2 \<Longrightarrow> \<tau> = \<sigma>"
    proof -
      let ?S = "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2}"
      have hS_fin: "finite ?S"
        using hK_fin by (by100 simp)
      have hS_ne: "?S \<noteq> {}"
        using hcard_one by (by100 force)
      obtain \<sigma> where h\<sigma>S: "\<sigma> \<in> ?S"
        using hS_ne by (by100 blast)
      have hS_eq: "?S = {\<sigma>}"
      proof -
        obtain \<sigma>' where hS_singleton: "?S = {\<sigma>'}"
          using hcard_one by (rule card_1_singletonE)
        have "\<sigma> = \<sigma>'"
          using hS_singleton h\<sigma>S by (by100 simp)
        thus ?thesis
          using hS_singleton by (by100 simp)
      qed
      have h\<sigma>K: "\<sigma> \<in> K"
        using h\<sigma>S by (by100 simp)
      have h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
        using h\<sigma>S by (by100 simp)
      have hunique2: "\<And>\<tau>. \<tau> \<in> K \<Longrightarrow> geotop_simplex_dim \<tau> 2 \<Longrightarrow> \<tau> = \<sigma>"
      proof -
        fix \<tau>
        assume h\<tau>K: "\<tau> \<in> K" and h\<tau>2: "geotop_simplex_dim \<tau> 2"
        have "\<tau> \<in> ?S"
          using h\<tau>K h\<tau>2 by (by100 simp)
        thus "\<tau> = \<sigma>"
          using hS_eq by (by100 simp)
      qed
      show ?thesis
        by (rule that[OF h\<sigma>K h\<sigma>2 hunique2])
    qed
    have hid_homeo: "top1_homeomorphism_on UNIV geotop_euclidean_topology
        UNIV geotop_euclidean_topology (\<lambda>x::real^2. x)"
    proof -
      have htop: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
        unfolding geotop_euclidean_topology_eq_open_sets
        by (rule top1_open_sets_is_topology_on_UNIV)
      show ?thesis
        using top1_homeomorphism_on_id[OF htop] unfolding id_def by (by100 simp)
    qed
    have hclosure_sigma: "closure (geotop_polygon_interior J) = \<sigma>"
    proof -
      let ?I = "geotop_polygon_interior J"
      let ?R = "\<Union>(K - {\<sigma>})"
      have hrest_fin: "finite (K - {\<sigma>})"
        using hK_fin by (by100 simp)
      have h_K_simplex: "\<forall>\<tau>\<in>K. geotop_is_simplex \<tau>"
        by (rule geotop_is_complex_simplex[OF hK])
      have hrest_each: "\<forall>\<tau>\<in>K - {\<sigma>}. closed \<tau> \<and> interior \<tau> = {}"
      proof
        fix \<tau>
        assume h\<tau>rest: "\<tau> \<in> K - {\<sigma>}"
        have h\<tau>K: "\<tau> \<in> K"
          using h\<tau>rest by (by100 simp)
        have h\<tau>ne: "\<tau> \<noteq> \<sigma>"
          using h\<tau>rest by (by100 simp)
        have h\<tau>simplex: "geotop_is_simplex \<tau>"
          using h_K_simplex h\<tau>K by (by100 blast)
        obtain n where h\<tau>dim: "geotop_simplex_dim \<tau> n"
          using h\<tau>simplex
          unfolding geotop_is_simplex_def geotop_simplex_dim_def
          by (by100 blast)
        have hn_le_2: "n \<le> 2"
          by (rule geotop_simplex_dim_le_2_R2_prefix[OF h\<tau>dim])
        have hn_ne_2: "n \<noteq> 2"
        proof
          assume hn2: "n = 2"
          have h\<tau>2: "geotop_simplex_dim \<tau> 2"
            using h\<tau>dim hn2 by (by100 simp)
          have "\<tau> = \<sigma>"
            by (rule hunique2[OF h\<tau>K h\<tau>2])
          thus False
            using h\<tau>ne by (by100 simp)
        qed
        have hn_le_1: "n \<le> 1"
          using hn_le_2 hn_ne_2 by (by100 linarith)
        have h\<tau>closed: "closed \<tau>"
          by (rule geotop_simplex_dim_closed[OF h\<tau>dim])
        have h\<tau>int: "interior \<tau> = {}"
          by (rule geotop_simplex_dim_le_1_empty_interior_R2[OF h\<tau>dim hn_le_1])
        show "closed \<tau> \<and> interior \<tau> = {}"
          using h\<tau>closed h\<tau>int by (by100 blast)
      qed
      have hrest_int_empty: "interior ?R = {}"
        by (rule finite_Union_closed_empty_interior[OF hrest_fin hrest_each])
      have h\<sigma>closed: "closed \<sigma>"
        by (rule geotop_simplex_dim_closed[OF h\<sigma>2])
      have hpoly_union: "geotop_polyhedron K = \<sigma> \<union> ?R"
      proof -
        have "\<Union>K = \<sigma> \<union> \<Union>(K - {\<sigma>})"
          using h\<sigma>K by (by100 blast)
        thus ?thesis
          unfolding geotop_polyhedron_def by (by100 simp)
      qed
      have hpoly_int_sub_\<sigma>: "interior (geotop_polyhedron K) \<subseteq> \<sigma>"
      proof -
        have "interior (\<sigma> \<union> ?R) \<subseteq> \<sigma>"
          by (rule interior_Un_subset_closed_left_if_right_empty
              [OF h\<sigma>closed hrest_int_empty])
        thus ?thesis
          using hpoly_union by (by100 simp)
      qed
      have hI_open: "open ?I"
        by (rule polygon_interior_open[OF hJ])
      have hclos_on: "closure_on UNIV geotop_euclidean_topology ?I = closure ?I"
        by (rule closure_on_geotop_UNIV_eq_closure)
      have hpoly_HOL: "geotop_polyhedron K = closure ?I"
        using hK_poly hclos_on by (by100 simp)
      have hI_sub_poly: "?I \<subseteq> geotop_polyhedron K"
        using hpoly_HOL closure_subset by (by100 simp)
      have hI_sub_int_poly: "?I \<subseteq> interior (geotop_polyhedron K)"
        by (rule interior_maximal[OF hI_sub_poly hI_open])
      have hI_sub_\<sigma>: "?I \<subseteq> \<sigma>"
        using hI_sub_int_poly hpoly_int_sub_\<sigma> by (by100 blast)
      have hclosure_sub_\<sigma>: "closure ?I \<subseteq> \<sigma>"
        by (rule closure_minimal[OF hI_sub_\<sigma> h\<sigma>closed])
      have h\<sigma>sub_closure: "\<sigma> \<subseteq> closure ?I"
      proof -
        have "\<sigma> \<subseteq> geotop_polyhedron K"
          using h\<sigma>K unfolding geotop_polyhedron_def by (by100 blast)
        thus ?thesis
          using hpoly_HOL by (by100 simp)
      qed
      show ?thesis
        using hclosure_sub_\<sigma> h\<sigma>sub_closure by (by100 blast)
    qed
    have hJ_frontier:
        "(\<lambda>x::real^2. x) ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
    proof -
      let ?I = "geotop_polygon_interior J"
      have hI_front_HOL: "frontier ?I = J"
      proof -
        have hI_front_geo:
          "geotop_frontier UNIV geotop_euclidean_topology ?I = J"
          using Theorem_GT_2_6(1)[OF hJ] by (by100 simp)
        have hfront_eq:
          "geotop_frontier UNIV geotop_euclidean_topology ?I = frontier ?I"
          by (rule geotop_frontier_UNIV_eq_frontier)
        show ?thesis
          using hI_front_geo hfront_eq by (by100 simp)
      qed
      have h\<sigma>_union: "\<sigma> = ?I \<union> J"
        using hclosure_sigma polygon_interior_closure_eq[OF hJ] by (by100 simp)
      have hI_disj_J: "?I \<inter> J = {}"
        by (rule polygon_interior_disjoint_polygon[OF hJ])
      have h\<sigma>_front_book_gap:
          "geotop_frontier UNIV geotop_euclidean_topology \<sigma> = J"
      proof -
        have h\<sigma>_interior_book_gap: "interior \<sigma> = ?I"
        proof -
          let ?E = "geotop_polygon_exterior J"
          have hI_sub_int_\<sigma>: "?I \<subseteq> interior \<sigma>"
          proof -
            have hI_sub_\<sigma>: "?I \<subseteq> \<sigma>"
              using h\<sigma>_union by (by100 blast)
            have hI_open_local: "open ?I"
              by (rule polygon_interior_open[OF hJ])
            show ?thesis
              by (rule interior_maximal[OF hI_sub_\<sigma> hI_open_local])
          qed
          have hE_front_HOL: "frontier ?E = J"
          proof -
            have hE_front_geo:
              "J = geotop_frontier UNIV geotop_euclidean_topology ?E"
              using Theorem_GT_2_6(2)[OF hJ] by (by100 simp)
            have hfront_eq:
              "geotop_frontier UNIV geotop_euclidean_topology ?E = frontier ?E"
              by (rule geotop_frontier_UNIV_eq_frontier)
            show ?thesis
              using hE_front_geo hfront_eq by (by100 simp)
          qed
          have hE_disj_\<sigma>: "?E \<inter> \<sigma> = {}"
          proof -
            have hI_E: "?I \<inter> ?E = {}"
              by (rule polygon_interior_exterior_disjoint[OF hJ])
            have hE_J: "?E \<inter> J = {}"
              by (rule polygon_exterior_disjoint_polygon[OF hJ])
            show ?thesis
              using h\<sigma>_union hI_E hE_J by (by100 blast)
          qed
          have hint_\<sigma>_sub_I: "interior \<sigma> \<subseteq> ?I"
          proof
            fix x
            assume hx: "x \<in> interior \<sigma>"
            have hx\<sigma>: "x \<in> \<sigma>"
              using hx interior_subset by (by100 blast)
            have hx_I_or_J: "x \<in> ?I \<or> x \<in> J"
              using h\<sigma>_union hx\<sigma> by (by100 blast)
            show "x \<in> ?I"
            proof (cases "x \<in> ?I")
              case True
              then show ?thesis .
            next
              case False
              have hxJ: "x \<in> J"
                using hx_I_or_J False by (by100 blast)
              have hxFrontE: "x \<in> frontier ?E"
                using hE_front_HOL hxJ by (by100 simp)
              have hxClosureE: "x \<in> closure ?E"
                using hxFrontE unfolding Elementary_Topology.frontier_def by (by100 simp)
              have hx_not_E: "x \<notin> ?E"
                using hE_disj_\<sigma> hx\<sigma> by (by100 blast)
              have hxLimE: "x islimpt ?E"
                using hxClosureE hx_not_E unfolding closure_def by (by100 blast)
              obtain U where hUopen: "open U" and hxU: "x \<in> U" and hUsub: "U \<subseteq> \<sigma>"
                using hx unfolding interior_def by (by100 blast)
              obtain y where hyE: "y \<in> ?E" and hyU: "y \<in> U" and "y \<noteq> x"
                by (rule islimptE[OF hxLimE hxU hUopen])
              have hy\<sigma>: "y \<in> \<sigma>"
                using hUsub hyU by (by100 blast)
              have False
                using hE_disj_\<sigma> hyE hy\<sigma> by (by100 blast)
              then show ?thesis
                by (by100 blast)
            qed
          qed
          show ?thesis
            using hI_sub_int_\<sigma> hint_\<sigma>_sub_I by (by100 blast)
        qed
        have h\<sigma>_closed: "closed \<sigma>"
          by (rule geotop_simplex_dim_closed[OF h\<sigma>2])
        have hfront_HOL: "frontier \<sigma> = J"
        proof -
          have hfront_def: "frontier \<sigma> = closure \<sigma> - interior \<sigma>"
            unfolding Elementary_Topology.frontier_def by (by100 simp)
          have hclosure_\<sigma>: "closure \<sigma> = \<sigma>"
            using h\<sigma>_closed by (by100 simp)
          have hfront_diff: "frontier \<sigma> = \<sigma> - ?I"
            using hfront_def hclosure_\<sigma> h\<sigma>_interior_book_gap by (by100 simp)
          have hdiff_sub_J: "\<sigma> - ?I \<subseteq> J"
          proof
            fix x
            assume hx: "x \<in> \<sigma> - ?I"
            have hx\<sigma>: "x \<in> \<sigma>"
              using hx by (by100 simp)
            have hx_not_I: "x \<notin> ?I"
              using hx by (by100 simp)
            have "x \<in> ?I \<union> J"
              using h\<sigma>_union hx\<sigma> by (by100 simp)
            thus "x \<in> J"
              using hx_not_I by (by100 blast)
          qed
          have hJ_sub_diff: "J \<subseteq> \<sigma> - ?I"
          proof
            fix x
            assume hxJ: "x \<in> J"
            have hx\<sigma>: "x \<in> \<sigma>"
              using h\<sigma>_union hxJ by (by100 simp)
            have hx_not_I: "x \<notin> ?I"
              using hI_disj_J hxJ by (by100 blast)
            show "x \<in> \<sigma> - ?I"
              using hx\<sigma> hx_not_I by (by100 simp)
          qed
          have hdiff_eq_J: "\<sigma> - ?I = J"
            using hdiff_sub_J hJ_sub_diff by (by100 blast)
          show ?thesis
            using hfront_diff hdiff_eq_J by (by100 simp)
        qed
        show ?thesis
          using hfront_HOL geotop_frontier_UNIV_eq_frontier[of \<sigma>] by (by100 simp)
      qed
      show ?thesis
        using h\<sigma>_front_book_gap by (by100 simp)
    qed
    have hsig_ex: "\<exists>\<sigma>::(real^2) set.
        top1_homeomorphism_on UNIV geotop_euclidean_topology
          UNIV geotop_euclidean_topology (\<lambda>x::real^2. x)
        \<and> geotop_simplex_dim \<sigma> 2
        \<and> (\<lambda>x::real^2. x) ` J =
          geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
    proof (rule exI[where x = \<sigma>])
      show "top1_homeomorphism_on UNIV geotop_euclidean_topology
          UNIV geotop_euclidean_topology (\<lambda>x::real^2. x)
        \<and> geotop_simplex_dim \<sigma> 2
        \<and> (\<lambda>x::real^2. x) ` J =
          geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
        using hid_homeo h\<sigma>2 hJ_frontier by (by100 blast)
    qed
    show "\<exists>(h :: real^2 \<Rightarrow> real^2) (\<sigma> :: (real^2) set).
             top1_homeomorphism_on UNIV geotop_euclidean_topology
             UNIV geotop_euclidean_topology h
          \<and> geotop_simplex_dim \<sigma> 2
          \<and> h ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
      using hsig_ex by (by100 blast)
  qed
  \<comment> \<open>Sub-claim 34-Step: if K has > 1 two-simplex, find a free 2-simplex (via
    GT_3_3); fold it to reduce #2-simplexes; apply IH on the reduced complex.
    Each fold gives a homeomorphism plane → plane; compose at the end.\<close>
  have ind_step:
    "\<And>K. geotop_is_complex K \<Longrightarrow> finite K \<Longrightarrow>
          geotop_polyhedron K =
            closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J) \<Longrightarrow>
          card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2} > 1 \<Longrightarrow>
          \<exists>(h :: real^2 \<Rightarrow> real^2) (\<sigma> :: (real^2) set).
              top1_homeomorphism_on UNIV geotop_euclidean_topology
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
          \<exists>(h :: real^2 \<Rightarrow> real^2) (\<sigma> :: (real^2) set).
              top1_homeomorphism_on UNIV geotop_euclidean_topology
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
    show "\<exists>(h :: real^2 \<Rightarrow> real^2) (\<sigma> :: (real^2) set).
                   top1_homeomorphism_on UNIV geotop_euclidean_topology
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
  obtain f\<^sub>1 :: "real^2 \<Rightarrow> real^2" and \<sigma> :: "(real^2) set"
    where hf1: "top1_homeomorphism_on UNIV geotop_euclidean_topology
                              UNIV geotop_euclidean_topology f\<^sub>1"
                   and h\<sigma>: "geotop_simplex_dim \<sigma> 2"
                   and hf1J: "f\<^sub>1 ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
    using Theorem_GT_3_4[OF hJ] by blast
  obtain f\<^sub>2 :: "real^2 \<Rightarrow> real^2" and \<tau> :: "(real^2) set"
    where hf2: "top1_homeomorphism_on UNIV geotop_euclidean_topology
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
  proof -
    obtain V m where hV_fin: "finite V" and hV_card: "card V = 2 + 1"
      and hV_m: "2 \<le> m" and hV_gp: "geotop_general_position V m"
      and h\<sigma>_hull: "\<sigma> = geotop_convex_hull V"
      using h\<sigma> unfolding geotop_simplex_dim_def by (by100 blast)
    have hV: "geotop_simplex_vertices \<sigma> V"
      unfolding geotop_simplex_vertices_def
      using hV_fin hV_card hV_m hV_gp h\<sigma>_hull by (by100 blast)
    obtain W m' where hW_fin: "finite W" and hW_card: "card W = 2 + 1"
      and hW_m: "2 \<le> m'" and hW_gp: "geotop_general_position W m'"
      and h\<tau>_hull: "\<tau> = geotop_convex_hull W"
      using h\<tau> unfolding geotop_simplex_dim_def by (by100 blast)
    have hW: "geotop_simplex_vertices \<tau> W"
      unfolding geotop_simplex_vertices_def
      using hW_fin hW_card hW_m hW_gp h\<tau>_hull by (by100 blast)
    have hcard_le: "card V \<le> card W"
      using hV_card hW_card by (by100 simp)
    obtain \<phi> where h\<phi>_img: "\<phi> ` V \<subseteq> W" and h\<phi>_inj: "inj_on \<phi> V"
      using card_le_inj[OF hV_fin hW_fin hcard_le] by (by100 blast)
    have h\<phi>_image: "\<phi> ` V = W"
    proof -
      have h_card_img: "card (\<phi> ` V) = card V"
        by (rule card_image[OF h\<phi>_inj])
      have h_card_img_W: "card (\<phi> ` V) = card W"
        using h_card_img hV_card hW_card by (by100 simp)
      show ?thesis
        using h\<phi>_img hW_fin h_card_img_W card_subset_eq by (by100 blast)
    qed
    define \<psi> where "\<psi> x = (if x \<in> V then \<phi> x else undefined)" for x
    have h\<psi>_image: "\<psi> ` V = W"
      unfolding \<psi>_def using h\<phi>_image by (by100 simp)
    have h\<psi>_inj: "inj_on \<psi> V"
    proof (rule inj_onI)
      fix x y
      assume hx: "x \<in> V" and hy: "y \<in> V" and hxy: "\<psi> x = \<psi> y"
      have hxy_phi: "\<phi> x = \<phi> y"
        using hx hy hxy unfolding \<psi>_def by (by100 simp)
      show "x = y"
        using h\<phi>_inj hx hy hxy_phi unfolding inj_on_def by (by100 blast)
    qed
    have h\<psi>_bij: "bij_betw \<psi> V W"
      unfolding bij_betw_def using h\<psi>_inj h\<psi>_image by (by100 blast)
    have h\<psi>_mem: "\<psi> \<in> V \<rightarrow>\<^sub>E W"
    proof -
      have h_into: "\<forall>x\<in>V. \<psi> x \<in> W"
      proof
        fix x assume hx: "x \<in> V"
        have "\<psi> x = \<phi> x"
          unfolding \<psi>_def using hx by (by100 simp)
        moreover have "\<phi> x \<in> W"
          using h\<phi>_img hx by (by100 blast)
        ultimately show "\<psi> x \<in> W" by (by100 simp)
      qed
      have h_ext: "\<psi> \<in> extensional V"
        unfolding \<psi>_def extensional_def by (by100 simp)
      show ?thesis
        unfolding PiE_def using h_into h_ext by (by100 blast)
    qed
    obtain f\<^sub>3 where hf3_homeo:
        "top1_homeomorphism_on UNIV geotop_euclidean_topology
           UNIV geotop_euclidean_topology f\<^sub>3"
      and hf3_image: "f\<^sub>3 ` \<sigma> = \<tau>"
      using Theorem_GT_3_2[
        where \<sigma>=\<sigma> and \<tau>=\<tau> and V=V and W=W and \<phi>=\<psi> and n=2,
        OF h\<sigma> h\<tau> hV hW h\<psi>_mem h\<psi>_bij]
      by (by100 blast)
    obtain k where hHOL: "homeomorphism UNIV UNIV f\<^sub>3 k"
      by (rule top1_homeomorphism_on_UNIV_R2_obtain_HOL_homeomorphism[OF hf3_homeo])
    have hfront_HOL: "f\<^sub>3 ` frontier \<sigma> = frontier \<tau>"
    proof -
      have "f\<^sub>3 ` frontier \<sigma> = frontier (f\<^sub>3 ` \<sigma>)"
        by (rule homeomorphism_UNIV_image_frontier[OF hHOL])
      thus ?thesis using hf3_image by (by100 simp)
    qed
    have hfront_geotop:
      "f\<^sub>3 ` (geotop_frontier UNIV geotop_euclidean_topology \<sigma>)
       = geotop_frontier UNIV geotop_euclidean_topology \<tau>"
      using hfront_HOL geotop_frontier_UNIV_eq_frontier[of \<sigma>]
            geotop_frontier_UNIV_eq_frontier[of \<tau>] by (by100 simp)
    show ?thesis using hf3_homeo hfront_geotop by (by100 blast)
  qed
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

definition geotop_polygon_cyclic_order ::
  "(real^2) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "geotop_polygon_cyclic_order J P Q R S \<longleftrightarrow>
    (\<exists>c tP tQ tR tS.
        simple_path c \<and> pathfinish c = pathstart c \<and> path_image c = J \<and>
        0 \<le> tP \<and> tP < tQ \<and> tQ < tR \<and> tR < tS \<and> tS < 1 \<and>
        c tP = P \<and> c tQ = Q \<and> c tR = R \<and> c tS = S)"

lemma geotop_polygon_interior_minus_arc_frontier_at_boundary_point_dev34:
  fixes J A :: "(real^2) set" and X P R :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hX: "X \<in> J"
  assumes hX_ne: "X \<noteq> P \<and> X \<noteq> R"
  assumes hA: "geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A)"
  assumes hAJ: "A \<inter> J = {P, R}"
  shows "\<exists>U. U \<in> geotop_euclidean_topology \<and>
          U \<subseteq> geotop_polygon_interior J - A \<and>
          X \<in> geotop_frontier UNIV geotop_euclidean_topology U"
  (**
    Book step used twice in Theorem 4.2: if a boundary point of the polygon is
    not one of the two arc endpoints, then it remains a frontier point of the
    cut-open interior \<open>I - A\<close>. **)
proof -
  let ?U = "geotop_polygon_interior J - A"
  obtain \<gamma> :: "real \<Rightarrow> real^2" where h\<gamma>_arc: "arc \<gamma>"
    and h\<gamma>_img: "path_image \<gamma> = A"
    using geotop_is_arc_imp_HOL_arc[OF hA] by (by100 blast)
  have hA_closed: "closed A"
    using closed_arc_image[OF h\<gamma>_arc] h\<gamma>_img by (by100 simp)
  have hI_open: "open (geotop_polygon_interior J)"
    by (rule polygon_interior_open[OF hJ])
  have hU_open_HOL: "open ?U"
    by (rule open_Diff[OF hI_open hA_closed])
  have hU_open: "?U \<in> geotop_euclidean_topology"
    by (metis hU_open_HOL geotop_euclidean_topology_eq_open_sets
              mem_Collect_eq top1_open_sets_def)
  have hX_not_A: "X \<notin> A"
  proof
    assume hXA: "X \<in> A"
    have "X \<in> A \<inter> J"
      using hXA hX by (by100 blast)
    hence "X = P \<or> X = R"
      using hAJ by (by100 blast)
    thus False
      using hX_ne by (by100 blast)
  qed
  have hX_not_I: "X \<notin> geotop_polygon_interior J"
    using hX polygon_interior_disjoint_polygon[OF hJ] by (by100 blast)
  have hlim_top:
      "is_limit_point_of X (geotop_polygon_interior J) UNIV geotop_euclidean_topology"
    using Theorem_GT_2_5[OF hJ] hX by (by100 blast)
  have hlim_I: "X islimpt geotop_polygon_interior J"
    using hlim_top
      is_limit_point_of_UNIV_geotop_iff_islimpt[of X "geotop_polygon_interior J"]
    by (by100 blast)
  have hnotA_open: "open (- A)"
    by (rule open_Compl[OF hA_closed])
  have hX_in_notA: "X \<in> - A"
    using hX_not_A by (by100 simp)
  have hevent_not_A: "eventually (\<lambda>x. x \<in> - A) (at X)"
    by (rule eventually_at_in_open'[OF hnotA_open hX_in_notA])
  have hlim_U: "X islimpt ?U"
  proof -
    have "X islimpt (geotop_polygon_interior J \<inter> - A)"
      by (rule islimpt_Int_eventually[OF hlim_I hevent_not_A])
    thus ?thesis by (simp add: Diff_eq)
  qed
  have hX_closure: "X \<in> closure ?U"
    using hlim_U unfolding closure_def by (by100 simp)
  have hX_not_int: "X \<notin> interior ?U"
    using hX_not_I interior_subset[of ?U] by (by100 blast)
  have hX_front_HOL: "X \<in> frontier ?U"
    using hX_closure hX_not_int
    unfolding Elementary_Topology.frontier_def by (by100 blast)
  have hX_front: "X \<in> geotop_frontier UNIV geotop_euclidean_topology ?U"
    using hX_front_HOL geotop_frontier_UNIV_eq_frontier[of ?U] by (by100 simp)
  show ?thesis
    using hU_open hX_front by (by100 blast)
qed

(** from \<S>4 Theorem 2 (geotop.tex:869)
    LATEX VERSION: Let I be the interior of a polygon in R^2, and let P, Q, R, S be points of
      Fr I, in cyclic order. Let A be an arc from P to R, lying in \<bar>I\<close>, with A \<inter> Fr I = {P,R}.
      Then I - A is the union of two disjoint open sets U_Q, U_S containing Q and S in
      their frontiers. **)
theorem Theorem_GT_4_2:
  fixes J :: "(real^2) set" and A :: "(real^2) set" and P Q R S :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hP: "P \<in> J" and hQ: "Q \<in> J" and hR: "R \<in> J" and hS: "S \<in> J"
  assumes hcyc: "geotop_polygon_cyclic_order J P Q R S"
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
  proof -
    have hQ_ne_PR: "Q \<noteq> P \<and> Q \<noteq> R"
    proof
      show "Q \<noteq> P"
      proof
        assume "Q = P"
        hence "card {P, Q, R, S} \<le> 3" by (simp add: card_insert_if)
        thus False using hcard by (by100 simp)
      qed
      show "Q \<noteq> R"
      proof
        assume "Q = R"
        hence "card {P, Q, R, S} \<le> 3" by (simp add: card_insert_if)
        thus False using hcard by (by100 simp)
      qed
    qed
    show ?thesis
      by (rule geotop_polygon_interior_minus_arc_frontier_at_boundary_point_dev34
          [OF hJ hQ hQ_ne_PR hA hAJ])
  qed
  \<comment> \<open>Sub-claim D42-2: similarly there's a U_S with S in its frontier.\<close>
  have hD42_US_ex:
    "\<exists>U\<^sub>S. U\<^sub>S \<in> geotop_euclidean_topology \<and>
            U\<^sub>S \<subseteq> geotop_polygon_interior J - A \<and>
            S \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>S"
  proof -
    have hS_ne_PR: "S \<noteq> P \<and> S \<noteq> R"
    proof
      show "S \<noteq> P"
      proof
        assume "S = P"
        hence "card {P, Q, R, S} \<le> 3" by (simp add: card_insert_if)
        thus False using hcard by (by100 simp)
      qed
      show "S \<noteq> R"
      proof
        assume "S = R"
        hence "card {P, Q, R, S} \<le> 3" by (simp add: card_insert_if)
        thus False using hcard by (by100 simp)
      qed
    qed
    show ?thesis
      by (rule geotop_polygon_interior_minus_arc_frontier_at_boundary_point_dev34
          [OF hJ hS hS_ne_PR hA hAJ])
  qed
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
  \<comment> \<open>Book step 1: choose a rectangular brick-decomposition, fine enough that
    \<open>closure I\<close> is a union of bricks and no brick meets both \<open>A1\<close> and \<open>A2\<close>.\<close>
  have hD44_bricks:
    "\<exists>G. geotop_brick_decomposition G \<and>
          closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)
            = \<Union>{g\<in>G. g \<subseteq>
                closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)} \<and>
          (\<forall>g\<in>G. \<not> (g \<inter> A1 \<noteq> {} \<and> g \<inter> A2 \<noteq> {}))"
    sorry
  \<comment> \<open>Book step 2: \<open>N'\<close>, the union of the bricks meeting \<open>A1\<close> inside
    \<open>closure I\<close>, is a 2-manifold with boundary.\<close>
  have hD44_N'_manifold:
    "\<exists>G N'. geotop_brick_decomposition G \<and>
       N' = \<Union>{g\<in>G. g \<inter> A1 \<noteq> {}} \<inter>
          closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J) \<and>
       geotop_n_manifold_with_boundary_on N' (\<lambda>x y. norm (x - y)) 2"
    sorry
  \<comment> \<open>Book step 3: take the component of \<open>Fr N'\<close> containing \<open>P\<close>; it is a
    1-sphere. Its intersection with \<open>Fr I\<close> gives the broken line \<open>B1\<close>,
    and the complementary broken line \<open>B2\<close> contains a sub-broken-line \<open>B\<close>
    between points \<open>V,W\<close> of \<open>Fr I\<close> with \<open>B \<inter> Fr I = {V,W}\<close>.\<close>
  have hD44_frontier_broken_line:
    "\<exists>J' B V W. geotop_is_n_sphere J'
          (subspace_topology UNIV geotop_euclidean_topology J') 1 \<and>
        geotop_is_broken_line B \<and> B \<subseteq> J' \<and>
        V \<in> J \<and> W \<in> J \<and> B \<inter> J = {V, W}"
    sorry
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
    sorry
  \<comment> \<open>Book step 5: by the cyclic order on \<open>Fr I\<close>, the endpoints \<open>V,W\<close>
    occur on opposite sides of \<open>P,R\<close>, so the same component that has
    \<open>V,W\<close> in its frontier also has \<open>Q,S\<close> in its frontier.\<close>
  have hD44_QS_component:
    "\<exists>C. Q \<in> geotop_frontier UNIV geotop_euclidean_topology C
       \<and> S \<in> geotop_frontier UNIV geotop_euclidean_topology C
       \<and> (\<exists>P'. P' \<in> geotop_polygon_interior J - (A1 \<union> A2) \<and>
           C = geotop_component_at UNIV geotop_euclidean_topology
                  (geotop_polygon_interior J - (A1 \<union> A2)) P')"
    sorry
  show ?thesis using hD44_QS_component by (by100 blast)
qed

end
