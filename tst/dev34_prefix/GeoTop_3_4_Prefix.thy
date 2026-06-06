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

lemma geotop_2simplex_edge_face_vertices_prefix:
  fixes e \<sigma> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes hedge: "geotop_is_edge e"
  assumes hface: "geotop_is_face e \<sigma>"
  obtains v\<^sub>0 v\<^sub>1 v\<^sub>2 where "v\<^sub>0 \<noteq> v\<^sub>1"
    and "v\<^sub>2 \<notin> {v\<^sub>0, v\<^sub>1}"
    and "e = geotop_convex_hull {v\<^sub>0, v\<^sub>1}"
    and "geotop_simplex_vertices \<sigma> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
  (**
    Book-notation extraction for Theorem 3.3: a boundary edge face of a
    2-simplex can be named as \<open>v\<^sub>0v\<^sub>1\<close>, and the 2-simplex as
    \<open>v\<^sub>0v\<^sub>1v\<^sub>2\<close>. **)
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and he_eq: "e = geotop_convex_hull W"
    and heW: "geotop_simplex_vertices e W"
    and hW_card: "card W = 2"
    by (rule geotop_edge_face_witness_card_two_prefix[OF hedge hface])
  obtain V\<^sub>\<sigma> m where hV\<^sub>\<sigma>_fin: "finite V\<^sub>\<sigma>"
    and hV\<^sub>\<sigma>_card: "card V\<^sub>\<sigma> = 2 + 1"
    and h2_le_m: "2 \<le> m"
    and hV\<^sub>\<sigma>_gp: "geotop_general_position V\<^sub>\<sigma> m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V\<^sub>\<sigma>"
    using h\<sigma>2 unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V\<^sub>\<sigma>: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>"
    unfolding geotop_simplex_vertices_def
    using hV\<^sub>\<sigma>_fin hV\<^sub>\<sigma>_card h2_le_m hV\<^sub>\<sigma>_gp h\<sigma>_eq by (by100 blast)
  have hV_eq: "V = V\<^sub>\<sigma>"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>V\<^sub>\<sigma>])
  have hV_fin: "finite V"
    using hV_eq hV\<^sub>\<sigma>_fin by (by100 simp)
  have hW_fin: "finite W"
    using hW_sub hV_fin by (rule finite_subset)
  have hV_card: "card V = 3"
    using hV_eq hV\<^sub>\<sigma>_card by (by100 simp)
  have hW_pair: "\<exists>v\<^sub>0 v\<^sub>1. W = {v\<^sub>0, v\<^sub>1} \<and> v\<^sub>0 \<noteq> v\<^sub>1"
    using hW_card card_2_iff[of W] by (by100 simp)
  obtain v\<^sub>0 v\<^sub>1 where hW_eq: "W = {v\<^sub>0, v\<^sub>1}"
    and hv\<^sub>0v\<^sub>1: "v\<^sub>0 \<noteq> v\<^sub>1"
    using hW_pair by (elim exE conjE)
  have hV_minus_ne: "V - W \<noteq> {}"
  proof
    assume hVW_empty: "V - W = {}"
    have "V \<subseteq> W"
      using hVW_empty by (by100 blast)
    hence "V = W"
      using hW_sub by (by100 blast)
    thus False
      using hV_card hW_card by (by100 simp)
  qed
  obtain v\<^sub>2 where hv\<^sub>2: "v\<^sub>2 \<in> V - W"
    using hV_minus_ne by (by100 blast)
  have hV_minus_card_eq: "card (V - W) = card V - card W"
    by (rule card_Diff_subset[OF hW_fin hW_sub])
  have hV_minus_card: "card (V - W) = 1"
    using hV_minus_card_eq hV_card hW_card by (by100 simp)
  obtain x where hx: "V - W = {x}"
  proof -
    have "\<exists>x. V - W = {x}"
      using hV_minus_card card_1_singleton_iff[of "V - W"] by (by100 simp)
    thus ?thesis
      using that by (elim exE)
  qed
  have hV_minus_eq: "V - W = {v\<^sub>2}"
    using hv\<^sub>2 hx by (by100 simp)
  have hV_vertices: "V = {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
  proof -
    have "V = W \<union> (V - W)"
      using hW_sub by (by100 blast)
    thus ?thesis
      using hW_eq hV_minus_eq by (by100 blast)
  qed
  have hv\<^sub>2_not: "v\<^sub>2 \<notin> {v\<^sub>0, v\<^sub>1}"
    using hv\<^sub>2 hW_eq by (by100 simp)
  have he_vertices: "e = geotop_convex_hull {v\<^sub>0, v\<^sub>1}"
    using he_eq hW_eq by (by100 simp)
  have h\<sigma>vertices: "geotop_simplex_vertices \<sigma> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
    using h\<sigma>V hV_vertices by (by100 simp)
  show ?thesis
    by (rule that[OF hv\<^sub>0v\<^sub>1 hv\<^sub>2_not he_vertices h\<sigma>vertices])
qed

lemma geotop_2simplex_vertices_other_edge_faces_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hvertices: "geotop_simplex_vertices \<sigma> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
  assumes hv\<^sub>0v\<^sub>1: "v\<^sub>0 \<noteq> v\<^sub>1"
  assumes hv\<^sub>2_not: "v\<^sub>2 \<notin> {v\<^sub>0, v\<^sub>1}"
  shows "geotop_is_edge (geotop_convex_hull {v\<^sub>0, v\<^sub>2})
      \<and> geotop_is_face (geotop_convex_hull {v\<^sub>0, v\<^sub>2}) \<sigma>
      \<and> geotop_is_edge (geotop_convex_hull {v\<^sub>1, v\<^sub>2})
      \<and> geotop_is_face (geotop_convex_hull {v\<^sub>1, v\<^sub>2}) \<sigma>"
  (**
    Book-notation companion: after naming a 2-simplex as \<open>v\<^sub>0v\<^sub>1v\<^sub>2\<close>,
    the remaining two sides \<open>v\<^sub>0v\<^sub>2\<close> and \<open>v\<^sub>1v\<^sub>2\<close> are edge faces. **)
proof -
  let ?e\<^sub>02 = "geotop_convex_hull {v\<^sub>0, v\<^sub>2}"
  let ?e\<^sub>12 = "geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
  obtain m n where hfin: "finite {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
    and hcard: "card {v\<^sub>0, v\<^sub>1, v\<^sub>2} = n + 1"
    and hn_le_m: "n \<le> m"
    and hgp: "geotop_general_position {v\<^sub>0, v\<^sub>1, v\<^sub>2} m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
    using hvertices unfolding geotop_simplex_vertices_def by (by100 blast)
  have hv\<^sub>0v\<^sub>2: "v\<^sub>0 \<noteq> v\<^sub>2"
    using hv\<^sub>2_not by (by100 blast)
  have hv\<^sub>1v\<^sub>2: "v\<^sub>1 \<noteq> v\<^sub>2"
    using hv\<^sub>2_not by (by100 blast)
  have hcard3: "card {v\<^sub>0, v\<^sub>1, v\<^sub>2} = 3"
    using hv\<^sub>0v\<^sub>1 hv\<^sub>0v\<^sub>2 hv\<^sub>1v\<^sub>2 by (by100 simp)
  have hn2: "n = 2"
    using hcard hcard3 by (by100 linarith)
  have h1_le_m: "1 \<le> m"
    using hn2 hn_le_m by (by100 linarith)
  have h02_sub: "{v\<^sub>0, v\<^sub>2} \<subseteq> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
    by (by100 simp)
  have h12_sub: "{v\<^sub>1, v\<^sub>2} \<subseteq> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
    by (by100 simp)
  have h02_gp: "geotop_general_position {v\<^sub>0, v\<^sub>2} m"
    by (rule geotop_general_position_subset[OF hgp h02_sub])
  have h12_gp: "geotop_general_position {v\<^sub>1, v\<^sub>2} m"
    by (rule geotop_general_position_subset[OF hgp h12_sub])
  have h02_dim: "geotop_simplex_dim ?e\<^sub>02 1"
    unfolding geotop_simplex_dim_def
  proof (rule exI[where x = "{v\<^sub>0, v\<^sub>2}"], rule exI[where x = m])
    show "finite {v\<^sub>0, v\<^sub>2} \<and> card {v\<^sub>0, v\<^sub>2} = 1 + 1 \<and> 1 \<le> m \<and>
        geotop_general_position {v\<^sub>0, v\<^sub>2} m \<and>
        ?e\<^sub>02 = geotop_convex_hull {v\<^sub>0, v\<^sub>2}"
      using h1_le_m h02_gp hv\<^sub>0v\<^sub>2 by (by100 simp)
  qed
  have h12_dim: "geotop_simplex_dim ?e\<^sub>12 1"
    unfolding geotop_simplex_dim_def
  proof (rule exI[where x = "{v\<^sub>1, v\<^sub>2}"], rule exI[where x = m])
    show "finite {v\<^sub>1, v\<^sub>2} \<and> card {v\<^sub>1, v\<^sub>2} = 1 + 1 \<and> 1 \<le> m \<and>
        geotop_general_position {v\<^sub>1, v\<^sub>2} m \<and>
        ?e\<^sub>12 = geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
      using h1_le_m h12_gp hv\<^sub>1v\<^sub>2 by (by100 simp)
  qed
  have h02_edge: "geotop_is_edge ?e\<^sub>02"
    unfolding geotop_is_edge_def using h02_dim by (by100 simp)
  have h12_edge: "geotop_is_edge ?e\<^sub>12"
    unfolding geotop_is_edge_def using h12_dim by (by100 simp)
  have h02_face: "geotop_is_face ?e\<^sub>02 \<sigma>"
  proof (rule geotop_is_face_of_subset[OF hvertices])
    show "{v\<^sub>0, v\<^sub>2} \<noteq> {}" by (by100 simp)
    show "{v\<^sub>0, v\<^sub>2} \<subseteq> {v\<^sub>0, v\<^sub>1, v\<^sub>2}" by (rule h02_sub)
  qed
  have h12_face: "geotop_is_face ?e\<^sub>12 \<sigma>"
  proof (rule geotop_is_face_of_subset[OF hvertices])
    show "{v\<^sub>1, v\<^sub>2} \<noteq> {}" by (by100 simp)
    show "{v\<^sub>1, v\<^sub>2} \<subseteq> {v\<^sub>0, v\<^sub>1, v\<^sub>2}" by (rule h12_sub)
  qed
  show ?thesis
    by (intro conjI h02_edge h02_face h12_edge h12_face)
qed

lemma geotop_pair_convex_hull_simplex_vertices_prefix:
  fixes v w :: "real^2"
  assumes hvw: "v \<noteq> w"
  shows "geotop_simplex_vertices (geotop_convex_hull {v, w}) {v, w}"
proof -
  have hfin: "finite {v, w}"
    by (by100 simp)
  have hne: "{v, w} \<noteq> {}"
    by (by100 simp)
  have hai: "\<not> affine_dependent {v, w}"
    by (rule affine_independent_2)
  show ?thesis
    by (rule geotop_AI_finite_ne_is_simplex_vertices[OF hfin hne hai])
qed

lemma geotop_2simplex_vertices_edge_hulls_distinct_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hvertices: "geotop_simplex_vertices \<sigma> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
  assumes hv\<^sub>0v\<^sub>1: "v\<^sub>0 \<noteq> v\<^sub>1"
  assumes hv\<^sub>2_not: "v\<^sub>2 \<notin> {v\<^sub>0, v\<^sub>1}"
  shows "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>0, v\<^sub>2}
      \<and> geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}
      \<and> geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
proof -
  have hv\<^sub>0v\<^sub>2: "v\<^sub>0 \<noteq> v\<^sub>2"
    using hv\<^sub>2_not by (by100 blast)
  have hv\<^sub>1v\<^sub>2: "v\<^sub>1 \<noteq> v\<^sub>2"
    using hv\<^sub>2_not by (by100 blast)
  have h01_vertices:
    "geotop_simplex_vertices (geotop_convex_hull {v\<^sub>0, v\<^sub>1}) {v\<^sub>0, v\<^sub>1}"
    by (rule geotop_pair_convex_hull_simplex_vertices_prefix[OF hv\<^sub>0v\<^sub>1])
  have h02_vertices:
    "geotop_simplex_vertices (geotop_convex_hull {v\<^sub>0, v\<^sub>2}) {v\<^sub>0, v\<^sub>2}"
    by (rule geotop_pair_convex_hull_simplex_vertices_prefix[OF hv\<^sub>0v\<^sub>2])
  have h12_vertices:
    "geotop_simplex_vertices (geotop_convex_hull {v\<^sub>1, v\<^sub>2}) {v\<^sub>1, v\<^sub>2}"
    by (rule geotop_pair_convex_hull_simplex_vertices_prefix[OF hv\<^sub>1v\<^sub>2])
  have h01_ne_02:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>0, v\<^sub>2}"
  proof
    assume heq: "geotop_convex_hull {v\<^sub>0, v\<^sub>1} = geotop_convex_hull {v\<^sub>0, v\<^sub>2}"
    have h01_on_02:
      "geotop_simplex_vertices (geotop_convex_hull {v\<^sub>0, v\<^sub>2}) {v\<^sub>0, v\<^sub>1}"
      using h01_vertices heq by (by100 simp)
    have hverts_eq: "{v\<^sub>0, v\<^sub>1} = {v\<^sub>0, v\<^sub>2}"
      by (rule geotop_simplex_vertices_unique[OF h01_on_02 h02_vertices])
    show False
      using hverts_eq hv\<^sub>0v\<^sub>1 hv\<^sub>2_not by (by100 blast)
  qed
  have h01_ne_12:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
  proof
    assume heq: "geotop_convex_hull {v\<^sub>0, v\<^sub>1} = geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
    have h01_on_12:
      "geotop_simplex_vertices (geotop_convex_hull {v\<^sub>1, v\<^sub>2}) {v\<^sub>0, v\<^sub>1}"
      using h01_vertices heq by (by100 simp)
    have hverts_eq: "{v\<^sub>0, v\<^sub>1} = {v\<^sub>1, v\<^sub>2}"
      by (rule geotop_simplex_vertices_unique[OF h01_on_12 h12_vertices])
    show False
      using hverts_eq hv\<^sub>0v\<^sub>1 hv\<^sub>2_not by (by100 blast)
  qed
  have h02_ne_12:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
  proof
    assume heq: "geotop_convex_hull {v\<^sub>0, v\<^sub>2} = geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
    have h02_on_12:
      "geotop_simplex_vertices (geotop_convex_hull {v\<^sub>1, v\<^sub>2}) {v\<^sub>0, v\<^sub>2}"
      using h02_vertices heq by (by100 simp)
    have hverts_eq: "{v\<^sub>0, v\<^sub>2} = {v\<^sub>1, v\<^sub>2}"
      by (rule geotop_simplex_vertices_unique[OF h02_on_12 h12_vertices])
    show False
      using hverts_eq hv\<^sub>0v\<^sub>1 hv\<^sub>2_not by (by100 blast)
  qed
  show ?thesis
    by (intro conjI h01_ne_02 h01_ne_12 h02_ne_12)
qed

lemma geotop_2simplex_vertices_frontier_eq_three_edge_hulls_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hvertices: "geotop_simplex_vertices \<sigma> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
  assumes hv\<^sub>0v\<^sub>1: "v\<^sub>0 \<noteq> v\<^sub>1"
  assumes hv\<^sub>2_not: "v\<^sub>2 \<notin> {v\<^sub>0, v\<^sub>1}"
  shows "frontier \<sigma> =
      geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<union>
      geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<union>
      geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
proof -
  obtain m n where h\<sigma>_eq: "\<sigma> = geotop_convex_hull {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
    using hvertices unfolding geotop_simplex_vertices_def by (by100 blast)
  have h\<sigma>_HOL: "\<sigma> = convex hull {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
    using h\<sigma>_eq geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>1, v\<^sub>2}"] by (by100 simp)
  have hfront:
    "frontier \<sigma> =
      closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>0"
    using frontier_of_triangle[where a = v\<^sub>0 and b = v\<^sub>1 and c = v\<^sub>2] h\<sigma>_HOL
    by (by100 simp)
  have h01: "closed_segment v\<^sub>0 v\<^sub>1 = geotop_convex_hull {v\<^sub>0, v\<^sub>1}"
    using segment_convex_hull[of v\<^sub>0 v\<^sub>1] geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>1}"]
    by (by100 simp)
  have h12: "closed_segment v\<^sub>1 v\<^sub>2 = geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
    using segment_convex_hull[of v\<^sub>1 v\<^sub>2] geotop_convex_hull_eq_HOL[of "{v\<^sub>1, v\<^sub>2}"]
    by (by100 simp)
  have h20_set: "{v\<^sub>2, v\<^sub>0} = {v\<^sub>0, v\<^sub>2}"
    by (rule insert_commute)
  have h20: "closed_segment v\<^sub>2 v\<^sub>0 = geotop_convex_hull {v\<^sub>0, v\<^sub>2}"
    using segment_convex_hull[of v\<^sub>2 v\<^sub>0] geotop_convex_hull_eq_HOL[of "{v\<^sub>2, v\<^sub>0}"]
      h20_set by (by100 simp)
  have hfront_order:
    "frontier \<sigma> =
      geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<union>
      geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<union>
      geotop_convex_hull {v\<^sub>0, v\<^sub>2}"
    using hfront h01 h12 h20 by (by100 simp)
  have hunion_order:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<union>
      geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<union>
      geotop_convex_hull {v\<^sub>0, v\<^sub>2}
    =
      geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<union>
      geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<union>
      geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
    by (by100 blast)
  show ?thesis
    using hfront_order hunion_order by (by100 simp)
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

lemma geotop_simplex_vertex_notin_hull_of_other_vertices_prefix:
  fixes \<sigma> :: "(real^2) set" and V W :: "(real^2) set"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hvV: "v \<in> V"
  assumes hW_sub: "W \<subseteq> V - {v}"
  shows "v \<notin> geotop_convex_hull W"
proof -
  have hV_ai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF h\<sigma>V])
  have hW_sub_V: "W \<subseteq> V"
    using hW_sub by (by100 blast)
  have hW_ai: "\<not> affine_dependent W"
    by (rule affine_independent_subset[OF hV_ai hW_sub_V])
  have hinsert_sub: "insert v W \<subseteq> V"
    using hvV hW_sub by (by100 blast)
  have hinsert_ai: "\<not> affine_dependent (insert v W)"
    by (rule affine_independent_subset[OF hV_ai hinsert_sub])
  have hv_not_W: "v \<notin> W"
    using hW_sub by (by100 blast)
  have hv_not_aff: "v \<notin> affine hull W"
  proof
    assume hv_aff: "v \<in> affine hull W"
    have "affine_dependent (insert v W)"
      using affine_dependent_choose[OF hW_ai, of v] hv_not_W hv_aff
      by (by100 simp)
    thus False
      using hinsert_ai by (by100 blast)
  qed
  have hconv_sub_aff: "convex hull W \<subseteq> affine hull W"
    by (rule convex_hull_subset_affine_hull)
  show ?thesis
  proof
    assume hv_hull: "v \<in> geotop_convex_hull W"
    have "v \<in> convex hull W"
      using hv_hull geotop_convex_hull_eq_HOL[of W] by (by100 simp)
    hence "v \<in> affine hull W"
      using hconv_sub_aff by (by100 blast)
    thus False
      using hv_not_aff by (by100 blast)
  qed
qed

lemma geotop_2simplex_face_containing_edge_eq_edge_or_simplex_prefix:
  fixes F e \<sigma> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes hF\<sigma>: "geotop_is_face F \<sigma>"
  assumes hedge: "geotop_is_edge e"
  assumes heF: "e \<subseteq> F"
  shows "F = e \<or> F = \<sigma>"
  (**
    Face-lattice form used by the two-triangle disk base case: inside a
    2-simplex there is no face strictly between an edge and the full simplex. **)
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and he_eq: "e = geotop_convex_hull W"
    and heW: "geotop_simplex_vertices e W"
    and hW_card: "card W = 2"
    by (rule geotop_edge_face_witness_card_two_prefix[OF hedge he\<sigma>])
  obtain V\<^sub>F W\<^sub>F where h\<sigma>VF: "geotop_simplex_vertices \<sigma> V\<^sub>F"
    and hWF_ne: "W\<^sub>F \<noteq> {}"
    and hWF_sub: "W\<^sub>F \<subseteq> V\<^sub>F"
    and hF_eq: "F = geotop_convex_hull W\<^sub>F"
    and hFWF: "geotop_simplex_vertices F W\<^sub>F"
    by (rule geotop_face_witness_simplex_vertices_prefix[OF hF\<sigma>])
  have hVF_eq: "V\<^sub>F = V"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>VF h\<sigma>V])
  have hWF_sub_V: "W\<^sub>F \<subseteq> V"
    using hWF_sub hVF_eq by (by100 simp)
  have hW_sub_WF: "W \<subseteq> W\<^sub>F"
  proof
    fix x
    assume hxW: "x \<in> W"
    have hxV: "x \<in> V"
      using hxW hW_sub by (by100 blast)
    have hx_e: "x \<in> e"
    proof -
      have "x \<in> convex hull W"
        using hxW hull_inc[of x W] by (by100 simp)
      hence "x \<in> geotop_convex_hull W"
        using geotop_convex_hull_eq_HOL[of W] by (by100 simp)
      thus ?thesis
        using he_eq by (by100 simp)
    qed
    have hxF: "x \<in> F"
      using hx_e heF by (by100 blast)
    show "x \<in> W\<^sub>F"
    proof (rule ccontr)
      assume hx_not_WF: "\<not> x \<in> W\<^sub>F"
      have hWF_sub_no_x: "W\<^sub>F \<subseteq> V - {x}"
        using hWF_sub_V hx_not_WF by (by100 blast)
      have hx_not_hull: "x \<notin> geotop_convex_hull W\<^sub>F"
        by (rule geotop_simplex_vertex_notin_hull_of_other_vertices_prefix
            [OF h\<sigma>V hxV hWF_sub_no_x])
      have "x \<in> geotop_convex_hull W\<^sub>F"
        using hxF hF_eq by (by100 simp)
      thus False
        using hx_not_hull by (by100 blast)
    qed
  qed
  have hV_card: "card V = 3"
  proof -
    obtain V2 m where hV2_fin: "finite V2"
      and hV2_card: "card V2 = 2 + 1"
      and h2_le_m: "2 \<le> m"
      and hgp_V2: "geotop_general_position V2 m"
      and h\<sigma>_eq_V2: "\<sigma> = geotop_convex_hull V2"
      using h\<sigma>2 unfolding geotop_simplex_dim_def by (by100 blast)
    have h\<sigma>V2: "geotop_simplex_vertices \<sigma> V2"
      unfolding geotop_simplex_vertices_def
      using hV2_fin hV2_card h2_le_m hgp_V2 h\<sigma>_eq_V2 by (by100 blast)
    have hV_eq: "V = V2"
      by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>V2])
    show ?thesis
      using hV_eq hV2_card by (by100 simp)
  qed
  have hV_fin: "finite V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hWF_cases: "W\<^sub>F = W \<or> W\<^sub>F = V"
  proof (cases "W\<^sub>F = W")
    case True
    show ?thesis
      using True by (by100 blast)
  next
    case False
    have hWF_fin: "finite W\<^sub>F"
      using hFWF unfolding geotop_simplex_vertices_def by (by100 blast)
    have hW_psub_WF: "W \<subset> W\<^sub>F"
      using hW_sub_WF False by (by100 blast)
    have hW_card_lt: "card W < card W\<^sub>F"
      by (rule psubset_card_mono[OF hWF_fin hW_psub_WF])
    have hWF_le_V: "card W\<^sub>F \<le> card V"
      by (rule card_mono[OF hV_fin hWF_sub_V])
    have hWF_card: "card W\<^sub>F = card V"
      using hW_card hW_card_lt hWF_le_V hV_card by (by100 arith)
    have hWF_eq_V: "W\<^sub>F = V"
    proof (rule card_seteq[OF hV_fin hWF_sub_V])
      show "card V \<le> card W\<^sub>F"
        using hWF_card by (by100 simp)
    qed
    show ?thesis
      using hWF_eq_V by (by100 blast)
  qed
  show ?thesis
  proof -
    have h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
      using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
    from hWF_cases show ?thesis
    proof
      assume hWF_eq_W: "W\<^sub>F = W"
      have "F = e"
        using hWF_eq_W hF_eq he_eq by (by100 simp)
      show ?thesis
        using \<open>F = e\<close> by (by100 blast)
    next
      assume hWF_eq_V: "W\<^sub>F = V"
      have "F = \<sigma>"
        using hWF_eq_V hF_eq h\<sigma>_eq by (by100 simp)
      show ?thesis
        using \<open>F = \<sigma>\<close> by (by100 blast)
    qed
  qed
qed

lemma geotop_complex_two_2simplex_shared_edge_inter_eq_edge_prefix:
  fixes K :: "(real^2) set set"
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  assumes hedge: "geotop_is_edge e"
  shows "\<sigma> \<inter> \<tau> = e"
  (**
    In a complex, two distinct 2-simplexes sharing an edge intersect exactly in
    that edge. **)
proof -
  let ?I = "\<sigma> \<inter> \<tau>"
  have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
    by (rule geotop_is_face_imp_subset_prefix[OF he\<sigma>])
  have he_sub_\<tau>: "e \<subseteq> \<tau>"
    by (rule geotop_is_face_imp_subset_prefix[OF he\<tau>])
  have he_nonempty: "e \<noteq> {}"
  proof -
    have he_dim: "geotop_simplex_dim e 1"
      using hedge unfolding geotop_is_edge_def by (by100 simp)
    have he_simplex: "geotop_is_simplex e"
      by (rule geotop_simplex_dim_imp_is_simplex[OF he_dim])
    show ?thesis
      by (rule geotop_simplex_nonempty[OF he_simplex])
  qed
  have he_sub_I: "e \<subseteq> ?I"
    using he_sub_\<sigma> he_sub_\<tau> by (by100 blast)
  have hI_nonempty: "?I \<noteq> {}"
    using he_nonempty he_sub_I by (by100 blast)
  have hI_face_\<sigma>: "geotop_is_face ?I \<sigma>"
    using geotop_is_complex_intersection[OF hK] h\<sigma>K h\<tau>K hI_nonempty
    by (by100 blast)
  have hI_face_\<tau>: "geotop_is_face ?I \<tau>"
    using geotop_is_complex_intersection[OF hK] h\<sigma>K h\<tau>K hI_nonempty
    by (by100 blast)
  have hcase_\<sigma>: "?I = e \<or> ?I = \<sigma>"
    by (rule geotop_2simplex_face_containing_edge_eq_edge_or_simplex_prefix
        [OF h\<sigma>2 he\<sigma> hI_face_\<sigma> hedge he_sub_I])
  have hcase_\<tau>: "?I = e \<or> ?I = \<tau>"
    by (rule geotop_2simplex_face_containing_edge_eq_edge_or_simplex_prefix
        [OF h\<tau>2 he\<tau> hI_face_\<tau> hedge he_sub_I])
  show ?thesis
  proof (rule ccontr)
    assume hnot: "\<not> ?thesis"
    have hI_eq_\<sigma>: "?I = \<sigma>"
      using hcase_\<sigma> hnot by (by100 blast)
    have hI_eq_\<tau>: "?I = \<tau>"
      using hcase_\<tau> hnot by (by100 blast)
    have "\<sigma> = \<tau>"
      using hI_eq_\<sigma> hI_eq_\<tau> by (by100 simp)
    thus False
      using h\<sigma>\<tau> by (by100 blast)
  qed
qed

lemma geotop_complex_subset_simplex_face_prefix:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes hsub: "\<tau> \<subseteq> \<sigma>"
  shows "geotop_is_face \<tau> \<sigma>"
  (**
    Complex intersection axiom in subset form: if one simplex of a complex is
    contained in another, then it is a face of the larger simplex. **)
proof -
  have h\<tau>_ne: "\<tau> \<noteq> {}"
    by (rule geotop_complex_simplex_nonempty[OF hK h\<tau>K])
  have hcap: "\<tau> \<inter> \<sigma> = \<tau>"
    using hsub by (by100 blast)
  have hcap_ne: "\<tau> \<inter> \<sigma> \<noteq> {}"
    using hcap h\<tau>_ne by (by100 simp)
  have hK_inter: "\<forall>\<sigma>'\<in>K. \<forall>\<tau>'\<in>K. \<sigma>' \<inter> \<tau>' \<noteq> {} \<longrightarrow>
      geotop_is_face (\<sigma>' \<inter> \<tau>') \<sigma>' \<and> geotop_is_face (\<sigma>' \<inter> \<tau>') \<tau>'"
    using hK unfolding geotop_is_complex_def by (by100 blast)
  have hface_cap: "geotop_is_face (\<tau> \<inter> \<sigma>) \<sigma>"
    using hK_inter h\<tau>K h\<sigma>K hcap_ne by (by100 blast)
  show ?thesis
    using hface_cap hcap by (by100 simp)
qed

lemma geotop_edge_closed_segment_obtain_prefix:
  fixes e :: "(real^2) set"
  assumes hedge: "geotop_is_edge e"
  obtains a b where "a \<noteq> b" and "e = closed_segment a b"
  (**
    Coordinate-free edge normalization used in edge-incidence bookkeeping. **)
proof -
  have he_dim: "geotop_simplex_dim e 1"
    using hedge unfolding geotop_is_edge_def by (by100 simp)
  obtain V m where hV_fin: "finite V"
    and hV_card: "card V = 1 + 1"
    and hgp: "geotop_general_position V m"
    and he_eq: "e = geotop_convex_hull V"
    using he_dim unfolding geotop_simplex_dim_def by (by100 blast)
  have hV_card2: "card V = 2"
    using hV_card by (by100 simp)
  obtain a b where hab: "a \<noteq> b" and hV_eq: "V = {a, b}"
    using hV_card2 hV_fin by (auto simp: card_2_iff)
  have "e = geotop_convex_hull {a, b}"
    using he_eq hV_eq by (by100 simp)
  also have "\<dots> = convex hull {a, b}"
    by (rule geotop_convex_hull_eq_HOL)
  also have "\<dots> = closed_segment a b"
    by (rule segment_convex_hull[symmetric])
  finally have he_seg: "e = closed_segment a b" .
  show ?thesis
    by (rule that[OF hab he_seg])
qed

lemma geotop_edge_face_of_edge_eq_prefix:
  fixes e \<tau> :: "(real^2) set"
  assumes hedge: "geotop_is_edge e"
  assumes h\<tau>edge: "geotop_is_edge \<tau>"
  assumes hface: "geotop_is_face e \<tau>"
  shows "e = \<tau>"
  (**
    A 1-face of a 1-simplex is the whole 1-simplex. **)
proof -
  obtain V W where h\<tau>V: "geotop_simplex_vertices \<tau> V"
    and hW_sub: "W \<subseteq> V"
    and he_eq: "e = geotop_convex_hull W"
    and heW: "geotop_simplex_vertices e W"
    and hW_card: "card W = 2"
    by (rule geotop_edge_face_witness_card_two_prefix[OF hedge hface])
  have h\<tau>dim: "geotop_simplex_dim \<tau> 1"
    using h\<tau>edge unfolding geotop_is_edge_def by (by100 simp)
  obtain V\<^sub>\<tau> m where hV\<^sub>\<tau>_fin: "finite V\<^sub>\<tau>"
    and hV\<^sub>\<tau>_card: "card V\<^sub>\<tau> = 1 + 1"
    and h1_le_m: "1 \<le> m"
    and hgp_V\<^sub>\<tau>: "geotop_general_position V\<^sub>\<tau> m"
    and h\<tau>_eq: "\<tau> = geotop_convex_hull V\<^sub>\<tau>"
    using h\<tau>dim unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<tau>V\<^sub>\<tau>: "geotop_simplex_vertices \<tau> V\<^sub>\<tau>"
    unfolding geotop_simplex_vertices_def
    using hV\<^sub>\<tau>_fin hV\<^sub>\<tau>_card h1_le_m hgp_V\<^sub>\<tau> h\<tau>_eq by (by100 blast)
  have hV_eq: "V = V\<^sub>\<tau>"
    by (rule geotop_simplex_vertices_unique[OF h\<tau>V h\<tau>V\<^sub>\<tau>])
  have hW_fin: "finite W"
    by (rule finite_subset[OF _ hV\<^sub>\<tau>_fin]) (use hW_sub hV_eq in \<open>by100 simp\<close>)
  have hW_eq: "W = V\<^sub>\<tau>"
  proof (rule card_subset_eq)
    show "finite V\<^sub>\<tau>"
      by (rule hV\<^sub>\<tau>_fin)
    show "W \<subseteq> V\<^sub>\<tau>"
      using hW_sub hV_eq by (by100 simp)
    show "card W = card V\<^sub>\<tau>"
      using hW_card hV\<^sub>\<tau>_card by (by100 simp)
  qed
  show ?thesis
    using he_eq h\<tau>_eq hW_eq by (by100 simp)
qed

lemma geotop_edge_face_in_ge_2_simplex_has_2_face_prefix:
  fixes e \<sigma> :: "(real^2) set"
  assumes hedge: "geotop_is_edge e"
  assumes hface: "geotop_is_face e \<sigma>"
  assumes h\<sigma>dim: "geotop_simplex_dim \<sigma> n"
  assumes hn: "2 \<le> n"
  shows "\<exists>\<tau>. geotop_is_face \<tau> \<sigma> \<and> geotop_simplex_dim \<tau> 2 \<and> e \<subseteq> \<tau>"
  (**
    If an edge is a face of a simplex of dimension at least two, it is contained
    in some 2-face of that simplex. **)
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and he_eq: "e = geotop_convex_hull W"
    and heW: "geotop_simplex_vertices e W"
    and hW_card: "card W = 2"
    by (rule geotop_edge_face_witness_card_two_prefix[OF hedge hface])
  obtain V\<^sub>\<sigma> m where hV\<^sub>\<sigma>_fin: "finite V\<^sub>\<sigma>"
    and hV\<^sub>\<sigma>_card: "card V\<^sub>\<sigma> = n + 1"
    and hn_le_m: "n \<le> m"
    and hgp_V\<^sub>\<sigma>: "geotop_general_position V\<^sub>\<sigma> m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V\<^sub>\<sigma>"
    using h\<sigma>dim unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V\<^sub>\<sigma>: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>"
    unfolding geotop_simplex_vertices_def
    using hV\<^sub>\<sigma>_fin hV\<^sub>\<sigma>_card hn_le_m hgp_V\<^sub>\<sigma> h\<sigma>_eq by (by100 blast)
  have hV_eq: "V = V\<^sub>\<sigma>"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>V\<^sub>\<sigma>])
  have hW_sub_V\<^sub>\<sigma>: "W \<subseteq> V\<^sub>\<sigma>"
    using hW_sub hV_eq by (by100 simp)
  have hV\<^sub>\<sigma>_ge3: "3 \<le> card V\<^sub>\<sigma>"
    using hV\<^sub>\<sigma>_card hn by (by100 linarith)
  have hW_fin: "finite W"
    using hW_sub_V\<^sub>\<sigma> hV\<^sub>\<sigma>_fin by (rule finite_subset)
  have "\<not> V\<^sub>\<sigma> \<subseteq> W"
  proof
    assume hV_sub_W: "V\<^sub>\<sigma> \<subseteq> W"
    have "card V\<^sub>\<sigma> \<le> card W"
      by (rule card_mono[OF hW_fin hV_sub_W])
    thus False
      using hV\<^sub>\<sigma>_ge3 hW_card by (by100 linarith)
  qed
  then obtain u where huV: "u \<in> V\<^sub>\<sigma>" and huW: "u \<notin> W"
    by (by100 blast)
  let ?X = "W \<union> {u}"
  have hX_sub: "?X \<subseteq> V\<^sub>\<sigma>"
    using hW_sub_V\<^sub>\<sigma> huV by (by100 blast)
  have hX_ne: "?X \<noteq> {}"
    using huV by (by100 blast)
  have hX_fin: "finite ?X"
    using hW_fin by (by100 simp)
  have hX_card: "card ?X = 3"
    using hW_fin hW_card huW by (by100 simp)
  have hm_ge2: "2 \<le> m"
    using hn hn_le_m by (by100 linarith)
  have hgp_X: "geotop_general_position ?X m"
    by (rule geotop_general_position_subset[OF hgp_V\<^sub>\<sigma> hX_sub])
  define \<tau> where "\<tau> = geotop_convex_hull ?X"
  have h\<tau>face: "geotop_is_face \<tau> \<sigma>"
    unfolding \<tau>_def
    by (rule geotop_is_face_of_subset[OF h\<sigma>V\<^sub>\<sigma> hX_ne hX_sub])
  have h\<tau>dim: "geotop_simplex_dim \<tau> 2"
  proof -
    have hX_card_dim: "card ?X = 2 + 1"
      using hX_card by (by100 simp)
    show ?thesis
      unfolding geotop_simplex_dim_def \<tau>_def
      using hX_fin hX_card_dim hm_ge2 hgp_X by (by100 blast)
  qed
  have hesub: "e \<subseteq> \<tau>"
  proof -
    have hmono: "convex hull W \<subseteq> convex hull ?X"
      by (rule hull_mono) (by100 blast)
    show ?thesis
      using hmono he_eq \<tau>_def geotop_convex_hull_eq_HOL[of W]
        geotop_convex_hull_eq_HOL[of ?X]
      by (by100 simp)
  qed
  show ?thesis
    using h\<tau>face h\<tau>dim hesub by (by100 blast)
qed

lemma geotop_complex_edge_in_higher_simplex_has_2_simplex_prefix:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hsub: "e \<subseteq> \<sigma>"
  assumes h\<sigma>dim: "geotop_simplex_dim \<sigma> n"
  assumes hn: "2 \<le> n"
  shows "\<exists>\<tau>\<in>K. geotop_simplex_dim \<tau> 2 \<and> e \<subseteq> \<tau>"
  (**
    Complex form of the preceding face-extension lemma, closing the produced
    2-face back into the complex. **)
proof -
  have hface: "geotop_is_face e \<sigma>"
    by (rule geotop_complex_subset_simplex_face_prefix[OF hK heK h\<sigma>K hsub])
  obtain \<tau> where h\<tau>face: "geotop_is_face \<tau> \<sigma>"
    and h\<tau>dim: "geotop_simplex_dim \<tau> 2"
    and he\<tau>: "e \<subseteq> \<tau>"
    using geotop_edge_face_in_ge_2_simplex_has_2_face_prefix
      [OF hedge hface h\<sigma>dim hn]
    by (by100 blast)
  have hface_closed: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    using hK unfolding geotop_is_complex_def by (by100 blast)
  have h\<tau>K: "\<tau> \<in> K"
    using hface_closed h\<sigma>K h\<tau>face by (by100 blast)
  show ?thesis
    using h\<tau>K h\<tau>dim he\<tau> by (by100 blast)
qed

lemma geotop_no_2_simplex_containing_edge_simplex_meeting_rel_interior_subset_prefix:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hmeet: "\<tau> \<inter> rel_interior e \<noteq> {}"
  assumes hno2: "\<not> (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>)"
  shows "\<tau> \<subseteq> e"
  (**
    If no 2-simplex of a complex lies over an edge, then every simplex meeting
    the edge interior is contained in the edge. **)
proof -
  obtain x where hx\<tau>: "x \<in> \<tau>" and hxe_rel: "x \<in> rel_interior e"
    using hmeet by (by100 blast)
  have he_sub_\<tau>: "e \<subseteq> \<tau>"
    by (rule geotop_complex_rel_interior_imp_subset[OF hK heK h\<tau>K hxe_rel hx\<tau>])
  have h\<tau>simp: "geotop_is_simplex \<tau>"
    using geotop_is_complex_simplex[OF hK] h\<tau>K by (by100 blast)
  obtain n where h\<tau>dim: "geotop_simplex_dim \<tau> n"
    using h\<tau>simp unfolding geotop_is_simplex_def geotop_simplex_dim_def
    by (by100 blast)
  have hn_le1: "n \<le> 1"
  proof (rule ccontr)
    assume "\<not> n \<le> 1"
    hence hn_ge2: "2 \<le> n"
      by (by100 simp)
    have "\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>"
      by (rule geotop_complex_edge_in_higher_simplex_has_2_simplex_prefix
          [OF hK heK h\<tau>K hedge he_sub_\<tau> h\<tau>dim hn_ge2])
    thus False
      using hno2 by (by100 blast)
  qed
  have hn_cases: "n = 0 \<or> n = 1"
    using hn_le1 by (by100 linarith)
  show ?thesis
  proof (rule disjE[OF hn_cases])
    assume hn0: "n = 0"
    obtain a b where hab: "a \<noteq> b" and he_seg: "e = closed_segment a b"
      by (rule geotop_edge_closed_segment_obtain_prefix[OF hedge])
    obtain V m where hV_fin: "finite V"
      and hV_card: "card V = 0 + 1"
      and h\<tau>_eq: "\<tau> = geotop_convex_hull V"
      using h\<tau>dim hn0 unfolding geotop_simplex_dim_def by (by100 blast)
    have hV_card1: "card V = 1"
      using hV_card by (by100 simp)
    obtain c where hV_eq: "V = {c}"
      using hV_card1 by (rule card_1_singletonE)
    have h\<tau>_sing: "\<tau> = {c}"
      using h\<tau>_eq hV_eq geotop_convex_hull_eq_HOL[of "{c}"] by (by100 simp)
    have ha\<tau>: "a \<in> \<tau>"
    proof -
      have "a \<in> e"
        using he_seg by (by100 simp)
      thus ?thesis
        using he_sub_\<tau> by (by100 blast)
    qed
    have hb\<tau>: "b \<in> \<tau>"
    proof -
      have "b \<in> e"
        using he_seg by (by100 simp)
      thus ?thesis
        using he_sub_\<tau> by (by100 blast)
    qed
    have "a = b"
      using ha\<tau> hb\<tau> h\<tau>_sing by (by100 simp)
    thus ?thesis
      using hab by (by100 blast)
  next
    assume hn1: "n = 1"
    have h\<tau>edge: "geotop_is_edge \<tau>"
      using h\<tau>dim hn1 unfolding geotop_is_edge_def by (by100 simp)
    have hface: "geotop_is_face e \<tau>"
      by (rule geotop_complex_subset_simplex_face_prefix[OF hK heK h\<tau>K he_sub_\<tau>])
    have heq: "e = \<tau>"
      by (rule geotop_edge_face_of_edge_eq_prefix[OF hedge h\<tau>edge hface])
    show ?thesis
      using heq by (by100 simp)
  qed
qed

lemma geotop_complex_point_finite_local_carrier_prefix:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hx: "x \<in> geotop_polyhedron K"
  shows "\<exists>r F. 0 < r \<and> finite F \<and> F \<subseteq> K
      \<and> ball x r \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
  (**
    Local finiteness of a complex, packaged as a finite carrier cover around a
    point of the polyhedron. **)
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

lemma geotop_complex_edge_point_finite_local_cover_prefix:
  fixes K :: "(real^2) set set" and e :: "(real^2) set" and p :: "real^2"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hp: "p \<in> e"
  shows "\<exists>r F. 0 < r \<and> finite F \<and> F \<subseteq> K \<and> e \<in> F
      \<and> ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
  (**
    Edge-point form of the same local finite cover, retaining the edge itself
    in the finite family. **)
proof -
  have hpM: "p \<in> geotop_polyhedron K"
    using heK hp unfolding geotop_polyhedron_def by (by100 blast)
  obtain r F where hr: "0 < r"
    and hFfin: "finite F"
    and hFsub: "F \<subseteq> K"
    and hcover: "ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
    using geotop_complex_point_finite_local_carrier_prefix[OF hK hpM]
    by (by100 blast)
  let ?F = "insert e F"
  have hFfin': "finite ?F"
    using hFfin by (by100 simp)
  have hFsub': "?F \<subseteq> K"
    using heK hFsub by (by100 blast)
  have hcover': "ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>?F"
    using hcover by (by100 blast)
  show ?thesis
    using hr hFfin' hFsub' hcover' by (by100 blast)
qed

lemma geotop_complex_edge_unique_face_count_eq_1_prefix:
  fixes K :: "(real^2) set set" and e :: "(real^2) set"
  assumes hunique:
    "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  shows "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
  (**
    Unique incident 2-simplex, converted to the cardinality form used by
    edge-star case splits. **)
proof -
  let ?S = "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
  let ?P = "\<lambda>\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  have hunique_def: "\<exists>\<sigma>. ?P \<sigma> \<and> (\<forall>\<tau>. ?P \<tau> \<longrightarrow> \<tau> = \<sigma>)"
    using hunique unfolding Ex1_def by (by100 simp)
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
    and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and h\<sigma>face: "geotop_is_face e \<sigma>"
    and huniq_all: "\<forall>\<tau>. ?P \<tau> \<longrightarrow> \<tau> = \<sigma>"
    using hunique_def by (elim exE conjE)
  have huniqP: "\<And>\<tau>. ?P \<tau> \<Longrightarrow> \<tau> = \<sigma>"
    using huniq_all by (by100 simp)
  have hSeq: "?S = {\<sigma>}"
  proof
    show "?S \<subseteq> {\<sigma>}"
    proof
      fix \<tau>
      assume h\<tau>S: "\<tau> \<in> ?S"
      have h\<tau>K: "\<tau> \<in> K"
        using h\<tau>S by (by100 simp)
      have h\<tau>2: "geotop_simplex_dim \<tau> 2"
        using h\<tau>S by (by100 simp)
      have h\<tau>face: "geotop_is_face e \<tau>"
        using h\<tau>S by (by100 simp)
      have h\<tau>P: "?P \<tau>"
        using h\<tau>K h\<tau>2 h\<tau>face by (by100 simp)
      have "\<tau> = \<sigma>"
        by (rule huniqP[OF h\<tau>P])
      thus "\<tau> \<in> {\<sigma>}"
        by (by100 simp)
    qed
  next
    show "{\<sigma>} \<subseteq> ?S"
      using h\<sigma>K h\<sigma>2 h\<sigma>face by (by100 simp)
  qed
  show ?thesis
    using hSeq by (by100 simp)
qed

lemma geotop_complex_edge_unique_face_obtain_prefix:
  fixes K :: "(real^2) set set" and e :: "(real^2) set"
  assumes hunique:
    "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  obtains \<sigma> where "\<sigma> \<in> K" and "geotop_simplex_dim \<sigma> 2" and "geotop_is_face e \<sigma>"
    and "{\<tau>\<in>K. geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>} = {\<sigma>}"
  (**
    Obtain form of the unique incident 2-simplex fact. **)
proof -
  let ?S = "{\<tau>\<in>K. geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>}"
  let ?P = "\<lambda>\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  have hunique_def: "\<exists>\<sigma>. ?P \<sigma> \<and> (\<forall>\<tau>. ?P \<tau> \<longrightarrow> \<tau> = \<sigma>)"
    using hunique unfolding Ex1_def by (by100 simp)
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
    and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and h\<sigma>face: "geotop_is_face e \<sigma>"
    and huniq_all: "\<forall>\<tau>. ?P \<tau> \<longrightarrow> \<tau> = \<sigma>"
    using hunique_def by (elim exE conjE)
  have huniqP: "\<And>\<tau>. ?P \<tau> \<Longrightarrow> \<tau> = \<sigma>"
    using huniq_all by (by100 simp)
  have hSeq: "?S = {\<sigma>}"
  proof
    show "?S \<subseteq> {\<sigma>}"
    proof
      fix \<tau>
      assume h\<tau>S: "\<tau> \<in> ?S"
      have h\<tau>K: "\<tau> \<in> K"
        using h\<tau>S by (by100 simp)
      have h\<tau>2: "geotop_simplex_dim \<tau> 2"
        using h\<tau>S by (by100 simp)
      have h\<tau>face: "geotop_is_face e \<tau>"
        using h\<tau>S by (by100 simp)
      have h\<tau>P: "?P \<tau>"
        using h\<tau>K h\<tau>2 h\<tau>face by (by100 simp)
      have "\<tau> = \<sigma>"
        by (rule huniqP[OF h\<tau>P])
      thus "\<tau> \<in> {\<sigma>}"
        by (by100 simp)
    qed
  next
    show "{\<sigma>} \<subseteq> ?S"
      using h\<sigma>K h\<sigma>2 h\<sigma>face by (by100 simp)
  qed
  show ?thesis
    by (rule that[OF h\<sigma>K h\<sigma>2 h\<sigma>face hSeq])
qed

lemma geotop_complex_unique_edge_face_point_finite_local_cover_prefix:
  fixes K :: "(real^2) set set" and e :: "(real^2) set" and p :: "real^2"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hp: "p \<in> e"
  assumes hunique:
    "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  obtains r F \<sigma>
    where "0 < r"
      and "finite F"
      and "F \<subseteq> K"
      and "e \<in> F"
      and "\<sigma> \<in> F"
      and "\<sigma> \<in> K"
      and "geotop_simplex_dim \<sigma> 2"
      and "geotop_is_face e \<sigma>"
      and "{\<tau>\<in>K. geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>} = {\<sigma>}"
      and "ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
  (**
    Local finite cover around a point of an edge with a unique incident
    2-simplex, retaining both the edge and that 2-simplex in the finite
    family. **)
proof -
  obtain r F where hr: "0 < r"
    and hFfin: "finite F"
    and hFsub: "F \<subseteq> K"
    and heF: "e \<in> F"
    and hcover: "ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>F"
    using geotop_complex_edge_point_finite_local_cover_prefix[OF hK heK hp]
    by (by100 blast)
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
    and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and h\<sigma>face: "geotop_is_face e \<sigma>"
    and hfaces: "{\<tau>\<in>K. geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>} = {\<sigma>}"
    by (rule geotop_complex_edge_unique_face_obtain_prefix[OF hunique])
  let ?F = "insert \<sigma> F"
  have hFfin': "finite ?F"
    using hFfin by (by100 simp)
  have hFsub': "?F \<subseteq> K"
    using hFsub h\<sigma>K by (by100 blast)
  have heF': "e \<in> ?F"
    using heF by (by100 simp)
  have h\<sigma>F': "\<sigma> \<in> ?F"
    by (by100 simp)
  have hcover': "ball p r \<inter> geotop_polyhedron K \<subseteq> \<Union>?F"
    using hcover by (by100 blast)
  show ?thesis
    by (rule that[OF hr hFfin' hFsub' heF' h\<sigma>F' h\<sigma>K h\<sigma>2 h\<sigma>face hfaces hcover'])
qed

lemma geotop_complex_finite_subcomplex_local_point_carriers_prefix:
  fixes K F :: "(real^2) set set" and p :: "real^2"
  assumes hK: "geotop_is_complex K"
  assumes hFfin: "finite F"
  assumes hFsub: "F \<subseteq> K"
  assumes hpF: "p \<in> \<Union>F"
  shows "\<exists>\<delta>>0. ball p \<delta> \<inter> \<Union>F \<subseteq> \<Union>{\<tau>\<in>F. p \<in> \<tau>}"
  (**
    In a finite subfamily of a complex, sufficiently close points can only lie
    in members that already contain the center point. **)
proof -
  have hclosed: "\<forall>\<tau>\<in>F. closed \<tau>"
  proof
    fix \<tau>
    assume h\<tau>F: "\<tau> \<in> F"
    have h\<tau>K: "\<tau> \<in> K"
      using hFsub h\<tau>F by (by100 blast)
    show "closed \<tau>"
      by (rule geotop_complex_simplex_closed[OF hK h\<tau>K])
  qed
  have hB: "\<Union>F = \<Union>F"
    by (by100 simp)
  show ?thesis
    by (rule finite_union_closed_local_isolation[OF hFfin hclosed hB hpF])
qed

lemma geotop_complex_unique_edge_face_point_carrier_subset_unique_face_prefix:
  fixes K :: "(real^2) set set" and e \<sigma> \<tau> :: "(real^2) set" and p :: "real^2"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>face: "geotop_is_face e \<sigma>"
  assumes hfaces: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>}"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes hp\<tau>: "p \<in> \<tau>"
  shows "\<tau> \<subseteq> \<sigma>"
  (**
    If an edge has one incident 2-simplex, every simplex containing an interior
    point of the edge is contained in that 2-simplex. **)
proof -
  have he_sub_\<tau>: "e \<subseteq> \<tau>"
    by (rule geotop_complex_rel_interior_imp_subset[OF hK heK h\<tau>K hp hp\<tau>])
  have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
    by (rule geotop_is_face_imp_subset_prefix[OF h\<sigma>face])
  have h\<tau>simp: "geotop_is_simplex \<tau>"
    using geotop_is_complex_simplex[OF hK] h\<tau>K by (by100 blast)
  obtain n where h\<tau>dim: "geotop_simplex_dim \<tau> n"
    using h\<tau>simp unfolding geotop_is_simplex_def geotop_simplex_dim_def
    by (by100 blast)
  have hn_le2: "n \<le> 2"
    by (rule geotop_simplex_dim_le_2_R2_prefix[OF h\<tau>dim])
  show ?thesis
  proof (cases "n = 2")
    case True
    have h\<tau>2: "geotop_simplex_dim \<tau> 2"
      using h\<tau>dim True by (by100 simp)
    have hface: "geotop_is_face e \<tau>"
      by (rule geotop_complex_subset_simplex_face_prefix[OF hK heK h\<tau>K he_sub_\<tau>])
    have h\<tau>in: "\<tau> \<in> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
      using h\<tau>K h\<tau>2 hface by (by100 simp)
    have "\<tau> = \<sigma>"
      using h\<tau>in hfaces by (by100 simp)
    thus ?thesis
      by (by100 simp)
  next
    case False
    have hn_le1: "n \<le> 1"
      using hn_le2 False by (by100 arith)
    have hn_cases: "n = 0 \<or> n = 1"
      using hn_le1 by (by100 arith)
    show ?thesis
    proof (rule disjE[OF hn_cases])
      assume hn0: "n = 0"
      obtain a b where hab: "a \<noteq> b" and he_seg: "e = closed_segment a b"
        by (rule geotop_edge_closed_segment_obtain_prefix[OF hedge])
      obtain V m where hV_fin: "finite V"
        and hV_card: "card V = 0 + 1"
        and h\<tau>_eq: "\<tau> = geotop_convex_hull V"
        using h\<tau>dim hn0 unfolding geotop_simplex_dim_def by (by100 blast)
      have hV_card1: "card V = 1"
        using hV_card by (by100 simp)
      obtain c where hV_eq: "V = {c}"
        using hV_card1 by (rule card_1_singletonE)
      have h\<tau>_sing: "\<tau> = {c}"
        using h\<tau>_eq hV_eq geotop_convex_hull_eq_HOL[of "{c}"] by (by100 simp)
      have ha\<tau>: "a \<in> \<tau>"
      proof -
        have "a \<in> e"
          using he_seg by (by100 simp)
        thus ?thesis
          using he_sub_\<tau> by (by100 blast)
      qed
      have hb\<tau>: "b \<in> \<tau>"
      proof -
        have "b \<in> e"
          using he_seg by (by100 simp)
        thus ?thesis
          using he_sub_\<tau> by (by100 blast)
      qed
      have "a = b"
        using ha\<tau> hb\<tau> h\<tau>_sing by (by100 simp)
      thus ?thesis
        using hab by (by100 blast)
    next
      assume hn1: "n = 1"
      have h\<tau>edge: "geotop_is_edge \<tau>"
        using h\<tau>dim hn1 unfolding geotop_is_edge_def by (by100 simp)
      have hface: "geotop_is_face e \<tau>"
        by (rule geotop_complex_subset_simplex_face_prefix[OF hK heK h\<tau>K he_sub_\<tau>])
      have heq: "e = \<tau>"
        by (rule geotop_edge_face_of_edge_eq_prefix[OF hedge h\<tau>edge hface])
      show ?thesis
        using heq he_sub_\<sigma> by (by100 blast)
    qed
  qed
qed

lemma geotop_complex_unique_edge_face_point_carrier_union_subset_unique_face_prefix:
  fixes K F :: "(real^2) set set" and e \<sigma> :: "(real^2) set" and p :: "real^2"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>face: "geotop_is_face e \<sigma>"
  assumes hfaces: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>}"
  assumes hFsub: "F \<subseteq> K"
  shows "\<Union>{\<tau>\<in>F. p \<in> \<tau>} \<subseteq> \<sigma>"
  (**
    Union form of the preceding point-carrier restriction for finite local
    families. **)
proof
  fix x
  assume hx: "x \<in> \<Union>{\<tau>\<in>F. p \<in> \<tau>}"
  obtain \<tau> where h\<tau>F: "\<tau> \<in> F" and hp\<tau>: "p \<in> \<tau>" and hx\<tau>: "x \<in> \<tau>"
    using hx by (by100 blast)
  have h\<tau>K: "\<tau> \<in> K"
    using hFsub h\<tau>F by (by100 blast)
  have h\<tau>sub: "\<tau> \<subseteq> \<sigma>"
    by (rule geotop_complex_unique_edge_face_point_carrier_subset_unique_face_prefix
        [OF hK heK hedge hp h\<sigma>K h\<sigma>2 h\<sigma>face hfaces h\<tau>K hp\<tau>])
  show "x \<in> \<sigma>"
    using h\<tau>sub hx\<tau> by (by100 blast)
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

lemma geotop_2simplex_HOL_interior_eq_rel_interior_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  shows "interior \<sigma> = rel_interior \<sigma>"
  (**
    A 2-simplex in the plane has full affine dimension, so its ordinary
    Euclidean interior is its relative interior. **)
proof -
  have hhyper: "geotop_hyperplane_dim (affine hull \<sigma>) 2"
    by (rule geotop_simplex_dim_imp_hyperplane_dim[OF h\<sigma>2])
  have hdim\<sigma>: "aff_dim \<sigma> = 2"
    using geotop_hyperplane_dim_imp_affine_aff_dim[OF hhyper] by (by100 simp)
  have hdim_UNIV: "aff_dim \<sigma> = int (DIM(real^2))"
    using hdim\<sigma> by (by100 simp)
  have hrel_eq_int: "rel_interior \<sigma> = interior \<sigma>"
    by (rule interior_rel_interior[OF hdim_UNIV])
  show ?thesis
    using hrel_eq_int by (by100 simp)
qed

lemma geotop_2simplex_closure_HOL_interior_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  shows "closure (interior \<sigma>) = \<sigma>"
  (**
    Full-dimensional simplex form of the standard simplex fact that the closed
    triangle is the closure of its open triangle interior. **)
proof -
  have hsimplex: "geotop_is_simplex \<sigma>"
    by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>2])
  have hclosure_rel: "closure (rel_interior \<sigma>) = \<sigma>"
    by (rule geotop_simplex_closure_rel_interior[OF hsimplex])
  have hint_rel: "interior \<sigma> = rel_interior \<sigma>"
    by (rule geotop_2simplex_HOL_interior_eq_rel_interior_prefix[OF h\<sigma>2])
  show ?thesis
    using hclosure_rel hint_rel by (by100 simp)
qed

lemma geotop_simplex_dim_bounded_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> n"
  shows "bounded \<sigma>"
  (**
    Simplexes are finite convex hulls, hence bounded. **)
proof -
  obtain V m where hVfin: "finite V"
      and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma> unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>_HOL: "\<sigma> = convex hull V"
    using h\<sigma>_eq geotop_convex_hull_eq_HOL by (by100 simp)
  show ?thesis
    using h\<sigma>_HOL hVfin finite_imp_bounded_convex_hull by (by100 simp)
qed

lemma geotop_simplex_dim_convex_HOL_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> n"
  shows "convex \<sigma>"
  (**
    HOL-convex form of the geotop simplex convexity fact. **)
proof -
  have hsimplex: "geotop_is_simplex \<sigma>"
    by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>])
  have hconv_geotop: "geotop_convex \<sigma>"
    by (rule geotop_simplex_is_convex[OF hsimplex])
  show ?thesis
    using hconv_geotop geotop_convex_iff_HOL_convex by (by100 blast)
qed

lemma geotop_closed_segment_arc_endpoints_prefix:
  fixes P Q :: "real^2"
  assumes hPQ: "P \<noteq> Q"
  shows "geotop_arc_endpoints (closed_segment P Q) {P, Q}"
  (**
    Segment-edge endpoint form used to split a triangle frontier into two
    broken arcs. **)
proof -
  have harc: "geotop_is_arc (closed_segment P Q)
      (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q))"
    by (rule geotop_closed_segment_is_arc[OF hPQ])
  have hcard: "card {P, Q} = 2"
    using hPQ by (by100 simp)
  have hsub: "{P, Q} \<subseteq> closed_segment P Q"
    by (by100 simp)
  have hunit_eq: "{t::real. 0 \<le> t \<and> t \<le> 1} = {0..1}"
    by (by100 auto)
  have h_image: "linepath P Q ` {0..1} = closed_segment P Q"
    by (rule linepath_image_01)
  have h_inj: "inj_on (linepath P Q) {0..1}"
    by (rule inj_on_linepath[OF hPQ])
  have h_cont: "continuous_on {0..1::real} (linepath P Q)"
    by (rule continuous_on_linepath)
  have h_compact: "compact {0..1::real}"
    by (by100 simp)
  have h_image_refl:
      "linepath P Q ` ({0..1}::real set) = linepath P Q ` ({0..1}::real set)"
    by (by100 simp)
  obtain g where hhomeo_img:
      "homeomorphism {0..1} (linepath P Q ` {0..1}) (linepath P Q) g"
    using homeomorphism_compact[OF h_compact h_cont h_image_refl h_inj] by (by100 blast)
  have hhomeo_seg:
      "homeomorphism {0..1} (closed_segment P Q) (linepath P Q) g"
    using hhomeo_img h_image by (by100 simp)
  have htop1_01: "top1_homeomorphism_on {0..1}
      (subspace_topology UNIV geotop_euclidean_topology {0..1})
      (closed_segment P Q)
      (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q))
      (linepath P Q)"
  proof -
    have h_Teucl_real: "is_topology_on (UNIV::real set) geotop_euclidean_topology"
      by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
    have h_Teucl_R2: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
      by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
    have htop_01: "is_topology_on ({0..1}::real set)
        (subspace_topology UNIV geotop_euclidean_topology ({0..1}::real set))"
      by (rule subspace_topology_is_topology_on[OF h_Teucl_real subset_UNIV])
    have htop_seg: "is_topology_on (closed_segment P Q)
        (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q))"
      by (rule subspace_topology_is_topology_on[OF h_Teucl_R2 subset_UNIV])
    have hbij: "bij_betw (linepath P Q) ({0..1}::real set) (closed_segment P Q)"
      unfolding bij_betw_def using h_inj h_image by (by100 simp)
    have hline_img: "linepath P Q ` ({0..1}::real set) \<subseteq> closed_segment P Q"
      using h_image by (by100 simp)
    have hline_top1: "top1_continuous_map_on ({0..1}::real set)
        (subspace_topology UNIV geotop_euclidean_topology ({0..1}::real set))
        (closed_segment P Q)
        (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q))
        (linepath P Q)"
      by (rule geotop_continuous_on_imp_top1_continuous_map_on[OF h_cont hline_img])
    have hg_cont: "continuous_on (closed_segment P Q) g"
      using hhomeo_seg unfolding homeomorphism_def by (by100 blast)
    have hg_img: "g ` (closed_segment P Q) \<subseteq> ({0..1}::real set)"
      using hhomeo_seg unfolding homeomorphism_def by (by100 blast)
    have hg_top1: "top1_continuous_map_on (closed_segment P Q)
        (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q))
        ({0..1}::real set)
        (subspace_topology UNIV geotop_euclidean_topology ({0..1}::real set)) g"
      by (rule geotop_continuous_on_imp_top1_continuous_map_on[OF hg_cont hg_img])
    have hgf_id: "\<forall>y\<in>closed_segment P Q. linepath P Q (g y) = y"
      using hhomeo_seg unfolding homeomorphism_def by (by100 blast)
    have hg_eq_inv:
        "\<forall>y\<in>closed_segment P Q.
          g y = inv_into ({0..1}::real set) (linepath P Q) y"
    proof
      fix y
      assume hy: "y \<in> closed_segment P Q"
      have hgy_in: "g y \<in> ({0..1}::real set)"
        using hg_img hy by (by100 blast)
      have hfgy: "linepath P Q (g y) = y"
        using hgf_id hy by (by100 blast)
      have "inv_into ({0..1}::real set) (linepath P Q) y = g y"
        by (rule inv_into_f_eq[OF h_inj hgy_in hfgy])
      thus "g y = inv_into ({0..1}::real set) (linepath P Q) y"
        by (by100 simp)
    qed
    have hinv_top1: "top1_continuous_map_on (closed_segment P Q)
        (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q))
        ({0..1}::real set)
        (subspace_topology UNIV geotop_euclidean_topology ({0..1}::real set))
        (inv_into ({0..1}::real set) (linepath P Q))"
      using hg_top1 top1_continuous_map_on_cong[OF hg_eq_inv] by (by100 blast)
    show ?thesis
      unfolding top1_homeomorphism_on_def
      using htop_01 htop_seg hbij hline_top1 hinv_top1 by (by100 blast)
  qed
  have htop1_unit: "top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
      (subspace_topology UNIV geotop_euclidean_topology {t::real. 0 \<le> t \<and> t \<le> 1})
      (closed_segment P Q)
      (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q))
      (linepath P Q)"
    using htop1_01 hunit_eq by (by100 simp)
  have hendpoints: "{P, Q} = {linepath P Q 0, linepath P Q 1}"
    unfolding linepath_def by (by100 simp)
  show ?thesis
    unfolding geotop_arc_endpoints_def
    using harc hcard hsub htop1_unit hendpoints by (by100 blast)
qed

lemma geotop_HOL_arc_imp_geotop_arc_endpoints_prefix:
  fixes \<gamma> :: "real \<Rightarrow> real^2"
  assumes h\<gamma>: "arc \<gamma>"
  shows "geotop_arc_endpoints (path_image \<gamma>) {pathstart \<gamma>, pathfinish \<gamma>}"
  (**
    Endpoint bridge for a HOL arc parametrised on the unit interval.  This
    lets the two-edge boundary path of a triangle supply the endpoint data
    required by \<open>pair_of_arcs_is_polygon\<close>. **)
proof -
  have hgeotop_arc: "geotop_is_arc (path_image \<gamma>)
      (subspace_topology UNIV geotop_euclidean_topology (path_image \<gamma>))"
    by (rule geotop_HOL_arc_imp_geotop_is_arc[OF h\<gamma>])
  have hpath: "path \<gamma>"
    using h\<gamma> unfolding arc_def by (by100 blast)
  have hcont: "continuous_on ({0..1}::real set) \<gamma>"
    using hpath unfolding path_def by (by100 simp)
  have hinj: "inj_on \<gamma> ({0..1}::real set)"
    using h\<gamma> unfolding arc_def by (by100 blast)
  have h0in: "(0::real) \<in> {0..1}"
    by (by100 simp)
  have h1in: "(1::real) \<in> {0..1}"
    by (by100 simp)
  have h01: "(0::real) \<noteq> 1"
    by (by100 simp)
  have hend_ne: "pathstart \<gamma> \<noteq> pathfinish \<gamma>"
  proof
    assume heq: "pathstart \<gamma> = pathfinish \<gamma>"
    have h\<gamma>01: "\<gamma> 0 = \<gamma> 1"
      using heq unfolding pathstart_def pathfinish_def by (by100 simp)
    have "0 = (1::real)"
      using hinj h0in h1in h\<gamma>01 unfolding inj_on_def by (by100 blast)
    thus False using h01 by (by100 simp)
  qed
  have hcard: "card {pathstart \<gamma>, pathfinish \<gamma>} = 2"
    using hend_ne by (by100 simp)
  have hsub: "{pathstart \<gamma>, pathfinish \<gamma>} \<subseteq> path_image \<gamma>"
    unfolding pathstart_def pathfinish_def path_image_def by (by100 simp)
  have hunit_eq: "{t::real. 0 \<le> t \<and> t \<le> 1} = {0..1}"
    by (by100 auto)
  have hpath_image: "\<gamma> ` ({0..1}::real set) = path_image \<gamma>"
    unfolding path_image_def by (by100 simp)
  have h_compact: "compact ({0..1}::real set)"
    by (by100 simp)
  have h_image_refl: "\<gamma> ` ({0..1}::real set) = \<gamma> ` ({0..1}::real set)"
    by (by100 simp)
  obtain g where hhomeo_img:
      "homeomorphism ({0..1}::real set) (\<gamma> ` ({0..1}::real set)) \<gamma> g"
    using homeomorphism_compact[OF h_compact hcont h_image_refl hinj] by (by100 blast)
  have hhomeo_path_image:
      "homeomorphism ({0..1}::real set) (path_image \<gamma>) \<gamma> g"
    using hhomeo_img hpath_image by (by100 simp)
  have htop1_01: "top1_homeomorphism_on ({0..1}::real set)
      (subspace_topology UNIV geotop_euclidean_topology ({0..1}::real set))
      (path_image \<gamma>)
      (subspace_topology UNIV geotop_euclidean_topology (path_image \<gamma>)) \<gamma>"
  proof -
    have h_Teucl_real: "is_topology_on (UNIV::real set) geotop_euclidean_topology"
      by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
    have h_Teucl_R2: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
      by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
    have htop_01: "is_topology_on ({0..1}::real set)
        (subspace_topology UNIV geotop_euclidean_topology ({0..1}::real set))"
      by (rule subspace_topology_is_topology_on[OF h_Teucl_real subset_UNIV])
    have htop_img: "is_topology_on (path_image \<gamma>)
        (subspace_topology UNIV geotop_euclidean_topology (path_image \<gamma>))"
      by (rule subspace_topology_is_topology_on[OF h_Teucl_R2 subset_UNIV])
    have hbij: "bij_betw \<gamma> ({0..1}::real set) (path_image \<gamma>)"
      unfolding bij_betw_def using hinj hpath_image by (by100 simp)
    have h\<gamma>_img: "\<gamma> ` ({0..1}::real set) \<subseteq> path_image \<gamma>"
      using hpath_image by (by100 simp)
    have h\<gamma>_top1: "top1_continuous_map_on ({0..1}::real set)
        (subspace_topology UNIV geotop_euclidean_topology ({0..1}::real set))
        (path_image \<gamma>)
        (subspace_topology UNIV geotop_euclidean_topology (path_image \<gamma>)) \<gamma>"
      by (rule geotop_continuous_on_imp_top1_continuous_map_on[OF hcont h\<gamma>_img])
    have hg_cont: "continuous_on (path_image \<gamma>) g"
      using hhomeo_path_image unfolding homeomorphism_def by (by100 blast)
    have hg_img: "g ` (path_image \<gamma>) \<subseteq> ({0..1}::real set)"
      using hhomeo_path_image unfolding homeomorphism_def by (by100 blast)
    have hg_top1: "top1_continuous_map_on (path_image \<gamma>)
        (subspace_topology UNIV geotop_euclidean_topology (path_image \<gamma>))
        ({0..1}::real set)
        (subspace_topology UNIV geotop_euclidean_topology ({0..1}::real set)) g"
      by (rule geotop_continuous_on_imp_top1_continuous_map_on[OF hg_cont hg_img])
    have hgf_id: "\<forall>y\<in>path_image \<gamma>. \<gamma> (g y) = y"
      using hhomeo_path_image unfolding homeomorphism_def by (by100 blast)
    have hg_eq_inv:
        "\<forall>y\<in>path_image \<gamma>.
          g y = inv_into ({0..1}::real set) \<gamma> y"
    proof
      fix y
      assume hy: "y \<in> path_image \<gamma>"
      have hgy_in: "g y \<in> ({0..1}::real set)"
        using hg_img hy by (by100 blast)
      have hfgy: "\<gamma> (g y) = y"
        using hgf_id hy by (by100 blast)
      have "inv_into ({0..1}::real set) \<gamma> y = g y"
        by (rule inv_into_f_eq[OF hinj hgy_in hfgy])
      thus "g y = inv_into ({0..1}::real set) \<gamma> y"
        by (by100 simp)
    qed
    have hinv_top1: "top1_continuous_map_on (path_image \<gamma>)
        (subspace_topology UNIV geotop_euclidean_topology (path_image \<gamma>))
        ({0..1}::real set)
        (subspace_topology UNIV geotop_euclidean_topology ({0..1}::real set))
        (inv_into ({0..1}::real set) \<gamma>)"
      using hg_top1 top1_continuous_map_on_cong[OF hg_eq_inv] by (by100 blast)
    show ?thesis
      unfolding top1_homeomorphism_on_def
      using htop_01 htop_img hbij h\<gamma>_top1 hinv_top1 by (by100 blast)
  qed
  have htop1_unit: "top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
      (subspace_topology UNIV geotop_euclidean_topology {t::real. 0 \<le> t \<and> t \<le> 1})
      (path_image \<gamma>)
      (subspace_topology UNIV geotop_euclidean_topology (path_image \<gamma>)) \<gamma>"
    using htop1_01 hunit_eq by (by100 simp)
  have hendpoints:
      "{pathstart \<gamma>, pathfinish \<gamma>} = {\<gamma> 0, \<gamma> 1}"
    unfolding pathstart_def pathfinish_def by (by100 simp)
  show ?thesis
    unfolding geotop_arc_endpoints_def
    using hgeotop_arc hcard hsub htop1_unit hendpoints by (by100 blast)
qed

lemma geotop_two_segment_join_arc_endpoints_prefix:
  fixes v\<^sub>0 v\<^sub>1 v\<^sub>2 :: "real^2"
  assumes hv\<^sub>0v\<^sub>2: "v\<^sub>0 \<noteq> v\<^sub>2"
  assumes hv\<^sub>1v\<^sub>2: "v\<^sub>1 \<noteq> v\<^sub>2"
  assumes hnot_col: "\<not> collinear {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
  shows "geotop_arc_endpoints
      (closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1) {v\<^sub>0, v\<^sub>1}"
  (**
    The two non-boundary edges of a nondegenerate triangle form the other
    broken arc from \<open>v\<^sub>0\<close> to \<open>v\<^sub>1\<close>. **)
proof -
  let ?\<gamma>\<^sub>0\<^sub>2 = "linepath v\<^sub>0 v\<^sub>2"
  let ?\<gamma>\<^sub>2\<^sub>1 = "linepath v\<^sub>2 v\<^sub>1"
  let ?\<gamma> = "?\<gamma>\<^sub>0\<^sub>2 +++ ?\<gamma>\<^sub>2\<^sub>1"
  have harc\<^sub>0\<^sub>2: "arc ?\<gamma>\<^sub>0\<^sub>2"
    by (rule arc_linepath[OF hv\<^sub>0v\<^sub>2])
  have hv\<^sub>2v\<^sub>1: "v\<^sub>2 \<noteq> v\<^sub>1"
    using hv\<^sub>1v\<^sub>2 by (by100 blast)
  have harc\<^sub>2\<^sub>1: "arc ?\<gamma>\<^sub>2\<^sub>1"
    by (rule arc_linepath[OF hv\<^sub>2v\<^sub>1])
  have hfinish_start: "pathfinish ?\<gamma>\<^sub>0\<^sub>2 = pathstart ?\<gamma>\<^sub>2\<^sub>1"
    by (by100 simp)
  have hinter: "path_image ?\<gamma>\<^sub>0\<^sub>2 \<inter> path_image ?\<gamma>\<^sub>2\<^sub>1 = {pathstart ?\<gamma>\<^sub>2\<^sub>1}"
  proof -
    have hseg_inter: "closed_segment v\<^sub>0 v\<^sub>2 \<inter> closed_segment v\<^sub>2 v\<^sub>1 = {v\<^sub>2}"
      by (rule Int_closed_segment[OF disjI2[OF hnot_col]])
    show ?thesis
      using hseg_inter by (by100 simp)
  qed
  have hinter_sub: "path_image ?\<gamma>\<^sub>0\<^sub>2 \<inter> path_image ?\<gamma>\<^sub>2\<^sub>1 \<subseteq> {pathstart ?\<gamma>\<^sub>2\<^sub>1}"
    using hinter by (by100 simp)
  have harc_join: "arc ?\<gamma>"
    by (rule arc_join[OF harc\<^sub>0\<^sub>2 harc\<^sub>2\<^sub>1 hfinish_start hinter_sub])
  have hpath_image_raw: "path_image ?\<gamma> = path_image ?\<gamma>\<^sub>0\<^sub>2 \<union> path_image ?\<gamma>\<^sub>2\<^sub>1"
    by (rule path_image_join[OF hfinish_start])
  have hpath_image:
      "path_image ?\<gamma> = closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1"
    using hpath_image_raw by (by100 simp)
  have hendpoints_raw:
      "geotop_arc_endpoints (path_image ?\<gamma>) {pathstart ?\<gamma>, pathfinish ?\<gamma>}"
    by (rule geotop_HOL_arc_imp_geotop_arc_endpoints_prefix[OF harc_join])
  have hendpoints_eq: "{pathstart ?\<gamma>, pathfinish ?\<gamma>} = {v\<^sub>0, v\<^sub>1}"
    by (by100 simp)
  show ?thesis
    using hendpoints_raw hpath_image hendpoints_eq by (by100 simp)
qed

lemma geotop_two_segment_join_broken_line_prefix:
  fixes v\<^sub>0 v\<^sub>1 v\<^sub>2 :: "real^2"
  assumes hv\<^sub>0v\<^sub>2: "v\<^sub>0 \<noteq> v\<^sub>2"
  assumes hv\<^sub>1v\<^sub>2: "v\<^sub>1 \<noteq> v\<^sub>2"
  assumes hnot_col: "\<not> collinear {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
  shows "geotop_is_broken_line
      (closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1)"
  (**
    Polyhedral side of the same two-edge triangle boundary arc. **)
proof -
  have hv\<^sub>2v\<^sub>1: "v\<^sub>2 \<noteq> v\<^sub>1"
    using hv\<^sub>1v\<^sub>2 by (by100 blast)
  have hB\<^sub>1: "geotop_is_broken_line (closed_segment v\<^sub>0 v\<^sub>2)"
    by (rule geotop_closed_segment_is_broken_line[OF hv\<^sub>0v\<^sub>2])
  have hB\<^sub>2: "geotop_is_broken_line (closed_segment v\<^sub>2 v\<^sub>1)"
    by (rule geotop_closed_segment_is_broken_line[OF hv\<^sub>2v\<^sub>1])
  have hR_end_1:
      "\<exists>\<gamma>\<^sub>1. arc \<gamma>\<^sub>1 \<and> path_image \<gamma>\<^sub>1 = closed_segment v\<^sub>0 v\<^sub>2
        \<and> pathfinish \<gamma>\<^sub>1 = v\<^sub>2"
  proof (rule exI[where x = "linepath v\<^sub>0 v\<^sub>2"])
    show "arc (linepath v\<^sub>0 v\<^sub>2) \<and> path_image (linepath v\<^sub>0 v\<^sub>2) =
        closed_segment v\<^sub>0 v\<^sub>2 \<and> pathfinish (linepath v\<^sub>0 v\<^sub>2) = v\<^sub>2"
      using arc_linepath[OF hv\<^sub>0v\<^sub>2] by (by100 simp)
  qed
  have hR_end_2:
      "\<exists>\<gamma>\<^sub>2. arc \<gamma>\<^sub>2 \<and> path_image \<gamma>\<^sub>2 = closed_segment v\<^sub>2 v\<^sub>1
        \<and> pathstart \<gamma>\<^sub>2 = v\<^sub>2"
  proof (rule exI[where x = "linepath v\<^sub>2 v\<^sub>1"])
    show "arc (linepath v\<^sub>2 v\<^sub>1) \<and> path_image (linepath v\<^sub>2 v\<^sub>1) =
        closed_segment v\<^sub>2 v\<^sub>1 \<and> pathstart (linepath v\<^sub>2 v\<^sub>1) = v\<^sub>2"
      using arc_linepath[OF hv\<^sub>2v\<^sub>1] by (by100 simp)
  qed
  have hdisj: "closed_segment v\<^sub>0 v\<^sub>2 \<inter> closed_segment v\<^sub>2 v\<^sub>1 = {v\<^sub>2}"
    by (rule Int_closed_segment[OF disjI2[OF hnot_col]])
  show ?thesis
    by (rule geotop_broken_lines_glue_disjoint_endpoints
        [OF hB\<^sub>1 hB\<^sub>2 hR_end_1 hR_end_2 hdisj])
qed

lemma geotop_triangle_edge_two_edge_arc_interiors_disjoint_prefix:
  fixes v\<^sub>0 v\<^sub>1 v\<^sub>2 :: "real^2"
  assumes hnot_col: "\<not> collinear {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
  shows "geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>1) {v\<^sub>0, v\<^sub>1} \<inter>
      geotop_arc_interior
        (closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1) {v\<^sub>0, v\<^sub>1} =
      {}"
  (**
    The open base edge is disjoint from the two open remaining edges of a
    nondegenerate triangle. **)
proof -
  have hset_left: "{v\<^sub>1, v\<^sub>0, v\<^sub>2} = {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
    by (by100 blast)
  have hnot_col_left: "\<not> collinear {v\<^sub>1, v\<^sub>0, v\<^sub>2}"
    using hnot_col hset_left by (by100 simp)
  have hleft_raw:
      "closed_segment v\<^sub>1 v\<^sub>0 \<inter> closed_segment v\<^sub>0 v\<^sub>2 = {v\<^sub>0}"
    by (rule Int_closed_segment[OF disjI2[OF hnot_col_left]])
  have hleft:
      "closed_segment v\<^sub>0 v\<^sub>1 \<inter> closed_segment v\<^sub>0 v\<^sub>2 = {v\<^sub>0}"
    using hleft_raw closed_segment_commute[of v\<^sub>1 v\<^sub>0] by (by100 simp)
  have hset_right: "{v\<^sub>0, v\<^sub>1, v\<^sub>2} = {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
    by (by100 blast)
  have hnot_col_right: "\<not> collinear {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
    using hnot_col hset_right by (by100 simp)
  have hright_raw:
      "closed_segment v\<^sub>0 v\<^sub>1 \<inter> closed_segment v\<^sub>1 v\<^sub>2 = {v\<^sub>1}"
    by (rule Int_closed_segment[OF disjI2[OF hnot_col_right]])
  have hright:
      "closed_segment v\<^sub>0 v\<^sub>1 \<inter> closed_segment v\<^sub>2 v\<^sub>1 = {v\<^sub>1}"
    using hright_raw closed_segment_commute[of v\<^sub>1 v\<^sub>2] by (by100 simp)
  have hmeet_subset:
      "closed_segment v\<^sub>0 v\<^sub>1 \<inter>
        (closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1) \<subseteq> {v\<^sub>0, v\<^sub>1}"
    using hleft hright by (by100 blast)
  show ?thesis
    unfolding geotop_arc_interior_def
    using hmeet_subset by (by100 blast)
qed

lemma geotop_2simplex_vertices_not_collinear_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hvertices: "geotop_simplex_vertices \<sigma> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
  assumes hv\<^sub>0v\<^sub>1: "v\<^sub>0 \<noteq> v\<^sub>1"
  assumes hv\<^sub>2_not: "v\<^sub>2 \<notin> {v\<^sub>0, v\<^sub>1}"
  shows "\<not> collinear {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
  (**
    Named-vertices form of the affine independence hidden in a 2-simplex:
    the three vertices are not collinear, in the edge-arc order used below. **)
proof -
  have hABC_ai: "\<not> affine_dependent {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
    by (rule geotop_general_position_imp_aff_indep[OF hvertices])
  have hv\<^sub>0v\<^sub>2: "v\<^sub>0 \<noteq> v\<^sub>2"
    using hv\<^sub>2_not by (by100 blast)
  have hv\<^sub>1v\<^sub>2: "v\<^sub>1 \<noteq> v\<^sub>2"
    using hv\<^sub>2_not by (by100 blast)
  have hnot_col_abc: "\<not> collinear {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
  proof
    assume hcol: "collinear {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
    have "v\<^sub>0 = v\<^sub>1 \<or> v\<^sub>0 = v\<^sub>2 \<or> v\<^sub>1 = v\<^sub>2
        \<or> affine_dependent {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
      using hcol collinear_3_eq_affine_dependent[of v\<^sub>0 v\<^sub>1 v\<^sub>2] by (by100 simp)
    thus False
      using hv\<^sub>0v\<^sub>1 hv\<^sub>0v\<^sub>2 hv\<^sub>1v\<^sub>2 hABC_ai by (by100 blast)
  qed
  have hset_col_order: "{v\<^sub>0, v\<^sub>2, v\<^sub>1} = {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
    by (by100 blast)
  show ?thesis
    using hnot_col_abc hset_col_order by (by100 simp)
qed

lemma geotop_triangle_frontier_is_polygon_from_vertices_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hvertices: "geotop_simplex_vertices \<sigma> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
  assumes hv\<^sub>0v\<^sub>1: "v\<^sub>0 \<noteq> v\<^sub>1"
  assumes hv\<^sub>2_not: "v\<^sub>2 \<notin> {v\<^sub>0, v\<^sub>1}"
  assumes hnot_col: "\<not> collinear {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
  shows "geotop_is_polygon (frontier \<sigma>)"
  (**
    The three edges of a named triangle are a pair of disjoint-interior arcs
    with common endpoints, hence form a GeoTop polygon. **)
proof -
  let ?B\<^sub>1 = "closed_segment v\<^sub>0 v\<^sub>1"
  let ?B\<^sub>2 = "closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1"
  let ?E = "{v\<^sub>0, v\<^sub>1}"
  have hv\<^sub>0v\<^sub>2: "v\<^sub>0 \<noteq> v\<^sub>2"
    using hv\<^sub>2_not by (by100 blast)
  have hv\<^sub>1v\<^sub>2: "v\<^sub>1 \<noteq> v\<^sub>2"
    using hv\<^sub>2_not by (by100 blast)
  have hB\<^sub>1: "geotop_is_broken_line ?B\<^sub>1"
    by (rule geotop_closed_segment_is_broken_line[OF hv\<^sub>0v\<^sub>1])
  have hB\<^sub>2: "geotop_is_broken_line ?B\<^sub>2"
    by (rule geotop_two_segment_join_broken_line_prefix
        [OF hv\<^sub>0v\<^sub>2 hv\<^sub>1v\<^sub>2 hnot_col])
  have hE\<^sub>1: "geotop_arc_endpoints ?B\<^sub>1 ?E"
    by (rule geotop_closed_segment_arc_endpoints_prefix[OF hv\<^sub>0v\<^sub>1])
  have hE\<^sub>2: "geotop_arc_endpoints ?B\<^sub>2 ?E"
    by (rule geotop_two_segment_join_arc_endpoints_prefix
        [OF hv\<^sub>0v\<^sub>2 hv\<^sub>1v\<^sub>2 hnot_col])
  have hdisj: "geotop_arc_interior ?B\<^sub>1 ?E \<inter> geotop_arc_interior ?B\<^sub>2 ?E = {}"
    by (rule geotop_triangle_edge_two_edge_arc_interiors_disjoint_prefix[OF hnot_col])
  have hpoly: "geotop_is_polygon (?B\<^sub>1 \<union> ?B\<^sub>2)"
    by (rule pair_of_arcs_is_polygon[OF hB\<^sub>1 hB\<^sub>2 hE\<^sub>1 hE\<^sub>2 hdisj])
  have hfront_hulls:
      "frontier \<sigma> =
        geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<union>
        geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<union>
        geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
    by (rule geotop_2simplex_vertices_frontier_eq_three_edge_hulls_prefix
        [OF hvertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
  have h01: "geotop_convex_hull {v\<^sub>0, v\<^sub>1} = closed_segment v\<^sub>0 v\<^sub>1"
    using segment_convex_hull[of v\<^sub>0 v\<^sub>1] geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>1}"]
    by (by100 simp)
  have h02: "geotop_convex_hull {v\<^sub>0, v\<^sub>2} = closed_segment v\<^sub>0 v\<^sub>2"
    using segment_convex_hull[of v\<^sub>0 v\<^sub>2] geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>2}"]
    by (by100 simp)
  have h12: "geotop_convex_hull {v\<^sub>1, v\<^sub>2} = closed_segment v\<^sub>2 v\<^sub>1"
    using segment_convex_hull[of v\<^sub>1 v\<^sub>2] geotop_convex_hull_eq_HOL[of "{v\<^sub>1, v\<^sub>2}"]
      closed_segment_commute[of v\<^sub>1 v\<^sub>2]
    by (by100 simp)
  have hfront: "frontier \<sigma> = ?B\<^sub>1 \<union> ?B\<^sub>2"
    using hfront_hulls h01 h02 h12 by (by100 blast)
  show ?thesis
    using hpoly hfront by (by100 simp)
qed

lemma geotop_2simplex_vertices_frontier_eq_base_union_two_segments_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hvertices: "geotop_simplex_vertices \<sigma> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
  assumes hv\<^sub>0v\<^sub>1: "v\<^sub>0 \<noteq> v\<^sub>1"
  assumes hv\<^sub>2_not: "v\<^sub>2 \<notin> {v\<^sub>0, v\<^sub>1}"
  shows "frontier \<sigma> =
      closed_segment v\<^sub>0 v\<^sub>1 \<union>
      (closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1)"
  (**
    Segment notation for the Figure 3.2 triangle boundary: the frontier of
    \<open>v\<^sub>0v\<^sub>1v\<^sub>2\<close> is the base edge together with the two remaining sides. **)
proof -
  have hfront_hulls:
    "frontier \<sigma> =
      geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<union>
      geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<union>
      geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
    by (rule geotop_2simplex_vertices_frontier_eq_three_edge_hulls_prefix
        [OF hvertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
  have h01: "geotop_convex_hull {v\<^sub>0, v\<^sub>1} = closed_segment v\<^sub>0 v\<^sub>1"
    using segment_convex_hull[of v\<^sub>0 v\<^sub>1] geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>1}"]
    by (by100 simp)
  have h02: "geotop_convex_hull {v\<^sub>0, v\<^sub>2} = closed_segment v\<^sub>0 v\<^sub>2"
    using segment_convex_hull[of v\<^sub>0 v\<^sub>2] geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>2}"]
    by (by100 simp)
  have h12: "geotop_convex_hull {v\<^sub>1, v\<^sub>2} = closed_segment v\<^sub>2 v\<^sub>1"
    using segment_convex_hull[of v\<^sub>1 v\<^sub>2] geotop_convex_hull_eq_HOL[of "{v\<^sub>1, v\<^sub>2}"]
      closed_segment_commute[of v\<^sub>1 v\<^sub>2]
    by (by100 simp)
  show ?thesis
    using hfront_hulls h01 h02 h12 by (by100 blast)
qed

lemma geotop_2simplex_frontier_is_polygon_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  shows "geotop_is_polygon (frontier \<sigma>)"
  (**
    The frontier of a 2-simplex is a polygonal 1-sphere: choose the three
    vertices and read the frontier as the closed three-edge path. **)
proof -
  obtain V m where hV_fin: "finite V"
    and hV_card: "card V = 2 + 1"
    and h2_le_m: "2 \<le> m"
    and hgp: "geotop_general_position V m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>2 unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    unfolding geotop_simplex_vertices_def
    using hV_fin hV_card h2_le_m hgp h\<sigma>_eq by (by100 blast)
  have hV_card3: "card V = 3"
    using hV_card by (by100 simp)
  obtain v\<^sub>0 v\<^sub>1 v\<^sub>2 where hV_eq: "V = {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
    and hv\<^sub>0v\<^sub>1: "v\<^sub>0 \<noteq> v\<^sub>1"
    and hv\<^sub>1v\<^sub>2: "v\<^sub>1 \<noteq> v\<^sub>2"
    and hv\<^sub>0v\<^sub>2: "v\<^sub>0 \<noteq> v\<^sub>2"
    using iffD1[OF card_3_iff hV_card3] by (by100 blast)
  have hvertices: "geotop_simplex_vertices \<sigma> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
    using h\<sigma>V hV_eq by (by100 simp)
  have hv\<^sub>2_not: "v\<^sub>2 \<notin> {v\<^sub>0, v\<^sub>1}"
    using hv\<^sub>1v\<^sub>2 hv\<^sub>0v\<^sub>2 by (by100 blast)
  have hnot_col: "\<not> collinear {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
    by (rule geotop_2simplex_vertices_not_collinear_prefix
        [OF hvertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
  show ?thesis
    by (rule geotop_triangle_frontier_is_polygon_from_vertices_prefix
        [OF hvertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not hnot_col])
qed

lemma geotop_2simplex_inside_frontier_eq_HOL_interior_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  shows "inside (frontier \<sigma>) = interior \<sigma>"
  (**
    HOL convex-geometry form of the triangle interior: the inside of the
    frontier of a bounded convex triangle is its ordinary interior. **)
proof -
  have hbd: "bounded \<sigma>"
    by (rule geotop_simplex_dim_bounded_prefix[OF h\<sigma>2])
  have hconv: "convex \<sigma>"
    by (rule geotop_simplex_dim_convex_HOL_prefix[OF h\<sigma>2])
  show ?thesis
    by (rule inside_frontier_eq_interior[OF hbd hconv])
qed

lemma geotop_2simplex_inside_frontier_HOL_component_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  shows "inside (frontier \<sigma>) \<in> components (UNIV - frontier \<sigma>) \<and>
      bounded (inside (frontier \<sigma>))"
  (**
    Component form needed to identify the polygon-interior convention with
    HOL's bounded inside component. **)
proof -
  have hinside_eq: "inside (frontier \<sigma>) = interior \<sigma>"
    by (rule geotop_2simplex_inside_frontier_eq_HOL_interior_prefix[OF h\<sigma>2])
  have hsimplex: "geotop_is_simplex \<sigma>"
    by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>2])
  have hrel_ne: "rel_interior \<sigma> \<noteq> {}"
    by (rule geotop_simplex_rel_interior_nonempty[OF hsimplex])
  have hint_rel: "interior \<sigma> = rel_interior \<sigma>"
    by (rule geotop_2simplex_HOL_interior_eq_rel_interior_prefix[OF h\<sigma>2])
  have hinside_ne: "inside (frontier \<sigma>) \<noteq> {}"
    using hinside_eq hint_rel hrel_ne by (by100 simp)
  have hconv: "convex \<sigma>"
    by (rule geotop_simplex_dim_convex_HOL_prefix[OF h\<sigma>2])
  have hconv_int: "convex (interior \<sigma>)"
    by (rule convex_interior[OF hconv])
  have hinside_conn: "connected (inside (frontier \<sigma>))"
    using hinside_eq hconv_int convex_connected by (by100 simp)
  have hinside_comp: "inside (frontier \<sigma>) \<in> components (- frontier \<sigma>)"
    using inside_in_components[of "frontier \<sigma>"] hinside_conn hinside_ne by (by100 simp)
  have hcomponents_eq: "components (- frontier \<sigma>) = components (UNIV - frontier \<sigma>)"
    by (simp only: Compl_eq_Diff_UNIV)
  have hinside_comp_UNIV: "inside (frontier \<sigma>) \<in> components (UNIV - frontier \<sigma>)"
    using hinside_comp hcomponents_eq by (by100 simp)
  have hbd\<sigma>: "bounded \<sigma>"
    by (rule geotop_simplex_dim_bounded_prefix[OF h\<sigma>2])
  have hbd_int: "bounded (interior \<sigma>)"
    using hbd\<sigma> interior_subset bounded_subset by (by100 blast)
  have hbd_inside: "bounded (inside (frontier \<sigma>))"
    using hinside_eq hbd_int by (by100 simp)
  show ?thesis
    using hinside_comp_UNIV hbd_inside by (by100 blast)
qed

lemma geotop_2simplex_frontier_polygon_interior_eq_HOL_interior_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  shows "geotop_polygon_interior (frontier \<sigma>) = interior \<sigma>"
  (**
    Triangle case of the polygon-interior convention: the bounded component of
    the complement of the frontier of a 2-simplex is the ordinary open triangle.
    This is the explicit local form of the fact used when Moise says the
    exactly-two-triangle case is clear. **)
proof -
  have hpoly: "geotop_is_polygon (frontier \<sigma>)"
    by (rule geotop_2simplex_frontier_is_polygon_prefix[OF h\<sigma>2])
  have hinside_component:
      "inside (frontier \<sigma>) \<in> components (UNIV - frontier \<sigma>) \<and>
        bounded (inside (frontier \<sigma>))"
    by (rule geotop_2simplex_inside_frontier_HOL_component_prefix[OF h\<sigma>2])
  have hinside_poly:
      "inside (frontier \<sigma>) = geotop_polygon_interior (frontier \<sigma>)"
    by (rule polygon_interior_unique[OF hpoly hinside_component])
  have hinside_int: "inside (frontier \<sigma>) = interior \<sigma>"
    by (rule geotop_2simplex_inside_frontier_eq_HOL_interior_prefix[OF h\<sigma>2])
  show ?thesis
    using hinside_poly hinside_int by (by100 simp)
qed

lemma geotop_polygon_boundary_contact_triangle_interior_component_prefix:
  fixes J \<sigma> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes hfront_sub: "frontier \<sigma> \<subseteq> J"
  assumes hcontact: "\<sigma> \<inter> J = frontier \<sigma>"
  shows "interior \<sigma> \<in> components (UNIV - J) \<and> bounded (interior \<sigma>)"
  (**
    If a polygon boundary contains the whole triangle frontier and does not
    enter the open triangle, then the ordinary open triangle remains a full
    bounded complementary component of that boundary. **)
proof -
  have hinside_data:
      "inside (frontier \<sigma>) \<in> components (UNIV - frontier \<sigma>) \<and>
        bounded (inside (frontier \<sigma>))"
    by (rule geotop_2simplex_inside_frontier_HOL_component_prefix[OF h\<sigma>2])
  have hinside_eq: "inside (frontier \<sigma>) = interior \<sigma>"
    by (rule geotop_2simplex_inside_frontier_eq_HOL_interior_prefix[OF h\<sigma>2])
  have hI_comp_front: "interior \<sigma> \<in> components (UNIV - frontier \<sigma>)"
    using hinside_data hinside_eq by (by100 simp)
  have hI_bounded: "bounded (interior \<sigma>)"
    using hinside_data hinside_eq by (by100 simp)
  have hI_ne: "interior \<sigma> \<noteq> {}"
    using hI_comp_front in_components_nonempty by (by100 blast)
  have hI_conn: "connected (interior \<sigma>)"
    using hI_comp_front in_components_connected by (by100 blast)
  have hI_sub_front_compl: "interior \<sigma> \<subseteq> UNIV - frontier \<sigma>"
    using hI_comp_front in_components_subset by (by100 blast)
  have hI_sub_\<sigma>: "interior \<sigma> \<subseteq> \<sigma>"
    by (rule interior_subset)
  have hI_Int_J_empty: "interior \<sigma> \<inter> J = {}"
  proof -
    have "interior \<sigma> \<inter> J \<subseteq> (UNIV - frontier \<sigma>) \<inter> frontier \<sigma>"
      using hI_sub_front_compl hI_sub_\<sigma> hcontact by (by100 blast)
    moreover have "(UNIV - frontier \<sigma>) \<inter> frontier \<sigma> = {}"
      by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  have hI_sub_J_compl: "interior \<sigma> \<subseteq> UNIV - J"
    using hI_Int_J_empty by (by100 blast)
  have hI_comp_J: "interior \<sigma> \<in> components (UNIV - J)"
    unfolding in_components_maximal
  proof (intro conjI)
    show "interior \<sigma> \<noteq> {}"
      by (rule hI_ne)
    show "interior \<sigma> \<subseteq> UNIV - J"
      by (rule hI_sub_J_compl)
    show "connected (interior \<sigma>)"
      by (rule hI_conn)
    show "\<forall>D. D \<noteq> {} \<and> interior \<sigma> \<subseteq> D \<and> D \<subseteq> UNIV - J \<and>
        connected D \<longrightarrow> D = interior \<sigma>"
    proof (intro allI impI)
      fix D
      assume hD:
        "D \<noteq> {} \<and> interior \<sigma> \<subseteq> D \<and> D \<subseteq> UNIV - J \<and> connected D"
      have hI_sub_D: "interior \<sigma> \<subseteq> D"
        using hD by (by100 blast)
      have hD_sub_J: "D \<subseteq> UNIV - J"
        using hD by (by100 blast)
      have hD_conn: "connected D"
        using hD by (by100 blast)
      have hD_sub_front: "D \<subseteq> UNIV - frontier \<sigma>"
        using hD_sub_J hfront_sub by (by100 blast)
      have hmeet: "interior \<sigma> \<inter> D \<noteq> {}"
        using hI_ne hI_sub_D by (by100 blast)
      have hD_sub_I: "D \<subseteq> interior \<sigma>"
        by (rule components_maximal[OF hI_comp_front hD_conn hD_sub_front hmeet])
      show "D = interior \<sigma>"
        using hI_sub_D hD_sub_I by (by100 blast)
    qed
  qed
  show ?thesis
    using hI_comp_J hI_bounded by (by100 blast)
qed

lemma geotop_polygon_boundary_contact_triangle_frontier_eq_prefix:
  fixes J \<sigma> :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes hfront_sub: "frontier \<sigma> \<subseteq> J"
  assumes hcontact: "\<sigma> \<inter> J = frontier \<sigma>"
  shows "J = frontier \<sigma>"
  (**
    Simple-closed-boundary part of the two-triangle base case: a polygonal
    1-sphere that contains the whole frontier of a triangle and has no further
    contact with the closed triangle cannot have extra boundary outside the
    triangle. **)
proof -
  have hfront_poly: "geotop_is_polygon (frontier \<sigma>)"
    by (rule geotop_2simplex_frontier_is_polygon_prefix[OF h\<sigma>2])
  have hI_comp:
      "interior \<sigma> \<in> components (UNIV - J) \<and> bounded (interior \<sigma>)"
    by (rule geotop_polygon_boundary_contact_triangle_interior_component_prefix
        [OF h\<sigma>2 hfront_sub hcontact])
  have hI_eq_J: "interior \<sigma> = geotop_polygon_interior J"
    by (rule polygon_interior_unique[OF hJ hI_comp])
  have hfront_I: "geotop_polygon_interior (frontier \<sigma>) = interior \<sigma>"
    by (rule geotop_2simplex_frontier_polygon_interior_eq_HOL_interior_prefix
        [OF h\<sigma>2])
  have hI_same: "geotop_polygon_interior J =
      geotop_polygon_interior (frontier \<sigma>)"
    using hI_eq_J hfront_I by (by100 simp)
  show ?thesis
    by (rule polygon_interior_injective[OF hJ hfront_poly hI_same])
qed

lemma geotop_polygon_boundary_2simplex_frontier_forces_same_interior_prefix:
  fixes J \<sigma> :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes hfront_sub: "frontier \<sigma> \<subseteq> J"
  assumes hcontact: "\<sigma> \<inter> J = frontier \<sigma>"
  shows "geotop_polygon_interior J = interior \<sigma>"
  (**
    Topological content of Moise's \"clear\" two-triangle base case: if a
    polygonal simple closed curve contains the whole frontier of a 2-simplex
    and its contact with the closed triangle is exactly that frontier, then the
    bounded polygon interior is the ordinary interior of the triangle. **)
proof -
  have hJ_eq: "J = frontier \<sigma>"
    by (rule geotop_polygon_boundary_contact_triangle_frontier_eq_prefix
        [OF hJ h\<sigma>2 hfront_sub hcontact])
  have hfront_int: "geotop_polygon_interior (frontier \<sigma>) = interior \<sigma>"
    by (rule geotop_2simplex_frontier_polygon_interior_eq_HOL_interior_prefix
        [OF h\<sigma>2])
  show ?thesis
    using hJ_eq hfront_int by (by100 simp)
qed

lemma geotop_polygon_disk_all_triangle_boundary_closure_subset_prefix:
  fixes J \<sigma> :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes hfront_sub: "frontier \<sigma> \<subseteq> J"
  assumes hcontact: "\<sigma> \<inter> J = frontier \<sigma>"
  shows "closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)
      \<subseteq> \<sigma>"
  (**
    Disk-carrier consequence used in the two-triangle base case: once all
    three edges of \<open>\<sigma>\<close> form the polygon boundary contact, the closed polygonal
    disk lies in \<open>\<sigma>\<close>. **)
proof -
  have hI_eq: "geotop_polygon_interior J = interior \<sigma>"
    by (rule geotop_polygon_boundary_2simplex_frontier_forces_same_interior_prefix
        [OF hJ h\<sigma>2 hfront_sub hcontact])
  have hclos_on: "closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)
      = closure (geotop_polygon_interior J)"
    by (rule closure_on_geotop_UNIV_eq_closure)
  have hclosure_int: "closure (interior \<sigma>) = \<sigma>"
    by (rule geotop_2simplex_closure_HOL_interior_prefix[OF h\<sigma>2])
  show ?thesis
    using hI_eq hclos_on hclosure_int by (by100 simp)
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

lemma geotop_2simplex_polygon_boundary_inter_subset_three_edge_hulls_prefix:
  fixes J \<sigma> :: "(real^2) set" and K :: "(real^2) set set"
    and v\<^sub>0 v\<^sub>1 v\<^sub>2 :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hvertices: "geotop_simplex_vertices \<sigma> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
  assumes hv\<^sub>0v\<^sub>1: "v\<^sub>0 \<noteq> v\<^sub>1"
  assumes hv\<^sub>2_not: "v\<^sub>2 \<notin> {v\<^sub>0, v\<^sub>1}"
  shows "\<sigma> \<inter> J \<subseteq>
      geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<union>
      geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<union>
      geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
  (**
    Named-edge form of the boundary-contact frontier fact: once a 2-simplex is
    written with vertices \<open>v\<^sub>0,v\<^sub>1,v\<^sub>2\<close>, every point where it meets the polygon
    boundary lies on one of the three displayed edge hulls. **)
proof -
  have hfrontier_named:
    "frontier \<sigma> =
      geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<union>
      geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<union>
      geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
    by (rule geotop_2simplex_vertices_frontier_eq_three_edge_hulls_prefix
        [OF hvertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
  have hcontact_frontier: "\<sigma> \<inter> J \<subseteq> frontier \<sigma>"
  proof
    fix x
    assume hx: "x \<in> \<sigma> \<inter> J"
    have hx\<sigma>: "x \<in> \<sigma>"
      using hx by (by100 simp)
    have hxJ: "x \<in> J"
      using hx by (by100 simp)
    show "x \<in> frontier \<sigma>"
      by (rule geotop_polygon_boundary_point_in_2simplex_frontier_prefix
          [OF hJ h\<sigma>K h\<sigma>2 hK_poly hx\<sigma> hxJ])
  qed
  show ?thesis
    using hcontact_frontier hfrontier_named by (by100 simp)
qed

lemma geotop_2simplex_three_selected_edge_faces_frontier_subset_prefix:
  fixes K :: "(real^2) set set" and J \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hcard: "card {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J} = 3"
  shows "frontier \<sigma> \<subseteq> J"
  (**
    If all three edge faces of a triangle have been selected as polygon-boundary
    edges, then the whole triangle frontier lies on the polygon boundary. **)
proof
  fix x
  assume hx: "x \<in> frontier \<sigma>"
  let ?A = "{e. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
  let ?E = "{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J}"
  have hfront: "frontier \<sigma> = \<Union>?A"
    by (rule geotop_2simplex_frontier_eq_edge_faces_prefix[OF h\<sigma>])
  have hA_eq_E: "?A = ?E"
    by (rule geotop_2simplex_three_selected_edge_faces_all_prefix[OF h\<sigma> hcard])
  have hxU: "x \<in> \<Union>?E"
    using hx hfront hA_eq_E by (by100 simp)
  obtain e where heE: "e \<in> ?E" and hxe: "x \<in> e"
    using hxU by (by100 blast)
  have heJ: "e \<subseteq> J"
    using heE by (by100 simp)
  show "x \<in> J"
    using hxe heJ by (by100 blast)
qed

lemma geotop_2simplex_three_selected_edge_faces_boundary_contact_eq_frontier_prefix:
  fixes K :: "(real^2) set set" and J \<sigma> :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hcard: "card {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J} = 3"
  shows "\<sigma> \<inter> J = frontier \<sigma>"
  (**
    Disk-carrier form of the preceding bridge: if all three edge faces are
    selected, the triangle's contact with the polygon boundary is exactly its
    frontier. **)
proof
  show "\<sigma> \<inter> J \<subseteq> frontier \<sigma>"
  proof
    fix x
    assume hx: "x \<in> \<sigma> \<inter> J"
    have hx\<sigma>: "x \<in> \<sigma>"
      using hx by (by100 simp)
    have hxJ: "x \<in> J"
      using hx by (by100 simp)
    show "x \<in> frontier \<sigma>"
      by (rule geotop_polygon_boundary_point_in_2simplex_frontier_prefix
          [OF hJ h\<sigma>K h\<sigma> hK_poly hx\<sigma> hxJ])
  qed
  show "frontier \<sigma> \<subseteq> \<sigma> \<inter> J"
  proof
    fix x
    assume hx: "x \<in> frontier \<sigma>"
    have hfrontJ: "frontier \<sigma> \<subseteq> J"
      by (rule geotop_2simplex_three_selected_edge_faces_frontier_subset_prefix
          [OF h\<sigma> hcard])
    have hxJ: "x \<in> J"
      using hfrontJ hx by (by100 blast)
    have h\<sigma>closed: "closed \<sigma>"
      by (rule geotop_simplex_dim_closed[OF h\<sigma>])
    have hx_closure: "x \<in> closure \<sigma>"
      using hx unfolding Elementary_Topology.frontier_def by (by100 simp)
    have hx\<sigma>: "x \<in> \<sigma>"
      using h\<sigma>closed hx_closure by (by100 simp)
    show "x \<in> \<sigma> \<inter> J"
      using hx\<sigma> hxJ by (by100 simp)
  qed
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

lemma geotop_edge_closure_rel_interior_prefix:
  fixes e :: "(real^2) set"
  assumes hedge: "geotop_is_edge e"
  shows "closure (rel_interior e) = e"
  (**
    An edge is the closure of its relative interior. **)
proof -
  have he_dim: "geotop_simplex_dim e 1"
    using hedge unfolding geotop_is_edge_def by (by100 simp)
  have he_simplex: "geotop_is_simplex e"
    by (rule geotop_simplex_dim_imp_is_simplex[OF he_dim])
  show ?thesis
    by (rule geotop_simplex_closure_rel_interior[OF he_simplex])
qed

lemma geotop_local_frontier_transfer_prefix:
  fixes M S :: "(real^2) set"
  assumes hs: "0 < s"
  assumes hlocal: "ball p s \<inter> M = ball p s \<inter> S"
  assumes hpfront: "p \<in> frontier S"
  assumes hpM: "p \<in> M"
  shows "p \<in> frontier M"
  (**
    If two sets agree in a positive ball around a point, frontier membership
    transfers locally from one set to the other. **)
proof -
  have hp_closure_M: "p \<in> closure M"
    using hpM closure_subset by (by100 blast)
  have hp_not_int_M: "p \<notin> interior M"
  proof
    assume hp_int_M: "p \<in> interior M"
    obtain r where hr: "0 < r" and hballM: "ball p r \<subseteq> M"
      using hp_int_M unfolding mem_interior by (by100 blast)
    define t where "t = min r s"
    have ht: "0 < t"
      using hr hs unfolding t_def by (by100 simp)
    have ht_le_r: "t \<le> r"
      unfolding t_def by (by100 simp)
    have ht_le_s: "t \<le> s"
      unfolding t_def by (by100 simp)
    have hballS: "ball p t \<subseteq> S"
    proof
      fix x
      assume hx: "x \<in> ball p t"
      have hxM: "x \<in> M"
        using hballM ht_le_r hx by (by100 auto)
      have hxs: "x \<in> ball p s"
        using ht_le_s hx by (by100 auto)
      have "x \<in> ball p s \<inter> M"
        using hxs hxM by (by100 blast)
      hence "x \<in> ball p s \<inter> S"
        using hlocal by (by100 simp)
      thus "x \<in> S"
        by (by100 blast)
    qed
    have hp_int_S: "p \<in> interior S"
      unfolding mem_interior using ht hballS by (by100 blast)
    have hp_not_int_S: "p \<notin> interior S"
      using hpfront unfolding Elementary_Topology.frontier_def by (by100 simp)
    show False
      using hp_int_S hp_not_int_S by (by100 blast)
  qed
  show ?thesis
    unfolding Elementary_Topology.frontier_def
    using hp_closure_M hp_not_int_M by (by100 simp)
qed

lemma geotop_unique_incident_edge_rel_interior_subset_polyhedron_frontier_prefix:
  fixes K :: "(real^2) set set" and e \<sigma> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>face: "geotop_is_face e \<sigma>"
  assumes hfaces: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>}"
  shows "rel_interior e \<subseteq> frontier (geotop_polyhedron K)"
  (**
    One-sided edge-star fact: if an edge has a unique incident 2-simplex, then
    every interior point of the edge lies on the frontier of the complex
    carrier. **)
proof
  fix p
  assume hp: "p \<in> rel_interior e"
  let ?M = "geotop_polyhedron K"
  have hp_e: "p \<in> e"
    using hp rel_interior_subset by (by100 blast)
  obtain r F where hr: "0 < r"
    and hFfin: "finite F"
    and hFsub: "F \<subseteq> K"
    and heF: "e \<in> F"
    and hcover: "ball p r \<inter> ?M \<subseteq> \<Union>F"
    using geotop_complex_edge_point_finite_local_cover_prefix[OF hK heK hp_e]
    by (by100 blast)
  have hp_unionF: "p \<in> \<Union>F"
    using heF hp_e by (by100 blast)
  obtain \<delta> where h\<delta>: "0 < \<delta>"
    and hisolate: "ball p \<delta> \<inter> \<Union>F \<subseteq> \<Union>{\<tau>\<in>F. p \<in> \<tau>}"
    using geotop_complex_finite_subcomplex_local_point_carriers_prefix
      [OF hK hFfin hFsub hp_unionF]
    by (by100 blast)
  define s where "s = min r \<delta>"
  have hs: "0 < s"
    using hr h\<delta> unfolding s_def by (by100 simp)
  have hcover_s: "ball p s \<inter> ?M \<subseteq> \<Union>F"
  proof -
    have hball_sub: "ball p s \<subseteq> ball p r"
      unfolding s_def by (by100 auto)
    have "ball p s \<inter> ?M \<subseteq> ball p r \<inter> ?M"
      using hball_sub by (by100 blast)
    thus ?thesis
      using hcover by (by100 blast)
  qed
  have hpoint_carriers_s: "ball p s \<inter> ?M \<subseteq> \<Union>{\<tau>\<in>F. p \<in> \<tau>}"
  proof
    fix x
    assume hx: "x \<in> ball p s \<inter> ?M"
    have hxF: "x \<in> \<Union>F"
      using hcover_s hx by (by100 blast)
    have hball_sub: "ball p s \<subseteq> ball p \<delta>"
      unfolding s_def by (by100 auto)
    have hx\<delta>: "x \<in> ball p \<delta>"
      using hx hball_sub by (by100 blast)
    have "x \<in> ball p \<delta> \<inter> \<Union>F"
      using hxF hx\<delta> by (by100 blast)
    thus "x \<in> \<Union>{\<tau>\<in>F. p \<in> \<tau>}"
      using hisolate by (by100 blast)
  qed
  have hpoint_carriers_subset_\<sigma>: "\<Union>{\<tau>\<in>F. p \<in> \<tau>} \<subseteq> \<sigma>"
    by (rule geotop_complex_unique_edge_face_point_carrier_union_subset_unique_face_prefix
        [OF hK heK hedge hp h\<sigma>K h\<sigma>2 h\<sigma>face hfaces hFsub])
  have hlocal_poly_\<sigma>: "ball p s \<inter> ?M \<subseteq> \<sigma>"
    using hpoint_carriers_s hpoint_carriers_subset_\<sigma> by (by100 blast)
  have h\<sigma>subM: "\<sigma> \<subseteq> ?M"
    using h\<sigma>K unfolding geotop_polyhedron_def by (by100 blast)
  have hlocal_eq: "ball p s \<inter> ?M = ball p s \<inter> \<sigma>"
  proof
    show "ball p s \<inter> ?M \<subseteq> ball p s \<inter> \<sigma>"
      using hlocal_poly_\<sigma> by (by100 blast)
  next
    show "ball p s \<inter> \<sigma> \<subseteq> ball p s \<inter> ?M"
      using h\<sigma>subM by (by100 blast)
  qed
  have hpfront_\<sigma>: "p \<in> frontier \<sigma>"
  proof -
    have hfront: "frontier \<sigma> = \<Union>{d. geotop_is_edge d \<and> geotop_is_face d \<sigma>}"
      by (rule geotop_2simplex_frontier_eq_edge_faces_prefix[OF h\<sigma>2])
    have he_in: "e \<in> {d. geotop_is_edge d \<and> geotop_is_face d \<sigma>}"
      using hedge h\<sigma>face by (by100 simp)
    show ?thesis
      using hfront he_in hp_e by (by100 blast)
  qed
  have hpM: "p \<in> ?M"
    using heK hp_e unfolding geotop_polyhedron_def by (by100 blast)
  show "p \<in> frontier ?M"
    by (rule geotop_local_frontier_transfer_prefix[OF hs hlocal_eq hpfront_\<sigma> hpM])
qed

lemma geotop_unique_incident_edge_subset_polygon_boundary_prefix:
  fixes J e \<sigma> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>face: "geotop_is_face e \<sigma>"
  assumes hfaces: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>}"
  shows "e \<subseteq> J"
  (**
    Polygon-disk form of the one-sided edge-star fact: a unique incident
    triangle edge is a boundary edge of the disk. **)
proof -
  have hrel_front: "rel_interior e \<subseteq> frontier (geotop_polyhedron K)"
    by (rule geotop_unique_incident_edge_rel_interior_subset_polyhedron_frontier_prefix
        [OF hK heK hedge h\<sigma>K h\<sigma>2 h\<sigma>face hfaces])
  have hfront_eq: "frontier (geotop_polyhedron K) = J"
    by (rule geotop_polygon_disk_polyhedron_frontier_prefix[OF hJ hK_poly])
  have hclosed_front: "closed (frontier (geotop_polyhedron K))"
    by (rule frontier_closed)
  have hclosure_sub_front:
      "closure (rel_interior e) \<subseteq> frontier (geotop_polyhedron K)"
    by (rule closure_minimal[OF hrel_front hclosed_front])
  have hclosure_e: "closure (rel_interior e) = e"
    by (rule geotop_edge_closure_rel_interior_prefix[OF hedge])
  show ?thesis
    using hclosure_sub_front hclosure_e hfront_eq by (by100 simp)
qed

lemma geotop_two_triangle_nonshared_edge_subset_boundary_prefix:
  fixes J e \<sigma> \<tau> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hT_eq: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2} = {\<sigma>, \<tau>}"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes hnot_tau: "\<not> geotop_is_face e \<tau>"
  shows "e \<subseteq> J"
  (**
    In the exactly two-triangle base case, an edge of one triangle not shared
    by the other triangle has a unique incident 2-simplex, hence is a polygon
    boundary edge. **)
proof -
  have hface_set: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>}"
  proof
    show "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} \<subseteq> {\<sigma>}"
    proof
      fix \<rho>
      assume h\<rho>: "\<rho> \<in> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
      have h\<rho>2set: "\<rho> \<in> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2}"
        using h\<rho> by (by100 simp)
      have h\<rho>case: "\<rho> = \<sigma> \<or> \<rho> = \<tau>"
        using hT_eq h\<rho>2set by (by100 simp)
      have h\<rho>face: "geotop_is_face e \<rho>"
        using h\<rho> by (by100 simp)
      have "\<rho> = \<sigma>"
        using h\<rho>case h\<rho>face hnot_tau by (by100 blast)
      thus "\<rho> \<in> {\<sigma>}"
        by (by100 simp)
    qed
  next
    show "{\<sigma>} \<subseteq> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
      using h\<sigma>K h\<sigma>2 he\<sigma> by (by100 simp)
  qed
  have hunique:
    "\<exists>!\<rho>. \<rho> \<in> K \<and> geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>"
  proof (rule ex1I[where a=\<sigma>])
    show "\<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
      using h\<sigma>K h\<sigma>2 he\<sigma> by (by100 blast)
  next
    fix \<rho>
    assume h\<rho>: "\<rho> \<in> K \<and> geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>"
    have "\<rho> \<in> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
      using h\<rho> by (by100 simp)
    thus "\<rho> = \<sigma>"
      using hface_set by (by100 simp)
  qed
  show ?thesis
    by (rule geotop_unique_incident_edge_subset_polygon_boundary_prefix
        [OF hJ hK hK_poly heK hedge h\<sigma>K h\<sigma>2 he\<sigma> hface_set])
qed


lemma geotop_simplex_vertex_notin_affine_hull_of_other_vertices_prefix:
  fixes \<sigma> :: "(real^2) set" and V W :: "(real^2) set"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hvV: "v \<in> V"
  assumes hW_sub: "W \<subseteq> V - {v}"
  shows "v \<notin> affine hull W"
proof -
  have hV_ai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF h\<sigma>V])
  have hW_sub_V: "W \<subseteq> V"
    using hW_sub by (by100 blast)
  have hW_ai: "\<not> affine_dependent W"
    by (rule affine_independent_subset[OF hV_ai hW_sub_V])
  have hinsert_sub: "insert v W \<subseteq> V"
    using hvV hW_sub by (by100 blast)
  have hinsert_ai: "\<not> affine_dependent (insert v W)"
    by (rule affine_independent_subset[OF hV_ai hinsert_sub])
  have hv_not_W: "v \<notin> W"
    using hW_sub by (by100 blast)
  show ?thesis
  proof
    assume hv_aff: "v \<in> affine hull W"
    have "affine_dependent (insert v W)"
      using affine_dependent_choose[OF hW_ai, of v] hv_not_W hv_aff
      by (by100 simp)
    thus False
      using hinsert_ai by (by100 blast)
  qed
qed


lemma geotop_2simplex_vertices_three_eq_prefix:
  fixes \<sigma> V :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hv: "v \<in> V"
  assumes hw: "w \<in> V"
  assumes hu: "u \<in> V"
  assumes hvw: "v \<noteq> w"
  assumes hvu: "v \<noteq> u"
  assumes hwu: "w \<noteq> u"
  shows "V = {v, w, u}"
proof -
  obtain V2 m where hV2_fin: "finite V2"
    and hV2_card: "card V2 = 2 + 1"
    and h2_le_m: "2 \<le> m"
    and hgp_V2: "geotop_general_position V2 m"
    and h\<sigma>_eq_V2: "\<sigma> = geotop_convex_hull V2"
    using h\<sigma>2 unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V2: "geotop_simplex_vertices \<sigma> V2"
    unfolding geotop_simplex_vertices_def
    using hV2_fin hV2_card h2_le_m hgp_V2 h\<sigma>_eq_V2 by (by100 blast)
  have hV_eq: "V = V2"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>V2])
  have hV_card: "card V = 3"
    using hV_eq hV2_card by (by100 simp)
  have hV_fin: "finite V"
    using hV_eq hV2_fin by (by100 simp)
  have hthree_sub: "{v, w, u} \<subseteq> V"
    using hv hw hu by (by100 blast)
  have hthree_card: "card {v, w, u} = 3"
    using hvw hvu hwu by (by100 simp)
  have hthree_eq: "{v, w, u} = V"
  proof (rule card_seteq[OF hV_fin hthree_sub])
    show "card V \<le> card {v, w, u}"
      using hthree_card hV_card by (by100 simp)
  qed
  show ?thesis
    using hthree_eq by (by100 simp)
qed


lemma geotop_2simplex_opposite_vertex_notin_edge_affine_hull_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hc: "c \<notin> {a, b}"
  shows "c \<notin> affine hull {a, b}"
  (**
    In the shared-edge picture, the vertex opposite the edge is not on the
    affine line of that edge. **)
proof -
  have hcV: "c \<in> {a, b, c}"
    by (by100 simp)
  have hsub: "{a, b} \<subseteq> {a, b, c} - {c}"
    using hc by (by100 blast)
  show ?thesis
    by (rule geotop_simplex_vertex_notin_affine_hull_of_other_vertices_prefix
        [OF h\<sigma>V hcV hsub])
qed

lemma geotop_two_2simplex_shared_edge_vertices_obtain_prefix:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  assumes hedge: "geotop_is_edge e"
  obtains a b c d where
    "a \<noteq> b"
    "c \<notin> {a, b}"
    "d \<notin> {a, b}"
    "c \<noteq> d"
    "e = geotop_convex_hull {a, b}"
    "geotop_simplex_vertices \<sigma> {a, b, c}"
    "geotop_simplex_vertices \<tau> {a, b, d}"
  (**
    Shared-edge vertex form for the two-triangle local model: the common edge
    has two vertices \<open>a,b\<close>, and the two distinct 2-simplexes have distinct
    third vertices \<open>c\<close> and \<open>d\<close>. **)
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and he_eq_W: "e = geotop_convex_hull W"
    and heW: "geotop_simplex_vertices e W"
    and hW_card: "card W = 2"
    by (rule geotop_edge_face_witness_card_two_prefix[OF hedge he\<sigma>])
  have hW_fin: "finite W"
    using heW unfolding geotop_simplex_vertices_def by (by100 blast)
  obtain a b where hW_eq: "W = {a, b}" and hab: "a \<noteq> b"
    using hW_card card_2_iff by (by100 metis)
  have he_eq_ab: "e = geotop_convex_hull {a, b}"
    using he_eq_W hW_eq by (by100 simp)
  have hV_card: "card V = 3"
  proof -
    obtain V2 m where hV2_fin: "finite V2"
      and hV2_card: "card V2 = 2 + 1"
      and h2_le_m: "2 \<le> m"
      and hgp_V2: "geotop_general_position V2 m"
      and h\<sigma>_eq_V2: "\<sigma> = geotop_convex_hull V2"
      using h\<sigma>2 unfolding geotop_simplex_dim_def by (by100 blast)
    have h\<sigma>V2: "geotop_simplex_vertices \<sigma> V2"
      unfolding geotop_simplex_vertices_def
      using hV2_fin hV2_card h2_le_m hgp_V2 h\<sigma>_eq_V2 by (by100 blast)
    have hV_eq: "V = V2"
      by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>V2])
    show ?thesis
      using hV_eq hV2_card by (by100 simp)
  qed
  have hV_fin: "finite V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  obtain c where hcV: "c \<in> V" and hc_not_W: "c \<notin> W"
  proof -
    have "W \<noteq> V"
    proof
      assume hWV: "W = V"
      show False
        using hW_card hV_card hWV by (by100 arith)
    qed
    then obtain c where "c \<in> V" and "c \<notin> W"
      using hW_sub by (by100 blast)
    thus ?thesis
      by (rule that)
  qed
  have hc_not_ab: "c \<notin> {a, b}"
    using hc_not_W hW_eq by (by100 simp)
  have h\<sigma>V_ab: "geotop_simplex_vertices \<sigma> {a, b, c}"
  proof -
    have haV: "a \<in> V"
      using hW_eq hW_sub by (by100 blast)
    have hbV: "b \<in> V"
      using hW_eq hW_sub by (by100 blast)
    have hac: "a \<noteq> c"
      using hc_not_ab by (by100 blast)
    have hbc: "b \<noteq> c"
      using hc_not_ab by (by100 blast)
    have hV_eq: "V = {a, b, c}"
      by (rule geotop_2simplex_vertices_three_eq_prefix
          [OF h\<sigma>2 h\<sigma>V haV hbV hcV hab hac hbc])
    show ?thesis
      using h\<sigma>V hV_eq by (by100 simp)
  qed
  obtain V\<^sub>\<tau> W\<^sub>\<tau> where h\<tau>V: "geotop_simplex_vertices \<tau> V\<^sub>\<tau>"
    and hW\<tau>_ne: "W\<^sub>\<tau> \<noteq> {}"
    and hW\<tau>_sub: "W\<^sub>\<tau> \<subseteq> V\<^sub>\<tau>"
    and he_eq_W\<tau>: "e = geotop_convex_hull W\<^sub>\<tau>"
    and heW\<tau>: "geotop_simplex_vertices e W\<^sub>\<tau>"
    and hW\<tau>_card: "card W\<^sub>\<tau> = 2"
    by (rule geotop_edge_face_witness_card_two_prefix[OF hedge he\<tau>])
  have hW\<tau>_eq: "W\<^sub>\<tau> = W"
    by (rule geotop_simplex_vertices_unique[OF heW\<tau> heW])
  have hW_sub_V\<tau>: "W \<subseteq> V\<^sub>\<tau>"
    using hW\<tau>_sub hW\<tau>_eq by (by100 simp)
  have hV\<tau>_card: "card V\<^sub>\<tau> = 3"
  proof -
    obtain V2 m where hV2_fin: "finite V2"
      and hV2_card: "card V2 = 2 + 1"
      and h2_le_m: "2 \<le> m"
      and hgp_V2: "geotop_general_position V2 m"
      and h\<tau>_eq_V2: "\<tau> = geotop_convex_hull V2"
      using h\<tau>2 unfolding geotop_simplex_dim_def by (by100 blast)
    have h\<tau>V2: "geotop_simplex_vertices \<tau> V2"
      unfolding geotop_simplex_vertices_def
      using hV2_fin hV2_card h2_le_m hgp_V2 h\<tau>_eq_V2 by (by100 blast)
    have hV_eq: "V\<^sub>\<tau> = V2"
      by (rule geotop_simplex_vertices_unique[OF h\<tau>V h\<tau>V2])
    show ?thesis
      using hV_eq hV2_card by (by100 simp)
  qed
  have hV\<tau>_fin: "finite V\<^sub>\<tau>"
    using h\<tau>V unfolding geotop_simplex_vertices_def by (by100 blast)
  obtain d where hdV: "d \<in> V\<^sub>\<tau>" and hd_not_W: "d \<notin> W"
  proof -
    have "W \<noteq> V\<^sub>\<tau>"
    proof
      assume hWV: "W = V\<^sub>\<tau>"
      show False
        using hW_card hV\<tau>_card hWV by (by100 arith)
    qed
    then obtain d where "d \<in> V\<^sub>\<tau>" and "d \<notin> W"
      using hW_sub_V\<tau> by (by100 blast)
    thus ?thesis
      by (rule that)
  qed
  have hd_not_ab: "d \<notin> {a, b}"
    using hd_not_W hW_eq by (by100 simp)
  have h\<tau>V_ab: "geotop_simplex_vertices \<tau> {a, b, d}"
  proof -
    have haV: "a \<in> V\<^sub>\<tau>"
      using hW_eq hW_sub_V\<tau> by (by100 blast)
    have hbV: "b \<in> V\<^sub>\<tau>"
      using hW_eq hW_sub_V\<tau> by (by100 blast)
    have had: "a \<noteq> d"
      using hd_not_ab by (by100 blast)
    have hbd: "b \<noteq> d"
      using hd_not_ab by (by100 blast)
    have hV_eq: "V\<^sub>\<tau> = {a, b, d}"
      by (rule geotop_2simplex_vertices_three_eq_prefix
          [OF h\<tau>2 h\<tau>V haV hbV hdV hab had hbd])
    show ?thesis
      using h\<tau>V hV_eq by (by100 simp)
  qed
  have hcd: "c \<noteq> d"
  proof
    assume hcd_eq: "c = d"
    have h\<sigma>_eq: "\<sigma> = geotop_convex_hull {a, b, c}"
      using h\<sigma>V_ab unfolding geotop_simplex_vertices_def by (by100 blast)
    have h\<tau>_eq: "\<tau> = geotop_convex_hull {a, b, d}"
      using h\<tau>V_ab unfolding geotop_simplex_vertices_def by (by100 blast)
    have "\<sigma> = \<tau>"
      using h\<sigma>_eq h\<tau>_eq hcd_eq by (by100 simp)
    thus False
      using h\<sigma>\<tau> by (by100 blast)
  qed
  show ?thesis
    by (rule that[OF hab hc_not_ab hd_not_ab hcd he_eq_ab h\<sigma>V_ab h\<tau>V_ab])
qed

lemma geotop_two_2simplex_shared_edge_vertices_affine_obtain_prefix:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  assumes hedge: "geotop_is_edge e"
  obtains a b c d where
    "a \<noteq> b"
    "c \<notin> {a, b}"
    "d \<notin> {a, b}"
    "c \<noteq> d"
    "e = geotop_convex_hull {a, b}"
    "geotop_simplex_vertices \<sigma> {a, b, c}"
    "geotop_simplex_vertices \<tau> {a, b, d}"
    "c \<notin> affine hull {a, b}"
    "d \<notin> affine hull {a, b}"
  (**
    The same shared-edge vertex form, with the two opposite vertices certified
    off the affine line of the common edge. **)
proof -
  obtain a b c d where hab: "a \<noteq> b"
    and hc_not_ab: "c \<notin> {a, b}"
    and hd_not_ab: "d \<notin> {a, b}"
    and hcd: "c \<noteq> d"
    and he_eq: "e = geotop_convex_hull {a, b}"
    and h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
    and h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
    by (rule geotop_two_2simplex_shared_edge_vertices_obtain_prefix
        [OF h\<sigma>2 h\<tau>2 h\<sigma>\<tau> he\<sigma> he\<tau> hedge])
  have hc_aff: "c \<notin> affine hull {a, b}"
    by (rule geotop_2simplex_opposite_vertex_notin_edge_affine_hull_prefix
        [OF h\<sigma>V hc_not_ab])
  have hd_aff: "d \<notin> affine hull {a, b}"
    by (rule geotop_2simplex_opposite_vertex_notin_edge_affine_hull_prefix
        [OF h\<tau>V hd_not_ab])
  show ?thesis
    by (rule that[OF hab hc_not_ab hd_not_ab hcd he_eq h\<sigma>V h\<tau>V hc_aff hd_aff])
qed

lemma geotop_edge_vertices_affine_hull_normal_form_prefix:
  fixes e :: "(real^2) set"
  assumes hedge: "geotop_is_edge e"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  shows "\<exists>n d. n \<noteq> 0 \<and> affine hull {a, b} = {x. n \<bullet> x = d}"
  (**
    The affine hull of the shared edge is a genuine line in the plane, written
    in normal form for the subsequent half-plane argument. **)
proof -
  have he1: "geotop_simplex_dim e 1"
    using hedge unfolding geotop_is_edge_def by (by100 simp)
  have hhyper: "geotop_hyperplane_dim (affine hull e) 1"
    by (rule geotop_simplex_dim_imp_hyperplane_dim[OF he1])
  obtain n d where hn: "n \<noteq> 0"
    and hline_e: "affine hull e = {x. n \<bullet> x = d}"
    using geotop_hyperplane_dim_1_R2_normal_form[OF hhyper] by (by100 blast)
  have he_HOL: "e = convex hull {a, b}"
    using he_eq geotop_convex_hull_eq_HOL by (by100 simp)
  have haff_eq: "affine hull e = affine hull {a, b}"
    using he_HOL affine_hull_convex_hull[of "{a, b}"] by (by100 simp)
  have hline_ab: "affine hull {a, b} = {x. n \<bullet> x = d}"
    using haff_eq hline_e by (by100 simp)
  show ?thesis
    using hn hline_ab by (by100 blast)
qed

lemma geotop_two_2simplex_shared_edge_vertices_normal_obtain_prefix:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  assumes hedge: "geotop_is_edge e"
  obtains a b c d n r where
    "a \<noteq> b"
    "c \<notin> {a, b}"
    "d \<notin> {a, b}"
    "c \<noteq> d"
    "e = geotop_convex_hull {a, b}"
    "geotop_simplex_vertices \<sigma> {a, b, c}"
    "geotop_simplex_vertices \<tau> {a, b, d}"
    "n \<noteq> 0"
    "affine hull {a, b} = {x. n \<bullet> x = r}"
    "n \<bullet> c \<noteq> r"
    "n \<bullet> d \<noteq> r"
  (**
    Normal-coordinate version of the shared-edge picture: the two opposite
    vertices are strictly off the line through the common edge. **)
proof -
  obtain a b c d where hab: "a \<noteq> b"
    and hc_not_ab: "c \<notin> {a, b}"
    and hd_not_ab: "d \<notin> {a, b}"
    and hcd: "c \<noteq> d"
    and he_eq: "e = geotop_convex_hull {a, b}"
    and h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
    and h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
    and hc_aff: "c \<notin> affine hull {a, b}"
    and hd_aff: "d \<notin> affine hull {a, b}"
    by (rule geotop_two_2simplex_shared_edge_vertices_affine_obtain_prefix
        [OF h\<sigma>2 h\<tau>2 h\<sigma>\<tau> he\<sigma> he\<tau> hedge])
  obtain n r where hn: "n \<noteq> 0"
    and hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
    using geotop_edge_vertices_affine_hull_normal_form_prefix[OF hedge he_eq]
    by (by100 blast)
  have hc_ne: "n \<bullet> c \<noteq> r"
  proof
    assume hc_eq: "n \<bullet> c = r"
    have "c \<in> affine hull {a, b}"
      using hline hc_eq by (by100 simp)
    thus False
      using hc_aff by (by100 blast)
  qed
  have hd_ne: "n \<bullet> d \<noteq> r"
  proof
    assume hd_eq: "n \<bullet> d = r"
    have "d \<in> affine hull {a, b}"
      using hline hd_eq by (by100 simp)
    thus False
      using hd_aff by (by100 blast)
  qed
  show ?thesis
    by (rule that[OF hab hc_not_ab hd_not_ab hcd he_eq h\<sigma>V h\<tau>V
          hn hline hc_ne hd_ne])
qed

lemma geotop_2simplex_vertices_HOL_interior_explicit_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  shows "interior \<sigma> =
    {v. \<exists>x y z. 0 < x \<and> 0 < y \<and> 0 < z \<and> x + y + z = 1
      \<and> x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = v}"
  (**
    HOL positive-barycentric description of the interior of a nondegenerate
    2-simplex, specialized to the vertex triples used in the shared-edge
    local model. **)
proof -
  have h\<sigma>_geo: "\<sigma> = geotop_convex_hull {a, b, c}"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have h\<sigma>_HOL: "\<sigma> = convex hull {a, b, c}"
    using h\<sigma>_geo geotop_convex_hull_eq_HOL[of "{a, b, c}"] by (by100 simp)
  have h_ai: "\<not> affine_dependent {a, b, c}"
    by (rule geotop_general_position_imp_aff_indep[OF h\<sigma>V])
  have hac: "a \<noteq> c"
    using hc_not_ab by (by100 blast)
  have hbc: "b \<noteq> c"
    using hc_not_ab by (by100 blast)
  have hcol_eq:
    "collinear {a, b, c} =
      (a = b \<or> a = c \<or> b = c \<or> affine_dependent {a, b, c})"
    by (rule collinear_3_eq_affine_dependent)
  have hnoncol: "\<not> collinear {a, b, c}"
    using h_ai hab hac hbc hcol_eq by (by100 simp)
  have hdim: "DIM(real^2) = 2"
    by (by100 simp)
  have hinter:
    "interior (convex hull {a, b, c}) =
      {v. \<exists>x y z. 0 < x \<and> 0 < y \<and> 0 < z \<and> x + y + z = 1
        \<and> x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = v}"
    by (rule interior_convex_hull_3_minimal[OF hnoncol hdim])
  show ?thesis
    using h\<sigma>_HOL hinter by (by100 simp)
qed

lemma geotop_2simplex_positive_bary_in_HOL_interior_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hx: "0 < x"
  assumes hy: "0 < y"
  assumes hz: "0 < z"
  assumes hsum: "x + y + z = 1"
  assumes hp: "p = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
  shows "p \<in> interior \<sigma>"
  (**
    Direct membership form of the positive-barycentric interior
    characterization. **)
proof -
  have hinter:
    "interior \<sigma> =
      {v. \<exists>x y z. 0 < x \<and> 0 < y \<and> 0 < z \<and> x + y + z = 1
        \<and> x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = v}"
    by (rule geotop_2simplex_vertices_HOL_interior_explicit_prefix
        [OF hab hc_not_ab h\<sigma>V])
  have "p \<in>
      {v. \<exists>x y z. 0 < x \<and> 0 < y \<and> 0 < z \<and> x + y + z = 1
        \<and> x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = v}"
    using hx hy hz hsum hp by (by100 blast)
  thus ?thesis
    using hinter by (by100 simp)
qed

lemma geotop_2simplex_HOL_interior_positive_side_of_edge_line_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c > r"
  assumes hp: "p \<in> interior \<sigma>"
  shows "n \<bullet> p > r"
  (**
    Positive-side half-plane form of the triangle interior: interior points of
    the triangle lie on the same strict side of the edge line as the opposite
    vertex. **)
proof -
  have ha_aff: "a \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have hb_aff: "b \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have ha_line: "n \<bullet> a = r"
    using hline ha_aff by (by100 simp)
  have hb_line: "n \<bullet> b = r"
    using hline hb_aff by (by100 simp)
  have hinter:
    "interior \<sigma> =
      {v. \<exists>x y z. 0 < x \<and> 0 < y \<and> 0 < z \<and> x + y + z = 1
        \<and> x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = v}"
    by (rule geotop_2simplex_vertices_HOL_interior_explicit_prefix
        [OF hab hc_not_ab h\<sigma>V])
  obtain x y z where hx: "0 < x"
    and hy: "0 < y"
    and hz: "0 < z"
    and hsum: "x + y + z = 1"
    and hp_eq: "x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = p"
    using hp hinter by (by100 blast)
  have hp_eq': "p = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
    using hp_eq by (by100 simp)
  have hp_dot: "n \<bullet> p = x * r + y * r + z * (n \<bullet> c)"
  proof -
    have "n \<bullet> p = n \<bullet> (x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c)"
      using hp_eq' by (by100 simp)
    also have "\<dots> = n \<bullet> (x *\<^sub>R a) + n \<bullet> (y *\<^sub>R b) + n \<bullet> (z *\<^sub>R c)"
      by (simp add: inner_add_right)
    also have "\<dots> = x * (n \<bullet> a) + y * (n \<bullet> b) + z * (n \<bullet> c)"
      by (simp add: inner_scaleR_right)
    also have "\<dots> = x * r + y * r + z * (n \<bullet> c)"
      using ha_line hb_line by (by100 simp)
    finally show ?thesis .
  qed
  have hsum_r: "x * r + y * r + z * r = r"
  proof -
    have "r * (x + y + z) = r"
      using hsum by (by100 simp)
    thus ?thesis
      by (simp add: algebra_simps)
  qed
  have "n \<bullet> p - r = z * (n \<bullet> c - r)"
  proof -
    have "n \<bullet> p - r =
        (x * r + y * r + z * (n \<bullet> c)) - (x * r + y * r + z * r)"
      using hp_dot hsum_r by (by100 linarith)
    also have "\<dots> = z * (n \<bullet> c - r)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  moreover have "0 < n \<bullet> c - r"
    using hc_side by (by100 linarith)
  hence "0 < z * (n \<bullet> c - r)"
    by (rule mult_pos_pos[OF hz])
  ultimately have "0 < n \<bullet> p - r"
    by (by100 linarith)
  thus ?thesis
    by (by100 linarith)
qed

lemma geotop_2simplex_HOL_interior_negative_side_of_edge_line_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c < r"
  assumes hp: "p \<in> interior \<sigma>"
  shows "n \<bullet> p < r"
  (**
    Negative-side half-plane form of the triangle interior, symmetric to the
    positive-side version. **)
proof -
  have ha_aff: "a \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have hb_aff: "b \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have ha_line: "n \<bullet> a = r"
    using hline ha_aff by (by100 simp)
  have hb_line: "n \<bullet> b = r"
    using hline hb_aff by (by100 simp)
  have hinter:
    "interior \<sigma> =
      {v. \<exists>x y z. 0 < x \<and> 0 < y \<and> 0 < z \<and> x + y + z = 1
        \<and> x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = v}"
    by (rule geotop_2simplex_vertices_HOL_interior_explicit_prefix
        [OF hab hc_not_ab h\<sigma>V])
  obtain x y z where hx: "0 < x"
    and hy: "0 < y"
    and hz: "0 < z"
    and hsum: "x + y + z = 1"
    and hp_eq: "x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c = p"
    using hp hinter by (by100 blast)
  have hp_eq': "p = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
    using hp_eq by (by100 simp)
  have hp_dot: "n \<bullet> p = x * r + y * r + z * (n \<bullet> c)"
  proof -
    have "n \<bullet> p = n \<bullet> (x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c)"
      using hp_eq' by (by100 simp)
    also have "\<dots> = n \<bullet> (x *\<^sub>R a) + n \<bullet> (y *\<^sub>R b) + n \<bullet> (z *\<^sub>R c)"
      by (simp add: inner_add_right)
    also have "\<dots> = x * (n \<bullet> a) + y * (n \<bullet> b) + z * (n \<bullet> c)"
      by (simp add: inner_scaleR_right)
    also have "\<dots> = x * r + y * r + z * (n \<bullet> c)"
      using ha_line hb_line by (by100 simp)
    finally show ?thesis .
  qed
  have hsum_r: "x * r + y * r + z * r = r"
  proof -
    have "r * (x + y + z) = r"
      using hsum by (by100 simp)
    thus ?thesis
      by (simp add: algebra_simps)
  qed
  have "n \<bullet> p - r = z * (n \<bullet> c - r)"
  proof -
    have "n \<bullet> p - r =
        (x * r + y * r + z * (n \<bullet> c)) - (x * r + y * r + z * r)"
      using hp_dot hsum_r by (by100 linarith)
    also have "\<dots> = z * (n \<bullet> c - r)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  moreover have "n \<bullet> c - r < 0"
    using hc_side by (by100 linarith)
  hence "z * (n \<bullet> c - r) < 0"
    by (rule mult_pos_neg[OF hz])
  ultimately have "n \<bullet> p - r < 0"
    by (by100 linarith)
  thus ?thesis
    by (by100 linarith)
qed

lemma geotop_2simplex_HOL_interior_subset_positive_side_of_edge_line_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c > r"
  shows "interior \<sigma> \<subseteq> {p. n \<bullet> p > r}"
  (**
    Set-form positive half-plane containment for the shared-edge triangle
    interior. **)
proof
  fix p
  assume hp: "p \<in> interior \<sigma>"
  have "n \<bullet> p > r"
    by (rule geotop_2simplex_HOL_interior_positive_side_of_edge_line_prefix
        [OF hab hc_not_ab h\<sigma>V hline hc_side hp])
  thus "p \<in> {p. n \<bullet> p > r}"
    by (by100 simp)
qed

lemma geotop_2simplex_HOL_interior_subset_negative_side_of_edge_line_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c < r"
  shows "interior \<sigma> \<subseteq> {p. n \<bullet> p < r}"
  (**
    Set-form negative half-plane containment for the shared-edge triangle
    interior. **)
proof
  fix p
  assume hp: "p \<in> interior \<sigma>"
  have "n \<bullet> p < r"
    by (rule geotop_2simplex_HOL_interior_negative_side_of_edge_line_prefix
        [OF hab hc_not_ab h\<sigma>V hline hc_side hp])
  thus "p \<in> {p. n \<bullet> p < r}"
    by (by100 simp)
qed

lemma geotop_two_2simplex_shared_edge_vertices_side_obtain_prefix:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  assumes hedge: "geotop_is_edge e"
  obtains a b c d n r where
    "a \<noteq> b"
    "c \<notin> {a, b}"
    "d \<notin> {a, b}"
    "c \<noteq> d"
    "e = geotop_convex_hull {a, b}"
    "geotop_simplex_vertices \<sigma> {a, b, c}"
    "geotop_simplex_vertices \<tau> {a, b, d}"
    "n \<noteq> 0"
    "affine hull {a, b} = {x. n \<bullet> x = r}"
    "n \<bullet> c \<noteq> r"
    "n \<bullet> d \<noteq> r"
    "n \<bullet> c > r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p > r}"
    "n \<bullet> c < r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p < r}"
    "n \<bullet> d > r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p > r}"
    "n \<bullet> d < r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p < r}"
  (**
    Shared-edge normal-coordinate package with the half-plane containments for
    the two triangle interiors. **)
proof -
  obtain a b c d n r where hab: "a \<noteq> b"
    and hc_not_ab: "c \<notin> {a, b}"
    and hd_not_ab: "d \<notin> {a, b}"
    and hcd: "c \<noteq> d"
    and he_eq: "e = geotop_convex_hull {a, b}"
    and h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
    and h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
    and hn: "n \<noteq> 0"
    and hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
    and hc_ne: "n \<bullet> c \<noteq> r"
    and hd_ne: "n \<bullet> d \<noteq> r"
    by (rule geotop_two_2simplex_shared_edge_vertices_normal_obtain_prefix
        [OF h\<sigma>2 h\<tau>2 h\<sigma>\<tau> he\<sigma> he\<tau> hedge])
  have h\<sigma>_pos: "n \<bullet> c > r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p > r}"
    by (rule geotop_2simplex_HOL_interior_subset_positive_side_of_edge_line_prefix
        [OF hab hc_not_ab h\<sigma>V hline])
  have h\<sigma>_neg: "n \<bullet> c < r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p < r}"
    by (rule geotop_2simplex_HOL_interior_subset_negative_side_of_edge_line_prefix
        [OF hab hc_not_ab h\<sigma>V hline])
  have h\<tau>_pos: "n \<bullet> d > r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p > r}"
    by (rule geotop_2simplex_HOL_interior_subset_positive_side_of_edge_line_prefix
        [OF hab hd_not_ab h\<tau>V hline])
  have h\<tau>_neg: "n \<bullet> d < r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p < r}"
    by (rule geotop_2simplex_HOL_interior_subset_negative_side_of_edge_line_prefix
        [OF hab hd_not_ab h\<tau>V hline])
  show ?thesis
    by (rule that[OF hab hc_not_ab hd_not_ab hcd he_eq h\<sigma>V h\<tau>V
          hn hline hc_ne hd_ne h\<sigma>_pos h\<sigma>_neg h\<tau>_pos h\<tau>_neg])
qed

lemma geotop_edge_vertices_subset_affine_hull_prefix:
  fixes e :: "(real^2) set"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  shows "e \<subseteq> affine hull {a, b}"
  (**
    Edge-line containment used in the shared-edge local model: the common edge
    itself lies in the affine line through its two vertices. **)
proof -
  have he_HOL: "e = convex hull {a, b}"
    using he_eq geotop_convex_hull_eq_HOL by (by100 simp)
  have "convex hull {a, b} \<subseteq> affine hull {a, b}"
    by (rule convex_hull_subset_affine_hull)
  thus ?thesis
    using he_HOL by (by100 simp)
qed

lemma geotop_edge_vertices_subset_normal_line_prefix:
  fixes e :: "(real^2) set"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  shows "e \<subseteq> {x. n \<bullet> x = r}"
  (**
    Normal-form version of edge-line containment for the half-plane
    contradiction in the two-triangle edge model. **)
proof -
  have he_aff: "e \<subseteq> affine hull {a, b}"
    by (rule geotop_edge_vertices_subset_affine_hull_prefix[OF he_eq])
  show ?thesis
    using he_aff hline by (by100 simp)
qed

lemma geotop_complex_distinct_2simplex_HOL_interiors_disjoint_prefix:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  shows "interior \<sigma> \<inter> interior \<tau> = {}"
  (**
    Complex disjointness in the ordinary plane-interior form needed by the
    shared-edge half-plane contradiction. **)
proof -
  have h\<sigma>_int: "interior \<sigma> = rel_interior \<sigma>"
    by (rule geotop_2simplex_HOL_interior_eq_rel_interior_prefix[OF h\<sigma>2])
  have h\<tau>_int: "interior \<tau> = rel_interior \<tau>"
    by (rule geotop_2simplex_HOL_interior_eq_rel_interior_prefix[OF h\<tau>2])
  have hrel_disj: "rel_interior \<sigma> \<inter> rel_interior \<tau> = {}"
    by (rule geotop_complex_rel_interior_disjoint_distinct[OF hK h\<sigma>K h\<tau>K h\<sigma>\<tau>])
  show ?thesis
    using h\<sigma>_int h\<tau>_int hrel_disj by (by100 simp)
qed

lemma geotop_2simplex_vertices_affine_hull_UNIV_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  shows "affine hull {a, b, c} = UNIV"
  (**
    Noncollinear vertices of a GeoTop 2-simplex affinely span the whole
    ambient plane. **)
proof -
  have h_ai: "\<not> affine_dependent {a, b, c}"
    by (rule geotop_general_position_imp_aff_indep[OF h\<sigma>V])
  have hac: "a \<noteq> c"
    using hc_not_ab by (by100 blast)
  have hbc: "b \<noteq> c"
    using hc_not_ab by (by100 blast)
  have hcard: "card {a, b, c} = 3"
    using hab hac hbc by (by100 simp)
  have hdim: "aff_dim {a, b, c} = 2"
    using h_ai hcard affine_independent_iff_card[of "{a, b, c}"] by (by100 simp)
  have hdim_UNIV: "aff_dim {a, b, c} = DIM(real^2)"
    using hdim by (by100 simp)
  show ?thesis
    using aff_dim_eq_full[of "{a, b, c}"] hdim_UNIV by (by100 simp)
qed

lemma geotop_2simplex_vertices_affine_coordinates_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  shows "\<exists>x y z. x + y + z = 1
      \<and> d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
  (**
    Affine-coordinate existence for the same-side overlap construction. **)
proof -
  have hUNIV: "affine hull {a, b, c} = UNIV"
    by (rule geotop_2simplex_vertices_affine_hull_UNIV_prefix
        [OF hab hc_not_ab h\<sigma>V])
  have hd_aff: "d \<in> affine hull {a, b, c}"
    using hUNIV by (by100 simp)
  obtain x y z where hsum: "x + y + z = 1"
    and hd: "d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
    using hd_aff affine_hull_3[of a b c] by (by100 blast)
  show ?thesis
    using hsum hd by (by100 blast)
qed

lemma geotop_2simplex_positive_side_affine_coordinate_positive_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c > r"
  assumes hd_side: "n \<bullet> d > r"
  shows "\<exists>x y z. x + y + z = 1
      \<and> d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c
      \<and> 0 < z"
  (**
    Same positive side of the edge line means the affine coordinate at the
    opposite vertex \<open>c\<close> is positive. **)
proof -
  have ha_aff: "a \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have hb_aff: "b \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have ha_line: "n \<bullet> a = r"
    using hline ha_aff by (by100 simp)
  have hb_line: "n \<bullet> b = r"
    using hline hb_aff by (by100 simp)
  obtain x y z where hsum: "x + y + z = 1"
    and hd: "d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
    using geotop_2simplex_vertices_affine_coordinates_prefix
      [OF hab hc_not_ab h\<sigma>V, of d]
    by (by100 blast)
  have hd_dot: "n \<bullet> d = x * r + y * r + z * (n \<bullet> c)"
  proof -
    have "n \<bullet> d = n \<bullet> (x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c)"
      using hd by (by100 simp)
    also have "\<dots> = n \<bullet> (x *\<^sub>R a) + n \<bullet> (y *\<^sub>R b) + n \<bullet> (z *\<^sub>R c)"
      by (simp add: inner_add_right)
    also have "\<dots> = x * (n \<bullet> a) + y * (n \<bullet> b) + z * (n \<bullet> c)"
      by (simp add: inner_scaleR_right)
    also have "\<dots> = x * r + y * r + z * (n \<bullet> c)"
      using ha_line hb_line by (by100 simp)
    finally show ?thesis .
  qed
  have hsum_r: "x * r + y * r + z * r = r"
  proof -
    have "r * (x + y + z) = r"
      using hsum by (by100 simp)
    thus ?thesis
      by (simp add: algebra_simps)
  qed
  have hdiff: "n \<bullet> d - r = z * (n \<bullet> c - r)"
  proof -
    have "n \<bullet> d - r =
        (x * r + y * r + z * (n \<bullet> c)) - (x * r + y * r + z * r)"
      using hd_dot hsum_r by (by100 linarith)
    also have "\<dots> = z * (n \<bullet> c - r)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have hprod_pos: "0 < z * (n \<bullet> c - r)"
    using hdiff hd_side by (by100 linarith)
  have hden_pos: "0 < n \<bullet> c - r"
    using hc_side by (by100 linarith)
  have hz: "0 < z"
    using hprod_pos hden_pos by (simp add: zero_less_mult_iff)
  show ?thesis
    using hsum hd hz by (by100 blast)
qed

lemma geotop_2simplex_negative_side_affine_coordinate_positive_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c < r"
  assumes hd_side: "n \<bullet> d < r"
  shows "\<exists>x y z. x + y + z = 1
      \<and> d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c
      \<and> 0 < z"
  (**
    Negative-side version, obtained by reversing the normal vector. **)
proof -
  have hline_neg: "affine hull {a, b} = {x. (-n) \<bullet> x = -r}"
    using hline by (simp add: set_eq_iff)
  have hc_pos: "(-n) \<bullet> c > -r"
    using hc_side by (by100 simp)
  have hd_pos: "(-n) \<bullet> d > -r"
    using hd_side by (by100 simp)
  show ?thesis
    by (rule geotop_2simplex_positive_side_affine_coordinate_positive_prefix
        [OF hab hc_not_ab h\<sigma>V hline_neg hc_pos hd_pos])
qed

lemma geotop_real_positive_overlap_parameter_prefix:
  fixes x y z :: real
  assumes hz: "0 < z"
  obtains s where
    "0 < s"
    "s < 1"
    "0 < (1 - s) / 2 + s * x"
    "0 < (1 - s) / 2 + s * y"
    "0 < s * z"
  (**
    Real parameter choice for the same-side overlap construction: move a small
    positive distance from the edge midpoint toward the second opposite vertex,
    while keeping positive barycentric coordinates in the first triangle. **)
proof -
  define bx where "bx = (if x < 1 / 2 then (1 / 2) / (1 / 2 - x) else 1)"
  define byy where "byy = (if y < 1 / 2 then (1 / 2) / (1 / 2 - y) else 1)"
  have hbx_pos: "0 < bx"
  proof (cases "x < 1 / 2")
    case True
    have "0 < 1 / 2 - x"
      using True by (by100 linarith)
    hence "0 < (1 / 2) / (1 / 2 - x)"
      by (simp add: divide_pos_pos)
    thus ?thesis
      using True bx_def by (by100 simp)
  next
    case False
    show ?thesis
      using False bx_def by (by100 simp)
  qed
  have hby_pos: "0 < byy"
  proof (cases "y < 1 / 2")
    case True
    have "0 < 1 / 2 - y"
      using True by (by100 linarith)
    hence "0 < (1 / 2) / (1 / 2 - y)"
      by (simp add: divide_pos_pos)
    thus ?thesis
      using True byy_def by (by100 simp)
  next
    case False
    show ?thesis
      using False byy_def by (by100 simp)
  qed
  obtain t where ht0: "0 < t" and htbx: "t < bx" and ht1: "t < 1"
    using field_lbound_gt_zero[OF hbx_pos zero_less_one] by (by100 blast)
  obtain s where hs0: "0 < s" and hst: "s < t" and hsby: "s < byy"
    using field_lbound_gt_zero[OF ht0 hby_pos] by (by100 blast)
  have hs1: "s < 1"
    using hst ht1 by (by100 linarith)
  have hsbx: "s < bx"
    using hst htbx by (by100 linarith)
  have hxpos: "0 < (1 - s) / 2 + s * x"
  proof (cases "x < 1 / 2")
    case True
    have hden: "0 < 1 / 2 - x"
      using True by (by100 linarith)
    have hsbound: "s < (1 / 2) / (1 / 2 - x)"
      using hsbx True bx_def by (by100 simp)
    have "s * (1 / 2 - x) < 1 / 2"
      using hsbound hden by (simp add: field_simps)
    hence "0 < 1 / 2 - s * (1 / 2 - x)"
      by (by100 linarith)
    also have "1 / 2 - s * (1 / 2 - x) = (1 - s) / 2 + s * x"
      by (simp add: field_simps algebra_simps)
    finally show ?thesis .
  next
    case False
    have hnonneg: "0 \<le> x - 1 / 2"
      using False by (by100 linarith)
    have hs_nonneg: "0 \<le> s"
      using hs0 by (by100 linarith)
    have "0 \<le> s * (x - 1 / 2)"
      by (rule mult_nonneg_nonneg[OF hs_nonneg hnonneg])
    moreover have "(1 - s) / 2 + s * x = 1 / 2 + s * (x - 1 / 2)"
      by (simp add: field_simps algebra_simps)
    ultimately show ?thesis
      by (by100 linarith)
  qed
  have hypos: "0 < (1 - s) / 2 + s * y"
  proof (cases "y < 1 / 2")
    case True
    have hden: "0 < 1 / 2 - y"
      using True by (by100 linarith)
    have hsbound: "s < (1 / 2) / (1 / 2 - y)"
      using hsby True byy_def by (by100 simp)
    have "s * (1 / 2 - y) < 1 / 2"
      using hsbound hden by (simp add: field_simps)
    hence "0 < 1 / 2 - s * (1 / 2 - y)"
      by (by100 linarith)
    also have "1 / 2 - s * (1 / 2 - y) = (1 - s) / 2 + s * y"
      by (simp add: field_simps algebra_simps)
    finally show ?thesis .
  next
    case False
    have hnonneg: "0 \<le> y - 1 / 2"
      using False by (by100 linarith)
    have hs_nonneg: "0 \<le> s"
      using hs0 by (by100 linarith)
    have "0 \<le> s * (y - 1 / 2)"
      by (rule mult_nonneg_nonneg[OF hs_nonneg hnonneg])
    moreover have "(1 - s) / 2 + s * y = 1 / 2 + s * (y - 1 / 2)"
      by (simp add: field_simps algebra_simps)
    ultimately show ?thesis
      by (by100 linarith)
  qed
  have hsz: "0 < s * z"
    by (rule mult_pos_pos[OF hs0 hz])
  show ?thesis
    by (rule that[OF hs0 hs1 hxpos hypos hsz])
qed

lemma geotop_2simplex_affine_coordinate_HOL_interiors_meet_prefix:
  fixes \<sigma> \<tau> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes hd_not_ab: "d \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
  assumes hsum: "x + y + z = 1"
  assumes hd: "d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
  assumes hz: "0 < z"
  shows "interior \<sigma> \<inter> interior \<tau> \<noteq> {}"
  (**
    Same-side overlap construction in barycentric coordinates: a small segment
    from the edge midpoint toward \<open>d\<close> lies in \<open>\<tau>\<close>'s interior and, after
    substituting the affine coordinates of \<open>d\<close>, also in \<open>\<sigma>\<close>'s interior. **)
proof -
  obtain s where hs0: "0 < s"
    and hs1: "s < 1"
    and hxpos: "0 < (1 - s) / 2 + s * x"
    and hypos: "0 < (1 - s) / 2 + s * y"
    and hsz: "0 < s * z"
    by (rule geotop_real_positive_overlap_parameter_prefix[OF hz])
  define u where "u = (1 - s) / 2"
  define p where "p = u *\<^sub>R a + u *\<^sub>R b + s *\<^sub>R d"
  have hu: "0 < u"
    using hs1 unfolding u_def by (simp add: field_simps)
  have hsum\<tau>: "u + u + s = 1"
    unfolding u_def by (simp add: field_simps)
  have hp\<tau>: "p \<in> interior \<tau>"
    by (rule geotop_2simplex_positive_bary_in_HOL_interior_prefix
        [OF hab hd_not_ab h\<tau>V hu hu hs0 hsum\<tau> p_def])
  have hxpos': "0 < u + s * x"
    using hxpos unfolding u_def by (by100 simp)
  have hypos': "0 < u + s * y"
    using hypos unfolding u_def by (by100 simp)
  have hsum\<sigma>: "(u + s * x) + (u + s * y) + s * z = 1"
  proof -
    have "(u + s * x) + (u + s * y) + s * z = u + u + s * (x + y + z)"
      by (simp add: algebra_simps)
    also have "\<dots> = u + u + s"
      using hsum by (by100 simp)
    also have "\<dots> = 1"
      using hsum\<tau> by (by100 simp)
    finally show ?thesis .
  qed
  have hp_eq\<sigma>:
      "p = (u + s * x) *\<^sub>R a + (u + s * y) *\<^sub>R b + (s * z) *\<^sub>R c"
    unfolding p_def hd by (simp add: algebra_simps scaleR_add_left scaleR_add_right)
  have hp\<sigma>: "p \<in> interior \<sigma>"
    by (rule geotop_2simplex_positive_bary_in_HOL_interior_prefix
        [OF hab hc_not_ab h\<sigma>V hxpos' hypos' hsz hsum\<sigma> hp_eq\<sigma>])
  have "p \<in> interior \<sigma> \<inter> interior \<tau>"
    using hp\<sigma> hp\<tau> by (by100 blast)
  thus ?thesis
    by (by100 blast)
qed

lemma geotop_2simplex_positive_same_side_HOL_interiors_meet_prefix:
  fixes \<sigma> \<tau> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes hd_not_ab: "d \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c > r"
  assumes hd_side: "n \<bullet> d > r"
  shows "interior \<sigma> \<inter> interior \<tau> \<noteq> {}"
  (**
    If both opposite vertices lie on the positive side of the shared-edge line,
    the barycentric overlap construction gives a common interior point. **)
proof -
  obtain x y z where hsum: "x + y + z = 1"
    and hd: "d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
    and hz: "0 < z"
    using geotop_2simplex_positive_side_affine_coordinate_positive_prefix
      [OF hab hc_not_ab h\<sigma>V hline hc_side hd_side]
    by (by100 blast)
  show ?thesis
    by (rule geotop_2simplex_affine_coordinate_HOL_interiors_meet_prefix
        [OF hab hc_not_ab hd_not_ab h\<sigma>V h\<tau>V hsum hd hz])
qed

lemma geotop_2simplex_negative_same_side_HOL_interiors_meet_prefix:
  fixes \<sigma> \<tau> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes hd_not_ab: "d \<notin> {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c < r"
  assumes hd_side: "n \<bullet> d < r"
  shows "interior \<sigma> \<inter> interior \<tau> \<noteq> {}"
  (**
    Negative-side same-side version, symmetric to the positive-side wrapper. **)
proof -
  obtain x y z where hsum: "x + y + z = 1"
    and hd: "d = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
    and hz: "0 < z"
    using geotop_2simplex_negative_side_affine_coordinate_positive_prefix
      [OF hab hc_not_ab h\<sigma>V hline hc_side hd_side]
    by (by100 blast)
  show ?thesis
    by (rule geotop_2simplex_affine_coordinate_HOL_interiors_meet_prefix
        [OF hab hc_not_ab hd_not_ab h\<sigma>V h\<tau>V hsum hd hz])
qed

lemma geotop_complex_two_2simplex_shared_edge_vertices_opposite_sides_prefix:
  fixes K :: "(real^2) set set"
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  assumes hedge: "geotop_is_edge e"
  obtains a b c d n r where
    "a \<noteq> b"
    "c \<notin> {a, b}"
    "d \<notin> {a, b}"
    "c \<noteq> d"
    "e = geotop_convex_hull {a, b}"
    "geotop_simplex_vertices \<sigma> {a, b, c}"
    "geotop_simplex_vertices \<tau> {a, b, d}"
    "n \<noteq> 0"
    "affine hull {a, b} = {x. n \<bullet> x = r}"
    "n \<bullet> c \<noteq> r"
    "n \<bullet> d \<noteq> r"
    "n \<bullet> c > r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p > r}"
    "n \<bullet> c < r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p < r}"
    "n \<bullet> d > r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p > r}"
    "n \<bullet> d < r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p < r}"
    "(n \<bullet> c > r \<and> n \<bullet> d < r) \<or> (n \<bullet> c < r \<and> n \<bullet> d > r)"
  (**
    Same-complex strengthening of the shared-edge side package: if the two
    2-simplexes put their opposite vertices on the same strict side of the
    shared edge line, the previous overlap lemma gives a common HOL-interior
    point, contradicting complex relative-interior disjointness. **)
proof (rule geotop_two_2simplex_shared_edge_vertices_side_obtain_prefix
    [OF h\<sigma>2 h\<tau>2 h\<sigma>\<tau> he\<sigma> he\<tau> hedge])
  fix a b c d n r
  assume hab: "a \<noteq> b"
    and hc_not_ab: "c \<notin> {a, b}"
    and hd_not_ab: "d \<notin> {a, b}"
    and hcd: "c \<noteq> d"
    and he_eq: "e = geotop_convex_hull {a, b}"
    and h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
    and h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
    and hn: "n \<noteq> 0"
    and hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
    and hc_ne: "n \<bullet> c \<noteq> r"
    and hd_ne: "n \<bullet> d \<noteq> r"
    and h\<sigma>_pos: "n \<bullet> c > r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p > r}"
    and h\<sigma>_neg: "n \<bullet> c < r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p < r}"
    and h\<tau>_pos: "n \<bullet> d > r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p > r}"
    and h\<tau>_neg: "n \<bullet> d < r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p < r}"
  have hdisj: "interior \<sigma> \<inter> interior \<tau> = {}"
    by (rule geotop_complex_distinct_2simplex_HOL_interiors_disjoint_prefix
        [OF hK h\<sigma>K h\<tau>K h\<sigma>2 h\<tau>2 h\<sigma>\<tau>])
  have hpos_not: "\<not> (n \<bullet> c > r \<and> n \<bullet> d > r)"
  proof
    assume hsame: "n \<bullet> c > r \<and> n \<bullet> d > r"
    have hc_side: "n \<bullet> c > r"
      using hsame by (by100 blast)
    have hd_side: "n \<bullet> d > r"
      using hsame by (by100 blast)
    have hmeet: "interior \<sigma> \<inter> interior \<tau> \<noteq> {}"
      by (rule geotop_2simplex_positive_same_side_HOL_interiors_meet_prefix
          [OF hab hc_not_ab hd_not_ab h\<sigma>V h\<tau>V hline hc_side hd_side])
    show False
      using hdisj hmeet by (by100 blast)
  qed
  have hneg_not: "\<not> (n \<bullet> c < r \<and> n \<bullet> d < r)"
  proof
    assume hsame: "n \<bullet> c < r \<and> n \<bullet> d < r"
    have hc_side: "n \<bullet> c < r"
      using hsame by (by100 blast)
    have hd_side: "n \<bullet> d < r"
      using hsame by (by100 blast)
    have hmeet: "interior \<sigma> \<inter> interior \<tau> \<noteq> {}"
      by (rule geotop_2simplex_negative_same_side_HOL_interiors_meet_prefix
          [OF hab hc_not_ab hd_not_ab h\<sigma>V h\<tau>V hline hc_side hd_side])
    show False
      using hdisj hmeet by (by100 blast)
  qed
  have hopp: "(n \<bullet> c > r \<and> n \<bullet> d < r) \<or> (n \<bullet> c < r \<and> n \<bullet> d > r)"
  proof -
    have hc_cases: "n \<bullet> c > r \<or> n \<bullet> c < r"
      using hc_ne by (by100 linarith)
    have hd_cases: "n \<bullet> d > r \<or> n \<bullet> d < r"
      using hd_ne by (by100 linarith)
    show ?thesis
      using hc_cases hd_cases hpos_not hneg_not by (by100 blast)
  qed
  show ?thesis
    by (rule that[OF hab hc_not_ab hd_not_ab hcd he_eq h\<sigma>V h\<tau>V
          hn hline hc_ne hd_ne h\<sigma>_pos h\<sigma>_neg h\<tau>_pos h\<tau>_neg hopp])
qed

lemma geotop_edge_rel_interior_parameter_prefix:
  fixes e :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes hp: "p \<in> rel_interior e"
  obtains t where "0 < t" "t < 1" "p = (1 - t) *\<^sub>R a + t *\<^sub>R b"
  (**
    Edge-relative-interior points are exactly open-segment points, recorded in
    the affine parameter form needed for the local diamond construction. **)
proof -
  have he_HOL: "e = closed_segment a b"
    using he_eq geotop_convex_hull_eq_HOL[of "{a, b}"] segment_convex_hull[of a b]
    by (by100 simp)
  have hrel: "rel_interior e = open_segment a b"
    using he_HOL hab rel_interior_closed_segment[of a b] by (by100 simp)
  have hp_open: "p \<in> open_segment a b"
    using hp hrel by (by100 simp)
  obtain t where ht0: "0 < t" and ht1: "t < 1"
    and hp_eq: "p = (1 - t) *\<^sub>R a + t *\<^sub>R b"
    using hp_open unfolding in_segment by (by100 auto)
  show ?thesis
    by (rule that[OF ht0 ht1 hp_eq])
qed

lemma geotop_edge_rel_interior_small_subsegment_prefix:
  fixes e :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes hp: "p \<in> rel_interior e"
  obtains u where
    "0 < u"
    "p - u *\<^sub>R (b - a) \<in> rel_interior e"
    "p + u *\<^sub>R (b - a) \<in> rel_interior e"
  (**
    Edge-relative-interior points contain a small open subsegment in the edge
    direction.  This is the horizontal base of the local diamond around a
    shared-edge point. **)
proof -
  obtain t where ht0: "0 < t" and ht1: "t < 1"
    and hp_eq: "p = (1 - t) *\<^sub>R a + t *\<^sub>R b"
    by (rule geotop_edge_rel_interior_parameter_prefix[OF hab he_eq hp])
  have h1mt: "0 < 1 - t"
    using ht1 by (by100 linarith)
  obtain u where hu0: "0 < u" and hut: "u < t" and hu1mt: "u < 1 - t"
    using field_lbound_gt_zero[OF ht0 h1mt] by (by100 blast)
  have he_HOL: "e = closed_segment a b"
    using he_eq geotop_convex_hull_eq_HOL[of "{a, b}"] segment_convex_hull[of a b]
    by (by100 simp)
  have hrel: "rel_interior e = open_segment a b"
    using he_HOL hab rel_interior_closed_segment[of a b] by (by100 simp)
  have htm0: "0 < t - u"
    using hut by (by100 linarith)
  have htm1: "t - u < 1"
    using ht1 hu0 by (by100 linarith)
  have htp0: "0 < t + u"
    using ht0 hu0 by (by100 linarith)
  have htp1: "t + u < 1"
    using hu1mt by (by100 linarith)
  have hminus_eq:
    "p - u *\<^sub>R (b - a) = (1 - (t - u)) *\<^sub>R a + (t - u) *\<^sub>R b"
    using hp_eq by (simp add: algebra_simps scaleR_diff_right)
  have hplus_eq:
    "p + u *\<^sub>R (b - a) = (1 - (t + u)) *\<^sub>R a + (t + u) *\<^sub>R b"
    using hp_eq by (simp add: algebra_simps scaleR_diff_right)
  have hminus_open: "p - u *\<^sub>R (b - a) \<in> open_segment a b"
    unfolding in_segment using hab htm0 htm1 hminus_eq by (by100 blast)
  have hplus_open: "p + u *\<^sub>R (b - a) \<in> open_segment a b"
    unfolding in_segment using hab htp0 htp1 hplus_eq by (by100 blast)
  have hminus_rel: "p - u *\<^sub>R (b - a) \<in> rel_interior e"
    using hminus_open hrel by (by100 simp)
  have hplus_rel: "p + u *\<^sub>R (b - a) \<in> rel_interior e"
    using hplus_open hrel by (by100 simp)
  show ?thesis
    by (rule that[OF hu0 hminus_rel hplus_rel])
qed

lemma geotop_real_positive_edge_probe_parameter_prefix:
  fixes u v x y z :: real
  assumes hu: "0 < u"
  assumes hv: "0 < v"
  assumes hz: "0 < z"
  obtains s where
    "0 < s"
    "s < 1"
    "0 < (1 - s) * u + s * x"
    "0 < (1 - s) * v + s * y"
    "0 < s * z"
  (**
    Real parameter choice for a small probe from an edge-interior point into a
    triangle: preserve the two positive edge barycentric coordinates while
    turning on a positive opposite-vertex coordinate. **)
proof -
  define bx where "bx = (if x < u then u / (u - x) else 1)"
  define byy where "byy = (if y < v then v / (v - y) else 1)"
  have hbx_pos: "0 < bx"
  proof (cases "x < u")
    case True
    have "0 < u - x"
      using True by (by100 linarith)
    hence "0 < u / (u - x)"
      using hu by (simp add: divide_pos_pos)
    thus ?thesis
      using True bx_def by (by100 simp)
  next
    case False
    show ?thesis
      using False bx_def by (by100 simp)
  qed
  have hby_pos: "0 < byy"
  proof (cases "y < v")
    case True
    have "0 < v - y"
      using True by (by100 linarith)
    hence "0 < v / (v - y)"
      using hv by (simp add: divide_pos_pos)
    thus ?thesis
      using True byy_def by (by100 simp)
  next
    case False
    show ?thesis
      using False byy_def by (by100 simp)
  qed
  obtain t where ht0: "0 < t" and htbx: "t < bx" and ht1: "t < 1"
    using field_lbound_gt_zero[OF hbx_pos zero_less_one] by (by100 blast)
  obtain s where hs0: "0 < s" and hst: "s < t" and hsby: "s < byy"
    using field_lbound_gt_zero[OF ht0 hby_pos] by (by100 blast)
  have hs1: "s < 1"
    using hst ht1 by (by100 linarith)
  have hsbx: "s < bx"
    using hst htbx by (by100 linarith)
  have hxpos: "0 < (1 - s) * u + s * x"
  proof (cases "x < u")
    case True
    have hden: "0 < u - x"
      using True by (by100 linarith)
    have hsbound: "s < u / (u - x)"
      using hsbx True bx_def by (by100 simp)
    have "s * (u - x) < u"
      using hsbound hden by (simp add: field_simps)
    hence "0 < u - s * (u - x)"
      by (by100 linarith)
    also have "u - s * (u - x) = (1 - s) * u + s * x"
      by (simp add: field_simps algebra_simps)
    finally show ?thesis .
  next
    case False
    have hnonneg: "0 \<le> x - u"
      using False by (by100 linarith)
    have hs_nonneg: "0 \<le> s"
      using hs0 by (by100 linarith)
    have "0 \<le> s * (x - u)"
      by (rule mult_nonneg_nonneg[OF hs_nonneg hnonneg])
    moreover have "(1 - s) * u + s * x = u + s * (x - u)"
      by (simp add: field_simps algebra_simps)
    ultimately show ?thesis
      using hu by (by100 linarith)
  qed
  have hypos: "0 < (1 - s) * v + s * y"
  proof (cases "y < v")
    case True
    have hden: "0 < v - y"
      using True by (by100 linarith)
    have hsbound: "s < v / (v - y)"
      using hsby True byy_def by (by100 simp)
    have "s * (v - y) < v"
      using hsbound hden by (simp add: field_simps)
    hence "0 < v - s * (v - y)"
      by (by100 linarith)
    also have "v - s * (v - y) = (1 - s) * v + s * y"
      by (simp add: field_simps algebra_simps)
    finally show ?thesis .
  next
    case False
    have hnonneg: "0 \<le> y - v"
      using False by (by100 linarith)
    have hs_nonneg: "0 \<le> s"
      using hs0 by (by100 linarith)
    have "0 \<le> s * (y - v)"
      by (rule mult_nonneg_nonneg[OF hs_nonneg hnonneg])
    moreover have "(1 - s) * v + s * y = v + s * (y - v)"
      by (simp add: field_simps algebra_simps)
    ultimately show ?thesis
      using hv by (by100 linarith)
  qed
  have hsz: "0 < s * z"
    by (rule mult_pos_pos[OF hs0 hz])
  show ?thesis
    by (rule that[OF hs0 hs1 hxpos hypos hsz])
qed

lemma geotop_2simplex_positive_side_edge_normal_probe_in_HOL_interior_prefix:
  fixes e \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes hn: "n \<noteq> 0"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c > r"
  assumes hp: "p \<in> rel_interior e"
  obtains s where "0 < s" "p + s *\<^sub>R n \<in> interior \<sigma>"
  (**
    Normal-probe half of the book's two-triangle edge-neighborhood
    construction: from an edge-interior point, a small move into the strict side
    of the opposite vertex lands in the triangle interior. **)
proof -
  obtain t where ht0: "0 < t" and ht1: "t < 1"
    and hp_eq: "p = (1 - t) *\<^sub>R a + t *\<^sub>R b"
    by (rule geotop_edge_rel_interior_parameter_prefix[OF hab he_eq hp])
  have ha_aff: "a \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have hb_aff: "b \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have ha_line: "n \<bullet> a = r"
    using hline ha_aff by (by100 simp)
  have hb_line: "n \<bullet> b = r"
    using hline hb_aff by (by100 simp)
  have hp_line: "n \<bullet> p = r"
  proof -
    have "n \<bullet> p = n \<bullet> ((1 - t) *\<^sub>R a + t *\<^sub>R b)"
      using hp_eq by (by100 simp)
    also have "\<dots> = (1 - t) * (n \<bullet> a) + t * (n \<bullet> b)"
      by (simp add: inner_add_right inner_scaleR_right)
    also have "\<dots> = (1 - t) * r + t * r"
      using ha_line hb_line by (by100 simp)
    also have "\<dots> = r"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have hnn_pos: "0 < n \<bullet> n"
    using hn by (simp add: inner_gt_zero_iff)
  define q where "q = p + n"
  have hq_side: "n \<bullet> q > r"
  proof -
    have "n \<bullet> q = n \<bullet> (p + n)"
      using q_def by (by100 simp)
    also have "\<dots> = n \<bullet> p + n \<bullet> n"
      by (simp add: inner_add_right)
    also have "\<dots> = r + n \<bullet> n"
      using hp_line by (by100 simp)
    finally show ?thesis
      using hnn_pos by (by100 linarith)
  qed
  obtain x y z where hsum: "x + y + z = 1"
    and hq_eq: "q = x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c"
    and hz: "0 < z"
    using geotop_2simplex_positive_side_affine_coordinate_positive_prefix
      [OF hab hc_not_ab h\<sigma>V hline hc_side hq_side]
    by (by100 blast)
  have hu: "0 < 1 - t"
    using ht1 by (by100 linarith)
  have hv: "0 < t"
    using ht0 .
  obtain s where hs0: "0 < s" and hs1: "s < 1"
    and hxpos: "0 < (1 - s) * (1 - t) + s * x"
    and hypos: "0 < (1 - s) * t + s * y"
    and hzpos: "0 < s * z"
    using geotop_real_positive_edge_probe_parameter_prefix[OF hu hv hz]
    by (by100 blast)
  have hsum_probe:
    "((1 - s) * (1 - t) + s * x) + ((1 - s) * t + s * y) + s * z = 1"
  proof -
    have "((1 - s) * (1 - t) + s * x) + ((1 - s) * t + s * y) + s * z =
        (1 - s) + s * (x + y + z)"
      by (simp add: algebra_simps)
    also have "\<dots> = 1"
      using hsum by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have hprobe_eq:
    "p + s *\<^sub>R n =
      ((1 - s) * (1 - t) + s * x) *\<^sub>R a
        + ((1 - s) * t + s * y) *\<^sub>R b
        + (s * z) *\<^sub>R c"
  proof -
    have "p + s *\<^sub>R n = (1 - s) *\<^sub>R p + s *\<^sub>R q"
      using q_def by (simp add: algebra_simps)
    also have "\<dots> =
      (1 - s) *\<^sub>R ((1 - t) *\<^sub>R a + t *\<^sub>R b)
        + s *\<^sub>R (x *\<^sub>R a + y *\<^sub>R b + z *\<^sub>R c)"
      using hp_eq hq_eq by (by100 simp)
    also have "\<dots> =
      ((1 - s) * (1 - t) + s * x) *\<^sub>R a
        + ((1 - s) * t + s * y) *\<^sub>R b
        + (s * z) *\<^sub>R c"
      by (simp add: algebra_simps scaleR_add_left scaleR_add_right)
    finally show ?thesis .
  qed
  have hprobe_in: "p + s *\<^sub>R n \<in> interior \<sigma>"
    by (rule geotop_2simplex_positive_bary_in_HOL_interior_prefix
        [OF hab hc_not_ab h\<sigma>V hxpos hypos hzpos hsum_probe hprobe_eq])
  show ?thesis
    by (rule that[OF hs0 hprobe_in])
qed

lemma geotop_2simplex_negative_side_edge_normal_probe_in_HOL_interior_prefix:
  fixes e \<sigma> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes hn: "n \<noteq> 0"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hc_side: "n \<bullet> c < r"
  assumes hp: "p \<in> rel_interior e"
  obtains s where "0 < s" "p - s *\<^sub>R n \<in> interior \<sigma>"
  (**
    Negative-side version of the normal probe, phrased with the original normal
    direction for use in the opposite-side shared-edge local model. **)
proof -
  have hn_neg: "-n \<noteq> 0"
    using hn by (by100 simp)
  have hline_neg: "affine hull {a, b} = {x. (-n) \<bullet> x = -r}"
    using hline by (simp add: set_eq_iff)
  have hc_pos: "(-n) \<bullet> c > -r"
    using hc_side by (by100 simp)
  obtain s where hs0: "0 < s"
    and hs_in: "p + s *\<^sub>R (-n) \<in> interior \<sigma>"
    by (rule geotop_2simplex_positive_side_edge_normal_probe_in_HOL_interior_prefix
        [OF hab hc_not_ab hn_neg he_eq h\<sigma>V hline_neg hc_pos hp])
  have hprobe: "p - s *\<^sub>R n \<in> interior \<sigma>"
    using hs_in by (by100 simp)
  show ?thesis
    by (rule that[OF hs0 hprobe])
qed

lemma geotop_2simplex_opposite_side_shared_edge_normal_probes_in_HOL_interiors_prefix:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes hd_not_ab: "d \<notin> {a, b}"
  assumes hn: "n \<noteq> 0"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hopp: "(n \<bullet> c > r \<and> n \<bullet> d < r) \<or> (n \<bullet> c < r \<and> n \<bullet> d > r)"
  assumes hp: "p \<in> rel_interior e"
  obtains s t where
    "0 < s"
    "0 < t"
    "(p + s *\<^sub>R n \<in> interior \<sigma> \<and> p - t *\<^sub>R n \<in> interior \<tau>)
      \<or> (p - s *\<^sub>R n \<in> interior \<sigma> \<and> p + t *\<^sub>R n \<in> interior \<tau>)"
  (**
    Opposite-side normal probes at an edge-interior point: according to the
    orientation of the two opposite vertices, the two incident triangle
    interiors meet the two normal rays from the edge point. **)
proof -
  consider (posneg) "n \<bullet> c > r" "n \<bullet> d < r"
    | (negpos) "n \<bullet> c < r" "n \<bullet> d > r"
    using hopp by (by100 blast)
  thus ?thesis
  proof cases
    case posneg
    obtain s where hs0: "0 < s"
      and hs_in: "p + s *\<^sub>R n \<in> interior \<sigma>"
      by (rule geotop_2simplex_positive_side_edge_normal_probe_in_HOL_interior_prefix
          [OF hab hc_not_ab hn he_eq h\<sigma>V hline posneg(1) hp])
    obtain t where ht0: "0 < t"
      and ht_in: "p - t *\<^sub>R n \<in> interior \<tau>"
      by (rule geotop_2simplex_negative_side_edge_normal_probe_in_HOL_interior_prefix
          [OF hab hd_not_ab hn he_eq h\<tau>V hline posneg(2) hp])
    show ?thesis
    proof (rule that[OF hs0 ht0])
      show "(p + s *\<^sub>R n \<in> interior \<sigma> \<and> p - t *\<^sub>R n \<in> interior \<tau>)
          \<or> (p - s *\<^sub>R n \<in> interior \<sigma> \<and> p + t *\<^sub>R n \<in> interior \<tau>)"
        using hs_in ht_in by (by100 blast)
    qed
  next
    case negpos
    obtain s where hs0: "0 < s"
      and hs_in: "p - s *\<^sub>R n \<in> interior \<sigma>"
      by (rule geotop_2simplex_negative_side_edge_normal_probe_in_HOL_interior_prefix
          [OF hab hc_not_ab hn he_eq h\<sigma>V hline negpos(1) hp])
    obtain t where ht0: "0 < t"
      and ht_in: "p + t *\<^sub>R n \<in> interior \<tau>"
      by (rule geotop_2simplex_positive_side_edge_normal_probe_in_HOL_interior_prefix
          [OF hab hd_not_ab hn he_eq h\<tau>V hline negpos(2) hp])
    show ?thesis
    proof (rule that[OF hs0 ht0])
      show "(p + s *\<^sub>R n \<in> interior \<sigma> \<and> p - t *\<^sub>R n \<in> interior \<tau>)
          \<or> (p - s *\<^sub>R n \<in> interior \<sigma> \<and> p + t *\<^sub>R n \<in> interior \<tau>)"
        using hs_in ht_in by (by100 blast)
    qed
  qed
qed

lemma geotop_edge_subset_2simplex_vertices_prefix:
  fixes e \<sigma> :: "(real^2) set"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  shows "e \<subseteq> \<sigma>"
  (**
    Vertex-form containment used in the local diamond argument: the edge
    spanned by two triangle vertices is contained in the triangle. **)
proof -
  have he_HOL: "e = convex hull {a, b}"
    using he_eq geotop_convex_hull_eq_HOL[of "{a, b}"] by (by100 simp)
  have h\<sigma>_geo: "\<sigma> = geotop_convex_hull {a, b, c}"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have h\<sigma>_HOL: "\<sigma> = convex hull {a, b, c}"
    using h\<sigma>_geo geotop_convex_hull_eq_HOL[of "{a, b, c}"] by (by100 simp)
  have hsub: "{a, b} \<subseteq> {a, b, c}"
    by (by100 blast)
  have "convex hull {a, b} \<subseteq> convex hull {a, b, c}"
    by (rule hull_mono[OF hsub])
  thus ?thesis
    using he_HOL h\<sigma>_HOL by (by100 simp)
qed

lemma geotop_shared_edge_rel_interior_subset_two_2simplexes_prefix:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
  shows "rel_interior e \<subseteq> \<sigma> \<inter> \<tau>"
  (**
    The common edge's relative interior is contained in both incident triangles,
    a direct set-level input for the local diamond neighborhood argument. **)
proof
  fix p
  assume hp: "p \<in> rel_interior e"
  have hp_e: "p \<in> e"
    using hp rel_interior_subset by (by100 blast)
  have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
    by (rule geotop_edge_subset_2simplex_vertices_prefix[OF he_eq h\<sigma>V])
  have he_sub_\<tau>: "e \<subseteq> \<tau>"
    by (rule geotop_edge_subset_2simplex_vertices_prefix[OF he_eq h\<tau>V])
  show "p \<in> \<sigma> \<inter> \<tau>"
    using hp_e he_sub_\<sigma> he_sub_\<tau> by (by100 blast)
qed

lemma geotop_shared_edge_small_subsegment_in_two_2simplexes_prefix:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
  assumes hp: "p \<in> rel_interior e"
  obtains u where
    "0 < u"
    "p - u *\<^sub>R (b - a) \<in> \<sigma> \<inter> \<tau>"
    "p + u *\<^sub>R (b - a) \<in> \<sigma> \<inter> \<tau>"
  (**
    Horizontal base of the local diamond in the two incident triangles: a
    sufficiently small edge-direction subsegment around \<open>p\<close> remains in both
    closed triangles. **)
proof -
  obtain u where hu0: "0 < u"
    and hminus_rel: "p - u *\<^sub>R (b - a) \<in> rel_interior e"
    and hplus_rel: "p + u *\<^sub>R (b - a) \<in> rel_interior e"
    by (rule geotop_edge_rel_interior_small_subsegment_prefix[OF hab he_eq hp])
  have hrel_sub: "rel_interior e \<subseteq> \<sigma> \<inter> \<tau>"
    by (rule geotop_shared_edge_rel_interior_subset_two_2simplexes_prefix
        [OF he_eq h\<sigma>V h\<tau>V])
  have hminus: "p - u *\<^sub>R (b - a) \<in> \<sigma> \<inter> \<tau>"
    using hminus_rel hrel_sub by (by100 blast)
  have hplus: "p + u *\<^sub>R (b - a) \<in> \<sigma> \<inter> \<tau>"
    using hplus_rel hrel_sub by (by100 blast)
  show ?thesis
    by (rule that[OF hu0 hminus hplus])
qed

lemma geotop_convex_hull_three_points_subset_2simplex_prefix:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hx: "x \<in> \<sigma>"
  assumes hy: "y \<in> \<sigma>"
  assumes hz: "z \<in> \<sigma>"
  shows "convex hull {x, y, z} \<subseteq> \<sigma>"
  (**
    Convexity wrapper for the local diamond construction: any small triangle
    whose vertices lie in a simplex is contained in that simplex. **)
proof -
  have h\<sigma>_geo: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have h\<sigma>_HOL: "\<sigma> = convex hull V"
    using h\<sigma>_geo geotop_convex_hull_eq_HOL[of V] by (by100 simp)
  have hconv: "convex \<sigma>"
    using h\<sigma>_HOL by (by100 simp)
  have hpts: "{x, y, z} \<subseteq> \<sigma>"
    using hx hy hz by (by100 blast)
  have "convex hull {x, y, z} \<subseteq> \<sigma>"
    by (rule hull_minimal[where S=convex, OF hpts hconv])
  thus ?thesis
    by (by100 simp)
qed

lemma geotop_shared_edge_probe_triangles_subset_union_prefix:
  fixes \<sigma> \<tau> :: "(real^2) set"
  fixes q1 q2 qtop qbot :: "real^2"
  fixes V\<sigma> V\<tau> :: "(real^2) set"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V\<sigma>"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> V\<tau>"
  assumes hq1: "q1 \<in> \<sigma> \<inter> \<tau>"
  assumes hq2: "q2 \<in> \<sigma> \<inter> \<tau>"
  assumes htop: "qtop \<in> interior \<sigma>"
  assumes hbot: "qbot \<in> interior \<tau>"
  shows "convex hull {q1, q2, qtop} \<union> convex hull {q1, q2, qbot} \<subseteq> \<sigma> \<union> \<tau>"
  (**
    Set-containment package for the local diamond: the upper small triangle
    lies in the first incident 2-simplex and the lower small triangle lies in
    the second. **)
proof -
  have hqtop_\<sigma>: "qtop \<in> \<sigma>"
    using htop interior_subset by (by100 blast)
  have hqbot_\<tau>: "qbot \<in> \<tau>"
    using hbot interior_subset by (by100 blast)
  have hq1_\<sigma>: "q1 \<in> \<sigma>" and hq2_\<sigma>: "q2 \<in> \<sigma>"
    using hq1 hq2 by (by100 blast)+
  have hq1_\<tau>: "q1 \<in> \<tau>" and hq2_\<tau>: "q2 \<in> \<tau>"
    using hq1 hq2 by (by100 blast)+
  have htop_sub: "convex hull {q1, q2, qtop} \<subseteq> \<sigma>"
    by (rule geotop_convex_hull_three_points_subset_2simplex_prefix
        [OF h\<sigma>V hq1_\<sigma> hq2_\<sigma> hqtop_\<sigma>])
  have hbot_sub: "convex hull {q1, q2, qbot} \<subseteq> \<tau>"
    by (rule geotop_convex_hull_three_points_subset_2simplex_prefix
        [OF h\<tau>V hq1_\<tau> hq2_\<tau> hqbot_\<tau>])
  show ?thesis
    using htop_sub hbot_sub by (by100 blast)
qed

lemma geotop_shared_edge_probe_diamond_contains_ball_prefix:
  fixes p v n :: "real^2"
  assumes hv: "v \<noteq> 0"
  assumes hn: "n \<noteq> 0"
  assumes horth: "v \<bullet> n = 0"
  assumes hu: "0 < u"
  assumes hs: "0 < s"
  assumes ht: "0 < t"
  obtains eps where
    "0 < eps"
    "ball p eps \<subseteq>
      convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p + s *\<^sub>R n}
        \<union> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p - t *\<^sub>R n}"
  (**
    Analytic diamond step in Moise's shared-edge local model: the two small
    triangles with common base in the edge direction and apices on opposite
    normal rays contain a genuine Euclidean ball around the edge point. **)
proof -
  have hspan: "span {v, n} = UNIV"
  proof -
    have hvn_distinct: "v \<noteq> n"
    proof
      assume hvn: "v = n"
      have "v \<bullet> v = 0"
        using horth hvn by (by100 simp)
      thus False
        using hv by (simp add: inner_eq_zero_iff)
    qed
    have hpair: "pairwise orthogonal {v, n}"
      using horth by (simp add: pairwise_def orthogonal_def inner_commute)
    have hzero: "0 \<notin> {v, n}"
      using hv hn by (by100 simp)
    have hind: "independent {v, n}"
      by (rule pairwise_orthogonal_independent[OF hpair hzero])
    have hcard: "card {v, n} = DIM(real^2)"
      using hvn_distinct by (by100 simp)
    have hdim: "dim {v, n} = DIM(real^2)"
      using indep_card_eq_dim_span[OF hind] hcard by (by100 simp)
    show ?thesis
      using hdim dim_eq_full[of "{v, n}"] by (by100 simp)
  qed
  have hcoords:
    "\<forall>x. \<exists>\<alpha> \<beta>. x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
  proof
    fix x
    have hxspan: "x - p \<in> span (insert v {n})"
      using hspan by (by100 simp)
    obtain \<alpha> where h\<alpha>: "x - p - \<alpha> *\<^sub>R v \<in> span {n}"
      using hxspan unfolding span_breakdown_eq by (by100 blast)
    obtain \<beta> where h\<beta>: "x - p - \<alpha> *\<^sub>R v - \<beta> *\<^sub>R n \<in> span ({} :: (real^2) set)"
      using h\<alpha> unfolding span_breakdown_eq by (by100 blast)
    have hzero: "x - p - \<alpha> *\<^sub>R v - \<beta> *\<^sub>R n = 0"
      using h\<beta> by (by100 simp)
    show "\<exists>\<alpha> \<beta>. x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
    proof (intro exI)
      show "x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
        using hzero by (simp add: algebra_simps)
    qed
  qed
  have hsmall_coords:
    "\<exists>eps>0. \<forall>x\<in>ball p eps.
      \<exists>\<alpha> \<beta>. x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
        \<and> \<bar>\<alpha>\<bar> < u / 2
        \<and> \<bar>\<beta>\<bar> < min s t / 2"
  proof -
    have hvn: "0 < norm v"
      using hv by (by100 simp)
    have hnn: "0 < norm n"
      using hn by (by100 simp)
    have hm: "0 < min s t"
      using hs ht by (by100 simp)
    define eps where "eps = min (u * norm v / 4) (min s t * norm n / 4)"
    have heps: "0 < eps"
      using hu hvn hm hnn unfolding eps_def by (by100 simp)
    have heps_v: "eps \<le> u * norm v / 4"
      unfolding eps_def by (by100 simp)
    have heps_n: "eps \<le> min s t * norm n / 4"
      unfolding eps_def by (by100 simp)
    have hvn_nonneg: "0 \<le> norm v"
      using hvn by (by100 linarith)
    have hnn_nonneg: "0 \<le> norm n"
      using hnn by (by100 linarith)
    have hbound:
      "\<forall>x\<in>ball p eps.
        \<exists>\<alpha> \<beta>. x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
          \<and> \<bar>\<alpha>\<bar> < u / 2
          \<and> \<bar>\<beta>\<bar> < min s t / 2"
    proof
      fix x
      assume hx: "x \<in> ball p eps"
      obtain \<alpha> \<beta> where hxrep: "x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
        using hcoords by (by100 blast)
      let ?y = "x - p"
      have hyrep: "?y = \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
        using hxrep by (simp add: algebra_simps)
      have hy_norm: "norm ?y < eps"
        using hx by (simp add: dist_norm norm_minus_commute)
      have hv_inner_pos: "0 < v \<bullet> v"
        using hv by (simp add: inner_gt_zero_iff)
      have hn_inner_pos: "0 < n \<bullet> n"
        using hn by (simp add: inner_gt_zero_iff)
      have hv_inner_nonneg: "0 \<le> v \<bullet> v"
        using hv_inner_pos by (by100 linarith)
      have hn_inner_nonneg: "0 \<le> n \<bullet> n"
        using hn_inner_pos by (by100 linarith)
      have hv_inner_norm: "v \<bullet> v = norm v * norm v"
        by (simp add: dot_square_norm power2_eq_square)
      have hn_inner_norm: "n \<bullet> n = norm n * norm n"
        by (simp add: dot_square_norm power2_eq_square)
      have hnv: "n \<bullet> v = 0"
        by (subst inner_commute) (rule horth)
      have hdot_v: "?y \<bullet> v = \<alpha> * (v \<bullet> v)"
      proof -
        have "?y \<bullet> v = (\<alpha> *\<^sub>R v + \<beta> *\<^sub>R n) \<bullet> v"
          using hyrep by (by100 simp)
        also have "\<dots> = \<alpha> * (v \<bullet> v) + \<beta> * (n \<bullet> v)"
          by (simp add: inner_add_left inner_scaleR_left)
        also have "\<dots> = \<alpha> * (v \<bullet> v)"
          using hnv by (by100 simp)
        finally show ?thesis .
      qed
      have halpha_eq: "\<alpha> = (?y \<bullet> v) / (v \<bullet> v)"
        using hdot_v hv_inner_pos by (simp add: field_simps)
      have hdot_n: "?y \<bullet> n = \<beta> * (n \<bullet> n)"
      proof -
        have "?y \<bullet> n = (\<alpha> *\<^sub>R v + \<beta> *\<^sub>R n) \<bullet> n"
          using hyrep by (by100 simp)
        also have "\<dots> = \<alpha> * (v \<bullet> n) + \<beta> * (n \<bullet> n)"
          by (simp add: inner_add_left inner_scaleR_left)
        also have "\<dots> = \<beta> * (n \<bullet> n)"
          using horth by (by100 simp)
        finally show ?thesis .
      qed
      have hbeta_eq: "\<beta> = (?y \<bullet> n) / (n \<bullet> n)"
        using hdot_n hn_inner_pos by (simp add: field_simps)
      have halpha_abs_le: "\<bar>\<alpha>\<bar> \<le> norm ?y / norm v"
      proof -
        have hcs: "\<bar>?y \<bullet> v\<bar> \<le> norm ?y * norm v"
          by (rule Cauchy_Schwarz_ineq2)
        have "\<bar>\<alpha>\<bar> = \<bar>?y \<bullet> v\<bar> / (v \<bullet> v)"
          using halpha_eq hv_inner_pos by (by100 simp)
        also have "\<dots> \<le> (norm ?y * norm v) / (v \<bullet> v)"
          by (rule divide_right_mono[OF hcs hv_inner_nonneg])
        also have "\<dots> = norm ?y / norm v"
          using hvn hv_inner_norm by (simp add: field_simps)
        finally show ?thesis .
      qed
      have hbeta_abs_le: "\<bar>\<beta>\<bar> \<le> norm ?y / norm n"
      proof -
        have hcs: "\<bar>?y \<bullet> n\<bar> \<le> norm ?y * norm n"
          by (rule Cauchy_Schwarz_ineq2)
        have "\<bar>\<beta>\<bar> = \<bar>?y \<bullet> n\<bar> / (n \<bullet> n)"
          using hbeta_eq hn_inner_pos by (by100 simp)
        also have "\<dots> \<le> (norm ?y * norm n) / (n \<bullet> n)"
          by (rule divide_right_mono[OF hcs hn_inner_nonneg])
        also have "\<dots> = norm ?y / norm n"
          using hnn hn_inner_norm by (simp add: field_simps)
        finally show ?thesis .
      qed
      have halpha_lt: "\<bar>\<alpha>\<bar> < u / 2"
      proof -
        have "norm ?y / norm v < eps / norm v"
          by (rule divide_strict_right_mono[OF hy_norm hvn])
        also have "\<dots> \<le> (u * norm v / 4) / norm v"
          by (rule divide_right_mono[OF heps_v hvn_nonneg])
        also have "\<dots> = u / 4"
          using hvn by (simp add: field_simps)
        also have "\<dots> < u / 2"
          using hu by (by100 linarith)
        finally show ?thesis
          using halpha_abs_le by (by100 linarith)
      qed
      have hbeta_lt: "\<bar>\<beta>\<bar> < min s t / 2"
      proof -
        have "norm ?y / norm n < eps / norm n"
          by (rule divide_strict_right_mono[OF hy_norm hnn])
        also have "\<dots> \<le> (min s t * norm n / 4) / norm n"
          by (rule divide_right_mono[OF heps_n hnn_nonneg])
        also have "\<dots> = min s t / 4"
          using hnn by (simp add: field_simps)
        also have "\<dots> < min s t / 2"
          using hm by (by100 linarith)
        finally show ?thesis
          using hbeta_abs_le by (by100 linarith)
      qed
      show "\<exists>\<alpha> \<beta>. x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
          \<and> \<bar>\<alpha>\<bar> < u / 2
          \<and> \<bar>\<beta>\<bar> < min s t / 2"
        using hxrep halpha_lt hbeta_lt by (by100 blast)
    qed
    show ?thesis
      using heps hbound by (by100 blast)
  qed
  have hupper_membership:
    "\<forall>\<alpha> \<beta>. \<bar>\<alpha>\<bar> < u / 2 \<and> 0 \<le> \<beta> \<and> \<beta> < s / 2 \<longrightarrow>
      p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
        \<in> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p + s *\<^sub>R n}"
  proof (intro allI impI)
    fix \<alpha> \<beta>
    assume h: "\<bar>\<alpha>\<bar> < u / 2 \<and> 0 \<le> \<beta> \<and> \<beta> < s / 2"
    define \<mu> where "\<mu> = \<beta> / s"
    define ell where "ell = ((\<alpha> / u) + 1 - \<mu>) / 2"
    have h\<mu>0: "0 \<le> \<mu>"
      using h hs unfolding \<mu>_def by (by100 simp)
    have h\<mu>half: "\<mu> < 1 / 2"
      using h hs unfolding \<mu>_def by (simp add: field_simps)
    have h\<alpha>abs: "\<bar>\<alpha>\<bar> < u / 2"
      using h by (by100 blast)
    have h\<alpha>gt: "- (u / 2) < \<alpha>"
    proof -
      have "- \<alpha> \<le> \<bar>\<alpha>\<bar>"
        by (by100 simp)
      thus ?thesis
        using h\<alpha>abs by (by100 linarith)
    qed
    have h\<alpha>lt: "\<alpha> < u / 2"
    proof -
      have "\<alpha> \<le> \<bar>\<alpha>\<bar>"
        by (by100 simp)
      thus ?thesis
        using h\<alpha>abs by (by100 linarith)
    qed
    have h\<alpha>u_gt: "- (1 / 2) < \<alpha> / u"
      using h\<alpha>gt hu by (simp add: field_simps)
    have h\<alpha>u_lt: "\<alpha> / u < 1 / 2"
      using h\<alpha>lt hu by (simp add: field_simps)
    have hell_num_pos: "0 < \<alpha> / u + 1 - \<mu>"
    proof -
      have "- (1 / 2) + 1 - (1 / 2) < \<alpha> / u + 1 - \<mu>"
        using h\<alpha>u_gt h\<mu>half by linarith
      thus ?thesis
        by (by100 simp)
    qed
    have hell0_strict: "0 < ell"
      using hell_num_pos unfolding ell_def by (by100 simp)
    have hell0: "0 \<le> ell"
      using hell0_strict by (by100 linarith)
    have hell\<mu>_num_lt: "\<alpha> / u + 1 + \<mu> < 2"
    proof -
      have "\<alpha> / u + 1 + \<mu> < (1 / 2) + 1 + (1 / 2)"
        using h\<alpha>u_lt h\<mu>half by linarith
      thus ?thesis
        by (by100 simp)
    qed
    have hell\<mu>_expr: "ell + \<mu> = (\<alpha> / u + 1 + \<mu>) / 2"
      unfolding ell_def by (simp add: field_simps)
    have hell\<mu>_strict: "ell + \<mu> < 1"
      using hell\<mu>_expr hell\<mu>_num_lt by (by100 simp)
    have hell\<mu>: "ell + \<mu> \<le> 1"
      using hell\<mu>_strict by (by100 linarith)
    have h\<mu>s: "\<mu> * s = \<beta>"
      using hs unfolding \<mu>_def by (by100 simp)
    have hv_coeff: "- u + 2 * u * ell + u * \<mu> = \<alpha>"
      using hu hs unfolding ell_def \<mu>_def by (simp add: field_simps)
    have heq:
      "p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n =
        (p - u *\<^sub>R v)
          + ell *\<^sub>R ((p + u *\<^sub>R v) - (p - u *\<^sub>R v))
          + \<mu> *\<^sub>R ((p + s *\<^sub>R n) - (p - u *\<^sub>R v))"
    proof -
      have hbase_diff:
        "(p + u *\<^sub>R v) - (p - u *\<^sub>R v) = (2 * u) *\<^sub>R v"
        by (simp add: vec_eq_iff algebra_simps)
      have hapex_diff:
        "(p + s *\<^sub>R n) - (p - u *\<^sub>R v) = u *\<^sub>R v + s *\<^sub>R n"
        by (simp add: vec_eq_iff algebra_simps)
      have "(p - u *\<^sub>R v)
          + ell *\<^sub>R ((p + u *\<^sub>R v) - (p - u *\<^sub>R v))
          + \<mu> *\<^sub>R ((p + s *\<^sub>R n) - (p - u *\<^sub>R v))
        = p + (- u + 2 * u * ell + u * \<mu>) *\<^sub>R v + (\<mu> * s) *\<^sub>R n"
        using hbase_diff hapex_diff
        by (simp add: algebra_simps scaleR_add_right)
      also have "\<dots> = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
        using h\<mu>s hv_coeff by (by100 simp)
      finally show ?thesis
        by (by100 simp)
    qed
    have "p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n \<in>
      {p - u *\<^sub>R v
        + ell *\<^sub>R ((p + u *\<^sub>R v) - (p - u *\<^sub>R v))
        + \<mu> *\<^sub>R ((p + s *\<^sub>R n) - (p - u *\<^sub>R v))
        | ell \<mu>. 0 \<le> ell \<and> 0 \<le> \<mu> \<and> ell + \<mu> \<le> 1}"
      using heq hell0 h\<mu>0 hell\<mu> by (by100 blast)
    thus "p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
        \<in> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p + s *\<^sub>R n}"
      using convex_hull_3_alt
        [of "p - u *\<^sub>R v" "p + u *\<^sub>R v" "p + s *\<^sub>R n"]
      by (by100 simp)
  qed
  have hlower_membership:
    "\<forall>\<alpha> \<beta>. \<bar>\<alpha>\<bar> < u / 2 \<and> - (t / 2) < \<beta> \<and> \<beta> < 0 \<longrightarrow>
      p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
        \<in> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p - t *\<^sub>R n}"
  proof (intro allI impI)
    fix \<alpha> \<beta>
    assume h: "\<bar>\<alpha>\<bar> < u / 2 \<and> - (t / 2) < \<beta> \<and> \<beta> < 0"
    define \<mu> where "\<mu> = - \<beta> / t"
    define ell where "ell = ((\<alpha> / u) + 1 - \<mu>) / 2"
    have h\<beta>neg: "\<beta> < 0"
      using h by (by100 blast)
    have hneg\<beta>_lt: "- \<beta> < t / 2"
      using h by (by100 linarith)
    have h\<mu>0: "0 \<le> \<mu>"
      using h\<beta>neg ht unfolding \<mu>_def by (simp add: field_simps)
    have h\<mu>half: "\<mu> < 1 / 2"
      using hneg\<beta>_lt ht unfolding \<mu>_def by (simp add: field_simps)
    have h\<alpha>abs: "\<bar>\<alpha>\<bar> < u / 2"
      using h by (by100 blast)
    have h\<alpha>gt: "- (u / 2) < \<alpha>"
    proof -
      have "- \<alpha> \<le> \<bar>\<alpha>\<bar>"
        by (by100 simp)
      thus ?thesis
        using h\<alpha>abs by (by100 linarith)
    qed
    have h\<alpha>lt: "\<alpha> < u / 2"
    proof -
      have "\<alpha> \<le> \<bar>\<alpha>\<bar>"
        by (by100 simp)
      thus ?thesis
        using h\<alpha>abs by (by100 linarith)
    qed
    have h\<alpha>u_gt: "- (1 / 2) < \<alpha> / u"
      using h\<alpha>gt hu by (simp add: field_simps)
    have h\<alpha>u_lt: "\<alpha> / u < 1 / 2"
      using h\<alpha>lt hu by (simp add: field_simps)
    have hell_num_pos: "0 < \<alpha> / u + 1 - \<mu>"
    proof -
      have "- (1 / 2) + 1 - (1 / 2) < \<alpha> / u + 1 - \<mu>"
        using h\<alpha>u_gt h\<mu>half by linarith
      thus ?thesis
        by (by100 simp)
    qed
    have hell0_strict: "0 < ell"
      using hell_num_pos unfolding ell_def by (by100 simp)
    have hell0: "0 \<le> ell"
      using hell0_strict by (by100 linarith)
    have hell\<mu>_num_lt: "\<alpha> / u + 1 + \<mu> < 2"
    proof -
      have "\<alpha> / u + 1 + \<mu> < (1 / 2) + 1 + (1 / 2)"
        using h\<alpha>u_lt h\<mu>half by linarith
      thus ?thesis
        by (by100 simp)
    qed
    have hell\<mu>_expr: "ell + \<mu> = (\<alpha> / u + 1 + \<mu>) / 2"
      unfolding ell_def by (simp add: field_simps)
    have hell\<mu>_strict: "ell + \<mu> < 1"
      using hell\<mu>_expr hell\<mu>_num_lt by (by100 simp)
    have hell\<mu>: "ell + \<mu> \<le> 1"
      using hell\<mu>_strict by (by100 linarith)
    have h\<mu>t: "- (\<mu> * t) = \<beta>"
      using ht unfolding \<mu>_def by (by100 simp)
    have hv_coeff: "- u + 2 * u * ell + u * \<mu> = \<alpha>"
      using hu ht unfolding ell_def \<mu>_def by (simp add: field_simps)
    have heq:
      "p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n =
        (p - u *\<^sub>R v)
          + ell *\<^sub>R ((p + u *\<^sub>R v) - (p - u *\<^sub>R v))
          + \<mu> *\<^sub>R ((p - t *\<^sub>R n) - (p - u *\<^sub>R v))"
    proof -
      have hbase_diff:
        "(p + u *\<^sub>R v) - (p - u *\<^sub>R v) = (2 * u) *\<^sub>R v"
        by (simp add: vec_eq_iff algebra_simps)
      have hapex_diff:
        "(p - t *\<^sub>R n) - (p - u *\<^sub>R v) = u *\<^sub>R v - t *\<^sub>R n"
        by (simp add: vec_eq_iff algebra_simps)
      have "(p - u *\<^sub>R v)
          + ell *\<^sub>R ((p + u *\<^sub>R v) - (p - u *\<^sub>R v))
          + \<mu> *\<^sub>R ((p - t *\<^sub>R n) - (p - u *\<^sub>R v))
        = p + (- u + 2 * u * ell + u * \<mu>) *\<^sub>R v + (- (\<mu> * t)) *\<^sub>R n"
        using hbase_diff hapex_diff
        by (simp add: algebra_simps scaleR_add_right)
      also have "\<dots> = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
        using h\<mu>t hv_coeff by (by100 simp)
      finally show ?thesis
        by (by100 simp)
    qed
    have "p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n \<in>
      {p - u *\<^sub>R v
        + ell *\<^sub>R ((p + u *\<^sub>R v) - (p - u *\<^sub>R v))
        + \<mu> *\<^sub>R ((p - t *\<^sub>R n) - (p - u *\<^sub>R v))
        | ell \<mu>. 0 \<le> ell \<and> 0 \<le> \<mu> \<and> ell + \<mu> \<le> 1}"
      using heq hell0 h\<mu>0 hell\<mu> by (by100 blast)
    thus "p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
        \<in> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p - t *\<^sub>R n}"
      using convex_hull_3_alt
        [of "p - u *\<^sub>R v" "p + u *\<^sub>R v" "p - t *\<^sub>R n"]
      by (by100 simp)
  qed
  have hdiamond_ball:
    "\<exists>eps>0. ball p eps \<subseteq>
      convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p + s *\<^sub>R n}
        \<union> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p - t *\<^sub>R n}"
    using hsmall_coords hupper_membership hlower_membership
  proof -
    obtain eps where heps: "0 < eps"
      and hball:
        "\<forall>x\<in>ball p eps.
          \<exists>\<alpha> \<beta>. x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n
            \<and> \<bar>\<alpha>\<bar> < u / 2
            \<and> \<bar>\<beta>\<bar> < min s t / 2"
      using hsmall_coords by (by100 blast)
    have hsub:
      "ball p eps \<subseteq>
        convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p + s *\<^sub>R n}
          \<union> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p - t *\<^sub>R n}"
    proof
      fix x
      assume hx: "x \<in> ball p eps"
      obtain \<alpha> \<beta> where hx_eq: "x = p + \<alpha> *\<^sub>R v + \<beta> *\<^sub>R n"
        and h\<alpha>: "\<bar>\<alpha>\<bar> < u / 2"
        and h\<beta>: "\<bar>\<beta>\<bar> < min s t / 2"
        using hball hx by (by100 blast)
      show "x \<in>
        convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p + s *\<^sub>R n}
          \<union> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p - t *\<^sub>R n}"
      proof (cases "0 \<le> \<beta>")
        case True
        have h\<beta>s: "\<beta> < s / 2"
          using h\<beta> True min.cobounded1[of s t] by (by100 linarith)
        have "x \<in> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p + s *\<^sub>R n}"
          using hupper_membership h\<alpha> True h\<beta>s hx_eq by (by100 blast)
        thus ?thesis
          by (by100 blast)
      next
        case False
        have h\<beta>neg: "\<beta> < 0"
          using False by (by100 linarith)
        have h\<beta>t: "- (t / 2) < \<beta>"
          using h\<beta> False min.cobounded2[of s t] by (by100 linarith)
        have "x \<in> convex hull {p - u *\<^sub>R v, p + u *\<^sub>R v, p - t *\<^sub>R n}"
          using hlower_membership h\<alpha> h\<beta>neg h\<beta>t hx_eq by (by100 blast)
        thus ?thesis
          by (by100 blast)
      qed
    qed
    show ?thesis
      using heps hsub by (by100 blast)
  qed
  show ?thesis
    using hdiamond_ball that
    by (by100 blast)
qed

lemma geotop_2simplex_opposite_side_shared_edge_rel_interior_subset_HOL_interior_union_prefix:
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes hab: "a \<noteq> b"
  assumes hc_not_ab: "c \<notin> {a, b}"
  assumes hd_not_ab: "d \<notin> {a, b}"
  assumes he_eq: "e = geotop_convex_hull {a, b}"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
  assumes hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
  assumes hopp: "(n \<bullet> c > r \<and> n \<bullet> d < r) \<or> (n \<bullet> c < r \<and> n \<bullet> d > r)"
  shows "rel_interior e \<subseteq> interior (\<sigma> \<union> \<tau>)"
  (**
    Analytic local-neighborhood step for the shared-edge model: along the
    relative interior of the common edge, the two opposite-side 2-simplexes
    fill a full Euclidean disk neighborhood. **)
proof
  fix p
  assume hp: "p \<in> rel_interior e"
  have hv: "b - a \<noteq> 0"
    using hab by (by100 simp)
  have hn: "n \<noteq> 0"
  proof
    assume hn0: "n = 0"
    show False
      using hopp hn0 by (by100 auto)
  qed
  have ha_aff: "a \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have hb_aff: "b \<in> affine hull {a, b}"
    by (rule hull_inc) (by100 simp)
  have ha_line: "n \<bullet> a = r"
    using hline ha_aff by (by100 simp)
  have hb_line: "n \<bullet> b = r"
    using hline hb_aff by (by100 simp)
  have horth_n: "n \<bullet> (b - a) = 0"
    using ha_line hb_line by (simp add: inner_diff_right)
  have horth: "(b - a) \<bullet> n = 0"
    using horth_n by (simp add: inner_commute)
  obtain u where hu: "0 < u"
    and hqminus: "p - u *\<^sub>R (b - a) \<in> \<sigma> \<inter> \<tau>"
    and hqplus: "p + u *\<^sub>R (b - a) \<in> \<sigma> \<inter> \<tau>"
    by (rule geotop_shared_edge_small_subsegment_in_two_2simplexes_prefix
        [OF hab he_eq h\<sigma>V h\<tau>V hp])
  obtain s t where hs: "0 < s"
    and ht: "0 < t"
    and hprobes:
      "(p + s *\<^sub>R n \<in> interior \<sigma> \<and> p - t *\<^sub>R n \<in> interior \<tau>)
        \<or> (p - s *\<^sub>R n \<in> interior \<sigma> \<and> p + t *\<^sub>R n \<in> interior \<tau>)"
    by (rule geotop_2simplex_opposite_side_shared_edge_normal_probes_in_HOL_interiors_prefix
        [OF hab hc_not_ab hd_not_ab hn he_eq h\<sigma>V h\<tau>V hline hopp hp])
  from hprobes show "p \<in> interior (\<sigma> \<union> \<tau>)"
  proof
    assume hside:
      "p + s *\<^sub>R n \<in> interior \<sigma> \<and> p - t *\<^sub>R n \<in> interior \<tau>"
    obtain eps where heps: "0 < eps"
      and hball:
        "ball p eps \<subseteq>
          convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p + s *\<^sub>R n}
            \<union> convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p - t *\<^sub>R n}"
      by (rule geotop_shared_edge_probe_diamond_contains_ball_prefix
          [OF hv hn horth hu hs ht])
    have hdiamond_sub:
      "convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p + s *\<^sub>R n}
        \<union> convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p - t *\<^sub>R n}
        \<subseteq> \<sigma> \<union> \<tau>"
      by (rule geotop_shared_edge_probe_triangles_subset_union_prefix
          [OF h\<sigma>V h\<tau>V hqminus hqplus hside[THEN conjunct1] hside[THEN conjunct2]])
    have hball_sub: "ball p eps \<subseteq> \<sigma> \<union> \<tau>"
      using hball hdiamond_sub by (by100 blast)
    have hp_ball: "p \<in> ball p eps"
      using heps by (by100 simp)
    show ?thesis
      by (rule interiorI[OF open_ball hp_ball hball_sub])
  next
    assume hside:
      "p - s *\<^sub>R n \<in> interior \<sigma> \<and> p + t *\<^sub>R n \<in> interior \<tau>"
    have hn_neg: "- n \<noteq> 0"
      using hn by (by100 simp)
    have horth_neg: "(b - a) \<bullet> (- n) = 0"
      using horth by (by100 simp)
    obtain eps where heps: "0 < eps"
      and hball_raw:
        "ball p eps \<subseteq>
          convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p + s *\<^sub>R (- n)}
            \<union> convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p - t *\<^sub>R (- n)}"
      by (rule geotop_shared_edge_probe_diamond_contains_ball_prefix
          [OF hv hn_neg horth_neg hu hs ht])
    have hball:
      "ball p eps \<subseteq>
        convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p - s *\<^sub>R n}
          \<union> convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p + t *\<^sub>R n}"
      using hball_raw by (by100 simp)
    have hdiamond_sub:
      "convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p - s *\<^sub>R n}
        \<union> convex hull {p - u *\<^sub>R (b - a), p + u *\<^sub>R (b - a), p + t *\<^sub>R n}
        \<subseteq> \<sigma> \<union> \<tau>"
      by (rule geotop_shared_edge_probe_triangles_subset_union_prefix
          [OF h\<sigma>V h\<tau>V hqminus hqplus hside[THEN conjunct1] hside[THEN conjunct2]])
    have hball_sub: "ball p eps \<subseteq> \<sigma> \<union> \<tau>"
      using hball hdiamond_sub by (by100 blast)
    have hp_ball: "p \<in> ball p eps"
      using heps by (by100 simp)
    show ?thesis
      by (rule interiorI[OF open_ball hp_ball hball_sub])
  qed
qed

lemma geotop_complex_two_2simplex_shared_edge_rel_interior_subset_HOL_interior_union_prefix:
  fixes K :: "(real^2) set set"
  fixes e \<sigma> \<tau> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  assumes hedge: "geotop_is_edge e"
  shows "rel_interior e \<subseteq> interior (\<sigma> \<union> \<tau>)"
  (**
    Moise local model for the two-sided edge case: two distinct 2-simplexes
    of the same complex that share the edge \<open>e\<close> lie on opposite sides of
    \<open>e\<close>.  Their union fills the two local half-disks along
    \<open>rel_interior e\<close>, so it has ordinary Euclidean interior there. **)
proof (rule geotop_complex_two_2simplex_shared_edge_vertices_opposite_sides_prefix
    [OF hK h\<sigma>K h\<tau>K h\<sigma>2 h\<tau>2 h\<sigma>\<tau> he\<sigma> he\<tau> hedge])
  fix a b c d n r
  assume hab: "a \<noteq> b"
    and hc_not_ab: "c \<notin> {a, b}"
    and hd_not_ab: "d \<notin> {a, b}"
    and hcd: "c \<noteq> d"
    and he_eq: "e = geotop_convex_hull {a, b}"
    and h\<sigma>V: "geotop_simplex_vertices \<sigma> {a, b, c}"
    and h\<tau>V: "geotop_simplex_vertices \<tau> {a, b, d}"
    and hn: "n \<noteq> 0"
    and hline: "affine hull {a, b} = {x. n \<bullet> x = r}"
    and hc_ne: "n \<bullet> c \<noteq> r"
    and hd_ne: "n \<bullet> d \<noteq> r"
    and h\<sigma>_pos: "n \<bullet> c > r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p > r}"
    and h\<sigma>_neg: "n \<bullet> c < r \<Longrightarrow> interior \<sigma> \<subseteq> {p. n \<bullet> p < r}"
    and h\<tau>_pos: "n \<bullet> d > r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p > r}"
    and h\<tau>_neg: "n \<bullet> d < r \<Longrightarrow> interior \<tau> \<subseteq> {p. n \<bullet> p < r}"
    and hopp: "(n \<bullet> c > r \<and> n \<bullet> d < r) \<or> (n \<bullet> c < r \<and> n \<bullet> d > r)"
  show ?thesis
    by (rule geotop_2simplex_opposite_side_shared_edge_rel_interior_subset_HOL_interior_union_prefix
        [OF hab hc_not_ab hd_not_ab he_eq h\<sigma>V h\<tau>V hline hopp])
qed

lemma geotop_polygon_disk_nonboundary_edge_rel_interior_disjoint_prefix:
  fixes J e \<sigma> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>face: "geotop_is_face e \<sigma>"
  assumes hnot_boundary: "\<not> e \<subseteq> J"
  shows "J \<inter> rel_interior e = {}"
  (**
    Contrapositive of the one-sided edge-star fact, in the form needed for
    Figure 3.2: once an edge is not a disk-boundary edge, any relative-interior
    point of it has a two-triangle local neighborhood inside the carrier, so it
    cannot lie on the polygon frontier. **)
proof (rule ccontr)
  assume hne: "J \<inter> rel_interior e \<noteq> {}"
  obtain x where hxJ: "x \<in> J" and hxrel: "x \<in> rel_interior e"
    using hne by (by100 blast)
  let ?F = "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
  have hfaces_ne: "?F \<noteq> {\<sigma>}"
  proof
    assume hfaces: "?F = {\<sigma>}"
    have "e \<subseteq> J"
      by (rule geotop_unique_incident_edge_subset_polygon_boundary_prefix
          [OF hJ hK hK_poly heK hedge h\<sigma>K h\<sigma>2 h\<sigma>face hfaces])
    thus False
      using hnot_boundary by (by100 blast)
  qed
  have h\<sigma>F: "\<sigma> \<in> ?F"
    using h\<sigma>K h\<sigma>2 h\<sigma>face by (by100 simp)
  have hex_\<tau>:
    "\<exists>\<tau>. \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau> \<and> \<tau> \<noteq> \<sigma>"
  proof (rule ccontr)
    assume hno: "\<not> (\<exists>\<tau>. \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and>
        geotop_is_face e \<tau> \<and> \<tau> \<noteq> \<sigma>)"
    have hF_sub_single: "?F \<subseteq> {\<sigma>}"
    proof
      fix \<tau>
      assume h\<tau>F: "\<tau> \<in> ?F"
      have "\<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>"
        using h\<tau>F by (by100 simp)
      hence "\<tau> = \<sigma>"
        using hno by (by100 blast)
      thus "\<tau> \<in> {\<sigma>}"
        by (by100 simp)
    qed
    have hsingle_sub_F: "{\<sigma>} \<subseteq> ?F"
      using h\<sigma>F by (by100 simp)
    have "?F = {\<sigma>}"
      using hF_sub_single hsingle_sub_F by (by100 blast)
    thus False
      using hfaces_ne by (by100 blast)
  qed
  obtain \<tau> where h\<tau>K: "\<tau> \<in> K"
    and h\<tau>2: "geotop_simplex_dim \<tau> 2"
    and h\<tau>face: "geotop_is_face e \<tau>"
    and h\<tau>\<sigma>: "\<tau> \<noteq> \<sigma>"
    using hex_\<tau> by (elim exE conjE)
  have h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
    using h\<tau>\<sigma> by (by100 blast)
  have hrel_int_union: "rel_interior e \<subseteq> interior (\<sigma> \<union> \<tau>)"
    by (rule geotop_complex_two_2simplex_shared_edge_rel_interior_subset_HOL_interior_union_prefix
        [OF hK h\<sigma>K h\<tau>K h\<sigma>2 h\<tau>2 h\<sigma>\<tau> h\<sigma>face h\<tau>face hedge])
  have hx_int_union: "x \<in> interior (\<sigma> \<union> \<tau>)"
    using hrel_int_union hxrel by (by100 blast)
  have hunion_sub_poly: "\<sigma> \<union> \<tau> \<subseteq> geotop_polyhedron K"
    using h\<sigma>K h\<tau>K unfolding geotop_polyhedron_def by (by100 blast)
  have hinterior_sub_poly:
    "interior (\<sigma> \<union> \<tau>) \<subseteq> interior (geotop_polyhedron K)"
    by (rule interior_mono[OF hunion_sub_poly])
  have hx_int_poly: "x \<in> interior (geotop_polyhedron K)"
    using hx_int_union hinterior_sub_poly by (by100 blast)
  have hfront_eq: "frontier (geotop_polyhedron K) = J"
    by (rule geotop_polygon_disk_polyhedron_frontier_prefix[OF hJ hK_poly])
  have hx_front: "x \<in> frontier (geotop_polyhedron K)"
    using hxJ hfront_eq by (by100 simp)
  show False
    using hx_int_poly hx_front unfolding Elementary_Topology.frontier_def
    by (by100 simp)
qed

lemma geotop_polygon_disk_nonboundary_segment_arc_interior_disjoint_prefix:
  fixes J e \<sigma> :: "(real^2) set" and K :: "(real^2) set set"
    and P Q :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hPQ: "P \<noteq> Q"
  assumes he_eq: "e = closed_segment P Q"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>face: "geotop_is_face e \<sigma>"
  assumes hnot_boundary: "\<not> closed_segment P Q \<subseteq> J"
  shows "J \<inter> geotop_arc_interior (closed_segment P Q) {P, Q} = {}"
  (**
    Segment-notation bridge for Figure 3.2: the edge-star argument rules out
    polygon-boundary contact in \<open>rel_interior e\<close>; for a nondegenerate closed
    segment this is the same as the GeoTop arc interior of that segment. **)
proof (rule ccontr)
  assume hne: "J \<inter> geotop_arc_interior (closed_segment P Q) {P, Q} \<noteq> {}"
  obtain x where hxJ: "x \<in> J"
    and hxarc: "x \<in> geotop_arc_interior (closed_segment P Q) {P, Q}"
    using hne by (by100 blast)
  have hnot_e_boundary: "\<not> e \<subseteq> J"
    using he_eq hnot_boundary by (by100 simp)
  have hrel_disj: "J \<inter> rel_interior e = {}"
    by (rule geotop_polygon_disk_nonboundary_edge_rel_interior_disjoint_prefix
        [OF hJ hK hK_poly heK hedge h\<sigma>K h\<sigma>2 h\<sigma>face hnot_e_boundary])
  have hrel_eq: "rel_interior e = open_segment P Q"
    using he_eq hPQ rel_interior_closed_segment[of P Q] by (by100 simp)
  have hx_open: "x \<in> open_segment P Q"
    using hxarc unfolding geotop_arc_interior_def open_segment_def by (by100 blast)
  have hxrel: "x \<in> rel_interior e"
    using hrel_eq hx_open by (by100 simp)
  have "x \<in> J \<inter> rel_interior e"
    using hxJ hxrel by (by100 blast)
  thus False
    using hrel_disj by (by100 blast)
qed

lemma geotop_polygon_disk_nonboundary_edge_rel_interior_subset_polygon_interior_prefix:
  fixes J e \<sigma> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>face: "geotop_is_face e \<sigma>"
  assumes hnot_boundary: "\<not> e \<subseteq> J"
  shows "rel_interior e \<subseteq> geotop_polygon_interior J"
proof
  fix x
  assume hxrel: "x \<in> rel_interior e"
  let ?F = "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
  have hfaces_ne: "?F \<noteq> {\<sigma>}"
  proof
    assume hfaces: "?F = {\<sigma>}"
    have "e \<subseteq> J"
      by (rule geotop_unique_incident_edge_subset_polygon_boundary_prefix
          [OF hJ hK hK_poly heK hedge h\<sigma>K h\<sigma>2 h\<sigma>face hfaces])
    thus False
      using hnot_boundary by (by100 blast)
  qed
  have h\<sigma>F: "\<sigma> \<in> ?F"
    using h\<sigma>K h\<sigma>2 h\<sigma>face by (by100 simp)
  have hex_\<tau>:
    "\<exists>\<tau>. \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau> \<and> \<tau> \<noteq> \<sigma>"
  proof (rule ccontr)
    assume hno: "\<not> (\<exists>\<tau>. \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and>
        geotop_is_face e \<tau> \<and> \<tau> \<noteq> \<sigma>)"
    have hF_sub_single: "?F \<subseteq> {\<sigma>}"
    proof
      fix \<tau>
      assume h\<tau>F: "\<tau> \<in> ?F"
      have "\<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>"
        using h\<tau>F by (by100 simp)
      hence "\<tau> = \<sigma>"
        using hno by (by100 blast)
      thus "\<tau> \<in> {\<sigma>}"
        by (by100 simp)
    qed
    have hsingle_sub_F: "{\<sigma>} \<subseteq> ?F"
      using h\<sigma>F by (by100 simp)
    have "?F = {\<sigma>}"
      using hF_sub_single hsingle_sub_F by (by100 blast)
    thus False
      using hfaces_ne by (by100 blast)
  qed
  obtain \<tau> where h\<tau>K: "\<tau> \<in> K"
    and h\<tau>2: "geotop_simplex_dim \<tau> 2"
    and h\<tau>face: "geotop_is_face e \<tau>"
    and h\<tau>\<sigma>: "\<tau> \<noteq> \<sigma>"
    using hex_\<tau> by (elim exE conjE)
  have h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
    using h\<tau>\<sigma> by (by100 blast)
  have hrel_int_union: "rel_interior e \<subseteq> interior (\<sigma> \<union> \<tau>)"
    by (rule geotop_complex_two_2simplex_shared_edge_rel_interior_subset_HOL_interior_union_prefix
        [OF hK h\<sigma>K h\<tau>K h\<sigma>2 h\<tau>2 h\<sigma>\<tau> h\<sigma>face h\<tau>face hedge])
  have hx_int_union: "x \<in> interior (\<sigma> \<union> \<tau>)"
    using hrel_int_union hxrel by (by100 blast)
  have hunion_sub_poly: "\<sigma> \<union> \<tau> \<subseteq> geotop_polyhedron K"
    using h\<sigma>K h\<tau>K unfolding geotop_polyhedron_def by (by100 blast)
  have hinterior_sub_poly:
    "interior (\<sigma> \<union> \<tau>) \<subseteq> interior (geotop_polyhedron K)"
    by (rule interior_mono[OF hunion_sub_poly])
  have hx_int_poly: "x \<in> interior (geotop_polyhedron K)"
    using hx_int_union hinterior_sub_poly by (by100 blast)
  have hclos_on:
    "closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J) =
      closure (geotop_polygon_interior J)"
    by (rule closure_on_geotop_UNIV_eq_closure)
  have hpoly_closure:
    "geotop_polyhedron K = closure (geotop_polygon_interior J)"
    using hK_poly hclos_on by (by100 simp)
  have hregular:
    "interior (closure (geotop_polygon_interior J)) = geotop_polygon_interior J"
    by (rule geotop_polygon_interior_regular_closed_prefix[OF hJ])
  have hpoly_int:
    "interior (geotop_polyhedron K) = geotop_polygon_interior J"
    using hpoly_closure hregular by (by100 simp)
  show "x \<in> geotop_polygon_interior J"
    using hx_int_poly hpoly_int by (by100 simp)
qed

lemma geotop_polygon_disk_nonboundary_segment_arc_interior_subset_polygon_interior_prefix:
  fixes J e \<sigma> :: "(real^2) set" and K :: "(real^2) set set"
    and P Q :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hPQ: "P \<noteq> Q"
  assumes he_eq: "e = closed_segment P Q"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>face: "geotop_is_face e \<sigma>"
  assumes hnot_boundary: "\<not> closed_segment P Q \<subseteq> J"
  shows "geotop_arc_interior (closed_segment P Q) {P, Q} \<subseteq>
      geotop_polygon_interior J"
proof
  fix x
  assume hxarc: "x \<in> geotop_arc_interior (closed_segment P Q) {P, Q}"
  have hnot_e_boundary: "\<not> e \<subseteq> J"
    using he_eq hnot_boundary by (by100 simp)
  have hrel_sub: "rel_interior e \<subseteq> geotop_polygon_interior J"
    by (rule geotop_polygon_disk_nonboundary_edge_rel_interior_subset_polygon_interior_prefix
        [OF hJ hK hK_poly heK hedge h\<sigma>K h\<sigma>2 h\<sigma>face hnot_e_boundary])
  have hrel_eq: "rel_interior e = open_segment P Q"
    using he_eq hPQ rel_interior_closed_segment[of P Q] by (by100 simp)
  have hx_open: "x \<in> open_segment P Q"
    using hxarc unfolding geotop_arc_interior_def open_segment_def by (by100 blast)
  have hxrel: "x \<in> rel_interior e"
    using hrel_eq hx_open by (by100 simp)
  show "x \<in> geotop_polygon_interior J"
    using hrel_sub hxrel by (by100 blast)
qed

lemma geotop_two_triangle_nonboundary_edge_shared_prefix:
  fixes J e \<sigma> \<tau> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hT_eq: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2} = {\<sigma>, \<tau>}"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes hnot_boundary: "\<not> e \<subseteq> J"
  shows "geotop_is_face e \<tau>"
  (**
    Contrapositive form used in pointwise boundary-contact bookkeeping: a
    non-boundary edge of \<open>\<sigma>\<close> must be the shared edge with \<open>\<tau>\<close>. **)
proof (rule ccontr)
  assume hnot: "\<not> geotop_is_face e \<tau>"
  have "e \<subseteq> J"
    by (rule geotop_two_triangle_nonshared_edge_subset_boundary_prefix
        [OF hJ hK hK_poly hT_eq h\<sigma>K h\<sigma>2 heK hedge he\<sigma> hnot])
  thus False
    using hnot_boundary by (by100 blast)
qed

lemma geotop_two_triangle_edge_boundary_or_shared_prefix:
  fixes J e \<sigma> \<tau> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hT_eq: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2} = {\<sigma>, \<tau>}"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  shows "e \<subseteq> J \<or> geotop_is_face e \<tau>"
  (**
    Exactly two triangles: every edge of one triangle is either a polygon
    boundary edge or the shared edge with the other triangle. **)
proof (cases "e \<subseteq> J")
  case True
  then show ?thesis
    by (by100 blast)
next
  case False
  have "geotop_is_face e \<tau>"
    by (rule geotop_two_triangle_nonboundary_edge_shared_prefix
        [OF hJ hK hK_poly hT_eq h\<sigma>K h\<sigma>2 heK hedge he\<sigma> False])
  then show ?thesis
    by (by100 blast)
qed

lemma geotop_two_triangle_shared_edge_inter_eq_prefix:
  fixes e \<sigma> \<tau> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hT_eq: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2} = {\<sigma>, \<tau>}"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes hedge: "geotop_is_edge e"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  shows "\<sigma> \<inter> \<tau> = e"
  (**
    Shared-edge form specialized to the exactly two-triangle base case. **)
proof -
  have h\<tau>_in: "\<tau> \<in> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2}"
    using hT_eq by (by100 simp)
  have h\<tau>K: "\<tau> \<in> K"
    using h\<tau>_in by (by100 simp)
  have h\<tau>2: "geotop_simplex_dim \<tau> 2"
    using h\<tau>_in by (by100 simp)
  show ?thesis
    by (rule geotop_complex_two_2simplex_shared_edge_inter_eq_edge_prefix
        [OF hK h\<sigma>K h\<tau>K h\<sigma>2 h\<tau>2 h\<sigma>\<tau> he\<sigma> he\<tau> hedge])
qed

lemma geotop_two_triangle_shared_edge_endpoint_boundary_cover_prefix:
  fixes J e \<sigma> \<tau> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hT_eq: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2} = {\<sigma>, \<tau>}"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes he\<sigma>: "geotop_is_face e \<sigma>"
  assumes he\<tau>: "geotop_is_face e \<tau>"
  assumes hxe: "x \<in> e"
  assumes hx_not_rel: "x \<notin> rel_interior e"
  shows "x \<in> \<Union>{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J}"
  (**
    Endpoint part of the exactly-two-triangle base case: a point of the shared
    edge outside its relative interior is one of its endpoints, and each such
    endpoint lies on one of the two nonshared boundary edges of \<open>\<sigma>\<close>. **)
proof -
  obtain v\<^sub>0 v\<^sub>1 v\<^sub>2 where hv\<^sub>0v\<^sub>1: "v\<^sub>0 \<noteq> v\<^sub>1"
    and hv\<^sub>2_not: "v\<^sub>2 \<notin> {v\<^sub>0, v\<^sub>1}"
    and he_eq: "e = geotop_convex_hull {v\<^sub>0, v\<^sub>1}"
    and hvertices: "geotop_simplex_vertices \<sigma> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
    by (rule geotop_2simplex_edge_face_vertices_prefix[OF h\<sigma>2 hedge he\<sigma>])
  let ?e\<^sub>02 = "geotop_convex_hull {v\<^sub>0, v\<^sub>2}"
  let ?e\<^sub>12 = "geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
  have hother:
    "geotop_is_edge ?e\<^sub>02 \<and> geotop_is_face ?e\<^sub>02 \<sigma>
      \<and> geotop_is_edge ?e\<^sub>12 \<and> geotop_is_face ?e\<^sub>12 \<sigma>"
    by (rule geotop_2simplex_vertices_other_edge_faces_prefix
        [OF hvertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
  have he\<^sub>02_edge: "geotop_is_edge ?e\<^sub>02"
    using hother by (by100 simp)
  have he\<^sub>02_face: "geotop_is_face ?e\<^sub>02 \<sigma>"
    using hother by (by100 simp)
  have he\<^sub>12_edge: "geotop_is_edge ?e\<^sub>12"
    using hother by (by100 simp)
  have he\<^sub>12_face: "geotop_is_face ?e\<^sub>12 \<sigma>"
    using hother by (by100 simp)
  have hface_closed: "\<forall>\<rho>\<in>K. \<forall>F. geotop_is_face F \<rho> \<longrightarrow> F \<in> K"
    using hK unfolding geotop_is_complex_def by (by100 blast)
  have he\<^sub>02K: "?e\<^sub>02 \<in> K"
    using hface_closed h\<sigma>K he\<^sub>02_face by (by100 blast)
  have he\<^sub>12K: "?e\<^sub>12 \<in> K"
    using hface_closed h\<sigma>K he\<^sub>12_face by (by100 blast)
  have hdistinct:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> ?e\<^sub>02
      \<and> geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> ?e\<^sub>12
      \<and> ?e\<^sub>02 \<noteq> ?e\<^sub>12"
    by (rule geotop_2simplex_vertices_edge_hulls_distinct_prefix
        [OF hvertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
  have he_ne_02: "e \<noteq> ?e\<^sub>02"
    using he_eq hdistinct by (by100 simp)
  have he_ne_12: "e \<noteq> ?e\<^sub>12"
    using he_eq hdistinct by (by100 simp)
  have h\<tau>_in: "\<tau> \<in> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2}"
    using hT_eq by (by100 simp)
  have h\<tau>K: "\<tau> \<in> K"
    using h\<tau>_in by (by100 simp)
  have h\<tau>2: "geotop_simplex_dim \<tau> 2"
    using h\<tau>_in by (by100 simp)
  have hinter: "\<sigma> \<inter> \<tau> = e"
    by (rule geotop_two_triangle_shared_edge_inter_eq_prefix
        [OF hK hT_eq h\<sigma>K h\<sigma>2 h\<sigma>\<tau> hedge he\<sigma> he\<tau>])
  have he\<^sub>02_not_tau: "\<not> geotop_is_face ?e\<^sub>02 \<tau>"
  proof
    assume he\<^sub>02_tau: "geotop_is_face ?e\<^sub>02 \<tau>"
    have he\<^sub>02_sub_\<sigma>: "?e\<^sub>02 \<subseteq> \<sigma>"
      by (rule geotop_is_face_imp_subset_prefix[OF he\<^sub>02_face])
    have he\<^sub>02_sub_\<tau>: "?e\<^sub>02 \<subseteq> \<tau>"
      by (rule geotop_is_face_imp_subset_prefix[OF he\<^sub>02_tau])
    have he\<^sub>02_sub_e: "?e\<^sub>02 \<subseteq> e"
      using he\<^sub>02_sub_\<sigma> he\<^sub>02_sub_\<tau> hinter by (by100 blast)
    have hface_e: "geotop_is_face ?e\<^sub>02 e"
      by (rule geotop_complex_subset_simplex_face_prefix[OF hK he\<^sub>02K heK he\<^sub>02_sub_e])
    have "?e\<^sub>02 = e"
      by (rule geotop_edge_face_of_edge_eq_prefix[OF he\<^sub>02_edge hedge hface_e])
    thus False
      using he_ne_02 by (by100 blast)
  qed
  have he\<^sub>12_not_tau: "\<not> geotop_is_face ?e\<^sub>12 \<tau>"
  proof
    assume he\<^sub>12_tau: "geotop_is_face ?e\<^sub>12 \<tau>"
    have he\<^sub>12_sub_\<sigma>: "?e\<^sub>12 \<subseteq> \<sigma>"
      by (rule geotop_is_face_imp_subset_prefix[OF he\<^sub>12_face])
    have he\<^sub>12_sub_\<tau>: "?e\<^sub>12 \<subseteq> \<tau>"
      by (rule geotop_is_face_imp_subset_prefix[OF he\<^sub>12_tau])
    have he\<^sub>12_sub_e: "?e\<^sub>12 \<subseteq> e"
      using he\<^sub>12_sub_\<sigma> he\<^sub>12_sub_\<tau> hinter by (by100 blast)
    have hface_e: "geotop_is_face ?e\<^sub>12 e"
      by (rule geotop_complex_subset_simplex_face_prefix[OF hK he\<^sub>12K heK he\<^sub>12_sub_e])
    have "?e\<^sub>12 = e"
      by (rule geotop_edge_face_of_edge_eq_prefix[OF he\<^sub>12_edge hedge hface_e])
    thus False
      using he_ne_12 by (by100 blast)
  qed
  have he\<^sub>02J: "?e\<^sub>02 \<subseteq> J"
    by (rule geotop_two_triangle_nonshared_edge_subset_boundary_prefix
        [OF hJ hK hK_poly hT_eq h\<sigma>K h\<sigma>2 he\<^sub>02K he\<^sub>02_edge he\<^sub>02_face he\<^sub>02_not_tau])
  have he\<^sub>12J: "?e\<^sub>12 \<subseteq> J"
    by (rule geotop_two_triangle_nonshared_edge_subset_boundary_prefix
        [OF hJ hK hK_poly hT_eq h\<sigma>K h\<sigma>2 he\<^sub>12K he\<^sub>12_edge he\<^sub>12_face he\<^sub>12_not_tau])
  have he_seg: "e = closed_segment v\<^sub>0 v\<^sub>1"
  proof -
    have "e = convex hull {v\<^sub>0, v\<^sub>1}"
      using he_eq geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>1}"] by (by100 simp)
    also have "\<dots> = closed_segment v\<^sub>0 v\<^sub>1"
      by (rule segment_convex_hull[symmetric])
    finally show ?thesis .
  qed
  have hrel_eq: "rel_interior e = open_segment v\<^sub>0 v\<^sub>1"
    using he_seg hv\<^sub>0v\<^sub>1 rel_interior_closed_segment[of v\<^sub>0 v\<^sub>1] by (by100 simp)
  have hx_endpoint: "x = v\<^sub>0 \<or> x = v\<^sub>1"
    using hxe hx_not_rel he_seg hrel_eq unfolding open_segment_def by (by100 blast)
  show ?thesis
  proof (rule disjE[OF hx_endpoint])
    assume hx0: "x = v\<^sub>0"
    have hx_e02: "x \<in> ?e\<^sub>02"
    proof -
      have "v\<^sub>0 \<in> convex hull {v\<^sub>0, v\<^sub>2}"
        by (rule hull_inc) (by100 simp)
      thus ?thesis
        using hx0 geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>2}"] by (by100 simp)
    qed
    have "?e\<^sub>02 \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J}"
      using he\<^sub>02K he\<^sub>02_edge he\<^sub>02_face he\<^sub>02J by (by100 simp)
    thus ?thesis
      using hx_e02 by (by100 blast)
  next
    assume hx1: "x = v\<^sub>1"
    have hx_e12: "x \<in> ?e\<^sub>12"
    proof -
      have "v\<^sub>1 \<in> convex hull {v\<^sub>1, v\<^sub>2}"
        by (rule hull_inc) (by100 simp)
      thus ?thesis
        using hx1 geotop_convex_hull_eq_HOL[of "{v\<^sub>1, v\<^sub>2}"] by (by100 simp)
    qed
    have "?e\<^sub>12 \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J}"
      using he\<^sub>12K he\<^sub>12_edge he\<^sub>12_face he\<^sub>12J by (by100 simp)
    thus ?thesis
      using hx_e12 by (by100 blast)
  qed
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
proof
  fix x
  assume hx: "x \<in> \<sigma> \<inter> J"
  have hxJ: "x \<in> J"
    using hx by (by100 simp)
  have h\<tau>_in: "\<tau> \<in> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2}"
    using hT_eq by (by100 simp)
  have h\<tau>K: "\<tau> \<in> K"
    using h\<tau>_in by (by100 simp)
  have h\<tau>2: "geotop_simplex_dim \<tau> 2"
    using h\<tau>_in by (by100 simp)
  have hx_all_edges:
      "x \<in> \<Union>{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
    using geotop_2simplex_polygon_boundary_inter_subset_complex_edge_faces_prefix
      [OF hJ hK h\<sigma>K h\<sigma>2 hK_poly] hx
    by (by100 blast)
  obtain e where heK: "e \<in> K"
    and hedge: "geotop_is_edge e"
    and he\<sigma>: "geotop_is_face e \<sigma>"
    and hxe: "x \<in> e"
    using hx_all_edges by (by100 blast)
  have hcase: "e \<subseteq> J \<or> geotop_is_face e \<tau>"
    by (rule geotop_two_triangle_edge_boundary_or_shared_prefix
        [OF hJ hK hK_poly hT_eq h\<sigma>K h\<sigma>2 heK hedge he\<sigma>])
  show "x \<in> \<Union>{e \<in> K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J}"
  proof (rule disjE[OF hcase])
    assume heJ: "e \<subseteq> J"
    have "e \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J}"
      using heK hedge he\<sigma> heJ by (by100 simp)
    thus ?thesis
      using hxe by (by100 blast)
  next
    assume he\<tau>: "geotop_is_face e \<tau>"
    show ?thesis
    proof (cases "x \<in> rel_interior e")
      case True
      have hlocal: "rel_interior e \<subseteq> interior (\<sigma> \<union> \<tau>)"
        by (rule geotop_complex_two_2simplex_shared_edge_rel_interior_subset_HOL_interior_union_prefix
            [OF hK h\<sigma>K h\<tau>K h\<sigma>2 h\<tau>2 h\<sigma>\<tau> he\<sigma> he\<tau> hedge])
      have hx_int_union: "x \<in> interior (\<sigma> \<union> \<tau>)"
        using hlocal True by (by100 blast)
      have hunion_sub: "\<sigma> \<union> \<tau> \<subseteq> geotop_polyhedron K"
        using h\<sigma>K h\<tau>K unfolding geotop_polyhedron_def by (by100 blast)
      have hinterior_sub:
          "interior (\<sigma> \<union> \<tau>) \<subseteq> interior (geotop_polyhedron K)"
        by (rule interior_mono[OF hunion_sub])
      have hx_int_poly: "x \<in> interior (geotop_polyhedron K)"
        using hx_int_union hinterior_sub by (by100 blast)
      have hfront_eq: "frontier (geotop_polyhedron K) = J"
        by (rule geotop_polygon_disk_polyhedron_frontier_prefix[OF hJ hK_poly])
      have hx_front: "x \<in> frontier (geotop_polyhedron K)"
        using hxJ hfront_eq by (by100 simp)
      have False
        using hx_int_poly hx_front unfolding Elementary_Topology.frontier_def
        by (by100 simp)
      thus ?thesis
        by (by100 simp)
    next
      case False
      show ?thesis
        by (rule geotop_two_triangle_shared_edge_endpoint_boundary_cover_prefix
            [OF hJ hK hK_poly hT_eq h\<sigma>K h\<sigma>2 h\<sigma>\<tau> heK hedge he\<sigma> he\<tau> hxe False])
    qed
  qed
qed

lemma geotop_two_triangle_other_2simplex_not_subset_prefix:
  fixes \<sigma> \<tau> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hT_eq: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2} = {\<sigma>, \<tau>}"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  shows "\<not> \<tau> \<subseteq> \<sigma>"
  (**
    Two-triangle base case bookkeeping: the second 2-simplex cannot be
    contained in the first one, since a proper containment between two
    simplexes of the same complex forces a strict dimension drop. **)
proof
  assume hsub: "\<tau> \<subseteq> \<sigma>"
  have h\<tau>_in: "\<tau> \<in> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2}"
    using hT_eq by (by100 simp)
  have h\<tau>K: "\<tau> \<in> K"
    using h\<tau>_in by (by100 simp)
  have h\<tau>2: "geotop_simplex_dim \<tau> 2"
    using h\<tau>_in by (by100 simp)
  have hproper: "\<tau> \<subset> \<sigma>"
    using hsub h\<sigma>\<tau> by (by100 blast)
  have "(2::nat) < 2"
    by (rule geotop_complex_proper_subset_dim_less
        [OF hK h\<tau>K h\<sigma>K hproper h\<tau>2 h\<sigma>2])
  thus False
    by (by100 simp)
qed

lemma geotop_two_triangle_all_boundary_edges_force_other_subset_prefix:
  fixes J \<sigma> \<tau> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hT_eq: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2} = {\<sigma>, \<tau>}"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes hcard: "card {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J} = 3"
  shows "\<tau> \<subseteq> \<sigma>"
  (**
    Book base case, exactly two 2-simplexes: if all three edge faces of
    \<open>\<sigma>\<close> lie on the polygon boundary, then the disk bounded by that frontier
    leaves no boundary edge through which the second 2-simplex can attach
    outside \<open>\<sigma>\<close>; hence the other 2-simplex is forced into \<open>\<sigma>\<close>. **)
proof -
  have h\<tau>_data: "\<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2"
  proof -
    have "\<tau> \<in> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2}"
      using hT_eq by (by100 simp)
    thus ?thesis
      by (by100 simp)
  qed
  have hfront_sub_J: "frontier \<sigma> \<subseteq> J"
    by (rule geotop_2simplex_three_selected_edge_faces_frontier_subset_prefix
        [OF h\<sigma>2 hcard])
  have h\<sigma>J_eq_frontier: "\<sigma> \<inter> J = frontier \<sigma>"
    by (rule geotop_2simplex_three_selected_edge_faces_boundary_contact_eq_frontier_prefix
        [OF hJ h\<sigma>K h\<sigma>2 hK_poly hcard])
  have h\<tau>_sub_poly: "\<tau> \<subseteq> geotop_polyhedron K"
    using h\<tau>_data unfolding geotop_polyhedron_def by (by100 blast)
  have h\<tau>_sub_disk:
      "\<tau> \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
    using h\<tau>_sub_poly hK_poly by (by100 simp)
  have hclosed_disk_sub_\<sigma>:
      "closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)
        \<subseteq> \<sigma>"
    by (rule geotop_polygon_disk_all_triangle_boundary_closure_subset_prefix
        [OF hJ h\<sigma>2 hfront_sub_J h\<sigma>J_eq_frontier])
  show ?thesis
    using h\<tau>_sub_disk hclosed_disk_sub_\<sigma> by (by100 blast)
qed

lemma geotop_polygon_disk_three_boundary_edges_force_2simplex_subset_prefix:
  fixes J \<sigma> \<tau> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>card: "card {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J} = 3"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  shows "\<tau> \<subseteq> \<sigma>"
  (**
    Disk-wide form of the all-boundary triangle obstruction: if all three
    edge faces of a triangle are selected as polygon-boundary edges, the
    closed polygonal disk is already contained in that triangle. **)
proof -
  have hfront_sub_J: "frontier \<sigma> \<subseteq> J"
    by (rule geotop_2simplex_three_selected_edge_faces_frontier_subset_prefix
        [OF h\<sigma>2 h\<sigma>card])
  have h\<sigma>J_eq_frontier: "\<sigma> \<inter> J = frontier \<sigma>"
    by (rule geotop_2simplex_three_selected_edge_faces_boundary_contact_eq_frontier_prefix
        [OF hJ h\<sigma>K h\<sigma>2 hK_poly h\<sigma>card])
  have h\<tau>_sub_poly: "\<tau> \<subseteq> geotop_polyhedron K"
    using h\<tau>K unfolding geotop_polyhedron_def by (by100 blast)
  have h\<tau>_sub_disk:
      "\<tau> \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
    using h\<tau>_sub_poly hK_poly by (by100 simp)
  have hclosed_disk_sub_\<sigma>:
      "closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)
        \<subseteq> \<sigma>"
    by (rule geotop_polygon_disk_all_triangle_boundary_closure_subset_prefix
        [OF hJ h\<sigma>2 hfront_sub_J h\<sigma>J_eq_frontier])
  show ?thesis
    using h\<tau>_sub_disk hclosed_disk_sub_\<sigma> by (by100 blast)
qed

lemma geotop_polygon_disk_three_boundary_edges_no_other_2simplex_prefix:
  fixes J \<sigma> \<tau> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>card: "card {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J} = 3"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<tau>\<sigma>: "\<tau> \<noteq> \<sigma>"
  shows False
  (**
    Consequence for the ear/decomposition package: an all-boundary triangle
    cannot coexist with a distinct 2-simplex in the same disk triangulation. **)
proof -
  have hsub: "\<tau> \<subseteq> \<sigma>"
    by (rule geotop_polygon_disk_three_boundary_edges_force_2simplex_subset_prefix
        [OF hJ hK_poly h\<sigma>K h\<sigma>2 h\<sigma>card h\<tau>K h\<tau>2])
  have hproper: "\<tau> \<subset> \<sigma>"
    using hsub h\<tau>\<sigma> by (by100 blast)
  have "(2::nat) < 2"
    by (rule geotop_complex_proper_subset_dim_less
        [OF hK h\<tau>K h\<sigma>K hproper h\<tau>2 h\<sigma>2])
  thus False
    by (by100 simp)
qed

lemma geotop_polygon_disk_three_boundary_edges_2simplexes_singleton_prefix:
  fixes J \<sigma> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>card: "card {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J} = 3"
  shows "{\<tau>\<in>K. geotop_simplex_dim \<tau> 2} = {\<sigma>}"
  (**
    Cardinal form of the same obstruction: a disk triangulation with an
    all-boundary triangle has no other 2-simplexes. **)
proof
  show "{\<tau>\<in>K. geotop_simplex_dim \<tau> 2} \<subseteq> {\<sigma>}"
  proof
    fix \<tau>
    assume h\<tau>T: "\<tau> \<in> {\<tau>\<in>K. geotop_simplex_dim \<tau> 2}"
    have h\<tau>K: "\<tau> \<in> K"
      using h\<tau>T by (by100 simp)
    have h\<tau>2: "geotop_simplex_dim \<tau> 2"
      using h\<tau>T by (by100 simp)
    show "\<tau> \<in> {\<sigma>}"
    proof (cases "\<tau> = \<sigma>")
      case True
      show ?thesis
        using True by (by100 simp)
    next
      case False
      have False
        by (rule geotop_polygon_disk_three_boundary_edges_no_other_2simplex_prefix
            [OF hJ hK hK_poly h\<sigma>K h\<sigma>2 h\<sigma>card h\<tau>K h\<tau>2 False])
      thus ?thesis
        by (by100 simp)
    qed
  qed
  show "{\<sigma>} \<subseteq> {\<tau>\<in>K. geotop_simplex_dim \<tau> 2}"
    using h\<sigma>K h\<sigma>2 by (by100 simp)
qed

lemma geotop_polygon_disk_multi_2simplex_not_three_boundary_edges_prefix:
  fixes J \<sigma> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes hT_gt1: "card {\<tau>\<in>K. geotop_simplex_dim \<tau> 2} > 1"
  shows "card {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J} \<noteq> 3"
  (**
    Multi-triangle disk form of the all-boundary obstruction: if the disk has
    more than one 2-simplex, no single triangle can put all three edge faces
    on the polygon boundary. **)
proof
  assume hcard3:
    "card {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J} = 3"
  have hT_single:
    "{\<tau>\<in>K. geotop_simplex_dim \<tau> 2} = {\<sigma>}"
    by (rule geotop_polygon_disk_three_boundary_edges_2simplexes_singleton_prefix
        [OF hJ hK hK_poly h\<sigma>K h\<sigma>2 hcard3])
  have "card {\<tau>\<in>K. geotop_simplex_dim \<tau> 2} = 1"
    using hT_single by (by100 simp)
  thus False
    using hT_gt1 by (by100 simp)
qed

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
proof
  assume hcard: "card {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J} = 3"
  have hsub: "\<tau> \<subseteq> \<sigma>"
    by (rule geotop_two_triangle_all_boundary_edges_force_other_subset_prefix
        [OF hJ hK hK_poly hT_eq h\<sigma>K h\<sigma>2 h\<sigma>\<tau> hcard])
  have hnsub: "\<not> \<tau> \<subseteq> \<sigma>"
    by (rule geotop_two_triangle_other_2simplex_not_subset_prefix
        [OF hK hT_eq h\<sigma>K h\<sigma>2 h\<sigma>\<tau>])
  show False
    using hnsub hsub by (by100 blast)
qed

lemma geotop_selected_boundary_edge_set_card_le3_prefix:
  fixes J \<sigma> :: "(real^2) set" and K :: "(real^2) set set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  shows "finite {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J}
      \<and> card {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J} \<le> 3"
  (**
    Selected-edge form of the three-edge bound for a 2-simplex: imposing
    membership in the polygon boundary only takes a subset of the edge faces. **)
proof -
  let ?E = "{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J}"
  let ?A = "{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma>}"
  have hA: "finite ?A \<and> card ?A \<le> 3"
    by (rule geotop_2simplex_complex_edge_faces_card_le3_prefix[OF h\<sigma>2])
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

lemma geotop_two_triangle_boundary_edge_faces_card_le2_prefix:
  fixes J \<sigma> \<tau> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hT_eq: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2} = {\<sigma>, \<tau>}"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  shows "card {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J} \<le> 2"
  (**
    Cardinal bookkeeping for the two-triangle base case: among the three edge
    faces of a 2-simplex, at most two can be selected as polygon-boundary
    edges. **)
proof -
  let ?E = "{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J}"
  have hE_card_le3: "card ?E \<le> 3"
  proof -
    have hE: "finite ?E \<and> card ?E \<le> 3"
      by (rule geotop_selected_boundary_edge_set_card_le3_prefix[OF h\<sigma>2])
    show ?thesis
      using hE by (by100 simp)
  qed
  have hE_card_ne3: "card ?E \<noteq> 3"
    by (rule geotop_two_triangle_not_all_boundary_edges_prefix
        [OF hJ hK hK_poly hT_eq h\<sigma>K h\<sigma>2 h\<sigma>\<tau>])
  show ?thesis
    using hE_card_le3 hE_card_ne3 by (by100 linarith)
qed

lemma geotop_selected_boundary_edge_set_allowed_card_le2_prefix:
  fixes J \<sigma> :: "(real^2) set" and K :: "(real^2) set set"
  assumes hE_fin: "finite {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J}"
  assumes hE_card_le2:
    "card {e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J} \<le> 2"
  shows "{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J} = {} \<or>
     (\<exists>e. {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} = {e}
        \<and> geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J) \<or>
     (\<exists>e1 e2. {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} = {e1, e2}
        \<and> e1 \<noteq> e2 \<and> geotop_is_edge e1 \<and> geotop_is_edge e2
        \<and> geotop_is_face e1 \<sigma> \<and> geotop_is_face e2 \<sigma> \<and> e1 \<subseteq> J \<and> e2 \<subseteq> J)"
  (**
    Pure finite-set bookkeeping for the formal free-simplex predicate: a
    selected boundary-edge set with at most two elements has exactly one of the
    allowed shapes. **)
proof -
  let ?E = "{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J}"
  have hcases: "card ?E = 0 \<or> card ?E = 1 \<or> card ?E = 2"
    using hE_card_le2 by (by100 linarith)
  show ?thesis
  proof (cases "card ?E = 0")
    case True
    have "?E = {}"
      using hE_fin True by (by100 simp)
    thus ?thesis by (by100 simp)
  next
    case False
    show ?thesis
    proof (cases "card ?E = 1")
      case True
      have hsingle: "\<exists>e. ?E = {e}"
        using True card_1_singleton_iff[of ?E] by (by100 simp)
      obtain e where hE: "?E = {e}"
        using hsingle by (elim exE)
      have he: "e \<in> ?E"
        using hE by (by100 simp)
      have hedge: "geotop_is_edge e"
        using he by (by100 simp)
      have hface: "geotop_is_face e \<sigma>"
        using he by (by100 simp)
      have hsub: "e \<subseteq> J"
        using he by (by100 simp)
      show ?thesis
      proof (rule disjI2)
        show "(\<exists>e. {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} = {e} \<and>
            geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J) \<or>
          (\<exists>e1 e2. {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} = {e1, e2} \<and>
            e1 \<noteq> e2 \<and> geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
            geotop_is_face e1 \<sigma> \<and> geotop_is_face e2 \<sigma> \<and> e1 \<subseteq> J \<and> e2 \<subseteq> J)"
        proof (rule disjI1)
          show "\<exists>e. {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} = {e} \<and>
              geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J"
          proof (rule exI[where x = e])
            show "{d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} = {e} \<and>
                geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J"
              by (intro conjI hE hedge hface hsub)
          qed
        qed
      qed
    next
      case False
      have hcard2: "card ?E = 2"
        using hcases \<open>card ?E \<noteq> 0\<close> False by (by100 simp)
      have hdouble: "\<exists>e1 e2. ?E = {e1, e2} \<and> e1 \<noteq> e2"
        using hcard2 card_2_iff[of ?E] by (by100 simp)
      obtain e1 e2 where hE: "?E = {e1, e2}" and hneq: "e1 \<noteq> e2"
        using hdouble by (elim exE conjE)
      have he1: "e1 \<in> ?E"
        using hE by (by100 simp)
      have he2: "e2 \<in> ?E"
        using hE by (by100 simp)
      have he1_edge: "geotop_is_edge e1"
        using he1 by (by100 simp)
      have he2_edge: "geotop_is_edge e2"
        using he2 by (by100 simp)
      have he1_face: "geotop_is_face e1 \<sigma>"
        using he1 by (by100 simp)
      have he2_face: "geotop_is_face e2 \<sigma>"
        using he2 by (by100 simp)
      have he1_sub: "e1 \<subseteq> J"
        using he1 by (by100 simp)
      have he2_sub: "e2 \<subseteq> J"
        using he2 by (by100 simp)
      show ?thesis
      proof (rule disjI2)
        show "(\<exists>e. {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} = {e} \<and>
            geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J) \<or>
          (\<exists>e1 e2. {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} = {e1, e2} \<and>
            e1 \<noteq> e2 \<and> geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
            geotop_is_face e1 \<sigma> \<and> geotop_is_face e2 \<sigma> \<and> e1 \<subseteq> J \<and> e2 \<subseteq> J)"
        proof (rule disjI2)
          show "\<exists>e1 e2. {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} = {e1, e2} \<and>
              e1 \<noteq> e2 \<and> geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
              geotop_is_face e1 \<sigma> \<and> geotop_is_face e2 \<sigma> \<and> e1 \<subseteq> J \<and> e2 \<subseteq> J"
          proof (rule exI[where x = e1], rule exI[where x = e2])
            show "{d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J} = {e1, e2} \<and>
                e1 \<noteq> e2 \<and> geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                geotop_is_face e1 \<sigma> \<and> geotop_is_face e2 \<sigma> \<and> e1 \<subseteq> J \<and> e2 \<subseteq> J"
              by (intro conjI hE hneq he1_edge he2_edge he1_face he2_face he1_sub he2_sub)
          qed
        qed
      qed
    qed
  qed
qed

lemma geotop_selected_boundary_edge_set_card_ge2_if_other_edge_prefix:
  fixes J \<theta> e\<^sub>0 e\<^sub>1 :: "(real^2) set" and K :: "(real^2) set set"
  assumes hE_fin: "finite {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  assumes he\<^sub>0_sel:
    "e\<^sub>0 \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  assumes he\<^sub>1_sel_if:
    "e\<^sub>1 \<subseteq> J \<Longrightarrow>
      e\<^sub>1 \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  assumes he\<^sub>0e\<^sub>1: "e\<^sub>0 \<noteq> e\<^sub>1"
  assumes he\<^sub>1_sub: "e\<^sub>1 \<subseteq> J"
  shows "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} \<ge> 2"
  (**
    Finite selected-edge bookkeeping: an already selected boundary edge and a
    distinct second boundary edge force at least two selected edge faces. **)
proof -
  let ?E = "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  let ?P = "{e\<^sub>0, e\<^sub>1}"
  have he\<^sub>1_sel: "e\<^sub>1 \<in> ?E"
    by (rule he\<^sub>1_sel_if[OF he\<^sub>1_sub])
  have hP_sub: "?P \<subseteq> ?E"
    using he\<^sub>0_sel he\<^sub>1_sel by (by100 blast)
  have hP_card: "card ?P = 2"
    using he\<^sub>0e\<^sub>1 by (by100 simp)
  have hcard_mono: "card ?P \<le> card ?E"
    by (rule card_mono[OF hE_fin hP_sub])
  show ?thesis
    using hP_card hcard_mono by (by100 simp)
qed

lemma geotop_selected_boundary_edge_set_card_eq3_if_two_other_edges_prefix:
  fixes J \<theta> e\<^sub>0 e\<^sub>1 e\<^sub>2 :: "(real^2) set" and K :: "(real^2) set set"
  assumes hE_fin: "finite {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  assumes he\<^sub>0_sel:
    "e\<^sub>0 \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  assumes he\<^sub>1_sel_if:
    "e\<^sub>1 \<subseteq> J \<Longrightarrow>
      e\<^sub>1 \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  assumes he\<^sub>2_sel_if:
    "e\<^sub>2 \<subseteq> J \<Longrightarrow>
      e\<^sub>2 \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  assumes he\<^sub>0e\<^sub>1: "e\<^sub>0 \<noteq> e\<^sub>1"
  assumes he\<^sub>0e\<^sub>2: "e\<^sub>0 \<noteq> e\<^sub>2"
  assumes he\<^sub>1e\<^sub>2: "e\<^sub>1 \<noteq> e\<^sub>2"
  assumes hE_card_le3:
    "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} \<le> 3"
  assumes he\<^sub>1_sub: "e\<^sub>1 \<subseteq> J"
  assumes he\<^sub>2_sub: "e\<^sub>2 \<subseteq> J"
  shows "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} = 3"
  (**
    Finite selected-edge bookkeeping: an already selected edge plus both
    distinct remaining boundary edges force exactly the three edge faces. **)
proof -
  let ?E = "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  let ?P = "{e\<^sub>0, e\<^sub>1, e\<^sub>2}"
  have he\<^sub>1_sel: "e\<^sub>1 \<in> ?E"
    by (rule he\<^sub>1_sel_if[OF he\<^sub>1_sub])
  have he\<^sub>2_sel: "e\<^sub>2 \<in> ?E"
    by (rule he\<^sub>2_sel_if[OF he\<^sub>2_sub])
  have hP_sub: "?P \<subseteq> ?E"
    using he\<^sub>0_sel he\<^sub>1_sel he\<^sub>2_sel by (by100 blast)
  have hP_card: "card ?P = 3"
    using he\<^sub>0e\<^sub>1 he\<^sub>0e\<^sub>2 he\<^sub>1e\<^sub>2 by (by100 simp)
  have hcard_mono: "card ?P \<le> card ?E"
    by (rule card_mono[OF hE_fin hP_sub])
  have hE_card_ge3: "card ?E \<ge> 3"
    using hP_card hcard_mono by (by100 simp)
  show ?thesis
    using hE_card_ge3 hE_card_le3 by (by100 simp)
qed

lemma geotop_selected_boundary_edge_set_eq_three_named_prefix:
  fixes J \<theta> e\<^sub>0 e\<^sub>1 e\<^sub>2 :: "(real^2) set" and K :: "(real^2) set set"
  assumes hE_fin: "finite {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  assumes he\<^sub>0_sel:
    "e\<^sub>0 \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  assumes he\<^sub>1_sel_if:
    "e\<^sub>1 \<subseteq> J \<Longrightarrow>
      e\<^sub>1 \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  assumes he\<^sub>2_sel_if:
    "e\<^sub>2 \<subseteq> J \<Longrightarrow>
      e\<^sub>2 \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  assumes he\<^sub>0e\<^sub>1: "e\<^sub>0 \<noteq> e\<^sub>1"
  assumes he\<^sub>0e\<^sub>2: "e\<^sub>0 \<noteq> e\<^sub>2"
  assumes he\<^sub>1e\<^sub>2: "e\<^sub>1 \<noteq> e\<^sub>2"
  assumes he\<^sub>1_sub: "e\<^sub>1 \<subseteq> J"
  assumes he\<^sub>2_sub: "e\<^sub>2 \<subseteq> J"
  assumes hE_card:
    "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} = 3"
  shows "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} =
      {e\<^sub>0, e\<^sub>1, e\<^sub>2}"
  (**
    Finite selected-edge bookkeeping: once the selected-edge set has cardinal
    three and contains the three distinct named edge faces, it is exactly that
    named set. **)
proof -
  let ?E = "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  let ?P = "{e\<^sub>0, e\<^sub>1, e\<^sub>2}"
  have he\<^sub>1_sel: "e\<^sub>1 \<in> ?E"
    by (rule he\<^sub>1_sel_if[OF he\<^sub>1_sub])
  have he\<^sub>2_sel: "e\<^sub>2 \<in> ?E"
    by (rule he\<^sub>2_sel_if[OF he\<^sub>2_sub])
  have hP_sub_E: "?P \<subseteq> ?E"
    using he\<^sub>0_sel he\<^sub>1_sel he\<^sub>2_sel by (by100 blast)
  have hP_card: "card ?P = 3"
    using he\<^sub>0e\<^sub>1 he\<^sub>0e\<^sub>2 he\<^sub>1e\<^sub>2 by (by100 simp)
  have hcard_eq: "card ?P = card ?E"
    using hP_card hE_card by (by100 simp)
  have hP_eq_E: "?P = ?E"
    by (rule card_subset_eq[OF hE_fin hP_sub_E hcard_eq])
  show ?thesis
    using hP_eq_E by (by100 simp)
qed

lemma geotop_union_eq_three_named_sets_prefix:
  fixes E :: "'a set set" and e\<^sub>0 e\<^sub>1 e\<^sub>2 :: "'a set"
  assumes hE: "E = {e\<^sub>0, e\<^sub>1, e\<^sub>2}"
  shows "\<Union>E = e\<^sub>0 \<union> e\<^sub>1 \<union> e\<^sub>2"
  (**
    Pure set bookkeeping for the selected-edge decomposition: once the selected
    family is exactly three named edge carriers, its carrier union is their
    ordinary union. **)
proof -
  have "\<Union>{e\<^sub>0, e\<^sub>1, e\<^sub>2} = e\<^sub>0 \<union> e\<^sub>1 \<union> e\<^sub>2"
    by (by100 blast)
  thus ?thesis
    using hE by (by100 simp)
qed

lemma geotop_subset_union_from_three_named_family_prefix:
  fixes C :: "'a set" and E :: "'a set set" and e\<^sub>0 e\<^sub>1 e\<^sub>2 :: "'a set"
  assumes hC: "C \<subseteq> e\<^sub>0 \<union> e\<^sub>1 \<union> e\<^sub>2"
  assumes hE: "E = {e\<^sub>0, e\<^sub>1, e\<^sub>2}"
  shows "C \<subseteq> \<Union>E"
  (**
    Inclusion form used in the nonfree boundary-triangle case of Theorem 3.3:
    containment in the three named edge carriers transfers to containment in
    the selected-edge carrier union. **)
proof -
  have hUnion: "\<Union>E = e\<^sub>0 \<union> e\<^sub>1 \<union> e\<^sub>2"
    by (rule geotop_union_eq_three_named_sets_prefix[OF hE])
  show ?thesis
    using hC hUnion by (by100 simp)
qed

lemma geotop_contact_outside_selected_union_on_other_two_sets_prefix:
  fixes C e\<^sub>0 e\<^sub>1 e\<^sub>2 :: "'a set" and E :: "'a set set"
  assumes houtside: "\<exists>x. x \<in> C \<and> x \<notin> \<Union>E"
  assumes hC: "C \<subseteq> e\<^sub>0 \<union> e\<^sub>1 \<union> e\<^sub>2"
  assumes he\<^sub>0E: "e\<^sub>0 \<in> E"
  shows "\<exists>x. x \<in> C \<and> x \<notin> \<Union>E \<and> x \<in> e\<^sub>1 \<union> e\<^sub>2"
  (**
    Pure set form of the nonfree boundary-triangle reduction: if the contact
    is covered by three named edge carriers and one of them is already selected,
    any contact point outside the selected carrier union lies on one of the
    other two named edge carriers. **)
proof -
  obtain x where hxC: "x \<in> C" and hxnot: "x \<notin> \<Union>E"
    using houtside by (elim exE conjE)
  have hx_three: "x \<in> e\<^sub>0 \<union> e\<^sub>1 \<union> e\<^sub>2"
    using hC hxC by (by100 blast)
  have hx_not_e\<^sub>0: "x \<notin> e\<^sub>0"
  proof
    assume "x \<in> e\<^sub>0"
    hence "x \<in> \<Union>E"
      using he\<^sub>0E by (by100 blast)
    thus False
      using hxnot by (by100 blast)
  qed
  have hx_other: "x \<in> e\<^sub>1 \<union> e\<^sub>2"
    using hx_three hx_not_e\<^sub>0 by (by100 blast)
  show ?thesis
    using hxC hxnot hx_other by (by100 blast)
qed

lemma geotop_contact_outside_selected_union_avoids_selected_set_prefix:
  fixes C D e :: "'a set" and E :: "'a set set"
  assumes houtside: "\<exists>x. x \<in> C \<and> x \<notin> \<Union>E \<and> x \<in> D"
  assumes heE: "e \<in> E"
  shows "\<exists>x. x \<in> C \<and> x \<notin> e \<and> x \<in> D"
  (**
    Pure set bookkeeping: a contact point outside the selected carrier union is
    not on any particular selected carrier. **)
proof -
  obtain x where hxC: "x \<in> C" and hxnot: "x \<notin> \<Union>E" and hxD: "x \<in> D"
    using houtside by (elim exE conjE)
  have hx_not_e: "x \<notin> e"
  proof
    assume "x \<in> e"
    hence "x \<in> \<Union>E"
      using heE by (by100 blast)
    thus False
      using hxnot by (by100 blast)
  qed
  show ?thesis
    using hxC hx_not_e hxD by (by100 blast)
qed

lemma geotop_other_edge_contact_not_base_avoids_base_endpoints_prefix:
  fixes C :: "(real^2) set" and v\<^sub>0 v\<^sub>1 v\<^sub>2 :: "real^2"
  assumes hcontact:
    "\<exists>x. x \<in> C
      \<and> x \<notin> geotop_convex_hull {v\<^sub>0, v\<^sub>1}
      \<and> x \<in> geotop_convex_hull {v\<^sub>0, v\<^sub>2}
          \<union> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
  shows "\<exists>x. x \<in> C
      \<and> x \<in> (geotop_convex_hull {v\<^sub>0, v\<^sub>2} - {v\<^sub>0})
          \<union> (geotop_convex_hull {v\<^sub>1, v\<^sub>2} - {v\<^sub>1})"
  (**
    Endpoint hygiene for the Figure 3.2 contact point: if it lies on one of
    the two non-base edges but not on the base edge, then it is not the base
    endpoint of whichever non-base edge contains it. **)
proof -
  obtain x where hxC: "x \<in> C"
    and hxnot: "x \<notin> geotop_convex_hull {v\<^sub>0, v\<^sub>1}"
    and hx_other: "x \<in> geotop_convex_hull {v\<^sub>0, v\<^sub>2}
          \<union> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
    using hcontact by (elim exE conjE)
  have hv\<^sub>0_HOL: "v\<^sub>0 \<in> convex hull {v\<^sub>0, v\<^sub>1}"
    using hull_inc[of v\<^sub>0 "{v\<^sub>0, v\<^sub>1}"] by (by100 simp)
  have hv\<^sub>0_base: "v\<^sub>0 \<in> geotop_convex_hull {v\<^sub>0, v\<^sub>1}"
    using hv\<^sub>0_HOL geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>1}"] by (by100 simp)
  have hv\<^sub>1_HOL: "v\<^sub>1 \<in> convex hull {v\<^sub>0, v\<^sub>1}"
    using hull_inc[of v\<^sub>1 "{v\<^sub>0, v\<^sub>1}"] by (by100 simp)
  have hv\<^sub>1_base: "v\<^sub>1 \<in> geotop_convex_hull {v\<^sub>0, v\<^sub>1}"
    using hv\<^sub>1_HOL geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>1}"] by (by100 simp)
  have hx_ne_v\<^sub>0: "x \<noteq> v\<^sub>0"
    using hxnot hv\<^sub>0_base by (by100 blast)
  have hx_ne_v\<^sub>1: "x \<noteq> v\<^sub>1"
    using hxnot hv\<^sub>1_base by (by100 blast)
  have hx_target:
      "x \<in> (geotop_convex_hull {v\<^sub>0, v\<^sub>2} - {v\<^sub>0})
          \<union> (geotop_convex_hull {v\<^sub>1, v\<^sub>2} - {v\<^sub>1})"
    using hx_other hx_ne_v\<^sub>0 hx_ne_v\<^sub>1 by (by100 blast)
  show ?thesis
    using hxC hx_target by (by100 blast)
qed

lemma geotop_nonbase_edge_contact_geotop_to_closed_segment_prefix:
  fixes C :: "(real^2) set" and v\<^sub>0 v\<^sub>1 v\<^sub>2 :: "real^2"
  assumes hcontact:
    "\<exists>x. x \<in> C
      \<and> x \<in> (geotop_convex_hull {v\<^sub>0, v\<^sub>2} - {v\<^sub>0})
          \<union> (geotop_convex_hull {v\<^sub>1, v\<^sub>2} - {v\<^sub>1})"
  shows "\<exists>x. x \<in> C
      \<and> x \<in> (closed_segment v\<^sub>0 v\<^sub>2 - {v\<^sub>0})
          \<union> (closed_segment v\<^sub>1 v\<^sub>2 - {v\<^sub>1})"
  (**
    Notational bridge for the Figure 3.2 witness: after the selected-edge
    bookkeeping is done in GeoTop convex-hull notation, the triangle-edge
    geometry below uses HOL closed segments. **)
proof -
  obtain x where hxC: "x \<in> C"
    and hx_geo: "x \<in> (geotop_convex_hull {v\<^sub>0, v\<^sub>2} - {v\<^sub>0})
          \<union> (geotop_convex_hull {v\<^sub>1, v\<^sub>2} - {v\<^sub>1})"
    using hcontact by (elim exE conjE)
  have h02: "geotop_convex_hull {v\<^sub>0, v\<^sub>2} = closed_segment v\<^sub>0 v\<^sub>2"
    using segment_convex_hull[of v\<^sub>0 v\<^sub>2] geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>2}"]
    by (by100 simp)
  have h12: "geotop_convex_hull {v\<^sub>1, v\<^sub>2} = closed_segment v\<^sub>1 v\<^sub>2"
    using segment_convex_hull[of v\<^sub>1 v\<^sub>2] geotop_convex_hull_eq_HOL[of "{v\<^sub>1, v\<^sub>2}"]
    by (by100 simp)
  have hx_seg:
      "x \<in> (closed_segment v\<^sub>0 v\<^sub>2 - {v\<^sub>0})
          \<union> (closed_segment v\<^sub>1 v\<^sub>2 - {v\<^sub>1})"
    using hx_geo h02 h12 by (by100 simp)
  show ?thesis
    using hxC hx_seg by (by100 blast)
qed

lemma geotop_nonbase_segment_contact_avoids_base_segment_prefix:
  fixes C :: "(real^2) set" and v\<^sub>0 v\<^sub>1 v\<^sub>2 :: "real^2"
  assumes hnot_col: "\<not> collinear {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
  assumes hcontact:
    "\<exists>x. x \<in> C
      \<and> x \<in> (closed_segment v\<^sub>0 v\<^sub>2 - {v\<^sub>0})
          \<union> (closed_segment v\<^sub>1 v\<^sub>2 - {v\<^sub>1})"
  shows "\<exists>x. x \<in> C
      \<and> x \<notin> closed_segment v\<^sub>0 v\<^sub>1
      \<and> x \<in> (closed_segment v\<^sub>0 v\<^sub>2 - {v\<^sub>0})
          \<union> (closed_segment v\<^sub>1 v\<^sub>2 - {v\<^sub>1})"
  (**
    Closed-segment endpoint hygiene for the Figure 3.2 witness: in a
    nondegenerate triangle, a point on either non-base edge away from the
    base endpoint is not on the base edge. **)
proof -
  obtain x where hxC: "x \<in> C"
    and hx_nonbase: "x \<in> (closed_segment v\<^sub>0 v\<^sub>2 - {v\<^sub>0})
          \<union> (closed_segment v\<^sub>1 v\<^sub>2 - {v\<^sub>1})"
    using hcontact by (elim exE conjE)
  have hset_left: "{v\<^sub>1, v\<^sub>0, v\<^sub>2} = {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
    by (by100 blast)
  have hnot_col_left: "\<not> collinear {v\<^sub>1, v\<^sub>0, v\<^sub>2}"
    using hnot_col hset_left by (by100 simp)
  have hleft_raw:
      "closed_segment v\<^sub>1 v\<^sub>0 \<inter> closed_segment v\<^sub>0 v\<^sub>2 = {v\<^sub>0}"
    by (rule Int_closed_segment[OF disjI2[OF hnot_col_left]])
  have hleft:
      "closed_segment v\<^sub>0 v\<^sub>1 \<inter> closed_segment v\<^sub>0 v\<^sub>2 = {v\<^sub>0}"
    using hleft_raw closed_segment_commute[of v\<^sub>1 v\<^sub>0] by (by100 simp)
  have hset_right: "{v\<^sub>0, v\<^sub>1, v\<^sub>2} = {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
    by (by100 blast)
  have hnot_col_right: "\<not> collinear {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
    using hnot_col hset_right by (by100 simp)
  have hright:
      "closed_segment v\<^sub>0 v\<^sub>1 \<inter> closed_segment v\<^sub>1 v\<^sub>2 = {v\<^sub>1}"
    by (rule Int_closed_segment[OF disjI2[OF hnot_col_right]])
  have hx_not_base: "x \<notin> closed_segment v\<^sub>0 v\<^sub>1"
  proof
    assume hxbase: "x \<in> closed_segment v\<^sub>0 v\<^sub>1"
    show False
    proof (cases "x \<in> closed_segment v\<^sub>0 v\<^sub>2 - {v\<^sub>0}")
      case True
      hence "x \<in> closed_segment v\<^sub>0 v\<^sub>1 \<inter> closed_segment v\<^sub>0 v\<^sub>2"
        using hxbase by (by100 blast)
      hence "x = v\<^sub>0"
        using hleft by (by100 simp)
      thus False
        using True by (by100 simp)
    next
      case False
      have hx12: "x \<in> closed_segment v\<^sub>1 v\<^sub>2 - {v\<^sub>1}"
        using hx_nonbase False by (by100 blast)
      hence "x \<in> closed_segment v\<^sub>0 v\<^sub>1 \<inter> closed_segment v\<^sub>1 v\<^sub>2"
        using hxbase by (by100 blast)
      hence "x = v\<^sub>1"
        using hright by (by100 simp)
      thus False
        using hx12 by (by100 simp)
    qed
  qed
  show ?thesis
    using hxC hx_not_base hx_nonbase by (by100 blast)
qed

lemma geotop_selected_boundary_edge_set_union_subset_contact_prefix:
  fixes J \<theta> :: "(real^2) set" and K :: "(real^2) set set"
  shows "\<Union>{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}
      \<subseteq> \<theta> \<inter> J"
  (**
    Selected-edge carrier bookkeeping: every selected edge face lies in both
    the ambient 2-simplex and the polygon-boundary set used for selection. **)
proof
  fix x
  assume hx: "x \<in> \<Union>{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  then obtain d where hdE: "d \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
      and hxd: "x \<in> d"
    by (by100 blast)
  have hd_face: "geotop_is_face d \<theta>"
    using hdE by (by100 simp)
  have hd_sub_\<theta>: "d \<subseteq> \<theta>"
    by (rule geotop_is_face_imp_subset_prefix[OF hd_face])
  have hd_sub_J: "d \<subseteq> J"
    using hdE by (by100 simp)
  show "x \<in> \<theta> \<inter> J"
    using hxd hd_sub_\<theta> hd_sub_J by (by100 blast)
qed

lemma geotop_selected_boundary_edge_set_not_both_other_edges_prefix:
  fixes J \<theta> e\<^sub>0 e\<^sub>1 e\<^sub>2 :: "(real^2) set" and K :: "(real^2) set set"
  assumes hE_fin: "finite {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  assumes he\<^sub>0_sel:
    "e\<^sub>0 \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  assumes he\<^sub>1_sel_if:
    "e\<^sub>1 \<subseteq> J \<Longrightarrow>
      e\<^sub>1 \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  assumes he\<^sub>2_sel_if:
    "e\<^sub>2 \<subseteq> J \<Longrightarrow>
      e\<^sub>2 \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  assumes he\<^sub>0e\<^sub>1: "e\<^sub>0 \<noteq> e\<^sub>1"
  assumes he\<^sub>0e\<^sub>2: "e\<^sub>0 \<noteq> e\<^sub>2"
  assumes he\<^sub>1e\<^sub>2: "e\<^sub>1 \<noteq> e\<^sub>2"
  assumes hE_card_le3:
    "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} \<le> 3"
  assumes hE_card_ne3:
    "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} \<noteq> 3"
  shows "\<not> (e\<^sub>1 \<subseteq> J \<and> e\<^sub>2 \<subseteq> J)"
  (**
    Finite selected-edge bookkeeping for the nonfree boundary triangle case:
    once one edge face is already on the polygon boundary, putting both other
    edge faces on the boundary would force all three selected edge faces. **)
proof
  assume hboth: "e\<^sub>1 \<subseteq> J \<and> e\<^sub>2 \<subseteq> J"
  let ?E = "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  have he\<^sub>1_sub: "e\<^sub>1 \<subseteq> J"
    using hboth by (by100 simp)
  have he\<^sub>2_sub: "e\<^sub>2 \<subseteq> J"
    using hboth by (by100 simp)
  have hE_card_eq3: "card ?E = 3"
    by (rule geotop_selected_boundary_edge_set_card_eq3_if_two_other_edges_prefix
        [OF hE_fin he\<^sub>0_sel he\<^sub>1_sel_if he\<^sub>2_sel_if
          he\<^sub>0e\<^sub>1 he\<^sub>0e\<^sub>2 he\<^sub>1e\<^sub>2 hE_card_le3 he\<^sub>1_sub he\<^sub>2_sub])
  show False
    using hE_card_ne3 hE_card_eq3 by (by100 blast)
qed

lemma geotop_polygon_disk_polygon_edge_subset_frontier_prefix:
  fixes J e :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes heJ: "e \<subseteq> J"
  shows "e \<subseteq> geotop_frontier UNIV geotop_euclidean_topology
      (geotop_polyhedron K)"
  (**
    Reverse rewriting form of the disk-carrier frontier identity.  This is the
    direction needed after the ear argument produces selected polygon-boundary
    edge faces and the book statement asks for edges in \<open>Fr |K|\<close>. **)
proof -
  have hfront: "geotop_frontier UNIV geotop_euclidean_topology
      (geotop_polyhedron K) = J"
    by (rule geotop_polygon_disk_polyhedron_geotop_frontier_prefix[OF hJ hK_poly])
  show ?thesis
    using heJ hfront by (by100 simp)
qed

lemma geotop_polygon_disk_two_selected_boundary_2simplexes_ear_prefix:
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
    Selected-edge form of Moise's ear step for Theorem 3.3.  The hard planar
    content is exactly that a triangulated polygonal disk with more than two
    triangles has two distinct 2-simplexes meeting the polygon boundary in
    edge faces.  The surrounding wrappers translate these selected edges to
    and from the book's \<open>Fr |K|\<close> phrasing. **)
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
proof -
  obtain \<sigma> \<tau> e\<^sub>\<sigma> e\<^sub>\<tau>
    where h\<sigma>K: "\<sigma> \<in> K"
      and h\<tau>K: "\<tau> \<in> K"
      and h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
      and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
      and h\<tau>2: "geotop_simplex_dim \<tau> 2"
      and he\<^sub>\<sigma>_sel:
        "e\<^sub>\<sigma> \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J}"
      and he\<^sub>\<tau>_sel:
        "e\<^sub>\<tau> \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J}"
    using geotop_polygon_disk_two_selected_boundary_2simplexes_ear_prefix
      [OF hJ hK hK_poly hT_gt2]
    by (elim exE conjE)
  have he\<^sub>\<sigma>_edge: "geotop_is_edge e\<^sub>\<sigma>"
    using he\<^sub>\<sigma>_sel by (by100 simp)
  have he\<^sub>\<sigma>_face: "geotop_is_face e\<^sub>\<sigma> \<sigma>"
    using he\<^sub>\<sigma>_sel by (by100 simp)
  have he\<^sub>\<sigma>J: "e\<^sub>\<sigma> \<subseteq> J"
    using he\<^sub>\<sigma>_sel by (by100 simp)
  have he\<^sub>\<sigma>front: "e\<^sub>\<sigma> \<subseteq> geotop_frontier UNIV geotop_euclidean_topology
      (geotop_polyhedron K)"
    by (rule geotop_polygon_disk_polygon_edge_subset_frontier_prefix
        [OF hJ hK_poly he\<^sub>\<sigma>J])
  have he\<^sub>\<tau>_edge: "geotop_is_edge e\<^sub>\<tau>"
    using he\<^sub>\<tau>_sel by (by100 simp)
  have he\<^sub>\<tau>_face: "geotop_is_face e\<^sub>\<tau> \<tau>"
    using he\<^sub>\<tau>_sel by (by100 simp)
  have he\<^sub>\<tau>J: "e\<^sub>\<tau> \<subseteq> J"
    using he\<^sub>\<tau>_sel by (by100 simp)
  have he\<^sub>\<tau>front: "e\<^sub>\<tau> \<subseteq> geotop_frontier UNIV geotop_euclidean_topology
      (geotop_polyhedron K)"
    by (rule geotop_polygon_disk_polygon_edge_subset_frontier_prefix
        [OF hJ hK_poly he\<^sub>\<tau>J])
  show ?thesis
    using h\<sigma>K h\<tau>K h\<sigma>\<tau> h\<sigma>2 h\<tau>2 he\<^sub>\<sigma>_edge he\<^sub>\<sigma>_face he\<^sub>\<sigma>front
      he\<^sub>\<tau>_edge he\<^sub>\<tau>_face he\<^sub>\<tau>front
    by (by100 blast)
qed

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
  show ?thesis
    by (rule geotop_polygon_disk_two_selected_boundary_2simplexes_ear_prefix
        [OF hJ hK hK_poly hT_gt2])
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

lemma geotop_free_2_simplex_selected_edges_intro_prefix:
  fixes K :: "(real^2) set set" and J \<sigma>\<^sub>2 :: "(real^2) set" and E :: "(real^2) set set"
  assumes h\<sigma>K: "\<sigma>\<^sub>2 \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma>\<^sub>2 2"
  assumes hEsub: "E \<subseteq> K"
  assumes hEallowed:
    "E = {} \<or>
     (\<exists>e. E = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<sigma>\<^sub>2 \<and> e \<subseteq> J) \<or>
     (\<exists>e1 e2. E = {e1, e2} \<and> e1 \<noteq> e2 \<and>
        geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
        geotop_is_face e1 \<sigma>\<^sub>2 \<and> geotop_is_face e2 \<sigma>\<^sub>2 \<and>
        e1 \<subseteq> J \<and> e2 \<subseteq> J)"
  assumes hcontact: "\<sigma>\<^sub>2 \<inter> J = \<Union>E"
  shows "geotop_free_2_simplex K J \<sigma>\<^sub>2"
  (**
    Introduction form for the book sentence: if the boundary contact is empty,
    one selected edge, or two selected edges, then the 2-simplex is free. **)
proof -
  have hE:
    "E \<subseteq> K \<and>
     (E = {} \<or>
      (\<exists>e. E = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<sigma>\<^sub>2 \<and> e \<subseteq> J) \<or>
      (\<exists>e1 e2. E = {e1, e2} \<and> e1 \<noteq> e2 \<and>
        geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
        geotop_is_face e1 \<sigma>\<^sub>2 \<and> geotop_is_face e2 \<sigma>\<^sub>2 \<and>
        e1 \<subseteq> J \<and> e2 \<subseteq> J)) \<and>
     \<sigma>\<^sub>2 \<inter> J = \<Union>E"
    by (intro conjI hEsub hEallowed hcontact)
  show ?thesis
    unfolding geotop_free_2_simplex_def
  proof (intro conjI h\<sigma>K h\<sigma>2)
    show "\<exists>E. E \<subseteq> K \<and>
      (E = {} \<or>
       (\<exists>e. E = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<sigma>\<^sub>2 \<and> e \<subseteq> J) \<or>
       (\<exists>e1 e2. E = {e1, e2} \<and> e1 \<noteq> e2 \<and>
          geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
          geotop_is_face e1 \<sigma>\<^sub>2 \<and> geotop_is_face e2 \<sigma>\<^sub>2 \<and>
          e1 \<subseteq> J \<and> e2 \<subseteq> J)) \<and>
      \<sigma>\<^sub>2 \<inter> J = \<Union>E"
      by (rule exI[where x = E]) (rule hE)
  qed
qed

lemma geotop_nonfree_selected_edges_contact_neq_prefix:
  fixes K :: "(real^2) set set" and J \<sigma>\<^sub>2 :: "(real^2) set" and E :: "(real^2) set set"
  assumes h\<sigma>K: "\<sigma>\<^sub>2 \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma>\<^sub>2 2"
  assumes hEsub: "E \<subseteq> K"
  assumes hEallowed:
    "E = {} \<or>
     (\<exists>e. E = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<sigma>\<^sub>2 \<and> e \<subseteq> J) \<or>
     (\<exists>e1 e2. E = {e1, e2} \<and> e1 \<noteq> e2 \<and>
        geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
        geotop_is_face e1 \<sigma>\<^sub>2 \<and> geotop_is_face e2 \<sigma>\<^sub>2 \<and>
        e1 \<subseteq> J \<and> e2 \<subseteq> J)"
  assumes hnot_free: "\<not> geotop_free_2_simplex K J \<sigma>\<^sub>2"
  shows "\<sigma>\<^sub>2 \<inter> J \<noteq> \<Union>E"
  (**
    Contrapositive form of the free-simplex introduction rule: if the selected
    boundary-edge family has an allowed free-simplex shape, then a nonfree
    triangle must have additional boundary contact beyond that selected union. **)
proof
  assume hcontact: "\<sigma>\<^sub>2 \<inter> J = \<Union>E"
  have hfree: "geotop_free_2_simplex K J \<sigma>\<^sub>2"
    by (rule geotop_free_2_simplex_selected_edges_intro_prefix
        [OF h\<sigma>K h\<sigma>2 hEsub hEallowed hcontact])
  show False
    using hnot_free hfree by (by100 blast)
qed

lemma geotop_nonfree_selected_edges_contact_outside_prefix:
  fixes K :: "(real^2) set set" and J \<sigma>\<^sub>2 :: "(real^2) set" and E :: "(real^2) set set"
  assumes h\<sigma>K: "\<sigma>\<^sub>2 \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma>\<^sub>2 2"
  assumes hEsub: "E \<subseteq> K"
  assumes hEallowed:
    "E = {} \<or>
     (\<exists>e. E = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<sigma>\<^sub>2 \<and> e \<subseteq> J) \<or>
     (\<exists>e1 e2. E = {e1, e2} \<and> e1 \<noteq> e2 \<and>
        geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
        geotop_is_face e1 \<sigma>\<^sub>2 \<and> geotop_is_face e2 \<sigma>\<^sub>2 \<and>
        e1 \<subseteq> J \<and> e2 \<subseteq> J)"
  assumes hnot_free: "\<not> geotop_free_2_simplex K J \<sigma>\<^sub>2"
  assumes hUnion_sub: "\<Union>E \<subseteq> \<sigma>\<^sub>2 \<inter> J"
  shows "\<exists>x. x \<in> \<sigma>\<^sub>2 \<inter> J \<and> x \<notin> \<Union>E"
  (**
    Witness form for the nonfree boundary-triangle case: because selected edge
    carriers already lie inside the triangle-boundary contact, nonfreeness
    produces a contact point not carried by the selected edges. **)
proof -
  have hneq: "\<sigma>\<^sub>2 \<inter> J \<noteq> \<Union>E"
    by (rule geotop_nonfree_selected_edges_contact_neq_prefix
        [OF h\<sigma>K h\<sigma>2 hEsub hEallowed hnot_free])
  have "\<not> \<sigma>\<^sub>2 \<inter> J \<subseteq> \<Union>E"
  proof
    assume hsub: "\<sigma>\<^sub>2 \<inter> J \<subseteq> \<Union>E"
    have "\<sigma>\<^sub>2 \<inter> J = \<Union>E"
      using hUnion_sub hsub by (by100 blast)
    thus False
      using hneq by (by100 blast)
  qed
  thus ?thesis
    by (by100 blast)
qed

lemma geotop_theta_middle_arc_inline_decomposition_prefix:
  fixes M B\<^sub>1 B\<^sub>2 B\<^sub>3 E :: "(real^2) set"
  assumes h\<theta>: "geotop_is_polyhedral_theta_graph M B\<^sub>1 B\<^sub>2 B\<^sub>3 E"
  assumes hB\<^sub>2_inner:
    "geotop_arc_interior B\<^sub>2 E \<subseteq> geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>3)"
  shows "{C. \<exists>P\<in>geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>3) -
            geotop_arc_interior B\<^sub>2 E.
           C = geotop_component_at UNIV geotop_euclidean_topology
                (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>3) -
                 geotop_arc_interior B\<^sub>2 E) P}
         =
         {geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>2),
          geotop_polygon_interior (B\<^sub>2 \<union> B\<^sub>3)}"
    and "closure_on UNIV geotop_euclidean_topology
           (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>3)) =
         closure_on UNIV geotop_euclidean_topology
           (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>2))
         \<union> closure_on UNIV geotop_euclidean_topology
           (geotop_polygon_interior (B\<^sub>2 \<union> B\<^sub>3))"
    and "closure_on UNIV geotop_euclidean_topology
           (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>3)) - B\<^sub>2 =
         (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>2) \<union>
          geotop_arc_interior B\<^sub>1 E) \<union>
         (geotop_polygon_interior (B\<^sub>2 \<union> B\<^sub>3) \<union>
          geotop_arc_interior B\<^sub>3 E)"
    and "top1_connected_on
           (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>2) \<union>
            geotop_arc_interior B\<^sub>1 E)
           (subspace_topology UNIV geotop_euclidean_topology
             (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>2) \<union>
              geotop_arc_interior B\<^sub>1 E))"
    and "top1_connected_on
           (geotop_polygon_interior (B\<^sub>2 \<union> B\<^sub>3) \<union>
            geotop_arc_interior B\<^sub>3 E)
           (subspace_topology UNIV geotop_euclidean_topology
             (geotop_polygon_interior (B\<^sub>2 \<union> B\<^sub>3) \<union>
              geotop_arc_interior B\<^sub>3 E))"
    and "geotop_separated UNIV geotop_euclidean_topology
           (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>2) \<union>
            geotop_arc_interior B\<^sub>1 E)
           (geotop_polygon_interior (B\<^sub>2 \<union> B\<^sub>3) \<union>
            geotop_arc_interior B\<^sub>3 E)"
proof -
  show "{C. \<exists>P\<in>geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>3) -
            geotop_arc_interior B\<^sub>2 E.
           C = geotop_component_at UNIV geotop_euclidean_topology
                (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>3) -
                 geotop_arc_interior B\<^sub>2 E) P}
         =
         {geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>2),
          geotop_polygon_interior (B\<^sub>2 \<union> B\<^sub>3)}"
    by (rule Theorem_GT_2_8(1)[OF h\<theta> hB\<^sub>2_inner])
  show "closure_on UNIV geotop_euclidean_topology
           (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>3)) =
         closure_on UNIV geotop_euclidean_topology
           (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>2))
         \<union> closure_on UNIV geotop_euclidean_topology
           (geotop_polygon_interior (B\<^sub>2 \<union> B\<^sub>3))"
    by (rule Theorem_GT_2_8(2)[OF h\<theta> hB\<^sub>2_inner])
  show "closure_on UNIV geotop_euclidean_topology
           (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>3)) - B\<^sub>2 =
         (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>2) \<union>
          geotop_arc_interior B\<^sub>1 E) \<union>
         (geotop_polygon_interior (B\<^sub>2 \<union> B\<^sub>3) \<union>
          geotop_arc_interior B\<^sub>3 E)"
    by (rule Theorem_GT_2_8(3)[OF h\<theta> hB\<^sub>2_inner])
  show "top1_connected_on
           (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>2) \<union>
            geotop_arc_interior B\<^sub>1 E)
           (subspace_topology UNIV geotop_euclidean_topology
             (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>2) \<union>
              geotop_arc_interior B\<^sub>1 E))"
    by (rule Theorem_GT_2_8(4)[OF h\<theta> hB\<^sub>2_inner])
  show "top1_connected_on
           (geotop_polygon_interior (B\<^sub>2 \<union> B\<^sub>3) \<union>
            geotop_arc_interior B\<^sub>3 E)
           (subspace_topology UNIV geotop_euclidean_topology
             (geotop_polygon_interior (B\<^sub>2 \<union> B\<^sub>3) \<union>
              geotop_arc_interior B\<^sub>3 E))"
    by (rule Theorem_GT_2_8(5)[OF h\<theta> hB\<^sub>2_inner])
  show "geotop_separated UNIV geotop_euclidean_topology
           (geotop_polygon_interior (B\<^sub>1 \<union> B\<^sub>2) \<union>
            geotop_arc_interior B\<^sub>1 E)
           (geotop_polygon_interior (B\<^sub>2 \<union> B\<^sub>3) \<union>
            geotop_arc_interior B\<^sub>3 E)"
    by (rule Theorem_GT_2_8(6)[OF h\<theta> hB\<^sub>2_inner])
qed

lemma geotop_polygon_disk_nonfree_boundary_triangle_split_free_count_prefix:
  fixes J \<theta> :: "(real^2) set" and K :: "(real^2) set set"
    and v\<^sub>0 v\<^sub>1 v\<^sub>2 :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_fin: "finite K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hT_gt2: "card {\<rho>\<in>K. geotop_simplex_dim \<rho> 2} > 2"
  assumes h\<theta>K: "\<theta> \<in> K"
  assumes h\<theta>2: "geotop_simplex_dim \<theta> 2"
  assumes h\<theta>_vertices: "geotop_simplex_vertices \<theta> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
  assumes hv\<^sub>0v\<^sub>1: "v\<^sub>0 \<noteq> v\<^sub>1"
  assumes hv\<^sub>2_not: "v\<^sub>2 \<notin> {v\<^sub>0, v\<^sub>1}"
  assumes hv\<^sub>0v\<^sub>1_sub_J: "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<subseteq> J"
  assumes h\<theta>_not_free: "\<not> geotop_free_2_simplex K J \<theta>"
  assumes h\<theta>_not_col: "\<not> collinear {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
  assumes hbase_segment_sub_J: "closed_segment v\<^sub>0 v\<^sub>1 \<subseteq> J"
  assumes hJ_meets_other_arc_interior:
    "J \<inter> geotop_arc_interior
      (closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1) {v\<^sub>0, v\<^sub>1} \<noteq> {}"
  assumes hJ_meets_\<theta>_frontier_other_arc_interior:
    "J \<inter> frontier \<theta> \<inter>
      geotop_arc_interior
        (closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1) {v\<^sub>0, v\<^sub>1} \<noteq> {}"
  assumes hJ_meets_nonbase_side_or_v\<^sub>2:
    "v\<^sub>2 \<in> J \<or>
      J \<inter> geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2} \<noteq> {} \<or>
      J \<inter> geotop_arc_interior (closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>1, v\<^sub>2} \<noteq> {}"
  assumes h\<theta>_frontier_polygon: "geotop_is_polygon (frontier \<theta>)"
  assumes h\<theta>_frontier_chord_polygon: "geotop_is_polygon (frontier \<theta>)"
  assumes hnot_both_nonbase_boundary_segments:
    "\<not> (closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> J
      \<and> closed_segment v\<^sub>1 v\<^sub>2 \<subseteq> J)"
  assumes hnonbase_boundary_segment_cases:
    "\<not> closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> J \<or>
      \<not> closed_segment v\<^sub>1 v\<^sub>2 \<subseteq> J"
  shows "card {\<sigma>\<^sub>2\<in>K. geotop_free_2_simplex K J \<sigma>\<^sub>2} \<ge> 2"
  (**
    Moise Figure 3.2 split lemma.  The preceding bookkeeping has isolated the
    nonfree boundary triangle, shown that the polygon frontier meets the
    opposite arc away from the base edge, and ruled out both opposite sides
    being boundary edges.  The remaining planar step constructs the two subdisk
    complexes along the chord \<open>v\<^sub>0v\<^sub>2\<close>, applies the strong induction hypothesis
    to both, and transfers the resulting free triangles back to \<open>K\<close>. **)
proof -
  have hv\<^sub>0v\<^sub>2: "v\<^sub>0 \<noteq> v\<^sub>2"
    using hv\<^sub>2_not by (by100 blast)
  have hv\<^sub>1v\<^sub>2: "v\<^sub>1 \<noteq> v\<^sub>2"
    using hv\<^sub>2_not by (by100 blast)
  have hnonbase_edge_face_data:
    "geotop_is_edge (geotop_convex_hull {v\<^sub>0, v\<^sub>2}) \<and>
      geotop_is_face (geotop_convex_hull {v\<^sub>0, v\<^sub>2}) \<theta> \<and>
      geotop_is_edge (geotop_convex_hull {v\<^sub>1, v\<^sub>2}) \<and>
      geotop_is_face (geotop_convex_hull {v\<^sub>1, v\<^sub>2}) \<theta>"
    by (rule geotop_2simplex_vertices_other_edge_faces_prefix
        [OF h\<theta>_vertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
  have hface_closed_K:
    "\<forall>\<rho>\<in>K. \<forall>\<eta>. geotop_is_face \<eta> \<rho> \<longrightarrow> \<eta> \<in> K"
    using hK unfolding geotop_is_complex_def by (by100 blast)
  have hchord_edge_K: "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<in> K"
    using hface_closed_K h\<theta>K hnonbase_edge_face_data by (by100 blast)
  have hside_edge_K: "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<in> K"
    using hface_closed_K h\<theta>K hnonbase_edge_face_data by (by100 blast)
  have hchord_hull_segment_eq:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>2} = closed_segment v\<^sub>0 v\<^sub>2"
    using segment_convex_hull[of v\<^sub>0 v\<^sub>2] geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>2}"]
    by (by100 simp)
  have hside_hull_segment_eq:
    "geotop_convex_hull {v\<^sub>1, v\<^sub>2} = closed_segment v\<^sub>1 v\<^sub>2"
    using segment_convex_hull[of v\<^sub>1 v\<^sub>2] geotop_convex_hull_eq_HOL[of "{v\<^sub>1, v\<^sub>2}"]
    by (by100 simp)
  have hchord_contact_forces_boundary:
    "J \<inter> geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2} \<noteq> {}
      \<Longrightarrow> closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> J"
  proof (rule ccontr)
    assume hcontact:
      "J \<inter> geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2} \<noteq> {}"
    assume hnot_boundary: "\<not> closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> J"
    have hchord_edge: "geotop_is_edge (geotop_convex_hull {v\<^sub>0, v\<^sub>2})"
      using hnonbase_edge_face_data by (by100 blast)
    have hchord_face: "geotop_is_face (geotop_convex_hull {v\<^sub>0, v\<^sub>2}) \<theta>"
      using hnonbase_edge_face_data by (by100 blast)
    have hchord_disj:
      "J \<inter> geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2} = {}"
      by (rule geotop_polygon_disk_nonboundary_segment_arc_interior_disjoint_prefix
          [OF hJ hK hK_poly hv\<^sub>0v\<^sub>2 hchord_hull_segment_eq hchord_edge_K
            hchord_edge h\<theta>K h\<theta>2 hchord_face hnot_boundary])
    show False
      using hcontact hchord_disj by (by100 blast)
  qed
  have hside_contact_forces_boundary:
    "J \<inter> geotop_arc_interior (closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>1, v\<^sub>2} \<noteq> {}
      \<Longrightarrow> closed_segment v\<^sub>1 v\<^sub>2 \<subseteq> J"
  proof (rule ccontr)
    assume hcontact:
      "J \<inter> geotop_arc_interior (closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>1, v\<^sub>2} \<noteq> {}"
    assume hnot_boundary: "\<not> closed_segment v\<^sub>1 v\<^sub>2 \<subseteq> J"
    have hside_edge: "geotop_is_edge (geotop_convex_hull {v\<^sub>1, v\<^sub>2})"
      using hnonbase_edge_face_data by (by100 blast)
    have hside_face: "geotop_is_face (geotop_convex_hull {v\<^sub>1, v\<^sub>2}) \<theta>"
      using hnonbase_edge_face_data by (by100 blast)
    have hside_disj:
      "J \<inter> geotop_arc_interior (closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>1, v\<^sub>2} = {}"
      by (rule geotop_polygon_disk_nonboundary_segment_arc_interior_disjoint_prefix
          [OF hJ hK hK_poly hv\<^sub>1v\<^sub>2 hside_hull_segment_eq hside_edge_K
            hside_edge h\<theta>K h\<theta>2 hside_face hnot_boundary])
    show False
      using hcontact hside_disj by (by100 blast)
  qed
  have hv\<^sub>2J: "v\<^sub>2 \<in> J"
  proof -
    have hv\<^sub>2_chord: "v\<^sub>2 \<in> closed_segment v\<^sub>0 v\<^sub>2"
      by (by100 simp)
    have hv\<^sub>2_side: "v\<^sub>2 \<in> closed_segment v\<^sub>1 v\<^sub>2"
      by (by100 simp)
    show ?thesis
    proof (rule disjE[OF hJ_meets_nonbase_side_or_v\<^sub>2])
      assume "v\<^sub>2 \<in> J"
      thus ?thesis .
    next
      assume hrest:
        "J \<inter> geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2} \<noteq> {} \<or>
         J \<inter> geotop_arc_interior (closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>1, v\<^sub>2} \<noteq> {}"
      show ?thesis
      proof (rule disjE[OF hrest])
        assume hcontact:
          "J \<inter> geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2} \<noteq> {}"
        have hsub: "closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> J"
          by (rule hchord_contact_forces_boundary[OF hcontact])
        show ?thesis
          using hsub hv\<^sub>2_chord by (by100 blast)
      next
        assume hcontact:
          "J \<inter> geotop_arc_interior (closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>1, v\<^sub>2} \<noteq> {}"
        have hsub: "closed_segment v\<^sub>1 v\<^sub>2 \<subseteq> J"
          by (rule hside_contact_forces_boundary[OF hcontact])
        show ?thesis
          using hsub hv\<^sub>2_side by (by100 blast)
      qed
    qed
  qed
  have hv\<^sub>0J: "v\<^sub>0 \<in> J"
  proof -
    have "v\<^sub>0 \<in> closed_segment v\<^sub>0 v\<^sub>1"
      by (by100 simp)
    thus ?thesis
      using hbase_segment_sub_J by (by100 blast)
  qed
  have hv\<^sub>1J: "v\<^sub>1 \<in> J"
  proof -
    have "v\<^sub>1 \<in> closed_segment v\<^sub>0 v\<^sub>1"
      by (by100 simp)
    thus ?thesis
      using hbase_segment_sub_J by (by100 blast)
  qed
  let ?Etheta = "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
  have h\<theta>_vertices_chord_order:
    "geotop_simplex_vertices \<theta> {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
  proof -
    have "{v\<^sub>0, v\<^sub>2, v\<^sub>1} = {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
      by (by100 blast)
    thus ?thesis using h\<theta>_vertices by (by100 simp)
  qed
  have hv\<^sub>1_not_chord: "v\<^sub>1 \<notin> {v\<^sub>0, v\<^sub>2}"
    using hv\<^sub>0v\<^sub>1 hv\<^sub>1v\<^sub>2 by (by100 blast)
  have hbase_edge_face_data:
    "geotop_is_edge (geotop_convex_hull {v\<^sub>0, v\<^sub>1}) \<and>
      geotop_is_face (geotop_convex_hull {v\<^sub>0, v\<^sub>1}) \<theta>"
  proof -
    have hdata:
      "geotop_is_edge (geotop_convex_hull {v\<^sub>0, v\<^sub>1}) \<and>
        geotop_is_face (geotop_convex_hull {v\<^sub>0, v\<^sub>1}) \<theta> \<and>
        geotop_is_edge (geotop_convex_hull {v\<^sub>2, v\<^sub>1}) \<and>
        geotop_is_face (geotop_convex_hull {v\<^sub>2, v\<^sub>1}) \<theta>"
      by (rule geotop_2simplex_vertices_other_edge_faces_prefix
          [OF h\<theta>_vertices_chord_order hv\<^sub>0v\<^sub>2 hv\<^sub>1_not_chord])
    show ?thesis using hdata by (by100 blast)
  qed
  have hbase_edge_K: "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<in> K"
    using hface_closed_K h\<theta>K hbase_edge_face_data by (by100 blast)
  have hbase_edge_selected:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<in>
      {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
    using hbase_edge_K hbase_edge_face_data hv\<^sub>0v\<^sub>1_sub_J by (by100 blast)
  have hchord_edge_selected_if:
    "closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> J \<Longrightarrow>
      geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<in> ?Etheta"
    using hchord_edge_K hnonbase_edge_face_data hchord_hull_segment_eq by (by100 blast)
  have hside_edge_selected_if:
    "closed_segment v\<^sub>1 v\<^sub>2 \<subseteq> J \<Longrightarrow>
      geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<in> ?Etheta"
    using hside_edge_K hnonbase_edge_face_data hside_hull_segment_eq by (by100 blast)
  have hEtheta_fin: "finite ?Etheta"
    using hK_fin by (by100 simp)
  have hEtheta_card_le3: "card ?Etheta \<le> 3"
  proof -
    have hE: "finite ?Etheta \<and> card ?Etheta \<le> 3"
      by (rule geotop_selected_boundary_edge_set_card_le3_prefix[OF h\<theta>2])
    show ?thesis
      using hE by (by100 simp)
  qed
  have hEtheta_card_ne3: "card ?Etheta \<noteq> 3"
  proof -
    have hT_gt1: "card {\<rho>\<in>K. geotop_simplex_dim \<rho> 2} > 1"
      using hT_gt2 by (by100 simp)
    show ?thesis
      by (rule geotop_polygon_disk_multi_2simplex_not_three_boundary_edges_prefix
          [OF hJ hK hK_poly h\<theta>K h\<theta>2 hT_gt1])
  qed
  have hEtheta_card_le2: "card ?Etheta \<le> 2"
    using hEtheta_card_le3 hEtheta_card_ne3 by (by100 linarith)
  have hEtheta_allowed:
    "?Etheta = {} \<or>
     (\<exists>e. ?Etheta = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<theta> \<and> e \<subseteq> J) \<or>
     (\<exists>e1 e2. ?Etheta = {e1, e2} \<and> e1 \<noteq> e2 \<and>
        geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
        geotop_is_face e1 \<theta> \<and> geotop_is_face e2 \<theta> \<and>
        e1 \<subseteq> J \<and> e2 \<subseteq> J)"
    by (rule geotop_selected_boundary_edge_set_allowed_card_le2_prefix
        [OF hEtheta_fin hEtheta_card_le2])
  have hEtheta_subset_K: "?Etheta \<subseteq> K"
    by (by100 simp)
  have hEtheta_union_sub_\<theta>J: "\<Union>?Etheta \<subseteq> \<theta> \<inter> J"
    by (rule geotop_selected_boundary_edge_set_union_subset_contact_prefix)
  have h\<theta>_contact_outside_selected:
    "\<exists>x. x \<in> \<theta> \<inter> J \<and> x \<notin> \<Union>?Etheta"
    by (rule geotop_nonfree_selected_edges_contact_outside_prefix
        [OF h\<theta>K h\<theta>2 hEtheta_subset_K hEtheta_allowed h\<theta>_not_free
          hEtheta_union_sub_\<theta>J])
  have h\<theta>J_sub_named_edges:
    "\<theta> \<inter> J \<subseteq>
      geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<union>
      geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<union>
      geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
    by (rule geotop_2simplex_polygon_boundary_inter_subset_three_edge_hulls_prefix
        [OF hJ h\<theta>K h\<theta>2 hK_poly h\<theta>_vertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
  have hchord_boundary_forces_side_boundary:
    "closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> J \<Longrightarrow> closed_segment v\<^sub>1 v\<^sub>2 \<subseteq> J"
  proof -
    assume hchord_sub: "closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> J"
    have hchord_selected: "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<in> ?Etheta"
      by (rule hchord_edge_selected_if[OF hchord_sub])
    obtain x where hx\<theta>J: "x \<in> \<theta> \<inter> J" and hx_not_E: "x \<notin> \<Union>?Etheta"
      using h\<theta>_contact_outside_selected by (elim exE conjE)
    have hxJ: "x \<in> J"
      using hx\<theta>J by (by100 blast)
    have hbase_sub_E: "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<subseteq> \<Union>?Etheta"
      using hbase_edge_selected by (by100 blast)
    have hchord_sub_E: "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> \<Union>?Etheta"
      using hchord_selected by (by100 blast)
    have hx_not_base_hull: "x \<notin> geotop_convex_hull {v\<^sub>0, v\<^sub>1}"
      using hx_not_E hbase_sub_E by (by100 blast)
    have hx_not_chord_hull: "x \<notin> geotop_convex_hull {v\<^sub>0, v\<^sub>2}"
      using hx_not_E hchord_sub_E by (by100 blast)
    have hx_side_hull: "x \<in> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
      using h\<theta>J_sub_named_edges hx\<theta>J hx_not_base_hull hx_not_chord_hull
      by (by100 blast)
    have hx_side_segment: "x \<in> closed_segment v\<^sub>1 v\<^sub>2"
      using hx_side_hull hside_hull_segment_eq by (by100 simp)
    have hv\<^sub>1_base_HOL: "v\<^sub>1 \<in> convex hull {v\<^sub>0, v\<^sub>1}"
      by (rule hull_inc) (by100 simp)
    have hv\<^sub>1_base_hull: "v\<^sub>1 \<in> geotop_convex_hull {v\<^sub>0, v\<^sub>1}"
      using hv\<^sub>1_base_HOL geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>1}"] by (by100 simp)
    have hv\<^sub>2_chord_HOL: "v\<^sub>2 \<in> convex hull {v\<^sub>0, v\<^sub>2}"
      by (rule hull_inc) (by100 simp)
    have hv\<^sub>2_chord_hull: "v\<^sub>2 \<in> geotop_convex_hull {v\<^sub>0, v\<^sub>2}"
      using hv\<^sub>2_chord_HOL geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>2}"] by (by100 simp)
    have hx_ne_v\<^sub>1: "x \<noteq> v\<^sub>1"
      using hx_not_base_hull hv\<^sub>1_base_hull by (by100 blast)
    have hx_ne_v\<^sub>2: "x \<noteq> v\<^sub>2"
      using hx_not_chord_hull hv\<^sub>2_chord_hull by (by100 blast)
    have hx_side_arc:
      "x \<in> geotop_arc_interior (closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>1, v\<^sub>2}"
      using hx_side_segment hx_ne_v\<^sub>1 hx_ne_v\<^sub>2
      unfolding geotop_arc_interior_def by (by100 blast)
    have hcontact:
      "J \<inter> geotop_arc_interior (closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>1, v\<^sub>2} \<noteq> {}"
      using hxJ hx_side_arc by (by100 blast)
    show ?thesis
      by (rule hside_contact_forces_boundary[OF hcontact])
  qed
  have hside_boundary_forces_chord_boundary:
    "closed_segment v\<^sub>1 v\<^sub>2 \<subseteq> J \<Longrightarrow> closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> J"
  proof -
    assume hside_sub: "closed_segment v\<^sub>1 v\<^sub>2 \<subseteq> J"
    have hside_selected: "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<in> ?Etheta"
      by (rule hside_edge_selected_if[OF hside_sub])
    obtain x where hx\<theta>J: "x \<in> \<theta> \<inter> J" and hx_not_E: "x \<notin> \<Union>?Etheta"
      using h\<theta>_contact_outside_selected by (elim exE conjE)
    have hxJ: "x \<in> J"
      using hx\<theta>J by (by100 blast)
    have hbase_sub_E: "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<subseteq> \<Union>?Etheta"
      using hbase_edge_selected by (by100 blast)
    have hside_sub_E: "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> \<Union>?Etheta"
      using hside_selected by (by100 blast)
    have hx_not_base_hull: "x \<notin> geotop_convex_hull {v\<^sub>0, v\<^sub>1}"
      using hx_not_E hbase_sub_E by (by100 blast)
    have hx_not_side_hull: "x \<notin> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
      using hx_not_E hside_sub_E by (by100 blast)
    have hx_chord_hull: "x \<in> geotop_convex_hull {v\<^sub>0, v\<^sub>2}"
      using h\<theta>J_sub_named_edges hx\<theta>J hx_not_base_hull hx_not_side_hull
      by (by100 blast)
    have hx_chord_segment: "x \<in> closed_segment v\<^sub>0 v\<^sub>2"
      using hx_chord_hull hchord_hull_segment_eq by (by100 simp)
    have hv\<^sub>0_base_HOL: "v\<^sub>0 \<in> convex hull {v\<^sub>0, v\<^sub>1}"
      by (rule hull_inc) (by100 simp)
    have hv\<^sub>0_base_hull: "v\<^sub>0 \<in> geotop_convex_hull {v\<^sub>0, v\<^sub>1}"
      using hv\<^sub>0_base_HOL geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>1}"] by (by100 simp)
    have hv\<^sub>2_side_HOL: "v\<^sub>2 \<in> convex hull {v\<^sub>1, v\<^sub>2}"
      by (rule hull_inc) (by100 simp)
    have hv\<^sub>2_side_hull: "v\<^sub>2 \<in> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
      using hv\<^sub>2_side_HOL geotop_convex_hull_eq_HOL[of "{v\<^sub>1, v\<^sub>2}"] by (by100 simp)
    have hx_ne_v\<^sub>0: "x \<noteq> v\<^sub>0"
      using hx_not_base_hull hv\<^sub>0_base_hull by (by100 blast)
    have hx_ne_v\<^sub>2: "x \<noteq> v\<^sub>2"
      using hx_not_side_hull hv\<^sub>2_side_hull by (by100 blast)
    have hx_chord_arc:
      "x \<in> geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2}"
      using hx_chord_segment hx_ne_v\<^sub>0 hx_ne_v\<^sub>2
      unfolding geotop_arc_interior_def by (by100 blast)
    have hcontact:
      "J \<inter> geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2} \<noteq> {}"
      using hxJ hx_chord_arc by (by100 blast)
    show ?thesis
      by (rule hchord_contact_forces_boundary[OF hcontact])
  qed
  have hnot_chord_boundary: "\<not> closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> J"
  proof
    assume hchord_sub: "closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> J"
    have hside_sub: "closed_segment v\<^sub>1 v\<^sub>2 \<subseteq> J"
      by (rule hchord_boundary_forces_side_boundary[OF hchord_sub])
    show False
      using hnot_both_nonbase_boundary_segments hchord_sub hside_sub by (by100 blast)
  qed
  have hnot_side_boundary: "\<not> closed_segment v\<^sub>1 v\<^sub>2 \<subseteq> J"
  proof
    assume hside_sub: "closed_segment v\<^sub>1 v\<^sub>2 \<subseteq> J"
    have hchord_sub: "closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> J"
      by (rule hside_boundary_forces_chord_boundary[OF hside_sub])
    show False
      using hnot_both_nonbase_boundary_segments hchord_sub hside_sub by (by100 blast)
  qed
  have hchord_edge: "geotop_is_edge (geotop_convex_hull {v\<^sub>0, v\<^sub>2})"
    using hnonbase_edge_face_data by (by100 blast)
  have hchord_face: "geotop_is_face (geotop_convex_hull {v\<^sub>0, v\<^sub>2}) \<theta>"
    using hnonbase_edge_face_data by (by100 blast)
  have hside_edge: "geotop_is_edge (geotop_convex_hull {v\<^sub>1, v\<^sub>2})"
    using hnonbase_edge_face_data by (by100 blast)
  have hside_face: "geotop_is_face (geotop_convex_hull {v\<^sub>1, v\<^sub>2}) \<theta>"
    using hnonbase_edge_face_data by (by100 blast)
  have hchord_arc_interior_sub_polygon_interior:
    "geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2} \<subseteq>
      geotop_polygon_interior J"
    by (rule geotop_polygon_disk_nonboundary_segment_arc_interior_subset_polygon_interior_prefix
        [OF hJ hK hK_poly hv\<^sub>0v\<^sub>2 hchord_hull_segment_eq hchord_edge_K
          hchord_edge h\<theta>K h\<theta>2 hchord_face hnot_chord_boundary])
  have hside_arc_interior_sub_polygon_interior:
    "geotop_arc_interior (closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>1, v\<^sub>2} \<subseteq>
      geotop_polygon_interior J"
    by (rule geotop_polygon_disk_nonboundary_segment_arc_interior_subset_polygon_interior_prefix
        [OF hJ hK hK_poly hv\<^sub>1v\<^sub>2 hside_hull_segment_eq hside_edge_K
          hside_edge h\<theta>K h\<theta>2 hside_face hnot_side_boundary])
  have hchord_arc_interior_disjoint_J:
    "J \<inter> geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2} = {}"
  proof (rule ccontr)
    assume hne:
      "J \<inter> geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2} \<noteq> {}"
    have "closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> J"
      by (rule hchord_contact_forces_boundary[OF hne])
    thus False
      using hnot_chord_boundary by (by100 blast)
  qed
  have hside_arc_interior_disjoint_J:
    "J \<inter> geotop_arc_interior (closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>1, v\<^sub>2} = {}"
  proof (rule ccontr)
    assume hne:
      "J \<inter> geotop_arc_interior (closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>1, v\<^sub>2} \<noteq> {}"
    have "closed_segment v\<^sub>1 v\<^sub>2 \<subseteq> J"
      by (rule hside_contact_forces_boundary[OF hne])
    thus False
      using hnot_side_boundary by (by100 blast)
  qed
  have hchord_segment_inter_J:
    "closed_segment v\<^sub>0 v\<^sub>2 \<inter> J = {v\<^sub>0, v\<^sub>2}"
  proof
    show "closed_segment v\<^sub>0 v\<^sub>2 \<inter> J \<subseteq> {v\<^sub>0, v\<^sub>2}"
    proof
      fix x
      assume hx: "x \<in> closed_segment v\<^sub>0 v\<^sub>2 \<inter> J"
      have hxseg: "x \<in> closed_segment v\<^sub>0 v\<^sub>2"
        using hx by (by100 blast)
      have hxJ: "x \<in> J"
        using hx by (by100 blast)
      have hx_not_arc:
        "x \<notin> geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2}"
        using hchord_arc_interior_disjoint_J hxJ by (by100 blast)
      show "x \<in> {v\<^sub>0, v\<^sub>2}"
        using hxseg hx_not_arc unfolding geotop_arc_interior_def by (by100 blast)
    qed
    show "{v\<^sub>0, v\<^sub>2} \<subseteq> closed_segment v\<^sub>0 v\<^sub>2 \<inter> J"
      using hv\<^sub>0J hv\<^sub>2J by (by100 simp)
  qed
  have hside_segment_inter_J:
    "closed_segment v\<^sub>1 v\<^sub>2 \<inter> J = {v\<^sub>1, v\<^sub>2}"
  proof
    show "closed_segment v\<^sub>1 v\<^sub>2 \<inter> J \<subseteq> {v\<^sub>1, v\<^sub>2}"
    proof
      fix x
      assume hx: "x \<in> closed_segment v\<^sub>1 v\<^sub>2 \<inter> J"
      have hxseg: "x \<in> closed_segment v\<^sub>1 v\<^sub>2"
        using hx by (by100 blast)
      have hxJ: "x \<in> J"
        using hx by (by100 blast)
      have hx_not_arc:
        "x \<notin> geotop_arc_interior (closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>1, v\<^sub>2}"
        using hside_arc_interior_disjoint_J hxJ by (by100 blast)
      show "x \<in> {v\<^sub>1, v\<^sub>2}"
        using hxseg hx_not_arc unfolding geotop_arc_interior_def by (by100 blast)
    qed
    show "{v\<^sub>1, v\<^sub>2} \<subseteq> closed_segment v\<^sub>1 v\<^sub>2 \<inter> J"
      using hv\<^sub>1J hv\<^sub>2J by (by100 simp)
  qed
  have hchord_edge_broken_line:
    "geotop_is_broken_line (closed_segment v\<^sub>0 v\<^sub>2)"
    by (rule geotop_closed_segment_is_broken_line[OF hv\<^sub>0v\<^sub>2])
  have hchord_edge_arc:
    "geotop_arc_endpoints (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2}"
    by (rule geotop_closed_segment_arc_endpoints_prefix[OF hv\<^sub>0v\<^sub>2])
  have h\<theta>_not_col_chord: "\<not> collinear {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
  proof -
    have "{v\<^sub>0, v\<^sub>1, v\<^sub>2} = {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
      by (by100 blast)
    thus ?thesis
      using h\<theta>_not_col by (by100 simp)
  qed
  have hv\<^sub>2v\<^sub>1: "v\<^sub>2 \<noteq> v\<^sub>1"
    using hv\<^sub>1v\<^sub>2 by (by100 blast)
  have hbase_side_edge_broken_line:
    "geotop_is_broken_line
      (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2)"
    by (rule geotop_two_segment_join_broken_line_prefix
        [OF hv\<^sub>0v\<^sub>1 hv\<^sub>2v\<^sub>1 h\<theta>_not_col_chord])
  have hbase_side_edge_arc:
    "geotop_arc_endpoints
      (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>0, v\<^sub>2}"
    by (rule geotop_two_segment_join_arc_endpoints_prefix
        [OF hv\<^sub>0v\<^sub>1 hv\<^sub>2v\<^sub>1 h\<theta>_not_col_chord])
  have hchord_base_side_arc_interiors_disjoint:
    "geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2} \<inter>
      geotop_arc_interior
        (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>0, v\<^sub>2} =
      {}"
    by (rule geotop_triangle_edge_two_edge_arc_interiors_disjoint_prefix
        [OF h\<theta>_not_col_chord])
  have htriangle_boundary_chord_polygon:
    "geotop_is_polygon
      (closed_segment v\<^sub>0 v\<^sub>2 \<union>
        (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2))"
    by (rule pair_of_arcs_is_polygon
        [OF hchord_edge_broken_line hbase_side_edge_broken_line
          hchord_edge_arc hbase_side_edge_arc hchord_base_side_arc_interiors_disjoint])
  have h\<theta>_frontier_chord_segments:
    "frontier \<theta> =
      closed_segment v\<^sub>0 v\<^sub>2 \<union>
        (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2)"
    by (rule geotop_2simplex_vertices_frontier_eq_base_union_two_segments_prefix
        [OF h\<theta>_vertices_chord_order hv\<^sub>0v\<^sub>2 hv\<^sub>1_not_chord])
  have hchord_base_side_inter:
    "closed_segment v\<^sub>0 v\<^sub>2 \<inter>
      (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2) = {v\<^sub>0, v\<^sub>2}"
  proof
    show "closed_segment v\<^sub>0 v\<^sub>2 \<inter>
        (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2) \<subseteq> {v\<^sub>0, v\<^sub>2}"
    proof
      fix x
      assume hx:
        "x \<in> closed_segment v\<^sub>0 v\<^sub>2 \<inter>
          (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2)"
      have hx_chord: "x \<in> closed_segment v\<^sub>0 v\<^sub>2"
        using hx by (by100 blast)
      have hx_base_side: "x \<in> closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2"
        using hx by (by100 blast)
      show "x \<in> {v\<^sub>0, v\<^sub>2}"
      proof (rule ccontr)
        assume hx_not: "x \<notin> {v\<^sub>0, v\<^sub>2}"
        have hx_chord_int:
          "x \<in> geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2}"
          using hx_chord hx_not unfolding geotop_arc_interior_def by (by100 blast)
        have hx_base_side_int:
          "x \<in> geotop_arc_interior
            (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>0, v\<^sub>2}"
          using hx_base_side hx_not unfolding geotop_arc_interior_def by (by100 blast)
        have "x \<in>
          geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2} \<inter>
          geotop_arc_interior
            (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>0, v\<^sub>2}"
          using hx_chord_int hx_base_side_int by (by100 blast)
        thus False
          using hchord_base_side_arc_interiors_disjoint by (by100 blast)
      qed
    qed
    show "{v\<^sub>0, v\<^sub>2} \<subseteq> closed_segment v\<^sub>0 v\<^sub>2 \<inter>
        (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2)"
      by (by100 simp)
  qed
  have h\<theta>_frontier_inter_J:
    "frontier \<theta> \<inter> J = closed_segment v\<^sub>0 v\<^sub>1 \<union> {v\<^sub>2}"
  proof
    have hv\<^sub>0_base: "v\<^sub>0 \<in> closed_segment v\<^sub>0 v\<^sub>1"
      by (by100 simp)
    have hv\<^sub>1_base: "v\<^sub>1 \<in> closed_segment v\<^sub>0 v\<^sub>1"
      by (by100 simp)
    show "frontier \<theta> \<inter> J \<subseteq> closed_segment v\<^sub>0 v\<^sub>1 \<union> {v\<^sub>2}"
    proof
      fix x
      assume hx: "x \<in> frontier \<theta> \<inter> J"
      have hxfront: "x \<in> frontier \<theta>"
        using hx by (by100 blast)
      have hxJ: "x \<in> J"
        using hx by (by100 blast)
      have hxsplit:
        "x \<in> closed_segment v\<^sub>0 v\<^sub>2 \<or>
         x \<in> closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2"
        using hxfront h\<theta>_frontier_chord_segments by (by100 blast)
      show "x \<in> closed_segment v\<^sub>0 v\<^sub>1 \<union> {v\<^sub>2}"
      proof (rule disjE[OF hxsplit])
        assume hxchord: "x \<in> closed_segment v\<^sub>0 v\<^sub>2"
        have "x \<in> closed_segment v\<^sub>0 v\<^sub>2 \<inter> J"
          using hxchord hxJ by (by100 blast)
        hence hxend: "x \<in> {v\<^sub>0, v\<^sub>2}"
          using hchord_segment_inter_J by (by100 simp)
        show ?thesis
          using hxend hv\<^sub>0_base by (by100 blast)
      next
        assume hxbase_side:
          "x \<in> closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2"
        have hxbase_side_cases:
          "x \<in> closed_segment v\<^sub>0 v\<^sub>1 \<or> x \<in> closed_segment v\<^sub>1 v\<^sub>2"
          using hxbase_side by (by100 blast)
        show ?thesis
        proof (rule disjE[OF hxbase_side_cases])
          assume hxbase: "x \<in> closed_segment v\<^sub>0 v\<^sub>1"
          show ?thesis
            using hxbase by (by100 blast)
        next
          assume hxside: "x \<in> closed_segment v\<^sub>1 v\<^sub>2"
          have "x \<in> closed_segment v\<^sub>1 v\<^sub>2 \<inter> J"
            using hxside hxJ by (by100 blast)
          hence hxend: "x \<in> {v\<^sub>1, v\<^sub>2}"
            using hside_segment_inter_J by (by100 simp)
          show ?thesis
            using hxend hv\<^sub>1_base by (by100 blast)
        qed
      qed
    qed
    show "closed_segment v\<^sub>0 v\<^sub>1 \<union> {v\<^sub>2} \<subseteq> frontier \<theta> \<inter> J"
    proof
      fix x
      assume hx: "x \<in> closed_segment v\<^sub>0 v\<^sub>1 \<union> {v\<^sub>2}"
      have hxcases: "x \<in> closed_segment v\<^sub>0 v\<^sub>1 \<or> x \<in> {v\<^sub>2}"
        using hx by (by100 blast)
      show "x \<in> frontier \<theta> \<inter> J"
      proof (rule disjE[OF hxcases])
        assume hxbase: "x \<in> closed_segment v\<^sub>0 v\<^sub>1"
        have hxfront: "x \<in> frontier \<theta>"
          using hxbase h\<theta>_frontier_chord_segments by (by100 blast)
        have hxJ: "x \<in> J"
          using hxbase hbase_segment_sub_J by (by100 blast)
        show ?thesis
          using hxfront hxJ by (by100 blast)
      next
        assume hxv\<^sub>2: "x \<in> {v\<^sub>2}"
        have hxfront: "x \<in> frontier \<theta>"
          using hxv\<^sub>2 h\<theta>_frontier_chord_segments by (by100 simp)
        have hxJ: "x \<in> J"
          using hxv\<^sub>2 hv\<^sub>2J by (by100 blast)
        show ?thesis
          using hxfront hxJ by (by100 blast)
      qed
    qed
  qed
  have h\<theta>_inter_J:
    "\<theta> \<inter> J = closed_segment v\<^sub>0 v\<^sub>1 \<union> {v\<^sub>2}"
  proof
    show "\<theta> \<inter> J \<subseteq> closed_segment v\<^sub>0 v\<^sub>1 \<union> {v\<^sub>2}"
    proof
      fix x
      assume hx: "x \<in> \<theta> \<inter> J"
      have hx\<theta>: "x \<in> \<theta>"
        using hx by (by100 blast)
      have hxJ: "x \<in> J"
        using hx by (by100 blast)
      have hxfront: "x \<in> frontier \<theta>"
        by (rule geotop_polygon_boundary_point_in_2simplex_frontier_prefix
            [OF hJ h\<theta>K h\<theta>2 hK_poly hx\<theta> hxJ])
      have "x \<in> frontier \<theta> \<inter> J"
        using hxfront hxJ by (by100 blast)
      thus "x \<in> closed_segment v\<^sub>0 v\<^sub>1 \<union> {v\<^sub>2}"
        using h\<theta>_frontier_inter_J by (by100 simp)
    qed
    show "closed_segment v\<^sub>0 v\<^sub>1 \<union> {v\<^sub>2} \<subseteq> \<theta> \<inter> J"
    proof
      fix x
      assume hx: "x \<in> closed_segment v\<^sub>0 v\<^sub>1 \<union> {v\<^sub>2}"
      have hxfrontJ: "x \<in> frontier \<theta> \<inter> J"
        using hx h\<theta>_frontier_inter_J by (by100 simp)
      have hxfront: "x \<in> frontier \<theta>"
        using hxfrontJ by (by100 blast)
      have hxJ: "x \<in> J"
        using hxfrontJ by (by100 blast)
      have h\<theta>closed: "closed \<theta>"
        by (rule geotop_simplex_dim_closed[OF h\<theta>2])
      have hxclosure: "x \<in> closure \<theta>"
        using hxfront unfolding Elementary_Topology.frontier_def by (by100 blast)
      have hx\<theta>: "x \<in> \<theta>"
        using h\<theta>closed hxclosure by (by100 simp)
      show "x \<in> \<theta> \<inter> J"
        using hx\<theta> hxJ by (by100 blast)
    qed
  qed
  have hv\<^sub>2_not_base_segment: "v\<^sub>2 \<notin> closed_segment v\<^sub>0 v\<^sub>1"
  proof
    assume hv\<^sub>2_base: "v\<^sub>2 \<in> closed_segment v\<^sub>0 v\<^sub>1"
    have hbase_col: "collinear (closed_segment v\<^sub>0 v\<^sub>1)"
      by (rule collinear_closed_segment)
    have hverts_sub: "{v\<^sub>0, v\<^sub>1, v\<^sub>2} \<subseteq> closed_segment v\<^sub>0 v\<^sub>1"
      using hv\<^sub>2_base by (by100 simp)
    have hcol: "collinear {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
      by (rule collinear_subset[OF hbase_col hverts_sub])
    have "{v\<^sub>0, v\<^sub>1, v\<^sub>2} = {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
      by (by100 blast)
    thus False
      using h\<theta>_not_col hcol by (by100 simp)
  qed
  have hbase_segment_inter_v\<^sub>2_empty:
    "closed_segment v\<^sub>0 v\<^sub>1 \<inter> {v\<^sub>2} = {}"
    using hv\<^sub>2_not_base_segment by (by100 blast)
  have h\<theta>_inter_J_minus_base:
    "(\<theta> \<inter> J) - closed_segment v\<^sub>0 v\<^sub>1 = {v\<^sub>2}"
    using h\<theta>_inter_J hv\<^sub>2_not_base_segment by (by100 blast)
  have hchord_polygon_cut_data:
    "v\<^sub>0 \<in> J \<and> v\<^sub>2 \<in> J
      \<and> geotop_is_broken_line (closed_segment v\<^sub>0 v\<^sub>2)
      \<and> geotop_arc_endpoints (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2}
      \<and> closed_segment v\<^sub>0 v\<^sub>2 \<inter> J = {v\<^sub>0, v\<^sub>2}
      \<and> geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2}
          \<subseteq> geotop_polygon_interior J"
    by (intro conjI hv\<^sub>0J hv\<^sub>2J hchord_edge_broken_line hchord_edge_arc
        hchord_segment_inter_J hchord_arc_interior_sub_polygon_interior)
  have hchord_segment_sub_polyhedron:
    "closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> geotop_polyhedron K"
    using hchord_edge_K hchord_hull_segment_eq
    unfolding geotop_polyhedron_def by (by100 blast)
  have hchord_arc_interior_sub_polyhedron:
    "geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2}
      \<subseteq> geotop_polyhedron K"
    using hchord_segment_sub_polyhedron
    unfolding geotop_arc_interior_def by (by100 blast)
  show ?thesis
    sorry
qed

lemma geotop_polygon_disk_nonfree_boundary_triangle_decomposition_free_count_prefix:
  fixes J \<theta> :: "(real^2) set" and K :: "(real^2) set set"
    and v\<^sub>0 v\<^sub>1 v\<^sub>2 :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_fin: "finite K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hT_gt2: "card {\<rho>\<in>K. geotop_simplex_dim \<rho> 2} > 2"
  assumes h\<theta>K: "\<theta> \<in> K"
  assumes h\<theta>2: "geotop_simplex_dim \<theta> 2"
  assumes h\<theta>_vertices: "geotop_simplex_vertices \<theta> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
  assumes hv\<^sub>0v\<^sub>1: "v\<^sub>0 \<noteq> v\<^sub>1"
  assumes hv\<^sub>2_not: "v\<^sub>2 \<notin> {v\<^sub>0, v\<^sub>1}"
  assumes hv\<^sub>0v\<^sub>1_sub_J: "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<subseteq> J"
  assumes h\<theta>_not_free: "\<not> geotop_free_2_simplex K J \<theta>"
  shows "card {\<sigma>\<^sub>2\<in>K. geotop_free_2_simplex K J \<sigma>\<^sub>2} \<ge> 2"
  (**
    Moise Figure 3.2 step for Theorem 3.3.  A nonfree boundary triangle
    \<open>v\<^sub>0v\<^sub>1v\<^sub>2\<close> with boundary edge \<open>v\<^sub>0v\<^sub>1\<close> forces the opposite vertex/cut data:
    the polygon frontier is decomposed at \<open>v\<^sub>0\<close> and \<open>v\<^sub>2\<close> into two broken
    lines, yielding the two polygonal subdisks \<open>L\<^sub>1\<close> and \<open>L\<^sub>2\<close>.  Applying the
    induction hypothesis to each smaller subdisk gives free 2-simplexes
    different from \<open>\<theta>\<close>; the usual carrier and boundary-contact comparisons then
    transfer those free simplexes back to the original complex \<open>K\<close>. **)
proof -
  have h\<theta>_not_col: "\<not> collinear {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
    by (rule geotop_2simplex_vertices_not_collinear_prefix
        [OF h\<theta>_vertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
  have hderived_contact_other_segment_off_base_pre:
    "\<exists>x. x \<in> \<theta> \<inter> J
      \<and> x \<notin> closed_segment v\<^sub>0 v\<^sub>1
      \<and> x \<in> (closed_segment v\<^sub>0 v\<^sub>2 - {v\<^sub>0})
          \<union> (closed_segment v\<^sub>1 v\<^sub>2 - {v\<^sub>1})"
  proof -
    have hv\<^sub>0v\<^sub>2_pre: "v\<^sub>0 \<noteq> v\<^sub>2"
      using hv\<^sub>2_not by (by100 blast)
    have hv\<^sub>1v\<^sub>2_pre: "v\<^sub>1 \<noteq> v\<^sub>2"
      using hv\<^sub>2_not by (by100 blast)
    have h\<theta>_vertices_chord_order_pre:
      "geotop_simplex_vertices \<theta> {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
    proof -
      have "{v\<^sub>0, v\<^sub>2, v\<^sub>1} = {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
        by (by100 blast)
      thus ?thesis using h\<theta>_vertices by (by100 simp)
    qed
    have hv\<^sub>1_not_chord_pre: "v\<^sub>1 \<notin> {v\<^sub>0, v\<^sub>2}"
      using hv\<^sub>0v\<^sub>1 hv\<^sub>1v\<^sub>2_pre by (by100 blast)
    have hbase_edge_face_data_pre:
      "geotop_is_edge (geotop_convex_hull {v\<^sub>0, v\<^sub>1}) \<and>
        geotop_is_face (geotop_convex_hull {v\<^sub>0, v\<^sub>1}) \<theta>"
    proof -
      have hdata:
        "geotop_is_edge (geotop_convex_hull {v\<^sub>0, v\<^sub>1}) \<and>
          geotop_is_face (geotop_convex_hull {v\<^sub>0, v\<^sub>1}) \<theta> \<and>
          geotop_is_edge (geotop_convex_hull {v\<^sub>2, v\<^sub>1}) \<and>
          geotop_is_face (geotop_convex_hull {v\<^sub>2, v\<^sub>1}) \<theta>"
        by (rule geotop_2simplex_vertices_other_edge_faces_prefix
            [OF h\<theta>_vertices_chord_order_pre hv\<^sub>0v\<^sub>2_pre hv\<^sub>1_not_chord_pre])
      show ?thesis using hdata by (by100 blast)
    qed
    have hnonbase_edge_face_data_pre:
      "geotop_is_edge (geotop_convex_hull {v\<^sub>0, v\<^sub>2}) \<and>
        geotop_is_face (geotop_convex_hull {v\<^sub>0, v\<^sub>2}) \<theta> \<and>
        geotop_is_edge (geotop_convex_hull {v\<^sub>1, v\<^sub>2}) \<and>
        geotop_is_face (geotop_convex_hull {v\<^sub>1, v\<^sub>2}) \<theta>"
      by (rule geotop_2simplex_vertices_other_edge_faces_prefix
          [OF h\<theta>_vertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
    have hface_closed_K_pre:
      "\<forall>\<rho>\<in>K. \<forall>\<eta>. geotop_is_face \<eta> \<rho> \<longrightarrow> \<eta> \<in> K"
      using hK unfolding geotop_is_complex_def by (by100 blast)
    have hbase_edge_K_pre: "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<in> K"
      using hface_closed_K_pre h\<theta>K hbase_edge_face_data_pre by (by100 blast)
    have hchord_edge_K_pre: "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<in> K"
      using hface_closed_K_pre h\<theta>K hnonbase_edge_face_data_pre by (by100 blast)
    have hside_edge_K_pre: "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<in> K"
      using hface_closed_K_pre h\<theta>K hnonbase_edge_face_data_pre by (by100 blast)
    have hbase_edge_selected_pre:
      "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<in>
        {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
      using hbase_edge_K_pre hbase_edge_face_data_pre hv\<^sub>0v\<^sub>1_sub_J by (by100 blast)
    have hchord_edge_selected_if_pre:
      "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J \<Longrightarrow>
        geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<in>
          {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
      using hchord_edge_K_pre hnonbase_edge_face_data_pre by (by100 blast)
    have hside_edge_selected_if_pre:
      "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J \<Longrightarrow>
        geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<in>
          {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
      using hside_edge_K_pre hnonbase_edge_face_data_pre by (by100 blast)
    have htriangle_edge_hulls_distinct_pre:
      "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>0, v\<^sub>2}
        \<and> geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}
        \<and> geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
      by (rule geotop_2simplex_vertices_edge_hulls_distinct_prefix
          [OF h\<theta>_vertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
    have hbase_ne_chord_edge_pre:
      "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>0, v\<^sub>2}"
      using htriangle_edge_hulls_distinct_pre by (by100 simp)
    have hbase_ne_side_edge_pre:
      "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
      using htriangle_edge_hulls_distinct_pre by (by100 simp)
    have hchord_ne_side_edge_pre:
      "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
      using htriangle_edge_hulls_distinct_pre by (by100 simp)
    have hE\<theta>_fin_pre:
      "finite {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
      using hK_fin by (by100 simp)
    have hE\<theta>_card_le3_pre:
      "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} \<le> 3"
    proof -
      let ?E = "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
      have hE: "finite ?E \<and> card ?E \<le> 3"
        by (rule geotop_selected_boundary_edge_set_card_le3_prefix[OF h\<theta>2])
      show ?thesis
        using hE by (by100 simp)
    qed
    have hE\<theta>_card_ne3_pre:
      "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} \<noteq> 3"
    proof -
      have hT_gt1: "card {\<rho>\<in>K. geotop_simplex_dim \<rho> 2} > 1"
        using hT_gt2 by (by100 simp)
      show ?thesis
        by (rule geotop_polygon_disk_multi_2simplex_not_three_boundary_edges_prefix
            [OF hJ hK hK_poly h\<theta>K h\<theta>2 hT_gt1])
    qed
    have hE\<theta>_card_le2_pre:
      "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} \<le> 2"
      using hE\<theta>_card_le3_pre hE\<theta>_card_ne3_pre by (by100 linarith)
    have hE\<theta>_allowed_pre:
      "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} = {} \<or>
       (\<exists>e. {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} = {e}
          \<and> geotop_is_edge e \<and> geotop_is_face e \<theta> \<and> e \<subseteq> J) \<or>
       (\<exists>e1 e2. {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} = {e1, e2}
          \<and> e1 \<noteq> e2 \<and> geotop_is_edge e1 \<and> geotop_is_edge e2
          \<and> geotop_is_face e1 \<theta> \<and> geotop_is_face e2 \<theta>
          \<and> e1 \<subseteq> J \<and> e2 \<subseteq> J)"
      by (rule geotop_selected_boundary_edge_set_allowed_card_le2_prefix
          [OF hE\<theta>_fin_pre hE\<theta>_card_le2_pre])
    have hE\<theta>_subset_K_pre:
      "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} \<subseteq> K"
      by (by100 simp)
    have hE\<theta>_union_sub_\<theta>J_pre:
      "\<Union>{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}
        \<subseteq> \<theta> \<inter> J"
      by (rule geotop_selected_boundary_edge_set_union_subset_contact_prefix)
    have h\<theta>_contact_outside_selected_pre:
      "\<exists>x. x \<in> \<theta> \<inter> J
        \<and> x \<notin> \<Union>{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
      by (rule geotop_nonfree_selected_edges_contact_outside_prefix
          [OF h\<theta>K h\<theta>2 hE\<theta>_subset_K_pre hE\<theta>_allowed_pre h\<theta>_not_free
            hE\<theta>_union_sub_\<theta>J_pre])
    have h\<theta>J_sub_named_edges_pre:
      "\<theta> \<inter> J \<subseteq>
        geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<union>
        geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<union>
        geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
      by (rule geotop_2simplex_polygon_boundary_inter_subset_three_edge_hulls_prefix
          [OF hJ h\<theta>K h\<theta>2 hK_poly h\<theta>_vertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
    have hselected_contact_on_other_named_edges_pre:
      "\<exists>x. x \<in> \<theta> \<inter> J
        \<and> x \<notin> \<Union>{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}
        \<and> x \<in> geotop_convex_hull {v\<^sub>0, v\<^sub>2}
            \<union> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
      by (rule geotop_contact_outside_selected_union_on_other_two_sets_prefix
          [OF h\<theta>_contact_outside_selected_pre h\<theta>J_sub_named_edges_pre
            hbase_edge_selected_pre])
    have hselected_contact_on_other_not_base_pre:
      "\<exists>x. x \<in> \<theta> \<inter> J
        \<and> x \<notin> geotop_convex_hull {v\<^sub>0, v\<^sub>1}
        \<and> x \<in> geotop_convex_hull {v\<^sub>0, v\<^sub>2}
            \<union> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
      by (rule geotop_contact_outside_selected_union_avoids_selected_set_prefix
          [OF hselected_contact_on_other_named_edges_pre hbase_edge_selected_pre])
    have hselected_contact_on_other_nonbase_edge_pre:
      "\<exists>x. x \<in> \<theta> \<inter> J
        \<and> x \<in> (geotop_convex_hull {v\<^sub>0, v\<^sub>2} - {v\<^sub>0})
            \<union> (geotop_convex_hull {v\<^sub>1, v\<^sub>2} - {v\<^sub>1})"
      by (rule geotop_other_edge_contact_not_base_avoids_base_endpoints_prefix
          [OF hselected_contact_on_other_not_base_pre])
    have hselected_contact_on_other_nonbase_segment_pre:
      "\<exists>x. x \<in> \<theta> \<inter> J
        \<and> x \<in> (closed_segment v\<^sub>0 v\<^sub>2 - {v\<^sub>0})
            \<union> (closed_segment v\<^sub>1 v\<^sub>2 - {v\<^sub>1})"
      by (rule geotop_nonbase_edge_contact_geotop_to_closed_segment_prefix
          [OF hselected_contact_on_other_nonbase_edge_pre])
    show ?thesis
      by (rule geotop_nonbase_segment_contact_avoids_base_segment_prefix
          [OF h\<theta>_not_col hselected_contact_on_other_nonbase_segment_pre])
  qed
  obtain x where hx\<theta>J: "x \<in> \<theta> \<inter> J"
    and hx_not_base: "x \<notin> closed_segment v\<^sub>0 v\<^sub>1"
    and hx_nonbase:
      "x \<in> (closed_segment v\<^sub>0 v\<^sub>2 - {v\<^sub>0})
        \<union> (closed_segment v\<^sub>1 v\<^sub>2 - {v\<^sub>1})"
    using hderived_contact_other_segment_off_base_pre by (elim exE conjE)
  have hcontact_side_cases:
    "(\<exists>x. x \<in> \<theta> \<inter> J
        \<and> x \<notin> closed_segment v\<^sub>0 v\<^sub>1
        \<and> x \<in> closed_segment v\<^sub>0 v\<^sub>2 - {v\<^sub>0})
     \<or> (\<exists>x. x \<in> \<theta> \<inter> J
        \<and> x \<notin> closed_segment v\<^sub>0 v\<^sub>1
        \<and> x \<in> closed_segment v\<^sub>1 v\<^sub>2 - {v\<^sub>1})"
    using hx\<theta>J hx_not_base hx_nonbase by (by100 blast)
  have hv\<^sub>0v\<^sub>2: "v\<^sub>0 \<noteq> v\<^sub>2"
    using hv\<^sub>2_not by (by100 blast)
  have hv\<^sub>1v\<^sub>2: "v\<^sub>1 \<noteq> v\<^sub>2"
    using hv\<^sub>2_not by (by100 blast)
  have hbase_segment_sub_J: "closed_segment v\<^sub>0 v\<^sub>1 \<subseteq> J"
    using hv\<^sub>0v\<^sub>1_sub_J segment_convex_hull[of v\<^sub>0 v\<^sub>1]
      geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>1}"] by (by100 simp)
  have hv\<^sub>0J: "v\<^sub>0 \<in> J"
  proof -
    have hv\<^sub>0_HOL: "v\<^sub>0 \<in> convex hull {v\<^sub>0, v\<^sub>1}"
      using hull_inc[of v\<^sub>0 "{v\<^sub>0, v\<^sub>1}"] by (by100 simp)
    have "v\<^sub>0 \<in> closed_segment v\<^sub>0 v\<^sub>1"
      using hv\<^sub>0_HOL segment_convex_hull[of v\<^sub>0 v\<^sub>1] by (by100 simp)
    thus ?thesis
      using hbase_segment_sub_J by (by100 blast)
  qed
  have hv\<^sub>1J: "v\<^sub>1 \<in> J"
  proof -
    have hv\<^sub>1_HOL: "v\<^sub>1 \<in> convex hull {v\<^sub>0, v\<^sub>1}"
      using hull_inc[of v\<^sub>1 "{v\<^sub>0, v\<^sub>1}"] by (by100 simp)
    have "v\<^sub>1 \<in> closed_segment v\<^sub>0 v\<^sub>1"
      using hv\<^sub>1_HOL segment_convex_hull[of v\<^sub>0 v\<^sub>1] by (by100 simp)
    thus ?thesis
      using hbase_segment_sub_J by (by100 blast)
  qed
  have hbase_edge_broken_line:
    "geotop_is_broken_line (closed_segment v\<^sub>0 v\<^sub>1)"
    by (rule geotop_closed_segment_is_broken_line[OF hv\<^sub>0v\<^sub>1])
  have hbase_edge_arc:
    "geotop_arc_endpoints (closed_segment v\<^sub>0 v\<^sub>1) {v\<^sub>0, v\<^sub>1}"
    by (rule geotop_closed_segment_arc_endpoints_prefix[OF hv\<^sub>0v\<^sub>1])
  have hother_two_edge_arc:
    "geotop_arc_endpoints
      (closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1) {v\<^sub>0, v\<^sub>1}"
    by (rule geotop_two_segment_join_arc_endpoints_prefix
        [OF hv\<^sub>0v\<^sub>2 hv\<^sub>1v\<^sub>2 h\<theta>_not_col])
  have hother_two_edge_broken_line:
    "geotop_is_broken_line
      (closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1)"
    by (rule geotop_two_segment_join_broken_line_prefix
        [OF hv\<^sub>0v\<^sub>2 hv\<^sub>1v\<^sub>2 h\<theta>_not_col])
  have h\<theta>_frontier_segments:
    "frontier \<theta> =
      closed_segment v\<^sub>0 v\<^sub>1 \<union>
      (closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1)"
    by (rule geotop_2simplex_vertices_frontier_eq_base_union_two_segments_prefix
        [OF h\<theta>_vertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
  have h\<theta>J_sub_frontier: "\<theta> \<inter> J \<subseteq> frontier \<theta>"
  proof
    fix y
    assume hy: "y \<in> \<theta> \<inter> J"
    have hy\<theta>: "y \<in> \<theta>"
      using hy by (by100 simp)
    have hyJ: "y \<in> J"
      using hy by (by100 simp)
    show "y \<in> frontier \<theta>"
      by (rule geotop_polygon_boundary_point_in_2simplex_frontier_prefix
          [OF hJ h\<theta>K h\<theta>2 hK_poly hy\<theta> hyJ])
  qed
  have hx_frontier: "x \<in> frontier \<theta>"
    using h\<theta>J_sub_frontier hx\<theta>J by (by100 blast)
  have hx_two_edge_arc:
    "x \<in> closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1"
    using hx_nonbase closed_segment_commute[of v\<^sub>1 v\<^sub>2] by (by100 blast)
  have hv\<^sub>0_base_segment: "v\<^sub>0 \<in> closed_segment v\<^sub>0 v\<^sub>1"
    by (by100 simp)
  have hv\<^sub>1_base_segment: "v\<^sub>1 \<in> closed_segment v\<^sub>0 v\<^sub>1"
    by (by100 simp)
  have hx_ne_v\<^sub>0: "x \<noteq> v\<^sub>0"
    using hx_not_base hv\<^sub>0_base_segment by (by100 blast)
  have hx_ne_v\<^sub>1: "x \<noteq> v\<^sub>1"
    using hx_not_base hv\<^sub>1_base_segment by (by100 blast)
  have hx_not_endpoints: "x \<notin> {v\<^sub>0, v\<^sub>1}"
    using hx_ne_v\<^sub>0 hx_ne_v\<^sub>1 by (by100 blast)
  have hx_other_arc_interior:
    "x \<in> geotop_arc_interior
      (closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1) {v\<^sub>0, v\<^sub>1}"
    using hx_two_edge_arc hx_not_endpoints
    unfolding geotop_arc_interior_def by (by100 blast)
  have hxJ: "x \<in> J"
    using hx\<theta>J by (by100 blast)
  have hJ_meets_other_arc_interior:
    "J \<inter> geotop_arc_interior
      (closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1) {v\<^sub>0, v\<^sub>1} \<noteq> {}"
    using hxJ hx_other_arc_interior by (by100 blast)
  have hbase_other_arc_interiors_disjoint:
    "geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>1) {v\<^sub>0, v\<^sub>1} \<inter>
      geotop_arc_interior
        (closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1) {v\<^sub>0, v\<^sub>1} =
      {}"
    by (rule geotop_triangle_edge_two_edge_arc_interiors_disjoint_prefix[OF h\<theta>_not_col])
  have htriangle_boundary_polygon:
    "geotop_is_polygon
      (closed_segment v\<^sub>0 v\<^sub>1 \<union>
        (closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1))"
    by (rule pair_of_arcs_is_polygon
        [OF hbase_edge_broken_line hother_two_edge_broken_line
          hbase_edge_arc hother_two_edge_arc hbase_other_arc_interiors_disjoint])
  have h\<theta>_frontier_polygon: "geotop_is_polygon (frontier \<theta>)"
    using h\<theta>_frontier_segments htriangle_boundary_polygon by (by100 simp)
  have hJ_meets_\<theta>_frontier_other_arc_interior:
    "J \<inter> frontier \<theta> \<inter>
      geotop_arc_interior
        (closed_segment v\<^sub>0 v\<^sub>2 \<union> closed_segment v\<^sub>2 v\<^sub>1) {v\<^sub>0, v\<^sub>1} \<noteq> {}"
    using hxJ hx_frontier hx_other_arc_interior by (by100 blast)
  have hJ_meets_nonbase_side_or_v\<^sub>2:
    "v\<^sub>2 \<in> J \<or>
      J \<inter> geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2} \<noteq> {} \<or>
      J \<inter> geotop_arc_interior (closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>1, v\<^sub>2} \<noteq> {}"
  proof (cases "x = v\<^sub>2")
    case True
    show ?thesis
      using True hxJ by (by100 blast)
  next
    case False
    have hside_int:
      "x \<in> geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2} \<or>
       x \<in> geotop_arc_interior (closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>1, v\<^sub>2}"
      using hx_nonbase False unfolding geotop_arc_interior_def by (by100 blast)
    show ?thesis
      using hxJ hside_int by (by100 blast)
  qed
  have h\<theta>_not_col_chord: "\<not> collinear {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
  proof -
    have "{v\<^sub>0, v\<^sub>1, v\<^sub>2} = {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
      by (by100 blast)
    thus ?thesis using h\<theta>_not_col by (by100 simp)
  qed
  have hchord_edge_broken_line:
    "geotop_is_broken_line (closed_segment v\<^sub>0 v\<^sub>2)"
    by (rule geotop_closed_segment_is_broken_line[OF hv\<^sub>0v\<^sub>2])
  have hchord_edge_arc:
    "geotop_arc_endpoints (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2}"
    by (rule geotop_closed_segment_arc_endpoints_prefix[OF hv\<^sub>0v\<^sub>2])
  have hv\<^sub>2v\<^sub>1: "v\<^sub>2 \<noteq> v\<^sub>1"
    using hv\<^sub>1v\<^sub>2 by (by100 blast)
  have hbase_side_edge_broken_line:
    "geotop_is_broken_line
      (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2)"
    by (rule geotop_two_segment_join_broken_line_prefix
        [OF hv\<^sub>0v\<^sub>1 hv\<^sub>2v\<^sub>1 h\<theta>_not_col_chord])
  have hbase_side_edge_arc:
    "geotop_arc_endpoints
      (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>0, v\<^sub>2}"
    by (rule geotop_two_segment_join_arc_endpoints_prefix
        [OF hv\<^sub>0v\<^sub>1 hv\<^sub>2v\<^sub>1 h\<theta>_not_col_chord])
  have hchord_base_side_arc_interiors_disjoint:
    "geotop_arc_interior (closed_segment v\<^sub>0 v\<^sub>2) {v\<^sub>0, v\<^sub>2} \<inter>
      geotop_arc_interior
        (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2) {v\<^sub>0, v\<^sub>2} =
      {}"
    by (rule geotop_triangle_edge_two_edge_arc_interiors_disjoint_prefix
        [OF h\<theta>_not_col_chord])
  have htriangle_boundary_chord_polygon:
    "geotop_is_polygon
      (closed_segment v\<^sub>0 v\<^sub>2 \<union>
        (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2))"
    by (rule pair_of_arcs_is_polygon
        [OF hchord_edge_broken_line hbase_side_edge_broken_line
          hchord_edge_arc hbase_side_edge_arc
          hchord_base_side_arc_interiors_disjoint])
  have h\<theta>_frontier_chord_segments:
    "frontier \<theta> =
      closed_segment v\<^sub>0 v\<^sub>2 \<union>
        (closed_segment v\<^sub>0 v\<^sub>1 \<union> closed_segment v\<^sub>1 v\<^sub>2)"
    using h\<theta>_frontier_segments closed_segment_commute[of v\<^sub>2 v\<^sub>1] by (by100 blast)
  have h\<theta>_frontier_chord_polygon: "geotop_is_polygon (frontier \<theta>)"
    using h\<theta>_frontier_chord_segments htriangle_boundary_chord_polygon by (by100 simp)
  have h\<theta>_vertices_chord_order:
    "geotop_simplex_vertices \<theta> {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
  proof -
    have "{v\<^sub>0, v\<^sub>2, v\<^sub>1} = {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
      by (by100 blast)
    thus ?thesis using h\<theta>_vertices by (by100 simp)
  qed
  have hv\<^sub>1_not_chord: "v\<^sub>1 \<notin> {v\<^sub>0, v\<^sub>2}"
    using hv\<^sub>0v\<^sub>1 hv\<^sub>1v\<^sub>2 by (by100 blast)
  have hbase_edge_face_data:
    "geotop_is_edge (geotop_convex_hull {v\<^sub>0, v\<^sub>1}) \<and>
      geotop_is_face (geotop_convex_hull {v\<^sub>0, v\<^sub>1}) \<theta>"
  proof -
    have hdata:
      "geotop_is_edge (geotop_convex_hull {v\<^sub>0, v\<^sub>1}) \<and>
        geotop_is_face (geotop_convex_hull {v\<^sub>0, v\<^sub>1}) \<theta> \<and>
        geotop_is_edge (geotop_convex_hull {v\<^sub>2, v\<^sub>1}) \<and>
        geotop_is_face (geotop_convex_hull {v\<^sub>2, v\<^sub>1}) \<theta>"
      by (rule geotop_2simplex_vertices_other_edge_faces_prefix
          [OF h\<theta>_vertices_chord_order hv\<^sub>0v\<^sub>2 hv\<^sub>1_not_chord])
    show ?thesis using hdata by (by100 blast)
  qed
  have hnonbase_edge_face_data:
    "geotop_is_edge (geotop_convex_hull {v\<^sub>0, v\<^sub>2}) \<and>
      geotop_is_face (geotop_convex_hull {v\<^sub>0, v\<^sub>2}) \<theta> \<and>
      geotop_is_edge (geotop_convex_hull {v\<^sub>1, v\<^sub>2}) \<and>
      geotop_is_face (geotop_convex_hull {v\<^sub>1, v\<^sub>2}) \<theta>"
    by (rule geotop_2simplex_vertices_other_edge_faces_prefix
        [OF h\<theta>_vertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
  have hface_closed_K:
    "\<forall>\<rho>\<in>K. \<forall>\<eta>. geotop_is_face \<eta> \<rho> \<longrightarrow> \<eta> \<in> K"
    using hK unfolding geotop_is_complex_def by (by100 blast)
  have hbase_edge_K:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<in> K"
    using hface_closed_K h\<theta>K hbase_edge_face_data by (by100 blast)
  have hchord_edge_K:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<in> K"
    using hface_closed_K h\<theta>K hnonbase_edge_face_data by (by100 blast)
  have hside_edge_K:
    "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<in> K"
    using hface_closed_K h\<theta>K hnonbase_edge_face_data by (by100 blast)
  have hbase_edge_selected:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<in>
      {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
    using hbase_edge_K hbase_edge_face_data hv\<^sub>0v\<^sub>1_sub_J by (by100 blast)
  have hchord_edge_selected_if:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J \<Longrightarrow>
      geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<in>
        {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
    using hchord_edge_K hnonbase_edge_face_data by (by100 blast)
  have hside_edge_selected_if:
    "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J \<Longrightarrow>
      geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<in>
        {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
    using hside_edge_K hnonbase_edge_face_data by (by100 blast)
  have htriangle_edge_hulls_distinct:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>0, v\<^sub>2}
      \<and> geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}
      \<and> geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
    by (rule geotop_2simplex_vertices_edge_hulls_distinct_prefix
        [OF h\<theta>_vertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
  have hbase_ne_chord_edge:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>0, v\<^sub>2}"
    using htriangle_edge_hulls_distinct by (by100 simp)
  have hbase_ne_side_edge:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
    using htriangle_edge_hulls_distinct by (by100 simp)
  have hchord_ne_side_edge:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
    using htriangle_edge_hulls_distinct by (by100 simp)
  have hE\<theta>_fin:
    "finite {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
    using hK_fin by (by100 simp)
  have hE\<theta>_card_le3:
    "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} \<le> 3"
  proof -
    let ?E = "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
    have hE: "finite ?E \<and> card ?E \<le> 3"
      by (rule geotop_selected_boundary_edge_set_card_le3_prefix[OF h\<theta>2])
    show ?thesis
      using hE by (by100 simp)
  qed
  have hE\<theta>_card_ne3:
    "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} \<noteq> 3"
  proof -
    have hT_gt1: "card {\<rho>\<in>K. geotop_simplex_dim \<rho> 2} > 1"
      using hT_gt2 by (by100 simp)
    show ?thesis
      by (rule geotop_polygon_disk_multi_2simplex_not_three_boundary_edges_prefix
          [OF hJ hK hK_poly h\<theta>K h\<theta>2 hT_gt1])
  qed
  have hnot_both_nonbase_boundary_edges:
    "\<not> (geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J
      \<and> geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J)"
    by (rule geotop_selected_boundary_edge_set_not_both_other_edges_prefix
        [OF hE\<theta>_fin hbase_edge_selected
          hchord_edge_selected_if hside_edge_selected_if
          hbase_ne_chord_edge hbase_ne_side_edge hchord_ne_side_edge
          hE\<theta>_card_le3 hE\<theta>_card_ne3])
  have hE\<theta>_card_le2:
    "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} \<le> 2"
    using hE\<theta>_card_le3 hE\<theta>_card_ne3 by (by100 linarith)
  have hE\<theta>_allowed:
    "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} = {} \<or>
     (\<exists>e. {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} = {e}
        \<and> geotop_is_edge e \<and> geotop_is_face e \<theta> \<and> e \<subseteq> J) \<or>
     (\<exists>e1 e2. {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} = {e1, e2}
        \<and> e1 \<noteq> e2 \<and> geotop_is_edge e1 \<and> geotop_is_edge e2
        \<and> geotop_is_face e1 \<theta> \<and> geotop_is_face e2 \<theta>
        \<and> e1 \<subseteq> J \<and> e2 \<subseteq> J)"
    by (rule geotop_selected_boundary_edge_set_allowed_card_le2_prefix
        [OF hE\<theta>_fin hE\<theta>_card_le2])
  have hE\<theta>_subset_K:
    "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J} \<subseteq> K"
    by (by100 simp)
  have hE\<theta>_union_sub_\<theta>J:
    "\<Union>{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}
      \<subseteq> \<theta> \<inter> J"
    by (rule geotop_selected_boundary_edge_set_union_subset_contact_prefix)
  have h\<theta>_contact_outside_selected:
    "\<exists>x. x \<in> \<theta> \<inter> J
      \<and> x \<notin> \<Union>{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}"
    by (rule geotop_nonfree_selected_edges_contact_outside_prefix
        [OF h\<theta>K h\<theta>2 hE\<theta>_subset_K hE\<theta>_allowed h\<theta>_not_free
          hE\<theta>_union_sub_\<theta>J])
  have h\<theta>J_sub_named_edges:
    "\<theta> \<inter> J \<subseteq>
      geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<union>
      geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<union>
      geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
    by (rule geotop_2simplex_polygon_boundary_inter_subset_three_edge_hulls_prefix
        [OF hJ h\<theta>K h\<theta>2 hK_poly h\<theta>_vertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
  have hselected_contact_on_other_named_edges:
    "\<exists>x. x \<in> \<theta> \<inter> J
      \<and> x \<notin> \<Union>{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J}
      \<and> x \<in> geotop_convex_hull {v\<^sub>0, v\<^sub>2}
          \<union> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
    by (rule geotop_contact_outside_selected_union_on_other_two_sets_prefix
        [OF h\<theta>_contact_outside_selected h\<theta>J_sub_named_edges hbase_edge_selected])
  have hselected_contact_on_other_not_base:
    "\<exists>x. x \<in> \<theta> \<inter> J
      \<and> x \<notin> geotop_convex_hull {v\<^sub>0, v\<^sub>1}
      \<and> x \<in> geotop_convex_hull {v\<^sub>0, v\<^sub>2}
          \<union> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
    by (rule geotop_contact_outside_selected_union_avoids_selected_set_prefix
        [OF hselected_contact_on_other_named_edges hbase_edge_selected])
  have hselected_contact_on_other_nonbase_edge:
    "\<exists>x. x \<in> \<theta> \<inter> J
      \<and> x \<in> (geotop_convex_hull {v\<^sub>0, v\<^sub>2} - {v\<^sub>0})
          \<union> (geotop_convex_hull {v\<^sub>1, v\<^sub>2} - {v\<^sub>1})"
    by (rule geotop_other_edge_contact_not_base_avoids_base_endpoints_prefix
        [OF hselected_contact_on_other_not_base])
  have hselected_contact_on_other_nonbase_segment:
    "\<exists>x. x \<in> \<theta> \<inter> J
      \<and> x \<in> (closed_segment v\<^sub>0 v\<^sub>2 - {v\<^sub>0})
          \<union> (closed_segment v\<^sub>1 v\<^sub>2 - {v\<^sub>1})"
    by (rule geotop_nonbase_edge_contact_geotop_to_closed_segment_prefix
        [OF hselected_contact_on_other_nonbase_edge])
  have hderived_contact_other_segment_off_base:
    "\<exists>x. x \<in> \<theta> \<inter> J
      \<and> x \<notin> closed_segment v\<^sub>0 v\<^sub>1
      \<and> x \<in> (closed_segment v\<^sub>0 v\<^sub>2 - {v\<^sub>0})
          \<union> (closed_segment v\<^sub>1 v\<^sub>2 - {v\<^sub>1})"
    by (rule geotop_nonbase_segment_contact_avoids_base_segment_prefix
        [OF h\<theta>_not_col hselected_contact_on_other_nonbase_segment])
  have hchord_hull_segment_eq:
    "geotop_convex_hull {v\<^sub>0, v\<^sub>2} = closed_segment v\<^sub>0 v\<^sub>2"
    using segment_convex_hull[of v\<^sub>0 v\<^sub>2] geotop_convex_hull_eq_HOL[of "{v\<^sub>0, v\<^sub>2}"]
    by (by100 simp)
  have hside_hull_segment_eq:
    "geotop_convex_hull {v\<^sub>1, v\<^sub>2} = closed_segment v\<^sub>1 v\<^sub>2"
    using segment_convex_hull[of v\<^sub>1 v\<^sub>2] geotop_convex_hull_eq_HOL[of "{v\<^sub>1, v\<^sub>2}"]
    by (by100 simp)
  have hnot_both_nonbase_boundary_segments:
    "\<not> (closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> J
      \<and> closed_segment v\<^sub>1 v\<^sub>2 \<subseteq> J)"
    using hnot_both_nonbase_boundary_edges hchord_hull_segment_eq hside_hull_segment_eq
    by (by100 simp)
  have hnonbase_boundary_segment_cases:
    "\<not> closed_segment v\<^sub>0 v\<^sub>2 \<subseteq> J \<or>
      \<not> closed_segment v\<^sub>1 v\<^sub>2 \<subseteq> J"
    using hnot_both_nonbase_boundary_segments by (by100 blast)
  show ?thesis
    by (rule geotop_polygon_disk_nonfree_boundary_triangle_split_free_count_prefix
        [OF hJ hK hK_fin hK_poly hT_gt2 h\<theta>K h\<theta>2 h\<theta>_vertices
          hv\<^sub>0v\<^sub>1 hv\<^sub>2_not hv\<^sub>0v\<^sub>1_sub_J h\<theta>_not_free
          h\<theta>_not_col hbase_segment_sub_J hJ_meets_other_arc_interior
          hJ_meets_\<theta>_frontier_other_arc_interior hJ_meets_nonbase_side_or_v\<^sub>2
          h\<theta>_frontier_polygon h\<theta>_frontier_chord_polygon
          hnot_both_nonbase_boundary_segments hnonbase_boundary_segment_cases])
qed

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
          let ?E\<sigma> = "{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J'}"
          have hE\<sigma>_subset: "?E\<sigma> \<subseteq> K"
            by (by100 simp)
          have hE\<sigma>_fin: "finite ?E\<sigma>"
            using hK_fin' by (by100 simp)
          have hE\<sigma>_card_le2: "card ?E\<sigma> \<le> 2"
            by (rule geotop_two_triangle_boundary_edge_faces_card_le2_prefix
                [OF hJ' hK' hK_poly' hT_eq h\<sigma>K h\<sigma>2 h\<sigma>\<tau>])
          have hE\<sigma>_allowed:
            "?E\<sigma> = {} \<or>
             (\<exists>e. ?E\<sigma> = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<sigma> \<and> e \<subseteq> J') \<or>
             (\<exists>e1 e2. ?E\<sigma> = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                geotop_is_face e1 \<sigma> \<and> geotop_is_face e2 \<sigma> \<and>
                e1 \<subseteq> J' \<and> e2 \<subseteq> J')"
            by (rule geotop_selected_boundary_edge_set_allowed_card_le2_prefix
                [OF hE\<sigma>_fin hE\<sigma>_card_le2])
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
            by (rule geotop_free_2_simplex_selected_edges_intro_prefix
                [OF h\<sigma>K h\<sigma>2 hE\<sigma>_subset hE\<sigma>_allowed h\<sigma>J_eq])
        qed
        have h\<tau>free: "geotop_free_2_simplex K J' \<tau>"
        proof -
          have h\<tau>K: "\<tau> \<in> K"
            using h\<tau>T by (by100 simp)
          have h\<tau>2: "geotop_simplex_dim \<tau> 2"
            using h\<tau>T by (by100 simp)
          let ?E\<tau> = "{e\<in>K. geotop_is_edge e \<and> geotop_is_face e \<tau> \<and> e \<subseteq> J'}"
          have hE\<tau>_subset: "?E\<tau> \<subseteq> K"
            by (by100 simp)
          have hE\<tau>_fin: "finite ?E\<tau>"
            using hK_fin' by (by100 simp)
          have hE\<tau>_card_le2: "card ?E\<tau> \<le> 2"
            by (rule geotop_two_triangle_boundary_edge_faces_card_le2_prefix
                [OF hJ' hK' hK_poly' hT_eq_swap h\<tau>K h\<tau>2 h\<tau>\<sigma>])
          have hE\<tau>_allowed:
            "?E\<tau> = {} \<or>
             (\<exists>e. ?E\<tau> = {e} \<and> geotop_is_edge e \<and> geotop_is_face e \<tau> \<and> e \<subseteq> J') \<or>
             (\<exists>e1 e2. ?E\<tau> = {e1, e2} \<and> e1 \<noteq> e2 \<and>
                geotop_is_edge e1 \<and> geotop_is_edge e2 \<and>
                geotop_is_face e1 \<tau> \<and> geotop_is_face e2 \<tau> \<and>
                e1 \<subseteq> J' \<and> e2 \<subseteq> J')"
            by (rule geotop_selected_boundary_edge_set_allowed_card_le2_prefix
                [OF hE\<tau>_fin hE\<tau>_card_le2])
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
            by (rule geotop_free_2_simplex_selected_edges_intro_prefix
                [OF h\<tau>K h\<tau>2 hE\<tau>_subset hE\<tau>_allowed h\<tau>J_eq])
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
        proof -
          obtain \<sigma> \<tau> where
            h\<sigma>K: "\<sigma> \<in> K" and
            h\<tau>K: "\<tau> \<in> K" and
            h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>" and
            h\<sigma>2: "geotop_simplex_dim \<sigma> 2" and
            h\<tau>2: "geotop_simplex_dim \<tau> 2" and
            hE\<sigma>_ne: "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J'} \<noteq> {}" and
            hE\<tau>_ne: "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J'} \<noteq> {}"
            using hboundary_edge_sets by (elim exE conjE)
          show ?thesis
          proof (cases "geotop_free_2_simplex K J' \<sigma> \<and> geotop_free_2_simplex K J' \<tau>")
            case True
            have h\<sigma>free: "geotop_free_2_simplex K J' \<sigma>"
              using True by (by100 simp)
            have h\<tau>free: "geotop_free_2_simplex K J' \<tau>"
              using True by (by100 simp)
            show ?thesis
              by (rule hboth_free_case[OF h\<sigma>K h\<tau>K h\<sigma>\<tau> h\<sigma>free h\<tau>free])
          next
            case False
            obtain \<theta> where
              h\<theta>K: "\<theta> \<in> K" and
              h\<theta>2: "geotop_simplex_dim \<theta> 2" and
              hE\<theta>_ne: "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'} \<noteq> {}" and
              h\<theta>_not_free: "\<not> geotop_free_2_simplex K J' \<theta>"
            proof -
              have hnot_both:
                "\<not> (geotop_free_2_simplex K J' \<sigma> \<and> geotop_free_2_simplex K J' \<tau>)"
                using False .
              have hnonfree_exists:
                "\<exists>\<theta>. \<theta> \<in> K \<and> geotop_simplex_dim \<theta> 2
                  \<and> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'} \<noteq> {}
                  \<and> \<not> geotop_free_2_simplex K J' \<theta>"
              proof (cases "geotop_free_2_simplex K J' \<sigma>")
                case True
                have h\<tau>_not_free: "\<not> geotop_free_2_simplex K J' \<tau>"
                  using hnot_both True by (by100 simp)
                show ?thesis
                proof (rule exI[where x = \<tau>])
                  show "\<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2
                    \<and> {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<tau> \<and> d \<subseteq> J'} \<noteq> {}
                    \<and> \<not> geotop_free_2_simplex K J' \<tau>"
                    by (intro conjI h\<tau>K h\<tau>2 hE\<tau>_ne h\<tau>_not_free)
                qed
              next
                case False
                show ?thesis
                proof (rule exI[where x = \<sigma>])
                  show "\<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2
                    \<and> {d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<sigma> \<and> d \<subseteq> J'} \<noteq> {}
                    \<and> \<not> geotop_free_2_simplex K J' \<sigma>"
                    by (intro conjI h\<sigma>K h\<sigma>2 hE\<sigma>_ne False)
                qed
              qed
              show ?thesis
                using hnonfree_exists that by (elim exE conjE)
            qed
            obtain e\<^sub>\<theta> where
              he\<^sub>\<theta>K: "e\<^sub>\<theta> \<in> K" and
              he\<^sub>\<theta>_edge: "geotop_is_edge e\<^sub>\<theta>" and
              he\<^sub>\<theta>_face: "geotop_is_face e\<^sub>\<theta> \<theta>" and
              he\<^sub>\<theta>_sub_J: "e\<^sub>\<theta> \<subseteq> J'"
            proof -
              have "\<exists>e. e \<in> K \<and> geotop_is_edge e \<and> geotop_is_face e \<theta> \<and> e \<subseteq> J'"
                using hE\<theta>_ne by (by100 blast)
              thus ?thesis
                using that by (elim exE conjE)
            qed
            have he\<^sub>\<theta>_sub_frontier:
              "e\<^sub>\<theta> \<subseteq> geotop_frontier UNIV geotop_euclidean_topology
                 (geotop_polyhedron K)"
            proof -
              have hfront_eq:
                "geotop_frontier UNIV geotop_euclidean_topology (geotop_polyhedron K) = J'"
                by (rule geotop_polygon_disk_polyhedron_geotop_frontier_prefix[OF hJ' hK_poly'])
              show ?thesis
                using he\<^sub>\<theta>_sub_J hfront_eq by (by100 simp)
            qed
            obtain v\<^sub>0 v\<^sub>1 v\<^sub>2 where
              hv\<^sub>0v\<^sub>1: "v\<^sub>0 \<noteq> v\<^sub>1" and
              hv\<^sub>2_not: "v\<^sub>2 \<notin> {v\<^sub>0, v\<^sub>1}" and
              he\<^sub>\<theta>_vertices: "e\<^sub>\<theta> = geotop_convex_hull {v\<^sub>0, v\<^sub>1}" and
              h\<theta>_vertices: "geotop_simplex_vertices \<theta> {v\<^sub>0, v\<^sub>1, v\<^sub>2}"
              by (rule geotop_2simplex_edge_face_vertices_prefix
                  [OF h\<theta>2 he\<^sub>\<theta>_edge he\<^sub>\<theta>_face])
            have hv\<^sub>0v\<^sub>1_sub_frontier:
              "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<subseteq>
                 geotop_frontier UNIV geotop_euclidean_topology
                   (geotop_polyhedron K)"
              using he\<^sub>\<theta>_vertices he\<^sub>\<theta>_sub_frontier by (by100 simp)
            have hv\<^sub>0v\<^sub>1_sub_J:
              "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<subseteq> J'"
              using he\<^sub>\<theta>_vertices he\<^sub>\<theta>_sub_J by (by100 simp)
            have hother_edge_faces:
              "geotop_is_edge (geotop_convex_hull {v\<^sub>0, v\<^sub>2})
                \<and> geotop_is_face (geotop_convex_hull {v\<^sub>0, v\<^sub>2}) \<theta>
                \<and> geotop_is_edge (geotop_convex_hull {v\<^sub>1, v\<^sub>2})
                \<and> geotop_is_face (geotop_convex_hull {v\<^sub>1, v\<^sub>2}) \<theta>"
              by (rule geotop_2simplex_vertices_other_edge_faces_prefix
                  [OF h\<theta>_vertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
            have hv\<^sub>0v\<^sub>2_edge: "geotop_is_edge (geotop_convex_hull {v\<^sub>0, v\<^sub>2})"
              using hother_edge_faces by (by100 simp)
            have hv\<^sub>0v\<^sub>2_face: "geotop_is_face (geotop_convex_hull {v\<^sub>0, v\<^sub>2}) \<theta>"
              using hother_edge_faces by (by100 simp)
            have hv\<^sub>1v\<^sub>2_edge: "geotop_is_edge (geotop_convex_hull {v\<^sub>1, v\<^sub>2})"
              using hother_edge_faces by (by100 simp)
            have hv\<^sub>1v\<^sub>2_face: "geotop_is_face (geotop_convex_hull {v\<^sub>1, v\<^sub>2}) \<theta>"
              using hother_edge_faces by (by100 simp)
            have hface_closed_K:
              "\<forall>\<rho>\<in>K. \<forall>\<eta>. geotop_is_face \<eta> \<rho> \<longrightarrow> \<eta> \<in> K"
              using hK' unfolding geotop_is_complex_def by (by100 blast)
            have hv\<^sub>0v\<^sub>2K: "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<in> K"
              using hface_closed_K h\<theta>K hv\<^sub>0v\<^sub>2_face by (by100 blast)
            have hv\<^sub>1v\<^sub>2K: "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<in> K"
              using hface_closed_K h\<theta>K hv\<^sub>1v\<^sub>2_face by (by100 blast)
            have hv\<^sub>0v\<^sub>1_selected:
              "geotop_convex_hull {v\<^sub>0, v\<^sub>1}
                \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'}"
              using he\<^sub>\<theta>K he\<^sub>\<theta>_edge he\<^sub>\<theta>_face he\<^sub>\<theta>_sub_J he\<^sub>\<theta>_vertices
              by (by100 simp)
            have hv\<^sub>0v\<^sub>2_selected_if_boundary:
              "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J' \<Longrightarrow>
                geotop_convex_hull {v\<^sub>0, v\<^sub>2}
                  \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'}"
              using hv\<^sub>0v\<^sub>2K hv\<^sub>0v\<^sub>2_edge hv\<^sub>0v\<^sub>2_face by (by100 simp)
            have hv\<^sub>1v\<^sub>2_selected_if_boundary:
              "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J' \<Longrightarrow>
                geotop_convex_hull {v\<^sub>1, v\<^sub>2}
                  \<in> {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'}"
              using hv\<^sub>1v\<^sub>2K hv\<^sub>1v\<^sub>2_edge hv\<^sub>1v\<^sub>2_face by (by100 simp)
            have htriangle_edge_hulls_distinct:
              "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>0, v\<^sub>2}
                \<and> geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}
                \<and> geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
              by (rule geotop_2simplex_vertices_edge_hulls_distinct_prefix
                  [OF h\<theta>_vertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
            have hv\<^sub>0v\<^sub>1_ne_v\<^sub>0v\<^sub>2:
              "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>0, v\<^sub>2}"
              using htriangle_edge_hulls_distinct by (by100 simp)
            have hv\<^sub>0v\<^sub>1_ne_v\<^sub>1v\<^sub>2:
              "geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
              using htriangle_edge_hulls_distinct by (by100 simp)
            have hv\<^sub>0v\<^sub>2_ne_v\<^sub>1v\<^sub>2:
              "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<noteq> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
              using htriangle_edge_hulls_distinct by (by100 simp)
            have hE\<theta>_fin:
              "finite {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'}"
              using hK_fin' by (by100 simp)
            have hE\<theta>_card_ge2_if_v\<^sub>0v\<^sub>2_boundary:
              "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J' \<Longrightarrow>
                card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'} \<ge> 2"
            proof -
              assume hv\<^sub>0v\<^sub>2_sub_J: "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J'"
              show ?thesis
                by (rule geotop_selected_boundary_edge_set_card_ge2_if_other_edge_prefix
                    [OF hE\<theta>_fin hv\<^sub>0v\<^sub>1_selected
                      hv\<^sub>0v\<^sub>2_selected_if_boundary hv\<^sub>0v\<^sub>1_ne_v\<^sub>0v\<^sub>2
                      hv\<^sub>0v\<^sub>2_sub_J])
            qed
            have hE\<theta>_card_ge2_if_v\<^sub>1v\<^sub>2_boundary:
              "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J' \<Longrightarrow>
                card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'} \<ge> 2"
            proof -
              assume hv\<^sub>1v\<^sub>2_sub_J: "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J'"
              show ?thesis
                by (rule geotop_selected_boundary_edge_set_card_ge2_if_other_edge_prefix
                    [OF hE\<theta>_fin hv\<^sub>0v\<^sub>1_selected
                      hv\<^sub>1v\<^sub>2_selected_if_boundary hv\<^sub>0v\<^sub>1_ne_v\<^sub>1v\<^sub>2
                      hv\<^sub>1v\<^sub>2_sub_J])
            qed
            have hE\<theta>_card_le3:
              "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'} \<le> 3"
            proof -
              let ?E = "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'}"
              have hE: "finite ?E \<and> card ?E \<le> 3"
                by (rule geotop_selected_boundary_edge_set_card_le3_prefix[OF h\<theta>2])
              show ?thesis
                using hE by (by100 simp)
            qed
            have hE\<theta>_card_eq3_if_both_other_boundary:
              "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J' \<Longrightarrow>
                geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J' \<Longrightarrow>
                card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'} = 3"
            proof -
              assume hv\<^sub>0v\<^sub>2_sub_J: "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J'"
              assume hv\<^sub>1v\<^sub>2_sub_J: "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J'"
              show ?thesis
                by (rule geotop_selected_boundary_edge_set_card_eq3_if_two_other_edges_prefix
                    [OF hE\<theta>_fin hv\<^sub>0v\<^sub>1_selected
                      hv\<^sub>0v\<^sub>2_selected_if_boundary hv\<^sub>1v\<^sub>2_selected_if_boundary
                      hv\<^sub>0v\<^sub>1_ne_v\<^sub>0v\<^sub>2 hv\<^sub>0v\<^sub>1_ne_v\<^sub>1v\<^sub>2 hv\<^sub>0v\<^sub>2_ne_v\<^sub>1v\<^sub>2
                      hE\<theta>_card_le3 hv\<^sub>0v\<^sub>2_sub_J hv\<^sub>1v\<^sub>2_sub_J])
            qed
            have h\<theta>J_eq_frontier_if_both_other_boundary:
              "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J' \<Longrightarrow>
                geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J' \<Longrightarrow>
                \<theta> \<inter> J' = frontier \<theta>"
            proof -
              assume hv\<^sub>0v\<^sub>2_sub_J: "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J'"
              assume hv\<^sub>1v\<^sub>2_sub_J: "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J'"
              have hcard3:
                "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'} = 3"
                by (rule hE\<theta>_card_eq3_if_both_other_boundary
                    [OF hv\<^sub>0v\<^sub>2_sub_J hv\<^sub>1v\<^sub>2_sub_J])
              show ?thesis
                by (rule geotop_2simplex_three_selected_edge_faces_boundary_contact_eq_frontier_prefix
                    [OF hJ' h\<theta>K h\<theta>2 hK_poly' hcard3])
            qed
            have hE\<theta>_eq_three_named_if_both_other_boundary:
              "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J' \<Longrightarrow>
                geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J' \<Longrightarrow>
                {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'} =
                  {geotop_convex_hull {v\<^sub>0, v\<^sub>1},
                   geotop_convex_hull {v\<^sub>0, v\<^sub>2},
                   geotop_convex_hull {v\<^sub>1, v\<^sub>2}}"
            proof -
              assume hv\<^sub>0v\<^sub>2_sub_J: "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J'"
              assume hv\<^sub>1v\<^sub>2_sub_J: "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J'"
              let ?E = "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'}"
              have hE_card: "card ?E = 3"
                by (rule hE\<theta>_card_eq3_if_both_other_boundary
                    [OF hv\<^sub>0v\<^sub>2_sub_J hv\<^sub>1v\<^sub>2_sub_J])
              show ?thesis
                by (rule geotop_selected_boundary_edge_set_eq_three_named_prefix
                    [OF hE\<theta>_fin hv\<^sub>0v\<^sub>1_selected
                      hv\<^sub>0v\<^sub>2_selected_if_boundary hv\<^sub>1v\<^sub>2_selected_if_boundary
                      hv\<^sub>0v\<^sub>1_ne_v\<^sub>0v\<^sub>2 hv\<^sub>0v\<^sub>1_ne_v\<^sub>1v\<^sub>2 hv\<^sub>0v\<^sub>2_ne_v\<^sub>1v\<^sub>2
                      hv\<^sub>0v\<^sub>2_sub_J hv\<^sub>1v\<^sub>2_sub_J hE_card])
            qed
            have h\<theta>J_sub_named_edges:
              "\<theta> \<inter> J' \<subseteq>
                geotop_convex_hull {v\<^sub>0, v\<^sub>1} \<union>
                geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<union>
                geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
              by (rule geotop_2simplex_polygon_boundary_inter_subset_three_edge_hulls_prefix
                  [OF hJ' h\<theta>K h\<theta>2 hK_poly' h\<theta>_vertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
            have hE\<theta>_union_sub_\<theta>J:
              "\<Union>{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'}
                \<subseteq> \<theta> \<inter> J'"
              by (rule geotop_selected_boundary_edge_set_union_subset_contact_prefix)
            have h\<theta>J_sub_selected_if_both_other_boundary:
              "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J' \<Longrightarrow>
                geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J' \<Longrightarrow>
                \<theta> \<inter> J' \<subseteq>
                  \<Union>{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'}"
            proof -
              assume hv\<^sub>0v\<^sub>2_sub_J: "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J'"
              assume hv\<^sub>1v\<^sub>2_sub_J: "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J'"
              have hE_eq:
                "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'} =
                  {geotop_convex_hull {v\<^sub>0, v\<^sub>1},
                   geotop_convex_hull {v\<^sub>0, v\<^sub>2},
                   geotop_convex_hull {v\<^sub>1, v\<^sub>2}}"
                by (rule hE\<theta>_eq_three_named_if_both_other_boundary
                    [OF hv\<^sub>0v\<^sub>2_sub_J hv\<^sub>1v\<^sub>2_sub_J])
              show ?thesis
                by (rule geotop_subset_union_from_three_named_family_prefix
                    [OF h\<theta>J_sub_named_edges hE_eq])
            qed
            have h\<theta>J_eq_selected_if_both_other_boundary:
              "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J' \<Longrightarrow>
                geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J' \<Longrightarrow>
                \<theta> \<inter> J' =
                  \<Union>{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'}"
            proof -
              assume hv\<^sub>0v\<^sub>2_sub_J: "geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J'"
              assume hv\<^sub>1v\<^sub>2_sub_J: "geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J'"
              show ?thesis
              proof
                show "\<theta> \<inter> J' \<subseteq>
                    \<Union>{d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'}"
                  by (rule h\<theta>J_sub_selected_if_both_other_boundary
                      [OF hv\<^sub>0v\<^sub>2_sub_J hv\<^sub>1v\<^sub>2_sub_J])
                show "\<Union>{d \<in> K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'}
                    \<subseteq> \<theta> \<inter> J'"
                  by (rule hE\<theta>_union_sub_\<theta>J)
              qed
            qed
            have hE\<theta>_card_ne3:
              "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'} \<noteq> 3"
            proof -
              have hT_gt1: "card ?T > 1"
                using hT_gt2 by (by100 simp)
              show ?thesis
                by (rule geotop_polygon_disk_multi_2simplex_not_three_boundary_edges_prefix
                    [OF hJ' hK' hK_poly' h\<theta>K h\<theta>2 hT_gt1])
            qed
            have hnot_both_other_boundary:
              "\<not> (geotop_convex_hull {v\<^sub>0, v\<^sub>2} \<subseteq> J'
                \<and> geotop_convex_hull {v\<^sub>1, v\<^sub>2} \<subseteq> J')"
              by (rule geotop_selected_boundary_edge_set_not_both_other_edges_prefix
                  [OF hE\<theta>_fin hv\<^sub>0v\<^sub>1_selected
                    hv\<^sub>0v\<^sub>2_selected_if_boundary hv\<^sub>1v\<^sub>2_selected_if_boundary
                    hv\<^sub>0v\<^sub>1_ne_v\<^sub>0v\<^sub>2 hv\<^sub>0v\<^sub>1_ne_v\<^sub>1v\<^sub>2 hv\<^sub>0v\<^sub>2_ne_v\<^sub>1v\<^sub>2
                    hE\<theta>_card_le3 hE\<theta>_card_ne3])
            have hE\<theta>_card_le2:
              "card {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'} \<le> 2"
              using hE\<theta>_card_le3 hE\<theta>_card_ne3 by (by100 linarith)
            have hE\<theta>_allowed:
              "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'} = {} \<or>
               (\<exists>e. {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'} = {e}
                  \<and> geotop_is_edge e \<and> geotop_is_face e \<theta> \<and> e \<subseteq> J') \<or>
               (\<exists>e1 e2. {d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'} = {e1, e2}
                  \<and> e1 \<noteq> e2 \<and> geotop_is_edge e1 \<and> geotop_is_edge e2
                  \<and> geotop_is_face e1 \<theta> \<and> geotop_is_face e2 \<theta> \<and> e1 \<subseteq> J' \<and> e2 \<subseteq> J')"
              by (rule geotop_selected_boundary_edge_set_allowed_card_le2_prefix
                  [OF hE\<theta>_fin hE\<theta>_card_le2])
            have hE\<theta>_subset_K:
              "{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'} \<subseteq> K"
              by (by100 simp)
            have h\<theta>_contact_outside_selected:
              "\<exists>x. x \<in> \<theta> \<inter> J'
                \<and> x \<notin> \<Union>{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'}"
              by (rule geotop_nonfree_selected_edges_contact_outside_prefix
                  [OF h\<theta>K h\<theta>2 hE\<theta>_subset_K hE\<theta>_allowed h\<theta>_not_free hE\<theta>_union_sub_\<theta>J])
            have h\<theta>_contact_on_other_named_edges:
              "\<exists>x. x \<in> \<theta> \<inter> J'
                \<and> x \<notin> \<Union>{d\<in>K. geotop_is_edge d \<and> geotop_is_face d \<theta> \<and> d \<subseteq> J'}
                \<and> x \<in> geotop_convex_hull {v\<^sub>0, v\<^sub>2}
                    \<union> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
              by (rule geotop_contact_outside_selected_union_on_other_two_sets_prefix
                  [OF h\<theta>_contact_outside_selected h\<theta>J_sub_named_edges hv\<^sub>0v\<^sub>1_selected])
            have h\<theta>_contact_on_other_not_base:
              "\<exists>x. x \<in> \<theta> \<inter> J'
                \<and> x \<notin> geotop_convex_hull {v\<^sub>0, v\<^sub>1}
                \<and> x \<in> geotop_convex_hull {v\<^sub>0, v\<^sub>2}
                    \<union> geotop_convex_hull {v\<^sub>1, v\<^sub>2}"
              by (rule geotop_contact_outside_selected_union_avoids_selected_set_prefix
                  [OF h\<theta>_contact_on_other_named_edges hv\<^sub>0v\<^sub>1_selected])
            have h\<theta>_contact_on_other_nonbase_edge:
              "\<exists>x. x \<in> \<theta> \<inter> J'
                \<and> x \<in> (geotop_convex_hull {v\<^sub>0, v\<^sub>2} - {v\<^sub>0})
                    \<union> (geotop_convex_hull {v\<^sub>1, v\<^sub>2} - {v\<^sub>1})"
              by (rule geotop_other_edge_contact_not_base_avoids_base_endpoints_prefix
                  [OF h\<theta>_contact_on_other_not_base])
            have h\<theta>_contact_on_other_nonbase_segment:
              "\<exists>x. x \<in> \<theta> \<inter> J'
                \<and> x \<in> (closed_segment v\<^sub>0 v\<^sub>2 - {v\<^sub>0})
                    \<union> (closed_segment v\<^sub>1 v\<^sub>2 - {v\<^sub>1})"
              by (rule geotop_nonbase_edge_contact_geotop_to_closed_segment_prefix
                  [OF h\<theta>_contact_on_other_nonbase_edge])
            have h\<theta>_not_col: "\<not> collinear {v\<^sub>0, v\<^sub>2, v\<^sub>1}"
              by (rule geotop_2simplex_vertices_not_collinear_prefix
                  [OF h\<theta>_vertices hv\<^sub>0v\<^sub>1 hv\<^sub>2_not])
            have h\<theta>_contact_on_other_segment_off_base:
              "\<exists>x. x \<in> \<theta> \<inter> J'
                \<and> x \<notin> closed_segment v\<^sub>0 v\<^sub>1
                \<and> x \<in> (closed_segment v\<^sub>0 v\<^sub>2 - {v\<^sub>0})
                    \<union> (closed_segment v\<^sub>1 v\<^sub>2 - {v\<^sub>1})"
              by (rule geotop_nonbase_segment_contact_avoids_base_segment_prefix
                  [OF h\<theta>_not_col h\<theta>_contact_on_other_nonbase_segment])
            show ?thesis
              by (rule geotop_polygon_disk_nonfree_boundary_triangle_decomposition_free_count_prefix
                  [OF hJ' hK' hK_fin' hK_poly' hT_gt2 h\<theta>K h\<theta>2 h\<theta>_vertices
                    hv\<^sub>0v\<^sub>1 hv\<^sub>2_not hv\<^sub>0v\<^sub>1_sub_J h\<theta>_not_free])
          qed
        qed
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
