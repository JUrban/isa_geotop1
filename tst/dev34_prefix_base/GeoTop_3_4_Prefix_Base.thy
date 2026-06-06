theory GeoTop_3_4_Prefix_Base
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

lemma geotop_HOL_homeomorphism_imp_top1_homeomorphism_on_cross_prefix:
  fixes X :: "'a::real_normed_vector set" and Y :: "'b::real_normed_vector set"
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
  have h_Teucl_X: "is_topology_on (UNIV::'a set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have h_Teucl_Y: "is_topology_on (UNIV::'b set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have hTX: "is_topology_on X (subspace_topology UNIV geotop_euclidean_topology X)"
    by (rule subspace_topology_is_topology_on[OF h_Teucl_X subset_UNIV])
  have hTY: "is_topology_on Y (subspace_topology UNIV geotop_euclidean_topology Y)"
    by (rule subspace_topology_is_topology_on[OF h_Teucl_Y subset_UNIV])
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

lemma geotop_segment_face_cases_prefix:
  fixes F :: "(real^2) set" and a b :: "real^2"
  assumes hface: "geotop_is_face F (closed_segment a b)"
  assumes hab: "a \<noteq> b"
  shows "F = {a} \<or> F = {b} \<or> F = closed_segment a b"
  (**
    Prefix-local form of the closed-segment face classification. **)
proof -
  have hseg_sv: "geotop_simplex_vertices (closed_segment a b) {a, b}"
    by (rule geotop_closed_segment_simplex_vertices[OF hab])
  obtain V W where hV_sv: "geotop_simplex_vertices (closed_segment a b) V"
      and hW_ne: "W \<noteq> {}"
      and hW_sub: "W \<subseteq> V"
      and hF_hull: "F = geotop_convex_hull W"
    using hface unfolding geotop_is_face_def by (by100 blast)
  have hV_eq: "V = {a, b}"
    using geotop_simplex_vertices_unique[OF hV_sv hseg_sv] .
  have hW_sub_ab: "W \<subseteq> {a, b}"
    using hW_sub hV_eq by (by100 simp)
  have hW_cases: "W = {a} \<or> W = {b} \<or> W = {a, b}"
    using hW_sub_ab hW_ne by (by100 blast)
  have hF_HOL: "F = convex hull W"
    using hF_hull geotop_convex_hull_eq_HOL by (by100 simp)
  show ?thesis
  proof (rule disjE[OF hW_cases])
    assume hW_a: "W = {a}"
    have "F = {a}"
      using hF_HOL hW_a by (by100 simp)
    thus ?thesis by (by100 blast)
  next
    assume hW_rest: "W = {b} \<or> W = {a, b}"
    show ?thesis
    proof (rule disjE[OF hW_rest])
      assume hW_b: "W = {b}"
      have "F = {b}"
        using hF_HOL hW_b by (by100 simp)
      thus ?thesis by (by100 blast)
    next
      assume hW_ab: "W = {a, b}"
      have "F = convex hull {a, b}"
        using hF_HOL hW_ab by (by100 simp)
      also have "\<dots> = closed_segment a b"
        using segment_convex_hull[of a b] by (by100 simp)
      finally have "F = closed_segment a b" .
      thus ?thesis by (by100 blast)
    qed
  qed
qed

lemma geotop_complex_distinct_intersecting_edges_inter_singleton_prefix:
  fixes K :: "(real^2) set set" and e\<^sub>1 e\<^sub>2 :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes he\<^sub>1K: "e\<^sub>1 \<in> K" and he\<^sub>2K: "e\<^sub>2 \<in> K"
  assumes he\<^sub>1_edge: "geotop_is_edge e\<^sub>1"
  assumes he\<^sub>2_edge: "geotop_is_edge e\<^sub>2"
  assumes hne: "e\<^sub>1 \<noteq> e\<^sub>2"
  assumes hInt: "e\<^sub>1 \<inter> e\<^sub>2 \<noteq> {}"
  shows "\<exists>p. e\<^sub>1 \<inter> e\<^sub>2 = {p}"
proof -
  have hK_inter: "\<forall>\<sigma>\<in>K. \<forall>\<tau>\<in>K. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
      geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    using hK unfolding geotop_is_complex_def by (by100 blast)
  have hface\<^sub>1: "geotop_is_face (e\<^sub>1 \<inter> e\<^sub>2) e\<^sub>1"
    using hK_inter he\<^sub>1K he\<^sub>2K hInt by (by100 blast)
  obtain a b where hab: "a \<noteq> b" and he\<^sub>1_eq: "e\<^sub>1 = closed_segment a b"
    by (rule geotop_edge_closed_segment_obtain_prefix[OF he\<^sub>1_edge])
  have hcases:
      "e\<^sub>1 \<inter> e\<^sub>2 = {a} \<or> e\<^sub>1 \<inter> e\<^sub>2 = {b}
        \<or> e\<^sub>1 \<inter> e\<^sub>2 = closed_segment a b"
    using geotop_segment_face_cases_prefix[OF _ hab] hface\<^sub>1 he\<^sub>1_eq by (by100 simp)
  show ?thesis
  proof (rule disjE[OF hcases])
    assume "e\<^sub>1 \<inter> e\<^sub>2 = {a}"
    thus ?thesis by (by100 blast)
  next
    assume hrest: "e\<^sub>1 \<inter> e\<^sub>2 = {b} \<or> e\<^sub>1 \<inter> e\<^sub>2 = closed_segment a b"
    show ?thesis
    proof (rule disjE[OF hrest])
      assume "e\<^sub>1 \<inter> e\<^sub>2 = {b}"
      thus ?thesis by (by100 blast)
    next
      assume hcap_seg: "e\<^sub>1 \<inter> e\<^sub>2 = closed_segment a b"
      have he\<^sub>1_sub_e\<^sub>2: "e\<^sub>1 \<subseteq> e\<^sub>2"
        using hcap_seg he\<^sub>1_eq by (by100 blast)
      have hface: "geotop_is_face e\<^sub>1 e\<^sub>2"
        by (rule geotop_complex_subset_simplex_face_prefix
            [OF hK he\<^sub>1K he\<^sub>2K he\<^sub>1_sub_e\<^sub>2])
      have "e\<^sub>1 = e\<^sub>2"
        by (rule geotop_edge_face_of_edge_eq_prefix
            [OF he\<^sub>1_edge he\<^sub>2_edge hface])
      thus ?thesis using hne by (by100 blast)
    qed
  qed
qed

lemma geotop_complex_two_intersecting_edges_union_broken_line_prefix:
  fixes K :: "(real^2) set set" and e\<^sub>1 e\<^sub>2 :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes he\<^sub>1K: "e\<^sub>1 \<in> K" and he\<^sub>2K: "e\<^sub>2 \<in> K"
  assumes he\<^sub>1_edge: "geotop_is_edge e\<^sub>1"
  assumes he\<^sub>2_edge: "geotop_is_edge e\<^sub>2"
  assumes hne: "e\<^sub>1 \<noteq> e\<^sub>2"
  assumes hInt: "e\<^sub>1 \<inter> e\<^sub>2 \<noteq> {}"
  shows "geotop_is_broken_line (e\<^sub>1 \<union> e\<^sub>2)"
proof -
  obtain p where hcap: "e\<^sub>1 \<inter> e\<^sub>2 = {p}"
    using geotop_complex_distinct_intersecting_edges_inter_singleton_prefix
      [OF hK he\<^sub>1K he\<^sub>2K he\<^sub>1_edge he\<^sub>2_edge hne hInt]
    by (by100 blast)
  obtain a b where hab: "a \<noteq> b" and he\<^sub>1_ab: "e\<^sub>1 = closed_segment a b"
    by (rule geotop_edge_closed_segment_obtain_prefix[OF he\<^sub>1_edge])
  obtain c d where hcd: "c \<noteq> d" and he\<^sub>2_cd: "e\<^sub>2 = closed_segment c d"
    by (rule geotop_edge_closed_segment_obtain_prefix[OF he\<^sub>2_edge])
  have hp_e\<^sub>1: "p \<in> e\<^sub>1"
    using hcap by (by100 blast)
  have hp_e\<^sub>2: "p \<in> e\<^sub>2"
    using hcap by (by100 blast)
  have hK_inter: "\<forall>\<sigma>\<in>K. \<forall>\<tau>\<in>K. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
      geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    using hK unfolding geotop_is_complex_def by (by100 blast)
  have hface\<^sub>1: "geotop_is_face (e\<^sub>1 \<inter> e\<^sub>2) e\<^sub>1"
    using hK_inter he\<^sub>1K he\<^sub>2K hInt by (by100 blast)
  have hface\<^sub>2: "geotop_is_face (e\<^sub>1 \<inter> e\<^sub>2) e\<^sub>2"
    using hK_inter he\<^sub>1K he\<^sub>2K hInt by (by100 blast)
  have hcases\<^sub>1:
      "e\<^sub>1 \<inter> e\<^sub>2 = {a} \<or> e\<^sub>1 \<inter> e\<^sub>2 = {b}
        \<or> e\<^sub>1 \<inter> e\<^sub>2 = closed_segment a b"
    using geotop_segment_face_cases_prefix[OF _ hab] hface\<^sub>1 he\<^sub>1_ab by (by100 simp)
  have hp_ab: "p = a \<or> p = b"
  proof -
    have "e\<^sub>1 \<inter> e\<^sub>2 \<noteq> closed_segment a b"
    proof
      assume hbad: "e\<^sub>1 \<inter> e\<^sub>2 = closed_segment a b"
      have "e\<^sub>1 \<subseteq> e\<^sub>2"
        using hbad he\<^sub>1_ab by (by100 blast)
      hence "geotop_is_face e\<^sub>1 e\<^sub>2"
        by (rule geotop_complex_subset_simplex_face_prefix[OF hK he\<^sub>1K he\<^sub>2K])
      hence "e\<^sub>1 = e\<^sub>2"
        by (rule geotop_edge_face_of_edge_eq_prefix[OF he\<^sub>1_edge he\<^sub>2_edge])
      thus False using hne by (by100 blast)
    qed
    thus ?thesis
      using hcases\<^sub>1 hcap by (by100 blast)
  qed
  have hcases\<^sub>2:
      "e\<^sub>1 \<inter> e\<^sub>2 = {c} \<or> e\<^sub>1 \<inter> e\<^sub>2 = {d}
        \<or> e\<^sub>1 \<inter> e\<^sub>2 = closed_segment c d"
    using geotop_segment_face_cases_prefix[OF _ hcd] hface\<^sub>2 he\<^sub>2_cd by (by100 simp)
  have hp_cd: "p = c \<or> p = d"
  proof -
    have "e\<^sub>1 \<inter> e\<^sub>2 \<noteq> closed_segment c d"
    proof
      assume hbad: "e\<^sub>1 \<inter> e\<^sub>2 = closed_segment c d"
      have "e\<^sub>2 \<subseteq> e\<^sub>1"
        using hbad he\<^sub>2_cd by (by100 blast)
      hence "geotop_is_face e\<^sub>2 e\<^sub>1"
        by (rule geotop_complex_subset_simplex_face_prefix[OF hK he\<^sub>2K he\<^sub>1K])
      hence "e\<^sub>2 = e\<^sub>1"
        by (rule geotop_edge_face_of_edge_eq_prefix[OF he\<^sub>2_edge he\<^sub>1_edge])
      thus False using hne by (by100 blast)
    qed
    thus ?thesis
      using hcases\<^sub>2 hcap by (by100 blast)
  qed
  obtain q where hq_ne_p: "q \<noteq> p" and he\<^sub>1_qp: "e\<^sub>1 = closed_segment q p"
  proof (rule disjE[OF hp_ab])
    assume hpa: "p = a"
    have hb_ne_p: "b \<noteq> p"
      using hab hpa by (by100 blast)
    have he\<^sub>1_bp: "e\<^sub>1 = closed_segment b p"
      using he\<^sub>1_ab hpa closed_segment_commute[of a b] by (by100 simp)
    show ?thesis
      by (rule that[OF hb_ne_p he\<^sub>1_bp])
  next
    assume hpb: "p = b"
    have ha_ne_p: "a \<noteq> p"
      using hab hpb by (by100 blast)
    have he\<^sub>1_ap: "e\<^sub>1 = closed_segment a p"
      using he\<^sub>1_ab hpb by (by100 simp)
    show ?thesis
      by (rule that[OF ha_ne_p he\<^sub>1_ap])
  qed
  obtain r where hr_ne_p: "r \<noteq> p" and he\<^sub>2_pr: "e\<^sub>2 = closed_segment p r"
  proof (rule disjE[OF hp_cd])
    assume hpc: "p = c"
    have hd_ne_p: "d \<noteq> p"
      using hcd hpc by (by100 blast)
    have he\<^sub>2_pd: "e\<^sub>2 = closed_segment p d"
      using he\<^sub>2_cd hpc by (by100 simp)
    show ?thesis
      by (rule that[OF hd_ne_p he\<^sub>2_pd])
  next
    assume hpd: "p = d"
    have hc_ne_p: "c \<noteq> p"
      using hcd hpd by (by100 blast)
    have he\<^sub>2_pc: "e\<^sub>2 = closed_segment p c"
      using he\<^sub>2_cd hpd closed_segment_commute[of c d] by (by100 simp)
    show ?thesis
      by (rule that[OF hc_ne_p he\<^sub>2_pc])
  qed
  have hB\<^sub>1: "geotop_is_broken_line e\<^sub>1"
    using geotop_closed_segment_is_broken_line[OF hq_ne_p] he\<^sub>1_qp by (by100 simp)
  have hB\<^sub>2: "geotop_is_broken_line e\<^sub>2"
    using geotop_closed_segment_is_broken_line[OF hr_ne_p] he\<^sub>2_pr
      closed_segment_commute[of p r]
    by (by100 simp)
  have hR_end_1:
      "\<exists>\<gamma>\<^sub>1. arc \<gamma>\<^sub>1 \<and> path_image \<gamma>\<^sub>1 = e\<^sub>1 \<and> pathfinish \<gamma>\<^sub>1 = p"
  proof (rule exI[where x = "linepath q p"])
    show "arc (linepath q p) \<and> path_image (linepath q p) = e\<^sub>1
        \<and> pathfinish (linepath q p) = p"
      using arc_linepath[OF hq_ne_p] he\<^sub>1_qp by (by100 simp)
  qed
  have hR_end_2:
      "\<exists>\<gamma>\<^sub>2. arc \<gamma>\<^sub>2 \<and> path_image \<gamma>\<^sub>2 = e\<^sub>2 \<and> pathstart \<gamma>\<^sub>2 = p"
  proof (rule exI[where x = "linepath p r"])
    have hpr: "p \<noteq> r"
      using hr_ne_p by (by100 blast)
    show "arc (linepath p r) \<and> path_image (linepath p r) = e\<^sub>2
        \<and> pathstart (linepath p r) = p"
      using arc_linepath[OF hpr] he\<^sub>2_pr by (by100 simp)
  qed
  show ?thesis
    by (rule geotop_broken_lines_glue_disjoint_endpoints
        [OF hB\<^sub>1 hB\<^sub>2 hR_end_1 hR_end_2 hcap])
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

lemma geotop_complex_no_2_simplex_over_edge_rel_interior_open_prefix:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hno2: "\<not> (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>)"
  shows "rel_interior e \<in>
    subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
  (**
    Prefix-local version of the edge-with-no-2-simplex neighborhood fact:
    if no 2-simplex lies over an edge, the edge interior is open in the
    carrier subspace. **)
proof -
  obtain a b where hab: "a \<noteq> b" and he_seg: "e = closed_segment a b"
    by (rule geotop_edge_closed_segment_obtain_prefix[OF hedge])
  have hrel_eq: "rel_interior e = open_segment a b"
    using he_seg hab rel_interior_closed_segment[of a b] by (by100 simp)
  have hrel_as_diff: "rel_interior e = e - {a, b}"
    using hrel_eq he_seg unfolding open_segment_def by (by100 simp)
  have hlocal_fin:
    "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]]])
  have hlocal_e: "\<exists>U. open U \<and> e \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule bspec[OF hlocal_fin heK])
  obtain U where hU_open: "open U"
    and heU: "e \<subseteq> U"
    and hU_fin: "finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    using hlocal_e by (elim exE conjE)
  let ?F = "{\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
  let ?Bad = "{\<tau>\<in>?F. \<tau> \<inter> rel_interior e = {}}"
  have hBad_fin: "finite ?Bad"
  proof -
    have "?Bad \<subseteq> ?F"
      by (by100 blast)
    show ?thesis
      by (rule finite_subset[OF \<open>?Bad \<subseteq> ?F\<close> hU_fin])
  qed
  have hBad_closed: "\<forall>\<tau>\<in>?Bad. closed \<tau>"
  proof
    fix \<tau> assume h\<tau>: "\<tau> \<in> ?Bad"
    have h\<tau>K: "\<tau> \<in> K"
      using h\<tau> by (by100 simp)
    show "closed \<tau>"
      by (rule geotop_complex_simplex_closed[OF hK h\<tau>K])
  qed
  have hB_closed: "closed (\<Union>?Bad)"
    by (rule closed_Union[OF hBad_fin hBad_closed])
  have hend_closed: "closed ({a, b}::(real^2) set)"
    by (by100 simp)
  define W where "W = U - \<Union>?Bad - {a, b}"
  have hW_open_HOL: "open W"
  proof -
    have hU_B_open: "open (U - \<Union>?Bad)"
      by (rule open_Diff[OF hU_open hB_closed])
    show ?thesis
      unfolding W_def by (rule open_Diff[OF hU_B_open hend_closed])
  qed
  have hpoly_inter_W: "geotop_polyhedron K \<inter> W = rel_interior e"
  proof
    show "geotop_polyhedron K \<inter> W \<subseteq> rel_interior e"
    proof
      fix x assume hx: "x \<in> geotop_polyhedron K \<inter> W"
      have hx_poly: "x \<in> geotop_polyhedron K"
        using hx by (by100 simp)
      have hxW: "x \<in> W"
        using hx by (by100 simp)
      have hxU: "x \<in> U"
        using hxW unfolding W_def by (by100 simp)
      have hx_not_end: "x \<notin> {a, b}"
        using hxW unfolding W_def by (by100 simp)
      obtain \<tau> where h\<tau>K: "\<tau> \<in> K" and hx\<tau>: "x \<in> \<tau>"
        using hx_poly unfolding geotop_polyhedron_def by (by100 blast)
      have h\<tau>F: "\<tau> \<in> ?F"
        using h\<tau>K hx\<tau> hxU by (by100 blast)
      have h\<tau>meet: "\<tau> \<inter> rel_interior e \<noteq> {}"
      proof (rule ccontr)
        assume "\<not> \<tau> \<inter> rel_interior e \<noteq> {}"
        hence h\<tau>bad: "\<tau> \<in> ?Bad"
          using h\<tau>F by (by100 simp)
        have "x \<in> \<Union>?Bad"
          using h\<tau>bad hx\<tau> by (by100 blast)
        thus False
          using hxW unfolding W_def by (by100 simp)
      qed
      have h\<tau>sube: "\<tau> \<subseteq> e"
        by (rule geotop_no_2_simplex_containing_edge_simplex_meeting_rel_interior_subset_prefix
            [OF hK heK h\<tau>K hedge h\<tau>meet hno2])
      have hxe: "x \<in> e"
        using h\<tau>sube hx\<tau> by (by100 blast)
      show "x \<in> rel_interior e"
        using hxe hx_not_end hrel_as_diff by (by100 blast)
    qed
  next
    show "rel_interior e \<subseteq> geotop_polyhedron K \<inter> W"
    proof
      fix x assume hxrel: "x \<in> rel_interior e"
      have hxe: "x \<in> e"
        using hxrel rel_interior_subset by (by100 blast)
      have hx_poly: "x \<in> geotop_polyhedron K"
        using heK hxe unfolding geotop_polyhedron_def by (by100 blast)
      have hxU: "x \<in> U"
        using heU hxe by (by100 blast)
      have hx_not_B: "x \<notin> \<Union>?Bad"
      proof
        assume "x \<in> \<Union>?Bad"
        then obtain \<tau> where h\<tau>bad: "\<tau> \<in> ?Bad" and hx\<tau>: "x \<in> \<tau>"
          by (by100 blast)
        have "\<tau> \<inter> rel_interior e \<noteq> {}"
          using hx\<tau> hxrel by (by100 blast)
        thus False
          using h\<tau>bad by (by100 simp)
      qed
      have hx_not_end: "x \<notin> {a, b}"
        using hxrel hrel_as_diff by (by100 blast)
      have hxW: "x \<in> W"
        unfolding W_def using hxU hx_not_B hx_not_end by (by100 simp)
      show "x \<in> geotop_polyhedron K \<inter> W"
        using hx_poly hxW by (by100 simp)
    qed
  qed
  have hW_top: "W \<in> geotop_euclidean_topology"
    by (metis hW_open_HOL geotop_euclidean_topology_eq_open_sets
        mem_Collect_eq top1_open_sets_def)
  show ?thesis
    unfolding subspace_topology_def
    using hW_top hpoly_inter_W by (by100 blast)
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

lemma geotop_broken_line_subarc_with_endpoints_prefix:
  fixes B :: "(real^2) set"
  assumes hB: "geotop_is_broken_line B"
  assumes hX: "X \<in> B"
  assumes hY: "Y \<in> B"
  assumes hXY: "X \<noteq> Y"
  shows "\<exists>B'. geotop_is_broken_line B' \<and> B' \<subseteq> B
      \<and> X \<in> B' \<and> Y \<in> B' \<and> geotop_arc_endpoints B' {X, Y}"
proof -
  obtain B' where hB': "geotop_is_broken_line B'"
      and hB'_sub: "B' \<subseteq> B"
      and hXB': "X \<in> B'"
      and hYB': "Y \<in> B'"
      and harc_data:
        "X = Y \<or> (\<exists>\<gamma>'. arc \<gamma>' \<and> path_image \<gamma>' = B'
          \<and> pathstart \<gamma>' = X \<and> pathfinish \<gamma>' = Y)"
    using geotop_broken_line_subarc[OF hB hX hY] by (by100 blast)
  obtain \<gamma>' where h\<gamma>_arc: "arc \<gamma>'"
      and h\<gamma>_img: "path_image \<gamma>' = B'"
      and h\<gamma>_start: "pathstart \<gamma>' = X"
      and h\<gamma>_finish: "pathfinish \<gamma>' = Y"
    using harc_data hXY by (by100 blast)
  have hE_raw: "geotop_arc_endpoints (path_image \<gamma>')
      {pathstart \<gamma>', pathfinish \<gamma>'}"
    by (rule geotop_HOL_arc_imp_geotop_arc_endpoints_prefix[OF h\<gamma>_arc])
  have hE: "geotop_arc_endpoints B' {X, Y}"
    using hE_raw h\<gamma>_img h\<gamma>_start h\<gamma>_finish by (by100 simp)
  show ?thesis
    using hB' hB'_sub hXB' hYB' hE by (by100 blast)
qed

lemma geotop_arc_endpoints_pair_data_prefix:
  fixes A :: "(real^2) set"
  assumes hE: "geotop_arc_endpoints A {P, Q}"
  shows "P \<noteq> Q \<and> P \<in> A \<and> Q \<in> A"
proof -
  have hcard: "card {P, Q} = 2"
    using hE unfolding geotop_arc_endpoints_def by (by100 blast)
  have hsub: "{P, Q} \<subseteq> A"
    using hE unfolding geotop_arc_endpoints_def by (by100 blast)
  have hPQ: "P \<noteq> Q"
  proof
    assume heq: "P = Q"
    have "card {P, Q} = 1"
      using heq by (by100 simp)
    thus False
      using hcard by (by100 simp)
  qed
  have hPA: "P \<in> A"
    using hsub by (by100 blast)
  have hQA: "Q \<in> A"
    using hsub by (by100 blast)
  show ?thesis
    using hPQ hPA hQA by (by100 blast)
qed

lemma geotop_same_endpoint_arcs_inter_eq_prefix:
  fixes B\<^sub>1 B\<^sub>2 E :: "(real^2) set"
  assumes hE\<^sub>1: "geotop_arc_endpoints B\<^sub>1 E"
  assumes hE\<^sub>2: "geotop_arc_endpoints B\<^sub>2 E"
  assumes hdisj:
    "geotop_arc_interior B\<^sub>1 E \<inter> geotop_arc_interior B\<^sub>2 E = {}"
  shows "B\<^sub>1 \<inter> B\<^sub>2 = E"
proof
  show "B\<^sub>1 \<inter> B\<^sub>2 \<subseteq> E"
  proof
    fix x
    assume hx: "x \<in> B\<^sub>1 \<inter> B\<^sub>2"
    show "x \<in> E"
    proof (rule ccontr)
      assume hx_not_E: "x \<notin> E"
      have hx_int_1: "x \<in> geotop_arc_interior B\<^sub>1 E"
        using hx hx_not_E unfolding geotop_arc_interior_def by (by100 blast)
      have hx_int_2: "x \<in> geotop_arc_interior B\<^sub>2 E"
        using hx hx_not_E unfolding geotop_arc_interior_def by (by100 blast)
      have "x \<in> geotop_arc_interior B\<^sub>1 E \<inter> geotop_arc_interior B\<^sub>2 E"
        using hx_int_1 hx_int_2 by (by100 blast)
      thus False
        using hdisj by (by100 blast)
    qed
  qed
next
  show "E \<subseteq> B\<^sub>1 \<inter> B\<^sub>2"
  proof -
    have hE_sub_1: "E \<subseteq> B\<^sub>1"
      using hE\<^sub>1 unfolding geotop_arc_endpoints_def by (by100 blast)
    have hE_sub_2: "E \<subseteq> B\<^sub>2"
      using hE\<^sub>2 unfolding geotop_arc_endpoints_def by (by100 blast)
    show ?thesis
      using hE_sub_1 hE_sub_2 by (by100 blast)
  qed
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

lemma geotop_polygon_disk_complex_finite_prefix:
  fixes J :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hK_poly: "geotop_polyhedron K =
      closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  shows "finite K"
  (**
    Compactness form of Moise's finite-polyhedron assertion: any locally
    finite complex whose carrier is the closed polygonal disk
    \<open>closure (Int J)\<close> is finite. **)
proof -
  have hJ_n_sph: "geotop_is_n_sphere J
      (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ unfolding geotop_is_polygon_def by (by100 blast)
  have h_int_bd: "bounded (geotop_polygon_interior J)"
    by (rule polygon_interior_bounded[OF hJ_n_sph])
  have h_clos_eq: "closure_on UNIV geotop_euclidean_topology
        (geotop_polygon_interior J) = closure (geotop_polygon_interior J)"
    by (rule closure_on_geotop_UNIV_eq_closure)
  have h_clos_bd: "bounded (closure (geotop_polygon_interior J))"
    using h_int_bd bounded_closure by (by100 blast)
  have h_clos_closed: "closed (closure (geotop_polygon_interior J))"
    by (by100 simp)
  have h_clos_compact: "compact (closure (geotop_polygon_interior J))"
    using h_clos_bd h_clos_closed compact_eq_bounded_closed by (by100 blast)
  have hK_poly_compact: "compact (geotop_polyhedron K)"
    using hK_poly h_clos_eq h_clos_compact by (by100 simp)
  show ?thesis
    by (rule compact_polyhedron_imp_finite_complex[OF hK hK_poly_compact])
qed

lemma geotop_polygon_finite_1dim_complex_with_two_vertices_prefix:
  fixes J :: "(real^2) set" and P Q :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hP: "P \<in> J"
  assumes hQ: "Q \<in> J"
  shows "\<exists>L. geotop_is_complex L \<and> finite L \<and> geotop_complex_is_1dim L
      \<and> geotop_polyhedron L = J \<and> {P} \<in> L \<and> {Q} \<in> L"
  (**
    Polygon-boundary graph witness with chosen vertices.  This packages the
    definition of polygon as a finite polyhedral 1-sphere and then subdivides
    its 1-dimensional witness complex at the two requested boundary points. **)
proof -
  obtain K where hK: "geotop_is_complex K"
      and hK_fin: "finite K"
      and hK_poly: "geotop_polyhedron K = J"
    using geotop_polygon_finite_triangulation[OF hJ] by (by100 blast)
  have hdim_le:
    "\<forall>\<sigma>\<in>K. \<forall>k. geotop_simplex_dim \<sigma> k \<longrightarrow> k \<le> 1"
    by (rule polygon_complex_dim_le_1[OF hJ hK hK_poly])
  have hK_1dim: "geotop_complex_is_1dim K"
  proof (unfold geotop_complex_is_1dim_def, intro ballI)
    fix \<sigma>
    assume h\<sigma>K: "\<sigma> \<in> K"
    have h\<sigma>_simp: "geotop_is_simplex \<sigma>"
      using geotop_is_complex_simplex[OF hK] h\<sigma>K by (by100 blast)
    obtain V m n where hV_fin: "finite V"
      and hV_card: "card V = n + 1"
      and hn_m: "n \<le> m"
      and hV_gp: "geotop_general_position V m"
      and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
      using h\<sigma>_simp unfolding geotop_is_simplex_def by (by100 blast)
    have h\<sigma>_dim: "geotop_simplex_dim \<sigma> n"
      unfolding geotop_simplex_dim_def
      using hV_fin hV_card hn_m hV_gp h\<sigma>_eq by (by100 blast)
    have hn_le: "n \<le> 1"
      using hdim_le h\<sigma>K h\<sigma>_dim by (by100 blast)
    show "\<exists>n\<le>1. geotop_simplex_dim \<sigma> n"
      using hn_le h\<sigma>_dim by (by100 blast)
  qed
  have hP_poly: "P \<in> geotop_polyhedron K"
    using hP hK_poly by (by100 simp)
  have hQ_poly: "Q \<in> geotop_polyhedron K"
    using hQ hK_poly by (by100 simp)
  obtain L where hL: "geotop_is_complex L"
      and hL_1dim: "geotop_complex_is_1dim L"
      and hL_poly: "geotop_polyhedron L = geotop_polyhedron K"
      and hPL: "{P} \<in> L"
      and hQL: "{Q} \<in> L"
      and hL_fin_imp: "finite K \<longrightarrow> finite L"
    using geotop_complex_subdivide_at_two[OF hK hK_1dim hP_poly hQ_poly]
    by (by100 blast)
  have hL_fin: "finite L"
    using hL_fin_imp hK_fin by (by100 blast)
  have hL_poly_J: "geotop_polyhedron L = J"
    using hL_poly hK_poly by (by100 simp)
  show ?thesis
    using hL hL_fin hL_1dim hL_poly_J hPL hQL by (by100 blast)
qed

lemma geotop_complex_1dim_imp_linear_graph_prefix:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hK1: "geotop_complex_is_1dim K"
  shows "geotop_is_linear_graph K"
proof -
  have hdim: "\<forall>\<sigma>\<in>K. \<exists>i\<le>1. geotop_simplex_dim \<sigma> i"
    using hK1 unfolding geotop_complex_is_1dim_def by (by100 simp)
  show ?thesis
    unfolding geotop_is_linear_graph_def using hK hdim by (by100 simp)
qed

lemma geotop_polygon_finite_linear_graph_with_two_vertices_prefix:
  fixes J :: "(real^2) set" and P Q :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hP: "P \<in> J"
  assumes hQ: "Q \<in> J"
  shows "\<exists>L. geotop_is_linear_graph L \<and> finite L
      \<and> geotop_polyhedron L = J \<and> {P} \<in> L \<and> {Q} \<in> L"
proof -
  obtain L where hL: "geotop_is_complex L"
      and hL_fin: "finite L"
      and hL_1dim: "geotop_complex_is_1dim L"
      and hL_poly: "geotop_polyhedron L = J"
      and hPL: "{P} \<in> L"
      and hQL: "{Q} \<in> L"
    using geotop_polygon_finite_1dim_complex_with_two_vertices_prefix
      [OF hJ hP hQ] by (by100 blast)
  have hL_linear: "geotop_is_linear_graph L"
    by (rule geotop_complex_1dim_imp_linear_graph_prefix[OF hL hL_1dim])
  show ?thesis
    using hL_linear hL_fin hL_poly hPL hQL by (by100 blast)
qed

lemma geotop_complex_connected_top1_connected_polyhedron_prefix:
  fixes K :: "(real^2) set set"
  assumes hconn: "geotop_complex_connected K"
  shows "top1_connected_on (geotop_polyhedron K)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
proof -
  have hcomplex: "geotop_is_complex K"
    using hconn unfolding geotop_complex_connected_def by (by100 blast)
  have hpath: "top1_path_connected_on (geotop_polyhedron K)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
    using Theorem_GT_1_12(1)[OF hcomplex] hconn by (by100 blast)
  show ?thesis
    using Theorem_GT_1_12(2)[OF hcomplex] hpath by (by100 blast)
qed

lemma geotop_finite_linear_graph_polygon_polyhedron_connected_prefix:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron L)"
  shows "geotop_complex_connected L"
proof -
  have hL_complex: "geotop_is_complex L"
    using hL_linear unfolding geotop_is_linear_graph_def by (by100 blast)
  have hhomeo: "geotop_polyhedron L homeomorphic sphere (0::real^2) 1"
    by (rule polygon_homeomorphic_S1_helper[OF hpolygon])
  have hdim: "(2::nat) \<le> DIM(real^2)"
    by (by100 simp)
  have hsphere_conn: "connected (sphere (0::real^2) 1)"
    by (rule connected_sphere[OF hdim])
  have hpoly_conn_HOL: "connected (geotop_polyhedron L)"
    using hhomeo hsphere_conn homeomorphic_connectedness by (by100 blast)
  have hpoly_conn:
      "top1_connected_on (geotop_polyhedron L)
        (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    using hpoly_conn_HOL top1_connected_on_geotop_iff_connected by (by100 blast)
  have hpath:
      "top1_path_connected_on (geotop_polyhedron L)
        (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    by (rule iffD2[OF Theorem_GT_1_12(2)[OF hL_complex] hpoly_conn])
  show ?thesis
    by (rule iffD2[OF Theorem_GT_1_12(1)[OF hL_complex] hpath])
qed

lemma geotop_polygon_finite_connected_linear_graph_with_two_vertices_prefix:
  fixes J :: "(real^2) set" and P Q :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hP: "P \<in> J"
  assumes hQ: "Q \<in> J"
  shows "\<exists>L. geotop_is_linear_graph L \<and> finite L
      \<and> geotop_complex_connected L
      \<and> geotop_polyhedron L = J \<and> {P} \<in> L \<and> {Q} \<in> L"
proof -
  obtain L where hL_linear: "geotop_is_linear_graph L"
      and hL_fin: "finite L"
      and hL_poly: "geotop_polyhedron L = J"
      and hPL: "{P} \<in> L"
      and hQL: "{Q} \<in> L"
    using geotop_polygon_finite_linear_graph_with_two_vertices_prefix
      [OF hJ hP hQ] by (by100 blast)
  have hpolygon_L: "geotop_is_polygon (geotop_polyhedron L)"
    using hJ hL_poly by (by100 simp)
  have hL_conn: "geotop_complex_connected L"
    by (rule geotop_finite_linear_graph_polygon_polyhedron_connected_prefix
        [OF hL_linear hpolygon_L])
  show ?thesis
    using hL_linear hL_fin hL_conn hL_poly hPL hQL by (by100 blast)
qed

lemma top1_homeomorphism_on_subspace_image_prefix:
  assumes hhomeo: "top1_homeomorphism_on X TX Y TY f"
  assumes hA: "A \<subseteq> X"
  shows "top1_homeomorphism_on A (subspace_topology X TX A)
      (f ` A) (subspace_topology Y TY (f ` A)) f"
proof -
  have hTX: "is_topology_on X TX"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hTY: "is_topology_on Y TY"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hbij: "bij_betw f X Y"
    by (rule top1_homeomorphism_on_imp_bij[OF hhomeo])
  have hmapX: "f ` X = Y"
    using hbij unfolding bij_betw_def by (by100 blast)
  have hImg_subY: "f ` A \<subseteq> Y"
    using hA hmapX by (by100 blast)
  have hinjX: "inj_on f X"
    using hbij by (rule bij_betw_imp_inj_on)
  have hinjA: "inj_on f A"
    by (rule inj_on_subset[OF hinjX hA])
  have htopA: "is_topology_on A (subspace_topology X TX A)"
    by (rule subspace_topology_is_topology_on[OF hTX hA])
  have htopImg: "is_topology_on (f ` A) (subspace_topology Y TY (f ` A))"
    by (rule subspace_topology_is_topology_on[OF hTY hImg_subY])
  have hbijA: "bij_betw f A (f ` A)"
    unfolding bij_betw_def using hinjA by (by100 blast)
  have hcont_f: "top1_continuous_map_on X TX Y TY f"
    by (rule top1_homeomorphism_on_imp_cont1[OF hhomeo])
  have hcont_A: "top1_continuous_map_on A (subspace_topology X TX A)
      (f ` A) (subspace_topology Y TY (f ` A)) f"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>A. f x \<in> f ` A"
      by (by100 blast)
    show "\<forall>V\<in>subspace_topology Y TY (f ` A).
        {x \<in> A. f x \<in> V} \<in> subspace_topology X TX A"
    proof
      fix V
      assume hV: "V \<in> subspace_topology Y TY (f ` A)"
      obtain W where hW: "W \<in> TY" and hVeq: "V = f ` A \<inter> W"
        using hV unfolding subspace_topology_def by (by100 blast)
      have hpreX: "{x \<in> X. f x \<in> W} \<in> TX"
        using hcont_f hW unfolding top1_continuous_map_on_def by (by100 blast)
      have hpre_eq: "{x \<in> A. f x \<in> V} = A \<inter> {x \<in> X. f x \<in> W}"
        using hA hVeq by (by100 blast)
      show "{x \<in> A. f x \<in> V} \<in> subspace_topology X TX A"
        unfolding hpre_eq subspace_topology_def using hpreX by (by100 blast)
    qed
  qed
  have hcont_inv: "top1_continuous_map_on Y TY X TX (inv_into X f)"
    by (rule top1_homeomorphism_on_imp_cont2[OF hhomeo])
  have hcont_inv_A: "top1_continuous_map_on (f ` A)
      (subspace_topology Y TY (f ` A)) A (subspace_topology X TX A)
      (inv_into A f)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>y\<in>f ` A. inv_into A f y \<in> A"
      using hinjA by (by100 simp)
    show "\<forall>V\<in>subspace_topology X TX A.
        {y \<in> f ` A. inv_into A f y \<in> V} \<in>
        subspace_topology Y TY (f ` A)"
    proof
      fix V
      assume hV: "V \<in> subspace_topology X TX A"
      obtain W where hW: "W \<in> TX" and hVeq: "V = A \<inter> W"
        using hV unfolding subspace_topology_def by (by100 blast)
      have hpreY: "{y \<in> Y. inv_into X f y \<in> W} \<in> TY"
        using hcont_inv hW unfolding top1_continuous_map_on_def by (by100 blast)
      have hpre_eq:
        "{y \<in> f ` A. inv_into A f y \<in> V} =
         (f ` A) \<inter> {y \<in> Y. inv_into X f y \<in> W}"
      proof
        show "{y \<in> f ` A. inv_into A f y \<in> V} \<subseteq>
            (f ` A) \<inter> {y \<in> Y. inv_into X f y \<in> W}"
        proof
          fix y
          assume hy: "y \<in> {y \<in> f ` A. inv_into A f y \<in> V}"
          obtain a where haA: "a \<in> A" and hyfa: "y = f a"
            using hy by (by100 blast)
          have haX: "a \<in> X"
            using hA haA by (by100 blast)
          have hinvA: "inv_into A f y = a"
            using hinjA haA hyfa by (by100 simp)
          have hinvX: "inv_into X f y = a"
            using hinjX haX hyfa by (by100 simp)
          have haW: "a \<in> W"
            using hy hVeq hinvA by (by100 blast)
          have hyY: "y \<in> Y"
            using hImg_subY hy by (by100 blast)
          show "y \<in> (f ` A) \<inter> {y \<in> Y. inv_into X f y \<in> W}"
            using hy hyY hinvX haW by (by100 blast)
        qed
      next
        show "(f ` A) \<inter> {y \<in> Y. inv_into X f y \<in> W} \<subseteq>
            {y \<in> f ` A. inv_into A f y \<in> V}"
        proof
          fix y
          assume hy: "y \<in> (f ` A) \<inter> {y \<in> Y. inv_into X f y \<in> W}"
          obtain a where haA: "a \<in> A" and hyfa: "y = f a"
            using hy by (by100 blast)
          have haX: "a \<in> X"
            using hA haA by (by100 blast)
          have hinvA: "inv_into A f y = a"
            using hinjA haA hyfa by (by100 simp)
          have hinvX: "inv_into X f y = a"
            using hinjX haX hyfa by (by100 simp)
          have haW: "a \<in> W"
            using hy hinvX by (by100 blast)
          have hinvA_V: "inv_into A f y \<in> V"
            using hVeq hinvA haA haW by (by100 blast)
          show "y \<in> {y \<in> f ` A. inv_into A f y \<in> V}"
            using hy hinvA_V by (by100 blast)
        qed
      qed
      show "{y \<in> f ` A. inv_into A f y \<in> V} \<in>
          subspace_topology Y TY (f ` A)"
        unfolding hpre_eq subspace_topology_def using hpreY by (by100 blast)
    qed
  qed
  show ?thesis
    unfolding top1_homeomorphism_on_def
    using htopA htopImg hbijA hcont_A hcont_inv_A by (by100 blast)
qed

lemma R2_to_pair_image_geotop_std_sphere_prefix:
  "R2_to_pair ` (geotop_std_sphere::(real^2) set) = top1_S1"
proof
  show "R2_to_pair ` (geotop_std_sphere::(real^2) set) \<subseteq> top1_S1"
  proof
    fix p
    assume hp: "p \<in> R2_to_pair ` (geotop_std_sphere::(real^2) set)"
    then obtain v :: "real^2" where hv: "v \<in> geotop_std_sphere"
      and hpv: "p = R2_to_pair v"
      by (by100 blast)
    show "p \<in> top1_S1"
      using hv hpv
      unfolding geotop_std_sphere_def R2_to_pair_def top1_S1_def
      unfolding norm_eq_sqrt_inner inner_vec_def sum_2 power2_eq_square
      by (by100 auto)
  qed
  show "top1_S1 \<subseteq> R2_to_pair ` (geotop_std_sphere::(real^2) set)"
  proof
    fix p :: "real \<times> real"
    assume hp: "p \<in> top1_S1"
    have hpair: "pair_to_R2 p \<in> (geotop_std_sphere::(real^2) set)"
      using hp
      unfolding geotop_std_sphere_def pair_to_R2_def top1_S1_def
      unfolding norm_eq_sqrt_inner inner_vec_def sum_2 power2_eq_square
      by (by100 auto)
    have hp_eq: "R2_to_pair (pair_to_R2 p) = p"
      by (rule R2_to_pair_pair_to_R2)
    show "p \<in> R2_to_pair ` (geotop_std_sphere::(real^2) set)"
    proof -
      have "R2_to_pair (pair_to_R2 p) \<in> R2_to_pair ` (geotop_std_sphere::(real^2) set)"
        by (rule imageI[OF hpair])
      thus ?thesis using hp_eq by (by100 simp)
    qed
  qed
qed

lemma R2_pair_top1_homeomorphism_std_sphere_prefix:
  "top1_homeomorphism_on (geotop_std_sphere::(real^2) set)
     (subspace_topology UNIV geotop_euclidean_topology
       (geotop_std_sphere::(real^2) set))
     top1_S1 top1_S1_topology R2_to_pair"
proof -
  have hraw: "top1_homeomorphism_on (geotop_std_sphere::(real^2) set)
      (subspace_topology UNIV geotop_euclidean_topology
        (geotop_std_sphere::(real^2) set))
      (R2_to_pair ` (geotop_std_sphere::(real^2) set))
      (subspace_topology (UNIV::(real \<times> real) set)
        (product_topology_on top1_open_sets top1_open_sets)
        (R2_to_pair ` (geotop_std_sphere::(real^2) set)))
      R2_to_pair"
    by (rule top1_homeomorphism_on_subspace_image_prefix
        [OF R2_pair_top1_homeomorphism_UNIV subset_UNIV])
  have himg: "R2_to_pair ` (geotop_std_sphere::(real^2) set) = top1_S1"
    by (rule R2_to_pair_image_geotop_std_sphere_prefix)
  have htop: "subspace_topology (UNIV::(real \<times> real) set)
        (product_topology_on top1_open_sets top1_open_sets) top1_S1 =
      top1_S1_topology"
    unfolding top1_S1_topology_def by (by100 simp)
  show ?thesis
    using hraw unfolding himg htop .
qed

lemma geotop_polygon_top1_simple_closed_curve_prefix:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "top1_simple_closed_curve_on UNIV geotop_euclidean_topology J"
  (**
    A GeoTop polygon is a topological 1-sphere in the Euclidean plane, hence a
    simple closed curve in the sense used by the Jordan-curve infrastructure. **)
proof -
  let ?S = "(geotop_std_sphere::(real^2) set)"
  let ?TS = "subspace_topology UNIV geotop_euclidean_topology ?S"
  let ?TJ = "subspace_topology UNIV geotop_euclidean_topology J"
  have hJsphere: "geotop_is_n_sphere J ?TJ 1"
    using hJ unfolding geotop_is_polygon_def by (by100 blast)
  obtain f where hJ_std: "top1_homeomorphism_on J ?TJ ?S ?TS f"
    using hJsphere unfolding geotop_is_n_sphere_def by (by100 blast)
  have hstd_J: "top1_homeomorphism_on ?S ?TS J ?TJ (inv_into J f)"
    by (rule top1_homeomorphism_on_sym[OF hJ_std])
  have hs1_std: "top1_homeomorphism_on top1_S1 top1_S1_topology ?S ?TS
      (inv_into ?S R2_to_pair)"
    by (rule top1_homeomorphism_on_sym[OF R2_pair_top1_homeomorphism_std_sphere_prefix])
  have hs1_J: "top1_homeomorphism_on top1_S1 top1_S1_topology J ?TJ
      (inv_into J f \<circ> inv_into ?S R2_to_pair)"
    by (rule top1_homeomorphism_on_comp[OF hs1_std hstd_J])
  have hcont_J: "top1_continuous_map_on top1_S1 top1_S1_topology J ?TJ
      (inv_into J f \<circ> inv_into ?S R2_to_pair)"
    using hs1_J unfolding top1_homeomorphism_on_def by (by100 blast)
  have hcont_UNIV_sub: "top1_continuous_map_on top1_S1 top1_S1_topology
      (UNIV::(real^2) set)
      (subspace_topology (UNIV::(real^2) set) geotop_euclidean_topology UNIV)
      (inv_into J f \<circ> inv_into ?S R2_to_pair)"
    by (rule top1_continuous_map_on_codomain_enlarge[OF hcont_J subset_UNIV subset_UNIV])
  have hcont_UNIV: "top1_continuous_map_on top1_S1 top1_S1_topology
      (UNIV::(real^2) set) geotop_euclidean_topology
      (inv_into J f \<circ> inv_into ?S R2_to_pair)"
    using hcont_UNIV_sub unfolding subspace_topology_UNIV_UNIV .
  have hinj: "inj_on (inv_into J f \<circ> inv_into ?S R2_to_pair) top1_S1"
    using hs1_J unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  have himg: "(inv_into J f \<circ> inv_into ?S R2_to_pair) ` top1_S1 = J"
    using hs1_J unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  show ?thesis
    unfolding top1_simple_closed_curve_on_def
    using hcont_UNIV hinj himg by (by100 blast)
qed

lemma geotop_polygon_two_point_topological_arc_split_prefix:
  fixes J :: "(real^2) set" and P Q :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hP: "P \<in> J"
  assumes hQ: "Q \<in> J"
  assumes hPQ: "P \<noteq> Q"
  shows "\<exists>C\<^sub>1 C\<^sub>2.
      J = C\<^sub>1 \<union> C\<^sub>2
      \<and> C\<^sub>1 \<inter> C\<^sub>2 = {P, Q}
      \<and> top1_is_arc_on C\<^sub>1
          (subspace_topology UNIV geotop_euclidean_topology C\<^sub>1)
      \<and> top1_is_arc_on C\<^sub>2
          (subspace_topology UNIV geotop_euclidean_topology C\<^sub>2)"
  (**
    Moise Figure 3.2 boundary cut, topological part.  A polygon is a simple
    closed curve; two distinct boundary points divide it into two arcs.  The
    remaining finite-PL step in the graph version is to recognize these arcs
    as broken lines in the finite 1-complex carrier. **)
proof -
  have hSCC:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology J"
    by (rule geotop_polygon_top1_simple_closed_curve_prefix[OF hJ])
  show ?thesis
    by (rule SCC_decompose_at_given_points
        [OF geotop_euclidean_topology_UNIV_strict
            geotop_euclidean_topology_UNIV_hausdorff hSCC hP hQ hPQ])
qed

lemma geotop_polygon_finite_linear_graph_two_vertex_topological_split_prefix:
  fixes L :: "(real^2) set set" and P Q :: "real^2"
  assumes hL_polygon: "geotop_is_polygon (geotop_polyhedron L)"
  assumes hPL: "{P} \<in> L"
  assumes hQL: "{Q} \<in> L"
  assumes hPQ: "P \<noteq> Q"
  shows "\<exists>C\<^sub>1 C\<^sub>2.
      geotop_polyhedron L = C\<^sub>1 \<union> C\<^sub>2
      \<and> C\<^sub>1 \<inter> C\<^sub>2 = {P, Q}
      \<and> top1_is_arc_on C\<^sub>1
          (subspace_topology UNIV geotop_euclidean_topology C\<^sub>1)
      \<and> top1_is_arc_on C\<^sub>2
          (subspace_topology UNIV geotop_euclidean_topology C\<^sub>2)"
  (**
    Figure 3.2 boundary cut specialized to a finite graph carrier.  This
    separates the SCC/topological content from the later finite linear graph
    refinement that upgrades the two arcs to broken lines. **)
proof -
  have hP_poly: "P \<in> geotop_polyhedron L"
    using hPL unfolding geotop_polyhedron_def by (by100 blast)
  have hQ_poly: "Q \<in> geotop_polyhedron L"
    using hQL unfolding geotop_polyhedron_def by (by100 blast)
  show ?thesis
    by (rule geotop_polygon_two_point_topological_arc_split_prefix
        [OF hL_polygon hP_poly hQ_poly hPQ])
qed

lemma geotop_polygon_two_point_topological_arc_split_endpoints_prefix:
  fixes J :: "(real^2) set" and P Q :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hP: "P \<in> J"
  assumes hQ: "Q \<in> J"
  assumes hPQ: "P \<noteq> Q"
  shows "\<exists>C\<^sub>1 C\<^sub>2.
      J = C\<^sub>1 \<union> C\<^sub>2
      \<and> C\<^sub>1 \<inter> C\<^sub>2 = {P, Q}
      \<and> top1_is_arc_on C\<^sub>1
          (subspace_topology UNIV geotop_euclidean_topology C\<^sub>1)
      \<and> top1_is_arc_on C\<^sub>2
          (subspace_topology UNIV geotop_euclidean_topology C\<^sub>2)
      \<and> top1_arc_endpoints_on C\<^sub>1
          (subspace_topology UNIV geotop_euclidean_topology C\<^sub>1) = {P, Q}
      \<and> top1_arc_endpoints_on C\<^sub>2
          (subspace_topology UNIV geotop_euclidean_topology C\<^sub>2) = {P, Q}"
  (**
    Endpoint-refined form of the Figure 3.2 topological boundary cut.  The
    SCC decomposition gives two arcs; the SCC endpoint lemma identifies their
    endpoint sets as exactly the two cut vertices. **)
proof -
  obtain C\<^sub>1 C\<^sub>2 where hsplit:
      "J = C\<^sub>1 \<union> C\<^sub>2"
      and hinter: "C\<^sub>1 \<inter> C\<^sub>2 = {P, Q}"
      and hC\<^sub>1_arc: "top1_is_arc_on C\<^sub>1
          (subspace_topology UNIV geotop_euclidean_topology C\<^sub>1)"
      and hC\<^sub>2_arc: "top1_is_arc_on C\<^sub>2
          (subspace_topology UNIV geotop_euclidean_topology C\<^sub>2)"
    using geotop_polygon_two_point_topological_arc_split_prefix
      [OF hJ hP hQ hPQ]
    by (by100 blast)
  have hSCC:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology J"
    by (rule geotop_polygon_top1_simple_closed_curve_prefix[OF hJ])
  have hC\<^sub>1_sub: "C\<^sub>1 \<subseteq> UNIV"
    by (by100 blast)
  have hC\<^sub>2_sub: "C\<^sub>2 \<subseteq> UNIV"
    by (by100 blast)
  have hC\<^sub>1_end:
      "top1_arc_endpoints_on C\<^sub>1
        (subspace_topology UNIV geotop_euclidean_topology C\<^sub>1) = {P, Q}"
    by (rule scc_decomp_arc_endpoints(1)
        [OF geotop_euclidean_topology_UNIV_strict
            geotop_euclidean_topology_UNIV_hausdorff hSCC
            hC\<^sub>1_arc hC\<^sub>2_arc hC\<^sub>1_sub hC\<^sub>2_sub hsplit hinter hPQ])
  have hC\<^sub>2_end:
      "top1_arc_endpoints_on C\<^sub>2
        (subspace_topology UNIV geotop_euclidean_topology C\<^sub>2) = {P, Q}"
    by (rule scc_decomp_arc_endpoints(2)
        [OF geotop_euclidean_topology_UNIV_strict
            geotop_euclidean_topology_UNIV_hausdorff hSCC
            hC\<^sub>1_arc hC\<^sub>2_arc hC\<^sub>1_sub hC\<^sub>2_sub hsplit hinter hPQ])
  show ?thesis
    using hsplit hinter hC\<^sub>1_arc hC\<^sub>2_arc hC\<^sub>1_end hC\<^sub>2_end by (by100 blast)
qed

lemma geotop_top1_arc_on_imp_geotop_is_arc_prefix:
  fixes A :: "(real^2) set"
  assumes hA: "top1_is_arc_on A
      (subspace_topology UNIV geotop_euclidean_topology A)"
  shows "geotop_is_arc A
      (subspace_topology UNIV geotop_euclidean_topology A)"
  (**
    Bridge for the Figure 3.2 boundary cut: the SCC decomposition produces
    \<open>top1_is_arc_on\<close> pieces, while the Moise/geotop broken-line interface is
    phrased with \<open>geotop_is_arc\<close>.  Compose the inverse interval
    parametrisation of \<open>A\<close> with a standard nondegenerate segment simplex. **)
proof -
  obtain h where hIA: "top1_homeomorphism_on I_set I_top A
      (subspace_topology UNIV geotop_euclidean_topology A) h"
    using hA unfolding top1_is_arc_on_def by (by100 blast)
  have hAI: "top1_homeomorphism_on A
      (subspace_topology UNIV geotop_euclidean_topology A)
      I_set I_top (inv_into I_set h)"
    by (rule top1_homeomorphism_on_sym[OF hIA])
  obtain b :: "real^2" where hb_basis: "b \<in> Basis"
    using nonempty_Basis by (by100 blast)
  have hb_ne: "(0::real^2) \<noteq> b"
    using hb_basis nonzero_Basis by (by100 blast)
  let ?S = "closed_segment (0::real^2) b"
  have hS_simplex: "geotop_simplex_dim ?S 1"
    by (rule geotop_closed_segment_is_simplex[OF hb_ne])
  have hS_end: "geotop_arc_endpoints ?S {0, b}"
    by (rule geotop_closed_segment_arc_endpoints_prefix[OF hb_ne])
  obtain g where hIS_raw:
      "top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
        (subspace_topology UNIV geotop_euclidean_topology
          {t::real. 0 \<le> t \<and> t \<le> 1})
        ?S (subspace_topology UNIV geotop_euclidean_topology ?S) g"
    using hS_end unfolding geotop_arc_endpoints_def by (by100 blast)
  have hI_set: "{t::real. 0 \<le> t \<and> t \<le> 1} = I_set"
    unfolding top1_unit_interval_def by (by100 auto)
  have hI_top:
      "subspace_topology (UNIV::real set) geotop_euclidean_topology
        {t::real. 0 \<le> t \<and> t \<le> 1} = I_top"
    unfolding top1_unit_interval_topology_def
    using hI_set by (simp add: geotop_euclidean_topology_eq_open_sets)
  have hIS: "top1_homeomorphism_on I_set I_top ?S
      (subspace_topology UNIV geotop_euclidean_topology ?S) g"
    using hIS_raw hI_set hI_top by (by100 simp)
  have hAS: "top1_homeomorphism_on A
      (subspace_topology UNIV geotop_euclidean_topology A)
      ?S (subspace_topology UNIV geotop_euclidean_topology ?S)
      (g \<circ> inv_into I_set h)"
    by (rule top1_homeomorphism_on_comp[OF hAI hIS])
  show ?thesis
    unfolding geotop_is_arc_def geotop_is_n_cell_def
    using hS_simplex hAS unfolding top1_homeomorphism_on_def by (by100 blast)
qed

lemma geotop_is_arc_has_arc_endpoints_prefix:
  fixes A :: "(real^2) set"
  assumes hA: "geotop_is_arc A
      (subspace_topology UNIV geotop_euclidean_topology A)"
  shows "\<exists>E. geotop_arc_endpoints A E"
proof -
  obtain \<gamma> :: "real \<Rightarrow> real^2" where h\<gamma>_arc: "arc \<gamma>" and h\<gamma>_pim: "path_image \<gamma> = A"
    using geotop_is_arc_imp_HOL_arc[OF hA] by (by100 blast)
  obtain h where hhomeo_HOL: "homeomorphism {0..1} (path_image \<gamma>) \<gamma> h"
    using geotop_arc_homeomorphism_image[OF h\<gamma>_arc] by (by100 blast)
  have hhomeo_top1_iv: "top1_homeomorphism_on {0..1}
              (subspace_topology UNIV geotop_euclidean_topology {0..1})
              (path_image \<gamma>) (subspace_topology UNIV geotop_euclidean_topology (path_image \<gamma>)) \<gamma>"
    by (rule geotop_HOL_homeomorphism_imp_top1_homeomorphism_on_cross_prefix[OF hhomeo_HOL])
  have hunit: "{t::real. 0 \<le> t \<and> t \<le> 1} = {0..1}"
    by (by100 auto)
  have hhomeo_top1_A: "top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
              (subspace_topology UNIV geotop_euclidean_topology {t::real. 0 \<le> t \<and> t \<le> 1})
              A (subspace_topology UNIV geotop_euclidean_topology A) \<gamma>"
    using hhomeo_top1_iv hunit h\<gamma>_pim by (by100 simp)
  have h\<gamma>_inj: "inj_on \<gamma> {0..1}"
    using h\<gamma>_arc unfolding arc_def by (by100 blast)
  have h\<gamma>0_ne_\<gamma>1: "\<gamma> 0 \<noteq> \<gamma> 1"
    using h\<gamma>_inj unfolding inj_on_def by (by100 force)
  have hcard: "card {\<gamma> 0, \<gamma> 1} = 2"
    using h\<gamma>0_ne_\<gamma>1 by (by100 simp)
  have hsub: "{\<gamma> 0, \<gamma> 1} \<subseteq> A"
    using h\<gamma>_pim unfolding path_image_def by (by100 force)
  show ?thesis
    unfolding geotop_arc_endpoints_def
    using hA hcard hsub hhomeo_top1_A by (by100 blast)
qed

lemma geotop_broken_line_has_arc_endpoints_prefix:
  fixes B :: "(real^2) set"
  assumes hB: "geotop_is_broken_line B"
  shows "\<exists>E. geotop_arc_endpoints B E"
proof -
  have hB_arc: "geotop_is_arc B
      (subspace_topology UNIV geotop_euclidean_topology B)"
    using hB unfolding geotop_is_broken_line_def by (by100 blast)
  show ?thesis
    by (rule geotop_is_arc_has_arc_endpoints_prefix[OF hB_arc])
qed

lemma geotop_top1_arc_endpoints_imp_geotop_arc_endpoints_prefix:
  fixes A :: "(real^2) set" and P Q :: "real^2"
  assumes hA: "top1_is_arc_on A
      (subspace_topology UNIV geotop_euclidean_topology A)"
  assumes hEnd: "top1_arc_endpoints_on A
      (subspace_topology UNIV geotop_euclidean_topology A) = {P, Q}"
  assumes hPQ: "P \<noteq> Q"
  shows "geotop_arc_endpoints A {P, Q}"
proof -
  obtain h where hIA: "top1_homeomorphism_on I_set I_top A
      (subspace_topology UNIV geotop_euclidean_topology A) h"
    using hA unfolding top1_is_arc_on_def by (by100 blast)
  have hboundary: "top1_arc_endpoints_on A
      (subspace_topology UNIV geotop_euclidean_topology A) = {h 0, h 1}"
    by (rule arc_endpoints_are_boundary[
        OF geotop_euclidean_topology_UNIV_strict
           geotop_euclidean_topology_UNIV_hausdorff subset_UNIV hA hIA])
  have hEPQ: "{P, Q} = {h 0, h 1}"
    using hEnd hboundary by (by100 simp)
  have hgeotop: "geotop_is_arc A
      (subspace_topology UNIV geotop_euclidean_topology A)"
    by (rule geotop_top1_arc_on_imp_geotop_is_arc_prefix[OF hA])
  have hcard: "card {P, Q} = 2"
    using hPQ by (by100 simp)
  have hsub: "{P, Q} \<subseteq> A"
    using hEnd unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hI_set: "{t::real. 0 \<le> t \<and> t \<le> 1} = I_set"
    unfolding top1_unit_interval_def by (by100 auto)
  have hI_top:
      "subspace_topology (UNIV::real set) geotop_euclidean_topology
        {t::real. 0 \<le> t \<and> t \<le> 1} = I_top"
    unfolding top1_unit_interval_topology_def
    using hI_set by (simp add: geotop_euclidean_topology_eq_open_sets)
  have hIA_raw:
      "top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
        (subspace_topology UNIV geotop_euclidean_topology
          {t::real. 0 \<le> t \<and> t \<le> 1})
        A (subspace_topology UNIV geotop_euclidean_topology A) h"
    using hIA hI_set hI_top by (by100 simp)
  show ?thesis
    unfolding geotop_arc_endpoints_def
    using hgeotop hcard hsub hIA_raw hEPQ by (by100 blast)
qed

lemma geotop_polygon_two_point_geotop_arc_split_endpoints_prefix:
  fixes J :: "(real^2) set" and P Q :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hP: "P \<in> J"
  assumes hQ: "Q \<in> J"
  assumes hPQ: "P \<noteq> Q"
  shows "\<exists>C\<^sub>1 C\<^sub>2.
      J = C\<^sub>1 \<union> C\<^sub>2
      \<and> C\<^sub>1 \<inter> C\<^sub>2 = {P, Q}
      \<and> geotop_arc_endpoints C\<^sub>1 {P, Q}
      \<and> geotop_arc_endpoints C\<^sub>2 {P, Q}"
proof -
  obtain C\<^sub>1 C\<^sub>2 where hsplit:
      "J = C\<^sub>1 \<union> C\<^sub>2"
      and hinter: "C\<^sub>1 \<inter> C\<^sub>2 = {P, Q}"
      and hC\<^sub>1_arc: "top1_is_arc_on C\<^sub>1
          (subspace_topology UNIV geotop_euclidean_topology C\<^sub>1)"
      and hC\<^sub>2_arc: "top1_is_arc_on C\<^sub>2
          (subspace_topology UNIV geotop_euclidean_topology C\<^sub>2)"
      and hC\<^sub>1_end: "top1_arc_endpoints_on C\<^sub>1
          (subspace_topology UNIV geotop_euclidean_topology C\<^sub>1) = {P, Q}"
      and hC\<^sub>2_end: "top1_arc_endpoints_on C\<^sub>2
          (subspace_topology UNIV geotop_euclidean_topology C\<^sub>2) = {P, Q}"
    using geotop_polygon_two_point_topological_arc_split_endpoints_prefix
      [OF hJ hP hQ hPQ]
    by (by100 blast)
  have hC\<^sub>1_geotop: "geotop_arc_endpoints C\<^sub>1 {P, Q}"
    by (rule geotop_top1_arc_endpoints_imp_geotop_arc_endpoints_prefix
        [OF hC\<^sub>1_arc hC\<^sub>1_end hPQ])
  have hC\<^sub>2_geotop: "geotop_arc_endpoints C\<^sub>2 {P, Q}"
    by (rule geotop_top1_arc_endpoints_imp_geotop_arc_endpoints_prefix
        [OF hC\<^sub>2_arc hC\<^sub>2_end hPQ])
  show ?thesis
    using hsplit hinter hC\<^sub>1_geotop hC\<^sub>2_geotop by (by100 blast)
qed

lemma geotop_polygon_two_point_geotop_arc_split_interior_disjoint_prefix:
  fixes J :: "(real^2) set" and P Q :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hP: "P \<in> J"
  assumes hQ: "Q \<in> J"
  assumes hPQ: "P \<noteq> Q"
  shows "\<exists>C\<^sub>1 C\<^sub>2.
      J = C\<^sub>1 \<union> C\<^sub>2
      \<and> C\<^sub>1 \<inter> C\<^sub>2 = {P, Q}
      \<and> geotop_arc_endpoints C\<^sub>1 {P, Q}
      \<and> geotop_arc_endpoints C\<^sub>2 {P, Q}
      \<and> geotop_arc_interior C\<^sub>1 {P, Q} \<inter>
          geotop_arc_interior C\<^sub>2 {P, Q} = {}"
proof -
  obtain C\<^sub>1 C\<^sub>2 where hsplit: "J = C\<^sub>1 \<union> C\<^sub>2"
      and hinter: "C\<^sub>1 \<inter> C\<^sub>2 = {P, Q}"
      and hC\<^sub>1E: "geotop_arc_endpoints C\<^sub>1 {P, Q}"
      and hC\<^sub>2E: "geotop_arc_endpoints C\<^sub>2 {P, Q}"
    using geotop_polygon_two_point_geotop_arc_split_endpoints_prefix
      [OF hJ hP hQ hPQ]
    by (by100 blast)
  have hinters_empty:
      "geotop_arc_interior C\<^sub>1 {P, Q} \<inter>
        geotop_arc_interior C\<^sub>2 {P, Q} = {}"
    using hinter unfolding geotop_arc_interior_def by (by100 blast)
  show ?thesis
    using hsplit hinter hC\<^sub>1E hC\<^sub>2E hinters_empty by (by100 blast)
qed

lemma geotop_polygon_finite_linear_graph_two_vertex_geotop_arc_split_interior_disjoint_prefix:
  fixes L :: "(real^2) set set" and P Q :: "real^2"
  assumes hL_polygon: "geotop_is_polygon (geotop_polyhedron L)"
  assumes hPL: "{P} \<in> L"
  assumes hQL: "{Q} \<in> L"
  assumes hPQ: "P \<noteq> Q"
  shows "\<exists>C\<^sub>1 C\<^sub>2.
      geotop_polyhedron L = C\<^sub>1 \<union> C\<^sub>2
      \<and> C\<^sub>1 \<inter> C\<^sub>2 = {P, Q}
      \<and> geotop_arc_endpoints C\<^sub>1 {P, Q}
      \<and> geotop_arc_endpoints C\<^sub>2 {P, Q}
      \<and> geotop_arc_interior C\<^sub>1 {P, Q} \<inter>
          geotop_arc_interior C\<^sub>2 {P, Q} = {}"
proof -
  have hP_poly: "P \<in> geotop_polyhedron L"
    using hPL unfolding geotop_polyhedron_def by (by100 blast)
  have hQ_poly: "Q \<in> geotop_polyhedron L"
    using hQL unfolding geotop_polyhedron_def by (by100 blast)
  show ?thesis
    by (rule geotop_polygon_two_point_geotop_arc_split_interior_disjoint_prefix
        [OF hL_polygon hP_poly hQ_poly hPQ])
qed

lemma geotop_1dim_complex_carrier_top1_arc_imp_broken_line_prefix:
  fixes K :: "(real^2) set set" and A :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hK1: "geotop_complex_is_1dim K"
  assumes hpoly: "geotop_polyhedron K = A"
  assumes hA: "top1_is_arc_on A
      (subspace_topology UNIV geotop_euclidean_topology A)"
  shows "geotop_is_broken_line A"
proof -
  have hA_geo: "geotop_is_arc A
      (subspace_topology UNIV geotop_euclidean_topology A)"
    by (rule geotop_top1_arc_on_imp_geotop_is_arc_prefix[OF hA])
  show ?thesis
    unfolding geotop_is_broken_line_def
    using hK hK1 hpoly hA_geo by (by100 blast)
qed

lemma geotop_1dim_complex_carrier_geotop_arc_imp_broken_line_prefix:
  fixes K :: "(real^2) set set" and A :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hK1: "geotop_complex_is_1dim K"
  assumes hpoly: "geotop_polyhedron K = A"
  assumes hA: "geotop_is_arc A
      (subspace_topology UNIV geotop_euclidean_topology A)"
  shows "geotop_is_broken_line A"
  unfolding geotop_is_broken_line_def
  using hK hK1 hpoly hA by (by100 blast)

lemma geotop_linear_graph_complex_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  shows "geotop_is_complex L"
  using hL unfolding geotop_is_linear_graph_def by (by100 blast)

lemma geotop_linear_graph_1dim_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  shows "geotop_complex_is_1dim L"
proof -
  have hdim: "\<forall>\<sigma>\<in>L. \<exists>i\<le>1. geotop_simplex_dim \<sigma> i"
    using hL unfolding geotop_is_linear_graph_def by (by100 blast)
  show ?thesis
    unfolding geotop_complex_is_1dim_def using hdim by (by100 blast)
qed

definition geotop_graph_endpoint ::
  "'a::real_normed_vector set set \<Rightarrow> 'a \<Rightarrow> bool" where
  "geotop_graph_endpoint K v \<longleftrightarrow>
    v \<in> geotop_complex_vertices K \<and>
    card {e\<in>K. geotop_is_edge e \<and> v \<in> e} = 1"

lemma geotop_graph_endpoint_singleton_and_card_one_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hend: "geotop_graph_endpoint L w"
  shows "{w} \<in> L \<and> card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have hw_vertex: "w \<in> geotop_complex_vertices L"
    using hend unfolding geotop_graph_endpoint_def by (by100 blast)
  have hwL: "{w} \<in> L"
    using geotop_complex_vertices_eq_0_simplexes[OF hcomplex] hw_vertex
    by (by100 blast)
  have hcard: "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1"
    using hend unfolding geotop_graph_endpoint_def by (by100 blast)
  show ?thesis
    using hwL hcard by (by100 blast)
qed

lemma geotop_broken_line_endpoint_in_finite_linear_graph_vertex_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hpoly: "geotop_polyhedron L = B"
  assumes hB: "geotop_is_broken_line B"
  assumes hE: "geotop_arc_endpoints B E"
  assumes hP: "P \<in> E"
  shows "{P} \<in> L"
proof -
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have hL_1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_prefix[OF hL])
  have hP_B: "P \<in> B"
    using hE hP unfolding geotop_arc_endpoints_def by (by100 blast)
  obtain \<gamma> :: "real \<Rightarrow> real^2"
    where h\<gamma>_arc: "arc \<gamma>"
      and h\<gamma>_pim: "path_image \<gamma> = B"
      and hE_eq: "E = {pathstart \<gamma>, pathfinish \<gamma>}"
    using arc_endpoints_imp_arc_HOL[OF hE] by (by100 blast)
  have hP_endpoint_param: "\<gamma> 0 = P \<or> \<gamma> 1 = P"
    using hP hE_eq unfolding pathstart_def pathfinish_def by (by100 blast)
  have hpoly_path: "geotop_polyhedron L = path_image \<gamma>"
    using hpoly h\<gamma>_pim by (by100 simp)
  have hP_poly: "P \<in> geotop_polyhedron L"
    using hP_B hpoly by (by100 simp)
  obtain \<sigma> where h\<sigma>L: "\<sigma> \<in> L" and hP\<sigma>: "P \<in> \<sigma>"
    using hP_poly unfolding geotop_polyhedron_def by (by100 blast)
  have hcases: "(\<exists>v. \<sigma> = {v}) \<or> (\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b)"
    by (rule geotop_1dim_simplex_cases[OF hL_1dim h\<sigma>L])
  show ?thesis
  proof (rule disjE[OF hcases])
    assume "\<exists>v. \<sigma> = {v}"
    then obtain v where h\<sigma>v: "\<sigma> = {v}" by (by100 blast)
    have hPv: "P = v" using hP\<sigma> h\<sigma>v by (by100 blast)
    show "{P} \<in> L" using h\<sigma>L h\<sigma>v hPv by (by100 simp)
  next
    assume "\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b"
    then obtain a b where hab: "a \<noteq> b" and h\<sigma>ab: "\<sigma> = closed_segment a b"
      by (by100 blast)
    have hP_ab: "P = a \<or> P = b"
    proof (rule ccontr)
      assume hnot: "\<not> (P = a \<or> P = b)"
      have hP_ne_a: "P \<noteq> a" and hP_ne_b: "P \<noteq> b"
        using hnot by (by100 blast)+
      obtain s t where hst_le: "s \<le> t"
          and hs_01: "s \<in> {0..1}"
          and ht_01: "t \<in> {0..1}"
          and hpre: "{r\<in>{0..1}. \<gamma> r \<in> \<sigma>} = {s..t}"
          and hends: "{\<gamma> s, \<gamma> t} = {a, b}"
        using geotop_arc_1simplex_preimage_structure
          [OF h\<gamma>_arc hL_1dim hpoly_path h\<sigma>L h\<sigma>ab hab]
        by (by100 blast)
      show False
      proof (rule disjE[OF hP_endpoint_param])
        assume h0P: "\<gamma> 0 = P"
        have h0_pre: "0 \<in> {r\<in>{0..1}. \<gamma> r \<in> \<sigma>}"
          using h0P hP\<sigma> by (by100 simp)
        have h0_iv: "0 \<in> {s..t}"
          using h0_pre hpre by (by100 simp)
        have hs0: "s = 0"
          using h0_iv hs_01 by (by100 simp)
        have "P \<in> {a, b}"
          using hends hs0 h0P by (by100 blast)
        thus False using hP_ne_a hP_ne_b by (by100 blast)
      next
        assume h1P: "\<gamma> 1 = P"
        have h1_pre: "1 \<in> {r\<in>{0..1}. \<gamma> r \<in> \<sigma>}"
          using h1P hP\<sigma> by (by100 simp)
        have h1_iv: "1 \<in> {s..t}"
          using h1_pre hpre by (by100 simp)
        have ht1: "t = 1"
          using h1_iv ht_01 by (by100 simp)
        have "P \<in> {a, b}"
          using hends ht1 h1P by (by100 blast)
        thus False using hP_ne_a hP_ne_b by (by100 blast)
      qed
    qed
    have hface_closed: "\<forall>\<rho>\<in>L. \<forall>\<tau>. geotop_is_face \<tau> \<rho> \<longrightarrow> \<tau> \<in> L"
      by (rule geotop_is_complex_face_closed[OF hL_complex])
    show "{P} \<in> L"
    proof (rule disjE[OF hP_ab])
      assume hPa: "P = a"
      have hface: "geotop_is_face {P} \<sigma>"
        using geotop_closed_segment_is_face_endpoint[OF hab, of P] hPa h\<sigma>ab by (by100 simp)
      show ?thesis using hface_closed h\<sigma>L hface by (by100 blast)
    next
      assume hPb: "P = b"
      have hba: "b \<noteq> a"
        using hab by (by100 blast)
      have hface: "geotop_is_face {P} \<sigma>"
        using geotop_closed_segment_is_face_endpoint[OF hba, of P] hPb h\<sigma>ab
          closed_segment_commute[of a b]
        by (by100 simp)
      show ?thesis using hface_closed h\<sigma>L hface by (by100 blast)
    qed
  qed
qed

lemma geotop_broken_line_endpoint_vertex_incident_edge_card_one_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hpoly: "geotop_polyhedron L = B"
  assumes hB: "geotop_is_broken_line B"
  assumes hE: "geotop_arc_endpoints B E"
  assumes hP: "P \<in> E"
  assumes hPL: "{P} \<in> L"
  shows "card {e\<in>L. geotop_is_edge e \<and> P \<in> e} = 1"
proof -
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have hL_1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_prefix[OF hL])
  have hP_B: "P \<in> B"
    using hE hP unfolding geotop_arc_endpoints_def by (by100 blast)
  obtain \<gamma> :: "real \<Rightarrow> real^2"
    where h\<gamma>_arc: "arc \<gamma>"
      and h\<gamma>_pim: "path_image \<gamma> = B"
      and hE_eq: "E = {pathstart \<gamma>, pathfinish \<gamma>}"
    using arc_endpoints_imp_arc_HOL[OF hE] by (by100 blast)
  have hP_endpoint_param: "\<gamma> 0 = P \<or> \<gamma> 1 = P"
    using hP hE_eq unfolding pathstart_def pathfinish_def by (by100 blast)
  define EdgesAtP where
    "EdgesAtP = {\<sigma>\<in>L. P \<in> \<sigma> \<and> geotop_simplex_dim \<sigma> 1}"
  have hEdges_fin: "finite EdgesAtP"
    unfolding EdgesAtP_def using hfin by (by100 simp)
  have hL_local_isolation:
    "\<exists>\<delta>>0. ball P \<delta> \<inter> B \<subseteq> \<Union>{\<tau>\<in>L. P \<in> \<tau>}"
  proof -
    have hL_simp_all: "\<forall>\<tau>\<in>L. geotop_is_simplex \<tau>"
      by (rule geotop_is_complex_simplex[OF hL_complex])
    have hL_closed_all: "\<forall>\<tau>\<in>L. closed \<tau>"
    proof
      fix \<tau> assume h\<tau>L: "\<tau> \<in> L"
      have hsim: "geotop_is_simplex \<tau>"
        by (rule bspec[OF hL_simp_all h\<tau>L])
      obtain V m n where hVfin: "finite V" and h\<tau>_hull: "\<tau> = geotop_convex_hull V"
        using hsim unfolding geotop_is_simplex_def by (by100 blast)
      have h\<tau>_HOL: "\<tau> = convex hull V"
        using h\<tau>_hull geotop_convex_hull_eq_HOL by (by100 simp)
      have h_compact: "compact (convex hull V)"
        using hVfin finite_imp_compact_convex_hull by (by100 blast)
      show "closed \<tau>"
        using h\<tau>_HOL compact_imp_closed[OF h_compact] by (by100 simp)
    qed
    have hB_union: "B = \<Union>L"
      using hpoly unfolding geotop_polyhedron_def by (by100 simp)
    show ?thesis
      using finite_union_closed_local_isolation[OF hfin hL_closed_all hB_union hP_B]
      by (by100 blast)
  qed
  have hEdges_nonempty: "EdgesAtP \<noteq> {}"
  proof
    assume hEdges_empty: "EdgesAtP = {}"
    obtain \<delta> where h\<delta>_pos: "\<delta> > 0"
        and h\<delta>_iso: "ball P \<delta> \<inter> B \<subseteq> \<Union>{\<tau>\<in>L. P \<in> \<tau>}"
      using hL_local_isolation by (by100 blast)
    have h_ball_only_P: "ball P \<delta> \<inter> B \<subseteq> {P}"
    proof
      fix x assume hx: "x \<in> ball P \<delta> \<inter> B"
      obtain \<tau> where h\<tau>L: "\<tau> \<in> L" and hP\<tau>: "P \<in> \<tau>" and hx\<tau>: "x \<in> \<tau>"
        using h\<delta>_iso hx by (by100 blast)
      have hdim: "\<exists>n\<le>1. geotop_simplex_dim \<tau> n"
        using hL_1dim h\<tau>L unfolding geotop_complex_is_1dim_def by (by100 blast)
      obtain n where hn_le: "n \<le> 1" and h\<tau>dim: "geotop_simplex_dim \<tau> n"
        using hdim by (by100 blast)
      have hcases: "n = 0 \<or> n = 1" using hn_le by (by100 linarith)
      show "x \<in> {P}"
      proof (rule disjE[OF hcases])
        assume hn0: "n = 0"
        have h\<tau>dim0: "geotop_simplex_dim \<tau> 0" using h\<tau>dim hn0 by (by100 simp)
        obtain V m where hVcard: "card V = 0 + 1" and h\<tau>_hull: "\<tau> = geotop_convex_hull V"
          using h\<tau>dim0 unfolding geotop_simplex_dim_def by (by100 blast)
        have hVcard1: "card V = 1" using hVcard by (by100 simp)
        obtain v where hV: "V = {v}"
          by (rule card_1_singletonE[OF hVcard1])
        have h\<tau>_HOL: "\<tau> = convex hull V"
          using h\<tau>_hull geotop_convex_hull_eq_HOL by (by100 simp)
        have h\<tau>_sing: "\<tau> = {v}" using h\<tau>_HOL hV by (by100 simp)
        have hP_v: "P = v" using hP\<tau> h\<tau>_sing by (by100 blast)
        have hxP: "x = P" using hx\<tau> h\<tau>_sing hP_v by (by100 blast)
        show ?thesis using hxP by (by100 simp)
      next
        assume hn1: "n = 1"
        have h\<tau>dim1: "geotop_simplex_dim \<tau> 1" using h\<tau>dim hn1 by (by100 simp)
        have "\<tau> \<in> EdgesAtP"
          unfolding EdgesAtP_def using h\<tau>L hP\<tau> h\<tau>dim1 by (by100 simp)
        hence False using hEdges_empty by (by100 simp)
        thus ?thesis by (rule FalseE)
      qed
    qed
    have hP_cl_int: "P \<in> closure (geotop_arc_interior B E)"
      using arc_closure_interior_eq_arc[OF hE] hP_B by (by100 simp)
    have h_ball_open: "open (ball P \<delta>)" by (by100 simp)
    have hP_ball: "P \<in> ball P \<delta>" using h\<delta>_pos by (by100 simp)
    have h_int_meets: "geotop_arc_interior B E \<inter> ball P \<delta> \<noteq> {}"
      using hP_cl_int closure_iff_nhds_not_empty[of P "geotop_arc_interior B E"]
            h_ball_open hP_ball
      by (by100 blast)
    obtain y where hy_int: "y \<in> geotop_arc_interior B E" and hy_ball: "y \<in> ball P \<delta>"
      using h_int_meets by (by100 blast)
    have hyB: "y \<in> B" using hy_int unfolding geotop_arc_interior_def by (by100 blast)
    have hyP: "y = P" using h_ball_only_P hy_ball hyB by (by100 blast)
    have hy_notP: "y \<noteq> P" using hy_int hP unfolding geotop_arc_interior_def by (by100 blast)
    show False using hyP hy_notP by (by100 blast)
  qed
  have hEdges_at_most_one: "\<forall>\<tau>\<in>EdgesAtP. \<forall>\<rho>\<in>EdgesAtP. \<tau> = \<rho>"
  proof (intro ballI)
    fix \<tau> \<rho>
    assume h\<tau>E: "\<tau> \<in> EdgesAtP" and h\<rho>E: "\<rho> \<in> EdgesAtP"
    have h\<tau>L: "\<tau> \<in> L" and hP\<tau>: "P \<in> \<tau>" and h\<tau>dim: "geotop_simplex_dim \<tau> 1"
      using h\<tau>E unfolding EdgesAtP_def by (by100 blast)+
    have h\<rho>L: "\<rho> \<in> L" and hP\<rho>: "P \<in> \<rho>" and h\<rho>dim: "geotop_simplex_dim \<rho> 1"
      using h\<rho>E unfolding EdgesAtP_def by (by100 blast)+
    have h_edge_segment_at_P:
      "\<And>e. \<lbrakk>e \<in> L; P \<in> e; geotop_simplex_dim e 1\<rbrakk>
        \<Longrightarrow> \<exists>q. q \<noteq> P \<and> e = closed_segment P q"
    proof -
      fix e
      assume heL: "e \<in> L" and hPe: "P \<in> e" and hedim: "geotop_simplex_dim e 1"
      have hcases: "(\<exists>v. e = {v}) \<or> (\<exists>a b. a \<noteq> b \<and> e = closed_segment a b)"
        by (rule geotop_1dim_simplex_cases[OF hL_1dim heL])
      show "\<exists>q. q \<noteq> P \<and> e = closed_segment P q"
      proof (rule disjE[OF hcases])
        assume "\<exists>v. e = {v}"
        then obtain v where hev: "e = {v}" by (by100 blast)
        have hdim0: "geotop_simplex_dim e 0"
          using hev geotop_singleton_is_simplex by (by100 simp)
        have "0 = (1::nat)" by (rule geotop_simplex_dim_unique[OF hdim0 hedim])
        hence False by simp
        thus ?thesis by (rule FalseE)
      next
        assume "\<exists>a b. a \<noteq> b \<and> e = closed_segment a b"
        then obtain a b where hab: "a \<noteq> b" and heab: "e = closed_segment a b"
          by (by100 blast)
        have hP_endpoint: "P = a \<or> P = b"
          by (rule geotop_1dim_vertex_in_1simplex_is_endpoint
              [OF hL_complex hPL heL heab hab hPe])
        show ?thesis
        proof (rule disjE[OF hP_endpoint])
          assume hPa: "P = a"
          have hb_ne: "b \<noteq> P" using hab hPa by (by100 blast)
          have hseg: "e = closed_segment P b" using heab hPa by (by100 simp)
          show ?thesis using hb_ne hseg by (by100 blast)
        next
          assume hPb: "P = b"
          have ha_ne: "a \<noteq> P" using hab hPb by (by100 blast)
          have hcomm: "closed_segment a b = closed_segment b a"
            by (rule closed_segment_commute)
          have hseg: "e = closed_segment P a" using heab hPb hcomm by (by100 simp)
          show ?thesis using ha_ne hseg by (by100 blast)
        qed
      qed
    qed
    obtain q\<tau> where hq\<tau>_ne: "q\<tau> \<noteq> P" and h\<tau>_seg: "\<tau> = closed_segment P q\<tau>"
      using h_edge_segment_at_P[OF h\<tau>L hP\<tau> h\<tau>dim] by (by100 blast)
    obtain q\<rho> where hq\<rho>_ne: "q\<rho> \<noteq> P" and h\<rho>_seg: "\<rho> = closed_segment P q\<rho>"
      using h_edge_segment_at_P[OF h\<rho>L hP\<rho> h\<rho>dim] by (by100 blast)
    have h_overlap_nonendpoint: "\<exists>z. z \<in> \<tau> \<inter> \<rho> \<and> z \<noteq> P"
    proof -
      have hL_path: "geotop_polyhedron L = path_image \<gamma>"
        using hpoly h\<gamma>_pim by (by100 simp)
      obtain s_tau t_tau where hst_tau_le: "s_tau \<le> t_tau"
          and hs_tau_01: "s_tau \<in> {0..1}"
          and ht_tau_01: "t_tau \<in> {0..1}"
          and hpre_tau: "{s\<in>{0..1}. \<gamma> s \<in> \<tau>} = {s_tau..t_tau}"
          and hends_tau: "{\<gamma> s_tau, \<gamma> t_tau} = {P, q\<tau>}"
        using geotop_arc_1simplex_preimage_structure
          [OF h\<gamma>_arc hL_1dim hL_path h\<tau>L h\<tau>_seg hq\<tau>_ne[symmetric]]
        by (by100 blast)
      obtain s_rho t_rho where hst_rho_le: "s_rho \<le> t_rho"
          and hs_rho_01: "s_rho \<in> {0..1}"
          and ht_rho_01: "t_rho \<in> {0..1}"
          and hpre_rho: "{s\<in>{0..1}. \<gamma> s \<in> \<rho>} = {s_rho..t_rho}"
          and hends_rho: "{\<gamma> s_rho, \<gamma> t_rho} = {P, q\<rho>}"
        using geotop_arc_1simplex_preimage_structure
          [OF h\<gamma>_arc hL_1dim hL_path h\<rho>L h\<rho>_seg hq\<rho>_ne[symmetric]]
        by (by100 blast)
      have h_ordered_endpoint_overlap:
        "\<exists>r\<in>{0..1}. \<gamma> r \<in> \<tau> \<and> \<gamma> r \<in> \<rho> \<and> \<gamma> r \<noteq> P"
      proof (rule disjE[OF hP_endpoint_param])
        assume h0P: "\<gamma> 0 = P"
        have hinj: "inj_on \<gamma> {0..1}"
          using h\<gamma>_arc unfolding arc_def by (by100 blast)
        have h0_pre_tau: "0 \<in> {s\<in>{0..1}. \<gamma> s \<in> \<tau>}"
          using h0P hP\<tau> by (by100 simp)
        have h0_tau_iv: "0 \<in> {s_tau..t_tau}"
          using h0_pre_tau hpre_tau by (by100 simp)
        have hs_tau_zero: "s_tau = 0"
          using h0_tau_iv hs_tau_01 by (by100 simp)
        have hq_tau_img: "\<gamma> t_tau = q\<tau>"
        proof -
          have "q\<tau> \<in> {\<gamma> s_tau, \<gamma> t_tau}"
            using hends_tau by (by100 blast)
          thus ?thesis using hs_tau_zero h0P hq\<tau>_ne by (by100 blast)
        qed
        have ht_tau_pos: "t_tau > 0"
        proof -
          have "t_tau \<noteq> 0"
          proof
            assume ht0: "t_tau = 0"
            have "\<gamma> t_tau = P" using ht0 h0P by (by100 simp)
            thus False using hq_tau_img hq\<tau>_ne by (by100 simp)
          qed
          thus ?thesis using ht_tau_01 by (by100 simp)
        qed
        have h0_pre_rho: "0 \<in> {s\<in>{0..1}. \<gamma> s \<in> \<rho>}"
          using h0P hP\<rho> by (by100 simp)
        have h0_rho_iv: "0 \<in> {s_rho..t_rho}"
          using h0_pre_rho hpre_rho by (by100 simp)
        have hs_rho_zero: "s_rho = 0"
          using h0_rho_iv hs_rho_01 by (by100 simp)
        have hq_rho_img: "\<gamma> t_rho = q\<rho>"
        proof -
          have "q\<rho> \<in> {\<gamma> s_rho, \<gamma> t_rho}"
            using hends_rho by (by100 blast)
          thus ?thesis using hs_rho_zero h0P hq\<rho>_ne by (by100 blast)
        qed
        have ht_rho_pos: "t_rho > 0"
        proof -
          have "t_rho \<noteq> 0"
          proof
            assume ht0: "t_rho = 0"
            have "\<gamma> t_rho = P" using ht0 h0P by (by100 simp)
            thus False using hq_rho_img hq\<rho>_ne by (by100 simp)
          qed
          thus ?thesis using ht_rho_01 by (by100 simp)
        qed
        define r where "r = min t_tau t_rho / 2"
        have hr_pos: "r > 0" unfolding r_def using ht_tau_pos ht_rho_pos by (by100 simp)
        have hr_le_tau: "r \<le> t_tau" unfolding r_def using ht_tau_pos by (by100 linarith)
        have hr_le_rho: "r \<le> t_rho" unfolding r_def using ht_rho_pos by (by100 linarith)
        have hr_01: "r \<in> {0..1}"
        proof -
          have ht_tau_le1: "t_tau \<le> 1" using ht_tau_01 by (by100 simp)
          have "r \<le> 1" unfolding r_def using ht_tau_le1 by (by100 linarith)
          thus ?thesis using hr_pos by (by100 simp)
        qed
        have hr_tau_iv: "r \<in> {s_tau..t_tau}"
          using hs_tau_zero hr_pos hr_le_tau by (by100 simp)
        have hr_rho_iv: "r \<in> {s_rho..t_rho}"
          using hs_rho_zero hr_pos hr_le_rho by (by100 simp)
        have hr_tau: "\<gamma> r \<in> \<tau>"
          using hpre_tau hr_01 hr_tau_iv by (by100 blast)
        have hr_rho: "\<gamma> r \<in> \<rho>"
          using hpre_rho hr_01 hr_rho_iv by (by100 blast)
        have hr_neP: "\<gamma> r \<noteq> P"
        proof
          assume hrP: "\<gamma> r = P"
          have h0_01: "(0::real) \<in> {0..1}" by (by100 simp)
          have "r = 0"
            using hinj hr_01 h0_01 hrP h0P unfolding inj_on_def by (by100 blast)
          thus False using hr_pos by (by100 simp)
        qed
        show ?thesis using hr_01 hr_tau hr_rho hr_neP by (by100 blast)
      next
        assume h1P: "\<gamma> 1 = P"
        have hinj: "inj_on \<gamma> {0..1}"
          using h\<gamma>_arc unfolding arc_def by (by100 blast)
        have h1_pre_tau: "1 \<in> {s\<in>{0..1}. \<gamma> s \<in> \<tau>}"
          using h1P hP\<tau> by (by100 simp)
        have h1_tau_iv: "1 \<in> {s_tau..t_tau}"
          using h1_pre_tau hpre_tau by (by100 simp)
        have ht_tau_one: "t_tau = 1"
          using h1_tau_iv ht_tau_01 by (by100 simp)
        have hq_tau_img: "\<gamma> s_tau = q\<tau>"
        proof -
          have "q\<tau> \<in> {\<gamma> s_tau, \<gamma> t_tau}"
            using hends_tau by (by100 blast)
          thus ?thesis using ht_tau_one h1P hq\<tau>_ne by (by100 blast)
        qed
        have hs_tau_lt1: "s_tau < 1"
        proof -
          have "s_tau \<noteq> 1"
          proof
            assume hs1: "s_tau = 1"
            have "\<gamma> s_tau = P" using hs1 h1P by (by100 simp)
            thus False using hq_tau_img hq\<tau>_ne by (by100 simp)
          qed
          thus ?thesis using hs_tau_01 by (by100 simp)
        qed
        have h1_pre_rho: "1 \<in> {s\<in>{0..1}. \<gamma> s \<in> \<rho>}"
          using h1P hP\<rho> by (by100 simp)
        have h1_rho_iv: "1 \<in> {s_rho..t_rho}"
          using h1_pre_rho hpre_rho by (by100 simp)
        have ht_rho_one: "t_rho = 1"
          using h1_rho_iv ht_rho_01 by (by100 simp)
        have hq_rho_img: "\<gamma> s_rho = q\<rho>"
        proof -
          have "q\<rho> \<in> {\<gamma> s_rho, \<gamma> t_rho}"
            using hends_rho by (by100 blast)
          thus ?thesis using ht_rho_one h1P hq\<rho>_ne by (by100 blast)
        qed
        have hs_rho_lt1: "s_rho < 1"
        proof -
          have "s_rho \<noteq> 1"
          proof
            assume hs1: "s_rho = 1"
            have "\<gamma> s_rho = P" using hs1 h1P by (by100 simp)
            thus False using hq_rho_img hq\<rho>_ne by (by100 simp)
          qed
          thus ?thesis using hs_rho_01 by (by100 simp)
        qed
        define eta where "eta = min (1 - s_tau) (1 - s_rho) / 2"
        define r where "r = 1 - eta"
        have heta_pos: "eta > 0" unfolding eta_def using hs_tau_lt1 hs_rho_lt1 by (by100 simp)
        have hmin_pos: "min (1 - s_tau) (1 - s_rho) > 0"
          using hs_tau_lt1 hs_rho_lt1 by (by100 simp)
        have heta_le_min: "eta \<le> min (1 - s_tau) (1 - s_rho)"
        proof -
          have hdiv: "min (1 - s_tau) (1 - s_rho) / 2
              \<le> min (1 - s_tau) (1 - s_rho) / 1"
          proof (rule divide_left_mono)
            show "(1::real) \<le> 2" by (by100 simp)
            show "0 \<le> min (1 - s_tau) (1 - s_rho)" using hmin_pos by (by100 simp)
            show "0 < (2::real) * 1" by (by100 simp)
          qed
          show ?thesis unfolding eta_def using hdiv by (by100 simp)
        qed
        have hmin_le_tau: "min (1 - s_tau) (1 - s_rho) \<le> 1 - s_tau"
          by (by100 simp)
        have hmin_le_rho: "min (1 - s_tau) (1 - s_rho) \<le> 1 - s_rho"
          by (by100 simp)
        have heta_le_tau: "eta \<le> 1 - s_tau"
          using heta_le_min hmin_le_tau by (by100 linarith)
        have heta_le_rho: "eta \<le> 1 - s_rho"
          using heta_le_min hmin_le_rho by (by100 linarith)
        have heta_le1: "eta \<le> 1"
        proof -
          have hs_tau_ge0: "0 \<le> s_tau" using hs_tau_01 by (by100 simp)
          have "1 - s_tau \<le> 1" using hs_tau_ge0 by (by100 simp)
          thus ?thesis using heta_le_tau by (by100 linarith)
        qed
        have hr_lt1: "r < 1" unfolding r_def using heta_pos by (by100 simp)
        have hr_ge0: "0 \<le> r" unfolding r_def using heta_le1 by (by100 simp)
        have hr_01: "r \<in> {0..1}" using hr_ge0 hr_lt1 by (by100 simp)
        have hr_ge_tau: "s_tau \<le> r" unfolding r_def using heta_le_tau by (by100 linarith)
        have hr_ge_rho: "s_rho \<le> r" unfolding r_def using heta_le_rho by (by100 linarith)
        have hr_tau_iv: "r \<in> {s_tau..t_tau}"
          using hr_ge_tau hr_lt1 ht_tau_one by (by100 simp)
        have hr_rho_iv: "r \<in> {s_rho..t_rho}"
          using hr_ge_rho hr_lt1 ht_rho_one by (by100 simp)
        have hr_tau: "\<gamma> r \<in> \<tau>"
          using hpre_tau hr_01 hr_tau_iv by (by100 blast)
        have hr_rho: "\<gamma> r \<in> \<rho>"
          using hpre_rho hr_01 hr_rho_iv by (by100 blast)
        have hr_neP: "\<gamma> r \<noteq> P"
        proof
          assume hrP: "\<gamma> r = P"
          have h1_01: "(1::real) \<in> {0..1}" by (by100 simp)
          have "r = 1"
            using hinj hr_01 h1_01 hrP h1P unfolding inj_on_def by (by100 blast)
          thus False using hr_lt1 by (by100 simp)
        qed
        show ?thesis using hr_01 hr_tau hr_rho hr_neP by (by100 blast)
      qed
      obtain r where hr_01: "r \<in> {0..1}"
          and hr_tau: "\<gamma> r \<in> \<tau>"
          and hr_rho: "\<gamma> r \<in> \<rho>"
          and hr_ne: "\<gamma> r \<noteq> P"
        using h_ordered_endpoint_overlap by (by100 blast)
      show ?thesis using hr_tau hr_rho hr_ne by (by100 blast)
    qed
    obtain z where hz_inter: "z \<in> \<tau> \<inter> \<rho>" and hz_ne: "z \<noteq> P"
      using h_overlap_nonendpoint by (by100 blast)
    have h_inter_ne: "\<tau> \<inter> \<rho> \<noteq> {}" using hP\<tau> hP\<rho> by (by100 blast)
    have hface_\<tau>: "geotop_is_face (\<tau> \<inter> \<rho>) \<tau>"
      using hL_complex h\<tau>L h\<rho>L h_inter_ne unfolding geotop_is_complex_def by (by100 blast)
    have hface_\<rho>: "geotop_is_face (\<tau> \<inter> \<rho>) \<rho>"
      using hL_complex h\<tau>L h\<rho>L h_inter_ne unfolding geotop_is_complex_def by (by100 blast)
    have hP_inter: "P \<in> \<tau> \<inter> \<rho>" using hP\<tau> hP\<rho> by (by100 blast)
    have h\<tau>eq: "\<tau> \<inter> \<rho> = \<tau>"
      using segment_face_with_endpoint_and_extra_eq[of "\<tau> \<inter> \<rho>" P q\<tau> z]
            hface_\<tau> hq\<tau>_ne hP_inter hz_inter hz_ne h\<tau>_seg
      by (by100 simp)
    have h\<rho>eq: "\<tau> \<inter> \<rho> = \<rho>"
      using segment_face_with_endpoint_and_extra_eq[of "\<tau> \<inter> \<rho>" P q\<rho> z]
            hface_\<rho> hq\<rho>_ne hP_inter hz_inter hz_ne h\<rho>_seg
      by (by100 simp)
    show "\<tau> = \<rho>" using h\<tau>eq h\<rho>eq by (by100 simp)
  qed
  have htarget_eq: "{e\<in>L. geotop_is_edge e \<and> P \<in> e} = EdgesAtP"
    unfolding EdgesAtP_def geotop_is_edge_def by (by100 blast)
  obtain e where he_in: "e \<in> EdgesAtP"
      and he_unique: "\<And>y. y \<in> EdgesAtP \<Longrightarrow> y = e"
  proof -
    obtain e where he: "e \<in> EdgesAtP"
      using hEdges_nonempty by (by100 blast)
    have huniq: "\<And>y. y \<in> EdgesAtP \<Longrightarrow> y = e"
    proof -
      fix y assume hy: "y \<in> EdgesAtP"
      show "y = e"
        using hEdges_at_most_one hy he by (by100 blast)
    qed
    show ?thesis by (rule that[OF he huniq])
  qed
  have he: "EdgesAtP = {e}"
  proof
    show "EdgesAtP \<subseteq> {e}"
      using he_unique by (by100 blast)
    show "{e} \<subseteq> EdgesAtP"
      using he_in by (by100 blast)
  qed
  show ?thesis
    using htarget_eq he by (by100 simp)
qed

lemma geotop_degree_one_vertex_graph_endpoint_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hwL: "{w} \<in> L"
  assumes hcard1: "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1"
  shows "geotop_graph_endpoint L w"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have hw_vertex: "w \<in> geotop_complex_vertices L"
    using geotop_complex_vertices_eq_0_simplexes[OF hcomplex] hwL
    by (by100 blast)
  show ?thesis
    using hw_vertex hcard1 unfolding geotop_graph_endpoint_def by (by100 blast)
qed

lemma geotop_graph_endpoint_unique_incident_edge_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  shows "\<exists>!e. e \<in> L \<and> geotop_is_edge e \<and> w \<in> e"
proof -
  let ?S = "{e\<in>L. geotop_is_edge e \<and> w \<in> e}"
  have hcard: "card ?S = 1"
    using geotop_graph_endpoint_singleton_and_card_one_prefix[OF hL hend]
    by (by100 blast)
  obtain e where hS: "?S = {e}"
    by (rule card_1_singletonE[OF hcard])
  show ?thesis
  proof (rule ex1I[of _ e])
    show "e \<in> L \<and> geotop_is_edge e \<and> w \<in> e"
      using hS by (by100 auto)
  next
    fix e'
    assume he': "e' \<in> L \<and> geotop_is_edge e' \<and> w \<in> e'"
    have "e' \<in> ?S" using he' by (by100 simp)
    thus "e' = e" using hS by (by100 simp)
  qed
qed

lemma geotop_graph_endpoint_unique_segment_neighbor_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  shows "\<exists>e q. e \<in> L \<and> geotop_is_edge e \<and> w \<in> e
      \<and> q \<noteq> w \<and> e = closed_segment w q \<and> {q} \<in> L"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have h1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_prefix[OF hL])
  have hwL: "{w} \<in> L"
    using geotop_graph_endpoint_singleton_and_card_one_prefix[OF hL hend]
    by (by100 blast)
  obtain e where heL: "e \<in> L" and hedge: "geotop_is_edge e" and hw_e: "w \<in> e"
    using geotop_graph_endpoint_unique_incident_edge_prefix[OF hL hfin hend]
    by (by100 blast)
  have hedim: "geotop_simplex_dim e 1"
    using hedge unfolding geotop_is_edge_def by (by100 simp)
  have hcases: "(\<exists>v. e = {v}) \<or> (\<exists>a b. a \<noteq> b \<and> e = closed_segment a b)"
    by (rule geotop_1dim_simplex_cases[OF h1dim heL])
  show ?thesis
  proof (rule disjE[OF hcases])
    assume "\<exists>v. e = {v}"
    then obtain v where hev: "e = {v}" by (by100 blast)
    have hdim0: "geotop_simplex_dim e 0"
      using hev geotop_singleton_is_simplex by (by100 simp)
    have "0 = (1::nat)" by (rule geotop_simplex_dim_unique[OF hdim0 hedim])
    hence False by simp
    thus ?thesis by (rule FalseE)
  next
    assume "\<exists>a b. a \<noteq> b \<and> e = closed_segment a b"
    then obtain a b where hab: "a \<noteq> b" and heab: "e = closed_segment a b"
      by (by100 blast)
    have hw_endpoint: "w = a \<or> w = b"
      by (rule geotop_1dim_vertex_in_1simplex_is_endpoint
          [OF hcomplex hwL heL heab hab hw_e])
    have hface_closed: "\<forall>\<rho>\<in>L. \<forall>\<tau>. geotop_is_face \<tau> \<rho> \<longrightarrow> \<tau> \<in> L"
      by (rule geotop_is_complex_face_closed[OF hcomplex])
    show ?thesis
    proof (rule disjE[OF hw_endpoint])
      assume hwa: "w = a"
      have hba: "b \<noteq> a" using hab by (by100 blast)
      have hface_b: "geotop_is_face {b} e"
        using geotop_closed_segment_is_face_endpoint[OF hba, of b]
          heab closed_segment_commute[of a b]
        by (by100 simp)
      have hbL: "{b} \<in> L"
        using hface_closed heL hface_b by (by100 blast)
      have hbw: "b \<noteq> w"
        using hba hwa by (by100 blast)
      have hewb: "e = closed_segment w b"
        using heab hwa by (by100 simp)
      show ?thesis
        using heL hedge hw_e hbw hewb hbL by (by100 blast)
    next
      assume hwb: "w = b"
      have hface_a: "geotop_is_face {a} e"
        using geotop_closed_segment_is_face_endpoint[OF hab, of a] heab
        by (by100 simp)
      have haL: "{a} \<in> L"
        using hface_closed heL hface_a by (by100 blast)
      have haw: "a \<noteq> w"
        using hab hwb by (by100 blast)
      have hewa: "e = closed_segment w a"
        using heab hwb closed_segment_commute[of a b] by (by100 simp)
      show ?thesis
        using heL hedge hw_e haw hewa haL by (by100 blast)
    qed
  qed
qed

lemma geotop_graph_endpoint_simplex_containing_endpoint_eq_vertex_or_edge_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  assumes h\<sigma>L: "\<sigma> \<in> L"
  assumes hw\<sigma>: "w \<in> \<sigma>"
  shows "\<sigma> = {w} \<or> \<sigma> = e"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have h1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_prefix[OF hL])
  have hwL: "{w} \<in> L"
    using geotop_graph_endpoint_singleton_and_card_one_prefix[OF hL hend]
    by (by100 blast)
  have hunique: "\<exists>!l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l"
    by (rule geotop_graph_endpoint_unique_incident_edge_prefix[OF hL hfin hend])
  have hcases: "(\<exists>v. \<sigma> = {v}) \<or> (\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b)"
    by (rule geotop_1dim_simplex_cases[OF h1dim h\<sigma>L])
  show ?thesis
  proof (rule disjE[OF hcases])
    assume "\<exists>v. \<sigma> = {v}"
    then obtain v where h\<sigma>v: "\<sigma> = {v}" by (by100 blast)
    have "v = w" using h\<sigma>v hw\<sigma> by (by100 blast)
    show ?thesis using h\<sigma>v \<open>v = w\<close> by (by100 simp)
  next
    assume "\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b"
    then obtain a b where hab: "a \<noteq> b" and h\<sigma>ab: "\<sigma> = closed_segment a b"
      by (by100 blast)
    have h\<sigma>edge: "geotop_is_edge \<sigma>"
      using geotop_closed_segment_is_simplex[OF hab] h\<sigma>ab
      unfolding geotop_is_edge_def by (by100 simp)
    have h\<sigma>prop: "\<sigma> \<in> L \<and> geotop_is_edge \<sigma> \<and> w \<in> \<sigma>"
      using h\<sigma>L h\<sigma>edge hw\<sigma> by (by100 blast)
    have heprop: "e \<in> L \<and> geotop_is_edge e \<and> w \<in> e"
      using heL hedge hwe by (by100 blast)
    have "\<sigma> = e"
      using hunique h\<sigma>prop heprop by (by100 blast)
    show ?thesis using \<open>\<sigma> = e\<close> by (by100 blast)
  qed
qed

lemma geotop_graph_endpoint_delete_leaf_polyhedron_union_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "geotop_polyhedron L = e \<union> geotop_polyhedron (L - {{w}, e})"
proof -
  have honly: "\<And>\<sigma>. \<lbrakk>\<sigma> \<in> L; w \<in> \<sigma>\<rbrakk> \<Longrightarrow> \<sigma> = {w} \<or> \<sigma> = e"
    by (rule geotop_graph_endpoint_simplex_containing_endpoint_eq_vertex_or_edge_prefix
        [OF hL hfin hend heL hedge hwe])
  have hsubset_w_e: "{w} \<subseteq> e"
    using hwe by (by100 blast)
  show ?thesis
  proof
    show "geotop_polyhedron L \<subseteq> e \<union> geotop_polyhedron (L - {{w}, e})"
    proof
      fix x
      assume hx: "x \<in> geotop_polyhedron L"
      obtain \<sigma> where h\<sigma>L: "\<sigma> \<in> L" and hx\<sigma>: "x \<in> \<sigma>"
        using hx unfolding geotop_polyhedron_def by (by100 blast)
      show "x \<in> e \<union> geotop_polyhedron (L - {{w}, e})"
      proof (cases "w \<in> \<sigma>")
        case True
        have hcase: "\<sigma> = {w} \<or> \<sigma> = e"
          by (rule honly[OF h\<sigma>L True])
        show ?thesis
        proof (rule disjE[OF hcase])
          assume "\<sigma> = {w}"
          have "x \<in> e" using hx\<sigma> \<open>\<sigma> = {w}\<close> hsubset_w_e by (by100 blast)
          thus ?thesis by (by100 blast)
        next
          assume "\<sigma> = e"
          have "x \<in> e" using hx\<sigma> \<open>\<sigma> = e\<close> by (by100 simp)
          thus ?thesis by (by100 blast)
        qed
      next
        case False
        have h\<sigma>rest: "\<sigma> \<in> L - {{w}, e}"
        proof -
          have "\<sigma> \<noteq> {w}" using False by (by100 blast)
          have "\<sigma> \<noteq> e" using False hwe by (by100 blast)
          show ?thesis using h\<sigma>L \<open>\<sigma> \<noteq> {w}\<close> \<open>\<sigma> \<noteq> e\<close> by (by100 simp)
        qed
        have "x \<in> geotop_polyhedron (L - {{w}, e})"
          unfolding geotop_polyhedron_def using h\<sigma>rest hx\<sigma> by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
    qed
  next
    show "e \<union> geotop_polyhedron (L - {{w}, e}) \<subseteq> geotop_polyhedron L"
    proof
      fix x
      assume hx: "x \<in> e \<union> geotop_polyhedron (L - {{w}, e})"
      show "x \<in> geotop_polyhedron L"
      proof (rule UnE[OF hx])
        assume "x \<in> e"
        show ?thesis
          unfolding geotop_polyhedron_def using heL \<open>x \<in> e\<close> by (by100 blast)
      next
        assume "x \<in> geotop_polyhedron (L - {{w}, e})"
        obtain \<sigma> where h\<sigma>rest: "\<sigma> \<in> L - {{w}, e}" and hx\<sigma>: "x \<in> \<sigma>"
          using \<open>x \<in> geotop_polyhedron (L - {{w}, e})\<close>
          unfolding geotop_polyhedron_def by (by100 blast)
        have h\<sigma>L: "\<sigma> \<in> L" using h\<sigma>rest by (by100 simp)
        show ?thesis
          unfolding geotop_polyhedron_def using h\<sigma>L hx\<sigma> by (by100 blast)
      qed
    qed
  qed
qed

lemma geotop_graph_endpoint_not_in_delete_leaf_polyhedron_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "w \<notin> geotop_polyhedron (L - {{w}, e})"
proof
  assume hwrest: "w \<in> geotop_polyhedron (L - {{w}, e})"
  obtain \<sigma> where h\<sigma>rest: "\<sigma> \<in> L - {{w}, e}" and hw\<sigma>: "w \<in> \<sigma>"
    using hwrest unfolding geotop_polyhedron_def by (by100 blast)
  have h\<sigma>L: "\<sigma> \<in> L"
    using h\<sigma>rest by (by100 simp)
  have hcase: "\<sigma> = {w} \<or> \<sigma> = e"
    by (rule geotop_graph_endpoint_simplex_containing_endpoint_eq_vertex_or_edge_prefix
        [OF hL hfin hend heL hedge hwe h\<sigma>L hw\<sigma>])
  show False
  proof (rule disjE[OF hcase])
    assume "\<sigma> = {w}"
    show False using h\<sigma>rest \<open>\<sigma> = {w}\<close> by (by100 simp)
  next
    assume "\<sigma> = e"
    show False using h\<sigma>rest \<open>\<sigma> = e\<close> by (by100 simp)
  qed
qed

lemma geotop_broken_line_polyhedron_finite_linear_graph_has_endpoint_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hB: "geotop_is_broken_line (geotop_polyhedron L)"
  shows "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
proof -
  obtain K where hB_arc:
      "geotop_is_arc (geotop_polyhedron L)
        (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    using hB unfolding geotop_is_broken_line_def by (by100 blast)
  obtain E where hE: "geotop_arc_endpoints (geotop_polyhedron L) E"
    using geotop_is_arc_has_arc_endpoints_prefix[OF hB_arc] by (by100 blast)
  have hcardE: "card E = 2"
    using hE unfolding geotop_arc_endpoints_def by (by100 blast)
  have hE_nonempty: "E \<noteq> {}"
  proof
    assume hE_empty: "E = {}"
    have "card E = 0" using hE_empty by (by100 simp)
    thus False using hcardE by (by100 simp)
  qed
  obtain P where hP: "P \<in> E" using hE_nonempty by (by100 blast)
  have hpoly_refl: "geotop_polyhedron L = geotop_polyhedron L"
    by (by100 simp)
  have hPL: "{P} \<in> L"
    by (rule geotop_broken_line_endpoint_in_finite_linear_graph_vertex_prefix
        [OF hL hfin hpoly_refl hB hE hP])
  have hcard_edges: "card {e\<in>L. geotop_is_edge e \<and> P \<in> e} = 1"
    by (rule geotop_broken_line_endpoint_vertex_incident_edge_card_one_prefix
        [OF hL hfin hpoly_refl hB hE hP hPL])
  have h_endpoint: "geotop_graph_endpoint L P"
    by (rule geotop_degree_one_vertex_graph_endpoint_prefix[OF hL hPL hcard_edges])
  show ?thesis using hPL h_endpoint by (by100 blast)
qed

lemma geotop_degree_two_linear_graph_polyhedron_not_broken_line_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  shows "\<not> geotop_is_broken_line (geotop_polyhedron L)"
proof
  assume hB: "geotop_is_broken_line (geotop_polyhedron L)"
  obtain w where hwL: "{w} \<in> L" and hend: "geotop_graph_endpoint L w"
    using geotop_broken_line_polyhedron_finite_linear_graph_has_endpoint_prefix
      [OF hL hfin hB] by (by100 blast)
  have hcard1: "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1"
    using hend unfolding geotop_graph_endpoint_def by (by100 blast)
  have hcard2: "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
    using hdegree hwL by (by100 blast)
  show False
    using hcard1 hcard2 by (by100 simp)
qed


end
