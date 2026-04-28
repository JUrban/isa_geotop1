theory Scratch
imports "GeoTopBase.GeoTopBase"
begin

text \<open>Chunk-out workspace for the deepest sub-sorry of h_open_in_int.
  Locale assumes the line/normal already extracted (via existing helpers
  in GeoTop.thy that aren't moved to base).\<close>

locale h_local_open_ctx =
  fixes M B1 B2 B3 E :: "(real^2) set" and i :: "(real^2) set"
    and U :: "(real^2) set" and x :: "real^2"
    and \<delta>_iso :: real and \<sigma>_x :: "(real^2) set"
    and a b :: "real^2"
    and n :: "real^2"
  assumes hU_open: "open U"
      and hxFr: "x \<in> frontier U"
      and hxInt: "x \<in> geotop_arc_interior i E"
      and hxi: "x \<in> i"
      and h\<delta>_iso_pos: "\<delta>_iso > 0"
      and h_ball_iso_M: "ball x \<delta>_iso \<inter> M \<subseteq> i"
      and hM_eq: "M = B1 \<union> B2 \<union> B3"
      and hU_disj_M: "U \<inter> M = {}"
      and hU_meets_ball: "\<forall>\<delta>'>0. ball x \<delta>' \<inter> U \<noteq> {}"
      and h\<sigma>_x_dim: "geotop_simplex_dim \<sigma>_x 1"
      and h\<sigma>_x_seg: "\<sigma>_x = closed_segment a b"
      and hab_ne: "a \<noteq> b"
      and hx\<sigma>_x: "x \<in> \<sigma>_x"
      and hn_ne: "n \<noteq> (0::real^2)"
      and hL_form: "affine hull \<sigma>_x = {y. inner (y - x) n = 0}"
      \<comment> \<open>Single-edge case: locally within ball x δ_iso, the line L is contained
        in σ_x. This simplifies to: ball x δ_iso ∩ L ⊆ M.\<close>
      and h_local_L_in_M: "ball x \<delta>_iso \<inter> {y. inner (y - x) n = 0} \<subseteq> M"
begin

text \<open>Step 13: Apply ball_minus_hyperplane_has_two_components.\<close>

lemma test_two_halfballs:
  shows "\<exists>U_pos U_neg. ball x \<delta>_iso - {y. inner (y - x) n = 0} = U_pos \<union> U_neg \<and>
                       U_pos \<inter> U_neg = {} \<and> U_pos \<noteq> {} \<and> U_neg \<noteq> {} \<and>
                       connected U_pos \<and> connected U_neg \<and>
                       open U_pos \<and> open U_neg"
  by (rule ball_minus_hyperplane_has_two_components[OF hn_ne h\<delta>_iso_pos])

text \<open>Step 14: Get the half-balls explicitly (named).\<close>

definition Hp where "Hp = ball x \<delta>_iso \<inter> {y. inner (y - x) n > 0}"
definition Hm where "Hm = ball x \<delta>_iso \<inter> {y. inner (y - x) n < 0}"

lemma Hp_open: "open Hp"
proof -
  have h_eq: "{y. inner (y - x) n > 0} = {y. inner n y > inner n x}"
    by (auto simp: inner_diff_right inner_commute)
  have h_open: "open {y. inner n y > inner n x}" by (rule open_halfspace_gt)
  show ?thesis unfolding Hp_def h_eq using h_open open_ball by (intro open_Int)
qed

lemma Hm_open: "open Hm"
proof -
  have h_eq: "{y. inner (y - x) n < 0} = {y. inner n y < inner n x}"
    by (auto simp: inner_diff_right inner_commute)
  have h_open: "open {y. inner n y < inner n x}" by (rule open_halfspace_lt)
  show ?thesis unfolding Hm_def h_eq using h_open open_ball by (intro open_Int)
qed

text \<open>Step 15: U-points within ball x δ_iso live in Hp ∪ Hm (since U disjoint
  from M, M locally fills the line).\<close>

lemma U_local_in_halfballs:
  shows "U \<inter> ball x \<delta>_iso \<subseteq> Hp \<union> Hm"
proof
  fix u assume hu: "u \<in> U \<inter> ball x \<delta>_iso"
  have huU: "u \<in> U" using hu by (by100 blast)
  have hu_ball: "u \<in> ball x \<delta>_iso" using hu by (by100 blast)
  have hu_notM: "u \<notin> M" using huU hU_disj_M by (by100 blast)
  have hu_notL: "u \<notin> {y. inner (y - x) n = 0}"
    using hu_ball hu_notM h_local_L_in_M by (by100 blast)
  have hu_inner_ne: "inner (u - x) n \<noteq> 0" using hu_notL by (by100 simp)
  consider (pos) "inner (u - x) n > 0" | (neg) "inner (u - x) n < 0"
    using hu_inner_ne by (by100 force)
  thus "u \<in> Hp \<union> Hm"
  proof cases
    case pos
    have "u \<in> Hp" unfolding Hp_def using hu_ball pos by (by100 simp)
    thus ?thesis by (by100 blast)
  next
    case neg
    have "u \<in> Hm" unfolding Hm_def using hu_ball neg by (by100 simp)
    thus ?thesis by (by100 blast)
  qed
qed

text \<open>Step 16: U meets at least one of Hp or Hm (since x ∈ frontier U + U open).\<close>

lemma U_meets_halfball:
  shows "U \<inter> Hp \<noteq> {} \<or> U \<inter> Hm \<noteq> {}"
proof -
  have h_meet: "ball x \<delta>_iso \<inter> U \<noteq> {}" using hU_meets_ball h\<delta>_iso_pos by (by100 blast)
  obtain u where hu_inter: "u \<in> ball x \<delta>_iso \<inter> U" using h_meet by (by100 blast)
  have hu_in: "u \<in> U \<inter> ball x \<delta>_iso" using hu_inter by (by100 blast)
  have hu_HpHm: "u \<in> Hp \<union> Hm" using hu_in U_local_in_halfballs by (by100 blast)
  show ?thesis using hu_in hu_HpHm by (by100 blast)
qed

text \<open>Step 17: For ANY ball around x, U meets some halfball with that smaller δ.\<close>

definition Hp_at where "Hp_at \<delta>' = ball x \<delta>' \<inter> {y. inner (y - x) n > 0}"
definition Hm_at where "Hm_at \<delta>' = ball x \<delta>' \<inter> {y. inner (y - x) n < 0}"

lemma U_meets_halfball_smaller:
  assumes h\<delta>'_pos: "\<delta>' > 0" and h\<delta>'_le: "\<delta>' \<le> \<delta>_iso"
  shows "U \<inter> Hp_at \<delta>' \<noteq> {} \<or> U \<inter> Hm_at \<delta>' \<noteq> {}"
proof -
  have h_meet: "ball x \<delta>' \<inter> U \<noteq> {}" using hU_meets_ball h\<delta>'_pos by (by100 blast)
  obtain u where hu: "u \<in> ball x \<delta>' \<inter> U" using h_meet by (by100 blast)
  have hu_ball_iso: "u \<in> ball x \<delta>_iso"
  proof -
    have h_sub: "ball x \<delta>' \<subseteq> ball x \<delta>_iso" using h\<delta>'_le by (by100 auto)
    show ?thesis using hu h_sub by (by100 blast)
  qed
  have huU: "u \<in> U" using hu by (by100 blast)
  have hu_in: "u \<in> U \<inter> ball x \<delta>_iso" using huU hu_ball_iso by (by100 blast)
  have hu_HpHm: "u \<in> Hp \<union> Hm" using hu_in U_local_in_halfballs by (by100 blast)
  have hu_ball': "u \<in> ball x \<delta>'" using hu by (by100 blast)
  consider (p) "u \<in> Hp" | (m) "u \<in> Hm" using hu_HpHm by (by100 blast)
  thus ?thesis
  proof cases
    case p
    have hu_pos: "inner (u - x) n > 0" using p Hp_def by (by100 simp)
    have "u \<in> Hp_at \<delta>'" unfolding Hp_at_def using hu_ball' hu_pos by (by100 simp)
    thus ?thesis using huU by (by100 blast)
  next
    case m
    have hu_neg: "inner (u - x) n < 0" using m Hm_def by (by100 simp)
    have "u \<in> Hm_at \<delta>'" unfolding Hm_at_def using hu_ball' hu_neg by (by100 simp)
    thus ?thesis using huU by (by100 blast)
  qed
qed

text \<open>Step 18: For y close to x on σ_x and r > |y-x|, ball y r meets U.
  Uses: U-points exist near x (within r-|y-x|) and triangle inequality.\<close>

lemma U_near_y_when_r_large:
  fixes y :: "real^2" and r :: real
  assumes h_y_seg: "y \<in> \<sigma>_x"
      and h_y_ball: "y \<in> ball x \<delta>_iso"
      and h_r_pos: "r > 0"
      and h_r_gt: "r > dist y x"
  shows "ball y r \<inter> U \<noteq> {}"
proof -
  define \<eta> where "\<eta> = r - dist y x"
  have h\<eta>_pos: "\<eta> > 0" unfolding \<eta>_def using h_r_gt by (by100 simp)
  have h_meet: "ball x \<eta> \<inter> U \<noteq> {}"
    using hU_meets_ball h\<eta>_pos by (by100 blast)
  obtain u where hu: "u \<in> ball x \<eta> \<inter> U" using h_meet by (by100 blast)
  have hu_in_ball_x: "u \<in> ball x \<eta>" using hu by (by100 blast)
  have hu_dist_xu: "dist x u < \<eta>" using hu_in_ball_x by (by100 simp)
  have hu_dist_y: "dist u y \<le> dist u x + dist x y" by (rule dist_triangle)
  have h_dux_eq: "dist u x = dist x u" by (rule dist_commute)
  have hu_dist_ux: "dist u x < \<eta>"
    using hu_dist_xu h_dux_eq by (by100 simp)
  have hu_dist_lt: "dist u y < \<eta> + dist x y"
    using hu_dist_ux hu_dist_y by (by100 simp)
  have h_dist_xy_eq: "dist x y = dist y x" by (rule dist_commute)
  have hu_dist_r: "dist u y < r"
    using hu_dist_lt h_dist_xy_eq \<eta>_def by (by100 simp)
  have h_dyu_eq: "dist y u = dist u y" by (rule dist_commute)
  have hu_dist_yu: "dist y u < r" using hu_dist_r h_dyu_eq by (by100 simp)
  have hu_in_ball: "u \<in> ball y r" using hu_dist_yu by (by100 simp)
  have huU: "u \<in> U" using hu by (by100 blast)
  show ?thesis using hu_in_ball huU by (by100 blast)
qed

end

text \<open>Helper: For x ∈ open_segment a b, ball x δ ∩ aff_hull(closed_segment a b)
  is contained in closed_segment a b, when δ ≤ min(dist x a, dist x b).\<close>

lemma scratch_segment_in_segment:
  fixes a b x :: "real^2"
  assumes hab_ne: "a \<noteq> b"
      and hx_open: "x \<in> open_segment a b"
      and h\<delta>_pos: "\<delta> > 0"
      and h\<delta>_le_a: "\<delta> \<le> dist x a"
      and h\<delta>_le_b: "\<delta> \<le> dist x b"
  shows "ball x \<delta> \<inter> affine hull (closed_segment a b) \<subseteq> closed_segment a b"
proof
  fix y assume hy: "y \<in> ball x \<delta> \<inter> affine hull (closed_segment a b)"
  have hy_ball: "y \<in> ball x \<delta>" using hy by blast
  have hy_aff_seg: "y \<in> affine hull (closed_segment a b)" using hy by blast
  have h_aff_eq: "affine hull (closed_segment a b) = affine hull {a, b}"
    using segment_convex_hull[of a b] affine_hull_convex_hull[of "{a, b}"]
    by simp
  have hy_aff: "y \<in> affine hull {a, b}" using hy_aff_seg h_aff_eq by simp
  have h_aff_form: "affine hull {a, b}
                     = {u *\<^sub>R a + v *\<^sub>R b | u v. u + v = 1}"
    by (rule affine_hull_2)
  obtain u v where huv: "u + v = 1" and hy_uv: "y = u *\<^sub>R a + v *\<^sub>R b"
    using hy_aff h_aff_form by blast
  \<comment> \<open>x has its own representation s, 1-s with s \<in> (0,1).\<close>
  obtain s where hs_pos: "0 < s" and hs_lt: "s < 1"
              and hx_eq: "x = (1 - s) *\<^sub>R a + s *\<^sub>R b"
    using hx_open in_segment(2) by blast
  \<comment> \<open>Compute y - x in terms of (v - s) and (b - a).\<close>
  have hu_eq: "u = 1 - v" using huv by simp
  have hy_uv2: "y = (1 - v) *\<^sub>R a + v *\<^sub>R b" using hy_uv hu_eq by simp
  have hyx_eq: "y - x = (v - s) *\<^sub>R (b - a)"
  proof -
    have "y - x = ((1-v) *\<^sub>R a + v *\<^sub>R b) - ((1-s) *\<^sub>R a + s *\<^sub>R b)"
      using hy_uv2 hx_eq by simp
    also have "\<dots> = (v - s) *\<^sub>R (b - a)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have h_norm_yx: "norm (y - x) = \<bar>v - s\<bar> * norm (b - a)"
    using hyx_eq by simp
  have h_dist_xy: "dist x y = \<bar>v - s\<bar> * norm (b - a)"
    using h_norm_yx by (simp add: dist_norm norm_minus_commute)
  have h_xa_eq: "x - a = s *\<^sub>R (b - a)"
  proof -
    have "x - a = (1-s) *\<^sub>R a + s *\<^sub>R b - a" using hx_eq by simp
    also have "\<dots> = s *\<^sub>R (b - a)" by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have h_dist_xa: "dist x a = s * norm (b - a)"
    using h_xa_eq hs_pos by (simp add: dist_norm)
  have h_xb_eq: "x - b = (1-s) *\<^sub>R (a - b)"
  proof -
    have "x - b = (1-s) *\<^sub>R a + s *\<^sub>R b - b" using hx_eq by simp
    also have "\<dots> = (1-s) *\<^sub>R (a - b)" by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have h_dist_xb: "dist x b = (1-s) * norm (b - a)"
    using h_xb_eq hs_lt by (simp add: dist_norm norm_minus_commute)
  \<comment> \<open>From hy_ball: dist x y < δ ≤ s * norm(b-a) AND ≤ (1-s) * norm(b-a).\<close>
  have h_dist_lt: "dist x y < \<delta>" using hy_ball by simp
  have h_norm_pos: "norm (b - a) > 0" using hab_ne by simp
  have h_abs_lt_s: "\<bar>v - s\<bar> < s"
  proof -
    have "\<bar>v - s\<bar> * norm (b - a) < \<delta>" using h_dist_lt h_dist_xy by simp
    also have "\<dots> \<le> dist x a" using h\<delta>_le_a .
    also have "\<dots> = s * norm (b - a)" using h_dist_xa .
    finally have "\<bar>v - s\<bar> * norm (b - a) < s * norm (b - a)" .
    thus ?thesis using h_norm_pos by simp
  qed
  have h_abs_lt_1ms: "\<bar>v - s\<bar> < 1 - s"
  proof -
    have "\<bar>v - s\<bar> * norm (b - a) < \<delta>" using h_dist_lt h_dist_xy by simp
    also have "\<dots> \<le> dist x b" using h\<delta>_le_b .
    also have "\<dots> = (1-s) * norm (b - a)" using h_dist_xb .
    finally have "\<bar>v - s\<bar> * norm (b - a) < (1-s) * norm (b - a)" .
    thus ?thesis using h_norm_pos by simp
  qed
  have hv_pos: "v > 0" using h_abs_lt_s by linarith
  have hv_lt_1: "v < 1" using h_abs_lt_1ms by linarith
  have hv_in: "0 \<le> v \<and> v \<le> 1" using hv_pos hv_lt_1 by simp
  show "y \<in> closed_segment a b"
    using hy_uv2 hv_in by (auto simp: closed_segment_def)
qed

end
