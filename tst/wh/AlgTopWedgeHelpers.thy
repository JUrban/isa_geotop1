theory AlgTopWedgeHelpers
  imports "AlgTopSvK.AlgTopSvK"
begin


section \<open>Chapter 12: Classification of Surfaces\<close>

text \<open>Surface: a connected, Hausdorff, compact 2-manifold.
  A 2-manifold is a space where every point has a neighborhood homeomorphic
  to an open subset of R^2.\<close>
definition top1_is_2_manifold_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_2_manifold_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     is_hausdorff_on X TX \<and>
     (\<forall>x\<in>X. \<exists>U (V :: (real \<times> real) set) h.
        x \<in> U \<and> openin_on X TX U \<and>
        V \<in> product_topology_on top1_open_sets top1_open_sets \<and>
        top1_homeomorphism_on U (subspace_topology X TX U) V
          (subspace_topology UNIV
             (product_topology_on top1_open_sets top1_open_sets) V)
          h)"
     \<comment> \<open>Munkres's definition of an n-manifold requires Hausdorff (and second countable,
         but that's implied by compact + locally Euclidean for our surface case).\<close>

definition top1_is_surface_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_surface_on X TX \<longleftrightarrow>
     top1_is_2_manifold_on X TX \<and>
     top1_connected_on X TX \<and>
     is_hausdorff_on X TX \<and>
     top1_compact_on X TX \<and>
     X \<noteq> {}"
     \<comment> \<open>Non-emptiness is required: classification theorem §77.5 says a surface is
         S^2, T_n, or P_m, none of which are empty. Without X \<noteq> {}, the empty set
         would vacuously satisfy locally-Euclidean and falsify §77.5.\<close>

section \<open>\<S>74 Fundamental Groups of Surfaces\<close>

\<comment> \<open>Unused undefined placeholders top1_n_fold_torus and top1_m_fold_projective
    removed. Use top1_is_n_fold_torus_on and top1_is_m_fold_projective_on predicates
    (defined earlier) on a space (X, TX) instead.\<close>


text \<open>Cone superset: cone(conv n, v_n) \<subseteq> conv(Suc n).\<close>
lemma convex_hull_cone_sup:
  fixes vx vy :: "nat \<Rightarrow> real"
  shows "(\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})
    \<subseteq> {(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}"
proof (rule subsetI)
  fix q assume hq_mem: "q \<in> (\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})"
  then obtain p where hp: "p \<in> {0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
      \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      and hq: "q = (case p of (t, x', y') \<Rightarrow> ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))"
    by (by100 blast)
  obtain t r where htr: "p = (t, r)" "t \<in> {0..1}" by (cases p) (use hp in \<open>(by100 auto)\<close>)
  obtain x' y' where hr: "r = (x', y')" by (cases r)
  have ht: "0 \<le> t" "t \<le> 1" using htr(2) by (by100 auto)+
  have hq_eq: "q = ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n)"
    using hq htr(1) hr by (by100 simp)
  obtain c' where hc': "\<forall>i<n. (0::real) \<le> c' i" "(\<Sum>i<n. c' i) = 1"
      "x' = (\<Sum>i<n. c' i * vx i)" "y' = (\<Sum>i<n. c' i * vy i)"
    using hp htr(1) hr by (by100 blast)
  let ?c = "\<lambda>i. if i < n then (1-t) * c' i else if i = n then t else 0 :: real"
  have hc_nn: "\<forall>i<Suc n. 0 \<le> ?c i" using ht hc'(1) by (by100 force)
  have hc_sum: "(\<Sum>i<Suc n. ?c i) = 1"
  proof -
    have "(\<Sum>i<n. ?c i) = (\<Sum>i<n. (1-t) * c' i)" by (rule sum.cong) (by100 simp)+
    also have "\<dots> = (1-t)" using hc'(2) by (simp add: sum_distrib_left[symmetric])
    finally show ?thesis by (by100 simp)
  qed
  have hc_x: "(\<Sum>i<Suc n. ?c i * vx i) = (1-t)*x' + t*vx n"
  proof -
    have "(\<Sum>i<n. ?c i * vx i) = (\<Sum>i<n. (1-t) * c' i * vx i)"
      by (rule sum.cong) (by100 simp)+
    also have "\<dots> = (1-t) * x'" using hc'(3) by (simp add: sum_distrib_left mult.assoc)
    finally show ?thesis by (by100 simp)
  qed
  have hc_y: "(\<Sum>i<Suc n. ?c i * vy i) = (1-t)*y' + t*vy n"
  proof -
    have "(\<Sum>i<n. ?c i * vy i) = (\<Sum>i<n. (1-t) * c' i * vy i)"
      by (rule sum.cong) (by100 simp)+
    also have "\<dots> = (1-t) * y'" using hc'(4) by (simp add: sum_distrib_left mult.assoc)
    finally show ?thesis by (by100 simp)
  qed
  show "q \<in> {(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}"
    unfolding hq_eq
    apply simp
    apply (rule_tac x="?c" in exI)
    using hc_nn hc_sum hc_x hc_y by force
qed

text \<open>Cone subset: conv(Suc n) \<subseteq> cone(conv n, v_n).\<close>
lemma convex_hull_cone_sub:
  fixes vx vy :: "nat \<Rightarrow> real"
  assumes "n \<ge> 1"
  shows "{(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}
    \<subseteq> (\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})"
proof (rule subsetI)
  fix q assume "q \<in> {(x, y). \<exists>c. (\<forall>i<Suc n. c i \<ge> 0) \<and> (\<Sum>i<Suc n. c i) = 1
      \<and> x = (\<Sum>i<Suc n. c i * vx i) \<and> y = (\<Sum>i<Suc n. c i * vy i)}"
  then obtain x y c where hq: "q = (x, y)"
      and hc: "\<forall>i<Suc n. (0::real) \<le> c i" "(\<Sum>i<Suc n. c i) = 1"
      "x = (\<Sum>i<Suc n. c i * vx i)" "y = (\<Sum>i<Suc n. c i * vy i)"
    by (by100 blast)
  let ?t = "c n"
  have ht0: "0 \<le> ?t" using hc(1) by (by100 force)
  have ht1: "?t \<le> 1"
    by (rule order_trans[OF member_le_sum[of n "{..<Suc n}" c]]) (use hc in auto)
  show "q \<in> (\<lambda>(t, x', y'). ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))
      ` ({0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
          \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)})"
  proof (cases "?t = 1")
    case True
    have hsum0: "(\<Sum>i<n. c i) = 0" using hc(2) True by simp
    have hall0: "\<forall>i<n. c i = 0"
    proof (intro allI impI)
      fix i assume "i < n"
      have "c i \<le> (\<Sum>i<n. c i)" by (rule member_le_sum) (use hc(1) \<open>i<n\<close> in auto)
      moreover have "0 \<le> c i" using hc(1) \<open>i<n\<close> by (by100 force)
      ultimately show "c i = 0" using hsum0 by (by100 linarith)
    qed
    have hx_vn: "x = vx n" using hc(3) hall0 True by simp
    have hy_vn: "y = vy n" using hc(4) hall0 True by simp
    \<comment> \<open>n \<ge> 1 (from induction hypothesis), so Pn is non-empty: (vx 0, vy 0) \<in> Pn.\<close>
    have hn1: "n \<ge> 1" using assms .
    let ?d = "\<lambda>i::nat. if i = 0 then 1::real else 0"
    have "(vx 0, vy 0) \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      apply simp
      apply (rule_tac x="?d" in exI)
    proof (intro conjI allI impI)
      fix i :: nat assume "i < n" thus "0 \<le> ?d i" by (by100 simp)
    next
      show "(\<Sum>i<n. ?d i) = 1" using hn1 by simp
    next
      show "vx 0 = (\<Sum>i<n. ?d i * vx i)"
      proof -
        have "(\<Sum>i<n. ?d i * vx i) = ?d 0 * vx 0 + (\<Sum>i\<in>{..<n}-{0}. ?d i * vx i)"
          using hn1 by (intro sum.remove) auto
        also have "(\<Sum>i\<in>{..<n}-{0}. ?d i * vx i) = 0"
          by (rule sum.neutral) (by100 simp)
        finally show ?thesis by (by100 simp)
      qed
    next
      show "vy 0 = (\<Sum>i<n. ?d i * vy i)"
      proof -
        have "(\<Sum>i<n. ?d i * vy i) = ?d 0 * vy 0 + (\<Sum>i\<in>{..<n}-{0}. ?d i * vy i)"
          using hn1 by (intro sum.remove) auto
        also have "(\<Sum>i\<in>{..<n}-{0}. ?d i * vy i) = 0"
          by (rule sum.neutral) (by100 simp)
        finally show ?thesis by (by100 simp)
      qed
    qed
    hence hpn_ne: "\<exists>p'. p' \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}" by (by100 blast)
    then obtain x0 y0 where hxy0: "(x0, y0) \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}" by (by100 blast)
    have "(1::real, (x0, y0)) \<in> {0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      using hxy0 by auto
    moreover have "q = (case (1::real, (x0, y0)) of (t, x', y') \<Rightarrow>
        ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))"
      using hq hx_vn hy_vn by (by100 simp)
    ultimately show ?thesis by (by100 blast)
  next
    case htnot1: False
    have hlt1: "?t < 1" using htnot1 ht1 by (by100 linarith)
    hence h1mt: "1 - ?t > 0" by (by100 linarith)
    let ?c' = "\<lambda>i. c i / (1 - ?t)"
    have hc'_nn: "\<forall>i<n. ?c' i \<ge> 0" using hc(1) h1mt by (by100 force)
    have hc'_sum: "(\<Sum>i<n. ?c' i) = 1"
    proof -
      have "(\<Sum>i<n. ?c' i) = (\<Sum>i<n. c i) / (1 - ?t)"
        by (simp add: sum_divide_distrib)
      also have "(\<Sum>i<n. c i) = 1 - ?t" using hc(2) by simp
      finally show ?thesis using h1mt by simp
    qed
    let ?x' = "\<Sum>i<n. ?c' i * vx i"
    let ?y' = "\<Sum>i<n. ?c' i * vy i"
    have hrescale_x: "(1-?t)*?x' = (\<Sum>i<n. c i * vx i)"
    proof -
      have "(1-?t)*?x' = (\<Sum>i<n. (1-?t) * (?c' i * vx i))"
        by (simp add: sum_distrib_left)
      also have "\<dots> = (\<Sum>i<n. c i * vx i)"
        using h1mt by (intro sum.cong) (simp_all add: field_simps)
      finally show ?thesis .
    qed
    have hrescale_y: "(1-?t)*?y' = (\<Sum>i<n. c i * vy i)"
    proof -
      have "(1-?t)*?y' = (\<Sum>i<n. (1-?t) * (?c' i * vy i))"
        by (simp add: sum_distrib_left)
      also have "\<dots> = (\<Sum>i<n. c i * vy i)"
        using h1mt by (intro sum.cong) (simp_all add: field_simps)
      finally show ?thesis .
    qed
    have hx_eq: "x = (1-?t)*?x' + ?t*vx n" using hc(3) hrescale_x by simp
    have hy_eq: "y = (1-?t)*?y' + ?t*vy n" using hc(4) hrescale_y by simp
    have "(?x', ?y') \<in> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      apply simp
      apply (rule_tac x="?c'" in exI)
      using hc'_nn hc'_sum by (by100 auto)
    have ht_in: "?t \<in> {0..1}" using ht0 ht1 by (by100 auto)
    hence "(?t, (?x', ?y')) \<in> {0..1} \<times> {(x, y). \<exists>c. (\<forall>i<n. c i \<ge> 0) \<and> (\<Sum>i<n. c i) = 1
        \<and> x = (\<Sum>i<n. c i * vx i) \<and> y = (\<Sum>i<n. c i * vy i)}"
      using \<open>(?x', ?y') \<in> _\<close> by (by100 blast)
    moreover have "q = (case (?t, (?x', ?y')) of (t, x', y') \<Rightarrow>
        ((1-t)*x'+t*vx n, (1-t)*y'+t*vy n))"
      using hq hx_eq hy_eq by (by100 simp)
    ultimately show ?thesis by (by100 blast)
  qed
qed

text \<open>A convex hull of n \<ge> 3 points in R^2 is compact.\<close>
text \<open>Convex hull of n \<ge> 1 points is compact, by induction on n.
  Base: single point. Step: conv(n+1) = image of [0,1] \<times> conv(n) under continuous cone map.\<close>
lemma convex_hull_compact_general:
  fixes vx vy :: "nat \<Rightarrow> real" and n :: nat
  assumes "n \<ge> 1"
  shows "compact {(x, y). \<exists>coeffs. (\<forall>i<n. (coeffs i :: real) \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
      \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
  using assms
proof (induction n rule: nat_induct_at_least)
  case base
  \<comment> \<open>n=1: P = {(vx 0, vy 0)}, a single point — trivially compact.\<close>
  have "{(x::real, y::real). \<exists>coeffs. (\<forall>i<1. coeffs i \<ge> 0) \<and> (\<Sum>i<1. coeffs i) = 1
      \<and> x = (\<Sum>i<1. coeffs i * vx i) \<and> y = (\<Sum>i<1. coeffs i * vy i)}
    = {(vx 0, vy 0)}"
  proof
    show "{(vx 0, vy 0)} \<subseteq> {(x, y). \<exists>coeffs. (\<forall>i<1. coeffs i \<ge> 0) \<and>
        (\<Sum>i<1. coeffs i) = 1 \<and> x = (\<Sum>i<1. coeffs i * vx i) \<and> y = (\<Sum>i<1. coeffs i * vy i)}"
      by (rule subsetI) (auto intro: exI[of _ "\<lambda>_. 1"])
  next
    show "{(x, y). \<exists>coeffs. (\<forall>i<1. coeffs i \<ge> 0) \<and> (\<Sum>i<1. coeffs i) = 1 \<and>
        x = (\<Sum>i<1. coeffs i * vx i) \<and> y = (\<Sum>i<1. coeffs i * vy i)} \<subseteq> {(vx 0, vy 0)}"
      by auto
  qed
  moreover have "compact {(vx 0, vy 0)}"
  proof (rule compactI)
    fix \<U> :: "(real \<times> real) set set"
    assume "\<forall>U\<in>\<U>. open U" "{(vx 0, vy 0)} \<subseteq> \<Union>\<U>"
    then obtain U where "U \<in> \<U>" "(vx 0, vy 0) \<in> U" by (by100 blast)
    thus "\<exists>\<F>\<subseteq>\<U>. finite \<F> \<and> {(vx 0, vy 0)} \<subseteq> \<Union>\<F>"
      by (rule_tac x="{U}" in exI) (by100 blast)
  qed
  ultimately show ?case by (by100 simp)
next
  case (Suc n)
  \<comment> \<open>Inductive step: conv(n+1 points) = cone from v_n over conv(n points).
     (x,y) \<in> conv(n+1) iff \<exists>t\<in>[0,1]. \<exists>(x',y')\<in>conv(n).
       x = (1-t)*x' + t*vx(n)  and  y = (1-t)*y' + t*vy(n).
     This is the image of [0,1] \<times> conv(n) under a continuous map.\<close>
  let ?Pn = "{(x::real, y::real). \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
      \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
  let ?Pn1 = "{(x::real, y::real). \<exists>coeffs. (\<forall>i<Suc n. coeffs i \<ge> 0) \<and> (\<Sum>i<Suc n. coeffs i) = 1
      \<and> x = (\<Sum>i<Suc n. coeffs i * vx i) \<and> y = (\<Sum>i<Suc n. coeffs i * vy i)}"
  have hPn_compact: "compact ?Pn" by (rule Suc.IH)
  \<comment> \<open>f: [0,1] \<times> ?Pn \<rightarrow> ?Pn1 via f(t, (x',y')) = ((1-t)*x' + t*vx n, (1-t)*y' + t*vy n).\<close>
  let ?f = "\<lambda>(t::real, (x'::real, y'::real)). ((1-t)*x' + t*vx n, (1-t)*y' + t*vy n)"
  \<comment> \<open>[0,1] \<times> ?Pn is compact.\<close>
  have hdom_compact: "compact ({0..1::real} \<times> ?Pn)"
    by (rule compact_Times_general[OF compact_Icc hPn_compact])
  \<comment> \<open>?f is continuous.\<close>
  have hf_cont: "continuous_on ({0..1} \<times> ?Pn) ?f"
  proof -
    have "continuous_on UNIV ?f"
      unfolding split_def
      by (intro continuous_on_Pair continuous_on_add continuous_on_mult continuous_on_id
          continuous_on_diff continuous_on_fst continuous_on_snd continuous_on_const)
    thus ?thesis by (rule continuous_on_subset) (by100 blast)
  qed
  \<comment> \<open>?Pn1 = ?f ` ({0..1} \<times> ?Pn).\<close>
  have hPn1_eq: "?Pn1 = ?f ` ({0..1} \<times> ?Pn)"
    by (rule equalityI[OF convex_hull_cone_sub[OF Suc(1)] convex_hull_cone_sup])
  show ?case unfolding hPn1_eq
    by (rule compact_continuous_image[OF hf_cont hdom_compact])
qed

lemma convex_hull_compact:
  fixes vx vy :: "nat \<Rightarrow> real" and n :: nat
  assumes "n \<ge> 3"
  shows "compact {(x, y). \<exists>coeffs. (\<forall>i<n. (coeffs i :: real) \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
      \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
  using convex_hull_compact_general[of n vx vy] assms by (by100 linarith)

\<comment> \<open>Strict polygonal quotient: all scheme properties + no extra identifications.
   Uses a SINGLE set of existentials (scheme, P, q, vx, vy) to avoid witness matching.\<close>
definition top1_is_polygonal_quotient_strict_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_polygonal_quotient_strict_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     (\<exists>(scheme :: (nat \<times> bool) list) P q (vx::nat\<Rightarrow>real) (vy::nat\<Rightarrow>real).
        top1_is_polygonal_region_on P (length scheme)
      \<and> top1_quotient_map_on P
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q
      \<and> (\<forall>i<length scheme. \<forall>j<length scheme. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j))
      \<and> (\<forall>i<length scheme. (vx i, vy i) \<in> P)
      \<and> (\<forall>i<length scheme. \<forall>j<length scheme.
            fst (scheme!i) = fst (scheme!j) \<longrightarrow>
            (\<forall>t\<in>I_set.
               q ((1-t) * vx i + t * vx (Suc i mod length scheme),
                  (1-t) * vy i + t * vy (Suc i mod length scheme))
             = (if snd (scheme!i) = snd (scheme!j)
                then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                        (1-t) * vy j + t * vy (Suc j mod length scheme))
                else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                        t * vy j + (1-t) * vy (Suc j mod length scheme)))))
      \<and> (\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
                    p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                          (1-t) * vy i + t * vy (Suc i mod length scheme)))
               \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p'))
      \<and> (\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
            q ((1-t) * vx i + t * vx (Suc i mod length scheme),
               (1-t) * vy i + t * vy (Suc i mod length scheme))
          = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
               (1-s) * vy j + s * vy (Suc j mod length scheme))
          \<longrightarrow> (i = j \<and> t = s)
            \<or> (fst (scheme!i) = fst (scheme!j) \<and>
               (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))))"

\<comment> \<open>Richer extraction from scheme: gives vertices, edge identification, interior singleton fibers.\<close>
lemma quotient_of_scheme_extract_full:
  assumes "top1_quotient_of_scheme_on X TX scheme"
  obtains P q vx vy where
    "top1_is_polygonal_region_on P (length scheme)"
    "top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q"
    "length scheme \<ge> 3"
    "\<forall>i<length scheme. (vx i, vy i) \<in> P"
    "P = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<length scheme. coeffs i) = 1
                       \<and> x = (\<Sum>i<length scheme. coeffs i * vx i)
                       \<and> y = (\<Sum>i<length scheme. coeffs i * vy i)}"
    "\<forall>i<length scheme. \<forall>j<length scheme.
        fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set.
           q ((1-t) * vx i + t * vx (Suc i mod length scheme),
              (1-t) * vy i + t * vy (Suc i mod length scheme))
         = (if snd (scheme!i) = snd (scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                    (1-t) * vy j + t * vy (Suc j mod length scheme))
            else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                    t * vy j + (1-t) * vy (Suc j mod length scheme))))"
    "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
              p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                    (1-t) * vy i + t * vy (Suc i mod length scheme)))
         \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
    "\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
              q ((1-t) * vx i + t * vx (Suc i mod length scheme),
                 (1-t) * vy i + t * vy (Suc i mod length scheme))
            = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
                 (1-s) * vy j + s * vy (Suc j mod length scheme))
            \<longrightarrow> (i = j \<and> t = s)
              \<or> (fst (scheme!i) = fst (scheme!j) \<and>
                 (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
    "\<forall>i<length scheme. let cx = (\<Sum>j<length scheme. vx j) / real (length scheme);
                            cy = (\<Sum>j<length scheme. vy j) / real (length scheme)
         in (vx i - cx) * (vy (Suc i mod length scheme) - cy)
          - (vy i - cy) * (vx (Suc i mod length scheme) - cx) > 0"
proof -
  from assms obtain P q vx vy where
    h1: "top1_is_polygonal_region_on P (length scheme)" and
    h2: "top1_quotient_map_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q" and
    h3: "\<forall>i<length scheme. (vx i, vy i) \<in> P" and
    h8: "P = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<length scheme. coeffs i) = 1
                       \<and> x = (\<Sum>i<length scheme. coeffs i * vx i)
                       \<and> y = (\<Sum>i<length scheme. coeffs i * vy i)}" and
    h4: "\<forall>i<length scheme. \<forall>j<length scheme.
        fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
            (1-t) * vy i + t * vy (Suc i mod length scheme))
         = (if snd (scheme!i) = snd (scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                    (1-t) * vy j + t * vy (Suc j mod length scheme))
            else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                    t * vy j + (1-t) * vy (Suc j mod length scheme))))" and
    h5: "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
          p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme)))
       \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')" and
    h7: "\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
              q ((1-t) * vx i + t * vx (Suc i mod length scheme),
                 (1-t) * vy i + t * vy (Suc i mod length scheme))
            = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
                 (1-s) * vy j + s * vy (Suc j mod length scheme))
            \<longrightarrow> (i = j \<and> t = s)
              \<or> (fst (scheme!i) = fst (scheme!j) \<and>
                 (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))" and
    h9: "\<forall>i<length scheme. let cx = (\<Sum>j<length scheme. vx j) / real (length scheme);
                               cy = (\<Sum>j<length scheme. vy j) / real (length scheme)
         in (vx i - cx) * (vy (Suc i mod length scheme) - cy)
          - (vy i - cy) * (vx (Suc i mod length scheme) - cx) > 0"
    using assms unfolding top1_quotient_of_scheme_on_def
    by (elim conjE exE) (rule that, assumption+)
  have h6: "length scheme \<ge> 3"
    using h1 unfolding top1_is_polygonal_region_on_def by (by100 blast)
  show ?thesis by (rule that[OF h1 h2 h6 h3 h8 h4 h5 h7 h9])
qed

\<comment> \<open>Note: quotient\_strict\_extract was removed because automation can't handle the
   50+ atom obtains formula. The "no extra identifications" condition has a proof gap
   directly in Theorem\_74\_1 instead. The top1\_is\_polygonal\_quotient\_strict\_on
   definition remains available for future use if the automation issue is resolved.\<close>

(** from \<S>74 Theorem 74.1: polygonal quotients are compact Hausdorff **)
theorem Theorem_74_1_polygon_quotient_compact_hausdorff:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "is_topology_on_strict X TX"
  and "top1_is_polygonal_quotient_on X TX"
  shows "top1_compact_on X TX \<and> is_hausdorff_on X TX"
proof -
  \<comment> \<open>Munkres 74.1: The polygonal region P is compact (closed bounded subset of R^2).
     The quotient map q: P \<rightarrow> X is continuous and surjective.
     Compact: q(P) = X is compact (continuous image of compact).
     Hausdorff: the quotient identifications are on the boundary only;
     use the finite edge-identification structure to verify the T2 axiom.\<close>
  \<comment> \<open>Extract scheme + P + q + vx + vy from the (non-strict) polygonal quotient definition.\<close>
  have "\<exists>scheme :: (nat \<times> bool) list. top1_quotient_of_scheme_on X TX scheme"
    using assms(2) unfolding top1_is_polygonal_quotient_on_def by (by100 blast)
  then obtain scheme :: "(nat \<times> bool) list" where hsch: "top1_quotient_of_scheme_on X TX scheme"
    by (by100 auto)
  obtain P q vx vy where
      hP_full: "top1_is_polygonal_region_on P (length scheme)"
      and hq_full: "top1_quotient_map_on P
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q"
      and hlen_full: "length scheme \<ge> 3"
      and hvert_full: "\<forall>i<length scheme. (vx i, vy i) \<in> P"
      and hP_hull_full: "P = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<length scheme. coeffs i) = 1
                       \<and> x = (\<Sum>i<length scheme. coeffs i * vx i)
                       \<and> y = (\<Sum>i<length scheme. coeffs i * vy i)}"
      and hedge_full: "\<forall>i<length scheme. \<forall>j<length scheme. fst (scheme!i) = fst (scheme!j) \<longrightarrow>
          (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
              (1-t) * vy i + t * vy (Suc i mod length scheme))
           = (if snd (scheme!i) = snd (scheme!j)
              then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                      (1-t) * vy j + t * vy (Suc j mod length scheme))
              else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                      t * vy j + (1-t) * vy (Suc j mod length scheme))))"
      and hinterior_full: "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
              p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                    (1-t) * vy i + t * vy (Suc i mod length scheme)))
           \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
      and hno_extra_full: "\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
              q ((1-t) * vx i + t * vx (Suc i mod length scheme),
                 (1-t) * vy i + t * vy (Suc i mod length scheme))
            = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
                 (1-s) * vy j + s * vy (Suc j mod length scheme))
            \<longrightarrow> (i = j \<and> t = s)
              \<or> (fst (scheme!i) = fst (scheme!j) \<and>
                 (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
    by (rule quotient_of_scheme_extract_full[OF hsch])
  have hcompact: "top1_compact_on X TX"
  proof -
    let ?TP_c = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
    \<comment> \<open>Reuse P, q from the extraction above.\<close>
    have hP: "top1_is_polygonal_region_on P (length scheme)" by (rule hP_full)
    have hq: "top1_quotient_map_on P ?TP_c X TX q" by (rule hq_full)
    let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
    \<comment> \<open>Step 1: P is compact (convex hull of finitely many points in R^2).\<close>
    have hP_compact: "top1_compact_on P ?TP"
    proof -
      \<comment> \<open>Bridge: product_topology_on top1_open_sets top1_open_sets = top1_open_sets for R^2.\<close>
      have hTP_eq: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
        using product_topology_on_open_sets_real2 by (by100 simp)
      \<comment> \<open>By bridge lemma: top1_compact_on P (subspace UNIV open P) \<longleftrightarrow> compact P.\<close>
      have "top1_compact_on P (subspace_topology UNIV top1_open_sets P) \<longleftrightarrow> compact P"
        by (rule top1_compact_on_subspace_UNIV_iff_compact)
      \<comment> \<open>Need: compact P (polygonal region is compact in R^2).
         P is a closed bounded convex hull, hence compact.\<close>
      moreover have "compact P"
      proof -
        \<comment> \<open>P is the convex hull of finitely many points.
           P = union of n-2 triangles (fan triangulation from vertex 0).
           Each triangle is compact (continuous image of compact [0,1]^2).
           Finite union of compact is compact.\<close>
        obtain vx vy :: "nat \<Rightarrow> real" where hn: "length scheme \<ge> 3"
            and hP_eq: "P = {(x, y). \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                \<and> (\<Sum>i<length scheme. coeffs i) = 1
                \<and> x = (\<Sum>i<length scheme. coeffs i * vx i)
                \<and> y = (\<Sum>i<length scheme. coeffs i * vy i)}"
          using hP unfolding top1_is_polygonal_region_on_def by blast
        show "compact P" unfolding hP_eq by (rule convex_hull_compact[OF hn])
      qed
      ultimately have "top1_compact_on P (subspace_topology UNIV top1_open_sets P)" by (by100 simp)
      thus ?thesis using hTP_eq by (by100 simp)
    qed
    \<comment> \<open>Step 2: q is continuous (from quotient map).\<close>
    have hq_cont: "top1_continuous_map_on P ?TP X TX q"
      using hq unfolding top1_quotient_map_on_def by (by100 blast)
    \<comment> \<open>Step 3: q is surjective (from quotient map).\<close>
    have hq_surj: "q ` P = X"
      using hq unfolding top1_quotient_map_on_def by (by100 blast)
    \<comment> \<open>Step 4: X = q(P) is compact (continuous image of compact).\<close>
    have hTX_top: "is_topology_on X TX"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have "top1_compact_on (q ` P) (subspace_topology X TX (q ` P))"
      by (rule top1_compact_on_continuous_image[OF hP_compact hTX_top hq_cont])
    hence "top1_compact_on X (subspace_topology X TX X)" using hq_surj by (by100 simp)
    moreover have "subspace_topology X TX X = TX"
    proof -
      have "\<forall>U\<in>TX. U \<subseteq> X" using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
      thus ?thesis by (rule subspace_topology_self)
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Hausdorff: P is a subspace of R^2 (Hausdorff). The quotient identifies
     finitely many boundary pairs. Prove via: P Hausdorff \<Rightarrow> closed map \<Rightarrow> Hausdorff quotient.\<close>
  have hhausdorff: "is_hausdorff_on X TX"
  proof -
    \<comment> \<open>Reuse P, q, vx, vy, scheme from the outer extraction.\<close>
    have hP_loc: "top1_is_polygonal_region_on P (length scheme)" by (rule hP_full)
    have hq_loc: "top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q"
      by (rule hq_full)
    have hlen_loc: "length scheme \<ge> 3" by (rule hlen_full)
    have hvert_loc: "\<forall>i<length scheme. (vx i, vy i) \<in> P" by (rule hvert_full)
    have hedge_loc: "\<forall>i<length scheme. \<forall>j<length scheme. fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
            (1-t) * vy i + t * vy (Suc i mod length scheme))
         = (if snd (scheme!i) = snd (scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                    (1-t) * vy j + t * vy (Suc j mod length scheme))
            else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                    t * vy j + (1-t) * vy (Suc j mod length scheme))))"
      by (rule hedge_full)
    have hinterior_loc: "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
          p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme)))
       \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
      by (rule hinterior_full)
    have hno_extra: "\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
          q ((1-t) * vx i + t * vx (Suc i mod length scheme),
             (1-t) * vy i + t * vy (Suc i mod length scheme))
        = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
             (1-s) * vy j + s * vy (Suc j mod length scheme))
        \<longrightarrow> (i = j \<and> t = s)
          \<or> (fst (scheme!i) = fst (scheme!j) \<and>
             (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
      by (rule hno_extra_full)
    let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
    \<comment> \<open>Step 1: R^2 is Hausdorff.\<close>
    have hR_haus: "is_hausdorff_on (UNIV::real set) top1_open_sets"
      by (rule top1_R_is_hausdorff)
    have hR2_prod_haus: "\<And>X1 T1 X2 T2. is_hausdorff_on X1 T1 \<Longrightarrow> is_hausdorff_on X2 T2 \<Longrightarrow>
        is_hausdorff_on (X1 \<times> X2) (product_topology_on T1 T2)"
      using Theorem_17_11 by (by100 blast)
    have hR2_sub_haus: "\<And>X T Y. is_hausdorff_on X T \<Longrightarrow> Y \<subseteq> X \<Longrightarrow>
        is_hausdorff_on Y (subspace_topology X T Y)"
      using Theorem_17_11 by (by100 blast)
    have hR2_haus: "is_hausdorff_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      by (rule hR2_prod_haus[OF hR_haus hR_haus, simplified])
    have hP_haus: "is_hausdorff_on P ?TP"
      by (rule hR2_sub_haus[OF hR2_haus]) (by100 blast)
    \<comment> \<open>Step 2: The full Hausdorff argument for the quotient.\<close>
    \<comment> \<open>The equivalence relation R = {(a,b)\<in>P\<times>P | q a = q b} is closed in P\<times>P.
       For polygonal quotients: R is a finite union of pairs of boundary segments,
       each compact (continuous image of [0,1]), hence closed.
       Closed R on compact Hausdorff P \<Rightarrow> P/R Hausdorff.\<close>
    have hR_closed: "closedin_on (P \<times> P)
        (product_topology_on ?TP ?TP)
        {(a, b). a \<in> P \<and> b \<in> P \<and> q a = q b}"
    proof -
      let ?n = "length scheme"
      let ?R = "{(a, b). a \<in> P \<and> b \<in> P \<and> q a = q b}"
      \<comment> \<open>Define boundary: the union of all edges.\<close>
      let ?edge = "\<lambda>i t. ((1-t) * vx i + t * vx (Suc i mod ?n),
                          (1-t) * vy i + t * vy (Suc i mod ?n))"
      let ?bdy = "\<Union>i\<in>{..<length scheme}. ?edge i ` I_set"
      \<comment> \<open>Interior points have singleton q-fibers (from hinterior\_loc).\<close>
      \<comment> \<open>So R \<subseteq> diagonal \<union> (?bdy \<times> ?bdy).\<close>
      have hR_sub: "?R \<subseteq> {(a, b). a \<in> P \<and> b \<in> P \<and> a = b} \<union> (?bdy \<times> ?bdy)"
      proof
        fix x assume "x \<in> ?R"
        then obtain a b where hx: "x = (a, b)" "a \<in> P" "b \<in> P" "q a = q b"
          by (cases x) (by100 blast)
        show "x \<in> {(a, b). a \<in> P \<and> b \<in> P \<and> a = b} \<union> (?bdy \<times> ?bdy)"
        proof (cases "a = b")
          case True thus ?thesis using hx by (by100 blast)
        next
          case False
          have "a \<in> ?bdy"
          proof (rule ccontr)
            assume "a \<notin> ?bdy"
            hence "\<forall>i<length scheme. \<forall>t\<in>I_set. a \<noteq> ?edge i t" by (by100 blast)
            from hinterior_loc hx(2) this hx(3) hx(4)
            have "a = b" by (by100 blast)
            thus False using False by (by100 simp)
          qed
          have "b \<in> ?bdy"
          proof (rule ccontr)
            assume "b \<notin> ?bdy"
            hence "\<forall>i<length scheme. \<forall>t\<in>I_set. b \<noteq> ?edge i t" by (by100 blast)
            from hinterior_loc hx(3) this hx(2) hx(4)[symmetric]
            have "b = a" by (by100 blast)
            thus False using False by (by100 simp)
          qed
          from \<open>a \<in> ?bdy\<close> \<open>b \<in> ?bdy\<close> show ?thesis using hx(1) by (by100 blast)
        qed
      qed
      \<comment> \<open>The diagonal is closed (P\<times>P Hausdorff, equalizer of pi1, pi2).\<close>
      have hPP_haus: "is_hausdorff_on (P \<times> P) (product_topology_on ?TP ?TP)"
        using hR2_prod_haus[OF hP_haus hP_haus] .
      have hTP_top: "is_topology_on P ?TP"
        using hP_haus unfolding is_hausdorff_on_def by (by100 blast)
      have hTPP: "is_topology_on (P \<times> P) (product_topology_on ?TP ?TP)"
        by (rule product_topology_on_is_topology_on[OF hTP_top hTP_top])
      have hpi1_cont: "top1_continuous_map_on (P \<times> P) (product_topology_on ?TP ?TP) P ?TP pi1"
        by (rule top1_continuous_pi1[OF hTP_top hTP_top])
      have hpi2_cont: "top1_continuous_map_on (P \<times> P) (product_topology_on ?TP ?TP) P ?TP pi2"
        by (rule top1_continuous_pi2[OF hTP_top hTP_top])
      have hDiag_eq: "{(a, b). a \<in> P \<and> b \<in> P \<and> a = b}
          = {x \<in> P \<times> P. pi1 x = pi2 x}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {(a, b). a \<in> P \<and> b \<in> P \<and> a = b}"
        then obtain a b where "x = (a, b)" "a \<in> P" "b \<in> P" "a = b" by (by100 blast)
        thus "x \<in> {x \<in> P \<times> P. pi1 x = pi2 x}" unfolding pi1_def pi2_def by (by100 simp)
      next
        fix x assume "x \<in> {x \<in> P \<times> P. pi1 x = pi2 x}"
        hence "x \<in> P \<times> P" "pi1 x = pi2 x" by (by100 blast)+
        then obtain a b where "x = (a, b)" "a \<in> P" "b \<in> P" by (by100 blast)
        have "a = b" using \<open>pi1 x = pi2 x\<close> \<open>x = (a, b)\<close> unfolding pi1_def pi2_def by (by100 simp)
        thus "x \<in> {(a, b). a \<in> P \<and> b \<in> P \<and> a = b}" using \<open>a \<in> P\<close> \<open>b \<in> P\<close> \<open>x = (a, b)\<close> by (by100 blast)
      qed
      have hDiag_closed: "closedin_on (P \<times> P) (product_topology_on ?TP ?TP)
          {(a, b). a \<in> P \<and> b \<in> P \<and> a = b}"
      proof -
        have "closedin_on (P \<times> P) (product_topology_on ?TP ?TP)
            {x \<in> P \<times> P. pi1 x = pi2 x}"
          by (rule top1_closedin_equalizer_of_continuous_maps[OF hTPP hP_haus hpi1_cont hpi2_cont])
        thus ?thesis using hDiag_eq by (by100 simp)
      qed
      \<comment> \<open>?bdy \<times> ?bdy is compact (each edge is compact image of [0,1],
         finite union of compact = compact, product of compact = compact).\<close>
      \<comment> \<open>Boundary compact: each edge is compact image of [0,1], finite union compact.\<close>
      \<comment> \<open>P is compact (polygonal region = convex hull).\<close>
      have hP_compact_here: "top1_compact_on P ?TP"
      proof -
        have hTP_eq: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
          using product_topology_on_open_sets_real2 by (by100 simp)
        have "compact P"
        proof -
          obtain vx' vy' :: "nat \<Rightarrow> real" where hn': "length scheme \<ge> 3"
              and hP_eq: "P = {(x, y). \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                  \<and> (\<Sum>i<length scheme. coeffs i) = 1
                  \<and> x = (\<Sum>i<length scheme. coeffs i * vx' i)
                  \<and> y = (\<Sum>i<length scheme. coeffs i * vy' i)}"
            using hP_loc unfolding top1_is_polygonal_region_on_def by blast
          show "compact P" unfolding hP_eq by (rule convex_hull_compact[OF hn'])
        qed
        hence "top1_compact_on P (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets P)"
          using iffD2[OF top1_compact_on_subspace_UNIV_iff_compact] by (by100 blast)
        thus ?thesis using hTP_eq by (by100 simp)
      qed
      have hbdy_sub_P: "?bdy \<subseteq> P"
      proof
        fix x assume "x \<in> ?bdy"
        then obtain i t where hi: "i < length scheme" "t \<in> I_set" "x = ?edge i t"
          by (by100 blast)
        have ht: "t \<ge> 0" "t \<le> 1" using \<open>t \<in> I_set\<close> unfolding top1_unit_interval_def
          by (by100 simp)+
        have hvi: "(vx i, vy i) \<in> P" using hvert_loc hi(1) by (by100 blast)
        have hj: "Suc i mod length scheme < length scheme"
        proof -
          have "length scheme > 0" using hlen_loc by (by100 linarith)
          thus ?thesis by (by100 simp)
        qed
        have hvi1: "(vx (Suc i mod length scheme), vy (Suc i mod length scheme)) \<in> P"
          using hvert_loc hj by (by100 blast)
        \<comment> \<open>P is convex hull: (1-t)*v_i + t*v_{i+1} is in P for t \<in> [0,1].\<close>
        show "x \<in> P"
        proof -
          \<comment> \<open>Define coefficients: all zero except i and (i+1 mod n).\<close>
          obtain vx' vy' where hP_eq: "P = {(x, y). \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
              \<and> (\<Sum>i<length scheme. coeffs i) = 1
              \<and> x = (\<Sum>i<length scheme. coeffs i * vx' i)
              \<and> y = (\<Sum>i<length scheme. coeffs i * vy' i)}"
            using hP_loc unfolding top1_is_polygonal_region_on_def by blast
          \<comment> \<open>From hvi and hvi1: vertices are in P, so the edge point is too.\<close>
          \<comment> \<open>v_i and v_{i+1} are in P (convex hull). P is convex, so
             (1-t)*v_i + t*v_{i+1} \<in> P. Proof: combine coefficients.\<close>
          from hvi obtain c1 where hc1: "\<forall>j<length scheme. c1 j \<ge> 0"
              "(\<Sum>j<length scheme. c1 j) = 1"
              "fst (vx i, vy i) = (\<Sum>j<length scheme. c1 j * vx' j)"
              "snd (vx i, vy i) = (\<Sum>j<length scheme. c1 j * vy' j)"
            unfolding hP_eq by auto
          from hvi1 obtain c2 where hc2: "\<forall>j<length scheme. c2 j \<ge> 0"
              "(\<Sum>j<length scheme. c2 j) = 1"
              "fst (vx (Suc i mod length scheme), vy (Suc i mod length scheme)) = (\<Sum>j<length scheme. c2 j * vx' j)"
              "snd (vx (Suc i mod length scheme), vy (Suc i mod length scheme)) = (\<Sum>j<length scheme. c2 j * vy' j)"
            unfolding hP_eq by auto
          let ?c = "\<lambda>j. (1-t) * c1 j + t * c2 j"
          have hc_nn: "\<forall>j<length scheme. ?c j \<ge> 0"
          proof (intro allI impI)
            fix j assume "j < length scheme"
            have "c1 j \<ge> 0" using hc1(1) \<open>j < length scheme\<close> by (by100 blast)
            have "c2 j \<ge> 0" using hc2(1) \<open>j < length scheme\<close> by (by100 blast)
            show "?c j \<ge> 0" using \<open>c1 j \<ge> 0\<close> \<open>c2 j \<ge> 0\<close> ht by (by100 simp)
          qed
          have hc_sum: "(\<Sum>j<length scheme. ?c j) = 1"
          proof -
            have "(\<Sum>j<length scheme. ?c j) = (\<Sum>j<length scheme. (1-t) * c1 j) + (\<Sum>j<length scheme. t * c2 j)"
              by (simp add: sum.distrib)
            also have "\<dots> = (1-t) * (\<Sum>j<length scheme. c1 j) + t * (\<Sum>j<length scheme. c2 j)"
              by (simp add: sum_distrib_left)
            finally show ?thesis using hc1(2) hc2(2) ht by (by100 simp)
          qed
          have hc_x: "fst (?edge i t) = (\<Sum>j<length scheme. ?c j * vx' j)"
          proof -
            have "(\<Sum>j<length scheme. ?c j * vx' j) =
                (\<Sum>j<length scheme. (1-t) * c1 j * vx' j) + (\<Sum>j<length scheme. t * c2 j * vx' j)"
              by (simp add: sum.distrib ring_distribs)
            also have "\<dots> = (1-t) * (\<Sum>j<length scheme. c1 j * vx' j) + t * (\<Sum>j<length scheme. c2 j * vx' j)"
              by (simp add: sum_distrib_left mult.assoc)
            finally show ?thesis using hc1(3) hc2(3) by (by100 simp)
          qed
          have hc_y: "snd (?edge i t) = (\<Sum>j<length scheme. ?c j * vy' j)"
          proof -
            have "(\<Sum>j<length scheme. ?c j * vy' j) =
                (\<Sum>j<length scheme. (1-t) * c1 j * vy' j) + (\<Sum>j<length scheme. t * c2 j * vy' j)"
              by (simp add: sum.distrib ring_distribs)
            also have "\<dots> = (1-t) * (\<Sum>j<length scheme. c1 j * vy' j) + t * (\<Sum>j<length scheme. c2 j * vy' j)"
              by (simp add: sum_distrib_left mult.assoc)
            finally show ?thesis using hc1(4) hc2(4) by (by100 simp)
          qed
          show ?thesis unfolding hP_eq hi(3)
            using hc_nn hc_sum hc_x hc_y by auto
        qed
      qed
      have hbdy_closed_P: "closedin_on P ?TP ?bdy"
      proof -
        \<comment> \<open>Each edge is compact in R^2 (continuous image of [0,1]).\<close>
        have "compact ?bdy"
        proof -
          have "\<forall>i \<in> {..<length scheme}. compact (?edge i ` I_set)"
          proof (intro ballI)
            fix i assume "i \<in> {..<length scheme}"
            let ?f = "\<lambda>t::real. ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme))"
            have "continuous_on UNIV ?f" by (intro continuous_intros)
            hence "continuous_on I_set ?f"
              using continuous_on_subset by (by100 blast)
            moreover have "compact I_set"
              unfolding top1_unit_interval_def by (by100 simp)
            ultimately have "compact (?f ` I_set)" by (rule compact_continuous_image)
            moreover have "?f ` I_set = ?edge i ` I_set" by (by100 simp)
            ultimately show "compact (?edge i ` I_set)" by (by100 simp)
          qed
          moreover have "finite {..<length scheme}" by (by100 simp)
          ultimately show "compact ?bdy"
          proof -
            assume hcomp: "\<forall>i \<in> {..<length scheme}. compact (?edge i ` I_set)"
            assume hfin: "finite {..<length scheme}"
            show ?thesis
              unfolding UN_simps
              apply (rule compact_Union)
              apply (rule finite_imageI[OF hfin])
              using hcomp by (by100 blast)
          qed
        qed
        \<comment> \<open>compact in Hausdorff P \<Rightarrow> closed in P.\<close>
        have "top1_compact_on ?bdy (subspace_topology P ?TP ?bdy)"
        proof -
          have hTP_eq: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
            using product_topology_on_open_sets_real2 by (by100 simp)
          have "top1_compact_on ?bdy (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets ?bdy)"
            using iffD2[OF top1_compact_on_subspace_UNIV_iff_compact] \<open>compact ?bdy\<close> by (by100 blast)
          moreover have "subspace_topology (UNIV::(real\<times>real) set) top1_open_sets ?bdy
              = subspace_topology P ?TP ?bdy"
          proof -
            have "subspace_topology P (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets P) ?bdy
                = subspace_topology (UNIV::(real\<times>real) set) top1_open_sets ?bdy"
              by (rule subspace_topology_trans[OF hbdy_sub_P])
            thus ?thesis using hTP_eq by (by100 simp)
          qed
          ultimately show ?thesis by simp
        qed
        thus ?thesis
          by (rule Theorem_26_3[OF hP_haus hbdy_sub_P])
      qed
      have hbdy_compact_P: "top1_compact_on ?bdy (subspace_topology P ?TP ?bdy)"
        by (rule Theorem_26_2[OF hP_compact_here hbdy_closed_P])
      have hbdy_compact: "top1_compact_on (?bdy \<times> ?bdy)
          (subspace_topology (P \<times> P) (product_topology_on ?TP ?TP) (?bdy \<times> ?bdy))"
      proof -
        have "top1_compact_on (?bdy \<times> ?bdy)
            (product_topology_on (subspace_topology P ?TP ?bdy) (subspace_topology P ?TP ?bdy))"
          by (rule Theorem_26_7[OF hbdy_compact_P hbdy_compact_P])
        moreover have "product_topology_on (subspace_topology P ?TP ?bdy) (subspace_topology P ?TP ?bdy)
            = subspace_topology (P \<times> P) (product_topology_on ?TP ?TP) (?bdy \<times> ?bdy)"
          by (rule Theorem_16_3[OF hTP_top hTP_top])
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>?R \<inter> (?bdy \<times> ?bdy) is compact: it's a finite union of edge-pair identification
         sets, each compact (image of [0,1] under continuous map t \<mapsto> (edge\_i(t), edge\_j(f(t)))).\<close>
      have hR_bdy_compact: "top1_compact_on (?R \<inter> (?bdy \<times> ?bdy))
          (subspace_topology (P \<times> P) (product_topology_on ?TP ?TP) (?R \<inter> (?bdy \<times> ?bdy)))"
      proof -
        \<comment> \<open>Step 1: compact ?bdy in HOL-Analysis.\<close>
        have hbdy_compact_HA: "compact ?bdy"
        proof -
          have "\<forall>i \<in> {..<length scheme}. compact (?edge i ` I_set)"
          proof (intro ballI)
            fix i assume "i \<in> {..<length scheme}"
            let ?f = "\<lambda>t::real. ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme))"
            have "continuous_on UNIV ?f" by (intro continuous_intros)
            hence "continuous_on I_set ?f" using continuous_on_subset by (by100 blast)
            moreover have "compact I_set" unfolding top1_unit_interval_def by (by100 simp)
            ultimately have "compact (?f ` I_set)" by (rule compact_continuous_image)
            moreover have "?f ` I_set = ?edge i ` I_set" by (by100 simp)
            ultimately show "compact (?edge i ` I_set)" by (by100 simp)
          qed
          hence hcomp_all: "\<forall>S \<in> (\<lambda>i. ?edge i ` I_set) ` {..<length scheme}. compact S" by (by100 blast)
          have hfin_set: "finite ((\<lambda>i. ?edge i ` I_set) ` {..<length scheme})" by (by100 simp)
          have "compact (\<Union> ((\<lambda>i. ?edge i ` I_set) ` {..<length scheme}))"
            by (rule compact_Union[OF hfin_set hcomp_all])
          moreover have "\<Union> ((\<lambda>i. ?edge i ` I_set) ` {..<length scheme}) = ?bdy" by (by100 auto)
          ultimately show "compact ?bdy" by (by100 simp)
        qed
        \<comment> \<open>Step 2: compact (bdy \<times> bdy) via compact\_Times\_general.\<close>
        have hbdybdy_compact_HA: "compact (?bdy \<times> ?bdy)"
          by (rule compact_Times_general[OF hbdy_compact_HA hbdy_compact_HA])
        \<comment> \<open>Step 3: R \<inter> bdy\<times>bdy \<subseteq> bdy\<times>bdy, and bdy\<times>bdy is compact,
           so R\<inter>bdy\<times>bdy is bounded. Need closedness to get compactness.\<close>
        \<comment> \<open>Alternative: show R\<inter>bdy\<times>bdy is ITSELF a finite union of compact sets.\<close>
        have "compact (?R \<inter> (?bdy \<times> ?bdy))"
        proof -
          \<comment> \<open>R\<inter>bdy\<times>bdy \<subseteq> diagonal\_on\_bdy \<union> edge\_pair\_curves.\<close>
          \<comment> \<open>Each curve is compact (continuous image of compact [0,1]).\<close>
          \<comment> \<open>Diagonal on bdy: image of bdy under x\<mapsto>(x,x). Compact.\<close>
          let ?D = "(\<lambda>x. (x, x)) ` ?bdy"
          have hD_compact: "compact ?D"
          proof -
            have "continuous_on ?bdy (\<lambda>x. (x, x))" by (intro continuous_intros)
            thus ?thesis using compact_continuous_image hbdy_compact_HA by (by100 blast)
          qed
          \<comment> \<open>Edge pair curves: for each (i,j) with same label.\<close>
          \<comment> \<open>?R \<inter> (?bdy \<times> ?bdy) \<subseteq> ?D \<union> (edge pair curves). Plus reverse.\<close>
          \<comment> \<open>Since both directions need the scheme structure,\<close>
          \<comment> \<open>we show R\<inter>bdy\<times>bdy is closed in the compact bdy\<times>bdy.\<close>
          \<comment> \<open>R\<inter>bdy\<times>bdy closed: equal to ?D \<union> finite union of compact sets.\<close>
          \<comment> \<open>?D compact \<Rightarrow> closed (in Hausdorff R^4). Each edge pair compact \<Rightarrow> closed.\<close>
          \<comment> \<open>Finite union of closed = closed. Closed subset of compact = compact.\<close>
          have hR_bdy_closed_HA: "closed (?R \<inter> (?bdy \<times> ?bdy))"
          proof -
            \<comment> \<open>R\<inter>bdy\<times>bdy = D \<union> \<Union>{C\_ij | same label}.\<close>
            \<comment> \<open>D = diagonal on bdy (compact \<Rightarrow> closed). Each C\_ij compact \<Rightarrow> closed.\<close>
            \<comment> \<open>Finite union of closed = closed.\<close>
            \<comment> \<open>Define edge pair curves.\<close>
            let ?n = "length scheme"
            let ?curves = "(\<lambda>(i,j). if fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j
                then (if snd (scheme!i) = snd (scheme!j)
                      then (\<lambda>t. (?edge i t, ?edge j t)) ` I_set
                      else (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set)
                else {}) ` ({..<?n} \<times> {..<?n})"
            \<comment> \<open>R\<inter>bdy\<times>bdy \<subseteq> ?D \<union> \<Union>?curves.\<close>
            have hR_bdy_sub_DC: "?R \<inter> (?bdy \<times> ?bdy) \<subseteq> ?D \<union> \<Union>?curves"
            proof
              fix x assume "x \<in> ?R \<inter> (?bdy \<times> ?bdy)"
              then obtain a b where hx: "x = (a, b)" "a \<in> P" "b \<in> P" "q a = q b"
                  "a \<in> ?bdy" "b \<in> ?bdy"
                by (cases x) (by100 blast)
              \<comment> \<open>a on some edge i at parameter t, b on edge j at parameter s.\<close>
              from hx(5) obtain i t where hi: "i < length scheme" "t \<in> I_set" "a = ?edge i t"
                by (by100 blast)
              from hx(6) obtain j s where hj: "j < length scheme" "s \<in> I_set" "b = ?edge j s"
                by (by100 blast)
              \<comment> \<open>Apply hno\_extra: q(edge\_i(t)) = q(edge\_j(s)) \<Rightarrow> diagonal or scheme pair.\<close>
              from hno_extra[rule_format, OF hi(1) hj(1) hi(2) hj(2)]
              have "q a = q b \<longrightarrow> (i = j \<and> t = s) \<or> (fst (scheme!i) = fst (scheme!j) \<and>
                  (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
                using hi(3) hj(3) by simp
              hence "(i = j \<and> t = s) \<or> (fst (scheme!i) = fst (scheme!j) \<and>
                  (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
                using hx(4) by (by100 blast)
              thus "x \<in> ?D \<union> \<Union>?curves"
              proof
                assume "i = j \<and> t = s"
                hence "a = b" using hi(3) hj(3) by (by100 simp)
                thus ?thesis using hx(1,5) by (by100 blast)
              next
                assume hpair: "fst (scheme!i) = fst (scheme!j) \<and>
                    (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t)"
                show ?thesis
                proof (cases "i = j")
                  case True
                  hence "t = s" using hpair by (by100 auto)
                  hence "a = b" using hi(3) hj(3) True by (by100 simp)
                  thus ?thesis using hx(1,5) by (by100 blast)
                next
                  case False
                  \<comment> \<open>(a,b) is on an edge pair curve.\<close>
                  \<comment> \<open>(a,b) = (edge\_i(t), edge\_j(s)) with same label and s = f(t).\<close>
                  have "fst (scheme!i) = fst (scheme!j)" using hpair by (by100 blast)
                  show ?thesis
                  proof (cases "snd (scheme!i) = snd (scheme!j)")
                    case True
                    hence "s = t" using hpair by (by100 auto)
                    hence "x = (?edge i t, ?edge j t)" using hx(1) hi(3) hj(3) by (by100 simp)
                    hence "x \<in> (\<lambda>t. (?edge i t, ?edge j t)) ` I_set" using hi(2) by auto
                    moreover have "(\<lambda>t. (?edge i t, ?edge j t)) ` I_set \<in> ?curves"
                    proof -
                      have "(i, j) \<in> {..<length scheme} \<times> {..<length scheme}"
                        using hi(1) hj(1) by (by100 blast)
                      moreover have "(case (i, j) of (i, j) \<Rightarrow>
                          if fst (scheme ! i) = fst (scheme ! j) \<and> i \<noteq> j
                          then (if snd (scheme ! i) = snd (scheme ! j)
                                then (\<lambda>t. (?edge i t, ?edge j t)) ` I_set
                                else (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set)
                          else {}) = (\<lambda>t. (?edge i t, ?edge j t)) ` I_set"
                        using \<open>fst (scheme!i) = fst (scheme!j)\<close> False True by (by100 simp)
                      ultimately show ?thesis
                        apply -
                        apply (rule image_eqI[where x="(i,j)"])
                        apply (by100 simp)
                        apply (by100 blast)
                        done
                    qed
                    hence "x \<in> \<Union>?curves" using \<open>x \<in> (\<lambda>t. (?edge i t, ?edge j t)) ` I_set\<close>
                      by blast
                    thus ?thesis by blast
                  next
                    case sndF: False
                    hence "s = 1 - t" using hpair by (by100 auto)
                    hence "x = (?edge i t, ?edge j (1-t))" using hx(1) hi(3) hj(3) by simp
                    hence hx_in: "x \<in> (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set" using hi(2) by auto
                    have "(\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set \<in> ?curves"
                    proof -
                      have "(i, j) \<in> {..<length scheme} \<times> {..<length scheme}"
                        using hi(1) hj(1) by (by100 blast)
                      moreover have "(case (i, j) of (i, j) \<Rightarrow>
                          if fst (scheme ! i) = fst (scheme ! j) \<and> i \<noteq> j
                          then (if snd (scheme ! i) = snd (scheme ! j)
                                then (\<lambda>t. (?edge i t, ?edge j t)) ` I_set
                                else (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set)
                          else {}) = (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set"
                        using \<open>fst (scheme!i) = fst (scheme!j)\<close> False sndF by (by100 simp)
                      ultimately show ?thesis
                        apply -
                        apply (rule image_eqI[where x="(i,j)"])
                        apply (by100 simp)
                        apply (by100 blast)
                        done
                    qed
                    hence "x \<in> \<Union>?curves" using hx_in by blast
                    thus ?thesis by blast
                  qed
                qed
              qed
            qed
            \<comment> \<open>?D \<union> \<Union>?curves \<subseteq> ?R \<inter> (?bdy\<times>?bdy).\<close>
            have hDC_sub_R_bdy: "?D \<union> \<Union>?curves \<subseteq> ?R \<inter> (?bdy \<times> ?bdy)"
            proof
              fix x assume "x \<in> ?D \<union> \<Union>?curves"
              thus "x \<in> ?R \<inter> (?bdy \<times> ?bdy)"
              proof
                \<comment> \<open>Case 1: x \<in> ?D (diagonal on boundary).\<close>
                assume "x \<in> ?D"
                then obtain a where ha: "a \<in> ?bdy" "x = (a, a)" by (by100 blast)
                have "a \<in> P" using ha(1) hbdy_sub_P by (by100 blast)
                thus "x \<in> ?R \<inter> (?bdy \<times> ?bdy)" using ha by (by100 blast)
              next
                \<comment> \<open>Case 2: x \<in> \<Union>?curves (edge pair curve).\<close>
                assume "x \<in> \<Union>?curves"
                then obtain C where "C \<in> ?curves" "x \<in> C" by (by100 blast)
                then obtain i j where hij: "i < ?n" "j < ?n"
                    "C = (if fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j
                          then (if snd (scheme!i) = snd (scheme!j)
                                then (\<lambda>t. (?edge i t, ?edge j t)) ` I_set
                                else (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set)
                          else {})" by auto
                show "x \<in> ?R \<inter> (?bdy \<times> ?bdy)"
                proof (cases "fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j")
                  case False thus ?thesis using \<open>x \<in> C\<close> hij(3) by auto
                next
                  case True
                  hence hsamelabel: "fst (scheme!i) = fst (scheme!j)" by (by100 blast)
                  show ?thesis
                  proof (cases "snd (scheme!i) = snd (scheme!j)")
                    case True
                    \<comment> \<open>Same direction: x = (edge\_i(t), edge\_j(t)).\<close>
                    then obtain t where ht: "t \<in> I_set" "x = (?edge i t, ?edge j t)"
                      using \<open>x \<in> C\<close> hij(3) \<open>fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j\<close> by auto
                    have "q (?edge i t) = q (?edge j t)"
                    proof -
                      have "\<forall>t\<in>I_set. q (?edge i t) =
                          (if snd (scheme!i) = snd (scheme!j) then q (?edge j t) else q (?edge j (1-t)))"
                      proof (intro ballI)
                        fix t assume "t \<in> I_set"
                        show "q (?edge i t) = (if snd (scheme!i) = snd (scheme!j) then q (?edge j t) else q (?edge j (1-t)))"
                          using hedge_loc[rule_format, OF hij(1) hij(2) hsamelabel \<open>t \<in> I_set\<close>] by simp
                      qed
                      thus ?thesis using True ht(1) by (by100 simp)
                    qed
                    moreover have hei: "?edge i t \<in> ?bdy" using hij(1) ht(1) by (by100 blast)
                    moreover have hej: "?edge j t \<in> ?bdy" using hij(2) ht(1) by (by100 blast)
                    moreover have "?edge i t \<in> P" using subsetD[OF hbdy_sub_P hei] .
                    moreover have "?edge j t \<in> P" using subsetD[OF hbdy_sub_P hej] .
                    ultimately show ?thesis using ht(2) by auto
                  next
                    case False
                    \<comment> \<open>Opposite direction: x = (edge\_i(t), edge\_j(1-t)).\<close>
                    then obtain t where ht: "t \<in> I_set" "x = (?edge i t, ?edge j (1-t))"
                      using \<open>x \<in> C\<close> hij(3) \<open>fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j\<close> by auto
                    have "q (?edge i t) = q (?edge j (1-t))"
                    proof -
                      have "\<forall>t\<in>I_set. q (?edge i t) =
                          (if snd (scheme!i) = snd (scheme!j) then q (?edge j t) else q (?edge j (1-t)))"
                      proof (intro ballI)
                        fix t assume "t \<in> I_set"
                        show "q (?edge i t) = (if snd (scheme!i) = snd (scheme!j) then q (?edge j t) else q (?edge j (1-t)))"
                          using hedge_loc[rule_format, OF hij(1) hij(2) hsamelabel \<open>t \<in> I_set\<close>] by simp
                      qed
                      thus ?thesis using False ht(1) by (by100 simp)
                    qed
                    moreover have hei2: "?edge i t \<in> ?bdy" using hij(1) ht(1) by (by100 blast)
                    moreover have h1t_I: "1 - t \<in> I_set" using ht(1) unfolding top1_unit_interval_def by auto
                    moreover have hej2: "?edge j (1-t) \<in> ?bdy" using hij(2) h1t_I by (by100 blast)
                    moreover have "?edge i t \<in> P" using subsetD[OF hbdy_sub_P hei2] .
                    moreover have "?edge j (1-t) \<in> P" using subsetD[OF hbdy_sub_P hej2] .
                    ultimately show ?thesis using ht(2) by auto
                  qed
                qed
              qed
            qed
            \<comment> \<open>So ?R \<inter> (?bdy \<times> ?bdy) = ?D \<union> \<Union>?curves.\<close>
            have hR_bdy_eq: "?R \<inter> (?bdy \<times> ?bdy) = ?D \<union> \<Union>?curves"
              using hR_bdy_sub_DC hDC_sub_R_bdy by (by100 blast)
            \<comment> \<open>?D is closed (compact \<Rightarrow> closed in R^4).\<close>
            have hD_closed: "closed ?D"
              using hD_compact compact_imp_closed by (by100 blast)
            \<comment> \<open>Each curve in ?curves is closed (compact \<Rightarrow> closed).\<close>
            have hcurves_closed: "\<forall>C \<in> ?curves. closed C"
            proof (intro ballI)
              fix C assume "C \<in> ?curves"
              then obtain i j where hij: "C = (if fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j
                  then (if snd (scheme!i) = snd (scheme!j)
                        then (\<lambda>t. (?edge i t, ?edge j t)) ` I_set
                        else (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set)
                  else {})" "i < ?n" "j < ?n" by auto
              show "closed C"
              proof (cases "fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j")
                case False thus ?thesis using hij(1) by auto
              next
                case True
                have "compact C"
                proof (cases "snd (scheme!i) = snd (scheme!j)")
                  case True
                  hence hC_eq: "C = (\<lambda>t. (?edge i t, ?edge j t)) ` I_set"
                    using hij(1) \<open>fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j\<close> by (by100 auto)
                  have "continuous_on UNIV (\<lambda>t::real. (?edge i t, ?edge j t))"
                    by (intro continuous_intros)
                  hence "continuous_on I_set (\<lambda>t. (?edge i t, ?edge j t))"
                    using continuous_on_subset by (by100 blast)
                  moreover have "compact I_set" unfolding top1_unit_interval_def by (by100 simp)
                  ultimately show ?thesis unfolding hC_eq by (rule compact_continuous_image)
                next
                  case False
                  hence hC_eq: "C = (\<lambda>t. (?edge i t, ?edge j (1-t))) ` I_set"
                    using hij(1) \<open>fst (scheme!i) = fst (scheme!j) \<and> i \<noteq> j\<close> by (by100 auto)
                  have "continuous_on UNIV (\<lambda>t::real. (?edge i t, ?edge j (1-t)))"
                    by (intro continuous_intros)
                  hence "continuous_on I_set (\<lambda>t. (?edge i t, ?edge j (1-t)))"
                    using continuous_on_subset by (by100 blast)
                  moreover have "compact I_set" unfolding top1_unit_interval_def by (by100 simp)
                  ultimately show ?thesis unfolding hC_eq by (rule compact_continuous_image)
                qed
                thus ?thesis using compact_imp_closed by (by100 blast)
              qed
            qed
            \<comment> \<open>Finite union of closed = closed.\<close>
            have "finite ?curves" by (by100 simp)
            have "closed (\<Union>?curves)"
              by (rule closed_Union[OF \<open>finite ?curves\<close> hcurves_closed])
            thus ?thesis using hR_bdy_eq hD_closed by auto
          qed
          from compact_Int_closed[OF hbdybdy_compact_HA hR_bdy_closed_HA]
          have "compact ((?bdy \<times> ?bdy) \<inter> (?R \<inter> (?bdy \<times> ?bdy)))" .
          moreover have "(?bdy \<times> ?bdy) \<inter> (?R \<inter> (?bdy \<times> ?bdy)) = ?R \<inter> (?bdy \<times> ?bdy)" by auto
          ultimately show "compact (?R \<inter> (?bdy \<times> ?bdy))" by simp
        qed
        \<comment> \<open>Step 4: Bridge compact to top1\_compact\_on.\<close>
        hence "top1_compact_on (?R \<inter> (?bdy \<times> ?bdy))
            (subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set)
                top1_open_sets (?R \<inter> (?bdy \<times> ?bdy)))"
          using iffD2[OF top1_compact_on_subspace_UNIV_iff_compact] by (by100 blast)
        moreover have "subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set)
            top1_open_sets (?R \<inter> (?bdy \<times> ?bdy))
            = subspace_topology (P \<times> P) (product_topology_on ?TP ?TP) (?R \<inter> (?bdy \<times> ?bdy))"
        proof -
          have hTP_eq: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
            using product_topology_on_open_sets_real2 by (by100 simp)
          have hTP_eq_sub: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
            using product_topology_on_open_sets_real2 by (by100 simp)
          have "product_topology_on ?TP ?TP =
              subspace_topology ((UNIV::(real\<times>real) set) \<times> (UNIV::(real\<times>real) set))
                  (product_topology_on top1_open_sets top1_open_sets) (P \<times> P)"
          proof -
            have hT_R2: "is_topology_on (UNIV::(real\<times>real) set) top1_open_sets"
              by (rule top1_open_sets_is_topology_on_UNIV)
            show ?thesis using Theorem_16_3[OF hT_R2 hT_R2] hTP_eq_sub by simp
          qed
          also have "subspace_topology ((UNIV::(real\<times>real) set) \<times> (UNIV::(real\<times>real) set))
                  (product_topology_on top1_open_sets top1_open_sets) (P \<times> P)
              = subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set) top1_open_sets (P \<times> P)"
          proof -
            have h1: "(UNIV::(real\<times>real) set) \<times> (UNIV::(real\<times>real) set) = (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set)"
              by (by100 simp)
            have h2: "product_topology_on (top1_open_sets::(real\<times>real) set set) (top1_open_sets::(real\<times>real) set set)
                = (top1_open_sets :: ((real \<times> real) \<times> (real \<times> real)) set set)"
              by (rule product_topology_on_open_sets)
            show ?thesis using h1 h2 by (by100 simp)
          qed
          finally have hPP_eq: "product_topology_on ?TP ?TP =
              subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set) top1_open_sets (P \<times> P)" .
          have hR_bdy_sub_PP: "?R \<inter> (?bdy \<times> ?bdy) \<subseteq> P \<times> P" by (by100 blast)
          have "subspace_topology (P \<times> P) (product_topology_on ?TP ?TP) (?R \<inter> (?bdy \<times> ?bdy))
              = subspace_topology (P \<times> P)
                  (subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set) top1_open_sets (P \<times> P))
                  (?R \<inter> (?bdy \<times> ?bdy))"
            using hPP_eq by (by100 simp)
          also have "\<dots> = subspace_topology (UNIV :: ((real \<times> real) \<times> (real \<times> real)) set) top1_open_sets
              (?R \<inter> (?bdy \<times> ?bdy))"
            by (rule subspace_topology_trans[OF hR_bdy_sub_PP])
          finally show ?thesis by simp
        qed
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>Compact in Hausdorff is closed.\<close>
      have hR_bdy_sub: "?R \<inter> (?bdy \<times> ?bdy) \<subseteq> P \<times> P" by (by100 blast)
      have hR_bdy_closed: "closedin_on (P \<times> P) (product_topology_on ?TP ?TP) (?R \<inter> (?bdy \<times> ?bdy))"
        by (rule Theorem_26_3[OF hPP_haus hR_bdy_sub hR_bdy_compact])
      \<comment> \<open>R \<subseteq> diagonal \<union> (?bdy \<times> ?bdy), so R = (R \<inter> diagonal) \<union> (R \<inter> (?bdy \<times> ?bdy)).
         R \<inter> diagonal = diagonal (on P\<times>P). Both parts closed. Union closed.\<close>
      have hR_decomp: "?R = {(a, b). a \<in> P \<and> b \<in> P \<and> a = b} \<union> (?R \<inter> (?bdy \<times> ?bdy))"
        using hR_sub by auto
      have "closedin_on (P \<times> P) (product_topology_on ?TP ?TP) ?R"
      proof -
        have "closedin_on (P \<times> P) (product_topology_on ?TP ?TP)
            ({(a, b). a \<in> P \<and> b \<in> P \<and> a = b} \<union> (?R \<inter> (?bdy \<times> ?bdy)))"
        proof -
          let ?F = "{{(a, b). a \<in> P \<and> b \<in> P \<and> a = b}, ?R \<inter> (?bdy \<times> ?bdy)}"
          have "finite ?F" by (by100 simp)
          have "\<forall>A \<in> ?F. closedin_on (P \<times> P) (product_topology_on ?TP ?TP) A"
            using hDiag_closed hR_bdy_closed by (by100 blast)
          from closedin_Union_finite[OF hTPP \<open>finite ?F\<close> this]
          have "closedin_on (P \<times> P) (product_topology_on ?TP ?TP) (\<Union>?F)" .
          moreover have "\<Union>?F = {(a, b). a \<in> P \<and> b \<in> P \<and> a = b} \<union> (?R \<inter> (?bdy \<times> ?bdy))"
            by (by100 simp)
          ultimately show ?thesis by auto
        qed
        thus ?thesis using hR_decomp by auto
      qed
      thus ?thesis .
    qed
    \<comment> \<open>Closed equivalence relation on compact Hausdorff \<Rightarrow> Hausdorff quotient.\<close>
    have hclosed_R_haus: "\<And>P' TP' X' TX' q'.
        is_hausdorff_on P' TP' \<Longrightarrow> top1_compact_on P' TP' \<Longrightarrow>
        top1_quotient_map_on P' TP' X' TX' q' \<Longrightarrow>
        closedin_on (P' \<times> P') (product_topology_on TP' TP')
            {(a, b). a \<in> P' \<and> b \<in> P' \<and> q' a = q' b} \<Longrightarrow>
        is_hausdorff_on X' TX'"
    proof -
      fix P' TP' X' TX' q'
      assume hP'H: "is_hausdorff_on P' TP'" and hP'C: "top1_compact_on P' TP'"
          and hq'Q: "top1_quotient_map_on P' TP' X' TX' q'"
          and hR'cl: "closedin_on (P' \<times> P') (product_topology_on TP' TP')
              {(a, b). a \<in> P' \<and> b \<in> P' \<and> q' a = q' b}"
      let ?R = "{(a, b). a \<in> P' \<and> b \<in> P' \<and> q' a = q' b}"
      have hTP': "is_topology_on P' TP'" using hP'H unfolding is_hausdorff_on_def by (by100 blast)
      have hTX': "is_topology_on X' TX'" using hq'Q unfolding top1_quotient_map_on_def by (by100 blast)
      have hq'_cont: "top1_continuous_map_on P' TP' X' TX' q'"
        using hq'Q unfolding top1_quotient_map_on_def by (by100 blast)
      have hq'_surj: "q' ` P' = X'" using hq'Q unfolding top1_quotient_map_on_def by (by100 blast)
      \<comment> \<open>P' compact Hausdorff \<Rightarrow> normal.\<close>
      have hP'N: "top1_normal_on P' TP'" by (rule Theorem_32_3[OF hP'C hP'H])
      show "is_hausdorff_on X' TX'" unfolding is_hausdorff_on_def
      proof (intro conjI)
        show "is_topology_on X' TX'" by (rule hTX')
      next
        show "\<forall>x\<in>X'. \<forall>y\<in>X'. x \<noteq> y \<longrightarrow>
            (\<exists>U V. neighborhood_of x X' TX' U \<and> neighborhood_of y X' TX' V \<and> U \<inter> V = {})"
        proof (intro ballI impI)
          fix x y assume "x \<in> X'" "y \<in> X'" "x \<noteq> y"
          let ?Fx = "{p \<in> P'. q' p = x}" and ?Fy = "{p \<in> P'. q' p = y}"
          \<comment> \<open>Fibers non-empty, closed, disjoint.\<close>
          have hFx_ne: "?Fx \<noteq> {}" using \<open>x \<in> X'\<close> hq'_surj by (by100 blast)
          have hFy_ne: "?Fy \<noteq> {}" using \<open>y \<in> X'\<close> hq'_surj by (by100 blast)
          have hFxy_disj: "?Fx \<inter> ?Fy = {}" using \<open>x \<noteq> y\<close> by (by100 blast)
          have hFx_cl: "closedin_on P' TP' ?Fx"
          proof -
            \<comment> \<open>Fx = {p | (p, p0) \<in> R} for any p0 \<in> Fx. Slice of closed R is closed.\<close>
            obtain p0 where "p0 \<in> P'" "q' p0 = x" using hFx_ne by (by100 blast)
            have hFx_eq: "?Fx = {p \<in> P'. (p, p0) \<in> ?R}"
            proof (rule set_eqI, rule iffI)
              fix p assume "p \<in> ?Fx"
              hence "p \<in> P'" "q' p = x" by (by100 blast)+
              hence "(p, p0) \<in> ?R" using \<open>p0 \<in> P'\<close> \<open>q' p0 = x\<close> by (by100 simp)
              thus "p \<in> {p \<in> P'. (p, p0) \<in> ?R}" using \<open>p \<in> P'\<close> by (by100 blast)
            next
              fix p assume "p \<in> {p \<in> P'. (p, p0) \<in> ?R}"
              hence "p \<in> P'" "(p, p0) \<in> ?R" by (by100 blast)+
              hence "q' p = q' p0" by (by100 simp)
              thus "p \<in> ?Fx" using \<open>p \<in> P'\<close> \<open>q' p0 = x\<close> by (by100 simp)
            qed
            \<comment> \<open>Slice of closed R at p0: {p\<in>P'|(p,p0)\<in>R} = preimage of R under i_{p0}.\<close>
            \<comment> \<open>i_{p0} continuous, R closed \<Rightarrow> preimage closed.\<close>
            have hTP'_prod: "is_topology_on (P' \<times> P') (product_topology_on TP' TP')"
              by (rule product_topology_on_is_topology_on[OF hTP' hTP'])
            have "closedin_on P' TP' {p \<in> P'. (\<lambda>p. (p, p0)) p \<in> ?R}"
            proof (rule continuous_preimage_closedin[OF hTP' hTP'_prod _ hR'cl])
              show "top1_continuous_map_on P' TP' (P' \<times> P') (product_topology_on TP' TP') (\<lambda>p. (p, p0))"
              proof -
                have hpi1: "top1_continuous_map_on P' TP' P' TP' (pi1 \<circ> (\<lambda>p. (p, p0)))"
                proof -
                  have heq: "pi1 \<circ> (\<lambda>p. (p, p0)) = id" unfolding pi1_def comp_def id_def by (by100 simp)
                  show ?thesis unfolding heq by (rule top1_continuous_map_on_id[OF hTP'])
                qed
                have hpi2: "top1_continuous_map_on P' TP' P' TP' (pi2 \<circ> (\<lambda>p. (p, p0)))"
                proof -
                  have heq2: "pi2 \<circ> (\<lambda>p. (p, p0)) = (\<lambda>_. p0)" unfolding pi2_def comp_def by (by100 simp)
                  have "top1_continuous_map_on P' TP' P' TP' (\<lambda>_. p0)"
                    using Theorem_18_2[OF hTP' hTP' hTP'] \<open>p0 \<in> P'\<close> by (by100 blast)
                  thus ?thesis unfolding heq2 .
                qed
                from iffD2[OF Theorem_18_4[OF hTP' hTP' hTP']] hpi1 hpi2
                show ?thesis by (by100 blast)
              qed
            qed
            moreover have "{p \<in> P'. (\<lambda>p. (p, p0)) p \<in> ?R} = {p \<in> P'. (p, p0) \<in> ?R}" by (by100 simp)
            ultimately have "closedin_on P' TP' {p \<in> P'. (p, p0) \<in> ?R}" by (by100 simp)
            thus ?thesis using hFx_eq by (by100 simp)
          qed
          have hFy_cl: "closedin_on P' TP' ?Fy"
          proof -
            obtain p0 where "p0 \<in> P'" "q' p0 = y" using hFy_ne by (by100 blast)
            have hFy_eq: "?Fy = {p \<in> P'. (p, p0) \<in> ?R}"
            proof (rule set_eqI, rule iffI)
              fix p assume "p \<in> ?Fy"
              hence "p \<in> P'" "q' p = y" by (by100 blast)+
              hence "(p, p0) \<in> ?R" using \<open>p0 \<in> P'\<close> \<open>q' p0 = y\<close> by (by100 simp)
              thus "p \<in> {p \<in> P'. (p, p0) \<in> ?R}" using \<open>p \<in> P'\<close> by (by100 blast)
            next
              fix p assume "p \<in> {p \<in> P'. (p, p0) \<in> ?R}"
              hence "p \<in> P'" "(p, p0) \<in> ?R" by (by100 blast)+
              hence "q' p = q' p0" by (by100 simp)
              thus "p \<in> ?Fy" using \<open>p \<in> P'\<close> \<open>q' p0 = y\<close> by (by100 simp)
            qed
            have hTP'_prod: "is_topology_on (P' \<times> P') (product_topology_on TP' TP')"
              by (rule product_topology_on_is_topology_on[OF hTP' hTP'])
            have "closedin_on P' TP' {p \<in> P'. (\<lambda>p. (p, p0)) p \<in> ?R}"
            proof (rule continuous_preimage_closedin[OF hTP' hTP'_prod _ hR'cl])
              show "top1_continuous_map_on P' TP' (P' \<times> P') (product_topology_on TP' TP') (\<lambda>p. (p, p0))"
              proof -
                have hpi1: "top1_continuous_map_on P' TP' P' TP' (pi1 \<circ> (\<lambda>p. (p, p0)))"
                proof -
                  have heq: "pi1 \<circ> (\<lambda>p. (p, p0)) = id" unfolding pi1_def comp_def id_def by (by100 simp)
                  show ?thesis unfolding heq by (rule top1_continuous_map_on_id[OF hTP'])
                qed
                have hpi2: "top1_continuous_map_on P' TP' P' TP' (pi2 \<circ> (\<lambda>p. (p, p0)))"
                proof -
                  have heq2: "pi2 \<circ> (\<lambda>p. (p, p0)) = (\<lambda>_. p0)" unfolding pi2_def comp_def by (by100 simp)
                  have "top1_continuous_map_on P' TP' P' TP' (\<lambda>_. p0)"
                    using Theorem_18_2[OF hTP' hTP' hTP'] \<open>p0 \<in> P'\<close> by (by100 blast)
                  thus ?thesis unfolding heq2 .
                qed
                from iffD2[OF Theorem_18_4[OF hTP' hTP' hTP']] hpi1 hpi2
                show ?thesis by (by100 blast)
              qed
            qed
            moreover have "{p \<in> P'. (\<lambda>p. (p, p0)) p \<in> ?R} = {p \<in> P'. (p, p0) \<in> ?R}" by (by100 simp)
            ultimately have "closedin_on P' TP' {p \<in> P'. (p, p0) \<in> ?R}" by (by100 simp)
            thus ?thesis using hFy_eq by (by100 simp)
          qed
          \<comment> \<open>By normality: disjoint open U \<supseteq> Fx, V \<supseteq> Fy.\<close>
          from normal_separation[OF hP'N hFx_cl hFy_cl hFxy_disj]
          obtain U V where hUV: "U \<in> TP'" "V \<in> TP'" "?Fx \<subseteq> U" "?Fy \<subseteq> V" "U \<inter> V = {}"
            by meson
          \<comment> \<open>Saturated complements: q'\<inverse>(q'(P'-U)) is closed (projection of closed from compact).\<close>
          let ?SU = "{p \<in> P'. \<exists>p' \<in> P' - U. q' p = q' p'}"
          let ?SV = "{p \<in> P'. \<exists>p' \<in> P' - V. q' p = q' p'}"
          \<comment> \<open>Projection of closed from compact is closed (tube lemma consequence).\<close>
          have hproj_closed: "\<And>C. closedin_on (P' \<times> P') (product_topology_on TP' TP') C \<Longrightarrow>
              closedin_on P' TP' {a \<in> P'. \<exists>b. (a, b) \<in> C}"
          proof -
            fix C assume hCcl: "closedin_on (P' \<times> P') (product_topology_on TP' TP') C"
            have hC_sub: "C \<subseteq> P' \<times> P'" using hCcl unfolding closedin_on_def by (by100 blast)
            have hprod_compact: "top1_compact_on (P' \<times> P') (product_topology_on TP' TP')"
              by (rule Theorem_26_7[OF hP'C hP'C])
            have hpi1_cont: "top1_continuous_map_on (P' \<times> P') (product_topology_on TP' TP') P' TP' pi1"
              by (rule top1_continuous_pi1[OF hTP' hTP'])
            have hpi1C_cl: "closedin_on P' TP' (pi1 ` C)"
              by (rule compact_hausdorff_continuous_closed_map[OF hprod_compact hP'H hpi1_cont hCcl])
            have hset_eq: "pi1 ` C = {a \<in> P'. \<exists>b. (a, b) \<in> C}"
            proof -
              have "\<And>a. a \<in> pi1 ` C \<Longrightarrow> a \<in> {a \<in> P'. \<exists>b. (a, b) \<in> C}"
              proof -
                fix a assume "a \<in> pi1 ` C"
                then obtain p where hp: "p \<in> C" "a = pi1 p" by (by100 blast)
                have "a = fst p" using hp(2) unfolding pi1_def by (by100 simp)
                have hp_mem: "p \<in> P' \<times> P'" using hp(1) hC_sub by (by100 blast)
                hence "fst p \<in> P'" using mem_Times_iff by (by100 blast)
                hence "a \<in> P'" using \<open>a = fst p\<close> by (by100 simp)
                have "p = (fst p, snd p)" by (by100 simp)
                hence "(a, snd p) \<in> C" using \<open>a = fst p\<close> hp(1) by (by100 simp)
                thus "a \<in> {a \<in> P'. \<exists>b. (a, b) \<in> C}" using \<open>a \<in> P'\<close> by (by100 blast)
              qed
              moreover have "\<And>a. a \<in> {a \<in> P'. \<exists>b. (a, b) \<in> C} \<Longrightarrow> a \<in> pi1 ` C"
              proof -
                fix a assume "a \<in> {a \<in> P'. \<exists>b. (a, b) \<in> C}"
                then obtain b where "a \<in> P'" "(a, b) \<in> C" by (by100 blast)
                have "a = pi1 (a, b)" unfolding pi1_def by (by100 simp)
                thus "a \<in> pi1 ` C" using \<open>(a, b) \<in> C\<close> by (by100 blast)
              qed
              ultimately show ?thesis by (by100 blast)
            qed
            show "closedin_on P' TP' {a \<in> P'. \<exists>b. (a, b) \<in> C}" using hpi1C_cl hset_eq by (by100 simp)
          qed
          have hTP'_prod2: "is_topology_on (P' \<times> P') (product_topology_on TP' TP')"
            by (rule product_topology_on_is_topology_on[OF hTP' hTP'])
          have hP'_in_TP': "P' \<in> TP'" using hTP' unfolding is_topology_on_def by (by100 blast)
          have hSU_closed: "closedin_on P' TP' ?SU"
          proof -
            have hPU_cl: "closedin_on P' TP' (P' - U)"
            proof (rule closedin_intro)
              show "P' - U \<subseteq> P'" by (by100 blast)
            next
              have "P' - (P' - U) = P' \<inter> U" by (by100 blast)
              moreover have "P' \<inter> U \<in> TP'" by (rule topology_inter2[OF hTP' hP'_in_TP' hUV(1)])
              ultimately show "P' - (P' - U) \<in> TP'" by (by100 simp)
            qed
            have hPxPU_cl: "closedin_on (P' \<times> P') (product_topology_on TP' TP') (P' \<times> (P' - U))"
            proof (rule closedin_intro)
              show "P' \<times> (P' - U) \<subseteq> P' \<times> P'" by (by100 blast)
            next
              have "(P' \<times> P') - (P' \<times> (P' - U)) = P' \<times> (P' \<inter> U)" by (by100 blast)
              moreover have "P' \<inter> U \<in> TP'" by (rule topology_inter2[OF hTP' hP'_in_TP' hUV(1)])
              moreover have "P' \<times> (P' \<inter> U) \<in> product_topology_on TP' TP'"
                by (rule product_rect_open[OF hP'_in_TP' \<open>P' \<inter> U \<in> TP'\<close>])
              ultimately show "(P' \<times> P') - (P' \<times> (P' - U)) \<in> product_topology_on TP' TP'" by (by100 simp)
            qed
            have hRC: "closedin_on (P' \<times> P') (product_topology_on TP' TP')
                (?R \<inter> (P' \<times> (P' - U)))"
              by (rule closedin_inter2[OF hTP'_prod2 hR'cl hPxPU_cl])
            have hSU_eq: "?SU = {a \<in> P'. \<exists>b. (a, b) \<in> ?R \<inter> (P' \<times> (P' - U))}"
              by (by100 blast)
            show ?thesis using hproj_closed[OF hRC] hSU_eq by (by100 simp)
          qed
          have hSV_closed: "closedin_on P' TP' ?SV"
          proof -
            have hPV_cl: "closedin_on P' TP' (P' - V)"
            proof (rule closedin_intro)
              show "P' - V \<subseteq> P'" by (by100 blast)
            next
              have "P' - (P' - V) = P' \<inter> V" by (by100 blast)
              moreover have "P' \<inter> V \<in> TP'" by (rule topology_inter2[OF hTP' hP'_in_TP' hUV(2)])
              ultimately show "P' - (P' - V) \<in> TP'" by (by100 simp)
            qed
            have hPxPV_cl: "closedin_on (P' \<times> P') (product_topology_on TP' TP') (P' \<times> (P' - V))"
            proof (rule closedin_intro)
              show "P' \<times> (P' - V) \<subseteq> P' \<times> P'" by (by100 blast)
            next
              have "(P' \<times> P') - (P' \<times> (P' - V)) = P' \<times> (P' \<inter> V)" by (by100 blast)
              moreover have "P' \<inter> V \<in> TP'" by (rule topology_inter2[OF hTP' hP'_in_TP' hUV(2)])
              moreover have "P' \<times> (P' \<inter> V) \<in> product_topology_on TP' TP'"
                by (rule product_rect_open[OF hP'_in_TP' \<open>P' \<inter> V \<in> TP'\<close>])
              ultimately show "(P' \<times> P') - (P' \<times> (P' - V)) \<in> product_topology_on TP' TP'" by (by100 simp)
            qed
            have hRC: "closedin_on (P' \<times> P') (product_topology_on TP' TP')
                (?R \<inter> (P' \<times> (P' - V)))"
              by (rule closedin_inter2[OF hTP'_prod2 hR'cl hPxPV_cl])
            have hSV_eq: "?SV = {a \<in> P'. \<exists>b. (a, b) \<in> ?R \<inter> (P' \<times> (P' - V))}"
              by (by100 blast)
            show ?thesis using hproj_closed[OF hRC] hSV_eq by (by100 simp)
          qed
          \<comment> \<open>P' - ?SU is open and saturated. q'(P' - ?SU) is open in X'.\<close>
          have hWx_open: "X' - q' ` (P' - U) \<in> TX'"
          proof -
            have "q' ` (P' - U) \<subseteq> X'" using hq'_surj by (by100 blast)
            have "closedin_on X' TX' (q' ` (P' - U))"
            proof -
              have "{p \<in> P'. q' p \<in> q' ` (P' - U)} = ?SU" by (by100 blast)
              hence "closedin_on P' TP' {p \<in> P'. q' p \<in> q' ` (P' - U)}"
                using hSU_closed by (by100 simp)
              thus ?thesis
                using top1_quotient_map_closed_iff_preimage_closed[OF hq'Q \<open>q' ` (P' - U) \<subseteq> X'\<close>]
                by (by100 blast)
            qed
            thus ?thesis using hTX' unfolding closedin_on_def by (by100 blast)
          qed
          have hWy_open: "X' - q' ` (P' - V) \<in> TX'"
          proof -
            have "q' ` (P' - V) \<subseteq> X'" using hq'_surj by (by100 blast)
            have "closedin_on X' TX' (q' ` (P' - V))"
            proof -
              have "{p \<in> P'. q' p \<in> q' ` (P' - V)} = ?SV" by (by100 blast)
              hence "closedin_on P' TP' {p \<in> P'. q' p \<in> q' ` (P' - V)}"
                using hSV_closed by (by100 simp)
              thus ?thesis
                using top1_quotient_map_closed_iff_preimage_closed[OF hq'Q \<open>q' ` (P' - V) \<subseteq> X'\<close>]
                by (by100 blast)
            qed
            thus ?thesis using hTX' unfolding closedin_on_def by (by100 blast)
          qed
          have hx_Wx: "x \<in> X' - q' ` (P' - U)"
          proof -
            have "x \<notin> q' ` (P' - U)"
            proof
              assume "x \<in> q' ` (P' - U)"
              then obtain p where "p \<in> P' - U" "q' p = x" by (by100 blast)
              hence "p \<in> ?Fx" by (by100 blast)
              hence "p \<in> U" using hUV(3) by (by100 blast)
              thus False using \<open>p \<in> P' - U\<close> by (by100 blast)
            qed
            thus ?thesis using \<open>x \<in> X'\<close> by (by100 blast)
          qed
          have hy_Wy: "y \<in> X' - q' ` (P' - V)"
          proof -
            have "y \<notin> q' ` (P' - V)"
            proof
              assume "y \<in> q' ` (P' - V)"
              then obtain p where "p \<in> P' - V" "q' p = y" by (by100 blast)
              hence "p \<in> ?Fy" by (by100 blast)
              hence "p \<in> V" using hUV(4) by (by100 blast)
              thus False using \<open>p \<in> P' - V\<close> by (by100 blast)
            qed
            thus ?thesis using \<open>y \<in> X'\<close> by (by100 blast)
          qed
          have hWxy_disj: "(X' - q' ` (P' - U)) \<inter> (X' - q' ` (P' - V)) = {}"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then obtain z where "z \<in> X'" "z \<notin> q' ` (P' - U)" "z \<notin> q' ` (P' - V)" by (by100 blast)
            hence "\<forall>p\<in>P'. q' p = z \<longrightarrow> p \<in> U" "\<forall>p\<in>P'. q' p = z \<longrightarrow> p \<in> V" by (by100 blast)+
            hence "\<forall>p\<in>P'. q' p = z \<longrightarrow> p \<in> U \<inter> V" by (by100 blast)
            hence "\<forall>p\<in>P'. q' p \<noteq> z" using hUV(5) by (by100 blast)
            hence "z \<notin> q' ` P'" by (by100 blast)
            thus False using \<open>z \<in> X'\<close> hq'_surj by (by100 blast)
          qed
          show "\<exists>U V. neighborhood_of x X' TX' U \<and> neighborhood_of y X' TX' V \<and> U \<inter> V = {}"
          proof (intro exI conjI)
            show "neighborhood_of x X' TX' (X' - q' ` (P' - U))"
              unfolding neighborhood_of_def using hWx_open hx_Wx by (by100 blast)
            show "neighborhood_of y X' TX' (X' - q' ` (P' - V))"
              unfolding neighborhood_of_def using hWy_open hy_Wy by (by100 blast)
            show "(X' - q' ` (P' - U)) \<inter> (X' - q' ` (P' - V)) = {}"
              by (rule hWxy_disj)
          qed
        qed
      qed
    qed
    have hP_compact_loc: "top1_compact_on P ?TP"
    proof -
      have hTP_eq: "?TP = subspace_topology (UNIV :: (real \<times> real) set) top1_open_sets P"
        using product_topology_on_open_sets_real2 by (by100 simp)
      have "compact P"
      proof -
        obtain vx vy :: "nat \<Rightarrow> real" where hn: "length scheme \<ge> 3"
            and hP_eq: "P = {(x, y). \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                \<and> (\<Sum>i<length scheme. coeffs i) = 1
                \<and> x = (\<Sum>i<length scheme. coeffs i * vx i)
                \<and> y = (\<Sum>i<length scheme. coeffs i * vy i)}"
          using hP_loc unfolding top1_is_polygonal_region_on_def by blast
        show "compact P" unfolding hP_eq by (rule convex_hull_compact[OF hn])
      qed
      hence "top1_compact_on P (subspace_topology (UNIV::((real\<times>real) set)) top1_open_sets P)"
        using top1_compact_on_subspace_UNIV_iff_compact by (by100 blast)
      thus ?thesis using hTP_eq by (by100 simp)
    qed
    show ?thesis
      by (rule hclosed_R_haus[OF hP_haus hP_compact_loc hq_loc hR_closed])
  qed
  show ?thesis using hcompact hhausdorff by (by100 blast)
qed

(** from \<S>74 Theorem 74.3: fundamental group of n-fold torus T_n has the
    presentation \<langle>a_1, b_1, \<dots>, a_n, b_n | [a_1,b_1]\<cdots>[a_n,b_n]\<rangle>.
    The single relator is the product (a_1 b_1 a_1\<inverse> b_1\<inverse>)\<cdots>(a_n b_n a_n\<inverse> b_n\<inverse>).
    We index generators 0, 1, ..., 2n-1 as a_i := 2i, b_i := 2i+1. **)

(** from \<S>74 Theorem 74.2: If P is a polygonal region with labelling scheme w,
    \<pi> maps all vertices to a single point x_0, and there are k distinct labels,
    then \<pi>_1(X, x_0) is the quotient of Free(k) by the normal closure of the relator.
    This is the general engine; 74.3 and 74.4 are immediate applications.
    Proof (book): A = \<pi>(Bd P) is a wedge of k circles (since all vertices identified).
    Theorem 72.1 gives \<pi>_1(X) \<cong> \<pi>_1(A)/N(relator). Then \<pi>_1(A) = Free(k). **)
text \<open>Helper: given CW data, free group iso, and Theorem 72.1 quotient,
  produce the group presentation. This factors out the relator identification
  step from Theorem 74.2 into a standalone lemma where proof blocks work.\<close>
text \<open>Helper: given a free group F \<cong> \<pi>_1(A), a quotient \<pi>_1(X) \<cong> \<pi>_1(A)/N(r),
  and a word w such that \<phi>^{-1}(r) = word\_product(\<iota>F, w),
  conclude that \<pi>_1(X) has presentation \<langle>S | w\<rangle>.\<close>
lemma presentation_from_free_quotient:
  fixes F :: "int set" and mulF :: "int \<Rightarrow> int \<Rightarrow> int" and eF :: int and invgF :: "int \<Rightarrow> int"
    and \<iota>F :: "'s \<Rightarrow> int" and S :: "'s set"
    and G :: "'g set" and mulG :: "'g \<Rightarrow> 'g \<Rightarrow> 'g" and eG :: 'g and invgG :: "'g \<Rightarrow> 'g"
    and H :: "'h set" and mulH :: "'h \<Rightarrow> 'h \<Rightarrow> 'h" and eH :: 'h and invgH :: "'h \<Rightarrow> 'h"
    and w :: "('s \<times> bool) list"
  assumes hF_free: "top1_is_free_group_full_on F mulF eF invgF \<iota>F S"
      and hG_grp: "top1_is_group_on G mulG eG invgG"
      and hH_grp: "top1_is_group_on H mulH eH invgH"
      and h\<phi>: "top1_group_iso_on F mulF G mulG \<phi>"
      and hproj_hom: "top1_group_hom_on G mulG Q mulQ proj"
      and hproj_surj: "proj ` G = Q"
      and hproj_ker: "top1_group_kernel_on G eQ proj = N"
      and hQ_grp: "top1_is_group_on Q mulQ eQ invgQ"
      and h\<psi>_iso: "top1_groups_isomorphic_on H mulH Q mulQ"
      and hrel_word: "inv_into F \<phi> r =
          top1_group_word_product mulF eF invgF (map (\<lambda>(s, b). (\<iota>F s, b)) w)"
      and hr_in: "r \<in> G"
      and hN_eq: "N = top1_normal_subgroup_generated_on G mulG eG invgG {r}"
      and hw_valid: "\<forall>i<length w. fst (w ! i) \<in> S"
  shows "top1_group_presented_by_on Q mulQ eQ invgQ S {w}
    \<and> top1_groups_isomorphic_on Q mulQ H mulH"
proof -
  \<comment> \<open>F --\<phi>--> G --proj--> Q \<cong> H.
     proj \<circ> \<phi>: F \<rightarrow> Q surjective hom.
     ker(proj \<circ> \<phi>) = \<phi>^{-1}(N) = \<phi>^{-1}(N\_G({r})) = N\_F({\<phi>^{-1}(r)}) = N\_F({word\_product}).
     So Q \<cong> F / N\_F({word\_product}) = presented group.
     And H \<cong> Q. So \<exists>G'. presented G' \<and> G' \<cong> H.\<close>
  \<comment> \<open>Step 1: proj \<circ> \<phi> is surjective hom.\<close>
  have h\<phi>_hom: "top1_group_hom_on F mulF G mulG \<phi>"
    using h\<phi> unfolding top1_group_iso_on_def by (by100 blast)
  have h\<phi>_bij: "bij_betw \<phi> F G"
    using h\<phi> unfolding top1_group_iso_on_def by (by100 blast)
  have hcomp_hom: "top1_group_hom_on F mulF Q mulQ (proj \<circ> \<phi>)"
    using group_hom_comp[OF h\<phi>_hom hproj_hom] .
  have hcomp_surj: "(proj \<circ> \<phi>) ` F = Q"
  proof -
    have "\<phi> ` F = G" using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
    thus ?thesis using hproj_surj image_image[of proj \<phi> F, symmetric] by (by100 simp)
  qed
  \<comment> \<open>Step 2: kernel.\<close>
  have hF_grp: "top1_is_group_on F mulF eF invgF"
    using hF_free unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hcomp_ker: "top1_group_kernel_on F eQ (proj \<circ> \<phi>) = {f \<in> F. \<phi> f \<in> N}"
  proof -
    have h\<phi>_img: "\<And>f. f \<in> F \<Longrightarrow> \<phi> f \<in> G" using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
    have hker_eq: "N = {g \<in> G. proj g = eQ}" using hproj_ker unfolding top1_group_kernel_on_def by (by100 simp)
    have "\<And>f. f \<in> F \<Longrightarrow> ((proj \<circ> \<phi>) f = eQ) = (\<phi> f \<in> N)"
    proof -
      fix f assume hf: "f \<in> F"
      have h\<phi>f: "\<phi> f \<in> G" using h\<phi>_img[OF hf] .
      have "(\<phi> f \<in> N) = (\<phi> f \<in> G \<and> proj (\<phi> f) = eQ)" using hker_eq by (by100 blast)
      also have "\<dots> = (proj (\<phi> f) = eQ)" using h\<phi>f by (by100 simp)
      also have "\<dots> = ((proj \<circ> \<phi>) f = eQ)" by (by100 simp)
      finally show "((proj \<circ> \<phi>) f = eQ) = (\<phi> f \<in> N)" by (by100 simp)
    qed
    thus ?thesis unfolding top1_group_kernel_on_def by (by100 blast)
  qed
  \<comment> \<open>Step 3: \<phi>^{-1}(N\_G({r})) = N\_F({\<phi>^{-1}(r)}).\<close>
  have hker_word: "top1_group_kernel_on F eQ (proj \<circ> \<phi>) =
      top1_normal_subgroup_generated_on F mulF eF invgF
        {top1_group_word_product mulF eF invgF (map (\<lambda>(s, b). (\<iota>F s, b)) w)}"
  proof -
    \<comment> \<open>From hcomp\_ker: kernel = {f \<in> F. \<phi> f \<in> N}.
       From hN\_eq: N = N\_G({r}).
       From hrel\_word: inv\_into F \<phi> r = word\_product.
       Need: {f \<in> F. \<phi> f \<in> N\_G({r})} = N\_F({word\_product}).
       Use inj\_hom\_preimage\_normal\_closure for \<subseteq> direction.\<close>
    define wp where "wp = top1_group_word_product mulF eF invgF (map (\<lambda>(s, b). (\<iota>F s, b)) w)"
    have hwp_eq: "wp = inv_into F \<phi> r" using hrel_word unfolding wp_def by (by100 simp)
    \<comment> \<open>\<subseteq>: if \<phi> f \<in> N\_G({r}) then f \<in> N\_F({wp}) using inj\_hom\_preimage\_normal\_closure.\<close>
    have hN_sub: "N \<subseteq> G"
    proof -
      have hr_sub: "{r} \<subseteq> G" using hr_in by (by100 blast)
      from normal_subgroup_generated_is_normal[OF hG_grp hr_sub]
      show ?thesis unfolding hN_eq top1_normal_subgroup_on_def by (by100 blast)
    qed
    have hr_in_N: "r \<in> N"
    proof -
      have "{r} \<subseteq> N" unfolding hN_eq top1_normal_subgroup_generated_on_def
        by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    have hsubset1: "{f \<in> F. \<phi> f \<in> N} \<subseteq>
        top1_normal_subgroup_generated_on F mulF eF invgF {wp}"
    proof (rule subsetI)
      fix c assume hc: "c \<in> {f \<in> F. \<phi> f \<in> N}"
      hence hcF: "c \<in> F" and h\<phi>c_N: "\<phi> c \<in> N" by (by100 blast)+
      from hN_eq have h\<phi>c: "\<phi> c \<in> top1_normal_subgroup_generated_on G mulG eG invgG {r}"
        using h\<phi>c_N by (by100 simp)
      have hwp_in_F: "wp \<in> F"
      proof -
        have "\<forall>i<length (map (\<lambda>(s, b). (\<iota>F s, b)) w).
            fst ((map (\<lambda>(s, b). (\<iota>F s, b)) w) ! i) \<in> F"
        proof (intro allI impI)
          fix i assume "i < length (map (\<lambda>(s, b). (\<iota>F s, b)) w)"
          hence hi: "i < length w" by (by100 simp)
          have "fst (w ! i) \<in> S" using hw_valid hi by (by100 blast)
          hence "\<iota>F (fst (w ! i)) \<in> F"
            using hF_free unfolding top1_is_free_group_full_on_def by (by100 blast)
          moreover have "(map (\<lambda>(s, b). (\<iota>F s, b)) w) ! i = (\<lambda>(s, b). (\<iota>F s, b)) (w ! i)"
            using nth_map[OF hi] by (by100 blast)
          ultimately show "fst ((map (\<lambda>(s, b). (\<iota>F s, b)) w) ! i) \<in> F"
            by (cases "w ! i") (by100 simp)
        qed
        thus ?thesis unfolding wp_def
          using word_product_in_group[OF hF_grp] by (by100 simp)
      qed
      have hN_F_normal: "top1_normal_subgroup_on F mulF eF invgF
          (top1_normal_subgroup_generated_on F mulF eF invgF {wp})"
        using normal_subgroup_generated_is_normal[OF hF_grp, of "{wp}"] hwp_in_F
        by (by100 blast)
      \<comment> \<open>Apply inj\_hom\_preimage\_normal\_closure.\<close>
      have h\<phi>_surj: "\<phi> ` F = G" using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
      have h\<phi>_inj: "inj_on \<phi> F" using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
      have hwp_in_NF: "wp \<in> top1_normal_subgroup_generated_on F mulF eF invgF {wp}"
        unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
      have h\<phi>wp: "\<phi> wp = r"
      proof -
        have "inv_into F \<phi> r = wp" using hwp_eq by (by100 simp)
        moreover have "r \<in> G" using hr_in .
        moreover have "r \<in> \<phi> ` F" using h\<phi>_surj \<open>r \<in> G\<close> by (by100 blast)
        ultimately have "\<phi> (inv_into F \<phi> r) = r"
          using f_inv_into_f[of r \<phi> F] by (by100 simp)
        thus ?thesis using \<open>inv_into F \<phi> r = wp\<close> by (by100 simp)
      qed
      have h\<phi>c_NG: "\<phi> c \<in> top1_normal_subgroup_generated_on G mulG eG invgG {\<phi> wp}"
        using h\<phi>c hN_eq h\<phi>wp by (by100 simp)
      show "c \<in> top1_normal_subgroup_generated_on F mulF eF invgF {wp}"
        using inj_hom_preimage_normal_closure[OF hF_grp hG_grp h\<phi>_hom h\<phi>_surj h\<phi>_inj
            hN_F_normal hwp_in_NF hcF h\<phi>c_NG] .
    qed
    \<comment> \<open>\<supseteq>: if f \<in> N\_F({wp}) then \<phi> f \<in> N\_G({r}).\<close>
    have hsubset2: "top1_normal_subgroup_generated_on F mulF eF invgF {wp} \<subseteq>
        {f \<in> F. \<phi> f \<in> N}"
    proof -
      have hN_normal: "top1_normal_subgroup_on G mulG eG invgG N"
        unfolding hN_eq
        using normal_subgroup_generated_is_normal[OF hG_grp, of "{r}"] hr_in
        by (by100 blast)
      have hK_normal: "top1_normal_subgroup_on F mulF eF invgF {f \<in> F. \<phi> f \<in> N}"
        using preimage_normal_subgroup[OF hF_grp hG_grp h\<phi>_hom hN_normal] .
      have hr_in_N: "r \<in> N" unfolding hN_eq top1_normal_subgroup_generated_on_def
      proof (rule InterI)
        fix X assume "X \<in> {Na. {r} \<subseteq> Na \<and> top1_normal_subgroup_on G mulG eG invgG Na}"
        thus "r \<in> X" by (by100 blast)
      qed
      have hwp_in_F: "wp \<in> F"
      proof -
        have "\<forall>i<length (map (\<lambda>(s, b). (\<iota>F s, b)) w).
            fst ((map (\<lambda>(s, b). (\<iota>F s, b)) w) ! i) \<in> F"
        proof (intro allI impI)
          fix i assume "i < length (map (\<lambda>(s, b). (\<iota>F s, b)) w)"
          hence hi: "i < length w" by (by100 simp)
          have "fst (w ! i) \<in> S" using hw_valid hi by (by100 blast)
          hence "\<iota>F (fst (w ! i)) \<in> F"
            using hF_free unfolding top1_is_free_group_full_on_def by (by100 blast)
          moreover have "(map (\<lambda>(s, b). (\<iota>F s, b)) w) ! i = (\<lambda>(s, b). (\<iota>F s, b)) (w ! i)"
            using nth_map[OF hi] by (by100 blast)
          ultimately show "fst ((map (\<lambda>(s, b). (\<iota>F s, b)) w) ! i) \<in> F"
            by (cases "w ! i") (by100 simp)
        qed
        thus ?thesis unfolding wp_def
          using word_product_in_group[OF hF_grp] by (by100 simp)
      qed
      have h\<phi>_surj2: "\<phi> ` F = G" using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
      have h\<phi>wp: "\<phi> wp = r"
      proof -
        have "inv_into F \<phi> r = wp" using hwp_eq by (by100 simp)
        moreover have "r \<in> G" using hr_in .
        moreover have "r \<in> \<phi> ` F" using h\<phi>_surj2 \<open>r \<in> G\<close> by (by100 blast)
        ultimately have "\<phi> (inv_into F \<phi> r) = r"
          using f_inv_into_f[of r \<phi> F] by (by100 simp)
        thus ?thesis using \<open>inv_into F \<phi> r = wp\<close> by (by100 simp)
      qed
      have hwp_in_K: "wp \<in> {f \<in> F. \<phi> f \<in> N}" using hwp_in_F h\<phi>wp hr_in_N by (by100 blast)
      have "{wp} \<subseteq> {f \<in> F. \<phi> f \<in> N}" using hwp_in_K by (by100 blast)
      thus ?thesis
        unfolding top1_normal_subgroup_generated_on_def
        using hK_normal by (by100 blast)
    qed
    have "{f \<in> F. \<phi> f \<in> N} = top1_normal_subgroup_generated_on F mulF eF invgF {wp}"
      using hsubset1 hsubset2 by (by100 blast)
    thus ?thesis using hcomp_ker hN_eq hrel_word unfolding wp_def by (by100 simp)
  qed
  \<comment> \<open>Step 4: Q is presented by (S, {w}).\<close>
  have hQ_presented: "top1_group_presented_by_on Q mulQ eQ invgQ S {w}"
  proof -
    have h1: "top1_is_free_group_full_on F mulF eF invgF \<iota>F S
      \<and> top1_group_hom_on F mulF Q mulQ (proj \<circ> \<phi>)
      \<and> (proj \<circ> \<phi>) ` F = Q
      \<and> top1_group_kernel_on F eQ (proj \<circ> \<phi>)
           = top1_normal_subgroup_generated_on F mulF eF invgF
               {r. \<exists>w'\<in>{w}. r = top1_group_word_product mulF eF invgF
                            (map (\<lambda>(s, b). (\<iota>F s, b)) w')}"
    proof -
      have "{r. \<exists>w'\<in>{w}. r = top1_group_word_product mulF eF invgF
                            (map (\<lambda>(s, b). (\<iota>F s, b)) w')}
        = {top1_group_word_product mulF eF invgF (map (\<lambda>(s, b). (\<iota>F s, b)) w)}"
        by (by100 blast)
      thus ?thesis using hF_free hcomp_hom hcomp_surj hker_word by (by5000 simp)
    qed
    show ?thesis
      unfolding top1_group_presented_by_on_def
      apply (rule conjI)
       apply (rule hQ_grp)
      apply (rule exI[of _ F])
      apply (rule exI[of _ mulF])
      apply (rule exI[of _ eF])
      apply (rule exI[of _ invgF])
      apply (rule exI[of _ \<iota>F])
      apply (rule exI[of _ "proj \<circ> \<phi>"])
      using h1 apply (by100 blast)
      done
  qed
  \<comment> \<open>Step 5: H \<cong> Q, so use Q as the witness.\<close>
  have hQ_iso_H: "top1_groups_isomorphic_on Q mulQ H mulH"
    using top1_groups_isomorphic_on_sym[OF h\<psi>_iso hH_grp hQ_grp] .
  have hconj: "top1_group_presented_by_on Q mulQ eQ invgQ S {w}
    \<and> top1_groups_isomorphic_on Q mulQ H mulH"
    using hQ_presented hQ_iso_H by (by100 blast)
  show ?thesis using hQ_presented hQ_iso_H by (by100 blast)
qed

lemma map_map_pair_compose:
  "map (\<lambda>(x, b). (f x, b)) (map (\<lambda>(s, b). (g s, b)) ws)
     = map (\<lambda>(s, b). (f (g s), b)) ws"
  by (induct ws) auto

text \<open>Re-indexing a free group: if free on S via \<iota> and f: S' \<rightarrow> S is bijective,
  then free on S' via \<iota> \<circ> f. Expert Step 5 helper.\<close>
lemma free_group_full_reindex:
  assumes hfree: "top1_is_free_group_full_on G mul e invg \<iota> S"
      and hbij: "bij_betw f S' S"
  shows "top1_is_free_group_full_on G mul e invg (\<iota> \<circ> f) S'"
proof -
  have hf_inj: "inj_on f S'" using hbij unfolding bij_betw_def by (by100 blast)
  have hf_img: "f ` S' = S" using hbij unfolding bij_betw_def by (by100 blast)
  have himg_eq: "(\<iota> \<circ> f) ` S' = \<iota> ` S"
    unfolding image_comp[symmetric] using hf_img by (by100 simp)
  \<comment> \<open>Extract conditions from hfree and build the result.
     Avoid unfolding the full definition at once to prevent automation blowup.\<close>
  have hfree_unfold: "top1_is_group_on G mul e invg
      \<and> (\<forall>s\<in>S. \<iota> s \<in> G) \<and> inj_on \<iota> S
      \<and> G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)
      \<and> (\<forall>ws. ws \<noteq> [] \<longrightarrow> top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<longrightarrow>
          (\<forall>i<length ws. fst (ws!i) \<in> S) \<longrightarrow>
          top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<noteq> e)"
    using hfree unfolding top1_is_free_group_full_on_def by (by100 blast)
  have h1: "top1_is_group_on G mul e invg" using hfree_unfold by (by100 blast)
  have h\<iota>_in: "\<forall>s\<in>S. \<iota> s \<in> G" using hfree_unfold by (by100 blast)
  have h\<iota>_inj: "inj_on \<iota> S" using hfree_unfold by (by100 blast)
  have hG_gen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
    using hfree_unfold by (by100 blast)
  have h2: "\<forall>s\<in>S'. (\<iota> \<circ> f) s \<in> G"
  proof (intro ballI)
    fix s assume "s \<in> S'"
    hence "f s \<in> S" using hf_img by (by100 blast)
    thus "(\<iota> \<circ> f) s \<in> G" using h\<iota>_in unfolding comp_def by (by100 blast)
  qed
  have h3: "inj_on (\<iota> \<circ> f) S'"
  proof (rule comp_inj_on[OF hf_inj])
    show "inj_on \<iota> (f ` S')" using h\<iota>_inj hf_img by (by100 simp)
  qed
  have h4: "G = top1_subgroup_generated_on G mul e invg ((\<iota> \<circ> f) ` S')"
    using hG_gen himg_eq by (by100 simp)
  have hred_orig: "\<forall>ws. ws \<noteq> [] \<longrightarrow>
      top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<longrightarrow>
      (\<forall>i<length ws. fst (ws!i) \<in> S) \<longrightarrow>
      top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<noteq> e"
    using hfree_unfold by (by100 blast)
  have h5: "\<forall>ws. ws \<noteq> [] \<longrightarrow>
      top1_is_reduced_word (map (\<lambda>(s, b). ((\<iota> \<circ> f) s, b)) ws) \<longrightarrow>
      (\<forall>i<length ws. fst (ws ! i) \<in> S') \<longrightarrow>
      top1_group_word_product mul e invg (map (\<lambda>(s, b). ((\<iota> \<circ> f) s, b)) ws) \<noteq> e"
  proof (intro allI impI)
    fix ws assume hne: "ws \<noteq> []"
       and hred_ws: "top1_is_reduced_word (map (\<lambda>(s, b). ((\<iota> \<circ> f) s, b)) ws)"
       and hentries: "\<forall>i<length ws. fst (ws ! i) \<in> S'"
    \<comment> \<open>Key: map (\<lambda>(s,b). ((\<iota>\<circ>f) s, b)) ws = map (\<lambda>(s,b). (\<iota> s, b)) (map (\<lambda>(s,b). (f s, b)) ws).\<close>
    define ws' where "ws' = map (\<lambda>(s, b). (f s, b)) ws"
    have hmap_eq: "map (\<lambda>(s, b). (\<iota> s, b)) ws' = map (\<lambda>(s, b). ((\<iota> \<circ> f) s, b)) ws"
      unfolding ws'_def
      using map_map_pair_compose[of \<iota> f ws, symmetric] unfolding comp_def by (by100 simp)
    have hne': "ws' \<noteq> []" unfolding ws'_def using hne by (by100 simp)
    have hentries': "\<forall>i<length ws'. fst (ws' ! i) \<in> S"
    proof (intro allI impI)
      fix i assume "i < length ws'"
      hence "i < length ws" unfolding ws'_def by (by100 simp)
      have "fst (ws ! i) \<in> S'" using hentries \<open>i < length ws\<close> by (by100 blast)
      hence "f (fst (ws ! i)) \<in> S" using hf_img by (by100 blast)
      moreover have "fst (ws' ! i) = f (fst (ws ! i))"
      proof -
        have "ws' ! i = (\<lambda>(s,b). (f s, b)) (ws ! i)"
          unfolding ws'_def using \<open>i < length ws\<close> by (by100 simp)
        thus ?thesis unfolding case_prod_beta by (by100 simp)
      qed
      ultimately show "fst (ws' ! i) \<in> S" by (by100 simp)
    qed
    have hred': "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws')"
      using hred_ws hmap_eq by (by100 simp)
    have "top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota> s, b)) ws') \<noteq> e"
      using hred_orig hne' hred' hentries' by (by100 blast)
    thus "top1_group_word_product mul e invg (map (\<lambda>(s, b). ((\<iota> \<circ> f) s, b)) ws) \<noteq> e"
      using hmap_eq by (by100 simp)
  qed
  show ?thesis unfolding top1_is_free_group_full_on_def
    using h1 h2 h3 h4 h5 by (by100 blast)
qed

text \<open>Book-faithful Theorem 58.3: the inclusion-induced map IS the iso.
  Munkres: "the inclusion map j:(A,x0) \<rightarrow> (X,x0) induces an isomorphism."
  Derives from AlgIsoFixed.Theorem\_58\_7 (explicit induced map iso) by
  constructing the homotopy equivalence from the deformation retract.\<close>
lemma Theorem_58_3_explicit:
  assumes hdr: "top1_deformation_retract_of_on X TX A"
      and hTX: "is_topology_on X TX"
      and hx0: "x0 \<in> A"
  shows "top1_group_iso_on
      (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
      (top1_fundamental_group_mul A (subspace_topology X TX A) x0)
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_induced_on A (subspace_topology X TX A) x0 X TX x0 (\<lambda>x. x))"
proof -
  have hA_sub: "A \<subseteq> X" using hdr unfolding top1_deformation_retract_of_on_def
    by (by100 blast)
  let ?TA = "subspace_topology X TX A"
  \<comment> \<open>Deformation retract \<Rightarrow> inclusion is a homotopy equivalence.
     r(x) = H(x,1) is the retraction. r \<circ> j = id (since H(a,1)=a).
     j \<circ> r \<simeq> id via H reversed: F(x,t) = H(x,1-t).\<close>
  have hdr_ex: "\<exists>H. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H
      \<and> (\<forall>x\<in>X. H (x, 0) = x) \<and> (\<forall>x\<in>X. H (x, 1) \<in> A)
      \<and> (\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) = a)"
    using hdr unfolding top1_deformation_retract_of_on_def by (by100 blast)
  then obtain H where
    hH_all: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H
      \<and> (\<forall>x\<in>X. H (x, 0) = x) \<and> (\<forall>x\<in>X. H (x, 1) \<in> A)
      \<and> (\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) = a)"
    by (by5000 auto)
  define r where "r x = H (x, 1)" for x
  have hH_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H"
    using hH_all by (by100 blast)
  have hH_0: "\<forall>x\<in>X. H (x, 0) = x" using hH_all by (by100 blast)
  have hH_1: "\<forall>x\<in>X. H (x, 1) \<in> A" using hH_all by (by100 blast)
  have hH_fix: "\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) = a" using hH_all by (by100 blast)
  \<comment> \<open>r as map X \<rightarrow> X continuous: r = H \<circ> section(x,1).\<close>
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
  have hpi1_eq: "pi1 \<circ> (\<lambda>x. (x, 1::real)) = id" unfolding pi1_def comp_def id_def by (by100 simp)
  have hpi2_eq: "pi2 \<circ> (\<lambda>x. (x, 1::real)) = (\<lambda>_. 1::real)" unfolding pi2_def comp_def by (by100 simp)
  have hsec: "top1_continuous_map_on X TX (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>x. (x, 1::real))"
  proof (rule iffD2[OF Theorem_18_4[OF hTX hTX hTI]])
    have "top1_continuous_map_on X TX X TX id" by (rule top1_continuous_map_on_id[OF hTX])
    hence "top1_continuous_map_on X TX X TX (pi1 \<circ> (\<lambda>x. (x, 1::real)))"
      unfolding hpi1_eq[symmetric] by (by100 simp)
    moreover have "top1_continuous_map_on X TX I_set I_top (\<lambda>_. 1::real)"
      using Theorem_18_2(1)[OF hTX hTI hTI, rule_format] h1_I by (by100 blast)
    hence "top1_continuous_map_on X TX I_set I_top (pi2 \<circ> (\<lambda>x. (x, 1::real)))"
      unfolding hpi2_eq[symmetric] by (by100 simp)
    ultimately show "top1_continuous_map_on X TX X TX (pi1 \<circ> (\<lambda>x. (x, 1::real))) \<and>
        top1_continuous_map_on X TX I_set I_top (pi2 \<circ> (\<lambda>x. (x, 1::real)))"
      by (by100 blast)
  qed
  have hr_X_cont: "top1_continuous_map_on X TX X TX r"
  proof -
    have "top1_continuous_map_on X TX X TX (H \<circ> (\<lambda>x. (x, 1::real)))"
      by (rule top1_continuous_map_on_comp[OF hsec hH_cont])
    moreover have "\<forall>x\<in>X. (H \<circ> (\<lambda>x. (x, 1::real))) x = r x"
      unfolding r_def comp_def by (by100 simp)
    ultimately show ?thesis using top1_continuous_map_on_agree by (by100 blast)
  qed
  have hj_equiv: "top1_homotopy_equivalence_on A ?TA X TX (\<lambda>x. x) r"
    unfolding top1_homotopy_equivalence_on_def
  proof (intro conjI)
    \<comment> \<open>j = id : A \<rightarrow> X continuous (inclusion).\<close>
    show "top1_continuous_map_on A ?TA X TX (\<lambda>x. x)"
    proof -
      have "top1_continuous_map_on A ?TA X TX id"
        using Theorem_18_2(2)[OF hTX hTX hTX] hA_sub by (by100 blast)
      thus ?thesis unfolding id_def by (by100 simp)
    qed
    \<comment> \<open>r : X \<rightarrow> A continuous.\<close>
    show "top1_continuous_map_on X TX A ?TA r"
    proof -
      \<comment> \<open>r = H \<circ> (\<lambda>x. (x,1)). Section x \<mapsto> (x,1) continuous by Theorem\_18\_4.\<close>
      have hTI: "is_topology_on I_set I_top"
        by (rule top1_unit_interval_topology_is_topology_on)
      have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
      \<comment> \<open>Section x \<mapsto> (x,1): X \<rightarrow> X \<times> I continuous.\<close>
      \<comment> \<open>Use the section lemma from Top1\_Ch3: (\<lambda>y. (x0, y)) continuous.\<close>
      have hsec: "top1_continuous_map_on X TX (X \<times> I_set) (product_topology_on TX I_top)
          (\<lambda>x. (x, 1::real))"
      proof (rule iffD2[OF Theorem_18_4[OF hTX hTX hTI]])
        have hpi1_eq: "pi1 \<circ> (\<lambda>x. (x, 1::real)) = id" unfolding pi1_def comp_def id_def by (by100 simp)
        have "top1_continuous_map_on X TX X TX id" by (rule top1_continuous_map_on_id[OF hTX])
        hence "top1_continuous_map_on X TX X TX (pi1 \<circ> (\<lambda>x. (x, 1::real)))"
          unfolding hpi1_eq[symmetric] by (by100 simp)
        moreover have "pi2 \<circ> (\<lambda>x. (x, 1::real)) = (\<lambda>_. 1::real)"
          unfolding pi2_def comp_def by (by100 simp)
        have hpi2_eq: "pi2 \<circ> (\<lambda>x. (x, 1::real)) = (\<lambda>_. 1::real)"
          unfolding pi2_def comp_def by (by100 simp)
        have "top1_continuous_map_on X TX I_set I_top (\<lambda>_. 1::real)"
          using Theorem_18_2(1)[OF hTX hTI hTI, rule_format] h1_I by (by100 blast)
        hence "top1_continuous_map_on X TX I_set I_top (pi2 \<circ> (\<lambda>x. (x, 1::real)))"
          unfolding hpi2_eq[symmetric] by (by100 simp)
        ultimately show "top1_continuous_map_on X TX X TX (pi1 \<circ> (\<lambda>x. (x, 1::real))) \<and>
            top1_continuous_map_on X TX I_set I_top (pi2 \<circ> (\<lambda>x. (x, 1::real)))"
          by (by100 blast)
      qed
      \<comment> \<open>r as map X \<rightarrow> X: composition of section with H.\<close>
      have hr_X: "top1_continuous_map_on X TX X TX (H \<circ> (\<lambda>x. (x, 1::real)))"
        by (rule top1_continuous_map_on_comp[OF hsec hH_cont])
      have hr_eq: "\<forall>x\<in>X. (H \<circ> (\<lambda>x. (x, 1::real))) x = r x"
        unfolding r_def comp_def by (by100 simp)
      have hr_X': "top1_continuous_map_on X TX X TX r"
        using top1_continuous_map_on_agree[OF hr_X hr_eq] by (by100 simp)
      \<comment> \<open>Restrict codomain from X to A. r maps into A (from hH\_1).\<close>
      have hr_range: "\<forall>x\<in>X. r x \<in> A" unfolding r_def using hH_1 by (by100 blast)
      hence hr_img: "r ` X \<subseteq> A" by (by100 blast)
      \<comment> \<open>Restrict codomain: Theorem\_18\_2(5) (restrict\_range).\<close>
      show ?thesis
        using Theorem_18_2(5)[OF hTX hTX hTX, rule_format] hr_X' hA_sub hr_img
        by (by100 blast)
    qed
    \<comment> \<open>r \<circ> j \<simeq> id on A. Actually r \<circ> j = id (since H(a,1) = a for a \<in> A).\<close>
    show "top1_homotopic_on A ?TA A ?TA (r \<circ> (\<lambda>x. x)) (\<lambda>x. x)"
    proof -
      \<comment> \<open>r \<circ> j = id on A: r(a) = H(a,1) = a for a \<in> A.\<close>
      have hrj_eq: "\<forall>a\<in>A. (r \<circ> (\<lambda>x. x)) a = a"
      proof (intro ballI)
        fix a assume "a \<in> A"
        have "(r \<circ> (\<lambda>x. x)) a = H (a, 1)" unfolding r_def by (by100 simp)
        also have "\<dots> = a"
        proof -
          have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
          thus ?thesis using hH_fix \<open>a \<in> A\<close> by (by100 blast)
        qed
        finally show "(r \<circ> (\<lambda>x. x)) a = a" .
      qed
      \<comment> \<open>id : A \<rightarrow> A continuous.\<close>
      have hTA: "is_topology_on A ?TA"
        by (rule subspace_topology_is_topology_on[OF hTX hA_sub])
      have hid_cont: "top1_continuous_map_on A ?TA A ?TA (\<lambda>x. x)"
        using top1_continuous_map_on_id[OF hTA] unfolding id_def by (by100 simp)
      \<comment> \<open>id \<simeq> id (reflexivity), then r \<circ> j agrees with id on A.\<close>
      have "top1_homotopic_on A ?TA A ?TA (\<lambda>x. x) (\<lambda>x. x)"
        using Lemma_51_1_homotopic_refl[OF hid_cont hTA] by (by100 simp)
      \<comment> \<open>r \<circ> j agrees with id on A, so they're homotopic.\<close>
      moreover have "top1_continuous_map_on A ?TA A ?TA (r \<circ> (\<lambda>x. x))"
      proof -
        have "\<forall>a\<in>A. (\<lambda>x. x) a = (r \<circ> (\<lambda>x. x)) a" using hrj_eq by (by100 simp)
        thus ?thesis using top1_continuous_map_on_agree[OF hid_cont] by (by100 blast)
      qed
      ultimately show ?thesis
      proof -
        assume hid_htpy: "top1_homotopic_on A ?TA A ?TA (\<lambda>x. x) (\<lambda>x. x)"
           and hrj_cont: "top1_continuous_map_on A ?TA A ?TA (r \<circ> (\<lambda>x. x))"
        from hid_htpy[unfolded top1_homotopic_on_def]
        obtain F where hF_cont: "top1_continuous_map_on (A \<times> I_set)
              (product_topology_on ?TA I_top) A ?TA F"
            and hF_0: "\<forall>x\<in>A. F (x, 0) = x" and hF_1: "\<forall>x\<in>A. F (x, 1) = x"
          by (by100 blast)
        have "\<forall>x\<in>A. F (x, 0) = (r \<circ> (\<lambda>x. x)) x"
          using hF_0 hrj_eq by (by100 simp)
        show "top1_homotopic_on A ?TA A ?TA (r \<circ> (\<lambda>x. x)) (\<lambda>x. x)"
          unfolding top1_homotopic_on_def
        proof (intro conjI)
          show "top1_continuous_map_on A ?TA A ?TA (r \<circ> (\<lambda>x. x))" by (rule hrj_cont)
          show "top1_continuous_map_on A ?TA A ?TA (\<lambda>x. x)" by (rule hid_cont)
          show "\<exists>Fa. top1_continuous_map_on (A \<times> I_set) (product_topology_on ?TA I_top) A ?TA Fa
              \<and> (\<forall>x\<in>A. Fa (x, 0) = (r \<circ> (\<lambda>x. x)) x) \<and> (\<forall>x\<in>A. Fa (x, 1) = x)"
            using hF_cont \<open>\<forall>x\<in>A. F (x, 0) = (r \<circ> (\<lambda>x. x)) x\<close> hF_1 by (by100 blast)
        qed
      qed
    qed
    \<comment> \<open>j \<circ> r \<simeq> id on X. Homotopy: F(x,t) = H(x,1-t).
       F(x,0) = H(x,1) = r(x) = (j \<circ> r)(x). F(x,1) = H(x,0) = x.\<close>
    show "top1_homotopic_on X TX X TX ((\<lambda>x. x) \<circ> r) (\<lambda>y. y)"
      unfolding top1_homotopic_on_def
    proof (intro conjI)
      \<comment> \<open>j \<circ> r = r : X \<rightarrow> X (since j = id).\<close>
      show "top1_continuous_map_on X TX X TX ((\<lambda>x. x) \<circ> r)"
      proof -
        have "(\<lambda>x. x) \<circ> r = r" unfolding comp_def by (by100 simp)
        thus ?thesis using hr_X_cont by (by100 simp)
      qed
      show "top1_continuous_map_on X TX X TX (\<lambda>y. y)"
        using top1_continuous_map_on_id[OF hTX] unfolding id_def by (by100 simp)
      \<comment> \<open>Homotopy witness: F(x,t) = H(x, 1-t).\<close>
      show "\<exists>F. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX F
          \<and> (\<forall>x\<in>X. F (x, 0) = ((\<lambda>x. x) \<circ> r) x) \<and> (\<forall>x\<in>X. F (x, 1) = x)"
      proof (rule exI[of _ "\<lambda>p. H (fst p, 1 - snd p)"])
        have hflip_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
            (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>p. (fst p, 1 - snd p))"
          by (rule flip_t_continuous_product[OF hTX])
        have hHflip_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
            X TX (\<lambda>p. H (fst p, 1 - snd p))"
        proof -
          have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
              X TX (H \<circ> (\<lambda>p. (fst p, 1 - snd p)))"
            by (rule top1_continuous_map_on_comp[OF hflip_cont hH_cont])
          moreover have "\<forall>p\<in>X \<times> I_set. (H \<circ> (\<lambda>p. (fst p, 1 - snd p))) p = H (fst p, 1 - snd p)"
            unfolding comp_def by (by100 simp)
          ultimately show ?thesis
            by (rule top1_continuous_map_on_agree)
        qed
        have hHflip_0: "\<forall>x\<in>X. H (fst (x, (0::real)), 1 - snd (x, (0::real))) = ((\<lambda>x. x) \<circ> r) x"
        proof (intro ballI)
          fix x assume "x \<in> X"
          have "H (fst (x, (0::real)), 1 - snd (x, (0::real))) = H (x, 1)"
            by (by100 simp)
          also have "\<dots> = r x" unfolding r_def by (by100 simp)
          finally show "H (fst (x, (0::real)), 1 - snd (x, (0::real))) = ((\<lambda>x. x) \<circ> r) x"
            by (by100 simp)
        qed
        have hHflip_1: "\<forall>x\<in>X. H (fst (x, (1::real)), 1 - snd (x, (1::real))) = x"
        proof (intro ballI)
          fix x assume "x \<in> X"
          have "H (fst (x, (1::real)), 1 - snd (x, (1::real))) = H (x, 0)"
            by (by100 simp)
          also have "\<dots> = x" using hH_0 \<open>x \<in> X\<close> by (by100 blast)
          finally show "H (fst (x, (1::real)), 1 - snd (x, (1::real))) = x" .
        qed
        show "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX (\<lambda>p. H (fst p, 1 - snd p))
            \<and> (\<forall>x\<in>X. H (fst (x, (0::real)), 1 - snd (x, (0::real))) = ((\<lambda>x. x) \<circ> r) x)
            \<and> (\<forall>x\<in>X. H (fst (x, (1::real)), 1 - snd (x, (1::real))) = x)"
          using hHflip_cont hHflip_0 hHflip_1 by (by100 blast)
      qed
    qed
  qed
  have hTA: "is_topology_on A ?TA"
    by (rule subspace_topology_is_topology_on[OF hTX hA_sub])
  from AlgIsoFixed.Theorem_58_7[OF hTA hTX hj_equiv hx0]
  show ?thesis by (by100 simp)
qed

text \<open>Pasting deformation retractions on finitely many closed subsets.
  Munkres 71.1: "The maps F\_i fit together... the pasting lemma applies."
  If X = \<Union>F with F finite, each A \<in> F closed in X, each A deformation-retracts
  to {p}, they pairwise intersect only at {p}, and all retractions fix p,
  then X deformation-retracts to {p}.\<close>
lemma pasting_deformation_retracts_to_point:
  assumes hTX: "is_topology_on_strict X TX"
      and hfin: "finite F"
      and hF_closed: "\<forall>A\<in>F. closedin_on X TX A"
      and hcover: "X = \<Union>F"
      and hp: "p \<in> X"
      and hp_all: "\<forall>A\<in>F. p \<in> A"
      and hpairwise: "\<forall>A\<in>F. \<forall>B\<in>F. A \<noteq> B \<longrightarrow> A \<inter> B = {p}"
      and hdr: "\<forall>A\<in>F. top1_deformation_retract_of_on A (subspace_topology X TX A) {p}"
  shows "top1_deformation_retract_of_on X TX {p}"
  using assms
proof (induction "card F" arbitrary: F X TX rule: less_induct)
  case (less F)
  have hTX_is: "is_topology_on X TX"
    using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
  show ?case
  proof (cases "F = {}")
    case True thus ?thesis using less.prems(4,5) by (by100 simp)
  next
    case False
    then obtain A where hA: "A \<in> F" by (by100 blast)
    define F0 where "F0 = F - {A}"
    have hF_eq: "F = insert A F0" and hA_notin: "A \<notin> F0"
      unfolding F0_def using hA by (by100 blast)+
    have hF0_fin: "finite F0" using less.prems(2) F0_def by (by100 simp)
    have hcard_lt: "card F0 < card F"
      using less.prems(2) hA hF_eq hA_notin by (by100 simp)
    show ?thesis
    proof (cases "F0 = {}")
      case True
      \<comment> \<open>|F| = 1. X = A. Retraction of A in subspace = retraction of X.\<close>
      hence "X = A" using less.prems(4) hF_eq by (by100 simp)
      have "top1_deformation_retract_of_on A (subspace_topology X TX A) {p}"
        using less.prems(8) hA by (by100 blast)
      moreover have "subspace_topology X TX A = TX"
      proof -
        have "A = X" using \<open>X = A\<close> by (by100 simp)
        have "\<forall>U\<in>TX. U \<subseteq> X"
          using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
        hence "subspace_topology X TX X = TX" by (rule subspace_topology_self)
        moreover have "X = A" using \<open>X = A\<close> by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      ultimately show ?thesis using \<open>X = A\<close> by (by100 simp)
    next
      case False
      \<comment> \<open>|F| \<ge> 2. X = A \<union> \<Union>F0.\<close>
      define Y where "Y = \<Union>F0"
      have hX_AY: "X = A \<union> Y" using less.prems(4) hF_eq Y_def by (by100 auto)
      have hY_sub: "Y \<subseteq> X" using hX_AY by (by100 blast)
      have hA_sub: "A \<subseteq> X" using hX_AY by (by100 blast)
      have hA_closed: "closedin_on X TX A" using less.prems(3) hA by (by100 blast)
      have hY_closed: "closedin_on X TX Y"
      proof -
        have "\<forall>B\<in>F0. closedin_on X TX B" using less.prems(3) F0_def by (by100 blast)
        hence "\<forall>A\<in>(\<lambda>B. B) ` F0. closedin_on X TX A" by (by100 simp)
        thus ?thesis unfolding Y_def
          using closedin_on_finite_Union[OF hTX_is] hF0_fin by (by100 blast)
      qed
      \<comment> \<open>A \<inter> Y = {p}.\<close>
      have hp_AY: "p \<in> A \<inter> Y"
      proof -
        have "p \<in> A" using less.prems(6) hA by (by100 blast)
        from False obtain B where "B \<in> F0" by (by100 blast)
        hence "p \<in> B" using less.prems(6) F0_def by (by100 blast)
        hence "p \<in> Y" unfolding Y_def using \<open>B \<in> F0\<close> by (by100 blast)
        thus ?thesis using \<open>p \<in> A\<close> by (by100 blast)
      qed
      have hAY_inter: "A \<inter> Y = {p}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> A \<inter> Y"
        hence "x \<in> A" "x \<in> Y" by (by100 blast)+
        from \<open>x \<in> Y\<close> obtain B where "B \<in> F0" "x \<in> B" unfolding Y_def by (by100 blast)
        have "A \<noteq> B" using hA_notin \<open>B \<in> F0\<close> by (by100 blast)
        have "A \<in> F" "B \<in> F" using hA \<open>B \<in> F0\<close> F0_def by (by100 blast)+
        hence "A \<inter> B = {p}" using less.prems(7) \<open>A \<noteq> B\<close> by (by100 blast)
        thus "x \<in> {p}" using \<open>x \<in> A\<close> \<open>x \<in> B\<close> by (by100 blast)
      next
        fix x assume "x \<in> {p}" thus "x \<in> A \<inter> Y" using hp_AY by (by100 blast)
      qed
      \<comment> \<open>IH: Y deformation-retracts to {p} in subspace X TX Y.\<close>
      have hY_dr: "top1_deformation_retract_of_on Y (subspace_topology X TX Y) {p}"
      proof -
        let ?TY = "subspace_topology X TX Y"
        have hTY_strict: "is_topology_on_strict Y ?TY"
          by (rule subspace_topology_is_strict[OF less.prems(1) hY_sub])
        have hTY: "is_topology_on Y ?TY"
          using hTY_strict unfolding is_topology_on_strict_def by (by100 blast)
        have hF0_closed_Y: "\<forall>B\<in>F0. closedin_on Y ?TY B"
        proof (intro ballI)
          fix B assume "B \<in> F0"
          hence "B \<in> F" using F0_def by (by100 blast)
          have "closedin_on X TX B" using less.prems(3) \<open>B \<in> F\<close> by (by100 blast)
          have "B \<subseteq> Y" using \<open>B \<in> F0\<close> Y_def by (by100 blast)
          hence "B = B \<inter> Y" by (by100 blast)
          thus "closedin_on Y ?TY B"
            using iffD2[OF Theorem_17_2[OF hTX_is hY_sub]]
                  \<open>closedin_on X TX B\<close> by (by100 blast)
        qed
        have hF0_cover: "Y = \<Union>F0" unfolding Y_def ..
        have hp_Y: "p \<in> Y" using hp_AY by (by100 blast)
        have hp_all_F0: "\<forall>B\<in>F0. p \<in> B" using less.prems(6) F0_def by (by100 blast)
        have hpairwise_F0: "\<forall>B1\<in>F0. \<forall>B2\<in>F0. B1 \<noteq> B2 \<longrightarrow> B1 \<inter> B2 = {p}"
        proof (intro ballI impI)
          fix B1 B2 assume "B1 \<in> F0" "B2 \<in> F0" "B1 \<noteq> B2"
          hence "B1 \<in> F" "B2 \<in> F" using F0_def by (by100 blast)+
          thus "B1 \<inter> B2 = {p}" using less.prems(7) \<open>B1 \<noteq> B2\<close> by (by100 blast)
        qed
        have hdr_F0: "\<forall>B\<in>F0. top1_deformation_retract_of_on B (subspace_topology Y ?TY B) {p}"
        proof (intro ballI)
          fix B assume "B \<in> F0"
          have "top1_deformation_retract_of_on B (subspace_topology X TX B) {p}"
            using less.prems(8) \<open>B \<in> F0\<close> F0_def by (by100 blast)
          moreover have "B \<subseteq> Y" using \<open>B \<in> F0\<close> Y_def by (by100 blast)
          hence "subspace_topology Y ?TY B = subspace_topology X TX B"
            by (rule subspace_topology_trans)
          ultimately show "top1_deformation_retract_of_on B (subspace_topology Y ?TY B) {p}"
            by (by100 simp)
        qed
        from less(1)[OF hcard_lt hTY_strict hF0_fin hF0_closed_Y hF0_cover hp_Y hp_all_F0 hpairwise_F0 hdr_F0]
        show ?thesis .
      qed
      have hA_dr: "top1_deformation_retract_of_on A (subspace_topology X TX A) {p}"
        using less.prems(8) hA by (by100 blast)
      \<comment> \<open>Paste: X = A \<union> Y, A \<inter> Y = {p}, A closed, Y closed,
         A and Y each deformation-retract to {p}.\<close>
      \<comment> \<open>Extract retraction homotopies HA and HY.\<close>
      have hA_dr_ex: "\<exists>HA. top1_continuous_map_on (A \<times> I_set)
            (product_topology_on (subspace_topology X TX A) I_top) A (subspace_topology X TX A) HA
          \<and> (\<forall>x\<in>A. HA (x, 0) = x) \<and> (\<forall>x\<in>A. HA (x, 1) \<in> {p})
          \<and> (\<forall>a\<in>{p}. \<forall>t\<in>I_set. HA (a, t) = a)"
        using hA_dr unfolding top1_deformation_retract_of_on_def by (by100 blast)
      then obtain HA where hHA: "top1_continuous_map_on (A \<times> I_set)
            (product_topology_on (subspace_topology X TX A) I_top) A (subspace_topology X TX A) HA
          \<and> (\<forall>x\<in>A. HA (x, 0) = x) \<and> (\<forall>x\<in>A. HA (x, 1) \<in> {p})
          \<and> (\<forall>a\<in>{p}. \<forall>t\<in>I_set. HA (a, t) = a)"
        by (by5000 auto)
      have hY_dr_ex: "\<exists>HY. top1_continuous_map_on (Y \<times> I_set)
            (product_topology_on (subspace_topology X TX Y) I_top) Y (subspace_topology X TX Y) HY
          \<and> (\<forall>x\<in>Y. HY (x, 0) = x) \<and> (\<forall>x\<in>Y. HY (x, 1) \<in> {p})
          \<and> (\<forall>a\<in>{p}. \<forall>t\<in>I_set. HY (a, t) = a)"
        using hY_dr unfolding top1_deformation_retract_of_on_def by (by100 blast)
      then obtain HY where hHY: "top1_continuous_map_on (Y \<times> I_set)
            (product_topology_on (subspace_topology X TX Y) I_top) Y (subspace_topology X TX Y) HY
          \<and> (\<forall>x\<in>Y. HY (x, 0) = x) \<and> (\<forall>x\<in>Y. HY (x, 1) \<in> {p})
          \<and> (\<forall>a\<in>{p}. \<forall>t\<in>I_set. HY (a, t) = a)"
        by (by5000 auto)
      \<comment> \<open>Define H piecewise.\<close>
      define H where "H = (\<lambda>(x, t). if x \<in> A then HA (x, t) else HY (x, t))"
      show ?thesis unfolding top1_deformation_retract_of_on_def
      proof (intro conjI)
        show "{p} \<subseteq> X" using less.prems(5) by (by100 blast)
        \<comment> \<open>H continuous + boundary conditions.\<close>
        show "\<exists>Hmap. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX Hmap
            \<and> (\<forall>x\<in>X. Hmap (x, 0) = x) \<and> (\<forall>x\<in>X. Hmap (x, 1) \<in> {p})
            \<and> (\<forall>a\<in>{p}. \<forall>t\<in>I_set. Hmap (a, t) = a)"
        proof (rule exI[of _ H])
          \<comment> \<open>Boundary conditions.\<close>
          have hH_0: "\<forall>x\<in>X. H (x, 0) = x"
          proof (intro ballI)
            fix x assume "x \<in> X"
            hence "x \<in> A \<or> x \<in> Y" using hX_AY by (by100 blast)
            thus "H (x, 0) = x"
              unfolding H_def using hHA hHY by (by100 force)
          qed
          have hH_1: "\<forall>x\<in>X. H (x, 1) \<in> {p}"
          proof (intro ballI)
            fix x assume "x \<in> X"
            hence "x \<in> A \<or> x \<in> Y" using hX_AY by (by100 blast)
            thus "H (x, 1) \<in> {p}"
              unfolding H_def using hHA hHY by (by100 force)
          qed
          have hH_fix: "\<forall>a\<in>{p}. \<forall>t\<in>I_set. H (a, t) = a"
          proof (intro ballI)
            fix a t assume "a \<in> {p}" "t \<in> I_set"
            hence "a = p" by (by100 blast)
            have "p \<in> A" using hp_AY by (by100 blast)
            thus "H (a, t) = a" unfolding H_def \<open>a = p\<close>
              using hHA \<open>t \<in> I_set\<close> \<open>p \<in> A\<close> by (by100 force)
          qed
          \<comment> \<open>Continuity by pasting\_lemma\_two\_closed.\<close>
          have hH_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H"
          proof -
            let ?TXI = "product_topology_on TX I_top"
            have hTXI: "is_topology_on (X \<times> I_set) ?TXI"
              by (rule product_topology_on_is_topology_on[OF hTX_is top1_unit_interval_topology_is_topology_on])
            \<comment> \<open>A\<times>I closed in X\<times>I.\<close>
            have hAI_closed: "closedin_on (X \<times> I_set) ?TXI (A \<times> I_set)"
            proof -
              have "(X \<times> I_set) - (A \<times> I_set) = (X - A) \<times> I_set" by (by100 blast)
              moreover have "X - A \<in> TX" using hA_closed unfolding closedin_on_def by (by100 blast)
              moreover have "I_set \<in> I_top"
                using top1_unit_interval_topology_is_topology_on unfolding is_topology_on_def by (by100 blast)
              ultimately have "(X \<times> I_set) - (A \<times> I_set) \<in> ?TXI"
                using product_rect_open by (by100 simp)
              moreover have "A \<times> I_set \<subseteq> X \<times> I_set" using hA_sub by (by100 blast)
              ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
            qed
            \<comment> \<open>Y\<times>I closed in X\<times>I.\<close>
            have hYI_closed: "closedin_on (X \<times> I_set) ?TXI (Y \<times> I_set)"
            proof -
              have "(X \<times> I_set) - (Y \<times> I_set) = (X - Y) \<times> I_set" by (by100 blast)
              moreover have "X - Y \<in> TX" using hY_closed unfolding closedin_on_def by (by100 blast)
              moreover have "I_set \<in> I_top"
                using top1_unit_interval_topology_is_topology_on unfolding is_topology_on_def by (by100 blast)
              ultimately have "(X \<times> I_set) - (Y \<times> I_set) \<in> ?TXI"
                using product_rect_open by (by100 simp)
              moreover have "Y \<times> I_set \<subseteq> X \<times> I_set" using hY_sub by (by100 blast)
              ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
            qed
            \<comment> \<open>A\<times>I \<union> Y\<times>I = X\<times>I.\<close>
            have hAYI_cover: "A \<times> I_set \<union> Y \<times> I_set = X \<times> I_set"
              using hX_AY by (by100 blast)
            \<comment> \<open>H maps X\<times>I to X.\<close>
            \<comment> \<open>HA maps into A, HY maps into Y.\<close>
            have hHA_range: "\<forall>x\<in>A. \<forall>t\<in>I_set. HA (x, t) \<in> A"
            proof (intro ballI)
              fix x t assume "x \<in> A" "t \<in> I_set"
              have "top1_continuous_map_on (A \<times> I_set) (product_topology_on (subspace_topology X TX A) I_top)
                  A (subspace_topology X TX A) HA" using hHA by (by100 blast)
              hence "\<forall>p\<in>A \<times> I_set. HA p \<in> A"
                unfolding top1_continuous_map_on_def by (by100 blast)
              thus "HA (x, t) \<in> A" using \<open>x \<in> A\<close> \<open>t \<in> I_set\<close> by (by100 blast)
            qed
            have hHY_range: "\<forall>x\<in>Y. \<forall>t\<in>I_set. HY (x, t) \<in> Y"
            proof (intro ballI)
              fix x t assume "x \<in> Y" "t \<in> I_set"
              have "top1_continuous_map_on (Y \<times> I_set) (product_topology_on (subspace_topology X TX Y) I_top)
                  Y (subspace_topology X TX Y) HY" using hHY by (by100 blast)
              hence "\<forall>p\<in>Y \<times> I_set. HY p \<in> Y"
                unfolding top1_continuous_map_on_def by (by100 blast)
              thus "HY (x, t) \<in> Y" using \<open>x \<in> Y\<close> \<open>t \<in> I_set\<close> by (by100 blast)
            qed
            have hH_range: "\<forall>p\<in>X \<times> I_set. H p \<in> X"
            proof (intro ballI)
              fix pt assume "pt \<in> X \<times> I_set"
              then obtain x t where hpt: "pt = (x, t)" "x \<in> X" "t \<in> I_set" by (by100 blast)
              show "H pt \<in> X"
              proof (cases "x \<in> A")
                case True
                have "H pt = HA (x, t)" unfolding H_def hpt using True by (by100 simp)
                have "HA (x, t) \<in> A" using hHA_range True \<open>t \<in> I_set\<close> by (by100 blast)
                hence "HA (x, t) \<in> X" using hA_sub by (by100 blast)
                thus ?thesis using \<open>H pt = HA (x, t)\<close> by (by100 simp)
              next
                case False
                hence "x \<in> Y" using \<open>x \<in> X\<close> hX_AY by (by100 blast)
                have "H pt = HY (x, t)" unfolding H_def hpt using False by (by100 simp)
                have "HY (x, t) \<in> Y" using hHY_range \<open>x \<in> Y\<close> \<open>t \<in> I_set\<close> by (by100 blast)
                hence "HY (x, t) \<in> X" using hY_sub by (by100 blast)
                thus ?thesis using \<open>H pt = HY (x, t)\<close> by (by100 simp)
              qed
            qed
            \<comment> \<open>H continuous on A\<times>I (agrees with HA there, which is continuous).\<close>
            \<comment> \<open>Subspace of product = product of subspaces (Theorem\_16\_3).\<close>
            have hTI: "is_topology_on I_set I_top"
              by (rule top1_unit_interval_topology_is_topology_on)
            have hI_strict: "I_top \<subseteq> Pow I_set"
            proof -
              have "is_topology_on_strict I_set I_top"
              proof -
                have "is_topology_on_strict (UNIV :: real set) top1_open_sets"
                  unfolding is_topology_on_strict_def
                  using top1_open_sets_is_topology_on_UNIV by (by100 blast)
                have "I_set \<subseteq> (UNIV :: real set)" by (by100 blast)
                thus ?thesis unfolding top1_unit_interval_topology_def
                  by (rule subspace_topology_is_strict[OF \<open>is_topology_on_strict UNIV top1_open_sets\<close>])
              qed
              thus ?thesis unfolding is_topology_on_strict_def by (by100 blast)
            qed
            \<comment> \<open>Subspace I I\_top I = I\_top (I\_top strict).\<close>
            have hI_self: "subspace_topology I_set I_top I_set = I_top"
            proof (rule subspace_topology_self)
              show "\<forall>U\<in>I_top. U \<subseteq> I_set" using hI_strict by (by100 blast)
            qed
            \<comment> \<open>Theorem\_16\_3: subspace(X\<times>I, product TX I\_top, A\<times>I) = product(subspace TX A, I\_top).\<close>
            have hTI: "is_topology_on I_set I_top"
              by (rule top1_unit_interval_topology_is_topology_on)
            have hA_sub_eq: "subspace_topology (X \<times> I_set) ?TXI (A \<times> I_set)
                = product_topology_on (subspace_topology X TX A) I_top"
            proof -
              have "product_topology_on (subspace_topology X TX A) (subspace_topology I_set I_top I_set)
                  = subspace_topology (X \<times> I_set) ?TXI (A \<times> I_set)"
                by (rule Theorem_16_3[OF hTX_is hTI])
              thus ?thesis using hI_self by (by100 simp)
            qed
            \<comment> \<open>H = HA on A\<times>I.\<close>
            have hH_eq_HA: "\<forall>p\<in>A \<times> I_set. HA p = H p"
              unfolding H_def by (by100 auto)
            \<comment> \<open>HA continuous product(subspace TX A, I\_top) \<rightarrow> A (given).\<close>
            have hHA_cont: "top1_continuous_map_on (A \<times> I_set)
                (product_topology_on (subspace_topology X TX A) I_top)
                A (subspace_topology X TX A) HA"
              using hHA by (by100 blast)
            \<comment> \<open>Expand codomain from A to X: Theorem\_18\_2(6).\<close>
            have hHA_cont_X: "top1_continuous_map_on (A \<times> I_set)
                (product_topology_on (subspace_topology X TX A) I_top) X TX HA"
            proof -
              have hTAI: "is_topology_on (A \<times> I_set) (product_topology_on (subspace_topology X TX A) I_top)"
                by (rule product_topology_on_is_topology_on[OF
                    subspace_topology_is_topology_on[OF hTX_is hA_sub] hTI])
              have hTA: "is_topology_on A (subspace_topology X TX A)"
                by (rule subspace_topology_is_topology_on[OF hTX_is hA_sub])
              have "subspace_topology X TX A = subspace_topology X TX A" ..
              show ?thesis
                using Theorem_18_2(6)[OF hTAI hTA hTX_is, rule_format]
                      hHA_cont hA_sub by (by100 blast)
            qed
            \<comment> \<open>Transfer: H = HA on A\<times>I, HA continuous \<Rightarrow> H continuous.\<close>
            have hH_on_A: "top1_continuous_map_on (A \<times> I_set)
                (subspace_topology (X \<times> I_set) ?TXI (A \<times> I_set)) X TX H"
            proof -
              have "top1_continuous_map_on (A \<times> I_set)
                  (product_topology_on (subspace_topology X TX A) I_top) X TX H"
                by (rule top1_continuous_map_on_agree[OF hHA_cont_X hH_eq_HA])
              thus ?thesis using hA_sub_eq by (by100 simp)
            qed
            \<comment> \<open>Same for Y side.\<close>
            \<comment> \<open>Y side: same argument.\<close>
            have hY_sub_eq: "subspace_topology (X \<times> I_set) ?TXI (Y \<times> I_set)
                = product_topology_on (subspace_topology X TX Y) I_top"
            proof -
              have "product_topology_on (subspace_topology X TX Y) (subspace_topology I_set I_top I_set)
                  = subspace_topology (X \<times> I_set) ?TXI (Y \<times> I_set)"
                by (rule Theorem_16_3[OF hTX_is hTI])
              thus ?thesis using hI_self by (by100 simp)
            qed
            have hH_eq_HY: "\<forall>p\<in>Y \<times> I_set. HY p = H p"
            proof (intro ballI)
              fix pt assume "pt \<in> Y \<times> I_set"
              then obtain x t where hpt: "pt = (x, t)" "x \<in> Y" "t \<in> I_set" by (by100 blast)
              show "HY pt = H pt"
              proof (cases "x \<in> A")
                case True
                hence "x = p" using \<open>x \<in> Y\<close> hAY_inter by (by100 blast)
                have hHA_fix: "\<forall>a\<in>{p}. \<forall>t\<in>I_set. HA (a, t) = a"
                  using hHA by (by100 blast)
                have hHY_fix: "\<forall>a\<in>{p}. \<forall>t\<in>I_set. HY (a, t) = a"
                  using hHY by (by100 blast)
                have "H pt = HA pt" unfolding H_def hpt using True by (by100 simp)
                also have "\<dots> = p" using hHA_fix \<open>x = p\<close> \<open>t \<in> I_set\<close> hpt by (by100 simp)
                also have "\<dots> = HY pt" using hHY_fix \<open>x = p\<close> \<open>t \<in> I_set\<close> hpt by (by100 simp)
                finally show ?thesis by (by100 simp)
              next
                case False
                show ?thesis unfolding H_def hpt using False by (by100 simp)
              qed
            qed
            have hHY_cont: "top1_continuous_map_on (Y \<times> I_set)
                (product_topology_on (subspace_topology X TX Y) I_top)
                Y (subspace_topology X TX Y) HY"
              using hHY by (by100 blast)
            have hHY_cont_X: "top1_continuous_map_on (Y \<times> I_set)
                (product_topology_on (subspace_topology X TX Y) I_top) X TX HY"
            proof -
              have hTYI: "is_topology_on (Y \<times> I_set) (product_topology_on (subspace_topology X TX Y) I_top)"
                by (rule product_topology_on_is_topology_on[OF
                    subspace_topology_is_topology_on[OF hTX_is hY_sub] hTI])
              have hTY_here: "is_topology_on Y (subspace_topology X TX Y)"
                by (rule subspace_topology_is_topology_on[OF hTX_is hY_sub])
              show ?thesis
                using Theorem_18_2(6)[OF hTYI hTY_here hTX_is, rule_format]
                      hHY_cont hY_sub by (by100 blast)
            qed
            have hH_on_Y: "top1_continuous_map_on (Y \<times> I_set)
                (subspace_topology (X \<times> I_set) ?TXI (Y \<times> I_set)) X TX H"
            proof -
              have "top1_continuous_map_on (Y \<times> I_set)
                  (product_topology_on (subspace_topology X TX Y) I_top) X TX H"
                by (rule top1_continuous_map_on_agree[OF hHY_cont_X hH_eq_HY])
              thus ?thesis using hY_sub_eq by (by100 simp)
            qed
            \<comment> \<open>Apply pasting\_lemma\_two\_closed.\<close>
            show ?thesis
              by (rule pasting_lemma_two_closed[OF hTXI hTX_is hAI_closed hYI_closed hAYI_cover hH_range hH_on_A hH_on_Y])
          qed
          show "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H
              \<and> (\<forall>x\<in>X. H (x, 0) = x) \<and> (\<forall>x\<in>X. H (x, 1) \<in> {p})
              \<and> (\<forall>a\<in>{p}. \<forall>t\<in>I_set. H (a, t) = a)"
            using hH_cont hH_0 hH_1 hH_fix by (by100 blast)
        qed
      qed
    qed
  qed
qed

text \<open>Variant: pasting deformation retractions to a subspace (not just a point).
  Munkres: "S\_1 is a deformation retract of U."
  A\_0 stays fixed (identity homotopy), each A\_j for j \<ge> 1 retracts to p \<in> A\_0.\<close>
lemma pasting_deformation_retract_to_subspace:
  assumes hTX: "is_topology_on_strict X TX"
      and hfin: "finite F"
      and hA0: "A0 \<in> F"
      and hF_closed: "\<forall>A\<in>F. closedin_on X TX A"
      and hcover: "X = \<Union>F"
      and hp: "p \<in> A0"
      and hp_all: "\<forall>A\<in>F. p \<in> A"
      and hpairwise: "\<forall>A\<in>F. \<forall>B\<in>F. A \<noteq> B \<longrightarrow> A \<inter> B \<subseteq> {p}"
      and hdr: "\<forall>A\<in>F - {A0}. top1_deformation_retract_of_on A (subspace_topology X TX A) {p}"
  shows "top1_deformation_retract_of_on X TX A0"
proof -
  have hTX_is: "is_topology_on X TX"
    using hTX unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>Y = \<Union>(F - {A0}). X = A0 \<union> Y.\<close>
  define Y where "Y = \<Union>(F - {A0})"
  have hX_eq: "X = A0 \<union> Y" using hcover hA0 Y_def by (by100 auto)
  have hA0_sub: "A0 \<subseteq> X" using hX_eq by (by100 blast)
  have hY_sub: "Y \<subseteq> X" using hX_eq by (by100 blast)
  have hA0_closed: "closedin_on X TX A0" using hF_closed hA0 by (by100 blast)
  have hY_closed: "closedin_on X TX Y"
  proof -
    have "\<forall>A\<in>F - {A0}. closedin_on X TX A" using hF_closed by (by100 blast)
    hence "\<forall>A\<in>(F - {A0}). closedin_on X TX A" by (by100 blast)
    moreover have "finite (F - {A0})" using hfin by (by100 simp)
    ultimately show ?thesis unfolding Y_def
      using closedin_on_finite_Union[OF hTX_is] by (by100 blast)
  qed
  show ?thesis
  proof (cases "F - {A0} = {}")
    case True
    \<comment> \<open>F = {A0}. X = A0. Identity is deformation retract.\<close>
    hence "Y = {}" unfolding Y_def using True by (by100 auto)
    hence "X = A0" using hX_eq by (by100 blast)
    show ?thesis unfolding \<open>X = A0\<close> top1_deformation_retract_of_on_def
    proof (intro conjI)
      show "A0 \<subseteq> A0" by (by100 blast)
      show "\<exists>H. top1_continuous_map_on (A0 \<times> I_set) (product_topology_on TX I_top) A0 TX H
          \<and> (\<forall>x\<in>A0. H (x, 0) = x) \<and> (\<forall>x\<in>A0. H (x, 1) \<in> A0)
          \<and> (\<forall>a\<in>A0. \<forall>t\<in>I_set. H (a, t) = a)"
      proof (rule exI[of _ "\<lambda>p. fst p"])
        have hTX_is: "is_topology_on X TX"
          using hTX unfolding is_topology_on_strict_def by (by100 blast)
        have hTI: "is_topology_on I_set I_top"
          by (rule top1_unit_interval_topology_is_topology_on)
        \<comment> \<open>X = A0, so TX is a topology on A0.\<close>
        have "top1_continuous_map_on (A0 \<times> I_set) (product_topology_on TX I_top) A0 TX fst"
        proof -
          have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX pi1"
            by (rule top1_continuous_pi1[OF hTX_is hTI])
          thus ?thesis unfolding \<open>X = A0\<close> pi1_def by (by100 simp)
        qed
        thus "top1_continuous_map_on (A0 \<times> I_set) (product_topology_on TX I_top) A0 TX (\<lambda>p. fst p)
            \<and> (\<forall>x\<in>A0. fst (x, (0::real)) = x) \<and> (\<forall>x\<in>A0. fst (x, (1::real)) \<in> A0)
            \<and> (\<forall>a\<in>A0. \<forall>t\<in>I_set. fst (a, t) = a)"
          by (by100 simp)
      qed
    qed
  next
    case False
    \<comment> \<open>F - {A0} \<noteq> \<emptyset>. Y \<noteq> \<emptyset>.\<close>
  \<comment> \<open>Y deformation-retracts to {p} by pasting\_deformation\_retracts\_to\_point.\<close>
  have hY_dr: "top1_deformation_retract_of_on Y (subspace_topology X TX Y) {p}"
  proof -
    let ?TY = "subspace_topology X TX Y"
    have hTY_strict: "is_topology_on_strict Y ?TY"
      by (rule subspace_topology_is_strict[OF hTX hY_sub])
    have hF0_closed_Y: "\<forall>A\<in>F - {A0}. closedin_on Y ?TY A"
    proof (intro ballI)
      fix B assume "B \<in> F - {A0}"
      have "closedin_on X TX B" using hF_closed \<open>B \<in> F - {A0}\<close> by (by100 blast)
      have "B \<subseteq> Y" using \<open>B \<in> F - {A0}\<close> Y_def by (by100 blast)
      hence "B = B \<inter> Y" by (by100 blast)
      thus "closedin_on Y ?TY B"
        using iffD2[OF Theorem_17_2[OF hTX_is hY_sub]] \<open>closedin_on X TX B\<close>
        by (by100 blast)
    qed
    have hp_all_F0: "\<forall>A\<in>F - {A0}. p \<in> A" using hp_all by (by100 blast)
    have hp_Y: "p \<in> Y"
    proof -
      from False obtain B where "B \<in> F - {A0}" by (by100 blast)
      hence "p \<in> B" using hp_all_F0 by (by100 blast)
      thus ?thesis unfolding Y_def using \<open>B \<in> F - {A0}\<close> by (by100 blast)
    qed
    have hpairwise_F0: "\<forall>A\<in>F - {A0}. \<forall>B\<in>F - {A0}. A \<noteq> B \<longrightarrow> A \<inter> B = {p}"
    proof (intro ballI impI)
      fix A B assume "A \<in> F - {A0}" "B \<in> F - {A0}" "A \<noteq> B"
      hence "A \<in> F" "B \<in> F" by (by100 blast)+
      from hpairwise \<open>A \<in> F\<close> \<open>B \<in> F\<close> \<open>A \<noteq> B\<close>
      have "A \<inter> B \<subseteq> {p}" by (by100 blast)
      moreover have "p \<in> A \<inter> B" using hp_all_F0 \<open>A \<in> F - {A0}\<close> \<open>B \<in> F - {A0}\<close> by (by100 blast)
      ultimately show "A \<inter> B = {p}" by (by100 blast)
    qed
    have hdr_F0: "\<forall>A\<in>F - {A0}. top1_deformation_retract_of_on A (subspace_topology Y ?TY A) {p}"
    proof (intro ballI)
      fix B assume "B \<in> F - {A0}"
      have "top1_deformation_retract_of_on B (subspace_topology X TX B) {p}"
        using hdr \<open>B \<in> F - {A0}\<close> by (by100 blast)
      moreover have "B \<subseteq> Y" using \<open>B \<in> F - {A0}\<close> Y_def by (by100 blast)
      hence "subspace_topology Y ?TY B = subspace_topology X TX B"
        by (rule subspace_topology_trans)
      ultimately show "top1_deformation_retract_of_on B (subspace_topology Y ?TY B) {p}"
        by (by100 simp)
    qed
    have "finite (F - {A0})" using hfin by (by100 simp)
    have "Y = \<Union>(F - {A0})" unfolding Y_def ..
    show ?thesis
      by (rule pasting_deformation_retracts_to_point[OF hTY_strict \<open>finite (F - {A0})\<close>
          hF0_closed_Y \<open>Y = \<Union>(F - {A0})\<close> hp_Y hp_all_F0 hpairwise_F0 hdr_F0])
  qed
  \<comment> \<open>Paste: identity on A0, retraction on Y.
     Same construction as pasting\_deformation\_retracts\_to\_point but target is A0.\<close>
  \<comment> \<open>Extract HY from hY\_dr.\<close>
  have hY_dr_ex: "\<exists>HY. top1_continuous_map_on (Y \<times> I_set)
        (product_topology_on (subspace_topology X TX Y) I_top) Y (subspace_topology X TX Y) HY
      \<and> (\<forall>x\<in>Y. HY (x, 0) = x) \<and> (\<forall>x\<in>Y. HY (x, 1) \<in> {p})
      \<and> (\<forall>a\<in>{p}. \<forall>t\<in>I_set. HY (a, t) = a)"
    using hY_dr unfolding top1_deformation_retract_of_on_def by (by100 blast)
  then obtain HY where hHY: "top1_continuous_map_on (Y \<times> I_set)
        (product_topology_on (subspace_topology X TX Y) I_top) Y (subspace_topology X TX Y) HY
      \<and> (\<forall>x\<in>Y. HY (x, 0) = x) \<and> (\<forall>x\<in>Y. HY (x, 1) \<in> {p})
      \<and> (\<forall>a\<in>{p}. \<forall>t\<in>I_set. HY (a, t) = a)"
    by (by5000 auto)
  \<comment> \<open>Define H: identity on A0, HY on Y.\<close>
  define H where "H = (\<lambda>(x, t). if x \<in> A0 then x else HY (x, t))"
  show ?thesis unfolding top1_deformation_retract_of_on_def
  proof (intro conjI)
    show "A0 \<subseteq> X" by (rule hA0_sub)
    show "\<exists>Hmap. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX Hmap
        \<and> (\<forall>x\<in>X. Hmap (x, 0) = x) \<and> (\<forall>x\<in>X. Hmap (x, 1) \<in> A0)
        \<and> (\<forall>a\<in>A0. \<forall>t\<in>I_set. Hmap (a, t) = a)"
    proof (rule exI[of _ H])
      have hH_0: "\<forall>x\<in>X. H (x, 0) = x"
      proof (intro ballI)
        fix x assume "x \<in> X"
        show "H (x, 0) = x"
        proof (cases "x \<in> A0")
          case True thus ?thesis unfolding H_def by (by100 simp)
        next
          case False hence "x \<in> Y" using \<open>x \<in> X\<close> hX_eq by (by100 blast)
          thus ?thesis unfolding H_def using False hHY by (by100 force)
        qed
      qed
      have hH_1: "\<forall>x\<in>X. H (x, 1) \<in> A0"
      proof (intro ballI)
        fix x assume "x \<in> X"
        show "H (x, 1) \<in> A0"
        proof (cases "x \<in> A0")
          case True thus ?thesis unfolding H_def by (by100 simp)
        next
          case False hence "x \<in> Y" using \<open>x \<in> X\<close> hX_eq by (by100 blast)
          have "H (x, 1) = HY (x, 1)" unfolding H_def using False by (by100 simp)
          have "(\<forall>y\<in>Y. HY (y, 1) \<in> {p})" using hHY by (by100 blast)
          hence "HY (x, 1) \<in> {p}" using \<open>x \<in> Y\<close> by (by100 blast)
          hence "HY (x, 1) = p" by (by100 blast)
          thus ?thesis using \<open>H (x, 1) = HY (x, 1)\<close> hp by (by100 simp)
        qed
      qed
      have hH_fix: "\<forall>a\<in>A0. \<forall>t\<in>I_set. H (a, t) = a"
        unfolding H_def by (by100 simp)
      have hH_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H"
      proof -
        let ?TXI = "product_topology_on TX I_top"
        have hTX_is: "is_topology_on X TX"
          using hTX unfolding is_topology_on_strict_def by (by100 blast)
        have hTI: "is_topology_on I_set I_top"
          by (rule top1_unit_interval_topology_is_topology_on)
        have hTXI: "is_topology_on (X \<times> I_set) ?TXI"
          by (rule product_topology_on_is_topology_on[OF hTX_is hTI])
        \<comment> \<open>A0\<times>I, Y\<times>I closed.\<close>
        have hA0I_closed: "closedin_on (X \<times> I_set) ?TXI (A0 \<times> I_set)"
        proof -
          have "(X \<times> I_set) - (A0 \<times> I_set) = (X - A0) \<times> I_set" by (by100 blast)
          moreover have "X - A0 \<in> TX" using hA0_closed unfolding closedin_on_def by (by100 blast)
          moreover have "I_set \<in> I_top"
            using hTI unfolding is_topology_on_def by (by100 blast)
          ultimately have "(X \<times> I_set) - (A0 \<times> I_set) \<in> ?TXI"
            using product_rect_open by (by100 simp)
          moreover have "A0 \<times> I_set \<subseteq> X \<times> I_set" using hA0_sub by (by100 blast)
          ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
        qed
        have hYI_closed: "closedin_on (X \<times> I_set) ?TXI (Y \<times> I_set)"
        proof -
          have "(X \<times> I_set) - (Y \<times> I_set) = (X - Y) \<times> I_set" by (by100 blast)
          moreover have "X - Y \<in> TX" using hY_closed unfolding closedin_on_def by (by100 blast)
          moreover have "I_set \<in> I_top"
            using hTI unfolding is_topology_on_def by (by100 blast)
          ultimately have "(X \<times> I_set) - (Y \<times> I_set) \<in> ?TXI"
            using product_rect_open by (by100 simp)
          moreover have "Y \<times> I_set \<subseteq> X \<times> I_set" using hY_sub by (by100 blast)
          ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
        qed
        have hAYI_cover: "A0 \<times> I_set \<union> Y \<times> I_set = X \<times> I_set"
          using hX_eq by (by100 blast)
        \<comment> \<open>H range.\<close>
        have hH_range: "\<forall>p\<in>X \<times> I_set. H p \<in> X"
        proof (intro ballI)
          fix pt assume "pt \<in> X \<times> I_set"
          then obtain x t where hpt: "pt = (x, t)" "x \<in> X" "t \<in> I_set" by (by100 blast)
          show "H pt \<in> X"
          proof (cases "x \<in> A0")
            case True
            have "H pt = x" unfolding H_def hpt using True by (by100 simp)
            thus ?thesis using \<open>x \<in> X\<close> by (by100 simp)
          next
            case False
            hence "x \<in> Y" using \<open>x \<in> X\<close> hX_eq by (by100 blast)
            have "H pt = HY (x, t)" unfolding H_def hpt using False by (by100 simp)
            have "HY (x, t) \<in> Y"
            proof -
              have "top1_continuous_map_on (Y \<times> I_set)
                  (product_topology_on (subspace_topology X TX Y) I_top) Y (subspace_topology X TX Y) HY"
                using hHY by (by100 blast)
              hence "\<forall>q\<in>Y \<times> I_set. HY q \<in> Y" unfolding top1_continuous_map_on_def by (by100 blast)
              thus ?thesis using \<open>x \<in> Y\<close> \<open>t \<in> I_set\<close> by (by100 blast)
            qed
            hence "HY (x, t) \<in> X" using hY_sub by (by100 blast)
            thus ?thesis using \<open>H pt = HY (x, t)\<close> by (by100 simp)
          qed
        qed
        \<comment> \<open>Subspace/product topology facts.\<close>
        have hI_strict: "I_top \<subseteq> Pow I_set"
        proof -
          have "is_topology_on_strict (UNIV :: real set) top1_open_sets"
            unfolding is_topology_on_strict_def
            using top1_open_sets_is_topology_on_UNIV by (by100 blast)
          hence "is_topology_on_strict I_set I_top"
            unfolding top1_unit_interval_topology_def
            by (rule subspace_topology_is_strict) (by100 blast)
          thus ?thesis unfolding is_topology_on_strict_def by (by100 blast)
        qed
        have hI_self: "subspace_topology I_set I_top I_set = I_top"
        proof (rule subspace_topology_self)
          show "\<forall>U\<in>I_top. U \<subseteq> I_set" using hI_strict by (by100 blast)
        qed
        have hA0_sub_eq: "subspace_topology (X \<times> I_set) ?TXI (A0 \<times> I_set)
            = product_topology_on (subspace_topology X TX A0) I_top"
        proof -
          have "product_topology_on (subspace_topology X TX A0) (subspace_topology I_set I_top I_set)
              = subspace_topology (X \<times> I_set) ?TXI (A0 \<times> I_set)"
            by (rule Theorem_16_3[OF hTX_is hTI])
          thus ?thesis using hI_self by (by100 simp)
        qed
        \<comment> \<open>H on A0\<times>I: agrees with fst (identity), which is continuous.\<close>
        have hH_eq_fst: "\<forall>p\<in>A0 \<times> I_set. fst p = H p"
          unfolding H_def by (by100 auto)
        have hfst_cont_A0: "top1_continuous_map_on (A0 \<times> I_set)
            (product_topology_on (subspace_topology X TX A0) I_top) X TX fst"
        proof -
          have "top1_continuous_map_on (A0 \<times> I_set)
              (product_topology_on (subspace_topology X TX A0) I_top)
              A0 (subspace_topology X TX A0) fst"
          proof -
            have "top1_continuous_map_on (A0 \<times> I_set)
                (product_topology_on (subspace_topology X TX A0) I_top)
                A0 (subspace_topology X TX A0) pi1"
              by (rule top1_continuous_pi1[OF subspace_topology_is_topology_on[OF hTX_is hA0_sub] hTI])
            thus ?thesis unfolding pi1_def by (by100 simp)
          qed
          thus ?thesis
            using Theorem_18_2(6)[OF
              product_topology_on_is_topology_on[OF subspace_topology_is_topology_on[OF hTX_is hA0_sub] hTI]
              subspace_topology_is_topology_on[OF hTX_is hA0_sub]
              hTX_is, rule_format]
            hA0_sub by (by100 blast)
        qed
        have hH_on_A0: "top1_continuous_map_on (A0 \<times> I_set)
            (subspace_topology (X \<times> I_set) ?TXI (A0 \<times> I_set)) X TX H"
        proof -
          have "top1_continuous_map_on (A0 \<times> I_set)
              (product_topology_on (subspace_topology X TX A0) I_top) X TX H"
            by (rule top1_continuous_map_on_agree[OF hfst_cont_A0 hH_eq_fst])
          thus ?thesis using hA0_sub_eq by (by100 simp)
        qed
        \<comment> \<open>H on Y\<times>I: agrees with HY, which is continuous Y\<times>I \<rightarrow> Y \<subseteq> X.\<close>
        have hY_sub_eq: "subspace_topology (X \<times> I_set) ?TXI (Y \<times> I_set)
            = product_topology_on (subspace_topology X TX Y) I_top"
        proof -
          have "product_topology_on (subspace_topology X TX Y) (subspace_topology I_set I_top I_set)
              = subspace_topology (X \<times> I_set) ?TXI (Y \<times> I_set)"
            by (rule Theorem_16_3[OF hTX_is hTI])
          thus ?thesis using hI_self by (by100 simp)
        qed
        have hH_eq_HY: "\<forall>p\<in>Y \<times> I_set. HY p = H p"
        proof (intro ballI)
          fix pt assume "pt \<in> Y \<times> I_set"
          then obtain x t where hpt: "pt = (x, t)" "x \<in> Y" "t \<in> I_set" by (by100 blast)
          show "HY pt = H pt"
          proof (cases "x \<in> A0")
            case True
            have "x \<in> Y" using \<open>x \<in> Y\<close> .
            then obtain B where "B \<in> F - {A0}" "x \<in> B" unfolding Y_def by (by100 blast)
            hence "B \<in> F" "A0 \<noteq> B" by (by100 blast)+
            hence "A0 \<inter> B \<subseteq> {p}" using hpairwise hA0 by (by100 blast)
            hence "x = p" using True \<open>x \<in> B\<close> by (by100 blast)
            have hHY_fix: "\<forall>a\<in>{p}. \<forall>t\<in>I_set. HY (a, t) = a" using hHY by (by100 blast)
            have "HY pt = p" using hHY_fix \<open>x = p\<close> \<open>t \<in> I_set\<close> hpt by (by100 simp)
            moreover have "H pt = p" unfolding H_def hpt using True \<open>x = p\<close> by (by100 simp)
            ultimately show ?thesis by (by100 simp)
          next
            case False
            show ?thesis unfolding H_def hpt using False by (by100 simp)
          qed
        qed
        have hHY_cont_X: "top1_continuous_map_on (Y \<times> I_set)
            (product_topology_on (subspace_topology X TX Y) I_top) X TX HY"
        proof -
          have hHY_cont: "top1_continuous_map_on (Y \<times> I_set)
              (product_topology_on (subspace_topology X TX Y) I_top)
              Y (subspace_topology X TX Y) HY"
            using hHY by (by100 blast)
          thus ?thesis
            using Theorem_18_2(6)[OF
              product_topology_on_is_topology_on[OF subspace_topology_is_topology_on[OF hTX_is hY_sub] hTI]
              subspace_topology_is_topology_on[OF hTX_is hY_sub]
              hTX_is, rule_format]
            hY_sub by (by100 blast)
        qed
        have hH_on_Y: "top1_continuous_map_on (Y \<times> I_set)
            (subspace_topology (X \<times> I_set) ?TXI (Y \<times> I_set)) X TX H"
        proof -
          have "top1_continuous_map_on (Y \<times> I_set)
              (product_topology_on (subspace_topology X TX Y) I_top) X TX H"
            by (rule top1_continuous_map_on_agree[OF hHY_cont_X hH_eq_HY])
          thus ?thesis using hY_sub_eq by (by100 simp)
        qed
        show ?thesis
          by (rule pasting_lemma_two_closed[OF hTXI hTX_is hA0I_closed hYI_closed hAYI_cover hH_range hH_on_A0 hH_on_Y])
      qed
      show "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H
          \<and> (\<forall>x\<in>X. H (x, 0) = x) \<and> (\<forall>x\<in>X. H (x, 1) \<in> A0)
          \<and> (\<forall>a\<in>A0. \<forall>t\<in>I_set. H (a, t) = a)"
        using hH_cont hH_0 hH_1 hH_fix by (by100 blast)
    qed
  qed
  qed
qed

text \<open>Deformation retraction to a singleton implies simply connected.
  Expert review Step 2: reusable lemma for deriving simply connected
  from deformation retraction to a point.\<close>
lemma deformation_retract_to_singleton_imp_simply_connected:
  assumes hTX: "is_topology_on X TX"
      and hp: "p \<in> X"
      and hpc: "top1_path_connected_on X TX"
      and hdr: "top1_deformation_retract_of_on X TX {p}"
  shows "top1_simply_connected_on X TX"
proof (rule top1_simply_connected_from_one_point[OF hTX hpc hp])
  show "\<forall>f. top1_is_loop_on X TX p f \<longrightarrow>
      top1_path_homotopic_on X TX p p f (top1_constant_path p)"
  proof (intro allI impI)
    fix f assume hloop: "top1_is_loop_on X TX p f"
    \<comment> \<open>Extract the deformation retraction homotopy H.\<close>
    have hdr': "{p} \<subseteq> X \<and> (\<exists>H. top1_continuous_map_on (X \<times> I_set)
          (product_topology_on TX I_top) X TX H
        \<and> (\<forall>x\<in>X. H (x, 0) = x) \<and> (\<forall>x\<in>X. H (x, 1) \<in> {p})
        \<and> (\<forall>a\<in>{p}. \<forall>t\<in>I_set. H (a, t) = a))"
      using hdr unfolding top1_deformation_retract_of_on_def by (by100 blast)
    then obtain H where hH_all: "top1_continuous_map_on (X \<times> I_set)
          (product_topology_on TX I_top) X TX H
        \<and> (\<forall>x\<in>X. H (x, 0) = x) \<and> (\<forall>x\<in>X. H (x, 1) \<in> {p})
        \<and> (\<forall>a\<in>{p}. \<forall>t\<in>I_set. H (a, t) = a)"
      by (by5000 auto)
    have hH_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H"
      using hH_all by (by100 blast)
    have hH_0: "\<forall>x\<in>X. H (x, 0) = x" using hH_all by (by100 blast)
    have hH_1: "\<forall>x\<in>X. H (x, 1) \<in> {p}" using hH_all by (by100 blast)
    have hH_fix: "\<forall>a\<in>{p}. \<forall>t\<in>I_set. H (a, t) = a" using hH_all by (by100 blast)
    \<comment> \<open>Define G(s,t) = H(f(s), t). This is the null-homotopy.\<close>
    define G where "G = (\<lambda>(s, t). H (f s, t))"
    \<comment> \<open>G is continuous: composition of H with (f \<times> id).\<close>
    have hG_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX G"
    proof -
      \<comment> \<open>G = H \<circ> (\<lambda>(s,t). (f s, t)). Show (\<lambda>(s,t). (f s, t)) : I\<times>I \<rightarrow> X\<times>I continuous,
         then compose with H.\<close>
      have hTI: "is_topology_on I_set I_top"
        by (rule top1_unit_interval_topology_is_topology_on)
      have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
        using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      \<comment> \<open>The map (s,t) \<mapsto> (f(s), t) : I\<times>I \<rightarrow> X\<times>I is continuous.
         By Theorem\_18\_4: continuous into product iff each projection is.\<close>
      define fid where "fid = (\<lambda>(s::real, t::real). (f s, t))"
      have hfid_cont: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
          (X \<times> I_set) (product_topology_on TX I_top) fid"
      proof -
        have "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
            (X \<times> I_set) (product_topology_on TX I_top) fid \<longleftrightarrow>
          (top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX (pi1 \<circ> fid) \<and>
           top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top (pi2 \<circ> fid))"
          by (rule Theorem_18_4[OF product_topology_on_is_topology_on[OF hTI hTI] hTX hTI])
        moreover have "pi1 \<circ> fid = f \<circ> pi1"
          unfolding pi1_def fid_def comp_def by (by100 auto)
        moreover have "pi2 \<circ> fid = pi2"
          unfolding pi2_def fid_def comp_def by (by100 auto)
        moreover have "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX (f \<circ> pi1)"
          by (rule top1_continuous_map_on_comp[OF top1_continuous_pi1[OF hTI hTI] hf_cont])
        moreover have "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top pi2"
          by (rule top1_continuous_pi2[OF hTI hTI])
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>G = H \<circ> fid.\<close>
      \<comment> \<open>G = H \<circ> fid pointwise on I\<times>I. Show (H \<circ> fid) continuous then transfer.\<close>
      have "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
          X TX (H \<circ> fid)"
        by (rule top1_continuous_map_on_comp[OF hfid_cont hH_cont])
      moreover have "\<forall>p\<in>I_set \<times> I_set. (H \<circ> fid) p = G p"
      proof (intro ballI)
        fix p assume hp: "p \<in> I_set \<times> I_set"
        then obtain s t where hst: "p = (s, t)" "s \<in> I_set" "t \<in> I_set" by (by100 blast)
        show "(H \<circ> fid) p = G p"
          unfolding comp_def fid_def G_def using hst by (by100 simp)
      qed
      ultimately show ?thesis unfolding II_topology_def
        by (rule top1_continuous_map_on_agree)
    qed
    \<comment> \<open>Boundary conditions.\<close>
    have hf_range: "\<forall>s\<in>I_set. f s \<in> X"
      using hloop unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def
      by (by100 blast)
    have hG_s0: "\<forall>s\<in>I_set. G (s, 0) = f s"
      unfolding G_def using hH_0 hf_range by (by100 simp)
    have hG_s1: "\<forall>s\<in>I_set. G (s, 1) = p"
      unfolding G_def using hH_1 hf_range by (by100 force)
    have hG_0t: "\<forall>t\<in>I_set. G (0, t) = p"
    proof (intro ballI)
      fix t assume "t \<in> I_set"
      have "f 0 = p" using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      thus "G (0, t) = p" unfolding G_def using hH_fix \<open>t \<in> I_set\<close> by (by100 simp)
    qed
    have hG_1t: "\<forall>t\<in>I_set. G (1, t) = p"
    proof (intro ballI)
      fix t assume "t \<in> I_set"
      have "f 1 = p" using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      thus "G (1, t) = p" unfolding G_def using hH_fix \<open>t \<in> I_set\<close> by (by100 simp)
    qed
    show "top1_path_homotopic_on X TX p p f (top1_constant_path p)"
      unfolding top1_path_homotopic_on_def
    proof (intro conjI)
      show "top1_is_path_on X TX p p f"
        using hloop unfolding top1_is_loop_on_def by (by100 blast)
      show "top1_is_path_on X TX p p (top1_constant_path p)"
        by (rule top1_constant_path_is_path[OF hTX hp])
      show "\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F \<and>
          (\<forall>s\<in>I_set. F (s, 0) = f s) \<and> (\<forall>s\<in>I_set. F (s, 1) = top1_constant_path p s) \<and>
          (\<forall>t\<in>I_set. F (0, t) = p) \<and> (\<forall>t\<in>I_set. F (1, t) = p)"
      proof (rule exI[of _ G], intro conjI)
        show "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX G" by (rule hG_cont)
        show "\<forall>s\<in>I_set. G (s, 0) = f s" by (rule hG_s0)
        have hcp: "top1_constant_path p = (\<lambda>_. p)" unfolding top1_constant_path_def by (by100 simp)
        show "\<forall>s\<in>I_set. G (s, 1) = top1_constant_path p s"
          using hG_s1 hcp by (by100 simp)
        show "\<forall>t\<in>I_set. G (0, t) = p" by (rule hG_0t)
        show "\<forall>t\<in>I_set. G (1, t) = p" by (rule hG_1t)
      qed
    qed
  qed
qed

text \<open>Homeomorphisms map open sets to open sets (the image is open).\<close>
lemma homeomorphism_image_open:
  assumes hhomeo: "top1_homeomorphism_on X TX Y TY f"
      and hU: "U \<in> TX" and hUX: "U \<subseteq> X"
  shows "f ` U \<in> TY"
proof -
  have hbij: "bij_betw f X Y"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hinv_cont: "top1_continuous_map_on Y TY X TX (inv_into X f)"
    using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hpre: "{y \<in> Y. inv_into X f y \<in> U} \<in> TY"
    using continuous_map_preimage_open[OF hinv_cont hU] by (by100 blast)
  have hpre_eq: "{y \<in> Y. inv_into X f y \<in> U} = f ` U"
  proof (rule set_eqI, rule iffI)
    fix y assume "y \<in> {y \<in> Y. inv_into X f y \<in> U}"
    hence "y \<in> Y" "inv_into X f y \<in> U" by (by100 blast)+
    have "inv_into X f y \<in> X"
      using \<open>inv_into X f y \<in> U\<close> hUX by (by100 blast)
    hence "f (inv_into X f y) = y"
      using f_inv_into_f[of y f X] bij_betw_imp_surj_on[OF hbij] \<open>y \<in> Y\<close>
      by (by100 blast)
    have "f (inv_into X f y) \<in> f ` U"
      using \<open>inv_into X f y \<in> U\<close> by (by100 blast)
    thus "y \<in> f ` U"
      using \<open>f (inv_into X f y) = y\<close> by (by100 simp)
  next
    fix y assume "y \<in> f ` U"
    then obtain x where "x \<in> U" "y = f x" by (by100 blast)
    have "x \<in> X" using \<open>x \<in> U\<close> hUX by (by100 blast)
    have "y \<in> Y" using bij_betw_apply[OF hbij \<open>x \<in> X\<close>] \<open>y = f x\<close> by (by100 blast)
    have "inv_into X f y = x"
      using inv_into_f_f[OF bij_betw_imp_inj_on[OF hbij] \<open>x \<in> X\<close>] \<open>y = f x\<close>
      by (by100 simp)
    thus "y \<in> {y \<in> Y. inv_into X f y \<in> U}" using \<open>y \<in> Y\<close> \<open>x \<in> U\<close> by (by100 blast)
  qed
  thus ?thesis using hpre by (by100 simp)
qed

text \<open>Covering maps are open maps.
  For V open in E, p(V) is open in B.
  Proof: for each b \<in> p(V), take evenly covered U \<ni> b.
  The sheet W containing a point of V\<inter>p^{-1}(b) maps W homeo U.
  p(V\<inter>W) open in U (homeo maps open to open), hence open in B.\<close>
lemma covering_map_is_open_map:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and hTE: "is_topology_on_strict E TE"
      and hTB: "is_topology_on B TB"
      and hV: "V \<in> TE"
  shows "p ` V \<in> TB"
proof -
  have hTE_top: "is_topology_on E TE"
    using hTE unfolding is_topology_on_strict_def by (by100 blast)
  have hVE: "V \<subseteq> E" using hV hTE unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>For each b in p(V), find an open neighborhood of b inside p(V).\<close>
  have "\<forall>b \<in> p ` V. \<exists>O_b \<in> TB. b \<in> O_b \<and> O_b \<subseteq> p ` V"
  proof
    fix b assume "b \<in> p ` V"
    then obtain e where "e \<in> V" "p e = b" by (by100 blast)
    have "e \<in> E" using \<open>e \<in> V\<close> hVE by (by100 blast)
    have "b \<in> B"
      using continuous_map_maps_to[OF top1_covering_map_on_continuous[OF hcov] \<open>e \<in> E\<close>]
            \<open>p e = b\<close> by (by100 simp)
    \<comment> \<open>Get evenly covered neighborhood of b.\<close>
    obtain U where "b \<in> U" and hec: "top1_evenly_covered_on E TE B TB p U"
      using top1_covering_map_on_evenly_covered[OF hcov \<open>b \<in> B\<close>] by (by100 blast)
    have hU_open: "openin_on B TB U"
      by (rule top1_evenly_covered_on_openin_on[OF hec])
    have hU_TB: "U \<in> TB" using hU_open unfolding openin_on_def by (by100 blast)
    have hU_B: "U \<subseteq> B" using hU_open unfolding openin_on_def by (by100 blast)
    \<comment> \<open>Get the sheets.\<close>
    have hec_full: "openin_on B TB U \<and>
      (\<exists>\<V>. (\<forall>V\<in>\<V>. openin_on E TE V) \<and>
           (\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}) \<and>
           {x\<in>E. p x \<in> U} = \<Union>\<V> \<and>
           (\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                        (subspace_topology B TB U) p))"
      using hec unfolding top1_evenly_covered_on_def .
    have hex: "\<exists>\<V>. (\<forall>V\<in>\<V>. openin_on E TE V) \<and>
           (\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}) \<and>
           {x\<in>E. p x \<in> U} = \<Union>\<V> \<and>
           (\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                        (subspace_topology B TB U) p)"
      using hec_full by (by100 blast)
    then obtain \<V> where hall: "(\<forall>V\<in>\<V>. openin_on E TE V) \<and>
           (\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}) \<and>
           {x\<in>E. p x \<in> U} = \<Union>\<V> \<and>
           (\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                        (subspace_topology B TB U) p)"
      apply (rule exE)
      apply (by100 blast)
      done
    have hV_open: "\<forall>W\<in>\<V>. openin_on E TE W" using hall by (by100 blast)
    have hV_union: "{x\<in>E. p x \<in> U} = \<Union>\<V>" using hall by (by100 blast)
    have hV_homeo: "\<forall>W\<in>\<V>. top1_homeomorphism_on W (subspace_topology E TE W) U
                       (subspace_topology B TB U) p" using hall by (by100 blast)
    \<comment> \<open>e is in some sheet W.\<close>
    have "e \<in> {x\<in>E. p x \<in> U}" using \<open>e \<in> E\<close> \<open>p e = b\<close> \<open>b \<in> U\<close> by (by100 blast)
    hence "e \<in> \<Union>\<V>" using hV_union by (by100 simp)
    then obtain W where "W \<in> \<V>" "e \<in> W" by (by100 blast)
    have hW_open: "W \<in> TE" using hV_open \<open>W \<in> \<V>\<close> unfolding openin_on_def by (by100 blast)
    have hW_E: "W \<subseteq> E" using hV_open \<open>W \<in> \<V>\<close> unfolding openin_on_def by (by100 blast)
    have hW_homeo: "top1_homeomorphism_on W (subspace_topology E TE W) U
                       (subspace_topology B TB U) p"
      using hV_homeo \<open>W \<in> \<V>\<close> by (by100 blast)
    \<comment> \<open>V \<inter> W is open in the subspace topology on W.\<close>
    have hVW_sub: "V \<inter> W \<in> subspace_topology E TE W"
      unfolding subspace_topology_def using hV by (by100 blast)
    have hVW_W: "V \<inter> W \<subseteq> W" by (by100 blast)
    \<comment> \<open>Homeomorphism maps V\<inter>W to an open subset of U.\<close>
    have hpVW_open: "p ` (V \<inter> W) \<in> subspace_topology B TB U"
      using homeomorphism_image_open[OF hW_homeo hVW_sub hVW_W] by (by100 blast)
    \<comment> \<open>Lift from subspace topology to TB.\<close>
    obtain O' where "O' \<in> TB" "p ` (V \<inter> W) = U \<inter> O'"
      using hpVW_open unfolding subspace_topology_def by (by100 blast)
    have hpVW_TB: "p ` (V \<inter> W) \<in> TB"
    proof -
      have "U \<inter> O' \<in> TB"
        using topology_inter2[OF hTB hU_TB \<open>O' \<in> TB\<close>] by (by100 blast)
      thus ?thesis using \<open>p ` (V \<inter> W) = U \<inter> O'\<close> by (by100 simp)
    qed
    have hb_in: "b \<in> p ` (V \<inter> W)"
      using \<open>e \<in> V\<close> \<open>e \<in> W\<close> \<open>p e = b\<close> by (by100 blast)
    have hpVW_sub: "p ` (V \<inter> W) \<subseteq> p ` V" by (by100 blast)
    show "\<exists>O_b \<in> TB. b \<in> O_b \<and> O_b \<subseteq> p ` V"
      using hpVW_TB hb_in hpVW_sub
      apply (rule_tac x="p ` (V \<inter> W)" in bexI)
      apply (by100 blast)
      by assumption
  qed
  \<comment> \<open>p(V) is a union of open sets in TB.\<close>
  then obtain F where hF: "\<forall>b \<in> p ` V. F b \<in> TB \<and> b \<in> F b \<and> F b \<subseteq> p ` V"
    by (by100 metis)
  have "p ` V = \<Union>(F ` (p ` V))"
  proof (rule set_eqI, rule iffI)
    fix b assume "b \<in> p ` V"
    thus "b \<in> \<Union>(F ` (p ` V))" using hF by (by100 blast)
  next
    fix b assume "b \<in> \<Union>(F ` (p ` V))"
    then obtain b' where "b' \<in> p ` V" "b \<in> F b'" by (by100 blast)
    thus "b \<in> p ` V" using hF by (by100 blast)
  qed
  moreover have "\<Union>(F ` (p ` V)) \<in> TB"
  proof -
    have "\<forall>U. U \<subseteq> TB \<longrightarrow> (\<Union>U) \<in> TB"
      using hTB unfolding is_topology_on_def by (by100 blast)
    moreover have "F ` (p ` V) \<subseteq> TB" using hF by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  ultimately show ?thesis by (by100 simp)
qed

text \<open>R\_to\_S1 restricted to an open interval of length 1 is a homeomorphism
  onto S1 minus the image of the endpoints.\<close>
lemma R_to_S1_interval_homeomorphism:
  shows "top1_homeomorphism_on
      {x. \<theta>q < x \<and> x < \<theta>q + 1}
      (subspace_topology (UNIV :: real set) top1_open_sets {x. \<theta>q < x \<and> x < \<theta>q + 1})
      (top1_S1 - {top1_R_to_S1 \<theta>q})
      (subspace_topology top1_S1 top1_S1_topology (top1_S1 - {top1_R_to_S1 \<theta>q}))
      top1_R_to_S1"
proof -
  let ?I = "{x::real. \<theta>q < x \<and> x < \<theta>q + 1}"
  let ?TI = "subspace_topology (UNIV :: real set) top1_open_sets ?I"
  let ?S = "top1_S1 - {top1_R_to_S1 \<theta>q}"
  let ?TS = "subspace_topology top1_S1 top1_S1_topology ?S"
  \<comment> \<open>Topologies.\<close>
  have hTI: "is_topology_on ?I ?TI"
    by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV])
       (by100 blast)
  have hTS: "is_topology_on ?S ?TS"
  proof -
    have "is_topology_on top1_S1 top1_S1_topology"
      using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
    thus ?thesis by (rule subspace_topology_is_topology_on) (by100 blast)
  qed
  \<comment> \<open>Bijectivity.\<close>
  have hbij: "bij_betw top1_R_to_S1 ?I ?S"
    unfolding bij_betw_def
  proof (intro conjI)
    \<comment> \<open>Injective: sin\_cos\_eq\_iff (same as hangle\_prop uniqueness argument).\<close>
    show "inj_on top1_R_to_S1 ?I"
    proof (rule inj_onI)
      fix a b assume "a \<in> ?I" "b \<in> ?I" "top1_R_to_S1 a = top1_R_to_S1 b"
      hence "(cos (2*pi*a), sin (2*pi*a)) = (cos (2*pi*b), sin (2*pi*b))"
        unfolding top1_R_to_S1_def by (by100 simp)
      hence "sin (2*pi*a) = sin (2*pi*b) \<and> cos (2*pi*a) = cos (2*pi*b)" by (by100 simp)
      hence "\<exists>k::int. 2*pi*a = 2*pi*b + 2*pi*of_int k"
        using iffD1[OF sin_cos_eq_iff] by (by100 blast)
      then obtain k :: int where "2*pi*a = 2*pi*b + 2*pi*of_int k" by (by100 blast)
      have "a - b = of_int k"
      proof -
        from \<open>2*pi*a = 2*pi*b + 2*pi*of_int k\<close>
        have "2*pi*a - 2*pi*b = 2*pi*of_int k" by (by100 linarith)
        hence "2*pi*(a - b) = 2*pi*of_int k"
          using right_diff_distrib[of "2*pi" a b] by (by100 linarith)
        moreover have "2*pi \<noteq> (0::real)" using pi_neq_zero by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      moreover have "\<bar>a - b\<bar> < 1"
      proof -
        from \<open>a \<in> ?I\<close> have "\<theta>q < a" "a < \<theta>q + 1" by (by100 simp)+
        from \<open>b \<in> ?I\<close> have "\<theta>q < b" "b < \<theta>q + 1" by (by100 simp)+
        have hab1: "a - b < 1" using \<open>a < \<theta>q + 1\<close> \<open>\<theta>q < b\<close> by (by100 linarith)
        have hab2: "b - a < 1" using \<open>b < \<theta>q + 1\<close> \<open>\<theta>q < a\<close> by (by100 linarith)
        thus ?thesis using hab1 hab2 by (by100 linarith)
      qed
      ultimately have "k = 0" by (by100 linarith)
      thus "a = b" using \<open>a - b = of_int k\<close> by (by100 simp)
    qed
    \<comment> \<open>Surjective onto S1-{q0}: same as \<theta>r existence.\<close>
    show "top1_R_to_S1 ` ?I = ?S"
    proof (rule set_eqI, rule iffI)
      fix s assume "s \<in> top1_R_to_S1 ` ?I"
      then obtain \<theta> where "s = top1_R_to_S1 \<theta>" "\<theta>q < \<theta>" "\<theta> < \<theta>q + 1" by (by100 blast)
      have "s \<in> top1_S1" unfolding \<open>s = top1_R_to_S1 \<theta>\<close> top1_R_to_S1_def top1_S1_def
        by (by100 simp)
      moreover have "s \<noteq> top1_R_to_S1 \<theta>q"
      proof
        assume "s = top1_R_to_S1 \<theta>q"
        hence "top1_R_to_S1 \<theta> = top1_R_to_S1 \<theta>q" using \<open>s = top1_R_to_S1 \<theta>\<close> by (by100 simp)
        hence "\<theta> = \<theta>q"
        proof -
          assume heq: "top1_R_to_S1 \<theta> = top1_R_to_S1 \<theta>q"
          hence "(cos (2*pi*\<theta>), sin (2*pi*\<theta>)) = (cos (2*pi*\<theta>q), sin (2*pi*\<theta>q))"
            unfolding top1_R_to_S1_def by (by100 simp)
          hence "sin (2*pi*\<theta>) = sin (2*pi*\<theta>q) \<and> cos (2*pi*\<theta>) = cos (2*pi*\<theta>q)" by (by100 simp)
          hence "\<exists>k::int. 2*pi*\<theta> = 2*pi*\<theta>q + 2*pi*of_int k"
            using iffD1[OF sin_cos_eq_iff] by (by100 blast)
          then obtain k :: int where "2*pi*\<theta> = 2*pi*\<theta>q + 2*pi*of_int k" by (by100 blast)
          have "\<theta> - \<theta>q = of_int k"
          proof -
            from \<open>2*pi*\<theta> = 2*pi*\<theta>q + 2*pi*of_int k\<close>
            have "2*pi*\<theta> - 2*pi*\<theta>q = 2*pi*of_int k" by (by100 linarith)
            hence "2*pi*(\<theta> - \<theta>q) = 2*pi*of_int k"
              using right_diff_distrib[of "2*pi" \<theta> \<theta>q] by (by100 linarith)
            moreover have "2*pi \<noteq> (0::real)" using pi_neq_zero by (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
          moreover have "\<bar>\<theta> - \<theta>q\<bar> < 1"
            using \<open>\<theta>q < \<theta>\<close> \<open>\<theta> < \<theta>q + 1\<close> by (by100 linarith)
          ultimately have "k = 0" by (by100 linarith)
          thus "\<theta> = \<theta>q" using \<open>\<theta> - \<theta>q = of_int k\<close> by (by100 simp)
        qed
        thus False using \<open>\<theta>q < \<theta>\<close> by (by100 linarith)
      qed
      ultimately show "s \<in> ?S" by (by100 blast)
    next
      fix s assume "s \<in> ?S"
      hence "s \<in> top1_S1" "s \<noteq> top1_R_to_S1 \<theta>q" by (by100 blast)+
      from S1_point_to_angle[OF \<open>s \<in> top1_S1\<close>] obtain \<theta>' where "top1_R_to_S1 \<theta>' = s" by (by100 blast)
      define k where "k = \<lfloor>\<theta>' - \<theta>q\<rfloor>"
      define \<theta>_s where "\<theta>_s = \<theta>' - of_int k"
      have "top1_R_to_S1 \<theta>_s = s"
      proof -
        have "\<theta>_s = \<theta>' + of_int (- k)" unfolding \<theta>_s_def by (by100 simp)
        hence "top1_R_to_S1 \<theta>_s = top1_R_to_S1 (\<theta>' + of_int (- k))" by (by100 simp)
        also have "\<dots> = top1_R_to_S1 \<theta>'" by (rule top1_R_to_S1_int_shift)
        finally show ?thesis using \<open>top1_R_to_S1 \<theta>' = s\<close> by (by100 simp)
      qed
      have "\<theta>q \<le> \<theta>_s" unfolding \<theta>_s_def k_def using floor_le_iff by (by100 linarith)
      have "\<theta>_s < \<theta>q + 1" unfolding \<theta>_s_def k_def using floor_less_iff by (by100 linarith)
      have "\<theta>_s \<noteq> \<theta>q"
      proof
        assume "\<theta>_s = \<theta>q"
        hence "top1_R_to_S1 \<theta>_s = top1_R_to_S1 \<theta>q" by (by100 simp)
        hence "s = top1_R_to_S1 \<theta>q" using \<open>top1_R_to_S1 \<theta>_s = s\<close> by (by100 simp)
        thus False using \<open>s \<noteq> top1_R_to_S1 \<theta>q\<close> by (by100 simp)
      qed
      hence "\<theta>q < \<theta>_s" using \<open>\<theta>q \<le> \<theta>_s\<close> by (by100 linarith)
      hence "\<theta>_s \<in> ?I" using \<open>\<theta>_s < \<theta>q + 1\<close> by (by100 simp)
      thus "s \<in> top1_R_to_S1 ` ?I" using \<open>top1_R_to_S1 \<theta>_s = s\<close> by (by100 blast)
    qed
  qed
  \<comment> \<open>Forward continuity.\<close>
  have hcont: "top1_continuous_map_on ?I ?TI ?S ?TS top1_R_to_S1"
  proof -
    have hR_S1_cont: "top1_continuous_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
      using top1_covering_map_on_continuous[OF Theorem_53_1] by (by100 blast)
    have hI_sub: "?I \<subseteq> (UNIV :: real set)" by (by100 blast)
    have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
      using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
    have hcont_I: "top1_continuous_map_on ?I ?TI top1_S1 top1_S1_topology top1_R_to_S1"
      using Theorem_18_2(4)[OF top1_open_sets_is_topology_on_UNIV
              hS1_top hS1_top] hR_S1_cont hI_sub
      by (by100 blast)
    have hS_sub: "?S \<subseteq> top1_S1" by (by100 blast)
    have himg_sub: "top1_R_to_S1 ` ?I \<subseteq> ?S"
      using bij_betw_imp_surj_on[OF hbij] by (by100 blast)
    show ?thesis
      using Theorem_18_2(5)[OF hTI hS1_top hS1_top]
            hcont_I hS_sub himg_sub
      by (by100 blast)
  qed
  \<comment> \<open>Inverse continuity: use covering\_map\_is\_open\_map to show R\_to\_S1 is open,
     then preimage under inv\_into = image under R\_to\_S1.\<close>
  have hcont_inv: "top1_continuous_map_on ?S ?TS ?I ?TI (inv_into ?I top1_R_to_S1)"
  proof (rule continuous_map_onI)
    \<comment> \<open>Maps ?S to ?I.\<close>
    show "\<forall>s\<in>?S. inv_into ?I top1_R_to_S1 s \<in> ?I"
    proof
      fix s assume "s \<in> ?S"
      hence "s \<in> top1_R_to_S1 ` ?I" using bij_betw_imp_surj_on[OF hbij] by (by100 blast)
      then obtain x where "x \<in> ?I" "top1_R_to_S1 x = s" by (by100 blast)
      have "inv_into ?I top1_R_to_S1 (top1_R_to_S1 x) = x"
        using inv_into_f_f[OF bij_betw_imp_inj_on[OF hbij] \<open>x \<in> ?I\<close>] by (by100 blast)
      hence "inv_into ?I top1_R_to_S1 s = x" using \<open>top1_R_to_S1 x = s\<close> by (by100 simp)
      thus "inv_into ?I top1_R_to_S1 s \<in> ?I" using \<open>x \<in> ?I\<close> by (by100 simp)
    qed
    \<comment> \<open>Preimage of open set V in ?TI is open in ?TS.\<close>
    show "\<forall>V\<in>?TI. {s \<in> ?S. inv_into ?I top1_R_to_S1 s \<in> V} \<in> ?TS"
    proof
      fix V assume "V \<in> ?TI"
      \<comment> \<open>V = Vb \<inter> ?I for some Vb \<in> top1\_open\_sets.\<close>
      obtain Vb where "Vb \<in> top1_open_sets" "V = ?I \<inter> Vb"
        using \<open>V \<in> ?TI\<close> unfolding subspace_topology_def by (by100 blast)
      \<comment> \<open>?I is open in \<real> (open interval).\<close>
      have hI_open: "?I \<in> top1_open_sets"
      proof -
        have "{x::real. \<theta>q < x \<and> x < \<theta>q + 1} = {\<theta>q <..< \<theta>q + 1}"
          by (by100 auto)
        moreover have "open ({\<theta>q <..< \<theta>q + 1} :: real set)" by (by100 simp)
        ultimately show ?thesis unfolding top1_open_sets_def by (by100 simp)
      qed
      have hV_open: "V \<in> top1_open_sets"
        using topology_inter2[OF top1_open_sets_is_topology_on_UNIV hI_open \<open>Vb \<in> top1_open_sets\<close>]
              \<open>V = ?I \<inter> Vb\<close> by (by100 simp)
      \<comment> \<open>R\_to\_S1 maps V (open in \<real>) to an open set in S1 (covering map is open).\<close>
      have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
        using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
      have hopen_strict: "is_topology_on_strict (UNIV :: real set) top1_open_sets"
        using top1_open_sets_is_topology_on_UNIV unfolding is_topology_on_strict_def
        by (by100 blast)
      have hpV_S1: "top1_R_to_S1 ` V \<in> top1_S1_topology"
        using covering_map_is_open_map[OF Theorem_53_1 hopen_strict
                                          hS1_top hV_open] by (by100 blast)
      \<comment> \<open>Image is contained in ?S.\<close>
      have hpV_sub: "top1_R_to_S1 ` V \<subseteq> ?S"
      proof
        fix s assume "s \<in> top1_R_to_S1 ` V"
        then obtain x where "x \<in> V" "s = top1_R_to_S1 x" by (by100 blast)
        have "x \<in> ?I" using \<open>x \<in> V\<close> \<open>V = ?I \<inter> Vb\<close> by (by100 blast)
        thus "s \<in> ?S" using bij_betw_imp_surj_on[OF hbij] \<open>x \<in> ?I\<close> \<open>s = top1_R_to_S1 x\<close>
          by (by100 blast)
      qed
      \<comment> \<open>Preimage under inv\_into equals image under R\_to\_S1 (by bijectivity).\<close>
      have hpre_eq: "{s \<in> ?S. inv_into ?I top1_R_to_S1 s \<in> V} = top1_R_to_S1 ` V"
      proof (rule set_eqI, rule iffI)
        fix s assume "s \<in> {s \<in> ?S. inv_into ?I top1_R_to_S1 s \<in> V}"
        hence "s \<in> ?S" "inv_into ?I top1_R_to_S1 s \<in> V" by (by100 blast)+
        have "inv_into ?I top1_R_to_S1 s \<in> ?I"
          using \<open>inv_into ?I top1_R_to_S1 s \<in> V\<close> \<open>V = ?I \<inter> Vb\<close> by (by100 blast)
        have "top1_R_to_S1 (inv_into ?I top1_R_to_S1 s) = s"
          using f_inv_into_f[of s top1_R_to_S1 ?I]
                bij_betw_imp_surj_on[OF hbij] \<open>s \<in> ?S\<close> by (by100 blast)
        have "top1_R_to_S1 (inv_into ?I top1_R_to_S1 s) \<in> top1_R_to_S1 ` V"
          using \<open>inv_into ?I top1_R_to_S1 s \<in> V\<close> by (by100 blast)
        thus "s \<in> top1_R_to_S1 ` V"
          using \<open>top1_R_to_S1 (inv_into ?I top1_R_to_S1 s) = s\<close> by (by100 simp)
      next
        fix s assume "s \<in> top1_R_to_S1 ` V"
        then obtain x where "x \<in> V" "s = top1_R_to_S1 x" by (by100 blast)
        have "x \<in> ?I" using \<open>x \<in> V\<close> \<open>V = ?I \<inter> Vb\<close> by (by100 blast)
        have "s \<in> ?S" using hpV_sub \<open>s \<in> top1_R_to_S1 ` V\<close> by (by100 blast)
        have "inv_into ?I top1_R_to_S1 s = x"
          using inv_into_f_f[OF bij_betw_imp_inj_on[OF hbij] \<open>x \<in> ?I\<close>]
                \<open>s = top1_R_to_S1 x\<close> by (by100 simp)
        thus "s \<in> {s \<in> ?S. inv_into ?I top1_R_to_S1 s \<in> V}"
          using \<open>s \<in> ?S\<close> \<open>x \<in> V\<close> by (by100 simp)
      qed
      \<comment> \<open>R\_to\_S1 ` V is in ?TS (open in S1, subset of ?S, so in subspace topology).\<close>
      show "{s \<in> ?S. inv_into ?I top1_R_to_S1 s \<in> V} \<in> ?TS"
        unfolding hpre_eq subspace_topology_def
        using hpV_S1 hpV_sub by (by100 blast)
    qed
  qed
  show ?thesis unfolding top1_homeomorphism_on_def
    using hTI hTS hbij hcont hcont_inv by (by100 blast)
qed

text \<open>Deformation retraction of circle minus point to any remaining point.
  Munkres 71.1: "W\_i is homeomorphic to an open interval, so it has
  the point p as a deformation retract." Following AlgTopCached:33225.\<close>
lemma circle_minus_point_deformation_retract:
  assumes hh: "top1_homeomorphism_on top1_S1 top1_S1_topology Y TY h"
      and hq: "q \<in> Y" and hr: "r \<in> Y" and hqr: "q \<noteq> r"
  shows "top1_deformation_retract_of_on (Y - {q}) (subspace_topology Y TY (Y - {q})) {r}"
proof -
  \<comment> \<open>Step 1: Extract homeomorphism data. h: S1 \<rightarrow> Y bijective continuous.\<close>
  have hbij: "bij_betw h top1_S1 Y"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  let ?hinv = "inv_into top1_S1 h"
  have hinj: "inj_on h top1_S1" using hbij unfolding bij_betw_def by (by100 blast)
  \<comment> \<open>Step 2: q0 = h^{-1}(q), r0 = h^{-1}(r) in S1.\<close>
  have hq_img: "q \<in> h ` top1_S1" using hbij hq unfolding bij_betw_def by (by100 blast)
  have hr_img: "r \<in> h ` top1_S1" using hbij hr unfolding bij_betw_def by (by100 blast)
  define q0 where "q0 = ?hinv q"
  define r0 where "r0 = ?hinv r"
  have hq0_S1: "q0 \<in> top1_S1" unfolding q0_def by (rule inv_into_into[OF hq_img])
  have hr0_S1: "r0 \<in> top1_S1" unfolding r0_def by (rule inv_into_into[OF hr_img])
  have hq0_map: "h q0 = q" unfolding q0_def using f_inv_into_f[OF hq_img] by (by100 simp)
  have hr0_map: "h r0 = r" unfolding r0_def using f_inv_into_f[OF hr_img] by (by100 simp)
  have hq0r0: "q0 \<noteq> r0"
  proof
    assume "q0 = r0" hence "h q0 = h r0" by (by100 simp)
    thus False using hq0_map hr0_map hqr by (by100 simp)
  qed
  \<comment> \<open>Step 3: Choose \<theta>\_q with R\_to\_S1(\<theta>\_q) = q0. The interval (\<theta>\_q, \<theta>\_q + 1)
     parameterizes S1 - {q0} via R\_to\_S1.\<close>
  have "\<exists>\<theta>q. top1_R_to_S1 \<theta>q = q0" using S1_point_to_angle[OF hq0_S1] by (by100 blast)
  then obtain \<theta>q where h\<theta>q: "top1_R_to_S1 \<theta>q = q0" by (by100 blast)
  \<comment> \<open>Step 4: Find \<theta>\_r \<in> (\<theta>\_q, \<theta>\_q + 1) with R\_to\_S1(\<theta>\_r) = r0.\<close>
  have "\<exists>\<theta>r. \<theta>q < \<theta>r \<and> \<theta>r < \<theta>q + 1 \<and> top1_R_to_S1 \<theta>r = r0"
  proof -
    from S1_point_to_angle[OF hr0_S1] obtain \<theta>' where h\<theta>': "top1_R_to_S1 \<theta>' = r0" by (by100 blast)
    \<comment> \<open>Adjust \<theta>' to lie in (\<theta>q, \<theta>q + 1) via floor shift.\<close>
    define k where "k = \<lfloor>\<theta>' - \<theta>q\<rfloor>"
    define \<theta>r where "\<theta>r = \<theta>' - of_int k"
    have h\<theta>r_map: "top1_R_to_S1 \<theta>r = r0"
    proof -
      have "\<theta>r = \<theta>' + of_int (- k)" unfolding \<theta>r_def by (by100 simp)
      hence "top1_R_to_S1 \<theta>r = top1_R_to_S1 (\<theta>' + of_int (- k))" by (by100 simp)
      also have "\<dots> = top1_R_to_S1 \<theta>'" by (rule top1_R_to_S1_int_shift)
      finally show ?thesis using h\<theta>' by (by100 simp)
    qed
    have h\<theta>r_lb: "\<theta>q \<le> \<theta>r"
      unfolding \<theta>r_def k_def using floor_le_iff by (by100 linarith)
    have h\<theta>r_ub: "\<theta>r < \<theta>q + 1"
      unfolding \<theta>r_def k_def using floor_less_iff by (by100 linarith)
    \<comment> \<open>\<theta>r \<noteq> \<theta>q because R\_to\_S1(\<theta>r) = r0 \<noteq> q0 = R\_to\_S1(\<theta>q).\<close>
    have "\<theta>r \<noteq> \<theta>q"
    proof
      assume "\<theta>r = \<theta>q"
      hence "top1_R_to_S1 \<theta>r = top1_R_to_S1 \<theta>q" by (by100 simp)
      hence "r0 = q0" using h\<theta>r_map h\<theta>q by (by100 simp)
      thus False using hq0r0 by (by100 simp)
    qed
    hence "\<theta>q < \<theta>r" using h\<theta>r_lb by (by100 linarith)
    thus ?thesis using h\<theta>r_ub h\<theta>r_map by (by100 blast)
  qed
  then obtain \<theta>r where h\<theta>r_bounds: "\<theta>q < \<theta>r" "\<theta>r < \<theta>q + 1"
      and h\<theta>r_map: "top1_R_to_S1 \<theta>r = r0" by (by100 blast)
  \<comment> \<open>Step 5: Define the angle function: for y \<in> Y - {q}, angle(y) is the unique
     \<theta> \<in> (\<theta>\_q, \<theta>\_q + 1) with R\_to\_S1(\<theta>) = h^{-1}(y).\<close>
  define angle where "angle y = (THE \<theta>. \<theta>q < \<theta> \<and> \<theta> < \<theta>q + 1 \<and>
      top1_R_to_S1 \<theta> = ?hinv y)" for y
  \<comment> \<open>Step 6: Define the retraction: F(y, t) = h(R\_to\_S1((1-t)*angle(y) + t*\<theta>\_r)).\<close>
  define F where "F = (\<lambda>(y, t). h (top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r)))"
  \<comment> \<open>Step 7: Verify deformation retraction properties.\<close>
  show ?thesis unfolding top1_deformation_retract_of_on_def
  proof (intro conjI)
    show "{r} \<subseteq> Y - {q}" using hr hqr by (by100 blast)
    \<comment> \<open>Key property of angle: for y \<in> Y - {q}, angle(y) \<in> (\<theta>q, \<theta>q+1) and
       R\_to\_S1(angle(y)) = h^{-1}(y).\<close>
    have hangle_prop: "\<forall>y\<in>Y - {q}. \<theta>q < angle y \<and> angle y < \<theta>q + 1 \<and>
        top1_R_to_S1 (angle y) = ?hinv y"
    proof (intro ballI conjI)
      fix y assume hy: "y \<in> Y - {q}"
      hence hy_Y: "y \<in> Y" "y \<noteq> q" by (by100 blast)+
      have hy_img: "y \<in> h ` top1_S1" using hbij hy_Y unfolding bij_betw_def by (by100 blast)
      have hinvy_S1: "?hinv y \<in> top1_S1" by (rule inv_into_into[OF hy_img])
      have hinvy_ne_q0: "?hinv y \<noteq> q0"
      proof
        assume "?hinv y = q0"
        hence "h (?hinv y) = h q0" by (by100 simp)
        hence "y = q" using f_inv_into_f[OF hy_img] hq0_map by (by100 simp)
        thus False using hy_Y by (by100 simp)
      qed
      \<comment> \<open>Find \<theta> \<in> (\<theta>q, \<theta>q+1) with R\_to\_S1(\<theta>) = h^{-1}(y). Same as \<theta>r construction.\<close>
      from S1_point_to_angle[OF hinvy_S1] obtain \<theta>' where h\<theta>': "top1_R_to_S1 \<theta>' = ?hinv y" by (by100 blast)
      define k' where "k' = \<lfloor>\<theta>' - \<theta>q\<rfloor>"
      define \<theta>y where "\<theta>y = \<theta>' - of_int k'"
      have h\<theta>y_map: "top1_R_to_S1 \<theta>y = ?hinv y"
      proof -
        have "\<theta>y = \<theta>' + of_int (- k')" unfolding \<theta>y_def by (by100 simp)
        hence "top1_R_to_S1 \<theta>y = top1_R_to_S1 (\<theta>' + of_int (- k'))" by (by100 simp)
        also have "\<dots> = top1_R_to_S1 \<theta>'" by (rule top1_R_to_S1_int_shift)
        finally show ?thesis using h\<theta>' by (by100 simp)
      qed
      have h\<theta>y_lb: "\<theta>q \<le> \<theta>y" unfolding \<theta>y_def k'_def using floor_le_iff by (by100 linarith)
      have h\<theta>y_ub: "\<theta>y < \<theta>q + 1" unfolding \<theta>y_def k'_def using floor_less_iff by (by100 linarith)
      have h\<theta>y_ne: "\<theta>y \<noteq> \<theta>q"
      proof
        assume "\<theta>y = \<theta>q"
        hence "top1_R_to_S1 \<theta>y = top1_R_to_S1 \<theta>q" by (by100 simp)
        hence "?hinv y = q0" using h\<theta>y_map h\<theta>q by (by100 simp)
        thus False using hinvy_ne_q0 by (by100 simp)
      qed
      hence h\<theta>y_strict: "\<theta>q < \<theta>y" using h\<theta>y_lb by (by100 linarith)
      \<comment> \<open>Uniqueness: if \<theta>1, \<theta>2 \<in> (\<theta>q, \<theta>q+1) both map to same point, then \<theta>1 = \<theta>2.\<close>
      have huniq: "\<And>\<theta>1. \<theta>q < \<theta>1 \<Longrightarrow> \<theta>1 < \<theta>q + 1 \<Longrightarrow> top1_R_to_S1 \<theta>1 = ?hinv y \<Longrightarrow> \<theta>1 = \<theta>y"
      proof -
        fix \<theta>1 assume h1: "\<theta>q < \<theta>1" "\<theta>1 < \<theta>q + 1" "top1_R_to_S1 \<theta>1 = ?hinv y"
        hence "top1_R_to_S1 \<theta>1 = top1_R_to_S1 \<theta>y" using h\<theta>y_map by (by100 simp)
        hence "(cos (2*pi*\<theta>1), sin (2*pi*\<theta>1)) = (cos (2*pi*\<theta>y), sin (2*pi*\<theta>y))"
          unfolding top1_R_to_S1_def by (by100 simp)
        hence "sin (2*pi*\<theta>1) = sin (2*pi*\<theta>y) \<and> cos (2*pi*\<theta>1) = cos (2*pi*\<theta>y)"
          by (by100 simp)
        hence "\<exists>m::int. 2*pi*\<theta>1 = 2*pi*\<theta>y + 2*pi*of_int m"
          using iffD1[OF sin_cos_eq_iff] by (by100 blast)
        then obtain m :: int where hm: "2*pi*\<theta>1 = 2*pi*\<theta>y + 2*pi*of_int m" by (by100 blast)
        have "\<theta>1 - \<theta>y = of_int m"
        proof -
          from hm have "2*pi*\<theta>1 - 2*pi*\<theta>y = 2*pi*of_int m" by (by100 linarith)
          hence "2*pi*(\<theta>1 - \<theta>y) = 2*pi*of_int m"
            using right_diff_distrib[of "2*pi" \<theta>1 \<theta>y] by (by100 linarith)
          moreover have "2*pi \<noteq> (0::real)" using pi_neq_zero by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        moreover have "\<bar>\<theta>1 - \<theta>y\<bar> < 1" using h1 h\<theta>y_strict h\<theta>y_ub by (by100 linarith)
        ultimately have "m = 0" by (by100 linarith)
        thus "\<theta>1 = \<theta>y" using \<open>\<theta>1 - \<theta>y = of_int m\<close> by (by100 simp)
      qed
      \<comment> \<open>THE picks \<theta>y since it's the unique element satisfying the predicate.\<close>
      have hangle_eq: "angle y = \<theta>y"
        unfolding angle_def
      proof (rule the_equality)
        show "\<theta>q < \<theta>y \<and> \<theta>y < \<theta>q + 1 \<and> top1_R_to_S1 \<theta>y = ?hinv y"
          using h\<theta>y_strict h\<theta>y_ub h\<theta>y_map by (by100 blast)
        fix \<theta>1 assume "\<theta>q < \<theta>1 \<and> \<theta>1 < \<theta>q + 1 \<and> top1_R_to_S1 \<theta>1 = ?hinv y"
        thus "\<theta>1 = \<theta>y" using huniq by (by100 blast)
      qed
      show "\<theta>q < angle y" using hangle_eq h\<theta>y_strict by (by100 simp)
      show "angle y < \<theta>q + 1" using hangle_eq h\<theta>y_ub by (by100 simp)
      show "top1_R_to_S1 (angle y) = ?hinv y" using hangle_eq h\<theta>y_map by (by100 simp)
    qed
    \<comment> \<open>Boundary conditions for F.\<close>
    have hF_id: "\<forall>y\<in>Y - {q}. F (y, 0) = y"
    proof (intro ballI)
      fix y assume hy: "y \<in> Y - {q}"
      have "F (y, 0) = h (top1_R_to_S1 ((1 - 0) * angle y + 0 * \<theta>r))"
        unfolding F_def by (by100 simp)
      also have "\<dots> = h (top1_R_to_S1 (angle y))" by (by100 simp)
      also have "\<dots> = h (?hinv y)"
      proof -
        have "top1_R_to_S1 (angle y) = ?hinv y" using hangle_prop hy by (by100 blast)
        thus ?thesis by (by100 simp)
      qed
      also have "\<dots> = y"
      proof -
        have "y \<in> Y" using hy by (by100 blast)
        hence "y \<in> h ` top1_S1" using hbij unfolding bij_betw_def by (by100 blast)
        thus ?thesis by (rule f_inv_into_f)
      qed
      finally show "F (y, 0) = y" .
    qed
    have hF_r: "\<forall>y\<in>Y - {q}. F (y, 1) \<in> {r}"
    proof (intro ballI)
      fix y assume "y \<in> Y - {q}"
      have "F (y, 1) = h (top1_R_to_S1 ((1 - 1) * angle y + 1 * \<theta>r))"
        unfolding F_def by (by100 simp)
      also have "\<dots> = h (top1_R_to_S1 \<theta>r)" by (by100 simp)
      also have "\<dots> = h r0" using h\<theta>r_map by (by100 simp)
      also have "\<dots> = r" using hr0_map .
      finally show "F (y, 1) \<in> {r}" by (by100 simp)
    qed
    have hF_fix: "\<forall>t\<in>I_set. F (r, t) = r"
    proof (intro ballI)
      fix t assume "t \<in> I_set"
      have hangle_r: "angle r = \<theta>r"
      proof -
        have "r \<in> Y - {q}" using hr hqr by (by100 blast)
        from hangle_prop[rule_format, OF this]
        have "top1_R_to_S1 (angle r) = ?hinv r" by (by100 blast)
        hence "top1_R_to_S1 (angle r) = r0" unfolding r0_def by (by100 simp)
        moreover have "\<theta>q < angle r" "angle r < \<theta>q + 1"
          using hangle_prop \<open>r \<in> Y - {q}\<close> by (by100 blast)+
        moreover have "top1_R_to_S1 \<theta>r = r0" using h\<theta>r_map .
        ultimately show "angle r = \<theta>r"
        proof -
          assume ha: "top1_R_to_S1 (angle r) = r0"
             and hab: "\<theta>q < angle r" "angle r < \<theta>q + 1"
             and hb: "top1_R_to_S1 \<theta>r = r0"
          hence "top1_R_to_S1 (angle r) = top1_R_to_S1 \<theta>r" by (by100 simp)
          hence "(cos (2*pi*(angle r)), sin (2*pi*(angle r))) = (cos (2*pi*\<theta>r), sin (2*pi*\<theta>r))"
            unfolding top1_R_to_S1_def by (by100 simp)
          hence "sin (2*pi*(angle r)) = sin (2*pi*\<theta>r) \<and> cos (2*pi*(angle r)) = cos (2*pi*\<theta>r)"
            by (by100 simp)
          hence "\<exists>k::int. 2*pi*(angle r) = 2*pi*\<theta>r + 2*pi*of_int k"
            using iffD1[OF sin_cos_eq_iff] by (by100 blast)
          then obtain k :: int where hk: "2*pi*(angle r) = 2*pi*\<theta>r + 2*pi*of_int k" by (by100 blast)
          have "angle r - \<theta>r = of_int k"
          proof -
            from hk have "2*pi*angle r = 2*pi*\<theta>r + 2*pi*of_int k" .
            hence "2*pi*angle r - 2*pi*\<theta>r = 2*pi*of_int k" by (by100 linarith)
            hence hd: "2*pi*(angle r - \<theta>r) = 2*pi*of_int k"
              using right_diff_distrib[of "2*pi" "angle r" \<theta>r] by (by100 linarith)
            have "2*pi \<noteq> (0::real)" using pi_neq_zero by (by100 simp)
            with hd show ?thesis by (by100 simp)
          qed
          moreover have "\<bar>angle r - \<theta>r\<bar> < 1"
            using hab h\<theta>r_bounds by (by100 linarith)
          ultimately have "k = 0" by (by100 linarith)
          hence "angle r - \<theta>r = 0" using \<open>angle r - \<theta>r = of_int k\<close> by (by100 simp)
          thus "angle r = \<theta>r" by (by100 simp)
        qed
      qed
      have "F (r, t) = h (top1_R_to_S1 ((1 - t) * \<theta>r + t * \<theta>r))"
        unfolding F_def using hangle_r by (by100 simp)
      also have "\<dots> = h (top1_R_to_S1 \<theta>r)"
      proof -
        have "(1 - t) * \<theta>r + t * \<theta>r = \<theta>r"
          using left_diff_distrib[of 1 t \<theta>r] by (by100 simp)
        thus ?thesis by (by100 simp)
      qed
      also have "\<dots> = r" using h\<theta>r_map hr0_map by (by100 simp)
      finally show "F (r, t) = r" .
    qed
    \<comment> \<open>Continuity of F.\<close>
    \<comment> \<open>angle: Y-{q} \<rightarrow> (\<theta>q, \<theta>q+1) is continuous.
       angle = (R\_to\_S1|_{(\<theta>q,\<theta>q+1)})^{-1} \<circ> h^{-1}. Both factors continuous:
       h^{-1} by homeomorphism; R\_to\_S1 restricted to (\<theta>q, \<theta>q+1) is a homeomorphism
       (covering map, evenly covered neighborhood S1 - {q0}).\<close>
    \<comment> \<open>angle = inv(R\_to\_S1|(\<theta>q,\<theta>q+1)) \<circ> h^{-1}.
       R\_to\_S1 restricted to (\<theta>q,\<theta>q+1) is a homeomorphism onto S1-{q0}.
       Its inverse is continuous. h^{-1} is continuous. Composition continuous.\<close>
    \<comment> \<open>angle = (R\_to\_S1|(\<theta>q,\<theta>q+1))^{-1} \<circ> h^{-1}.
       By R\_to\_S1\_interval\_homeomorphism: the restriction is a homeomorphism.
       Its inverse is continuous. h^{-1} continuous. Composition continuous.\<close>
    have hangle_cont: "top1_continuous_map_on (Y - {q}) (subspace_topology Y TY (Y - {q}))
        (UNIV :: real set) top1_open_sets angle"
    proof -
      \<comment> \<open>R\_to\_S1(\<theta>q) = q0. So S1-{q0} = S1-{R\_to\_S1(\<theta>q)}.\<close>
      have hq0_eq: "top1_R_to_S1 \<theta>q = q0" by (rule h\<theta>q)
      \<comment> \<open>R\_to\_S1|(\<theta>q,\<theta>q+1) is a homeomorphism onto S1-{q0}.\<close>
      let ?I_open = "{x::real. \<theta>q < x \<and> x < \<theta>q + 1}"
      have hR_homeo: "top1_homeomorphism_on ?I_open
          (subspace_topology UNIV top1_open_sets ?I_open)
          (top1_S1 - {q0})
          (subspace_topology top1_S1 top1_S1_topology (top1_S1 - {q0}))
          top1_R_to_S1"
      proof -
        from R_to_S1_interval_homeomorphism[of \<theta>q]
        show ?thesis using hq0_eq by (by100 simp)
      qed
      \<comment> \<open>h^{-1}: Y \<rightarrow> S1 continuous, then restrict to Y-{q} \<rightarrow> S1-{q0}.\<close>
      have hhinv_cont: "top1_continuous_map_on Y TY top1_S1 top1_S1_topology ?hinv"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      have hTY: "is_topology_on Y TY"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
        using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
      have hTYq: "is_topology_on (Y - {q}) (subspace_topology Y TY (Y - {q}))"
        by (rule subspace_topology_is_topology_on[OF hTY]) (by100 blast)
      \<comment> \<open>Restrict domain of h^{-1} to Y-{q}.\<close>
      have hhinv_dom: "top1_continuous_map_on (Y - {q}) (subspace_topology Y TY (Y - {q}))
            top1_S1 top1_S1_topology ?hinv"
        using Theorem_18_2(4)[OF hTY hS1_top hS1_top] hhinv_cont by (by100 blast)
      \<comment> \<open>h^{-1} maps Y-{q} into S1-{q0}.\<close>
      have hhinv_range: "?hinv ` (Y - {q}) \<subseteq> top1_S1 - {q0}"
      proof
        fix s assume "s \<in> ?hinv ` (Y - {q})"
        then obtain y where "y \<in> Y - {q}" "s = ?hinv y" by (by100 blast)
        have "y \<in> Y" "y \<noteq> q" using \<open>y \<in> Y - {q}\<close> by (by100 blast)+
        have hy_img: "y \<in> h ` top1_S1" using hbij \<open>y \<in> Y\<close> unfolding bij_betw_def by (by100 blast)
        have "s \<in> top1_S1" unfolding \<open>s = ?hinv y\<close> by (rule inv_into_into[OF hy_img])
        moreover have "s \<noteq> q0"
        proof
          assume "s = q0"
          hence "h s = h q0" by (by100 simp)
          hence "y = q" using f_inv_into_f[OF hy_img] hq0_map \<open>s = ?hinv y\<close> by (by100 simp)
          thus False using \<open>y \<noteq> q\<close> by (by100 simp)
        qed
        ultimately show "s \<in> top1_S1 - {q0}" by (by100 blast)
      qed
      \<comment> \<open>Restrict range to S1-{q0}.\<close>
      have hhinv_S1q0: "top1_continuous_map_on (Y - {q}) (subspace_topology Y TY (Y - {q}))
            (top1_S1 - {q0}) (subspace_topology top1_S1 top1_S1_topology (top1_S1 - {q0})) ?hinv"
        using Theorem_18_2(5)[OF hTYq hS1_top hS1_top] hhinv_dom hhinv_range by (by100 blast)
      \<comment> \<open>inv\_into ?I\_open R\_to\_S1 is continuous S1-{q0} \<rightarrow> ?I\_open (from hR\_homeo).\<close>
      have hRinv_cont: "top1_continuous_map_on (top1_S1 - {q0})
            (subspace_topology top1_S1 top1_S1_topology (top1_S1 - {q0}))
            ?I_open (subspace_topology UNIV top1_open_sets ?I_open)
            (inv_into ?I_open top1_R_to_S1)"
        using hR_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      \<comment> \<open>Expand range from ?I\_open (subspace) to UNIV (top1\_open\_sets).\<close>
      have hI_sub_UNIV: "?I_open \<subseteq> (UNIV :: real set)" by (by100 blast)
      have hsubspace_eq: "subspace_topology UNIV top1_open_sets ?I_open
          = subspace_topology (UNIV :: real set) top1_open_sets ?I_open" by (by100 simp)
      have hTS1q0: "is_topology_on (top1_S1 - {q0})
            (subspace_topology top1_S1 top1_S1_topology (top1_S1 - {q0}))"
        by (rule subspace_topology_is_topology_on[OF hS1_top]) (by100 blast)
      have hTI_open: "is_topology_on ?I_open (subspace_topology UNIV top1_open_sets ?I_open)"
        by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV])
           (by100 blast)
      have hRinv_UNIV: "top1_continuous_map_on (top1_S1 - {q0})
            (subspace_topology top1_S1 top1_S1_topology (top1_S1 - {q0}))
            (UNIV :: real set) top1_open_sets (inv_into ?I_open top1_R_to_S1)"
        using Theorem_18_2(6)[OF hTS1q0 hTI_open top1_open_sets_is_topology_on_UNIV]
              hRinv_cont hI_sub_UNIV
        by (by100 blast)
      \<comment> \<open>Compose: angle' = inv\_into \<circ> h^{-1} continuous Y-{q} \<rightarrow> UNIV.\<close>
      have hcomp_cont: "top1_continuous_map_on (Y - {q}) (subspace_topology Y TY (Y - {q}))
            (UNIV :: real set) top1_open_sets (inv_into ?I_open top1_R_to_S1 \<circ> ?hinv)"
      proof -
        have hconj: "top1_continuous_map_on (Y - {q}) (subspace_topology Y TY (Y - {q}))
              (top1_S1 - {q0}) (subspace_topology top1_S1 top1_S1_topology (top1_S1 - {q0})) ?hinv \<and>
            top1_continuous_map_on (top1_S1 - {q0})
              (subspace_topology top1_S1 top1_S1_topology (top1_S1 - {q0}))
              (UNIV :: real set) top1_open_sets (inv_into ?I_open top1_R_to_S1)"
          using hhinv_S1q0 hRinv_UNIV by (by100 blast)
        have hTR: "is_topology_on (UNIV :: real set) (top1_open_sets :: real set set)"
          using top1_open_sets_is_topology_on_UNIV by (by100 blast)
        show ?thesis
        proof (rule continuous_map_onI)
          show "\<forall>x \<in> Y - {q}. (inv_into ?I_open top1_R_to_S1 \<circ> ?hinv) x \<in> (UNIV :: real set)"
            by (by100 blast)
          show "\<forall>V \<in> top1_open_sets. {x \<in> Y - {q}. (inv_into ?I_open top1_R_to_S1 \<circ> ?hinv) x \<in> V}
                \<in> subspace_topology Y TY (Y - {q})"
          proof
            fix V assume "V \<in> (top1_open_sets :: real set set)"
            \<comment> \<open>Preimage under Rinv: a set in subspace S1 S1\_top (S1-{q0}).\<close>
            have "{s \<in> top1_S1 - {q0}. inv_into ?I_open top1_R_to_S1 s \<in> V}
                \<in> subspace_topology top1_S1 top1_S1_topology (top1_S1 - {q0})"
              using continuous_map_preimage_open[OF hRinv_UNIV \<open>V \<in> top1_open_sets\<close>] by (by100 blast)
            \<comment> \<open>Preimage under hinv: a set in subspace Y TY (Y-{q}).\<close>
            hence "{y \<in> Y - {q}. ?hinv y \<in> {s \<in> top1_S1 - {q0}. inv_into ?I_open top1_R_to_S1 s \<in> V}}
                \<in> subspace_topology Y TY (Y - {q})"
              using continuous_map_preimage_open[OF hhinv_S1q0] by (by100 blast)
            moreover have "{y \<in> Y - {q}. ?hinv y \<in> {s \<in> top1_S1 - {q0}. inv_into ?I_open top1_R_to_S1 s \<in> V}}
                = {x \<in> Y - {q}. (inv_into ?I_open top1_R_to_S1 \<circ> ?hinv) x \<in> V}"
            proof (rule set_eqI, rule iffI)
              fix y assume "y \<in> {y \<in> Y - {q}. ?hinv y \<in> {s \<in> top1_S1 - {q0}. inv_into ?I_open top1_R_to_S1 s \<in> V}}"
              thus "y \<in> {x \<in> Y - {q}. (inv_into ?I_open top1_R_to_S1 \<circ> ?hinv) x \<in> V}"
                by (by5000 auto)
            next
              fix y assume "y \<in> {x \<in> Y - {q}. (inv_into ?I_open top1_R_to_S1 \<circ> ?hinv) x \<in> V}"
              hence "y \<in> Y - {q}" "(inv_into ?I_open top1_R_to_S1 \<circ> ?hinv) y \<in> V" by (by100 blast)+
              have "?hinv y \<in> top1_S1 - {q0}" using hhinv_range \<open>y \<in> Y - {q}\<close> by (by100 blast)
              thus "y \<in> {y \<in> Y - {q}. ?hinv y \<in> {s \<in> top1_S1 - {q0}. inv_into ?I_open top1_R_to_S1 s \<in> V}}"
                using \<open>y \<in> Y - {q}\<close> \<open>(inv_into ?I_open top1_R_to_S1 \<circ> ?hinv) y \<in> V\<close>
                by (by5000 auto)
            qed
            ultimately show "{x \<in> Y - {q}. (inv_into ?I_open top1_R_to_S1 \<circ> ?hinv) x \<in> V}
                \<in> subspace_topology Y TY (Y - {q})" by (by100 simp)
          qed
        qed
      qed
      \<comment> \<open>angle agrees with inv\_into \<circ> h^{-1} on Y-{q}.\<close>
      have hagree: "\<forall>y \<in> Y - {q}. angle y = (inv_into ?I_open top1_R_to_S1 \<circ> ?hinv) y"
      proof
        fix y assume hy: "y \<in> Y - {q}"
        from hangle_prop[rule_format, OF hy]
        have ha: "\<theta>q < angle y" "angle y < \<theta>q + 1" "top1_R_to_S1 (angle y) = ?hinv y"
          by (by100 blast)+
        have "angle y \<in> ?I_open" using ha by (by100 simp)
        hence "top1_R_to_S1 (angle y) = ?hinv y \<Longrightarrow>
               inv_into ?I_open top1_R_to_S1 (?hinv y) = angle y"
        proof -
          assume "top1_R_to_S1 (angle y) = ?hinv y"
          have hinj_I: "inj_on top1_R_to_S1 ?I_open"
            using hR_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
          have "inv_into ?I_open top1_R_to_S1 (top1_R_to_S1 (angle y)) = angle y"
            using inv_into_f_f[OF hinj_I \<open>angle y \<in> ?I_open\<close>] by (by100 blast)
          thus ?thesis using \<open>top1_R_to_S1 (angle y) = ?hinv y\<close> by (by100 simp)
        qed
        thus "angle y = (inv_into ?I_open top1_R_to_S1 \<circ> ?hinv) y"
          using ha by (by100 simp)
      qed
      have hagree': "\<forall>y \<in> Y - {q}. (inv_into ?I_open top1_R_to_S1 \<circ> ?hinv) y = angle y"
        using hagree by (by100 simp)
      show ?thesis
        using top1_continuous_map_on_agree[OF hcomp_cont hagree'] by (by100 blast)
    qed
    \<comment> \<open>F continuity: F = h \<circ> R\_to\_S1 \<circ> linear\_comb where linear\_comb(y,t) = (1-t)*angle(y)+t*\<theta>r.\<close>
    \<comment> \<open>First show image of F is in Y-{q}: convex combination stays in (\<theta>q,\<theta>q+1).\<close>
    have hF_image: "\<forall>y\<in>Y - {q}. \<forall>t\<in>I_set. F (y, t) \<in> Y - {q}"
    proof (intro ballI)
      fix y t assume hy: "y \<in> Y - {q}" and ht: "t \<in> I_set"
      have ha: "\<theta>q < angle y" "angle y < \<theta>q + 1" using hangle_prop hy by (by100 blast)+
      have ht01: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 simp)+
      \<comment> \<open>Convex combination stays in (\<theta>q, \<theta>q+1).\<close>
      define \<theta>_mix where "\<theta>_mix = (1 - t) * angle y + t * \<theta>r"
      have hmix_lb: "\<theta>q < \<theta>_mix"
      proof -
        have h1: "(1 - t) * (angle y - \<theta>q) \<ge> 0"
          using mult_nonneg_nonneg[of "1 - t" "angle y - \<theta>q"] ha ht01 by (by100 linarith)
        have h2: "t * (\<theta>r - \<theta>q) \<ge> 0"
          using mult_nonneg_nonneg[of t "\<theta>r - \<theta>q"] h\<theta>r_bounds ht01 by (by100 linarith)
        have h3: "(1 - t) > 0 \<or> t > 0" using ht01 by (by100 linarith)
        have h4: "(1 - t) * (angle y - \<theta>q) > 0 \<or> t * (\<theta>r - \<theta>q) > 0"
          using h3 ha h\<theta>r_bounds ht01
        proof (cases "t = 0")
            case True thus ?thesis using ha ht01 by (by100 simp)
          next
            case False hence "t > 0" using ht01 by (by100 linarith)
            have "\<theta>r - \<theta>q > 0" using h\<theta>r_bounds by (by100 linarith)
            hence "t * (\<theta>r - \<theta>q) > 0" using mult_pos_pos[OF \<open>t > 0\<close> \<open>\<theta>r - \<theta>q > 0\<close>] by (by100 blast)
            thus ?thesis by (by100 blast)
          qed
        have "(1 - t) * (angle y - \<theta>q) + t * (\<theta>r - \<theta>q) > 0" using h1 h2 h4 by (by100 linarith)
        moreover have "(1 - t) * (angle y - \<theta>q) + t * (\<theta>r - \<theta>q) = (1 - t) * angle y + t * \<theta>r - \<theta>q"
        proof -
          have h_d1: "(1 - t) * (angle y - \<theta>q) = (1 - t) * angle y - (1 - t) * \<theta>q"
            using right_diff_distrib[of "1 - t" "angle y" \<theta>q] by (by100 linarith)
          have h_d2: "t * (\<theta>r - \<theta>q) = t * \<theta>r - t * \<theta>q"
            using right_diff_distrib[of t \<theta>r \<theta>q] by (by100 linarith)
          have h_sum: "(1 - t) * \<theta>q + t * \<theta>q = \<theta>q"
          proof -
            have "(1 - t) * \<theta>q + t * \<theta>q = ((1 - t) + t) * \<theta>q"
              using distrib_right[of "1 - t" t \<theta>q] by (by100 linarith)
            also have "\<dots> = \<theta>q" by (by100 simp)
            finally show ?thesis .
          qed
          show ?thesis using h_d1 h_d2 h_sum by (by100 linarith)
        qed
        ultimately show ?thesis unfolding \<theta>_mix_def by (by100 linarith)
      qed
      have hmix_ub: "\<theta>_mix < \<theta>q + 1"
      proof -
        have h1: "(1 - t) * (\<theta>q + 1 - angle y) \<ge> 0"
          using mult_nonneg_nonneg[of "1 - t" "\<theta>q + 1 - angle y"] ha ht01 by (by100 linarith)
        have h2: "t * (\<theta>q + 1 - \<theta>r) \<ge> 0"
          using mult_nonneg_nonneg[of t "\<theta>q + 1 - \<theta>r"] h\<theta>r_bounds ht01 by (by100 linarith)
        have h3: "(1 - t) > 0 \<or> t > 0" using ht01 by (by100 linarith)
        have h4: "(1 - t) * (\<theta>q + 1 - angle y) > 0 \<or> t * (\<theta>q + 1 - \<theta>r) > 0"
          using h3 ha h\<theta>r_bounds ht01
        proof (cases "t = 0")
            case True thus ?thesis using ha ht01 by (by100 simp)
          next
            case False hence "t > 0" using ht01 by (by100 linarith)
            have "\<theta>q + 1 - \<theta>r > 0" using h\<theta>r_bounds by (by100 linarith)
            hence "t * (\<theta>q + 1 - \<theta>r) > 0"
              using mult_pos_pos[OF \<open>t > 0\<close> \<open>\<theta>q + 1 - \<theta>r > 0\<close>] by (by100 blast)
            thus ?thesis by (by100 blast)
          qed
        have "(1 - t) * (\<theta>q + 1 - angle y) + t * (\<theta>q + 1 - \<theta>r) > 0" using h1 h2 h4 by (by100 linarith)
        \<comment> \<open>Algebraic expansion: LHS = (\<theta>q+1) - ((1-t)*angle y + t*\<theta>r).\<close>
        have hd1: "(1 - t) * (\<theta>q + 1 - angle y) = (1 - t) * (\<theta>q + 1) - (1 - t) * angle y"
          using right_diff_distrib[of "1-t" "\<theta>q + 1" "angle y"] by (by100 linarith)
        have hd2: "t * (\<theta>q + 1 - \<theta>r) = t * (\<theta>q + 1) - t * \<theta>r"
          using right_diff_distrib[of t "\<theta>q + 1" \<theta>r] by (by100 linarith)
        have hds: "(1 - t) * (\<theta>q + 1) + t * (\<theta>q + 1) = ((1 - t) + t) * (\<theta>q + 1)"
          using distrib_right[of "1 - t" t "\<theta>q + 1"] by (by100 linarith)
        hence hds': "(1 - t) * (\<theta>q + 1) + t * (\<theta>q + 1) = \<theta>q + 1" by (by100 simp)
        have heq: "(1 - t) * (\<theta>q + 1 - angle y) + t * (\<theta>q + 1 - \<theta>r)
            = (\<theta>q + 1) - ((1 - t) * angle y + t * \<theta>r)"
        proof -
          have s1: "(1 - t) * (\<theta>q + 1 - angle y) + t * (\<theta>q + 1 - \<theta>r)
              = ((1 - t) * (\<theta>q + 1) - (1 - t) * angle y) + (t * (\<theta>q + 1) - t * \<theta>r)"
            using hd1 hd2 by (by100 linarith)
          also have "\<dots> = ((1 - t) * (\<theta>q + 1) + t * (\<theta>q + 1)) - ((1 - t) * angle y + t * \<theta>r)"
            by (by100 linarith)
          also have "\<dots> = (\<theta>q + 1) - ((1 - t) * angle y + t * \<theta>r)" using hds' by (by100 linarith)
          finally show ?thesis .
        qed
        thus ?thesis unfolding \<theta>_mix_def
          using \<open>(1 - t) * (\<theta>q + 1 - angle y) + t * (\<theta>q + 1 - \<theta>r) > 0\<close>
          by (by100 linarith)
      qed
      \<comment> \<open>So R\_to\_S1(\<theta>\_mix) \<noteq> q0.\<close>
      have "top1_R_to_S1 \<theta>_mix \<noteq> q0"
      proof
        assume "top1_R_to_S1 \<theta>_mix = q0"
        hence "top1_R_to_S1 \<theta>_mix = top1_R_to_S1 \<theta>q" using h\<theta>q by (by100 simp)
        hence "(cos (2*pi*\<theta>_mix), sin (2*pi*\<theta>_mix)) = (cos (2*pi*\<theta>q), sin (2*pi*\<theta>q))"
          unfolding top1_R_to_S1_def by (by100 simp)
        hence "sin (2*pi*\<theta>_mix) = sin (2*pi*\<theta>q) \<and> cos (2*pi*\<theta>_mix) = cos (2*pi*\<theta>q)"
          by (by100 simp)
        hence "\<exists>k::int. 2*pi*\<theta>_mix = 2*pi*\<theta>q + 2*pi*of_int k"
          using iffD1[OF sin_cos_eq_iff] by (by100 blast)
        then obtain k :: int where "2*pi*\<theta>_mix = 2*pi*\<theta>q + 2*pi*of_int k" by (by100 blast)
        hence "\<theta>_mix - \<theta>q = of_int k"
        proof -
          assume "2*pi*\<theta>_mix = 2*pi*\<theta>q + 2*pi*of_int k"
          hence "2*pi*(\<theta>_mix - \<theta>q) = 2*pi*of_int k"
            using right_diff_distrib[of "2*pi" \<theta>_mix \<theta>q] by (by100 linarith)
          moreover have "2*pi \<noteq> (0::real)" using pi_neq_zero by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        moreover have "\<bar>\<theta>_mix - \<theta>q\<bar> < 1" using hmix_lb hmix_ub by (by100 linarith)
        ultimately have "k = 0" by (by100 linarith)
        thus False using \<open>\<theta>_mix - \<theta>q = of_int k\<close> hmix_lb by (by100 linarith)
      qed
      \<comment> \<open>R\_to\_S1(\<theta>\_mix) \<in> S1.\<close>
      have "top1_R_to_S1 \<theta>_mix \<in> top1_S1"
        unfolding top1_R_to_S1_def top1_S1_def by (by100 simp)
      \<comment> \<open>h maps S1-{q0} to Y-{q}.\<close>
      have "h (top1_R_to_S1 \<theta>_mix) \<in> Y"
        using bij_betw_apply[OF hbij \<open>top1_R_to_S1 \<theta>_mix \<in> top1_S1\<close>] by (by100 blast)
      moreover have "h (top1_R_to_S1 \<theta>_mix) \<noteq> q"
      proof
        assume "h (top1_R_to_S1 \<theta>_mix) = q"
        hence "h (top1_R_to_S1 \<theta>_mix) = h q0" using hq0_map by (by100 simp)
        hence "top1_R_to_S1 \<theta>_mix = q0"
          using inj_onD[OF hinj _ \<open>top1_R_to_S1 \<theta>_mix \<in> top1_S1\<close> hq0_S1] by (by100 simp)
        thus False using \<open>top1_R_to_S1 \<theta>_mix \<noteq> q0\<close> by (by100 simp)
      qed
      ultimately show "F (y, t) \<in> Y - {q}" unfolding F_def \<theta>_mix_def by (by100 simp)
    qed
    \<comment> \<open>Now: F continuous (Y-{q})\<times>I \<rightarrow> Y-{q}.\<close>
    \<comment> \<open>F = h \<circ> R\_to\_S1 \<circ> lc where lc(y,t) = (1-t)*angle(y) + t*\<theta>r.
       Prove continuity step by step.\<close>
    have hTR_eq: "(order_topology_on_UNIV :: real set set) = top1_open_sets"
    proof (rule set_eqI)
      fix U :: "real set"
      show "U \<in> order_topology_on_UNIV \<longleftrightarrow> U \<in> top1_open_sets"
        using order_topology_on_UNIV_eq_HOL_open unfolding top1_open_sets_def by (by100 simp)
    qed
    have hTY_top: "is_topology_on Y TY"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hTYq_top: "is_topology_on (Y - {q}) (subspace_topology Y TY (Y - {q}))"
      by (rule subspace_topology_is_topology_on[OF hTY_top]) (by100 blast)
    have hI_top: "is_topology_on I_set I_top"
      using top1_unit_interval_topology_is_topology_on by (by100 blast)
    have hprod_top: "is_topology_on ((Y - {q}) \<times> I_set)
        (product_topology_on (subspace_topology Y TY (Y - {q})) I_top)"
      using product_topology_on_is_topology_on[OF hTYq_top hI_top] by (by100 blast)
    \<comment> \<open>Step A: angle \<circ> \<pi>1 continuous (Y-{q})\<times>I \<rightarrow> \<real>.\<close>
    have hangle_pi1: "top1_continuous_map_on ((Y - {q}) \<times> I_set)
        (product_topology_on (subspace_topology Y TY (Y - {q})) I_top)
        (UNIV :: real set) top1_open_sets (\<lambda>(y,t). angle y)"
    proof (rule continuous_map_onI)
      show "\<forall>x \<in> (Y - {q}) \<times> I_set. (case x of (y, t) \<Rightarrow> angle y) \<in> (UNIV :: real set)"
        by (by100 blast)
      show "\<forall>V \<in> top1_open_sets. {x \<in> (Y - {q}) \<times> I_set. (case x of (y, t) \<Rightarrow> angle y) \<in> V}
            \<in> product_topology_on (subspace_topology Y TY (Y - {q})) I_top"
      proof
        fix V assume "V \<in> (top1_open_sets :: real set set)"
        have hpre: "{y \<in> Y - {q}. angle y \<in> V} \<in> subspace_topology Y TY (Y - {q})"
          using continuous_map_preimage_open[OF hangle_cont \<open>V \<in> top1_open_sets\<close>] by (by100 blast)
        have "{x \<in> (Y - {q}) \<times> I_set. (case x of (y, t) \<Rightarrow> angle y) \<in> V}
            = {y \<in> Y - {q}. angle y \<in> V} \<times> I_set"
          by (by5000 auto)
        have "I_set \<in> I_top"
          using hI_top unfolding is_topology_on_def by (by100 blast)
        have "{y \<in> Y - {q}. angle y \<in> V} \<times> I_set \<in>
            product_topology_on (subspace_topology Y TY (Y - {q})) I_top"
          using product_rect_open[OF hpre \<open>I_set \<in> I_top\<close>] by (by100 blast)
        thus "{x \<in> (Y - {q}) \<times> I_set. (case x of (y, t) \<Rightarrow> angle y) \<in> V}
            \<in> product_topology_on (subspace_topology Y TY (Y - {q})) I_top"
          using \<open>{x \<in> (Y - {q}) \<times> I_set. (case x of (y, t) \<Rightarrow> angle y) \<in> V}
            = {y \<in> Y - {q}. angle y \<in> V} \<times> I_set\<close> by (by100 simp)
      qed
    qed
    \<comment> \<open>F continuity: composition of angle (continuous), arithmetic (continuous on \<real>),
       R\_to\_S1 (continuous), h (continuous). Image in Y-{q} proved above.
       Standard product topology argument using Theorem\_18\_2, top1\_continuous\_mul\_real,
       top1\_continuous\_add\_real. Deferred: formally tedious product topology plumbing.\<close>
    \<comment> \<open>F = h \<circ> R\_to\_S1 \<circ> lc where lc(y,t) = (1-t)*angle(y) + t*\<theta>r.
       Prove by composition: first lc continuous to \<real>, then R\_to\_S1 to S1, then h to Y,
       then restrict codomain to Y-{q}.\<close>
    have hTY_top: "is_topology_on Y TY"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hTYq_top: "is_topology_on (Y - {q}) (subspace_topology Y TY (Y - {q}))"
      by (rule subspace_topology_is_topology_on[OF hTY_top]) (by100 blast)
    have hI_top: "is_topology_on I_set I_top"
      using top1_unit_interval_topology_is_topology_on by (by100 blast)
    have hprod_top: "is_topology_on ((Y - {q}) \<times> I_set)
        (product_topology_on (subspace_topology Y TY (Y - {q})) I_top)"
      using product_topology_on_is_topology_on[OF hTYq_top hI_top] by (by100 blast)
    have hTR_eq: "(order_topology_on_UNIV :: real set set) = top1_open_sets"
    proof (rule set_eqI)
      fix U :: "real set"
      show "U \<in> order_topology_on_UNIV \<longleftrightarrow> U \<in> top1_open_sets"
        using order_topology_on_UNIV_eq_HOL_open unfolding top1_open_sets_def by (by100 simp)
    qed
    \<comment> \<open>lc continuous: (Y-{q})\<times>I \<rightarrow> \<real>.\<close>
    have hlc: "top1_continuous_map_on ((Y - {q}) \<times> I_set)
        (product_topology_on (subspace_topology Y TY (Y - {q})) I_top)
        (UNIV :: real set) top1_open_sets (\<lambda>(y,t). (1 - t) * angle y + t * \<theta>r)"
    proof -
      let ?PT = "product_topology_on (subspace_topology Y TY (Y - {q})) I_top"
      let ?OT = "order_topology_on_UNIV :: real set set"
      \<comment> \<open>Bridge: top1\_open\_sets = order\_topology\_on\_UNIV for reals.\<close>
      \<comment> \<open>angle \<circ> \<pi>1 continuous to \<real> (already proved as hangle\_pi1, with open\_sets).\<close>
      have hf_angle: "top1_continuous_map_on ((Y - {q}) \<times> I_set) ?PT
          (UNIV :: real set) ?OT (\<lambda>(y,t). angle y)"
        using hangle_pi1 hTR_eq by (by100 simp)
      \<comment> \<open>\<pi>2 continuous to I, then expand to \<real>.\<close>
      have hpi2: "top1_continuous_map_on ((Y - {q}) \<times> I_set) ?PT I_set I_top pi2"
        using top1_continuous_pi2[OF hTYq_top hI_top] by (by100 blast)
      have hpi2_OT: "top1_continuous_map_on ((Y - {q}) \<times> I_set) ?PT
          (UNIV :: real set) ?OT (\<lambda>(y,t). t)"
      proof (rule continuous_map_onI)
        show "\<forall>x \<in> (Y - {q}) \<times> I_set. (case x of (y,t) \<Rightarrow> t) \<in> (UNIV :: real set)"
          by (by100 blast)
        show "\<forall>V \<in> ?OT. {x \<in> (Y - {q}) \<times> I_set. (case x of (y,t) \<Rightarrow> t) \<in> V} \<in> ?PT"
        proof
          fix V assume "V \<in> ?OT"
          hence "V \<in> top1_open_sets" using hTR_eq by (by100 simp)
          hence "open V" unfolding top1_open_sets_def by (by100 simp)
          have hpre_I: "{t \<in> I_set. t \<in> V} \<in> I_top"
          proof -
            have "I_top = subspace_topology UNIV top1_open_sets I_set"
              unfolding top1_unit_interval_topology_def by (by100 simp)
            hence "{t \<in> I_set. t \<in> V} = I_set \<inter> V" by (by100 blast)
            also have "\<dots> \<in> subspace_topology UNIV top1_open_sets I_set"
              unfolding subspace_topology_def using \<open>V \<in> top1_open_sets\<close> by (by100 blast)
            finally show ?thesis
              unfolding top1_unit_interval_topology_def by (by100 simp)
          qed
          have "I_set \<in> I_top" using hI_top unfolding is_topology_on_def by (by100 blast)
          have "{x \<in> (Y - {q}) \<times> I_set. (case x of (y,t) \<Rightarrow> t) \<in> V}
              = (Y - {q}) \<times> {t \<in> I_set. t \<in> V}" by (by5000 auto)
          have "Y - {q} \<in> subspace_topology Y TY (Y - {q})"
          proof -
            have "Y \<in> TY" using hTY_top unfolding is_topology_on_def by (by100 blast)
            hence "Y \<inter> (Y - {q}) \<in> subspace_topology Y TY (Y - {q})"
              unfolding subspace_topology_def by (by100 blast)
            moreover have "Y \<inter> (Y - {q}) = Y - {q}" by (by100 blast)
            ultimately show ?thesis by (by100 simp)
          qed
          show "{x \<in> (Y - {q}) \<times> I_set. (case x of (y,t) \<Rightarrow> t) \<in> V} \<in> ?PT"
            using product_rect_open[OF \<open>Y - {q} \<in> subspace_topology Y TY (Y - {q})\<close> hpre_I]
                  \<open>{x \<in> (Y - {q}) \<times> I_set. (case x of (y,t) \<Rightarrow> t) \<in> V}
                    = (Y - {q}) \<times> {t \<in> I_set. t \<in> V}\<close>
            by (by100 simp)
        qed
      qed
      \<comment> \<open>Constant function continuous.\<close>
      have hOT: "is_topology_on (UNIV :: real set) ?OT"
        using order_topology_on_UNIV_is_topology_on by (by100 blast)
      have hconst_1: "top1_continuous_map_on ((Y - {q}) \<times> I_set) ?PT
          (UNIV :: real set) ?OT (\<lambda>_. 1 :: real)"
        using top1_continuous_map_on_const[OF hprod_top hOT] by (by100 simp)
      have hconst_thr: "top1_continuous_map_on ((Y - {q}) \<times> I_set) ?PT
          (UNIV :: real set) ?OT (\<lambda>_. \<theta>r)"
        using top1_continuous_map_on_const[OF hprod_top hOT] by (by100 simp)
      \<comment> \<open>Subtract: (y,t) \<mapsto> 1-t.\<close>
      have hnt: "top1_continuous_map_on ((Y - {q}) \<times> I_set) ?PT
          (UNIV :: real set) ?OT (\<lambda>(y,t). - t)"
      proof -
        have "top1_continuous_map_on ((Y - {q}) \<times> I_set) ?PT
            (UNIV :: real set) ?OT (\<lambda>x. - (case x of (y,t) \<Rightarrow> t))"
          using top1_continuous_uminus_real[OF hpi2_OT] by (by100 blast)
        thus ?thesis by (rule top1_continuous_map_on_agree') (by100 auto)
      qed
      have h1mt: "top1_continuous_map_on ((Y - {q}) \<times> I_set) ?PT
          (UNIV :: real set) ?OT (\<lambda>(y,t). 1 - t)"
      proof -
        have "top1_continuous_map_on ((Y - {q}) \<times> I_set) ?PT
            (UNIV :: real set) ?OT (\<lambda>x. (\<lambda>_. 1::real) x + (\<lambda>(y,t). - t) x)"
          using top1_continuous_add_real[OF hprod_top hconst_1 hnt] by (by100 blast)
        thus ?thesis by (rule top1_continuous_map_on_agree') (by100 auto)
      qed
      \<comment> \<open>Product: (1-t) * angle(y).\<close>
      have hprod1: "top1_continuous_map_on ((Y - {q}) \<times> I_set) ?PT
          (UNIV :: real set) ?OT (\<lambda>(y,t). (1 - t) * angle y)"
      proof -
        have "top1_continuous_map_on ((Y - {q}) \<times> I_set) ?PT
            (UNIV :: real set) ?OT (\<lambda>x. (case x of (y,t) \<Rightarrow> 1 - t) * (case x of (y,t) \<Rightarrow> angle y))"
          using top1_continuous_mul_real[OF hprod_top h1mt hf_angle] by (by100 blast)
        thus ?thesis by (rule top1_continuous_map_on_agree') (by100 auto)
      qed
      \<comment> \<open>Product: t * \<theta>r.\<close>
      have hprod2: "top1_continuous_map_on ((Y - {q}) \<times> I_set) ?PT
          (UNIV :: real set) ?OT (\<lambda>(y,t). t * \<theta>r)"
      proof -
        have hraw: "top1_continuous_map_on ((Y - {q}) \<times> I_set) ?PT
            (UNIV :: real set) ?OT (\<lambda>x. (case x of (y,t) \<Rightarrow> t) * \<theta>r)"
          using top1_continuous_mul_real[OF hprod_top hpi2_OT hconst_thr] by (by100 simp)
        show ?thesis using top1_continuous_map_on_agree'[OF hraw] by (by100 auto)
      qed
      \<comment> \<open>Sum: (1-t)*angle(y) + t*\<theta>r.\<close>
      have hsum: "top1_continuous_map_on ((Y - {q}) \<times> I_set) ?PT
          (UNIV :: real set) ?OT (\<lambda>(y,t). (1 - t) * angle y + t * \<theta>r)"
      proof -
        have "top1_continuous_map_on ((Y - {q}) \<times> I_set) ?PT
            (UNIV :: real set) ?OT (\<lambda>x. (case x of (y,t) \<Rightarrow> (1 - t) * angle y) +
                                         (case x of (y,t) \<Rightarrow> t * \<theta>r))"
          using top1_continuous_add_real[OF hprod_top hprod1 hprod2] by (by100 blast)
        thus ?thesis by (rule top1_continuous_map_on_agree') (by100 auto)
      qed
      show ?thesis using hsum hTR_eq by (by100 simp)
    qed
    \<comment> \<open>R\_to\_S1 \<circ> lc continuous: (Y-{q})\<times>I \<rightarrow> S1.\<close>
    have hh_cont: "top1_continuous_map_on top1_S1 top1_S1_topology Y TY h"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hR_S1_cont: "top1_continuous_map_on (UNIV :: real set) top1_open_sets
        top1_S1 top1_S1_topology top1_R_to_S1"
      using top1_covering_map_on_continuous[OF Theorem_53_1] by (by100 blast)
    have hR_lc: "top1_continuous_map_on ((Y - {q}) \<times> I_set)
        (product_topology_on (subspace_topology Y TY (Y - {q})) I_top)
        top1_S1 top1_S1_topology (\<lambda>(y,t). top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r))"
    proof (rule continuous_map_onI)
      show "\<forall>x \<in> (Y - {q}) \<times> I_set. (case x of (y,t) \<Rightarrow> top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r)) \<in> top1_S1"
      proof
        fix x assume "x \<in> (Y - {q}) \<times> I_set"
        then obtain y t where "x = (y, t)" "y \<in> Y - {q}" "t \<in> I_set" by (by100 blast)
        thus "(case x of (y,t) \<Rightarrow> top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r)) \<in> top1_S1"
          unfolding top1_R_to_S1_def top1_S1_def by (by100 simp)
      qed
      show "\<forall>V \<in> top1_S1_topology. {x \<in> (Y - {q}) \<times> I_set.
          (case x of (y,t) \<Rightarrow> top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r)) \<in> V}
          \<in> product_topology_on (subspace_topology Y TY (Y - {q})) I_top"
      proof
        fix V assume "V \<in> top1_S1_topology"
        have hpre_R: "{x \<in> (UNIV :: real set). top1_R_to_S1 x \<in> V} \<in> top1_open_sets"
          using continuous_map_preimage_open[OF hR_S1_cont \<open>V \<in> top1_S1_topology\<close>] by (by100 blast)
        have hpre_lc: "{x \<in> (Y - {q}) \<times> I_set.
            (case x of (y,t) \<Rightarrow> (1 - t) * angle y + t * \<theta>r) \<in> {x \<in> UNIV. top1_R_to_S1 x \<in> V}}
            \<in> product_topology_on (subspace_topology Y TY (Y - {q})) I_top"
          using continuous_map_preimage_open[OF hlc hpre_R] by (by100 blast)
        moreover have "{x \<in> (Y - {q}) \<times> I_set.
            (case x of (y,t) \<Rightarrow> top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r)) \<in> V}
            = {x \<in> (Y - {q}) \<times> I_set.
            (case x of (y,t) \<Rightarrow> (1 - t) * angle y + t * \<theta>r) \<in> {x \<in> UNIV. top1_R_to_S1 x \<in> V}}"
          by (by5000 auto)
        ultimately show "{x \<in> (Y - {q}) \<times> I_set.
            (case x of (y,t) \<Rightarrow> top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r)) \<in> V}
            \<in> product_topology_on (subspace_topology Y TY (Y - {q})) I_top"
          by (by100 simp)
      qed
    qed
    \<comment> \<open>h \<circ> (R\_to\_S1 \<circ> lc) continuous: (Y-{q})\<times>I \<rightarrow> Y.\<close>
    have hF_Y: "top1_continuous_map_on ((Y - {q}) \<times> I_set)
        (product_topology_on (subspace_topology Y TY (Y - {q})) I_top)
        Y TY (\<lambda>(y,t). h (top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r)))"
    proof (rule continuous_map_onI)
      show "\<forall>x \<in> (Y - {q}) \<times> I_set. (case x of (y,t) \<Rightarrow> h (top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r))) \<in> Y"
      proof
        fix x assume "x \<in> (Y - {q}) \<times> I_set"
        then obtain y t where "x = (y, t)" "y \<in> Y - {q}" "t \<in> I_set" by (by100 blast)
        have "F (y, t) \<in> Y - {q}" using hF_image \<open>y \<in> Y - {q}\<close> \<open>t \<in> I_set\<close> by (by100 blast)
        thus "(case x of (y,t) \<Rightarrow> h (top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r))) \<in> Y"
          using \<open>x = (y, t)\<close> unfolding F_def by (by100 simp)
      qed
      show "\<forall>V \<in> TY. {x \<in> (Y - {q}) \<times> I_set.
          (case x of (y,t) \<Rightarrow> h (top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r))) \<in> V}
          \<in> product_topology_on (subspace_topology Y TY (Y - {q})) I_top"
      proof
        fix V assume "V \<in> TY"
        have hpre_h: "{s \<in> top1_S1. h s \<in> V} \<in> top1_S1_topology"
          using continuous_map_preimage_open[OF hh_cont \<open>V \<in> TY\<close>] by (by100 blast)
        have hpre_Rlc: "{x \<in> (Y - {q}) \<times> I_set.
            (case x of (y,t) \<Rightarrow> top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r)) \<in>
              {s \<in> top1_S1. h s \<in> V}}
            \<in> product_topology_on (subspace_topology Y TY (Y - {q})) I_top"
          using continuous_map_preimage_open[OF hR_lc hpre_h] by (by100 blast)
        show "{x \<in> (Y - {q}) \<times> I_set.
            (case x of (y,t) \<Rightarrow> h (top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r))) \<in> V}
            \<in> product_topology_on (subspace_topology Y TY (Y - {q})) I_top"
        proof -
          have hR_in_S1: "\<And>x::real. top1_R_to_S1 x \<in> top1_S1"
            unfolding top1_R_to_S1_def top1_S1_def by (by100 simp)
          have "{x \<in> (Y - {q}) \<times> I_set.
              (case x of (y,t) \<Rightarrow> h (top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r))) \<in> V}
              \<subseteq> {x \<in> (Y - {q}) \<times> I_set.
              (case x of (y,t) \<Rightarrow> top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r)) \<in>
                {s \<in> top1_S1. h s \<in> V}}"
            using hR_in_S1 by (by5000 force)
          moreover have "{x \<in> (Y - {q}) \<times> I_set.
              (case x of (y,t) \<Rightarrow> top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r)) \<in>
                {s \<in> top1_S1. h s \<in> V}}
              \<subseteq> {x \<in> (Y - {q}) \<times> I_set.
              (case x of (y,t) \<Rightarrow> h (top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r))) \<in> V}"
            by (by5000 force)
          ultimately have heq: "{x \<in> (Y - {q}) \<times> I_set.
              (case x of (y,t) \<Rightarrow> h (top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r))) \<in> V}
              = {x \<in> (Y - {q}) \<times> I_set.
              (case x of (y,t) \<Rightarrow> top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r)) \<in>
                {s \<in> top1_S1. h s \<in> V}}" by (by100 blast)
          show ?thesis using hpre_Rlc heq by (by100 simp)
        qed
      qed
    qed
    \<comment> \<open>Restrict codomain to Y-{q} using Theorem\_18\_2(5) and hF\_image.\<close>
    have hF_cont: "top1_continuous_map_on ((Y - {q}) \<times> I_set)
        (product_topology_on (subspace_topology Y TY (Y - {q})) I_top)
        (Y - {q}) (subspace_topology Y TY (Y - {q})) F"
    proof -
      have hF_agree: "\<forall>x \<in> (Y - {q}) \<times> I_set.
          (case x of (y,t) \<Rightarrow> h (top1_R_to_S1 ((1 - t) * angle y + t * \<theta>r))) = F x"
        unfolding F_def by (by100 auto)
      have hF_Y': "top1_continuous_map_on ((Y - {q}) \<times> I_set)
          (product_topology_on (subspace_topology Y TY (Y - {q})) I_top) Y TY F"
        using top1_continuous_map_on_agree[OF hF_Y hF_agree] by (by100 blast)
      have hF_sub: "F ` ((Y - {q}) \<times> I_set) \<subseteq> Y - {q}"
      proof
        fix z assume "z \<in> F ` ((Y - {q}) \<times> I_set)"
        then obtain y t where "z = F (y, t)" "y \<in> Y - {q}" "t \<in> I_set" by (by100 blast)
        thus "z \<in> Y - {q}" using hF_image by (by100 blast)
      qed
      have hYq_sub: "Y - {q} \<subseteq> Y" by (by100 blast)
      show ?thesis
        using Theorem_18_2(5)[OF hprod_top hTY_top hTY_top] hF_Y' hF_sub hYq_sub
        by (by5000 blast)
    qed
    show "\<exists>H. top1_continuous_map_on ((Y - {q}) \<times> I_set)
        (product_topology_on (subspace_topology Y TY (Y - {q})) I_top)
        (Y - {q}) (subspace_topology Y TY (Y - {q})) H
      \<and> (\<forall>y\<in>Y - {q}. H (y, 0) = y) \<and> (\<forall>y\<in>Y - {q}. H (y, 1) \<in> {r})
      \<and> (\<forall>a\<in>{r}. \<forall>t\<in>I_set. H (a, t) = a)"
      apply (rule exI[of _ F])
      using hF_cont hF_id hF_r hF_fix by (by100 blast)
  qed
qed

end
