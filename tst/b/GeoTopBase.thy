theory GeoTopBase
  imports "Top0.AlgTop" "HOL-Analysis.Cartesian_Euclidean_Space"
          "HOL-Analysis.Smooth_Paths" "HOL-Analysis.Further_Topology"
begin

ML \<open>
  fun method_evaluate text ctxt facts =
    NO_CONTEXT_TACTIC ctxt (Method.evaluate_runtime text ctxt facts)

  fun timed_seq name limit seq =
    Seq.make (fn () =>
      (case
         (Timeout.apply limit (fn () => Seq.pull seq) ()
           handle Timeout.TIMEOUT _ =>
             error (name ^ ": timeout after " ^
               string_of_int (Time.toMilliseconds limit) ^ " ms"))
       of
         NONE => NONE
       | SOME (st, seq') => SOME (st, timed_seq name limit seq')))
\<close>

method_setup by100 =
  \<open>
    Method.text_closure >> (fn text => fn ctxt => fn facts =>
      let
        val limit = Time.fromMilliseconds 100
        fun tac st = timed_seq "by100" limit (method_evaluate text ctxt facts st)
      in
        SIMPLE_METHOD tac facts
      end)
  \<close>
  "apply a proof method with 100ms timeout per result step"


text \<open>
  Formalization of geometric topology from Moise's "Geometric topology in dimensions 2 and 3"
  (geotop.tex). This file follows the source text section-by-section, starting from the
  Introduction and proceeding through the 36 numbered sections.

  Convention: definitions and theorems are prefixed with \<open>geotop_\<close> or use the book's numbering
  (Theorem_GT_N) as named identifiers. Before each item we include an origin comment of the form:
  \<open>(** from \<S>N Theorem/Lemma K: brief description (geotop.tex:LINE) **)\<close>
  \<open>(** LATEX VERSION: ... **)\<close>

  This file uses the previously developed general topology in Top0, including \<open>top1_metric_on\<close>,
  \<open>is_topology_on\<close>, \<open>is_topology_on_strict\<close>, \<open>top1_continuous_map_on\<close>,
  \<open>top1_connected_on\<close>, \<open>top1_path_connected_on\<close>, and related notions.
\<close>

section \<open>Introduction: Basic definitions from Moise\<close>

subsection \<open>Metric notions ($\varepsilon$-neighborhoods)\<close>

(** from Introduction: N(P,\<epsilon>) definition (geotop.tex:64)
    LATEX VERSION: N(P,\<epsilon>) = {Q | Q \<in> X and d(P,Q) < \<epsilon>} **)
text \<open>The open \<epsilon>-neighborhood of a point, written $N(P,\varepsilon)$ in Moise.
  This is the same as \<open>top1_ball_on X d P \<epsilon>\<close> from Top0.\<close>

definition geotop_nbhd_pt :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a set" where
  "geotop_nbhd_pt X d P \<epsilon> = top1_ball_on X d P \<epsilon>"

(** from Introduction: N(M,\<epsilon>) \<epsilon>-neighborhood of a set (geotop.tex:70)
    LATEX VERSION: N(M,\<epsilon>) = {Q | Q \<in> X and d(P,Q) < \<epsilon> for some P \<in> M} **)
definition geotop_nbhd_set :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 'a set" where
  "geotop_nbhd_set X d M \<epsilon> = {Q \<in> X. \<exists>P\<in>M. d P Q < \<epsilon>}"

(** from Introduction: neighborhood system induced by d (geotop.tex:79)
    LATEX VERSION: \<^bold>N = \<^bold>N(d) = {N(P,\<epsilon>) | P \<in> X and \<epsilon> > 0} **)
definition geotop_nbhd_system :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set set" where
  "geotop_nbhd_system X d = {geotop_nbhd_pt X d P \<epsilon> | P \<epsilon>. P \<in> X \<and> \<epsilon> > 0}"

subsection \<open>Subspace, frontier, interior (reprise from general topology)\<close>

(** from Introduction: Frontier of U in X (geotop.tex:196)
    LATEX VERSION: Fr U = Fr_X U = \<bar>U\<close> \<inter> \<bar>X - U\<close> **)
definition geotop_frontier :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "geotop_frontier X T U = closure_on X T U \<inter> closure_on X T (X - U)"

(** from Introduction: topological interior (geotop.tex:200)
    LATEX VERSION: the topological interior of M in X is the union of all open sets that lie in M **)
definition geotop_top_interior :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "geotop_top_interior X T M = \<Union>{U. U \<in> T \<and> U \<subseteq> M}"

subsection \<open>Vectors, hyperplanes, general position, convexity\<close>

(** from Introduction: hyperplane in R^m (geotop.tex:101)
    LATEX VERSION: H = V + v_0 where V is a vector subspace, H is a k-dimensional hyperplane
      if dim V = k **)
text \<open>We work in \<open>real \<times> real\<close>-like $\mathbf{R}^m$ via \<open>'a::real_vector\<close> when appropriate.
  For the concrete developments in dimensions 2 and 3, we will often specialize to \<open>real ^ m\<close>.\<close>

definition geotop_is_hyperplane :: "'a::real_vector set \<Rightarrow> bool" where
  "geotop_is_hyperplane H \<longleftrightarrow>
    (\<exists>V v0. subspace V \<and> H = (\<lambda>v. v + v0) ` V)"

definition geotop_hyperplane_dim :: "'a::real_vector set \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_hyperplane_dim H k \<longleftrightarrow>
    (\<exists>V v0. subspace V \<and> (\<exists>B. independent B \<and> finite B \<and> card B = k \<and> span B = V)
         \<and> H = (\<lambda>v. v + v0) ` V)"

(** from Introduction: general position in R^m (geotop.tex:107)
    LATEX VERSION: V \<subset> R^m is in general position if no k-dimensional hyperplane (k < m)
      contains more than k+1 points of V **)
definition geotop_general_position :: "'a::real_vector set \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_general_position V m \<longleftrightarrow>
    (\<forall>H k. geotop_hyperplane_dim H k \<and> k < m \<longrightarrow> finite (V \<inter> H) \<and> card (V \<inter> H) \<le> k+1)"

(** from Introduction: convex set (geotop.tex:109)
    LATEX VERSION: W \<subset> R^m is convex if for each v,w \<in> W, W contains the segment vw **)
definition geotop_segment :: "'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "geotop_segment v w = {u. \<exists>\<alpha> \<beta>. \<alpha> \<ge> 0 \<and> \<beta> \<ge> 0 \<and> \<alpha> + \<beta> = 1 \<and> u = \<alpha> *\<^sub>R v + \<beta> *\<^sub>R w}"

definition geotop_convex :: "'a::real_vector set \<Rightarrow> bool" where
  "geotop_convex W \<longleftrightarrow> (\<forall>v\<in>W. \<forall>w\<in>W. geotop_segment v w \<subseteq> W)"

(** from Introduction: convex hull (geotop.tex:115)
    LATEX VERSION: convex hull of X \<subset> R^m is the smallest convex subset of R^m containing X,
      i.e., the intersection of all convex subsets of R^m that contain X **)
definition geotop_convex_hull :: "'a::real_vector set \<Rightarrow> 'a set" where
  "geotop_convex_hull X = \<Inter>{W. geotop_convex W \<and> X \<subseteq> W}"

(** Bridge: Moise's geotop_convex coincides with HOL-Analysis's convex. **)
lemma geotop_convex_iff_HOL_convex:
  fixes S :: "'a::real_vector set"
  shows "geotop_convex S \<longleftrightarrow> convex S"
  unfolding geotop_convex_def geotop_segment_def convex_def by (by100 blast)

(** The geotop convex hull coincides with HOL-Analysis's convex hull. **)
lemma geotop_convex_hull_eq_HOL:
  fixes V :: "'a::real_vector set"
  shows "geotop_convex_hull V = convex hull V"
proof -
  have "{W. geotop_convex W \<and> V \<subseteq> W} = {W. convex W \<and> V \<subseteq> W}"
    using geotop_convex_iff_HOL_convex by (by100 auto)
  then show ?thesis
    unfolding geotop_convex_hull_def hull_def by (by100 simp)
qed

(** Helper: for a finite V and a map f satisfying bary-linearity on V,
    f \`\` (conv V) \<subseteq> conv (f \`\` V). No injectivity required.
    Key insight: x \<in> conv V has bary \<alpha>; f(x) = \<Sum> \<alpha>(v) f(v) ∈ conv(f V)
    via grouping duplicates of f-values. **)
lemma geotop_bary_lin_image_subset_hull:
  fixes V :: "'a::euclidean_space set" and f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes hVfin: "finite V"
  assumes h_bary: "\<And>\<alpha>. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<Longrightarrow> sum \<alpha> V = 1 \<Longrightarrow>
                        f (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
  shows "f ` (convex hull V) \<subseteq> convex hull (f ` V)"
proof
  fix y assume "y \<in> f ` (convex hull V)"
  (** (1) Unpack y = f x with x in conv V. **)
  then obtain x where hx: "x \<in> convex hull V" and hy: "y = f x" by (by100 blast)
  (** (2) Extract barycentric coordinates of x over V. **)
  obtain \<alpha> where h\<alpha>_nn: "\<forall>v\<in>V. 0 \<le> \<alpha> v" and h\<alpha>_sum: "sum \<alpha> V = 1"
              and h\<alpha>_eq: "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = x"
    using hx convex_hull_finite[OF hVfin] by (by100 blast)
  (** (3) Apply bary-linearity: f(x) = \<Sum> \<alpha> v *R f v. **)
  have hfx: "f x = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
    using h\<alpha>_eq[symmetric] h_bary[OF h\<alpha>_nn h\<alpha>_sum] by (by100 simp)
  (** (4) Regroup by f-value: define \<beta> w = sum of \<alpha> over preimage of w in V. **)
  define \<beta> where "\<beta> = (\<lambda>w. (\<Sum>v\<in>V \<inter> f -` {w}. \<alpha> v))"
  have h_sum_regroup: "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v) = (\<Sum>w\<in>f`V. \<beta> w *\<^sub>R w)"
  proof -
    have h_eq_set: "\<And>w. V \<inter> f -` {w} = {v\<in>V. f v = w}" by (by100 blast)
    (** Step 4a: image_gen regroups by f-value. **)
    have h4a: "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)
             = (\<Sum>w\<in>f`V. \<Sum>v\<in>V \<inter> f -` {w}. \<alpha> v *\<^sub>R f v)"
      using sum.image_gen[OF hVfin, of "\<lambda>v. \<alpha> v *\<^sub>R f v" f] h_eq_set by (by100 simp)
    (** Step 4b: on the preimage, f v = w so α v *R f v = α v *R w. **)
    have h4b: "\<And>w. (\<Sum>v\<in>V \<inter> f -` {w}. \<alpha> v *\<^sub>R f v)
                 = (\<Sum>v\<in>V \<inter> f -` {w}. \<alpha> v *\<^sub>R w)"
    proof -
      fix w
      show "(\<Sum>v\<in>V \<inter> f -` {w}. \<alpha> v *\<^sub>R f v)
              = (\<Sum>v\<in>V \<inter> f -` {w}. \<alpha> v *\<^sub>R w)"
        by (rule sum.cong) (by100 auto)+
    qed
    (** Step 4c: factor scalar out. **)
    have h4c: "\<And>w. (\<Sum>v\<in>V \<inter> f -` {w}. \<alpha> v *\<^sub>R w) = \<beta> w *\<^sub>R w"
      unfolding \<beta>_def using scaleR_left.sum[symmetric] by (by100 simp)
    (** Combine. **)
    have h4d: "(\<Sum>w\<in>f`V. \<Sum>v\<in>V \<inter> f -` {w}. \<alpha> v *\<^sub>R f v)
             = (\<Sum>w\<in>f`V. \<beta> w *\<^sub>R w)"
      using h4b h4c by (by100 simp)
    from h4a have s1: "(\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v) = (\<Sum>w\<in>f`V. \<Sum>v\<in>V \<inter> f -` {w}. \<alpha> v *\<^sub>R f v)" .
    also from h4d have s2: "\<dots> = (\<Sum>w\<in>f`V. \<beta> w *\<^sub>R w)" .
    finally show ?thesis .
  qed
  (** (5) \<beta> is nonneg (sum of nonneg). **)
  have h\<beta>_nn: "\<forall>w\<in>f`V. 0 \<le> \<beta> w"
  proof
    fix w assume "w \<in> f`V"
    have h_sub: "V \<inter> f -` {w} \<subseteq> V" by (by100 blast)
    have h_each: "\<And>v. v \<in> V \<inter> f -` {w} \<Longrightarrow> 0 \<le> \<alpha> v"
      using h\<alpha>_nn h_sub by (by100 blast)
    have "0 \<le> (\<Sum>v\<in>V \<inter> f -` {w}. \<alpha> v)"
      using sum_nonneg[of "V \<inter> f -` {w}" \<alpha>] h_each by (by100 blast)
    thus "0 \<le> \<beta> w" unfolding \<beta>_def by (by100 simp)
  qed
  (** (6) \<beta> sums to 1 (double-sum equals sum \<alpha> V = 1). **)
  have h\<beta>_sum: "sum \<beta> (f`V) = 1"
  proof -
    have h1: "sum \<beta> (f`V) = (\<Sum>w\<in>f`V. \<Sum>v\<in>V \<inter> f -` {w}. \<alpha> v)"
      unfolding \<beta>_def by (by100 simp)
    have h_eq_set: "\<And>w. V \<inter> f -` {w} = {v. v \<in> V \<and> f v = w}" by (by100 blast)
    have h2: "(\<Sum>w\<in>f`V. \<Sum>v\<in>V \<inter> f -` {w}. \<alpha> v) = sum \<alpha> V"
      using sum.image_gen[OF hVfin, of \<alpha> f, symmetric] h_eq_set by (by100 simp)
    from h1 have "sum \<beta> (f`V) = (\<Sum>w\<in>f`V. \<Sum>v\<in>V \<inter> f -` {w}. \<alpha> v)" .
    also from h2 have "\<dots> = sum \<alpha> V" .
    also from h\<alpha>_sum have "\<dots> = 1" .
    finally show ?thesis .
  qed
  (** (7) Hence f(x) in conv(f``V). **)
  have h_fVfin: "finite (f`V)" using hVfin by (by100 simp)
  have h_final: "(\<Sum>w\<in>f`V. \<beta> w *\<^sub>R w) \<in> convex hull (f ` V)"
    using convex_hull_finite[OF h_fVfin] h\<beta>_nn h\<beta>_sum by (by100 blast)
  from hy have "y = f x" .
  also from hfx have "\<dots> = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)" .
  also from h_sum_regroup have "\<dots> = (\<Sum>w\<in>f`V. \<beta> w *\<^sub>R w)" .
  finally have "y = (\<Sum>w\<in>f`V. \<beta> w *\<^sub>R w)" .
  then show "y \<in> convex hull (f ` V)" using h_final by (by100 simp)
qed

(** Helper (backward direction): with injectivity and bary-linearity,
    conv (f \`\` V) \<subseteq> f \`\` (conv V). Each y in conv(f\`V) lifts via
    inv_into V f to a bary combination over V. **)
lemma geotop_bary_lin_inj_image_superset_hull:
  fixes V :: "'a::euclidean_space set" and f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes hVfin: "finite V"
  assumes h_inj: "inj_on f V"
  assumes h_bary: "\<And>\<alpha>. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<Longrightarrow> sum \<alpha> V = 1 \<Longrightarrow>
                        f (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
  shows "convex hull (f ` V) \<subseteq> f ` (convex hull V)"
proof
  fix y assume hy_in: "y \<in> convex hull (f ` V)"
  have h_fVfin: "finite (f ` V)" using hVfin by (by100 simp)
  (** (1) Extract bary coords u on f V. **)
  have h_hull_char: "convex hull (f ` V) =
                      {z. \<exists>u. (\<forall>x\<in>f`V. 0 \<le> u x) \<and> sum u (f ` V) = 1
                              \<and> (\<Sum>x\<in>f`V. u x *\<^sub>R x) = z}"
    by (rule convex_hull_finite[OF h_fVfin])
  have h_ex: "\<exists>u. (\<forall>x\<in>f`V. 0 \<le> u x) \<and> sum u (f ` V) = 1
                  \<and> (\<Sum>x\<in>f`V. u x *\<^sub>R x) = y"
    using hy_in h_hull_char by (by100 blast)
  obtain u where hu_nn: "\<forall>w\<in>f`V. 0 \<le> u w" and hu_sum: "sum u (f ` V) = 1"
              and hy_raw: "(\<Sum>w\<in>f`V. u w *\<^sub>R w) = y"
    using h_ex by (by100 blast)
  (** (2) Lift to V via t v = u(f v). **)
  define t :: "'a \<Rightarrow> real" where "t v = u (f v)" for v
  have h_t_nn: "\<forall>v\<in>V. 0 \<le> t v" unfolding t_def using hu_nn by (by100 blast)
  have h_t_sum: "sum t V = 1"
  proof -
    have h1: "sum t V = sum (u \<circ> f) V" unfolding t_def by (by100 simp)
    have h_re: "sum u (f ` V) = sum (u \<circ> f) V" by (rule sum.reindex[OF h_inj])
    show ?thesis using h1 h_re hu_sum by (by100 simp)
  qed
  (** (3) x = Σ t v *R v is in conv V. **)
  define x where "x = (\<Sum>v\<in>V. t v *\<^sub>R v)"
  have hx_hull: "x \<in> convex hull V"
    unfolding x_def convex_hull_finite[OF hVfin]
    using h_t_nn h_t_sum by (by100 blast)
  (** (4) f x = y via bary and reindex. **)
  have h_fx: "f x = (\<Sum>v\<in>V. t v *\<^sub>R f v)"
    unfolding x_def using h_bary[OF h_t_nn h_t_sum] by (by100 simp)
  have h_vec_eq: "(\<Sum>v\<in>V. t v *\<^sub>R f v) = (\<Sum>w\<in>f`V. u w *\<^sub>R w)"
  proof -
    have hs1: "(\<Sum>v\<in>V. t v *\<^sub>R f v) = (\<Sum>v\<in>V. u (f v) *\<^sub>R f v)"
      unfolding t_def by (by100 simp)
    have hs2: "(\<Sum>v\<in>V. u (f v) *\<^sub>R f v) = sum ((\<lambda>w. u w *\<^sub>R w) \<circ> f) V"
      by (by100 simp)
    have h_re: "sum (\<lambda>w. u w *\<^sub>R w) (f ` V) = sum ((\<lambda>w. u w *\<^sub>R w) \<circ> f) V"
      by (rule sum.reindex[OF h_inj])
    from hs1 have "(\<Sum>v\<in>V. t v *\<^sub>R f v) = (\<Sum>v\<in>V. u (f v) *\<^sub>R f v)" .
    also from hs2 have "\<dots> = sum ((\<lambda>w. u w *\<^sub>R w) \<circ> f) V" .
    also from h_re have "\<dots> = (\<Sum>w\<in>f`V. u w *\<^sub>R w)" by (by100 simp)
    finally show ?thesis .
  qed
  have h_fx_y: "f x = y"
  proof -
    from h_fx have "f x = (\<Sum>v\<in>V. t v *\<^sub>R f v)" .
    also from h_vec_eq have "\<dots> = (\<Sum>w\<in>f`V. u w *\<^sub>R w)" .
    also from hy_raw have "\<dots> = y" .
    finally show ?thesis .
  qed
  show "y \<in> f ` (convex hull V)" using hx_hull h_fx_y by (by100 blast)
qed

(** Combined: under inj + bary-linearity, f preserves convex hulls. **)
lemma geotop_bary_lin_inj_image_hull_eq:
  fixes V :: "'a::euclidean_space set" and f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes hVfin: "finite V"
  assumes h_inj: "inj_on f V"
  assumes h_bary: "\<And>\<alpha>. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<Longrightarrow> sum \<alpha> V = 1 \<Longrightarrow>
                        f (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
  shows "f ` (convex hull V) = convex hull (f ` V)"
proof -
  have h_sub: "f ` (convex hull V) \<subseteq> convex hull (f ` V)"
    by (rule geotop_bary_lin_image_subset_hull[OF hVfin h_bary])
  have h_sup: "convex hull (f ` V) \<subseteq> f ` (convex hull V)"
    by (rule geotop_bary_lin_inj_image_superset_hull[OF hVfin h_inj h_bary])
  show ?thesis using h_sub h_sup by (by100 blast)
qed

subsection \<open>Simplexes and faces\<close>

(** from Introduction: n-dimensional simplex (geotop.tex:117)
    LATEX VERSION: Let V = {v_0,...,v_n} be n+1 points in general position in R^m with n \<le> m.
      Then \<sigma>^n = v_0 v_1 ... v_n is the convex hull of V. **)
definition geotop_is_simplex :: "'a::real_vector set \<Rightarrow> bool" where
  "geotop_is_simplex \<sigma> \<longleftrightarrow>
    (\<exists>V m n. finite V \<and> card V = n + 1 \<and> n \<le> m \<and> geotop_general_position V m
          \<and> \<sigma> = geotop_convex_hull V)"

definition geotop_simplex_dim :: "'a::real_vector set \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_simplex_dim \<sigma> n \<longleftrightarrow>
    (\<exists>V m. finite V \<and> card V = n + 1 \<and> n \<le> m \<and> geotop_general_position V m
         \<and> \<sigma> = geotop_convex_hull V)"

definition geotop_simplex_vertices :: "'a::real_vector set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_simplex_vertices \<sigma> V \<longleftrightarrow>
    (\<exists>m n. finite V \<and> card V = n + 1 \<and> n \<le> m \<and> geotop_general_position V m
         \<and> \<sigma> = geotop_convex_hull V)"

(** from Introduction: face of a simplex (geotop.tex:123)
    LATEX VERSION: The convex hull \<tau> of a nonempty subset W of V is called a face of \<sigma>^n.
      If \<tau> is a k-simplex, then \<tau> is called a k-face of \<sigma>^n. **)
definition geotop_is_face :: "'a::real_vector set \<Rightarrow> 'a::real_vector set \<Rightarrow> bool" where
  "geotop_is_face \<tau> \<sigma> \<longleftrightarrow>
    (\<exists>V W. geotop_simplex_vertices \<sigma> V \<and> W \<noteq> {} \<and> W \<subseteq> V \<and> \<tau> = geotop_convex_hull W)"

text \<open>Edge = 1-simplex (face).\<close>
definition geotop_is_edge :: "'a::real_vector set \<Rightarrow> bool" where
  "geotop_is_edge \<tau> \<longleftrightarrow> geotop_simplex_dim \<tau> 1"

subsection \<open>Euclidean complexes\<close>

(** from Introduction: (Euclidean) complex (geotop.tex:123)
    LATEX VERSION: A (Euclidean) complex is a collection K of simplexes in R^m such that
      (K.1) K contains all faces of all elements of K,
      (K.2) If \<sigma>, \<tau> \<in> K and \<sigma> \<inter> \<tau> \<noteq> \<emptyset>, then \<sigma> \<inter> \<tau> is a face both of \<sigma> and of \<tau>,
      (K.3) Every \<sigma> in K lies in an open set U which intersects only a finite number of
            elements of K. **)
definition geotop_is_complex :: "'a::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_is_complex K \<longleftrightarrow>
    (\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>)
    \<and> (\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K)
    \<and> (\<forall>\<sigma>\<in>K. \<forall>\<tau>\<in>K. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow> geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>)
    \<and> (\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}})"

(** from Introduction: vertices of a complex (geotop.tex:129)
    LATEX VERSION: The vertices of the elements of K will be called vertices of K. **)
definition geotop_complex_vertices :: "'a::real_normed_vector set set \<Rightarrow> 'a set" where
  "geotop_complex_vertices K = \<Union>{V. \<exists>\<sigma>\<in>K. geotop_simplex_vertices \<sigma> V}"

(** from Introduction: i-skeleton (geotop.tex:129)
    LATEX VERSION: For each i \<ge> 0, K^i is the i-skeleton of K, that is, the set of all simplexes
      of K that have dimension \<le> i. **)
definition geotop_skeleton :: "'a::real_normed_vector set set \<Rightarrow> nat \<Rightarrow> 'a set set" where
  "geotop_skeleton K i = {\<sigma>\<in>K. \<exists>n. n \<le> i \<and> geotop_simplex_dim \<sigma> n}"

(** from Introduction: |K| (geotop.tex:133)
    LATEX VERSION: |K| denotes the union of the elements of K, with the subspace topology
      induced by R^m. Such a set is called a polyhedron. If K is finite, |K| is a finite polyhedron. **)
definition geotop_polyhedron :: "'a::real_normed_vector set set \<Rightarrow> 'a set" where
  "geotop_polyhedron K = \<Union>K"

(** In a complex, the complex vertices are exactly the points whose singletons are
    0-simplexes of K. Forward: vertex in \<sigma> \<Rightarrow> {v} is a face of \<sigma> \<Rightarrow>
    {v} \<in> K by face-closure (extracted inline from geotop_is_complex_def).
    Backward: {v} \<in> K has simplex_vertices {v} {v} (direct). **)
lemma geotop_complex_vertices_eq_0_simplexes:
  fixes K :: "'a::real_normed_vector set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_complex_vertices K = {v. {v} \<in> K}"
proof (rule set_eqI, rule iffI)
  fix v assume hv: "v \<in> geotop_complex_vertices K"
  obtain \<sigma> V where h\<sigma>K: "\<sigma> \<in> K" and h\<sigma>V: "geotop_simplex_vertices \<sigma> V" and hvV: "v \<in> V"
    using hv unfolding geotop_complex_vertices_def by (by100 blast)
  (** \<open>{v}\<close> is a face of \<sigma>: take W = \<open>{v}\<close> subset of V with \<open>{v}\<close> = conv \<open>{v}\<close>. **)
  have hvhull: "{v} = geotop_convex_hull {v}"
    using geotop_convex_hull_eq_HOL[of "{v}"] by (by100 simp)
  have h_face: "geotop_is_face {v} \<sigma>"
    unfolding geotop_is_face_def
    using h\<sigma>V hvV hvhull by (by100 blast)
  have h_face_closed_raw: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    by (rule conjunct1[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]])
  show "v \<in> {v. {v} \<in> K}"
    using h_face_closed_raw h\<sigma>K h_face by (by100 blast)
next
  fix v assume hv: "v \<in> {v. {v} \<in> K}"
  hence hvK: "{v} \<in> K" by (by100 simp)
  (** simplex_vertices {v} {v}: finite, card=1, n=0, gp vacuous. **)
  have h_conv: "{v} = geotop_convex_hull {v}"
    using geotop_convex_hull_eq_HOL[of "{v}"] by (by100 simp)
  have h_gp: "geotop_general_position {v} 0"
    unfolding geotop_general_position_def by (by100 simp)
  have h_sv_body: "finite ({v}::'a set) \<and> card ({v}::'a set) = 0 + 1 \<and>
                    (0::nat) \<le> 0 \<and> geotop_general_position ({v}::'a set) 0 \<and>
                    ({v}::'a set) = geotop_convex_hull ({v}::'a set)"
    using h_conv h_gp by (by100 simp)
  have h_sv: "geotop_simplex_vertices {v} {v}"
    unfolding geotop_simplex_vertices_def
    using h_sv_body by (by100 blast)
  show "v \<in> geotop_complex_vertices K"
    unfolding geotop_complex_vertices_def
    using hvK h_sv by (by100 blast)
qed

(** Polyhedron of an image-of-simplexes complex: \<open>|f \<sup>`\<sup>` K| = f \<sup>` |K|\<close>.
    Useful for transport/pushforward of subdivisions through a bijection. **)
lemma geotop_polyhedron_image:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector" and K :: "'a set set"
  shows "geotop_polyhedron ((`) f ` K) = f ` geotop_polyhedron K"
  unfolding geotop_polyhedron_def by (by100 blast)

subsection \<open>Linear maps and simplicial maps\<close>

(** from Introduction: linear and simplicial maps (geotop.tex:164)
    LATEX VERSION: A function f: \<sigma> \<rightarrow> \<tau> is linear if the coordinates of f(P) are linear functions
      of those of P. If vertices are mapped onto vertices, then f is simplicial. **)
definition geotop_linear_on :: "'a::real_vector set \<Rightarrow> ('a \<Rightarrow> 'b::real_vector) \<Rightarrow> bool" where
  "geotop_linear_on \<sigma> f \<longleftrightarrow>
    (\<exists>V. geotop_simplex_vertices \<sigma> V \<and>
      (\<forall>\<alpha>. (\<forall>v\<in>V. \<alpha> v \<ge> 0) \<and> sum \<alpha> V = 1 \<longrightarrow>
         f (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)))"

definition geotop_simplicial_on :: "'a::real_vector set \<Rightarrow> ('a \<Rightarrow> 'b::real_vector) \<Rightarrow> 'b set \<Rightarrow> bool" where
  "geotop_simplicial_on \<sigma> f \<tau> \<longleftrightarrow>
    (\<exists>V W. geotop_simplex_vertices \<sigma> V \<and> geotop_simplex_vertices \<tau> W
        \<and> (\<forall>v\<in>V. f v \<in> W) \<and> geotop_linear_on \<sigma> f)"

subsection \<open>Refinement and subdivision\<close>

(** from Introduction: refinement relation (geotop.tex:166)
    LATEX VERSION: If every element of G is a subset of some element of H, then G is a
      refinement of H, written G \<le> H. **)
definition geotop_refines :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "geotop_refines G H \<longleftrightarrow> (\<forall>g\<in>G. \<exists>h\<in>H. g \<subseteq> h)"

(** from Introduction: subdivision (geotop.tex:168)
    LATEX VERSION: Let K and L be complexes, in the same space R^n. If L \<le> K and |L| = |K|,
      then L is a subdivision of K, written L < K. **)
definition geotop_is_subdivision :: "'a::real_normed_vector set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "geotop_is_subdivision L K \<longleftrightarrow>
    geotop_is_complex K \<and> geotop_is_complex L
    \<and> geotop_refines L K \<and> geotop_polyhedron L = geotop_polyhedron K"

subsection \<open>General position descent\<close>

(** Subsets of general-position sets inherit the general-position property. **)
(** Every singleton \<open>{v}\<close> is a 0-simplex with vertex set \<open>{v}\<close>. **)
lemma geotop_simplex_vertices_singleton:
  fixes v :: "'a::real_vector"
  shows "geotop_simplex_vertices {v} {v}"
  unfolding geotop_simplex_vertices_def
proof -
  have h_hull_v: "geotop_convex_hull ({v}::'a set) = {v}"
    using geotop_convex_hull_eq_HOL[of "{v}::'a set"] by (by100 simp)
  have h_gp: "geotop_general_position ({v}::'a set) 0"
    unfolding geotop_general_position_def by (by100 blast)
  show "\<exists>m n. finite {v} \<and> card {v} = n + 1 \<and> n \<le> m \<and>
              geotop_general_position {v} m \<and> {v} = geotop_convex_hull {v}"
    apply (rule exI[of _ "0::nat"])
    apply (rule exI[of _ "0::nat"])
    using h_hull_v h_gp by (by100 simp)
qed

lemma geotop_general_position_mono:
  fixes V W :: "'a::real_vector set"
  assumes hV: "geotop_general_position V m"
  assumes hWV: "W \<subseteq> V"
  assumes hWfin: "finite W"
  shows "geotop_general_position W m"
  unfolding geotop_general_position_def
proof (intro allI impI)
  fix H :: "'a set" and k :: nat
  assume hHk: "geotop_hyperplane_dim H k \<and> k < m"
  have hVk: "finite (V \<inter> H) \<and> card (V \<inter> H) \<le> k+1"
    using hV hHk unfolding geotop_general_position_def by (by100 blast)
  have hW_sub: "W \<inter> H \<subseteq> V \<inter> H" using hWV by (by100 blast)
  have hWfin_H: "finite (W \<inter> H)" using hWfin by (by100 blast)
  have "card (W \<inter> H) \<le> card (V \<inter> H)"
    using hW_sub hVk card_mono by (by100 blast)
  then have "card (W \<inter> H) \<le> k+1" using hVk by (by100 linarith)
  then show "finite (W \<inter> H) \<and> card (W \<inter> H) \<le> k+1" using hWfin_H by (by100 blast)
qed

subsection \<open>Vertex uniqueness for simplexes\<close>

(** A simplex \<open>\<sigma>\<close> has a unique vertex set: if \<open>\<sigma> = conv V\<^sub>1 = conv V\<^sub>2\<close> with
    both \<open>V\<^sub>1, V\<^sub>2\<close> satisfying \<open>geotop_simplex_vertices\<close>, then \<open>V\<^sub>1 = V\<^sub>2\<close>.
    Proof: for affinely independent finite \<open>V\<close>, the extreme points of \<open>conv V\<close>
    are exactly \<open>V\<close> (HOL \<open>extreme_point_of_convex_hull_affine_independent\<close>); the
    affine independence follows from \<open>geotop_general_position\<close> with the matching
    dimension parameter. **)
lemma geotop_general_position_imp_aff_indep:
  fixes V :: "'a::euclidean_space set"
  assumes hV: "geotop_simplex_vertices \<sigma> V"
  shows "\<not> affine_dependent V"
proof (rule ccontr)
  assume hAD: "\<not> \<not> affine_dependent V"
  then have hdep: "affine_dependent V" by (by100 blast)
  obtain m n where hVfin: "finite V" and hVcard: "card V = n+1" and hnm: "n \<le> m"
                 and hVgp: "geotop_general_position V m"
    using hV unfolding geotop_simplex_vertices_def by (by100 blast)
  (** \<open>¬affine_dependent\<close> iff \<open>aff_dim V = int(card V) - 1\<close>; so dependence ⇒ strict. **)
  have haff_le: "aff_dim V \<le> int (card V) - 1"
    using hVfin aff_dim_le_card by (by100 simp)
  have hdep_neq: "aff_dim V \<noteq> int (card V) - 1"
    using hdep hVfin affine_independent_iff_card by (by100 blast)
  have haff_lt: "aff_dim V < int (card V) - 1"
    using haff_le hdep_neq by (by100 linarith)
  have hdim_le: "aff_dim V \<le> int n - 1"
    using haff_lt hVcard by (by100 linarith)
  (** Take \<open>k = aff_dim V\<close> (nat). We have \<open>k \<le> n - 1 < n \<le> m\<close>, so \<open>k < m\<close>. **)
  define k::nat where "k = nat (aff_dim V)"
  have hVne: "V \<noteq> {}"
    using hVfin hVcard card_gt_0_iff by (by100 fastforce)
  have hk_nonneg: "aff_dim V \<ge> 0"
  proof -
    obtain a0 where ha0: "a0 \<in> V" using hVne by (by100 blast)
    have hsing_sub: "{a0} \<subseteq> V" using ha0 by (by100 blast)
    have h0_le: "aff_dim {a0} \<le> aff_dim V"
      by (rule aff_dim_subset[OF hsing_sub])
    have h_sing: "aff_dim {a0} = 0" by (by100 simp)
    show "aff_dim V \<ge> 0" using h0_le h_sing by (by100 simp)
  qed
  have hk_int: "int k = aff_dim V" unfolding k_def using hk_nonneg by (by100 simp)
  have hk_n: "k < n"
    using hdim_le hk_int hVcard hVne by (by100 linarith)
  have hk_m: "k < m" using hk_n hnm by (by100 linarith)
  (** \<open>affine hull V\<close> is a \<open>k\<close>-dim affine subspace containing \<open>V\<close>. Write it as
      a translate of a linear subspace of dim \<open>k\<close>. **)
  have hV_sub_aff: "V \<subseteq> affine hull V" by (rule hull_subset)
  obtain a where ha: "a \<in> V" using hVne by (by100 blast)
  define W where "W = (+)(-a) ` (V - {a})"
  define L where "L = span W"
  have hL_sub: "subspace L" unfolding L_def by (by100 simp)
  have haff_form: "affine hull V = (+) a ` L"
    using ha unfolding L_def W_def by (rule affine_hull_span2)
  (** The subspace \<open>L\<close> has a basis of size \<open>k\<close>. **)
  (** Build parallelism: \<open>affine hull V = (+) a ` L\<close>, so \<open>L = (+) (-a) ` affine hull V\<close>. **)
  have h_L_from: "(+) (-a) ` (affine hull V) = L"
  proof -
    have "(+) (-a) ` ((+) a ` L) = L"
      by (by100 force)
    thus ?thesis using haff_form by (by100 simp)
  qed
  have h_parallel: "affine_parallel (affine hull V) L"
    unfolding affine_parallel_def
    apply (rule exI[of _ "-a"])
    using h_L_from by (by100 simp)
  have h_aff_V: "aff_dim V = int (dim L)"
    by (rule aff_dim_parallel_subspace[OF hVne hL_sub h_parallel])
  have hL_dim: "dim L = k"
    using h_aff_V hk_int by (by100 simp)
  (** \<open>basis_exists\<close> gives \<open>B \<subseteq> L\<close>, \<open>independent B\<close>, \<open>L \<subseteq> span B\<close>, \<open>card B = dim L\<close>.
      Combine with \<open>span B \<subseteq> L\<close> (since \<open>B \<subseteq> L\<close>, \<open>subspace L\<close>, \<open>span\<close> is the smallest
      subspace containing B); and \<open>independent_bound\<close> gives \<open>finite B\<close>. **)
  obtain B where hB_sub: "B \<subseteq> L" and hB_indep: "independent B"
             and hB_span_sup: "L \<subseteq> span B" and hBcard_dim: "card B = dim L"
    using basis_exists[of L] by (by100 blast)
  have hBfin: "finite B" using independent_bound[OF hB_indep] by (by100 blast)
  have hBcard: "card B = k" using hBcard_dim hL_dim by (by100 simp)
  have hB_span_sub: "span B \<subseteq> L"
    by (rule span_minimal[OF hB_sub hL_sub])
  have hB_span: "span B = L"
    using hB_span_sub hB_span_sup by (by100 blast)
  (** Hence \<open>geotop_hyperplane_dim (affine hull V) k\<close>. **)
  define H where "H = (+) a ` L"
  have hH_eq: "H = affine hull V" unfolding H_def using haff_form by (by100 simp)
  have h_plusa_eq: "(+) a = (\<lambda>v. v + a)"
    by (intro ext) (rule add.commute)
  have h_plusa: "(+) a ` L = (\<lambda>v. v + a) ` L"
    using h_plusa_eq by (by100 simp)
  have hH_hpdim: "geotop_hyperplane_dim H k"
    unfolding geotop_hyperplane_dim_def H_def
    apply (rule exI[of _ L])
    apply (rule exI[of _ a])
    using hL_sub hB_indep hBfin hBcard hB_span h_plusa by (by100 blast)
  (** \<open>V \<subseteq> H\<close>, so \<open>V \<inter> H = V\<close> with \<open>card = n+1\<close>. **)
  have hV_H: "V \<subseteq> H" using hV_sub_aff hH_eq by (by100 simp)
  have hV_int_H: "V \<inter> H = V" using hV_H by (by100 blast)
  (** By general_position: \<open>card(V \<inter> H) \<le> k+1\<close>. **)
  have hgp_bound: "card (V \<inter> H) \<le> k+1"
    using hVgp hH_hpdim hk_m unfolding geotop_general_position_def by (by100 blast)
  have hbound: "n+1 \<le> k+1" using hV_int_H hVcard hgp_bound by (by100 simp)
  have hn_le_k: "n \<le> k" using hbound by (by100 linarith)
  show False using hn_le_k hk_n by (by100 linarith)
qed \<comment> \<open>\<open>card V = n+1\<close>, \<open>n \<le> m\<close>, and \<open>geotop_general_position V m\<close> together
           imply affine independence. Key step: if \<open>V\<close> were affinely dependent, it
           would lie in an \<open>(n-1)\<close>-dim affine subspace, contradicting
           \<open>card(V \<inter> H) \<le> k+1\<close> for the containing hyperplane.\<close>

(** Converse direction: AI + card n+1 gives general_position V n.
    Proof: for any k-hyperplane H with k < n, V \<inter> H is AI (subset of AI V),
    finite, and contained in a k-dim affine set H, so card(V \<inter> H) \<le> k+1
    via aff_dim reasoning. **)
lemma geotop_ai_imp_general_position:
  fixes V :: "'a::euclidean_space set"
  assumes hVfin: "finite V"
  assumes hVcard: "card V = n + 1"
  assumes hVai: "\<not> affine_dependent V"
  shows "geotop_general_position V n"
  unfolding geotop_general_position_def
proof (intro allI impI)
  fix H :: "'a set" and k :: nat
  assume "geotop_hyperplane_dim H k \<and> k < n"
  then have hHk: "geotop_hyperplane_dim H k" and hkn: "k < n" by auto
  (** H = (+) v0 ` U for subspace U of dim k. Hence H is affine of dim k. **)
  have hHk_unf_raw:
    "\<exists>V v0. subspace V \<and> (\<exists>B. independent B \<and> finite B \<and> card B = k \<and> span B = V)
          \<and> H = (\<lambda>v. v + v0) ` V"
    using hHk unfolding geotop_hyperplane_dim_def by (by100 simp)
  obtain U v0 where hU_sub: "subspace U"
                and hU_basis_ex: "\<exists>B. independent B \<and> finite B \<and> card B = k \<and> span B = U"
                and hH_eq: "H = (\<lambda>v. v + v0) ` U"
    using hHk_unf_raw by (by100 fast)
  obtain B where hB_indep: "independent B" and hB_fin: "finite B"
             and hB_card: "card B = k" and hB_span: "span B = U"
    using hU_basis_ex by (by100 blast)
  (** aff_dim U = int k (subspace dim = affine dim for subspaces). **)
  have hU_dim: "dim U = k"
  proof -
    have h1: "dim U = dim (span B)" using hB_span by (by100 simp)
    have h2: "dim (span B) = dim B" by (rule dim_span)
    have h3: "dim B = card B" using hB_indep by (rule dim_eq_card_independent)
    show ?thesis using h1 h2 h3 hB_card by (by100 simp)
  qed
  have hU_affine: "affine U" using hU_sub subspace_imp_affine by (by100 simp)
  have hU_ne: "U \<noteq> {}" using hU_sub subspace_0 by (by100 blast)
  have hU_aff_dim: "aff_dim U = int k"
    using hU_dim aff_dim_subspace[OF hU_sub] by (by100 simp)
  (** H = translate of U, aff_dim H = aff_dim U = k. **)
  have hH_eq_sym: "H = ((+) v0) ` U"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> H"
    then obtain u where hu: "u \<in> U" and hx: "x = u + v0"
      using hH_eq by (by100 blast)
    have "x = v0 + u" using hx by (by100 simp)
    then show "x \<in> (+) v0 ` U" using hu by (by100 blast)
  next
    fix x assume "x \<in> (+) v0 ` U"
    then obtain u where hu: "u \<in> U" and hx: "x = v0 + u" by (by100 blast)
    have "x = u + v0" using hx by (by100 simp)
    then show "x \<in> H" using hu hH_eq by (by100 blast)
  qed
  have hU_eq: "U = ((+) (-v0)) ` H"
  proof (rule set_eqI, rule iffI)
    fix u assume hu: "u \<in> U"
    have hx_in_H: "v0 + u \<in> H" using hu hH_eq_sym by (by100 blast)
    have hu_eq: "u = (-v0) + (v0 + u)" by (by100 simp)
    show "u \<in> (+) (-v0) ` H" using hu_eq hx_in_H by (by100 blast)
  next
    fix u assume "u \<in> (+) (-v0) ` H"
    then obtain x where hx: "x \<in> H" and hu: "u = -v0 + x" by (by100 blast)
    obtain w where hwU: "w \<in> U" and hxw: "x = v0 + w" using hx hH_eq_sym by (by100 blast)
    have "u = w" using hu hxw by (by100 simp)
    then show "u \<in> U" using hwU by (by100 simp)
  qed
  have hH_parallel: "affine_parallel H U"
    unfolding affine_parallel_def
    using hU_eq by (by100 blast)
  have hH_affine_step: "affine U = affine ((+) v0 ` U)"
    by (rule affine_translation)
  have hH_affine: "affine H"
    using hH_affine_step hU_affine hH_eq_sym by (by100 simp)
  have hH_ne: "H \<noteq> {}" using hU_ne hH_eq by (by100 simp)
  have hH_aff_dim: "aff_dim H = int k"
    using aff_dim_affine[OF hH_affine hU_sub hH_parallel hH_ne] hU_dim by (by100 simp)
  (** V \<inter> H is finite (subset of finite V) and AI (subset of AI V). **)
  have hVH_fin: "finite (V \<inter> H)" using hVfin by (by100 simp)
  have hVH_sub_V: "V \<inter> H \<subseteq> V" by (by100 blast)
  have hVH_ai: "\<not> affine_dependent (V \<inter> H)"
  proof
    assume h_dep: "affine_dependent (V \<inter> H)"
    have "affine_dependent V"
      using affine_dependent_subset[OF h_dep hVH_sub_V] by (by100 simp)
    thus False using hVai by (by100 blast)
  qed
  (** aff_dim (V \<inter> H) = card - 1 (finite + AI). Also \<le> aff_dim H = k. **)
  have hVH_card_eq: "int (card (V \<inter> H)) = aff_dim (V \<inter> H) + 1"
  proof -
    have h_iff: "(\<not> affine_dependent (V \<inter> H)) =
                  (finite (V \<inter> H) \<and> aff_dim (V \<inter> H) = int (card (V \<inter> H)) - 1)"
      by (rule affine_independent_iff_card)
    have h_eq: "aff_dim (V \<inter> H) = int (card (V \<inter> H)) - 1"
      using h_iff hVH_ai by (by100 blast)
    show ?thesis using h_eq by (by100 linarith)
  qed
  have hVH_in_H: "V \<inter> H \<subseteq> H" by (by100 blast)
  have hVH_aff_le: "aff_dim (V \<inter> H) \<le> aff_dim H"
    by (rule aff_dim_subset[OF hVH_in_H])
  have hVH_aff_le_k: "aff_dim (V \<inter> H) \<le> int k"
    using hVH_aff_le hH_aff_dim by (by100 simp)
  have hVH_card_le: "int (card (V \<inter> H)) \<le> int k + 1"
    using hVH_card_eq hVH_aff_le_k by (by100 linarith)
  have hVH_card_le_nat: "card (V \<inter> H) \<le> k + 1"
    using hVH_card_le by (by100 linarith)
  show "finite (V \<inter> H) \<and> card (V \<inter> H) \<le> k + 1"
    using hVH_fin hVH_card_le_nat by (by100 blast)
qed

lemma geotop_simplex_vertices_unique:
  fixes V\<^sub>1 V\<^sub>2 :: "'a::euclidean_space set" and \<sigma> :: "'a set"
  assumes h1: "geotop_simplex_vertices \<sigma> V\<^sub>1"
  assumes h2: "geotop_simplex_vertices \<sigma> V\<^sub>2"
  shows "V\<^sub>1 = V\<^sub>2"
proof -
  have h1_hull: "\<sigma> = convex hull V\<^sub>1"
    using h1 geotop_convex_hull_eq_HOL
    unfolding geotop_simplex_vertices_def by (by100 blast)
  have h2_hull: "\<sigma> = convex hull V\<^sub>2"
    using h2 geotop_convex_hull_eq_HOL
    unfolding geotop_simplex_vertices_def by (by100 blast)
  have h1_ai: "\<not> affine_dependent V\<^sub>1"
    by (rule geotop_general_position_imp_aff_indep[OF h1])
  have h2_ai: "\<not> affine_dependent V\<^sub>2"
    by (rule geotop_general_position_imp_aff_indep[OF h2])
  have h1_ext: "{x. x extreme_point_of convex hull V\<^sub>1} = V\<^sub>1"
    using extreme_point_of_convex_hull_affine_independent[OF h1_ai] by blast
  have h2_ext: "{x. x extreme_point_of convex hull V\<^sub>2} = V\<^sub>2"
    using extreme_point_of_convex_hull_affine_independent[OF h2_ai] by blast
  have hhull_eq: "convex hull V\<^sub>1 = convex hull V\<^sub>2"
    using h1_hull h2_hull by (by100 simp)
  have hext_eq: "{x. x extreme_point_of convex hull V\<^sub>1}
                  = {x. x extreme_point_of convex hull V\<^sub>2}"
    using hhull_eq by (by100 simp)
  have "V\<^sub>1 = {x. x extreme_point_of convex hull V\<^sub>1}" using h1_ext by (by100 simp)
  also have "\<dots> = {x. x extreme_point_of convex hull V\<^sub>2}" using hext_eq .
  also have "\<dots> = V\<^sub>2" using h2_ext by (by100 simp)
  finally show "V\<^sub>1 = V\<^sub>2" .
qed

(** Linearity on a simplex restricts to linearity on any face. Key technical lemma
    for PL-map transfer across subdivisions (e.g. hK12_witness in GT_5_1). **)
lemma geotop_linear_on_face:
  fixes \<sigma> \<tau> :: "'a::euclidean_space set" and f :: "'a \<Rightarrow> 'b::real_vector"
  assumes h_lin: "geotop_linear_on \<sigma> f"
  assumes h_face: "geotop_is_face \<tau> \<sigma>"
  shows "geotop_linear_on \<tau> f"
proof -
  (** (1) Unpack linear_on: obtain V with simplex_vertices \<sigma> V and the bary-linearity. **)
  obtain V where h_sv: "geotop_simplex_vertices \<sigma> V"
             and h_prop: "\<forall>\<alpha>. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1 \<longrightarrow>
                              f (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
    using h_lin unfolding geotop_linear_on_def by (by100 blast)
  (** (2) Unpack face: W \<subseteq> V' with \<tau> = conv(W); V' = V by vertex uniqueness. **)
  obtain V' W where h_sv': "geotop_simplex_vertices \<sigma> V'"
                and h_Wne: "W \<noteq> {}"
                and h_WV': "W \<subseteq> V'"
                and h_\<tau>hull: "\<tau> = geotop_convex_hull W"
    using h_face unfolding geotop_is_face_def by (by100 blast)
  have h_VV': "V = V'"
    by (rule geotop_simplex_vertices_unique[OF h_sv h_sv'])
  have h_WV: "W \<subseteq> V" using h_WV' h_VV' by (by100 simp)
  (** (3) simplex_vertices \<tau> W. **)
  obtain m n where h_Vfin: "finite V"
               and h_Vcard: "card V = n + 1"
               and h_nm: "n \<le> m"
               and h_Vgp: "geotop_general_position V m"
    using h_sv unfolding geotop_simplex_vertices_def by (by100 blast)
  have h_Wfin: "finite W" using h_Vfin h_WV by (rule finite_subset[rotated])
  define k where "k = card W - 1"
  have h_Wcard_pos: "card W > 0"
    using h_Wne h_Wfin by (by100 fastforce)
  have h_Wcard: "card W = k + 1" unfolding k_def using h_Wcard_pos by (by100 simp)
  have h_W_le_V: "card W \<le> card V" using h_WV h_Vfin card_mono by blast
  have h_k_n: "k \<le> n" using h_Wcard h_Vcard h_W_le_V by (by100 linarith)
  have h_k_m: "k \<le> m" using h_k_n h_nm by (by100 linarith)
  have h_Wgp: "geotop_general_position W m"
    by (rule geotop_general_position_mono[OF h_Vgp h_WV h_Wfin])
  have h_sv_\<tau>: "geotop_simplex_vertices \<tau> W"
    unfolding geotop_simplex_vertices_def
    using h_Wfin h_Wcard h_k_m h_Wgp h_\<tau>hull by (by100 blast)
  (** (4) Bary-linearity for W: extend any \<alpha> over W to \<alpha>' over V by 0 outside W. **)
  have h_prop_\<tau>: "\<forall>\<alpha>. (\<forall>v\<in>W. 0 \<le> \<alpha> v) \<and> sum \<alpha> W = 1 \<longrightarrow>
                      f (\<Sum>v\<in>W. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>W. \<alpha> v *\<^sub>R f v)"
  proof (intro allI impI)
    fix \<alpha> :: "'a \<Rightarrow> real"
    assume h\<alpha>: "(\<forall>v\<in>W. 0 \<le> \<alpha> v) \<and> sum \<alpha> W = 1"
    define \<alpha>' :: "'a \<Rightarrow> real" where "\<alpha>' v = (if v \<in> W then \<alpha> v else 0)" for v
    (** Sum of \<alpha>' over V equals sum of \<alpha> over W. **)
    have h_VW_inter: "V \<inter> W = W" using h_WV by (by100 blast)
    have h_sum_\<alpha>'_V: "sum \<alpha>' V = sum \<alpha> W"
    proof -
      have "sum \<alpha>' V = sum \<alpha>' W + sum \<alpha>' (V - W)"
        using h_Vfin h_WV sum.subset_diff[of W V \<alpha>'] by (by100 simp)
      also have "sum \<alpha>' W = sum \<alpha> W"
        unfolding \<alpha>'_def by (by100 simp)
      also have "sum \<alpha>' (V - W) = 0"
        unfolding \<alpha>'_def by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
    have h_sum_\<alpha>'_eq1: "sum \<alpha>' V = 1" using h_sum_\<alpha>'_V h\<alpha> by (by100 simp)
    have h_\<alpha>'_nn: "\<forall>v\<in>V. 0 \<le> \<alpha>' v"
      unfolding \<alpha>'_def using h\<alpha> by (by100 simp)
    (** Vector sum: \<Sum>_V \<alpha>' v *\<^sub>R v = \<Sum>_W \<alpha> v *\<^sub>R v. **)
    have h_vsum_eq: "(\<Sum>v\<in>V. \<alpha>' v *\<^sub>R v) = (\<Sum>v\<in>W. \<alpha> v *\<^sub>R v)"
    proof -
      have "(\<Sum>v\<in>V. \<alpha>' v *\<^sub>R v)
              = (\<Sum>v\<in>W. \<alpha>' v *\<^sub>R v) + (\<Sum>v\<in>V - W. \<alpha>' v *\<^sub>R v)"
        using h_Vfin h_WV sum.subset_diff[of W V "\<lambda>v. \<alpha>' v *\<^sub>R v"] by (by100 simp)
      also have "(\<Sum>v\<in>W. \<alpha>' v *\<^sub>R v) = (\<Sum>v\<in>W. \<alpha> v *\<^sub>R v)"
        unfolding \<alpha>'_def by (by100 simp)
      also have "(\<Sum>v\<in>V - W. \<alpha>' v *\<^sub>R v) = 0"
        unfolding \<alpha>'_def by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
    have h_fsum_eq: "(\<Sum>v\<in>V. \<alpha>' v *\<^sub>R f v) = (\<Sum>v\<in>W. \<alpha> v *\<^sub>R f v)"
    proof -
      have "(\<Sum>v\<in>V. \<alpha>' v *\<^sub>R f v)
              = (\<Sum>v\<in>W. \<alpha>' v *\<^sub>R f v) + (\<Sum>v\<in>V - W. \<alpha>' v *\<^sub>R f v)"
        using h_Vfin h_WV sum.subset_diff[of W V "\<lambda>v. \<alpha>' v *\<^sub>R f v"] by (by100 simp)
      also have "(\<Sum>v\<in>W. \<alpha>' v *\<^sub>R f v) = (\<Sum>v\<in>W. \<alpha> v *\<^sub>R f v)"
        unfolding \<alpha>'_def by (by100 simp)
      also have "(\<Sum>v\<in>V - W. \<alpha>' v *\<^sub>R f v) = 0"
        unfolding \<alpha>'_def by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
    (** Apply the linearity on \<sigma>. **)
    have h_lin_V: "f (\<Sum>v\<in>V. \<alpha>' v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha>' v *\<^sub>R f v)"
      using h_prop h_\<alpha>'_nn h_sum_\<alpha>'_eq1 by (by100 blast)
    show "f (\<Sum>v\<in>W. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>W. \<alpha> v *\<^sub>R f v)"
      using h_lin_V h_vsum_eq h_fsum_eq by (by100 simp)
  qed
  show ?thesis
    unfolding geotop_linear_on_def
    using h_sv_\<tau> h_prop_\<tau> by (by100 blast)
qed

(** Linearity on a simplex descends to any sub-simplex (subset that is itself a simplex).
    Unlike \<open>geotop_linear_on_face\<close> which requires face relation, this works for arbitrary
    simplex-subsets (e.g. sub-simplexes in a common refinement). Proof sketch (early.tex
    style): each vertex w of \<sigma>' lies in \<sigma>, so w = \<Sum> t_{w,v} v (bary coords over V_\<sigma>).
    For any \<alpha> over V_{\<sigma>'}, expand \<Sum> \<alpha>_w w = \<Sum>_v (\<Sum>_w \<alpha>_w t_{w,v}) v = \<Sum>_v \<beta>_v v.
    Apply linear_on \<sigma> f twice: once to get f(w) = \<Sum> t_{w,v} f(v), once to get
    f(\<Sum> \<beta>_v v) = \<Sum> \<beta>_v f(v). Conclude f(\<Sum> \<alpha>_w w) = \<Sum> \<alpha>_w f(w). **)
lemma geotop_linear_on_sub_simplex:
  fixes \<sigma> \<sigma>' :: "'a::euclidean_space set" and f :: "'a \<Rightarrow> 'b::real_vector"
  assumes h_lin: "geotop_linear_on \<sigma> f"
  assumes h_sim': "geotop_is_simplex \<sigma>'"
  assumes h_sub: "\<sigma>' \<subseteq> \<sigma>"
  shows "geotop_linear_on \<sigma>' f"
proof -
  (** (1) Extract V = vertices(\<sigma>) from linear_on. **)
  obtain V where h_sv: "geotop_simplex_vertices \<sigma> V"
             and h_prop: "\<forall>\<alpha>. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1 \<longrightarrow>
                              f (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
    using h_lin unfolding geotop_linear_on_def by (by100 blast)
  have h_sv_unf:
    "\<exists>m n. finite V \<and> card V = n + 1 \<and> n \<le> m \<and> geotop_general_position V m
          \<and> \<sigma> = geotop_convex_hull V"
    using h_sv unfolding geotop_simplex_vertices_def by (by100 simp)
  obtain m_\<sigma> n_\<sigma> where h_Vfin: "finite V" and h_Vcard: "card V = n_\<sigma> + 1"
                   and h_Vnm: "n_\<sigma> \<le> m_\<sigma>" and h_Vgp: "geotop_general_position V m_\<sigma>"
                   and h_\<sigma>hull: "\<sigma> = geotop_convex_hull V"
    using h_sv_unf by (by100 blast)
  have h_\<sigma>_HOL: "\<sigma> = convex hull V"
    using h_\<sigma>hull geotop_convex_hull_eq_HOL by (by100 simp)
  (** (2) Extract V' = vertices(\<sigma>'). **)
  obtain V' where h_sv': "geotop_simplex_vertices \<sigma>' V'"
    using h_sim' unfolding geotop_is_simplex_def geotop_simplex_vertices_def by (by100 blast)
  obtain m' n' where h_V'fin: "finite V'" and h_V'card: "card V' = n' + 1"
                 and h_V'nm: "n' \<le> m'" and h_V'gp: "geotop_general_position V' m'"
                 and h_\<sigma>'hull: "\<sigma>' = geotop_convex_hull V'"
    using h_sv' unfolding geotop_simplex_vertices_def by (by100 blast)
  have h_\<sigma>'_HOL: "\<sigma>' = convex hull V'"
    using h_\<sigma>'hull geotop_convex_hull_eq_HOL by (by100 simp)
  (** (3) Each v' \<in> V' is in \<sigma>' \<subseteq> \<sigma> = conv(V), so v' has bary coords in V. **)
  have h_V'_in_\<sigma>: "V' \<subseteq> \<sigma>"
  proof
    fix v' assume h_v'V': "v' \<in> V'"
    have h_v'_hull: "v' \<in> convex hull V'"
      by (rule subsetD[OF hull_subset h_v'V'])
    have h_v'_\<sigma>': "v' \<in> \<sigma>'" using h_v'_hull h_\<sigma>'_HOL by (by100 simp)
    show "v' \<in> \<sigma>" using h_v'_\<sigma>' h_sub by (by100 blast)
  qed
  have h_hull_char: "convex hull V =
                      {y. \<exists>u. (\<forall>x\<in>V. 0 \<le> u x) \<and> sum u V = 1 \<and> (\<Sum>x\<in>V. u x *\<^sub>R x) = y}"
    by (rule convex_hull_finite[OF h_Vfin])
  have h_bary_exists: "\<forall>v'\<in>V'. \<exists>t. (\<forall>v\<in>V. 0 \<le> t v) \<and> sum t V = 1 \<and>
                                      v' = (\<Sum>v\<in>V. t v *\<^sub>R v)"
  proof
    fix v' assume h_v'V': "v' \<in> V'"
    have h_v'_in_\<sigma>: "v' \<in> \<sigma>" using h_V'_in_\<sigma> h_v'V' by (by100 blast)
    have h_v'_in: "v' \<in> convex hull V"
      using h_v'_in_\<sigma> h_\<sigma>_HOL by (by100 simp)
    have h_v'_exp: "\<exists>u. (\<forall>x\<in>V. 0 \<le> u x) \<and> sum u V = 1 \<and> (\<Sum>x\<in>V. u x *\<^sub>R x) = v'"
      using h_v'_in h_hull_char by (by100 blast)
    then obtain u where h_u_nn: "\<forall>x\<in>V. 0 \<le> u x" and h_u_sum: "sum u V = 1"
                    and h_u_eq: "(\<Sum>x\<in>V. u x *\<^sub>R x) = v'"
      by (by100 blast)
    have h_v'_eq: "v' = (\<Sum>v\<in>V. u v *\<^sub>R v)" using h_u_eq by (by100 simp)
    show "\<exists>t. (\<forall>v\<in>V. 0 \<le> t v) \<and> sum t V = 1 \<and> v' = (\<Sum>v\<in>V. t v *\<^sub>R v)"
      using h_u_nn h_u_sum h_v'_eq by (by100 blast)
  qed
  (** (4) Use a SOME to fix bary coords per v'. **)
  define t :: "'a \<Rightarrow> 'a \<Rightarrow> real" where
    "t v' = (SOME s. (\<forall>v\<in>V. 0 \<le> s v) \<and> sum s V = 1 \<and> v' = (\<Sum>v\<in>V. s v *\<^sub>R v))" for v'
  have h_t_prop: "\<forall>v'\<in>V'. (\<forall>v\<in>V. 0 \<le> t v' v) \<and> sum (t v') V = 1 \<and>
                             v' = (\<Sum>v\<in>V. t v' v *\<^sub>R v)"
  proof
    fix v' assume h_v'V': "v' \<in> V'"
    have h_ex: "\<exists>s. (\<forall>v\<in>V. 0 \<le> s v) \<and> sum s V = 1 \<and> v' = (\<Sum>v\<in>V. s v *\<^sub>R v)"
      using h_bary_exists h_v'V' by (by100 blast)
    show "(\<forall>v\<in>V. 0 \<le> t v' v) \<and> sum (t v') V = 1 \<and> v' = (\<Sum>v\<in>V. t v' v *\<^sub>R v)"
      unfolding t_def using someI_ex[OF h_ex] by (by100 blast)
  qed
  (** (5) f(v') = Σ t[v',v] f(v) for each v' ∈ V' (by linear_on σ f). **)
  have h_f_v': "\<forall>v'\<in>V'. f v' = (\<Sum>v\<in>V. t v' v *\<^sub>R f v)"
  proof
    fix v' assume h_v'V': "v' \<in> V'"
    have h_t_nn: "\<forall>v\<in>V. 0 \<le> t v' v" using h_t_prop h_v'V' by (by100 blast)
    have h_t_sum: "sum (t v') V = 1" using h_t_prop h_v'V' by (by100 blast)
    have h_v'_decomp: "v' = (\<Sum>v\<in>V. t v' v *\<^sub>R v)" using h_t_prop h_v'V' by (by100 blast)
    have "f (\<Sum>v\<in>V. t v' v *\<^sub>R v) = (\<Sum>v\<in>V. t v' v *\<^sub>R f v)"
      using h_prop h_t_nn h_t_sum by (by100 blast)
    thus "f v' = (\<Sum>v\<in>V. t v' v *\<^sub>R f v)" using h_v'_decomp by (by100 simp)
  qed
  (** (6) Now prove linearity on \<sigma>'. **)
  have h_prop': "\<forall>\<alpha>. (\<forall>v'\<in>V'. 0 \<le> \<alpha> v') \<and> sum \<alpha> V' = 1 \<longrightarrow>
                     f (\<Sum>v'\<in>V'. \<alpha> v' *\<^sub>R v') = (\<Sum>v'\<in>V'. \<alpha> v' *\<^sub>R f v')"
  proof (intro allI impI)
    fix \<alpha> :: "'a \<Rightarrow> real"
    assume h\<alpha>: "(\<forall>v'\<in>V'. 0 \<le> \<alpha> v') \<and> sum \<alpha> V' = 1"
    (** Define \<beta> v = Σ_{v'} \<alpha> v' * t v' v (the combined bary coords over V). **)
    define \<beta> :: "'a \<Rightarrow> real" where "\<beta> v = (\<Sum>v'\<in>V'. \<alpha> v' * t v' v)" for v
    (** \<beta> is a valid bary over V. **)
    have h_\<beta>_nn: "\<forall>v\<in>V. 0 \<le> \<beta> v"
    proof
      fix v assume h_vV: "v \<in> V"
      have "\<forall>v'\<in>V'. 0 \<le> \<alpha> v' * t v' v"
      proof
        fix v' assume h_v'V': "v' \<in> V'"
        have h_\<alpha>_nn: "0 \<le> \<alpha> v'" using h\<alpha> h_v'V' by (by100 blast)
        have h_t_nn: "0 \<le> t v' v" using h_t_prop h_v'V' h_vV by (by100 blast)
        show "0 \<le> \<alpha> v' * t v' v" using h_\<alpha>_nn h_t_nn by (by100 simp)
      qed
      then have h_all: "\<And>v'. v' \<in> V' \<Longrightarrow> 0 \<le> \<alpha> v' * t v' v" by (by100 blast)
      show "0 \<le> \<beta> v" unfolding \<beta>_def by (rule sum_nonneg[OF h_all])
    qed
    have h_\<beta>_sum: "sum \<beta> V = 1"
    proof -
      have "sum \<beta> V = (\<Sum>v\<in>V. \<Sum>v'\<in>V'. \<alpha> v' * t v' v)"
        unfolding \<beta>_def by (by100 simp)
      also have "\<dots> = (\<Sum>v'\<in>V'. \<Sum>v\<in>V. \<alpha> v' * t v' v)"
        by (rule sum.swap)
      also have "\<dots> = (\<Sum>v'\<in>V'. \<alpha> v' * sum (t v') V)"
      proof (rule sum.cong)
        show "V' = V'" by (by100 simp)
      next
        fix v' assume "v' \<in> V'"
        show "(\<Sum>v\<in>V. \<alpha> v' * t v' v) = \<alpha> v' * sum (t v') V"
          by (rule sum_distrib_left[symmetric])
      qed
      also have "\<dots> = (\<Sum>v'\<in>V'. \<alpha> v')"
        using h_t_prop by (by100 simp)
      also have "\<dots> = 1" using h\<alpha> by (by100 simp)
      finally show ?thesis .
    qed
    (** Show: \<Sum>_{v'} \<alpha> v' v' = \<Sum>_v \<beta> v v (in vector sense). **)
    have h_vec_eq: "(\<Sum>v'\<in>V'. \<alpha> v' *\<^sub>R v') = (\<Sum>v\<in>V. \<beta> v *\<^sub>R v)"
    proof -
      have "(\<Sum>v'\<in>V'. \<alpha> v' *\<^sub>R v') = (\<Sum>v'\<in>V'. \<alpha> v' *\<^sub>R (\<Sum>v\<in>V. t v' v *\<^sub>R v))"
        using h_t_prop by (by100 simp)
      also have "\<dots> = (\<Sum>v'\<in>V'. \<Sum>v\<in>V. \<alpha> v' *\<^sub>R (t v' v *\<^sub>R v))"
      proof (rule sum.cong)
        show "V' = V'" by (by100 simp)
      next
        fix v' assume "v' \<in> V'"
        show "\<alpha> v' *\<^sub>R (\<Sum>v\<in>V. t v' v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v' *\<^sub>R (t v' v *\<^sub>R v))"
          by (rule scaleR_right.sum)
      qed
      also have "\<dots> = (\<Sum>v'\<in>V'. \<Sum>v\<in>V. (\<alpha> v' * t v' v) *\<^sub>R v)"
        by (by100 simp)
      also have "\<dots> = (\<Sum>v\<in>V. \<Sum>v'\<in>V'. (\<alpha> v' * t v' v) *\<^sub>R v)"
        by (rule sum.swap)
      also have "\<dots> = (\<Sum>v\<in>V. (\<Sum>v'\<in>V'. \<alpha> v' * t v' v) *\<^sub>R v)"
      proof (rule sum.cong)
        show "V = V" by (by100 simp)
      next
        fix v assume "v \<in> V"
        show "(\<Sum>v'\<in>V'. (\<alpha> v' * t v' v) *\<^sub>R v) = (\<Sum>v'\<in>V'. \<alpha> v' * t v' v) *\<^sub>R v"
          by (rule scaleR_left.sum[symmetric])
      qed
      also have "\<dots> = (\<Sum>v\<in>V. \<beta> v *\<^sub>R v)"
        unfolding \<beta>_def by (by100 simp)
      finally show ?thesis .
    qed
    (** Show: \<Sum>_v \<beta> v f(v) = \<Sum>_{v'} \<alpha> v' f(v'). **)
    have h_fvec_eq: "(\<Sum>v\<in>V. \<beta> v *\<^sub>R f v) = (\<Sum>v'\<in>V'. \<alpha> v' *\<^sub>R f v')"
    proof -
      have "(\<Sum>v\<in>V. \<beta> v *\<^sub>R f v) = (\<Sum>v\<in>V. (\<Sum>v'\<in>V'. \<alpha> v' * t v' v) *\<^sub>R f v)"
        unfolding \<beta>_def by (by100 simp)
      also have "\<dots> = (\<Sum>v\<in>V. \<Sum>v'\<in>V'. (\<alpha> v' * t v' v) *\<^sub>R f v)"
      proof (rule sum.cong)
        show "V = V" by (by100 simp)
      next
        fix v assume "v \<in> V"
        show "(\<Sum>v'\<in>V'. \<alpha> v' * t v' v) *\<^sub>R f v = (\<Sum>v'\<in>V'. (\<alpha> v' * t v' v) *\<^sub>R f v)"
          by (rule scaleR_left.sum)
      qed
      also have "\<dots> = (\<Sum>v'\<in>V'. \<Sum>v\<in>V. (\<alpha> v' * t v' v) *\<^sub>R f v)"
        by (rule sum.swap)
      also have "\<dots> = (\<Sum>v'\<in>V'. \<Sum>v\<in>V. \<alpha> v' *\<^sub>R (t v' v *\<^sub>R f v))"
        by (by100 simp)
      also have "\<dots> = (\<Sum>v'\<in>V'. \<alpha> v' *\<^sub>R (\<Sum>v\<in>V. t v' v *\<^sub>R f v))"
      proof (rule sum.cong)
        show "V' = V'" by (by100 simp)
      next
        fix v' assume "v' \<in> V'"
        show "(\<Sum>v\<in>V. \<alpha> v' *\<^sub>R (t v' v *\<^sub>R f v)) = \<alpha> v' *\<^sub>R (\<Sum>v\<in>V. t v' v *\<^sub>R f v)"
          by (rule scaleR_right.sum[symmetric])
      qed
      also have "\<dots> = (\<Sum>v'\<in>V'. \<alpha> v' *\<^sub>R f v')"
        using h_f_v' by (by100 simp)
      finally show ?thesis .
    qed
    (** Apply linear_on \<sigma> f to \<beta>. **)
    have h_f_\<beta>: "f (\<Sum>v\<in>V. \<beta> v *\<^sub>R v) = (\<Sum>v\<in>V. \<beta> v *\<^sub>R f v)"
      using h_prop h_\<beta>_nn h_\<beta>_sum by (by100 blast)
    show "f (\<Sum>v'\<in>V'. \<alpha> v' *\<^sub>R v') = (\<Sum>v'\<in>V'. \<alpha> v' *\<^sub>R f v')"
      using h_vec_eq h_fvec_eq h_f_\<beta> by (by100 simp)
  qed
  show ?thesis
    unfolding geotop_linear_on_def
    using h_sv' h_prop' by (by100 blast)
qed

(** Shared classical fact: an affine map that is a bijection on a finite AI set V
    preserves affine independence of the image. Used by is_simplex, preserves_face,
    and face_preimage. Proof deferred — classical linear-algebra result. **)
(** FAITHFULNESS NOTE (2026-04-19): The original statement had hypothesis
    \<open>inj_on f V\<close>, but this is INSUFFICIENT. Counterexample:
    V = {(0,0), (1,0), (0,1)} AI in \<real>\<twosuperior>, f(x,y) = 2x+3y is linear/bary-preserving,
    inj on V (three distinct values 0, 2, 3), but f V = {0, 2, 3} \<subset> \<real> is DEP
    (aff_dim = 1 < card - 1 = 2). Strengthened to \<open>inj_on f (convex hull V)\<close>
    which the actual callers (PLH f + σ = conv V, inj_on f σ) DO satisfy. **)
lemma geotop_bary_lin_inj_preserves_ai:
  fixes V :: "'a::euclidean_space set" and f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes hVfin: "finite V"
  assumes h_inj: "inj_on f (convex hull V)"
  assumes hV_ai: "\<not> affine_dependent V"
  assumes h_bary: "\<And>\<alpha>. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<Longrightarrow> sum \<alpha> V = 1 \<Longrightarrow>
                        f (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
  shows "\<not> affine_dependent (f ` V)"
proof (rule ccontr)
  assume h_abs: "\<not> \<not> affine_dependent (f ` V)"
  then have h_dep: "affine_dependent (f ` V)" by (by100 blast)
  (** (1) Pull back the dependence witness through f on V. Since f is inj on V,
      there's a nontrivial w: V \<to> \<real> with sum w V = 0, \<Sum>v. w v *\<^sub>R f v = 0,
      and some w v \<noteq> 0. **)
  have h_fVfin: "finite (f ` V)" using hVfin by (by100 simp)
  (** f is inj on V \<subseteq> conv V. **)
  have h_V_hull: "V \<subseteq> convex hull V" by (rule hull_subset)
  have h_inj_V: "inj_on f V" using h_inj h_V_hull inj_on_subset by (by100 blast)
  have h_witness: "\<exists>w::'a \<Rightarrow> real. (\<exists>v\<in>V. w v \<noteq> 0) \<and> sum w V = 0
                                  \<and> (\<Sum>v\<in>V. w v *\<^sub>R f v) = 0"
  proof -
    (** (A) Unfold affine_dependent_explicit on f V. **)
    have h_f_exp: "\<exists>T u. finite T \<and> T \<subseteq> f ` V \<and> sum u T = 0
                       \<and> (\<exists>y\<in>T. u y \<noteq> 0) \<and> (\<Sum>y\<in>T. u y *\<^sub>R y) = 0"
      using h_dep unfolding affine_dependent_explicit by (by100 blast)
    obtain T u where hTfin: "finite T" and hT_sub: "T \<subseteq> f ` V"
                 and hu_sum: "sum u T = 0"
                 and hu_nonzero: "\<exists>y\<in>T. u y \<noteq> 0"
                 and hu_vsum: "(\<Sum>y\<in>T. u y *\<^sub>R y) = 0"
      using h_f_exp by (by100 blast)
    (** (B) Define V_T = preimage of T in V, and w = u \<circ> f on V_T, 0 elsewhere. **)
    define V_T where "V_T = V \<inter> f -` T"
    have hV_T_sub: "V_T \<subseteq> V" unfolding V_T_def by (by100 blast)
    have h_fV_T_eq: "f ` V_T = T"
    proof
      show "f ` V_T \<subseteq> T" unfolding V_T_def by (by100 blast)
    next
      show "T \<subseteq> f ` V_T"
      proof
        fix y assume hyT: "y \<in> T"
        have hy_fV: "y \<in> f ` V" using hyT hT_sub by (by100 blast)
        obtain v where hvV: "v \<in> V" and hy_eq: "y = f v" using hy_fV by (by100 blast)
        have hvV_T: "v \<in> V_T" unfolding V_T_def using hvV hy_eq hyT by (by100 simp)
        show "y \<in> f ` V_T" using hvV_T hy_eq by (by100 blast)
      qed
    qed
    have h_inj_V_T: "inj_on f V_T" using h_inj_V hV_T_sub inj_on_subset by (by100 blast)
    define w where "w = (\<lambda>v::'a. if v \<in> V_T then u (f v) else 0)"
    (** (C) sum w V = sum_{v \<in> V_T} u(f v) = sum u T = 0. **)
    have h_sum_w: "sum w V = sum u T"
    proof -
      have hVfin': "finite V" using hVfin by (by100 simp)
      have h_split: "sum w V = sum w V_T + sum w (V - V_T)"
        using hV_T_sub hVfin' sum.subset_diff[of V_T V w] by (by100 simp)
      have h_w_on_diff: "sum w (V - V_T) = 0"
      proof -
        have "\<And>v. v \<in> V - V_T \<Longrightarrow> w v = 0" unfolding w_def by (by100 simp)
        thus ?thesis by (by100 simp)
      qed
      have h_w_on_V_T: "sum w V_T = sum u T"
      proof -
        have h1: "sum w V_T = sum (\<lambda>v. u (f v)) V_T"
        proof (rule sum.cong)
          show "V_T = V_T" by (by100 simp)
        next
          fix v assume "v \<in> V_T"
          thus "w v = u (f v)" unfolding w_def by (by100 simp)
        qed
        have h2: "sum (\<lambda>v. u (f v)) V_T = sum (u \<circ> f) V_T" by (by100 simp)
        have h3: "sum (u \<circ> f) V_T = sum u (f ` V_T)"
          by (rule sum.reindex[OF h_inj_V_T, symmetric])
        have h4: "sum u (f ` V_T) = sum u T" using h_fV_T_eq by (by100 simp)
        from h1 have s1: "sum w V_T = sum (\<lambda>v. u (f v)) V_T" .
        also from h2 have "\<dots> = sum (u \<circ> f) V_T" .
        also from h3 have "\<dots> = sum u (f ` V_T)" .
        also from h4 have "\<dots> = sum u T" .
        finally show ?thesis .
      qed
      show ?thesis using h_split h_w_on_diff h_w_on_V_T by (by100 simp)
    qed
    have h_sum_w_V: "sum w V = 0" using h_sum_w hu_sum by (by100 simp)
    (** (D) Similar for vector-sum. **)
    have h_vsum_w: "(\<Sum>v\<in>V. w v *\<^sub>R f v) = (\<Sum>y\<in>T. u y *\<^sub>R y)"
    proof -
      have hVfin': "finite V" using hVfin by (by100 simp)
      have h_split: "(\<Sum>v\<in>V. w v *\<^sub>R f v) = (\<Sum>v\<in>V_T. w v *\<^sub>R f v)
                                         + (\<Sum>v\<in>V - V_T. w v *\<^sub>R f v)"
        using hV_T_sub hVfin'
              sum.subset_diff[of V_T V "\<lambda>v. w v *\<^sub>R f v"] by (by100 simp)
      have h_diff_zero: "(\<Sum>v\<in>V - V_T. w v *\<^sub>R f v) = 0"
      proof -
        have h_w_zero: "\<forall>v\<in>V - V_T. w v = 0"
        proof
          fix v assume hv: "v \<in> V - V_T"
          show "w v = 0" unfolding w_def using hv by (by100 simp)
        qed
        have "(\<Sum>v\<in>V - V_T. w v *\<^sub>R f v) = (\<Sum>v\<in>V - V_T. 0 *\<^sub>R f v)"
          using h_w_zero by (by100 simp)
        also have "\<dots> = (\<Sum>v\<in>V - V_T. (0::'b))" by (by100 simp)
        also have "\<dots> = 0" by (by100 simp)
        finally show ?thesis .
      qed
      have h_V_T_part: "(\<Sum>v\<in>V_T. w v *\<^sub>R f v) = (\<Sum>y\<in>T. u y *\<^sub>R y)"
      proof -
        have h1: "(\<Sum>v\<in>V_T. w v *\<^sub>R f v) = (\<Sum>v\<in>V_T. u (f v) *\<^sub>R f v)"
        proof (rule sum.cong)
          show "V_T = V_T" by (by100 simp)
        next
          fix v assume "v \<in> V_T"
          thus "w v *\<^sub>R f v = u (f v) *\<^sub>R f v" unfolding w_def by (by100 simp)
        qed
        have h2: "(\<Sum>v\<in>V_T. u (f v) *\<^sub>R f v) = sum ((\<lambda>y. u y *\<^sub>R y) \<circ> f) V_T" by (by100 simp)
        have h3: "sum ((\<lambda>y. u y *\<^sub>R y) \<circ> f) V_T = sum (\<lambda>y. u y *\<^sub>R y) (f ` V_T)"
          by (rule sum.reindex[OF h_inj_V_T, symmetric])
        have h4: "sum (\<lambda>y. u y *\<^sub>R y) (f ` V_T) = sum (\<lambda>y. u y *\<^sub>R y) T"
          using h_fV_T_eq by (by100 simp)
        from h1 have s1: "(\<Sum>v\<in>V_T. w v *\<^sub>R f v) = (\<Sum>v\<in>V_T. u (f v) *\<^sub>R f v)" .
        also from h2 have "\<dots> = sum ((\<lambda>y. u y *\<^sub>R y) \<circ> f) V_T" .
        also from h3 have "\<dots> = sum (\<lambda>y. u y *\<^sub>R y) (f ` V_T)" .
        also from h4 have "\<dots> = (\<Sum>y\<in>T. u y *\<^sub>R y)" .
        finally show ?thesis .
      qed
      show ?thesis using h_split h_diff_zero h_V_T_part by (by100 simp)
    qed
    have h_vsum_w_V: "(\<Sum>v\<in>V. w v *\<^sub>R f v) = 0" using h_vsum_w hu_vsum by (by100 simp)
    (** (E) \<exists>v\<in>V. w v \<noteq> 0: pick y\<^sub>0 \<in> T with u y\<^sub>0 \<noteq> 0, preimage v\<^sub>0. **)
    obtain y0 where hy0T: "y0 \<in> T" and hu_y0: "u y0 \<noteq> 0" using hu_nonzero by (by100 blast)
    have hy0_in_fV_T: "y0 \<in> f ` V_T" using hy0T h_fV_T_eq by (by100 simp)
    obtain v0 where hv0V_T: "v0 \<in> V_T" and hfv0: "y0 = f v0"
      using hy0_in_fV_T by (by100 blast)
    have hv0V: "v0 \<in> V" using hv0V_T hV_T_sub by (by100 blast)
    have hw_v0: "w v0 = u y0" unfolding w_def using hv0V_T hfv0 by (by100 simp)
    have hw_v0_ne: "w v0 \<noteq> 0" using hw_v0 hu_y0 by (by100 simp)
    have h_exists_nz: "\<exists>v\<in>V. w v \<noteq> 0" using hv0V hw_v0_ne by (by100 blast)
    (** (F) Assemble. **)
    have "(\<exists>v\<in>V. w v \<noteq> 0) \<and> sum w V = 0 \<and> (\<Sum>v\<in>V. w v *\<^sub>R f v) = 0"
      using h_exists_nz h_sum_w_V h_vsum_w_V by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  then obtain w :: "'a \<Rightarrow> real"
    where h_nonzero: "\<exists>v\<in>V. w v \<noteq> 0"
      and h_sum0: "sum w V = 0"
      and h_vsum0: "(\<Sum>v\<in>V. w v *\<^sub>R f v) = 0"
    by (by100 blast)
  (** (2) Split \<open>w\<close> into positive and negative parts. **)
  define wp where "wp = (\<lambda>v. max 0 (w v))"
  define wn where "wn = (\<lambda>v. max 0 (- w v))"
  have h_wp_nn: "\<forall>v. 0 \<le> wp v" unfolding wp_def by (by100 simp)
  have h_wn_nn: "\<forall>v. 0 \<le> wn v" unfolding wn_def by (by100 simp)
  have h_w_split: "\<forall>v. w v = wp v - wn v"
    unfolding wp_def wn_def by (by100 auto)
  (** (3) Normalize to bary-coordinates. sum wp V = sum wn V = s > 0. **)
  define s where "s = sum wp V"
  have h_sums_eq: "sum wp V = sum wn V"
  proof -
    have h_sum_split: "sum w V = sum wp V - sum wn V"
    proof -
      have "sum w V = (\<Sum>v\<in>V. wp v - wn v)"
        using h_w_split by (by100 simp)
      also have "\<dots> = sum wp V - sum wn V"
        by (rule sum_subtractf)
      finally show ?thesis .
    qed
    show ?thesis using h_sum_split h_sum0 by (by100 simp)
  qed
  have h_s_pos: "0 < s"
  proof -
    have h_wp_nn_in: "\<forall>v\<in>V. 0 \<le> wp v" using h_wp_nn by (by100 blast)
    have h_wn_nn_in: "\<forall>v\<in>V. 0 \<le> wn v" using h_wn_nn by (by100 blast)
    have h_s_nn: "0 \<le> s" unfolding s_def
      using sum_nonneg[of V wp] h_wp_nn_in by (by100 blast)
    have h_not_zero: "s \<noteq> 0"
    proof
      assume h_s_eq0: "s = 0"
      have h_sum_wp: "sum wp V = 0" using h_s_eq0 unfolding s_def by (by100 simp)
      have h_sum_wn: "sum wn V = 0" using h_sums_eq h_sum_wp by (by100 simp)
      have h_wp_zero: "\<forall>v\<in>V. wp v = 0"
        using h_sum_wp h_wp_nn_in hVfin sum_nonneg_eq_0_iff by (by100 blast)
      have h_wn_zero: "\<forall>v\<in>V. wn v = 0"
        using h_sum_wn h_wn_nn_in hVfin sum_nonneg_eq_0_iff by (by100 blast)
      have h_all_zero: "\<forall>v\<in>V. w v = 0"
        using h_wp_zero h_wn_zero h_w_split by (by100 simp)
      show False using h_all_zero h_nonzero by (by100 blast)
    qed
    show ?thesis using h_s_nn h_not_zero by (by100 simp)
  qed
  define \<alpha>p where "\<alpha>p = (\<lambda>v. wp v / s)"
  define \<alpha>n where "\<alpha>n = (\<lambda>v. wn v / s)"
  have h_\<alpha>p_nn: "\<forall>v\<in>V. 0 \<le> \<alpha>p v" unfolding \<alpha>p_def using h_wp_nn h_s_pos by (by100 simp)
  have h_\<alpha>n_nn: "\<forall>v\<in>V. 0 \<le> \<alpha>n v" unfolding \<alpha>n_def using h_wn_nn h_s_pos by (by100 simp)
  have h_\<alpha>p_sum: "sum \<alpha>p V = 1"
  proof -
    have h1: "sum \<alpha>p V = sum wp V / s"
      unfolding \<alpha>p_def using sum_divide_distrib[symmetric, where f=wp and A=V and r=s]
      by (by100 simp)
    have h_s_eq: "sum wp V = s" unfolding s_def by (by100 simp)
    have h_s_ne: "s \<noteq> 0" using h_s_pos by (by100 simp)
    have h2: "sum wp V / s = 1" using h_s_eq h_s_ne by (by100 simp)
    show ?thesis using h1 h2 by (by100 simp)
  qed
  have h_\<alpha>n_sum: "sum \<alpha>n V = 1"
  proof -
    have h1: "sum \<alpha>n V = sum wn V / s"
      unfolding \<alpha>n_def using sum_divide_distrib[symmetric, where f=wn and A=V and r=s]
      by (by100 simp)
    have h_s_eq: "sum wn V = s" using h_sums_eq unfolding s_def by (by100 simp)
    have h_s_ne: "s \<noteq> 0" using h_s_pos by (by100 simp)
    have h2: "sum wn V / s = 1" using h_s_eq h_s_ne by (by100 simp)
    show ?thesis using h1 h2 by (by100 simp)
  qed
  (** (4) Apply bary-preservation at \<alpha>p and \<alpha>n; build a nonzero combination on V. **)
  define xp where "xp = (\<Sum>v\<in>V. \<alpha>p v *\<^sub>R v)"
  define xn where "xn = (\<Sum>v\<in>V. \<alpha>n v *\<^sub>R v)"
  have h_fxp: "f xp = (\<Sum>v\<in>V. \<alpha>p v *\<^sub>R f v)"
    unfolding xp_def using h_bary[OF h_\<alpha>p_nn h_\<alpha>p_sum] by (by100 simp)
  have h_fxn: "f xn = (\<Sum>v\<in>V. \<alpha>n v *\<^sub>R f v)"
    unfolding xn_def using h_bary[OF h_\<alpha>n_nn h_\<alpha>n_sum] by (by100 simp)
  (** \<open>f xp - f xn = (1/s) \<Sum> w v *\<^sub>R f v = 0\<close>. **)
  have h_fxp_eq_fxn: "f xp = f xn"
  proof -
    have h_diff: "f xp - f xn = (\<Sum>v\<in>V. (\<alpha>p v - \<alpha>n v) *\<^sub>R f v)"
    proof -
      have "f xp - f xn = (\<Sum>v\<in>V. \<alpha>p v *\<^sub>R f v) - (\<Sum>v\<in>V. \<alpha>n v *\<^sub>R f v)"
        using h_fxp h_fxn by (by100 simp)
      also have "\<dots> = (\<Sum>v\<in>V. \<alpha>p v *\<^sub>R f v - \<alpha>n v *\<^sub>R f v)"
        by (rule sum_subtractf[symmetric])
      also have "\<dots> = (\<Sum>v\<in>V. (\<alpha>p v - \<alpha>n v) *\<^sub>R f v)"
      proof (rule sum.cong)
        show "V = V" by (by100 simp)
      next
        fix v assume "v \<in> V"
        show "\<alpha>p v *\<^sub>R f v - \<alpha>n v *\<^sub>R f v = (\<alpha>p v - \<alpha>n v) *\<^sub>R f v"
          by (rule scaleR_left_diff_distrib[symmetric])
      qed
      finally show ?thesis .
    qed
    have h_sdiff: "\<And>v. \<alpha>p v - \<alpha>n v = w v / s"
    proof -
      fix v
      have "\<alpha>p v - \<alpha>n v = wp v / s - wn v / s" unfolding \<alpha>p_def \<alpha>n_def by (by100 simp)
      also have "\<dots> = (wp v - wn v) / s" by (rule diff_divide_distrib[symmetric])
      also have "\<dots> = w v / s" using h_w_split by (by100 simp)
      finally show "\<alpha>p v - \<alpha>n v = w v / s" .
    qed
    have h_vsum_w_scale: "(\<Sum>v\<in>V. (\<alpha>p v - \<alpha>n v) *\<^sub>R f v) = (1/s) *\<^sub>R (\<Sum>v\<in>V. w v *\<^sub>R f v)"
    proof -
      have "(\<Sum>v\<in>V. (\<alpha>p v - \<alpha>n v) *\<^sub>R f v) = (\<Sum>v\<in>V. (w v / s) *\<^sub>R f v)"
        using h_sdiff by (by100 simp)
      also have "\<dots> = (\<Sum>v\<in>V. (1/s) *\<^sub>R (w v *\<^sub>R f v))"
        by (by100 simp)
      also have "\<dots> = (1/s) *\<^sub>R (\<Sum>v\<in>V. w v *\<^sub>R f v)"
        by (rule scaleR_right.sum[symmetric])
      finally show ?thesis .
    qed
    have h_zero: "(1/s) *\<^sub>R (\<Sum>v\<in>V. w v *\<^sub>R f v) = 0"
      using h_vsum0 by (by100 simp)
    have "f xp - f xn = 0" using h_diff h_vsum_w_scale h_zero by (by100 simp)
    thus ?thesis by (by100 simp)
  qed
  (** xp = xn would give \<Sum>v. w v *\<^sub>R v = 0 with sum w V = 0 and some w v \<noteq> 0,
      contradicting V AI. So xp \<noteq> xn. **)
  have h_xp_ne_xn: "xp \<noteq> xn"
  proof
    assume h_eq: "xp = xn"
    have h_diff_v: "xp - xn = (\<Sum>v\<in>V. (\<alpha>p v - \<alpha>n v) *\<^sub>R v)"
    proof -
      have "xp - xn = (\<Sum>v\<in>V. \<alpha>p v *\<^sub>R v) - (\<Sum>v\<in>V. \<alpha>n v *\<^sub>R v)"
        unfolding xp_def xn_def by (by100 simp)
      also have "\<dots> = (\<Sum>v\<in>V. \<alpha>p v *\<^sub>R v - \<alpha>n v *\<^sub>R v)"
        by (rule sum_subtractf[symmetric])
      also have "\<dots> = (\<Sum>v\<in>V. (\<alpha>p v - \<alpha>n v) *\<^sub>R v)"
      proof (rule sum.cong)
        show "V = V" by (by100 simp)
      next
        fix v assume "v \<in> V"
        show "\<alpha>p v *\<^sub>R v - \<alpha>n v *\<^sub>R v = (\<alpha>p v - \<alpha>n v) *\<^sub>R v"
          by (rule scaleR_left_diff_distrib[symmetric])
      qed
      finally show ?thesis .
    qed
    have h_sdiff: "\<And>v. \<alpha>p v - \<alpha>n v = w v / s"
    proof -
      fix v
      have "\<alpha>p v - \<alpha>n v = wp v / s - wn v / s" unfolding \<alpha>p_def \<alpha>n_def by (by100 simp)
      also have "\<dots> = (wp v - wn v) / s" by (rule diff_divide_distrib[symmetric])
      also have "\<dots> = w v / s" using h_w_split by (by100 simp)
      finally show "\<alpha>p v - \<alpha>n v = w v / s" .
    qed
    have h_vsum_w_v_scale: "(\<Sum>v\<in>V. (\<alpha>p v - \<alpha>n v) *\<^sub>R v) = (1/s) *\<^sub>R (\<Sum>v\<in>V. w v *\<^sub>R v)"
    proof -
      have "(\<Sum>v\<in>V. (\<alpha>p v - \<alpha>n v) *\<^sub>R v) = (\<Sum>v\<in>V. (w v / s) *\<^sub>R v)"
        using h_sdiff by (by100 simp)
      also have "\<dots> = (\<Sum>v\<in>V. (1/s) *\<^sub>R (w v *\<^sub>R v))" by (by100 simp)
      also have "\<dots> = (1/s) *\<^sub>R (\<Sum>v\<in>V. w v *\<^sub>R v)"
        by (rule scaleR_right.sum[symmetric])
      finally show ?thesis .
    qed
    have h_diff_zero: "xp - xn = 0" using h_eq by (by100 simp)
    have h_scale_zero: "(1/s) *\<^sub>R (\<Sum>v\<in>V. w v *\<^sub>R v) = 0"
      using h_diff_zero h_diff_v h_vsum_w_v_scale by (by100 simp)
    have h_wsum_v_zero: "(\<Sum>v\<in>V. w v *\<^sub>R v) = 0"
      using h_scale_zero h_s_pos by (by100 simp)
    (** V is affine_dependent via affine_dependent_explicit witness (V, w). **)
    have h_V_dep: "affine_dependent V"
      unfolding affine_dependent_explicit
      using hVfin h_sum0 h_wsum_v_zero h_nonzero by (by100 blast)
    show False using h_V_dep hV_ai by (by100 blast)
  qed
  (** xp, xn \<in> conv V (bary combinations with nonneg weights summing to 1).
      f inj on conv V + f xp = f xn \<Longrightarrow> xp = xn, contradicting h_xp_ne_xn. **)
  have h_xp_hull: "xp \<in> convex hull V"
    unfolding xp_def convex_hull_finite[OF hVfin]
    using h_\<alpha>p_nn h_\<alpha>p_sum by (by100 blast)
  have h_xn_hull: "xn \<in> convex hull V"
    unfolding xn_def convex_hull_finite[OF hVfin]
    using h_\<alpha>n_nn h_\<alpha>n_sum by (by100 blast)
  have h_xp_eq_xn: "xp = xn"
    using inj_onD[OF h_inj h_fxp_eq_fxn h_xp_hull h_xn_hull] by (by100 simp)
  show False using h_xp_eq_xn h_xp_ne_xn by (by100 blast)
qed

(** Image of a simplex under a map that is linear on it and injective on it is a simplex. **)
lemma geotop_linear_inj_image_is_simplex:
  fixes \<sigma> :: "'a::euclidean_space set" and f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes h_lin: "geotop_linear_on \<sigma> f"
  assumes h_inj: "inj_on f \<sigma>"
  assumes h_sim: "geotop_is_simplex \<sigma>"
  shows "geotop_is_simplex (f ` \<sigma>)"
proof -
  (** (1) Extract V from linear_on: V is vertex set, bary-linearity holds. **)
  obtain V where h_sv: "geotop_simplex_vertices \<sigma> V"
             and h_prop: "\<forall>\<alpha>. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1 \<longrightarrow>
                              f (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
    using h_lin unfolding geotop_linear_on_def by (by100 blast)
  obtain m n where hVfin: "finite V" and hVcard: "card V = n + 1" and hnm: "n \<le> m"
               and hVgp: "geotop_general_position V m"
               and h\<sigma>hull: "\<sigma> = geotop_convex_hull V"
    using h_sv unfolding geotop_simplex_vertices_def by (by100 blast)
  have h\<sigma>_HOL: "\<sigma> = convex hull V"
    using h\<sigma>hull geotop_convex_hull_eq_HOL by (by100 simp)
  have hVai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF h_sv])
  (** (2) f \<sigma> = conv (f V) via bary expansion. **)
  have h_f_img_eq: "f ` \<sigma> = convex hull (f ` V)"
  proof (rule set_eqI, rule iffI)
    fix y assume "y \<in> f ` \<sigma>"
    then obtain x where hx\<sigma>: "x \<in> \<sigma>" and hy: "y = f x" by (by100 blast)
    have hx_hull: "x \<in> convex hull V" using hx\<sigma> h\<sigma>_HOL by (by100 simp)
    have h_hull_char: "convex hull V = {y. \<exists>u. (\<forall>v\<in>V. 0 \<le> u v) \<and> sum u V = 1
                                               \<and> (\<Sum>v\<in>V. u v *\<^sub>R v) = y}"
      by (rule convex_hull_finite[OF hVfin])
    have h_ex: "\<exists>u. (\<forall>v\<in>V. 0 \<le> u v) \<and> sum u V = 1 \<and> (\<Sum>v\<in>V. u v *\<^sub>R v) = x"
      using hx_hull h_hull_char by (by100 blast)
    obtain t where ht_nn: "\<forall>v\<in>V. 0 \<le> t v" and ht_sum: "sum t V = 1"
                 and hx_eq_raw: "(\<Sum>v\<in>V. t v *\<^sub>R v) = x"
      using h_ex by (by100 blast)
    have hx_eq: "x = (\<Sum>v\<in>V. t v *\<^sub>R v)" using hx_eq_raw by (by100 simp)
    have h_lin_at_t: "f (\<Sum>v\<in>V. t v *\<^sub>R v) = (\<Sum>v\<in>V. t v *\<^sub>R f v)"
      using h_prop ht_nn ht_sum by (by100 blast)
    have hy_eq: "y = (\<Sum>v\<in>V. t v *\<^sub>R f v)"
      using hy hx_eq h_lin_at_t by (by100 simp)
    have hfV_fin: "finite (f ` V)" using hVfin by (by100 simp)
    (** Translate t on V to t' on f V; we need inj for this. **)
    have hV_sub_\<sigma>: "V \<subseteq> \<sigma>"
      using h_sv h\<sigma>hull unfolding geotop_simplex_vertices_def geotop_convex_hull_def
      by (by100 blast)
    have h_inj_V: "inj_on f V" using h_inj hV_sub_\<sigma> inj_on_subset by (by100 blast)
    define t' :: "'b \<Rightarrow> real" where "t' w = t (inv_into V f w)" for w
    have h_t'_nn: "\<forall>w\<in>f`V. 0 \<le> t' w"
    proof
      fix w assume hw: "w \<in> f ` V"
      obtain v where hvV: "v \<in> V" and hwv: "w = f v" using hw by (by100 blast)
      have h_inv_raw: "inv_into V f (f v) = v"
        by (rule inv_into_f_f[OF h_inj_V hvV])
      have h_inv: "inv_into V f w = v"
        using h_inv_raw hwv by (by100 simp)
      show "0 \<le> t' w" unfolding t'_def using h_inv ht_nn hvV by (by100 simp)
    qed
    have h_t'_sum: "sum t' (f ` V) = 1"
    proof -
      have h_step1: "sum t' (f ` V) = (\<Sum>w\<in>f`V. t (inv_into V f w))"
        unfolding t'_def by (by100 simp)
      have h_reindex: "sum (t \<circ> inv_into V f) (f ` V) = sum ((t \<circ> inv_into V f) \<circ> f) V"
        by (rule sum.reindex[OF h_inj_V])
      have h_comp_id: "\<And>v. v \<in> V \<Longrightarrow> ((t \<circ> inv_into V f) \<circ> f) v = t v"
      proof -
        fix v assume hvV: "v \<in> V"
        have "inv_into V f (f v) = v" by (rule inv_into_f_f[OF h_inj_V hvV])
        thus "((t \<circ> inv_into V f) \<circ> f) v = t v" by (by100 simp)
      qed
      have h_sum_eq: "sum ((t \<circ> inv_into V f) \<circ> f) V = sum t V"
      proof (rule sum.cong)
        show "V = V" by (by100 simp)
      next
        fix v assume hvV: "v \<in> V"
        show "((t \<circ> inv_into V f) \<circ> f) v = t v" by (rule h_comp_id[OF hvV])
      qed
      have h_step2: "(\<Sum>w\<in>f`V. t (inv_into V f w)) = sum t V"
        using h_reindex h_sum_eq by (by100 simp)
      show ?thesis using h_step1 h_step2 ht_sum by (by100 simp)
    qed
    have h_vec_eq: "(\<Sum>w\<in>f`V. t' w *\<^sub>R w) = (\<Sum>v\<in>V. t v *\<^sub>R f v)"
    proof -
      have h_re: "sum (\<lambda>w. t' w *\<^sub>R w) (f ` V) = sum ((\<lambda>w. t' w *\<^sub>R w) \<circ> f) V"
        by (rule sum.reindex[OF h_inj_V])
      have h_expand: "\<And>v. v \<in> V \<Longrightarrow> ((\<lambda>w. t' w *\<^sub>R w) \<circ> f) v = t v *\<^sub>R f v"
      proof -
        fix v assume hvV: "v \<in> V"
        have "inv_into V f (f v) = v" by (rule inv_into_f_f[OF h_inj_V hvV])
        thus "((\<lambda>w. t' w *\<^sub>R w) \<circ> f) v = t v *\<^sub>R f v"
          unfolding t'_def by (by100 simp)
      qed
      have h_sum_after: "sum ((\<lambda>w. t' w *\<^sub>R w) \<circ> f) V = (\<Sum>v\<in>V. t v *\<^sub>R f v)"
      proof (rule sum.cong)
        show "V = V" by (by100 simp)
      next
        fix v assume hvV: "v \<in> V"
        show "((\<lambda>w. t' w *\<^sub>R w) \<circ> f) v = t v *\<^sub>R f v" by (rule h_expand[OF hvV])
      qed
      show ?thesis using h_re h_sum_after by (by100 simp)
    qed
    have hy_bary: "y = (\<Sum>w\<in>f`V. t' w *\<^sub>R w)"
      using hy_eq h_vec_eq by (by100 simp)
    show "y \<in> convex hull (f ` V)"
      unfolding convex_hull_finite[OF hfV_fin]
      using h_t'_nn h_t'_sum hy_bary by (by100 blast)
  next
    fix y assume hy_in: "y \<in> convex hull (f ` V)"
    have hfV_fin2: "finite (f ` V)" using hVfin by (by100 simp)
    have h_hull_char2: "convex hull (f ` V) =
                        {y. \<exists>u. (\<forall>x\<in>f`V. 0 \<le> u x) \<and> sum u (f ` V) = 1
                                 \<and> (\<Sum>x\<in>f`V. u x *\<^sub>R x) = y}"
      by (rule convex_hull_finite[OF hfV_fin2])
    have h_ex2: "\<exists>u. (\<forall>x\<in>f`V. 0 \<le> u x) \<and> sum u (f ` V) = 1
                     \<and> (\<Sum>x\<in>f`V. u x *\<^sub>R x) = y"
      using hy_in h_hull_char2 by (by100 blast)
    obtain u where hu_nn: "\<forall>w\<in>f`V. 0 \<le> u w" and hu_sum: "sum u (f ` V) = 1"
                 and hy_raw: "(\<Sum>w\<in>f`V. u w *\<^sub>R w) = y"
      using h_ex2 by (by100 blast)
    have hy: "y = (\<Sum>w\<in>f`V. u w *\<^sub>R w)" using hy_raw by (by100 simp)
    define t :: "'a \<Rightarrow> real" where "t v = u (f v)" for v
    have hV_sub_\<sigma>: "V \<subseteq> \<sigma>"
      using h_sv h\<sigma>hull unfolding geotop_simplex_vertices_def geotop_convex_hull_def
      by (by100 blast)
    have h_inj_V: "inj_on f V" using h_inj hV_sub_\<sigma> inj_on_subset by (by100 blast)
    have h_t_nn: "\<forall>v\<in>V. 0 \<le> t v" unfolding t_def using hu_nn by (by100 blast)
    have h_t_sum: "sum t V = 1"
    proof -
      have h1: "sum t V = sum (u \<circ> f) V" unfolding t_def by (by100 simp)
      have h_re: "sum u (f ` V) = sum (u \<circ> f) V" by (rule sum.reindex[OF h_inj_V])
      show ?thesis using h1 h_re hu_sum by (by100 simp)
    qed
    define x where "x = (\<Sum>v\<in>V. t v *\<^sub>R v)"
    have hx_in_hull: "x \<in> convex hull V"
    proof -
      have h_mem: "\<exists>a. (\<forall>v\<in>V. 0 \<le> a v) \<and> sum a V = 1 \<and> (\<Sum>v\<in>V. a v *\<^sub>R v) = x"
        unfolding x_def using h_t_nn h_t_sum by (by100 blast)
      show ?thesis unfolding convex_hull_finite[OF hVfin] using h_mem by (by100 blast)
    qed
    have hx_\<sigma>: "x \<in> \<sigma>" using hx_in_hull h\<sigma>_HOL by (by100 simp)
    have h_fx: "f x = (\<Sum>v\<in>V. t v *\<^sub>R f v)"
    proof -
      have h_apply: "f (\<Sum>v\<in>V. t v *\<^sub>R v) = (\<Sum>v\<in>V. t v *\<^sub>R f v)"
        using h_prop h_t_nn h_t_sum by (by100 blast)
      thus ?thesis unfolding x_def by (by100 simp)
    qed
    have h_vec_eq: "(\<Sum>v\<in>V. t v *\<^sub>R f v) = (\<Sum>w\<in>f`V. u w *\<^sub>R w)"
    proof -
      have "(\<Sum>v\<in>V. t v *\<^sub>R f v) = (\<Sum>v\<in>V. u (f v) *\<^sub>R f v)"
        unfolding t_def by (by100 simp)
      also have "\<dots> = sum ((\<lambda>w. u w *\<^sub>R w) \<circ> f) V" by (by100 simp)
      also have "\<dots> = (\<Sum>w\<in>f`V. u w *\<^sub>R w)"
      proof -
        have h_re: "sum (\<lambda>w. u w *\<^sub>R w) (f ` V) = sum ((\<lambda>w. u w *\<^sub>R w) \<circ> f) V"
          by (rule sum.reindex[OF h_inj_V])
        show ?thesis using h_re by (by100 simp)
      qed
      finally show ?thesis .
    qed
    have h_fx_y: "f x = y"
    proof -
      have "f x = (\<Sum>v\<in>V. t v *\<^sub>R f v)" using h_fx .
      also have "\<dots> = (\<Sum>w\<in>f`V. u w *\<^sub>R w)" using h_vec_eq .
      also have "\<dots> = y" using hy by (by100 simp)
      finally show ?thesis .
    qed
    then show "y \<in> f ` \<sigma>" using hx_\<sigma> by (by100 blast)
  qed
  (** (3) card (f V) = card V (inj on V \<subseteq> \<sigma>). **)
  have hV_sub_\<sigma>: "V \<subseteq> \<sigma>"
    using h_sv h\<sigma>hull unfolding geotop_simplex_vertices_def geotop_convex_hull_def
    by (by100 blast)
  have h_inj_V: "inj_on f V" using h_inj hV_sub_\<sigma> inj_on_subset by (by100 blast)
  have h_fV_card: "card (f ` V) = card V" by (rule card_image[OF h_inj_V])
  have h_fV_fin: "finite (f ` V)" using hVfin by (by100 simp)
  have h_fV_card_eq: "card (f ` V) = n + 1" using h_fV_card hVcard by (by100 simp)
  (** (4) f V is AI via the shared preserves_ai helper. **)
  have h_bary_V: "\<And>\<alpha>. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<Longrightarrow> sum \<alpha> V = 1 \<Longrightarrow>
                        f (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
    using h_prop by (by100 blast)
  have h_inj_hullV: "inj_on f (convex hull V)"
    using h_inj h\<sigma>_HOL by (by100 simp)
  have h_fV_ai: "\<not> affine_dependent (f ` V)"
    by (rule geotop_bary_lin_inj_preserves_ai[OF hVfin h_inj_hullV hVai h_bary_V])
  (** (5) AI + card → general_position. **)
  have h_fV_gp: "geotop_general_position (f ` V) n"
    by (rule geotop_ai_imp_general_position[OF h_fV_fin h_fV_card_eq h_fV_ai])
  (** (6) Assemble simplex definition. **)
  have h_fV_hull_HOL: "geotop_convex_hull (f ` V) = convex hull (f ` V)"
    by (rule geotop_convex_hull_eq_HOL)
  have h_fV_hull: "f ` \<sigma> = geotop_convex_hull (f ` V)"
    using h_f_img_eq h_fV_hull_HOL by (by100 simp)
  show "geotop_is_simplex (f ` \<sigma>)"
    unfolding geotop_is_simplex_def
    using h_fV_fin h_fV_card_eq h_fV_gp h_fV_hull by (by100 blast)
qed

(** Image of a face under a linear+injective map is a face of the image. **)
lemma geotop_linear_inj_image_preserves_face:
  fixes \<sigma> \<tau> :: "'a::euclidean_space set" and f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes h_lin: "geotop_linear_on \<sigma> f"
  assumes h_inj: "inj_on f \<sigma>"
  assumes h_face: "geotop_is_face \<tau> \<sigma>"
  shows "geotop_is_face (f ` \<tau>) (f ` \<sigma>)"
proof -
  (** (1) Extract V and bary-linearity from h_lin. **)
  obtain V where hVsv: "geotop_simplex_vertices \<sigma> V"
             and h_prop: "\<forall>\<alpha>. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1 \<longrightarrow>
                              f (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
    using h_lin unfolding geotop_linear_on_def by (by100 blast)
  obtain m n where hVfin: "finite V" and hVcard: "card V = n + 1" and hnm: "n \<le> m"
               and hVgp: "geotop_general_position V m"
               and h\<sigma>hull: "\<sigma> = geotop_convex_hull V"
    using hVsv unfolding geotop_simplex_vertices_def by (by100 blast)
  (** (2) Extract W from h_face. Uniqueness of simplex_vertices forces the V. **)
  obtain V' W where hV'sv: "geotop_simplex_vertices \<sigma> V'"
                and hWne: "W \<noteq> {}" and hWV': "W \<subseteq> V'"
                and h\<tau>_eq_raw: "\<tau> = geotop_convex_hull W"
    using h_face unfolding geotop_is_face_def by (by100 blast)
  have hVV': "V = V'" by (rule geotop_simplex_vertices_unique[OF hVsv hV'sv])
  have hWV: "W \<subseteq> V" using hWV' hVV' by (by100 simp)
  have h\<tau>_HOL: "\<tau> = convex hull W"
    using h\<tau>_eq_raw geotop_convex_hull_eq_HOL by (by100 simp)
  (** (3) V \<subseteq> \<sigma> and inj on V. **)
  have hV_sub_\<sigma>: "V \<subseteq> \<sigma>"
    using hVsv h\<sigma>hull unfolding geotop_simplex_vertices_def geotop_convex_hull_def
    by (by100 blast)
  have h_inj_V: "inj_on f V" using h_inj hV_sub_\<sigma> inj_on_subset by (by100 blast)
  have h_inj_W: "inj_on f W" using h_inj_V hWV inj_on_subset by (by100 blast)
  (** (4) \<sigma> = conv V (HOL). **)
  have h\<sigma>_HOL: "\<sigma> = convex hull V"
    using h\<sigma>hull geotop_convex_hull_eq_HOL by (by100 simp)
  (** (5) Apply hull_eq at V: f(\<sigma>) = conv(f V). **)
  have h_bary_V: "\<And>\<alpha>. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<Longrightarrow> sum \<alpha> V = 1 \<Longrightarrow>
                        f (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
    using h_prop by (by100 blast)
  have h_fV_hull_eq: "f ` (convex hull V) = convex hull (f ` V)"
    by (rule geotop_bary_lin_inj_image_hull_eq[OF hVfin h_inj_V h_bary_V])
  have h_f\<sigma>_HOL: "f ` \<sigma> = convex hull (f ` V)"
    using h_fV_hull_eq h\<sigma>_HOL by (by100 simp)
  (** (6) Apply hull_eq at W: f(\<tau>) = conv(f W). **)
  have hWfin: "finite W" using hWV hVfin finite_subset by (by100 blast)
  (** bary on W via geotop_linear_on_face + simplex_vertices uniqueness for \<tau>. **)
  have h_lin_\<tau>: "geotop_linear_on \<tau> f"
    by (rule geotop_linear_on_face[OF h_lin h_face])
  obtain Vt where hVt_sv: "geotop_simplex_vertices \<tau> Vt"
              and h_bary_Vt: "\<forall>\<alpha>. (\<forall>v\<in>Vt. 0 \<le> \<alpha> v) \<and> sum \<alpha> Vt = 1 \<longrightarrow>
                                  f (\<Sum>v\<in>Vt. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>Vt. \<alpha> v *\<^sub>R f v)"
    using h_lin_\<tau> unfolding geotop_linear_on_def by (by100 blast)
  (** W is also simplex_vertices of \<tau>: W \<subseteq> V(\<sigma>) ai, \<tau> = conv W, |W| = some k+1. **)
  have hW_ai: "\<not> affine_dependent W"
  proof -
    have hV_ai: "\<not> affine_dependent V"
      by (rule geotop_general_position_imp_aff_indep[OF hVsv])
    show ?thesis using hV_ai hWV affine_dependent_subset by (by100 blast)
  qed
  have hW_pos: "0 < card W" using hWne hWfin card_gt_0_iff by (by100 blast)
  have hW_card: "card W = (card W - 1) + 1" using hW_pos by (by100 simp)
  have hW_gp_W: "geotop_general_position W (card W - 1)"
    by (rule geotop_ai_imp_general_position[OF hWfin hW_card hW_ai])
  have hWsv: "geotop_simplex_vertices \<tau> W"
    unfolding geotop_simplex_vertices_def
    using hWfin hW_card hW_gp_W h\<tau>_eq_raw
    by (by100 blast)
  have hWVt: "W = Vt" by (rule geotop_simplex_vertices_unique[OF hWsv hVt_sv])
  have h_bary_W: "\<And>\<alpha>. (\<forall>v\<in>W. 0 \<le> \<alpha> v) \<Longrightarrow> sum \<alpha> W = 1 \<Longrightarrow>
                        f (\<Sum>v\<in>W. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>W. \<alpha> v *\<^sub>R f v)"
    using h_bary_Vt hWVt by (by100 simp)
  have h_fW_hull_eq: "f ` (convex hull W) = convex hull (f ` W)"
    by (rule geotop_bary_lin_inj_image_hull_eq[OF hWfin h_inj_W h_bary_W])
  have h_f\<tau>_HOL: "f ` \<tau> = convex hull (f ` W)"
    using h_fW_hull_eq h\<tau>_HOL by (by100 simp)
  have h_f\<tau>_geo: "f ` \<tau> = geotop_convex_hull (f ` W)"
    using h_f\<tau>_HOL geotop_convex_hull_eq_HOL[of "f ` W", symmetric] by (by100 simp)
  (** (7) f V is the simplex_vertices of f \<sigma>. **)
  have h_fV_fin: "finite (f ` V)" using hVfin by (by100 simp)
  have h_fV_card: "card (f ` V) = n + 1"
    using card_image[OF h_inj_V] hVcard by (by100 simp)
  have hVai_here: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF hVsv])
  have h_inj_hullV: "inj_on f (convex hull V)"
    using h_inj h\<sigma>_HOL by (by100 simp)
  have h_fV_ai: "\<not> affine_dependent (f ` V)"
    by (rule geotop_bary_lin_inj_preserves_ai[OF hVfin h_inj_hullV hVai_here h_bary_V])
  have h_fV_gp: "geotop_general_position (f ` V) n"
    by (rule geotop_ai_imp_general_position[OF h_fV_fin h_fV_card h_fV_ai])
  have h_f\<sigma>_geo: "f ` \<sigma> = geotop_convex_hull (f ` V)"
    using h_f\<sigma>_HOL geotop_convex_hull_eq_HOL[of "f ` V", symmetric] by (by100 simp)
  have h_fVsv: "geotop_simplex_vertices (f ` \<sigma>) (f ` V)"
    unfolding geotop_simplex_vertices_def
    using h_fV_fin h_fV_card hnm h_fV_gp h_f\<sigma>_geo by (by100 blast)
  (** (8) f W \<subseteq> f V, f W \<noteq> {}. **)
  have h_fW_sub: "f ` W \<subseteq> f ` V" using hWV by (by100 blast)
  have h_fW_ne: "f ` W \<noteq> {}" using hWne by (by100 blast)
  (** (9) Assemble. **)
  have h_witness: "geotop_simplex_vertices (f ` \<sigma>) (f ` V) \<and> f ` W \<noteq> {}
                   \<and> f ` W \<subseteq> f ` V \<and> f ` \<tau> = geotop_convex_hull (f ` W)"
    using h_fVsv h_fW_ne h_fW_sub h_f\<tau>_geo by (by100 simp)
  have h_ex_W: "\<exists>W0. geotop_simplex_vertices (f ` \<sigma>) (f ` V) \<and> W0 \<noteq> {}
                      \<and> W0 \<subseteq> (f ` V) \<and> f ` \<tau> = geotop_convex_hull W0"
    using h_witness by (rule exI[where x="f ` W"])
  then have h_ex: "\<exists>V0 W0. geotop_simplex_vertices (f ` \<sigma>) V0 \<and> W0 \<noteq> {}
                            \<and> W0 \<subseteq> V0 \<and> f ` \<tau> = geotop_convex_hull W0"
    by (rule exI[where x="f ` V"])
  then show "geotop_is_face (f ` \<tau>) (f ` \<sigma>)"
    unfolding geotop_is_face_def by (by100 simp)
qed

(** Every face of f(\<sigma>) (for \<sigma> a simplex, f linear+inj on \<sigma>) arises as f(face of \<sigma>). **)
lemma geotop_linear_inj_image_face_preimage:
  fixes \<sigma> :: "'a::euclidean_space set"
    and \<tau> :: "'b::euclidean_space set"
    and f :: "'a \<Rightarrow> 'b"
  assumes h_lin: "geotop_linear_on \<sigma> f"
  assumes h_inj: "inj_on f \<sigma>"
  assumes h_sim: "geotop_is_simplex \<sigma>"
  assumes h_face: "geotop_is_face \<tau> (f ` \<sigma>)"
  shows "\<exists>\<tau>_pre. geotop_is_face \<tau>_pre \<sigma> \<and> \<tau> = f ` \<tau>_pre"
proof -
  (** (1) Extract V and bary-linearity from h_lin. **)
  obtain V where hVsv: "geotop_simplex_vertices \<sigma> V"
             and h_prop: "\<forall>\<alpha>. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<and> sum \<alpha> V = 1 \<longrightarrow>
                              f (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
    using h_lin unfolding geotop_linear_on_def by (by100 blast)
  obtain m n where hVfin: "finite V" and hVcard: "card V = n + 1" and hnm: "n \<le> m"
               and hVgp: "geotop_general_position V m"
               and h\<sigma>hull: "\<sigma> = geotop_convex_hull V"
    using hVsv unfolding geotop_simplex_vertices_def by (by100 blast)
  have hV_sub_\<sigma>: "V \<subseteq> \<sigma>"
    using hVsv h\<sigma>hull unfolding geotop_simplex_vertices_def geotop_convex_hull_def
    by (by100 blast)
  have h_inj_V: "inj_on f V" using h_inj hV_sub_\<sigma> inj_on_subset by (by100 blast)
  (** (2) Extract V0 W0 from h_face (\<tau> is face of f\<sigma>). **)
  obtain V0 W0 where hV0sv: "geotop_simplex_vertices (f ` \<sigma>) V0"
                 and hW0ne: "W0 \<noteq> {}" and hW0V0: "W0 \<subseteq> V0"
                 and h\<tau>_eq_raw: "\<tau> = geotop_convex_hull W0"
    using h_face unfolding geotop_is_face_def by (by100 blast)
  (** (3) We need f ` V as simplex_vertices of f\<sigma>. Same AI sorry as preserves_face. **)
  have h\<sigma>_HOL: "\<sigma> = convex hull V"
    using h\<sigma>hull geotop_convex_hull_eq_HOL by (by100 simp)
  have h_bary_V: "\<And>\<alpha>. (\<forall>v\<in>V. 0 \<le> \<alpha> v) \<Longrightarrow> sum \<alpha> V = 1 \<Longrightarrow>
                        f (\<Sum>v\<in>V. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V. \<alpha> v *\<^sub>R f v)"
    using h_prop by (by100 blast)
  have h_fV_hull_eq: "f ` (convex hull V) = convex hull (f ` V)"
    by (rule geotop_bary_lin_inj_image_hull_eq[OF hVfin h_inj_V h_bary_V])
  have h_f\<sigma>_HOL: "f ` \<sigma> = convex hull (f ` V)"
    using h_fV_hull_eq h\<sigma>_HOL by (by100 simp)
  have h_fV_fin: "finite (f ` V)" using hVfin by (by100 simp)
  have h_fV_card: "card (f ` V) = n + 1"
    using card_image[OF h_inj_V] hVcard by (by100 simp)
  have hVai_here: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF hVsv])
  have h_inj_hullV: "inj_on f (convex hull V)"
    using h_inj h\<sigma>_HOL by (by100 simp)
  have h_fV_ai: "\<not> affine_dependent (f ` V)"
    by (rule geotop_bary_lin_inj_preserves_ai[OF hVfin h_inj_hullV hVai_here h_bary_V])
  have h_fV_gp: "geotop_general_position (f ` V) n"
    by (rule geotop_ai_imp_general_position[OF h_fV_fin h_fV_card h_fV_ai])
  have h_f\<sigma>_geo: "f ` \<sigma> = geotop_convex_hull (f ` V)"
    using h_f\<sigma>_HOL geotop_convex_hull_eq_HOL[of "f ` V", symmetric] by (by100 simp)
  have h_fVsv: "geotop_simplex_vertices (f ` \<sigma>) (f ` V)"
    unfolding geotop_simplex_vertices_def
    using h_fV_fin h_fV_card hnm h_fV_gp h_f\<sigma>_geo by (by100 blast)
  (** (4) By uniqueness V0 = f ` V. Hence W0 \<subseteq> f ` V. **)
  have hV0eq: "V0 = f ` V" by (rule geotop_simplex_vertices_unique[OF hV0sv h_fVsv])
  have hW0fV: "W0 \<subseteq> f ` V" using hW0V0 hV0eq by (by100 simp)
  (** (5) Lift W0 back to W_pre = inv_into V f ` W0 \<subseteq> V. **)
  define W_pre where "W_pre = inv_into V f ` W0"
  have hW_pre_V: "W_pre \<subseteq> V"
  proof
    fix v assume hv: "v \<in> W_pre"
    then obtain w where hwW0: "w \<in> W0" and hv_eq: "v = inv_into V f w"
      unfolding W_pre_def by (by100 blast)
    have "w \<in> f ` V" using hwW0 hW0fV by (by100 blast)
    then have "inv_into V f w \<in> V" by (rule inv_into_into)
    thus "v \<in> V" using hv_eq by (by100 simp)
  qed
  have hW_pre_ne: "W_pre \<noteq> {}" unfolding W_pre_def using hW0ne by (by100 blast)
  have hW_pre_fin: "finite W_pre" using hW_pre_V hVfin finite_subset by (by100 blast)
  (** (6) f ` W_pre = W0. **)
  have h_fW_pre: "f ` W_pre = W0"
  proof -
    have h_pointwise: "\<And>w. w \<in> W0 \<Longrightarrow> f (inv_into V f w) = w"
    proof -
      fix w assume hw: "w \<in> W0"
      have "w \<in> f ` V" using hw hW0fV by (by100 blast)
      thus "f (inv_into V f w) = w" by (rule f_inv_into_f)
    qed
    have "f ` W_pre = (\<lambda>w. f (inv_into V f w)) ` W0"
      unfolding W_pre_def image_image by (by100 simp)
    also have "\<dots> = (\<lambda>w. w) ` W0" using h_pointwise by (by100 simp)
    also have "\<dots> = W0" by (by100 simp)
    finally show ?thesis .
  qed
  (** (7) Build \<tau>_pre = conv W_pre; show it is a face of \<sigma>. **)
  define \<tau>_pre where "\<tau>_pre = geotop_convex_hull W_pre"
  have h\<tau>_pre_face: "geotop_is_face \<tau>_pre \<sigma>"
  proof -
    have hwit: "geotop_simplex_vertices \<sigma> V \<and> W_pre \<noteq> {} \<and> W_pre \<subseteq> V
                 \<and> \<tau>_pre = geotop_convex_hull W_pre"
      unfolding \<tau>_pre_def using hVsv hW_pre_ne hW_pre_V by (by100 simp)
    then have h_ex1: "\<exists>W1. geotop_simplex_vertices \<sigma> V \<and> W1 \<noteq> {}
                            \<and> W1 \<subseteq> V \<and> \<tau>_pre = geotop_convex_hull W1"
      by (rule exI[where x=W_pre])
    then have h_ex2: "\<exists>V1 W1. geotop_simplex_vertices \<sigma> V1 \<and> W1 \<noteq> {}
                               \<and> W1 \<subseteq> V1 \<and> \<tau>_pre = geotop_convex_hull W1"
      by (rule exI[where x=V])
    then show ?thesis unfolding geotop_is_face_def by (by100 simp)
  qed
  (** (8) f ` \<tau>_pre = \<tau>. **)
  have h_inj_W_pre: "inj_on f W_pre" using h_inj_V hW_pre_V inj_on_subset by (by100 blast)
  have h_lin_\<tau>_pre: "geotop_linear_on \<tau>_pre f"
    by (rule geotop_linear_on_face[OF h_lin h\<tau>_pre_face])
  obtain Vt_pre where hVtp_sv: "geotop_simplex_vertices \<tau>_pre Vt_pre"
                  and h_bary_Vtp: "\<forall>\<alpha>. (\<forall>v\<in>Vt_pre. 0 \<le> \<alpha> v) \<and> sum \<alpha> Vt_pre = 1 \<longrightarrow>
                                       f (\<Sum>v\<in>Vt_pre. \<alpha> v *\<^sub>R v)
                                         = (\<Sum>v\<in>Vt_pre. \<alpha> v *\<^sub>R f v)"
    using h_lin_\<tau>_pre unfolding geotop_linear_on_def by (by100 blast)
  have hW_pre_ai: "\<not> affine_dependent W_pre"
  proof -
    have hV_ai: "\<not> affine_dependent V"
      by (rule geotop_general_position_imp_aff_indep[OF hVsv])
    show ?thesis using hV_ai hW_pre_V affine_dependent_subset by (by100 blast)
  qed
  have hW_pre_pos: "0 < card W_pre" using hW_pre_ne hW_pre_fin card_gt_0_iff by (by100 blast)
  have hW_pre_card: "card W_pre = (card W_pre - 1) + 1" using hW_pre_pos by (by100 simp)
  have hW_pre_gp_W: "geotop_general_position W_pre (card W_pre - 1)"
    by (rule geotop_ai_imp_general_position[OF hW_pre_fin hW_pre_card hW_pre_ai])
  have hW_pre_sv: "geotop_simplex_vertices \<tau>_pre W_pre"
    unfolding geotop_simplex_vertices_def \<tau>_pre_def
    using hW_pre_fin hW_pre_card hW_pre_gp_W by (by100 blast)
  have hW_pre_Vtp: "W_pre = Vt_pre"
    by (rule geotop_simplex_vertices_unique[OF hW_pre_sv hVtp_sv])
  have h_bary_W_pre: "\<And>\<alpha>. (\<forall>v\<in>W_pre. 0 \<le> \<alpha> v) \<Longrightarrow> sum \<alpha> W_pre = 1 \<Longrightarrow>
                           f (\<Sum>v\<in>W_pre. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>W_pre. \<alpha> v *\<^sub>R f v)"
    using h_bary_Vtp hW_pre_Vtp by (by100 simp)
  have h_fW_pre_hull_eq: "f ` (convex hull W_pre) = convex hull (f ` W_pre)"
    by (rule geotop_bary_lin_inj_image_hull_eq[OF hW_pre_fin h_inj_W_pre h_bary_W_pre])
  have h_\<tau>_HOL: "\<tau> = convex hull W0"
    using h\<tau>_eq_raw geotop_convex_hull_eq_HOL by (by100 simp)
  have h_\<tau>_pre_HOL: "\<tau>_pre = convex hull W_pre"
    unfolding \<tau>_pre_def by (rule geotop_convex_hull_eq_HOL)
  have h_f\<tau>_pre: "f ` \<tau>_pre = \<tau>"
  proof -
    have "f ` \<tau>_pre = f ` (convex hull W_pre)" using h_\<tau>_pre_HOL by (by100 simp)
    also have "\<dots> = convex hull (f ` W_pre)" using h_fW_pre_hull_eq .
    also have "\<dots> = convex hull W0" using h_fW_pre by (by100 simp)
    also have "\<dots> = \<tau>" using h_\<tau>_HOL by (by100 simp)
    finally show ?thesis .
  qed
  (** (9) Assemble. **)
  have "geotop_is_face \<tau>_pre \<sigma> \<and> \<tau> = f ` \<tau>_pre"
    using h\<tau>_pre_face h_f\<tau>_pre by (by100 simp)
  then show ?thesis by (rule exI[where x=\<tau>_pre])
qed

subsection \<open>Diameter and mesh\<close>

(** from \<S>4: diameter and mesh (geotop.tex:953)
    LATEX VERSION: In a metric space [X,d], the diameter \<delta>M of M is the least upper bound of
      d(P,Q) (P,Q \<in> M). If G is a collection of subsets, the mesh of G is the least upper
      bound of \<delta>g (g \<in> G). Moved here from \<S>4 because the mesh-shrinkage lemma for
      iterated barycentric subdivision (needed in Theorem_GT_1) references \<open>geotop_mesh\<close>. **)
definition geotop_diameter :: "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> real" where
  "geotop_diameter d M = (if M = {} then 0 else (SUP P\<in>M. SUP Q\<in>M. d P Q))"

definition geotop_mesh :: "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set set \<Rightarrow> real" where
  "geotop_mesh d G = (if G = {} then 0 else (SUP g\<in>G. geotop_diameter d g))"

subsection \<open>Barycentric subdivision infrastructure (from early.tex \<S>4)\<close>

text \<open>The proof of Theorem 1 goes via iterated barycentric subdivision, as
developed in early.tex \<S>4. We define the barycenter of a simplex, the
barycentric subdivision \<open>Sd(K)\<close> of a complex, and its iterates; we state
the key lemmas (Sd is a subdivision, mesh tends to 0, sufficient iteration
refines any given subdivision). Full proofs of the listed lemmas follow
early.tex and are deferred to dedicated sub-proofs.\<close>

(** from Problem Set 5 / \<S>5: barycenter of a simplex (geotop.tex:1197,
    early.tex Def 4.1). The barycenter of \<sigma> = [v_0, \<dots>, v_n] is
    \<open>(1/(n+1)) \<cdot> \<Sum> v_i\<close>, equivalently the unique point with all barycentric
    coordinates equal to 1/(n+1). **)
definition geotop_barycenter :: "'a::real_vector set \<Rightarrow> 'a" where
  "geotop_barycenter \<sigma> = (SOME v. \<exists>V. geotop_simplex_vertices \<sigma> V \<and>
     v = (\<Sum>w\<in>V. (1 / real (card V)) *\<^sub>R w))"

(** from Problem Set 5 / \<S>5: barycentric subdivision of a complex
    (geotop.tex:1197, early.tex Def 4.4). \<open>Sd(K)\<close> is the subdivision of
    \<open>K\<close> whose simplexes are the convex hulls of barycenters of flags
    \<open>\<sigma>_0 < \<sigma>_1 < \<dots> < \<sigma>_n\<close> of faces of simplexes of \<open>K\<close>. We specify it
    existentially via \<open>SOME\<close>; concrete construction is deferred.

    CRITICAL: the spec MUST pin down the mesh-shrinkage property (early.tex
    Lemma 4.11): if \<open>K\<close> has dimension \<open>\<le>n\<close>, then \<open>mesh(Sd K) \<le> (n/(n+1)) \<cdot> mesh K\<close>,
    AND \<open>Sd(K)\<close> preserves the dimension bound. Otherwise the SOME could pick
    \<open>K\<close> itself (K is a subdivision of itself preserving 0-simplexes), making
    \<open>geotop_mesh_iterated_Sd_tends_to_zero\<close> FALSE. The spec is packaged as a
    separate predicate to keep its unfolding localized. **)
definition geotop_is_barycentric_Sd ::
  "'a::real_normed_vector set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "geotop_is_barycentric_Sd bK K \<longleftrightarrow>
      geotop_is_subdivision bK K
    \<and> (\<forall>\<sigma>. geotop_simplex_dim \<sigma> 0 \<and> \<sigma> \<in> K \<longrightarrow> \<sigma> \<in> bK)
    \<and> (\<forall>n::nat.
          (\<forall>\<sigma>\<in>K. \<forall>k. geotop_simplex_dim \<sigma> k \<longrightarrow> k \<le> n) \<longrightarrow>
          (\<forall>\<sigma>'\<in>bK. \<forall>k. geotop_simplex_dim \<sigma>' k \<longrightarrow> k \<le> n)
          \<and> geotop_mesh (\<lambda>x y. norm (x - y)) bK
            \<le> (real n / real (Suc n))
             * geotop_mesh (\<lambda>x y. norm (x - y)) K)"

definition geotop_barycentric_subdivision ::
  "'a::real_normed_vector set set \<Rightarrow> 'a set set" where
  "geotop_barycentric_subdivision K = (SOME bK. geotop_is_barycentric_Sd bK K)"

abbreviation geotop_Sd :: "'a::real_normed_vector set set \<Rightarrow> 'a set set" where
  "geotop_Sd K \<equiv> geotop_barycentric_subdivision K"

(** Iterated barycentric subdivision \<open>Sd^m(K)\<close>. **)
primrec geotop_iterated_Sd ::
  "nat \<Rightarrow> 'a::real_normed_vector set set \<Rightarrow> 'a set set" where
  "geotop_iterated_Sd 0 K = K"
| "geotop_iterated_Sd (Suc m) K = geotop_Sd (geotop_iterated_Sd m K)"

(** Reflexivity of subdivision: every complex is a subdivision of itself. **)
lemma geotop_is_subdivision_refl:
  fixes K :: "'a::real_normed_vector set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_is_subdivision K K"
proof -
  have hrefl: "geotop_refines K K"
    unfolding geotop_refines_def by (by100 blast)
  show ?thesis
    unfolding geotop_is_subdivision_def
    using hK hrefl by (by100 blast)
qed

(** Transitivity of subdivision: if C < B and B < A, then C < A. **)
lemma geotop_is_subdivision_trans:
  fixes K L M :: "'a::real_normed_vector set set"
  assumes hLK: "geotop_is_subdivision L K"
  assumes hML: "geotop_is_subdivision M L"
  shows "geotop_is_subdivision M K"
proof -
  have hKcomp: "geotop_is_complex K"
    using hLK unfolding geotop_is_subdivision_def by (by100 blast)
  have hMcomp: "geotop_is_complex M"
    using hML unfolding geotop_is_subdivision_def by (by100 blast)
  have hML_ref: "geotop_refines M L"
    using hML unfolding geotop_is_subdivision_def by (by100 blast)
  have hLK_ref: "geotop_refines L K"
    using hLK unfolding geotop_is_subdivision_def by (by100 blast)
  have hML_poly: "geotop_polyhedron M = geotop_polyhedron L"
    using hML unfolding geotop_is_subdivision_def by (by100 blast)
  have hLK_poly: "geotop_polyhedron L = geotop_polyhedron K"
    using hLK unfolding geotop_is_subdivision_def by (by100 blast)
  (** Transitivity of refines: m \<subseteq> l \<subseteq> k. **)
  have hMK_ref: "geotop_refines M K"
    unfolding geotop_refines_def
  proof
    fix m assume hm: "m \<in> M"
    obtain l where hlL: "l \<in> L" and hml: "m \<subseteq> l"
      using hm hML_ref unfolding geotop_refines_def by (by100 blast)
    obtain k where hkK: "k \<in> K" and hlk: "l \<subseteq> k"
      using hlL hLK_ref unfolding geotop_refines_def by (by100 blast)
    show "\<exists>k\<in>K. m \<subseteq> k"
      using hkK hml hlk by (by100 blast)
  qed
  have hMK_poly: "geotop_polyhedron M = geotop_polyhedron K"
    using hML_poly hLK_poly by (by100 simp)
  show ?thesis
    unfolding geotop_is_subdivision_def
    using hMcomp hKcomp hMK_ref hMK_poly by (by100 blast)
qed

(** from early.tex Lemma 4.9: \<open>Sd(K)\<close> is a simplicial complex and is a
    subdivision of \<open>K\<close>. The \<open>SOME\<close>-defined witness is selected from the set
    of subdivisions of K whose 0-simplexes contain those of K; this set is
    non-empty (take \<open>K\<close> itself), so \<open>SOME\<close> picks something with that property. **)
(** D-support: barycenter of a simplex is in the simplex. Classical fact:
    barycenter = convex combination of vertices with equal weights 1/card V,
    hence ∈ conv hull V = simplex. **)
lemma geotop_barycenter_in_simplex:
  fixes \<sigma> :: "'a::real_vector set"
  assumes h\<sigma>: "geotop_is_simplex \<sigma>"
  shows "geotop_barycenter \<sigma> \<in> \<sigma>"
proof -
  obtain V m n where hVfin: "finite V" and hVcard: "card V = n + 1"
                 and hnm: "n \<le> m" and hVgp: "geotop_general_position V m"
                 and h\<sigma>_hull: "\<sigma> = geotop_convex_hull V"
    using h\<sigma> unfolding geotop_is_simplex_def by (by100 blast)
  have hV_ne: "V \<noteq> {}"
  proof
    assume "V = {}"
    hence "card V = 0" by (by100 simp)
    thus False using hVcard by (by100 simp)
  qed
  have hV_card_pos: "card V > 0" using hVcard by (by100 simp)
  have h_sv: "geotop_simplex_vertices \<sigma> V"
    unfolding geotop_simplex_vertices_def
    using hVfin hVcard hnm hVgp h\<sigma>_hull by (by100 blast)
  (** The candidate barycenter = equal-weight combination of V's vertices. **)
  define u_V where "u_V = (\<Sum>w\<in>V. (1 / real (card V)) *\<^sub>R w)"
  have h_ex_witness: "\<exists>V'. geotop_simplex_vertices \<sigma> V' \<and>
                          u_V = (\<Sum>w\<in>V'. (1 / real (card V')) *\<^sub>R w)"
    unfolding u_V_def using h_sv by (by100 blast)
  (** barycenter σ picks some such u_V via SOME; its value ∈ σ. **)
  have h_bary_char:
    "\<forall>u. (\<exists>V'. geotop_simplex_vertices \<sigma> V' \<and>
               u = (\<Sum>w\<in>V'. (1 / real (card V')) *\<^sub>R w)) \<longrightarrow> u \<in> \<sigma>"
  proof (intro allI impI)
    fix u assume hu: "\<exists>V'. geotop_simplex_vertices \<sigma> V' \<and>
                           u = (\<Sum>w\<in>V'. (1 / real (card V')) *\<^sub>R w)"
    obtain V' where hV'_sv: "geotop_simplex_vertices \<sigma> V'"
                 and hu_val: "u = (\<Sum>w\<in>V'. (1 / real (card V')) *\<^sub>R w)"
      using hu by (by100 blast)
    have hV'fin: "finite V'"
      using hV'_sv unfolding geotop_simplex_vertices_def by (by100 blast)
    obtain m' n' where hV'card: "card V' = n' + 1"
      using hV'_sv unfolding geotop_simplex_vertices_def by (by100 blast)
    have hV'_card_pos: "card V' > 0" using hV'card by (by100 simp)
    have h\<sigma>_hull': "\<sigma> = geotop_convex_hull V'"
      using hV'_sv unfolding geotop_simplex_vertices_def by (by100 blast)
    have h\<sigma>_hull'_HOL: "\<sigma> = convex hull V'"
      using h\<sigma>_hull' geotop_convex_hull_eq_HOL by (by100 simp)
    (** u is a convex combination: coefficients 1/card V' ≥ 0, sum = 1. **)
    have h_coef_nn: "\<forall>w\<in>V'. 1 / real (card V') \<ge> 0" using hV'_card_pos by (by100 simp)
    have h_coef_sum: "(\<Sum>w\<in>V'. 1 / real (card V')) = 1"
    proof -
      have h_const_sum: "(\<Sum>w\<in>V'. 1 / real (card V')) = real (card V') * (1 / real (card V'))"
        by (by100 simp)
      have h_mul: "real (card V') * (1 / real (card V')) = 1" using hV'_card_pos by (by100 simp)
      show ?thesis using h_const_sum h_mul by (by100 simp)
    qed
    have h_u_in_hull: "u \<in> convex hull V'"
    proof -
      let ?t = "\<lambda>w. (1 / real (card V')::real)"
      have h_t_nn: "\<forall>w\<in>V'. 0 \<le> ?t w" using h_coef_nn by (by100 simp)
      have h_t_sum: "sum ?t V' = 1" using h_coef_sum by (by100 simp)
      have h_t_combo: "(\<Sum>w\<in>V'. ?t w *\<^sub>R w) = u" using hu_val by (by100 simp)
      have h_hull_char: "convex hull V' = {y. \<exists>u'. (\<forall>x\<in>V'. 0 \<le> u' x)
                             \<and> sum u' V' = 1 \<and> (\<Sum>x\<in>V'. u' x *\<^sub>R x) = y}"
        by (rule convex_hull_finite[OF hV'fin])
      have h_u_form: "\<exists>u'. (\<forall>x\<in>V'. 0 \<le> u' x)
                       \<and> sum u' V' = 1 \<and> (\<Sum>x\<in>V'. u' x *\<^sub>R x) = u"
      proof (rule exI[where x = "?t"])
        show "(\<forall>x\<in>V'. 0 \<le> ?t x) \<and> sum ?t V' = 1 \<and> (\<Sum>x\<in>V'. ?t x *\<^sub>R x) = u"
          using h_t_nn h_t_sum h_t_combo by (by100 blast)
      qed
      show ?thesis using h_u_form h_hull_char by (by100 blast)
    qed
    show "u \<in> \<sigma>" using h_u_in_hull h\<sigma>_hull'_HOL by (by100 simp)
  qed
  show ?thesis unfolding geotop_barycenter_def
  proof (rule someI2[where a = u_V])
    show "\<exists>V'. geotop_simplex_vertices \<sigma> V' \<and>
               u_V = (\<Sum>w\<in>V'. (1 / real (card V')) *\<^sub>R w)" by (rule h_ex_witness)
  next
    fix u
    assume hu: "\<exists>V'. geotop_simplex_vertices \<sigma> V' \<and>
                      u = (\<Sum>w\<in>V'. (1 / real (card V')) *\<^sub>R w)"
    show "u \<in> \<sigma>" using h_bary_char hu by (by100 blast)
  qed
qed

(** Classical existence of a barycentric subdivision satisfying the full spec.
    Moise early.tex Def 4.4 + Lemma 4.11 give the concrete construction:
    bK = {conv hull (barycenter ` flag) | flag a chain σ_0 ⊊ σ_1 ⊊ ⋯ ⊊ σ_n in K}.

    Detailed proof sketch (CLAUDE.md Phase 3 "more and more detailed formal
    proof sketches"): scaffold into 5 sub-goals, each representing one of
    the barycentric_Sd_def conjuncts. Each sub-goal is independently
    tractable in future sessions. **)
lemma geotop_classical_Sd_exists:
  fixes K :: "'a::real_normed_vector set set"
  assumes hK: "geotop_is_complex K"
  shows "\<exists>bK. geotop_is_barycentric_Sd bK K"
proof -
  (** CONSTRUCTION: A flag in K is a non-empty strictly-increasing chain
      of K-simplices [σ_0, σ_1, ..., σ_n] with σ_0 ⊊ σ_1 ⊊ ⋯ ⊊ σ_n.
      bK = set of convex hulls of barycenter sets of all such flags. **)
  define flags :: "'a set list set" where
    "flags = {c. c \<noteq> [] \<and> set c \<subseteq> K \<and> sorted_wrt (\<lambda>\<sigma> \<tau>. \<sigma> \<subset> \<tau>) c \<and> distinct c}"
  define bK :: "'a set set" where
    "bK = {geotop_convex_hull (geotop_barycenter ` set c) | c. c \<in> flags}"
  (** STEP 1: bK is a simplicial complex (K.0, K.1, K.2, K.3 axioms).
      Classical PL fact (Moise early.tex Lemma 4.9-like argument):
      - K.0: each hull of |flag| ≤ (n+1) affinely-indep barycenters is a simplex.
      - K.1: faces of a flag-simplex = hulls of sub-flags.
      - K.2: two flag-simplices intersect in the hull of their common sub-flag.
      - K.3: inherits from finite (in finite K) or local finiteness of K. **)
  have h_bK_complex: "geotop_is_complex bK"
    sorry \<comment> \<open>D-step 1: bK is a complex (K.0/1/2/3 via flag-based simplex structure).\<close>
  (** STEP 2: bK is a subdivision of K (same polyhedron, each bK simplex ⊆ some K simplex).
      Split into: (2a) polyhedron eq, (2b) refines. Refines provable via
      geotop_barycenter_in_simplex + sorted_wrt structure; polyhedron eq
      needs barycentric decomposition (deferred). **)
  have h_K_simp_all: "\<forall>\<tau>\<in>K. geotop_is_simplex \<tau>"
    by (rule conjunct1[OF hK[unfolded geotop_is_complex_def]])
  (** (2b) refines bK K: each τ ∈ bK sits inside the TOP simplex of its flag. **)
  have h_bK_refines: "geotop_refines bK K"
    unfolding geotop_refines_def
  proof (rule ballI)
    fix \<tau> assume h\<tau>_bK: "\<tau> \<in> bK"
    obtain c where hc_flag: "c \<in> flags"
                and h\<tau>_hull: "\<tau> = geotop_convex_hull (geotop_barycenter ` set c)"
      using h\<tau>_bK unfolding bK_def by (by100 blast)
    have hc_ne: "c \<noteq> []" using hc_flag unfolding flags_def by (by100 blast)
    have hc_subK: "set c \<subseteq> K" using hc_flag unfolding flags_def by (by100 blast)
    have hc_sorted: "sorted_wrt (\<lambda>\<sigma>\<^sub>1 \<sigma>\<^sub>2. \<sigma>\<^sub>1 \<subset> \<sigma>\<^sub>2) c"
      using hc_flag unfolding flags_def by (by100 blast)
    (** σ = last c ∈ K. **)
    define \<sigma> :: "'a set" where "\<sigma> = last c"
    have h\<sigma>_in_c: "\<sigma> \<in> set c" unfolding \<sigma>_def using hc_ne by (by100 simp)
    have h\<sigma>_K: "\<sigma> \<in> K" using h\<sigma>_in_c hc_subK by (by100 blast)
    (** Every element s ∈ set c satisfies s ⊆ σ (last c). **)
    have h_all_sub: "\<forall>s\<in>set c. s \<subseteq> \<sigma>"
    proof
      fix s assume hs_c: "s \<in> set c"
      show "s \<subseteq> \<sigma>"
      proof (cases "s = \<sigma>")
        case True thus ?thesis by (by100 simp)
      next
        case h_ne: False
        (** s ≠ last c; sorted gives s ⊊ last c. **)
        have hs_lt: "s \<subset> \<sigma>"
        proof -
          have h_append: "butlast c @ [last c] = c" using hc_ne by (rule append_butlast_last_id)
          have h_set_eq: "set c = set (butlast c) \<union> {last c}"
          proof -
            have "set c = set (butlast c @ [last c])" using h_append by (by100 simp)
            also have "\<dots> = set (butlast c) \<union> set [last c]" by (by100 simp)
            also have "\<dots> = set (butlast c) \<union> {last c}" by (by100 simp)
            finally show ?thesis .
          qed
          have hs_in_split: "s \<in> set (butlast c) \<or> s = last c"
            using hs_c h_set_eq by (by100 blast)
          have hs_butlast: "s \<in> set (butlast c)" using hs_in_split h_ne unfolding \<sigma>_def by (by100 blast)
          have h_last_in: "last c \<in> set c" using hc_ne last_in_set by (by100 blast)
          (** Apply sorted_wrt: for s ∈ butlast, last follows s. **)
          have h_sw_split: "sorted_wrt (\<subset>) (butlast c @ [last c])"
            using hc_sorted h_append by (by100 simp)
          have h_sw_split_expand: "sorted_wrt (\<subset>) (butlast c)
                \<and> sorted_wrt (\<subset>) [last c]
                \<and> (\<forall>x\<in>set (butlast c). \<forall>y\<in>set [last c]. x \<subset> y)"
            using h_sw_split sorted_wrt_append[of "(\<subset>)" "butlast c" "[last c]"]
            by (by100 blast)
          have h_sw_aux: "\<forall>x\<in>set (butlast c). x \<subset> last c"
            using h_sw_split_expand by (by100 simp)
          show ?thesis using h_sw_aux hs_butlast unfolding \<sigma>_def by (by100 blast)
        qed
        thus ?thesis by (by100 blast)
      qed
    qed
    (** Each barycenter is in its simplex ⊆ σ. **)
    have h_bary_sub_\<sigma>: "geotop_barycenter ` set c \<subseteq> \<sigma>"
    proof
      fix b assume hb: "b \<in> geotop_barycenter ` set c"
      obtain s where hs_c: "s \<in> set c" and hb_eq: "b = geotop_barycenter s"
        using hb by (by100 blast)
      have hs_K: "s \<in> K" using hs_c hc_subK by (by100 blast)
      have hs_simp: "geotop_is_simplex s" using hs_K h_K_simp_all by (by100 blast)
      have hb_in_s: "b \<in> s" using hb_eq geotop_barycenter_in_simplex[OF hs_simp] by (by100 simp)
      have hs_sub_\<sigma>: "s \<subseteq> \<sigma>" using hs_c h_all_sub by (by100 blast)
      show "b \<in> \<sigma>" using hb_in_s hs_sub_\<sigma> by (by100 blast)
    qed
    (** σ is convex (simplex = conv hull). **)
    have h\<sigma>_cvx: "convex \<sigma>"
    proof -
      obtain V\<^sub>\<sigma> where hV\<^sub>\<sigma>: "\<sigma> = geotop_convex_hull V\<^sub>\<sigma>"
        using h\<sigma>_K h_K_simp_all unfolding geotop_is_simplex_def by (by100 blast)
      have hV\<^sub>\<sigma>_HOL: "\<sigma> = convex hull V\<^sub>\<sigma>"
        using hV\<^sub>\<sigma> geotop_convex_hull_eq_HOL by (by100 simp)
      show ?thesis using hV\<^sub>\<sigma>_HOL convex_convex_hull by (by100 simp)
    qed
    (** conv hull of barycenters ⊆ σ (convex). **)
    have h_hull_HOL_sub: "convex hull (geotop_barycenter ` set c) \<subseteq> \<sigma>"
      using h_bary_sub_\<sigma> h\<sigma>_cvx hull_minimal[of "geotop_barycenter ` set c" \<sigma> convex]
      by (by100 blast)
    have h\<tau>_hullHOL: "\<tau> = convex hull (geotop_barycenter ` set c)"
      using h\<tau>_hull geotop_convex_hull_eq_HOL by (by100 simp)
    have h\<tau>_sub_\<sigma>: "\<tau> \<subseteq> \<sigma>" using h\<tau>_hullHOL h_hull_HOL_sub by (by100 simp)
    show "\<exists>\<sigma>'\<in>K. \<tau> \<subseteq> \<sigma>'" using h\<sigma>_K h\<tau>_sub_\<sigma> by (by100 blast)
  qed
  (** (2a) polyhedron bK = polyhedron K — deferred (requires barycentric decomposition). **)
  have h_bK_poly: "geotop_polyhedron bK = geotop_polyhedron K"
    sorry \<comment> \<open>D-step 2a: polyhedron equality (barycentric decomposition of σ ∈ K).\<close>
  (** Assemble (2a) + (2b) + complex assumptions. **)
  have h_bK_sub: "geotop_is_subdivision bK K"
    unfolding geotop_is_subdivision_def
    using h_bK_complex hK h_bK_poly h_bK_refines by (by100 blast)
  (** STEP 3: 0-simplices of K are preserved in bK.
      Proof: for σ = {v} ∈ K with dim 0, the flag [{v}] is a valid 1-element
      chain. barycenter {v} = v. conv hull {v} = {v} = σ ∈ bK. **)
  have h_bK_0simp: "\<forall>\<sigma>. geotop_simplex_dim \<sigma> 0 \<and> \<sigma> \<in> K \<longrightarrow> \<sigma> \<in> bK"
  proof (intro allI impI)
    fix \<sigma> assume h\<sigma>: "geotop_simplex_dim \<sigma> 0 \<and> \<sigma> \<in> K"
    have h\<sigma>_dim: "geotop_simplex_dim \<sigma> 0" using h\<sigma> by (by100 blast)
    have h\<sigma>_K: "\<sigma> \<in> K" using h\<sigma> by (by100 blast)
    (** Extract σ = {v}. **)
    obtain V m where hVfin: "finite V" and hVcard: "card V = 0 + 1"
                 and hnm: "0 \<le> m" and hVgp: "geotop_general_position V m"
                 and h\<sigma>_hull: "\<sigma> = geotop_convex_hull V"
      using h\<sigma>_dim unfolding geotop_simplex_dim_def by (by100 blast)
    have hVcard1: "card V = 1" using hVcard by (by100 simp)
    have hVsing: "\<exists>v. V = {v}"
      using hVcard1 card_1_singletonE by (by100 metis)
    obtain v where hVeq: "V = {v}" using hVsing by (by100 blast)
    have h\<sigma>_sing: "\<sigma> = {v}"
      using h\<sigma>_hull hVeq geotop_convex_hull_eq_HOL[of "{v}"] by (by100 simp)
    (** Flag [σ] = [{v}] is in flags. **)
    let ?c = "[\<sigma>]"
    have h_c_ne: "?c \<noteq> []" by (by100 simp)
    have h_set_c: "set ?c = {\<sigma>}" by (by100 simp)
    have h_c_subK: "set ?c \<subseteq> K" using h_set_c h\<sigma>_K by (by100 simp)
    have h_c_sorted: "sorted_wrt (\<lambda>\<tau>\<^sub>1 \<tau>\<^sub>2. \<tau>\<^sub>1 \<subset> \<tau>\<^sub>2) ?c" by (by100 simp)
    have h_c_dist: "distinct ?c" by (by100 simp)
    have h_c_flag: "?c \<in> flags"
      unfolding flags_def using h_c_ne h_c_subK h_c_sorted h_c_dist by (by100 simp)
    (** barycenter ` set c = {barycenter σ}. **)
    have h_bary_img: "geotop_barycenter ` set ?c = {geotop_barycenter \<sigma>}"
      using h_set_c by (by100 simp)
    (** barycenter σ = v. Key: for σ = {v}, any V' with conv hull V' = σ must
        be {v}, so barycenter's weighted average is always v. **)
    have h_bary_v: "geotop_barycenter \<sigma> = v"
    proof -
      have h_sv: "geotop_simplex_vertices \<sigma> V"
        unfolding geotop_simplex_vertices_def
        using hVfin hVcard hnm hVgp h\<sigma>_hull by (by100 blast)
      have h_v_val: "v = (\<Sum>w\<in>V. (1 / real (card V)) *\<^sub>R w)"
        using hVeq hVcard1 by (by100 simp)
      have h_ex: "\<exists>V'. geotop_simplex_vertices \<sigma> V' \<and>
                      v = (\<Sum>w\<in>V'. (1 / real (card V')) *\<^sub>R w)"
        using h_sv h_v_val by (by100 blast)
      (** For any V' with simplex_vertices σ V': V' = {v}. **)
      have h_V'_char: "\<And>V'. geotop_simplex_vertices \<sigma> V' \<Longrightarrow> V' = {v}"
      proof -
        fix V' assume hV'_sv: "geotop_simplex_vertices \<sigma> V'"
        have hV'fin: "finite V'"
          using hV'_sv unfolding geotop_simplex_vertices_def by (by100 blast)
        have hV'_hull: "\<sigma> = geotop_convex_hull V'"
          using hV'_sv unfolding geotop_simplex_vertices_def by (by100 blast)
        have hV'_hull_HOL: "\<sigma> = convex hull V'"
          using hV'_hull geotop_convex_hull_eq_HOL by (by100 simp)
        have hV'_sing: "convex hull V' = {v}" using hV'_hull_HOL h\<sigma>_sing by (by100 simp)
        (** V' ⊆ conv hull V' = {v}, and card V' ≥ 1, so V' = {v}. **)
        have hV'_sub: "V' \<subseteq> convex hull V'" by (rule hull_subset)
        have hV'_sub_v: "V' \<subseteq> {v}" using hV'_sub hV'_sing by (by100 simp)
        obtain n' m' where hV'_card_raw: "card V' = n' + 1"
                       and hV'_fin_raw: "finite V'"
          using hV'_sv unfolding geotop_simplex_vertices_def by (by100 blast)
        have hV'_card_ge1: "card V' \<ge> 1" using hV'_card_raw by (by100 simp)
        have hV'_card_le1: "card V' \<le> 1"
          using hV'_sub_v hV'_fin_raw card_mono[of "{v}" V'] by (by100 simp)
        have hV'_card1: "card V' = 1" using hV'_card_ge1 hV'_card_le1 by (by100 linarith)
        have hV'_ne: "V' \<noteq> {}"
        proof
          assume "V' = {}"
          hence "card V' = 0" by (by100 simp)
          thus False using hV'_card1 by (by100 simp)
        qed
        show "V' = {v}" using hV'_sub_v hV'_ne by (by100 blast)
      qed
      show ?thesis unfolding geotop_barycenter_def
      proof (rule someI2[where a = v])
        show "\<exists>V'. geotop_simplex_vertices \<sigma> V' \<and>
                 v = (\<Sum>w\<in>V'. (1 / real (card V')) *\<^sub>R w)" by (rule h_ex)
      next
        fix w assume hw: "\<exists>V'. geotop_simplex_vertices \<sigma> V' \<and>
                                w = (\<Sum>x\<in>V'. (1 / real (card V')) *\<^sub>R x)"
        obtain V' where hV'_sv: "geotop_simplex_vertices \<sigma> V'"
                     and hw_val: "w = (\<Sum>x\<in>V'. (1 / real (card V')) *\<^sub>R x)"
          using hw by (by100 blast)
        have hV'_eq_v: "V' = {v}" using h_V'_char hV'_sv by (by100 simp)
        have hw_sum: "w = (\<Sum>x\<in>{v}. (1 / real (card {v})) *\<^sub>R x)"
          using hw_val hV'_eq_v by (by100 simp)
        have hw_v: "w = v" using hw_sum by (by100 simp)
        show "w = v" by (rule hw_v)
      qed
    qed
    (** conv hull {v} = {v} = σ. **)
    have h_hull_v: "geotop_convex_hull {v} = {v}"
      using geotop_convex_hull_eq_HOL[of "{v}"] by (by100 simp)
    (** So σ = hull of barycenters of flag c. **)
    have h_\<sigma>_bK: "\<sigma> = geotop_convex_hull (geotop_barycenter ` set ?c)"
      using h\<sigma>_sing h_bary_img h_bary_v h_hull_v by (by100 simp)
    have h_\<sigma>_bK_set: "\<sigma> \<in> bK"
      unfolding bK_def using h_c_flag h_\<sigma>_bK by (by100 blast)
    show "\<sigma> \<in> bK" by (rule h_\<sigma>_bK_set)
  qed
  (** STEP 4 (combined with STEP 5): dim preservation AND mesh shrinkage.
      Moise early.tex Lemma 4.11: flag of length ≤ n+1 gives simplex of dim ≤ n.
      Mesh: bary(σ_0)-to-bary(σ_n) distance ≤ (n/(n+1)) · diam(σ_n) via
      center-of-mass lemma (distance from centroid to vertex of simplex is
      at most n/(n+1) times diameter). **)
  have h_dim_mesh: "\<forall>n::nat.
        (\<forall>\<sigma>\<in>K. \<forall>k. geotop_simplex_dim \<sigma> k \<longrightarrow> k \<le> n) \<longrightarrow>
        (\<forall>\<sigma>'\<in>bK. \<forall>k. geotop_simplex_dim \<sigma>' k \<longrightarrow> k \<le> n)
        \<and> geotop_mesh (\<lambda>x y. norm (x - y)) bK
          \<le> (real n / real (Suc n))
           * geotop_mesh (\<lambda>x y. norm (x - y)) K"
    sorry \<comment> \<open>D-step 4+5: dim preservation + mesh shrinkage (Moise Lemma 4.11).\<close>
  (** COMBINE into the barycentric-Sd predicate. **)
  have h_bary: "geotop_is_barycentric_Sd bK K"
    unfolding geotop_is_barycentric_Sd_def
    using h_bK_sub h_bK_0simp h_dim_mesh by (by100 blast)
  show ?thesis using h_bary by (by100 blast)
qed

lemma geotop_Sd_is_barycentric:
  fixes K :: "'a::real_normed_vector set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_is_barycentric_Sd (geotop_Sd K) K"
  unfolding geotop_barycentric_subdivision_def
  using someI_ex[OF geotop_classical_Sd_exists[OF hK]] by (by100 blast)

lemma geotop_Sd_is_subdivision:
  fixes K :: "'a::real_normed_vector set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_is_subdivision (geotop_Sd K) K"
  using geotop_Sd_is_barycentric[OF hK]
  unfolding geotop_is_barycentric_Sd_def by (by100 blast)

(** The mesh-shrinkage property as a usable helper. **)
lemma geotop_Sd_mesh_shrinkage:
  fixes K :: "'a::real_normed_vector set set"
  assumes hK: "geotop_is_complex K"
  assumes hdim: "\<forall>\<sigma>\<in>K. \<forall>k. geotop_simplex_dim \<sigma> k \<longrightarrow> k \<le> n"
  shows "(\<forall>\<sigma>'\<in>geotop_Sd K. \<forall>k. geotop_simplex_dim \<sigma>' k \<longrightarrow> k \<le> n)
       \<and> geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_Sd K)
         \<le> (real n / real (Suc n))
          * geotop_mesh (\<lambda>x y. norm (x - y)) K"
  using geotop_Sd_is_barycentric[OF hK] hdim
  unfolding geotop_is_barycentric_Sd_def by (by100 blast)

(** \<open>Sd^m(K)\<close> is a subdivision of \<open>K\<close> (induction on \<open>m\<close>). **)
lemma geotop_iterated_Sd_is_subdivision:
  fixes K :: "'a::real_normed_vector set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_is_subdivision (geotop_iterated_Sd m K) K"
proof (induction m)
  case 0
  show ?case by (simp add: geotop_is_subdivision_refl[OF hK])
next
  case (Suc m)
  (** \<open>Sd^m(K) < K\<close> (IH), hence \<open>Sd^m(K)\<close> is a complex; then \<open>Sd(Sd^m K) < Sd^m K\<close>
      by \<open>geotop_Sd_is_subdivision\<close>; then \<open>Sd^{Suc m} K < K\<close> by transitivity. **)
  have hSdm_comp: "geotop_is_complex (geotop_iterated_Sd m K)"
    using Suc.IH unfolding geotop_is_subdivision_def by (by100 blast)
  have hSuc_m: "geotop_is_subdivision (geotop_iterated_Sd (Suc m) K)
                                        (geotop_iterated_Sd m K)"
    by (simp add: geotop_Sd_is_subdivision[OF hSdm_comp])
  show ?case
    by (rule geotop_is_subdivision_trans[OF Suc.IH hSuc_m])
qed

(** \<open>Sd^{Suc m}(K)\<close> is a subdivision of \<open>Sd^m(K)\<close>. **)
lemma geotop_iterated_Sd_Suc_refines:
  fixes K :: "'a::real_normed_vector set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_is_subdivision (geotop_iterated_Sd (Suc m) K) (geotop_iterated_Sd m K)"
proof -
  have hSdm_comp: "geotop_is_complex (geotop_iterated_Sd m K)"
    using geotop_iterated_Sd_is_subdivision[OF hK, of m]
    unfolding geotop_is_subdivision_def by (by100 blast)
  show ?thesis
    by (simp add: geotop_Sd_is_subdivision[OF hSdm_comp])
qed

(** Monotonicity: \<open>Sd^N(K)\<close> is a subdivision of \<open>Sd^m(K)\<close> whenever \<open>N \<ge> m\<close>.
    Proof by induction on \<open>N - m\<close> using Suc-step refinement and transitivity. **)
lemma geotop_iterated_Sd_mono:
  fixes K :: "'a::real_normed_vector set set"
  assumes hK: "geotop_is_complex K"
  assumes hmN: "m \<le> N"
  shows "geotop_is_subdivision (geotop_iterated_Sd N K) (geotop_iterated_Sd m K)"
  using hmN
proof (induction N)
  case 0
  (** \<open>m \<le> 0\<close> forces \<open>m = 0\<close>, and any complex is a subdivision of itself. **)
  have hmzero: "m = 0" using "0.prems" by (by100 simp)
  have hSdK: "geotop_is_complex (geotop_iterated_Sd 0 K)"
    using hK by (by100 simp)
  show ?case
    using hmzero hSdK geotop_is_subdivision_refl[OF hK]
    by (by100 simp)
next
  case (Suc N)
  (** Two cases: \<open>m = Suc N\<close> (reflexivity) or \<open>m \<le> N\<close> (IH + Suc_refines + trans). **)
  show ?case
  proof (cases "m = Suc N")
    case True
    have hcomp: "geotop_is_complex (geotop_iterated_Sd (Suc N) K)"
      using geotop_iterated_Sd_is_subdivision[OF hK, of "Suc N"]
      unfolding geotop_is_subdivision_def by (by100 blast)
    show ?thesis
      using True hcomp geotop_is_subdivision_refl[OF hcomp]
      by (by100 simp)
  next
    case False
    have hmN: "m \<le> N" using Suc.prems False by (by100 simp)
    have hIH: "geotop_is_subdivision (geotop_iterated_Sd N K) (geotop_iterated_Sd m K)"
      using Suc.IH[OF hmN] .
    have hsuc: "geotop_is_subdivision (geotop_iterated_Sd (Suc N) K)
                                       (geotop_iterated_Sd N K)"
      by (rule geotop_iterated_Sd_Suc_refines[OF hK])
    show ?thesis
      by (rule geotop_is_subdivision_trans[OF hIH hsuc])
  qed
qed

text \<open>The Euclidean topology on a normed vector space, expressed as a topology in
  Top0's set-of-sets formulation, via the distance function \<open>\<lambda>x y. norm (x - y)\<close>.
  Moved up here from the Cells/manifolds subsection so that early.tex infrastructure
  (open stars, subspace topology) can reference it.\<close>
definition geotop_euclidean_topology :: "('a::real_normed_vector) set set" where
  "geotop_euclidean_topology = top1_metric_topology_on (UNIV::'a set) (\<lambda>x y. norm (x - y))"

(** Auxiliary: top1 norm-ball equals HOL-Analysis ball. **)
lemma top1_ball_on_UNIV_norm_eq_ball:
  fixes x :: "'a::real_normed_vector" and e :: real
  shows "top1_ball_on UNIV (\<lambda>x y. norm (x - y)) x e = ball x e"
  unfolding top1_ball_on_def ball_def dist_norm by simp

(** Bridge: the metric topology from the norm equals top1_open_sets, which
    coincides with HOL's built-in topology on real_normed_vector types. **)
lemma geotop_euclidean_topology_eq_open_sets:
  "(geotop_euclidean_topology :: ('a::real_normed_vector) set set) = top1_open_sets"
proof (rule set_eqI, rule iffI)
  fix U :: "'a set" assume hU: "U \<in> geotop_euclidean_topology"
  have hball: "\<And>x e. top1_ball_on UNIV (\<lambda>x y. norm (x - y)) x e = ball x e"
    by (rule top1_ball_on_UNIV_norm_eq_ball)
  have "\<forall>x\<in>U. \<exists>e>0. ball x e \<subseteq> U"
  proof (intro ballI)
    fix x assume hxU: "x \<in> U"
    obtain b where hb1: "b \<in> top1_metric_basis_on UNIV (\<lambda>x y. norm (x - y))"
               and hb2: "x \<in> b" and hb3: "b \<subseteq> U"
      using hU hxU
      unfolding geotop_euclidean_topology_def top1_metric_topology_on_def
                topology_generated_by_basis_def by blast
    obtain x' e' where hb_eq: "b = top1_ball_on UNIV (\<lambda>x y. norm (x - y)) x' e'"
                   and he': "0 < e'"
      using hb1 unfolding top1_metric_basis_on_def by blast
    have hb_ball: "b = ball x' e'" using hb_eq top1_ball_on_UNIV_norm_eq_ball by simp
    have hxb: "x \<in> ball x' e'" using hb2 hb_ball by simp
    obtain e where he0: "0 < e" and he_sub: "ball x e \<subseteq> ball x' e'"
      using hxb openE open_ball by blast
    from he_sub hb3 hb_ball he0 show "\<exists>e>0. ball x e \<subseteq> U" by auto
  qed
  then have "open U" using open_contains_ball by blast
  thus "U \<in> top1_open_sets" unfolding top1_open_sets_def by simp
next
  fix U :: "'a set" assume hU: "U \<in> top1_open_sets"
  then have hopen: "open U" unfolding top1_open_sets_def by simp
  have hball: "\<And>x e. top1_ball_on UNIV (\<lambda>x y. norm (x - y)) x e = ball x e"
    by (rule top1_ball_on_UNIV_norm_eq_ball)
  have hforall: "\<forall>x\<in>U. \<exists>e>0. ball x e \<subseteq> U"
    using hopen open_contains_ball by blast
  show "U \<in> geotop_euclidean_topology"
    unfolding geotop_euclidean_topology_def top1_metric_topology_on_def
              topology_generated_by_basis_def
  proof (intro CollectI conjI ballI)
    show "U \<subseteq> UNIV" by simp
  next
    fix x assume hxU: "x \<in> U"
    obtain e where he0: "0 < e" and heU: "ball x e \<subseteq> U"
      using hforall hxU by blast
    let ?b = "top1_ball_on UNIV (\<lambda>x y. norm (x - y)) x e"
    have hb_in: "?b \<in> top1_metric_basis_on UNIV (\<lambda>x y. norm (x - y))"
      unfolding top1_metric_basis_on_def using he0 by blast
    have hb_eq: "?b = ball x e" by (rule top1_ball_on_UNIV_norm_eq_ball)
    have hxb: "x \<in> ?b" using hb_eq he0 by simp
    have hbU: "?b \<subseteq> U" using hb_eq heU by simp
    show "\<exists>b \<in> top1_metric_basis_on UNIV (\<lambda>x y. norm (x - y)). x \<in> b \<and> b \<subseteq> U"
      using hb_in hxb hbU by blast
  qed
qed

(** from early.tex Lemma 4.10: open star of a vertex \<open>v\<close> in a complex \<open>K\<close>
    is the union of the relative interiors of simplexes of \<open>K\<close> having \<open>v\<close>
    as a vertex. We use HOL's \<open>rel_interior\<close> to express this. **)
definition geotop_open_star ::
  "'a::euclidean_space set set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "geotop_open_star K v = \<Union>{rel_interior \<sigma> |\<sigma>. \<sigma> \<in> K \<and> v \<in> \<sigma>}"

(** from early.tex Lemma 4.11: the open star is relatively open in \<open>|K|\<close>,
    i.e. its intersection with \<open>|K|\<close> equals itself and is open in the subspace. **)
lemma geotop_open_star_subset:
  fixes K :: "'a::euclidean_space set set"
  shows "geotop_open_star K v \<subseteq> geotop_polyhedron K"
proof
  fix x assume hx: "x \<in> geotop_open_star K v"
  then obtain \<sigma> where h\<sigma>: "\<sigma> \<in> K" and hv\<sigma>: "v \<in> \<sigma>" and hx\<sigma>: "x \<in> rel_interior \<sigma>"
    unfolding geotop_open_star_def by (by100 blast)
  have "x \<in> \<sigma>" using hx\<sigma> rel_interior_subset by (by100 blast)
  then show "x \<in> geotop_polyhedron K"
    using h\<sigma> unfolding geotop_polyhedron_def by (by100 blast)
qed

(** Alternative characterisation: \<open>|K| \<setminus> star_K(v)\<close> = union of simplices not
    containing \<open>v\<close>. This uses the fact that each point of \<open>|K|\<close> has a unique
    "support simplex" \<open>\<tau>_0\<close> (the face whose rel_interior it lies in), so
    \<open>x \<in> star_K(v)\<close> iff \<open>v \<in> \<tau>_0\<close>, iff \<open>x\<close> is in some rel_interior \<tau> with \<open>v \<in> \<tau>\<close>.
    Consequently the complement is \<open>\<Union>{\<tau> \<in> K : v \<notin> \<tau>}\<close>. **)
lemma geotop_open_star_complement:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_polyhedron K - geotop_open_star K v =
          \<Union>{\<tau> \<in> K. v \<notin> \<tau>}"
proof (rule set_eqI, rule iffI)
  fix x assume hLHS: "x \<in> geotop_polyhedron K - geotop_open_star K v"
  have hxK: "x \<in> geotop_polyhedron K" using hLHS by (by100 blast)
  have hx_not_star: "x \<notin> geotop_open_star K v" using hLHS by (by100 blast)
  (** Pick a simplex \<sigma> containing x. **)
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K" and hx\<sigma>: "x \<in> \<sigma>"
    using hxK unfolding geotop_polyhedron_def by (by100 blast)
  have h\<sigma>_simp: "geotop_is_simplex \<sigma>"
    using h\<sigma>K conjunct1[OF hK[unfolded geotop_is_complex_def]] by (by100 blast)
  obtain V\<^sub>\<sigma> where hV\<^sub>\<sigma>: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>"
    using h\<sigma>_simp unfolding geotop_is_simplex_def geotop_simplex_vertices_def
    by (by100 blast)
  obtain m n where hV\<^sub>\<sigma>fin: "finite V\<^sub>\<sigma>" and hV\<^sub>\<sigma>card: "card V\<^sub>\<sigma> = n + 1"
                and hnm: "n \<le> m" and hV\<^sub>\<sigma>gp: "geotop_general_position V\<^sub>\<sigma> m"
                and h\<sigma>_hull: "\<sigma> = geotop_convex_hull V\<^sub>\<sigma>"
    using hV\<^sub>\<sigma> unfolding geotop_simplex_vertices_def by (by100 blast)
  have h\<sigma>_hullHOL: "\<sigma> = convex hull V\<^sub>\<sigma>"
    using h\<sigma>_hull geotop_convex_hull_eq_HOL by (by100 simp)
  have hV\<^sub>\<sigma>_ai: "\<not> affine_dependent V\<^sub>\<sigma>"
    by (rule geotop_general_position_imp_aff_indep[OF hV\<^sub>\<sigma>])
  (** Find barycentric coords of x. **)
  have hx_hull: "x \<in> convex hull V\<^sub>\<sigma>" using hx\<sigma> h\<sigma>_hullHOL by (by100 simp)
  obtain u where hu_nn: "\<forall>w\<in>V\<^sub>\<sigma>. 0 \<le> u w" and hu_sum: "sum u V\<^sub>\<sigma> = 1"
             and hx_eq: "(\<Sum>w\<in>V\<^sub>\<sigma>. u w *\<^sub>R w) = x"
    using hx_hull hV\<^sub>\<sigma>fin convex_hull_finite[of V\<^sub>\<sigma>] by (by100 blast)
  (** Support set W, then \<tau>_0 = conv W. **)
  define W where "W = {w \<in> V\<^sub>\<sigma>. u w > 0}"
  define \<tau>\<^sub>0 where "\<tau>\<^sub>0 = convex hull W"
  have hWV\<^sub>\<sigma>: "W \<subseteq> V\<^sub>\<sigma>" unfolding W_def by (by100 blast)
  have hWfin: "finite W"
    unfolding W_def using hV\<^sub>\<sigma>fin finite_subset by (by100 fastforce)
  have hWne: "W \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> W \<noteq> {}"
    then have hallz: "\<forall>w\<in>V\<^sub>\<sigma>. u w = 0" unfolding W_def using hu_nn by (by100 fastforce)
    have "sum u V\<^sub>\<sigma> = 0" using hallz by (by100 simp)
    thus False using hu_sum by (by100 simp)
  qed
  have hu_pos_W: "\<forall>w\<in>W. 0 < u w" unfolding W_def by (by100 simp)
  have hsum_uW: "sum u W = 1"
  proof -
    have hz: "\<forall>w\<in>V\<^sub>\<sigma>-W. u w = 0" unfolding W_def using hu_nn by (by100 fastforce)
    have "sum u W = sum u V\<^sub>\<sigma>"
      using hV\<^sub>\<sigma>fin hWV\<^sub>\<sigma> hz sum.mono_neutral_left[of V\<^sub>\<sigma> W u] by (by100 blast)
    thus ?thesis using hu_sum by (by100 simp)
  qed
  have hx_W: "(\<Sum>w\<in>W. u w *\<^sub>R w) = x"
  proof -
    have hz: "\<forall>w\<in>V\<^sub>\<sigma>-W. u w *\<^sub>R w = 0"
      unfolding W_def using hu_nn by (by100 fastforce)
    have "(\<Sum>w\<in>W. u w *\<^sub>R w) = (\<Sum>w\<in>V\<^sub>\<sigma>. u w *\<^sub>R w)"
      using hV\<^sub>\<sigma>fin hWV\<^sub>\<sigma> hz sum.mono_neutral_left[of V\<^sub>\<sigma> W "\<lambda>w. u w *\<^sub>R w"]
      by (by100 blast)
    thus ?thesis using hx_eq by (by100 simp)
  qed
  have hW_ai: "\<not> affine_dependent W"
    using hV\<^sub>\<sigma>_ai hWV\<^sub>\<sigma> affine_dependent_subset by (by100 blast)
  have hx_rel\<tau>\<^sub>0: "x \<in> rel_interior \<tau>\<^sub>0"
    unfolding \<tau>\<^sub>0_def
    using hW_ai hu_pos_W hsum_uW hx_W
    rel_interior_convex_hull_explicit[OF hW_ai] by (by100 blast)
  (** \<tau>_0 is a face of \<sigma>, hence in K. **)
  have h_hull_eq_W: "geotop_convex_hull W = convex hull W"
    by (rule geotop_convex_hull_eq_HOL)
  have h\<tau>\<^sub>0_geo: "\<tau>\<^sub>0 = geotop_convex_hull W"
    unfolding \<tau>\<^sub>0_def using h_hull_eq_W by (by100 simp)
  have h\<tau>\<^sub>0_face_geo: "geotop_is_face \<tau>\<^sub>0 \<sigma>"
    unfolding geotop_is_face_def
    apply (rule exI[of _ V\<^sub>\<sigma>])
    apply (rule exI[of _ W])
    using hV\<^sub>\<sigma> hWne hWV\<^sub>\<sigma> h\<tau>\<^sub>0_geo by (by100 blast)
  have hK_fc: "\<forall>\<sigma>'\<in>K. \<forall>\<tau>'. geotop_is_face \<tau>' \<sigma>' \<longrightarrow> \<tau>' \<in> K"
    using conjunct1[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]]
    by (by100 blast)
  have h\<tau>\<^sub>0K: "\<tau>\<^sub>0 \<in> K" using hK_fc h\<sigma>K h\<tau>\<^sub>0_face_geo by (by100 blast)
  (** If \<open>v \<in> \<tau>_0\<close>, then \<open>x \<in> star_K(v)\<close>, contradiction. So \<open>v \<notin> \<tau>_0\<close>. **)
  have hv_not_\<tau>\<^sub>0: "v \<notin> \<tau>\<^sub>0"
  proof
    assume hv_\<tau>\<^sub>0: "v \<in> \<tau>\<^sub>0"
    have "x \<in> geotop_open_star K v"
      unfolding geotop_open_star_def
      using h\<tau>\<^sub>0K hv_\<tau>\<^sub>0 hx_rel\<tau>\<^sub>0 by (by100 blast)
    thus False using hx_not_star by (by100 blast)
  qed
  (** x \<in> \<tau>_0 (since x \<in> rel_interior \<tau>_0 \<subseteq> \<tau>_0). **)
  have hx_\<tau>\<^sub>0: "x \<in> \<tau>\<^sub>0" using hx_rel\<tau>\<^sub>0 rel_interior_subset by (by100 blast)
  show "x \<in> \<Union>{\<tau> \<in> K. v \<notin> \<tau>}"
    using h\<tau>\<^sub>0K hv_not_\<tau>\<^sub>0 hx_\<tau>\<^sub>0 by (by100 blast)
next
  fix x assume hRHS: "x \<in> \<Union>{\<tau> \<in> K. v \<notin> \<tau>}"
  obtain \<tau> where h\<tau>K: "\<tau> \<in> K" and h\<tau>nv: "v \<notin> \<tau>" and hx\<tau>: "x \<in> \<tau>"
    using hRHS by (by100 blast)
  have hxK: "x \<in> geotop_polyhedron K"
    using h\<tau>K hx\<tau> unfolding geotop_polyhedron_def by (by100 blast)
  have hx_not_star: "x \<notin> geotop_open_star K v"
  proof
    assume hx_star: "x \<in> geotop_open_star K v"
    obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K" and hv\<sigma>: "v \<in> \<sigma>"
                 and hx_rel: "x \<in> rel_interior \<sigma>"
      using hx_star unfolding geotop_open_star_def by (by100 blast)
    have hx\<sigma>: "x \<in> \<sigma>" using hx_rel rel_interior_subset by (by100 blast)
    have h\<sigma>_cap_\<tau>_ne: "\<sigma> \<inter> \<tau> \<noteq> {}" using hx\<sigma> hx\<tau> by (by100 blast)
    (** \<sigma> \<inter> \<tau> is a face of \<sigma> (K intersection-compat). **)
    have hK_inter: "\<forall>\<sigma>'\<in>K. \<forall>\<tau>'\<in>K. \<sigma>' \<inter> \<tau>' \<noteq> {} \<longrightarrow>
                      geotop_is_face (\<sigma>' \<inter> \<tau>') \<sigma>' \<and> geotop_is_face (\<sigma>' \<inter> \<tau>') \<tau>'"
      using conjunct1[OF conjunct2[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]]]
      by (by100 blast)
    have h_face_\<sigma>: "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma>"
      using hK_inter h\<sigma>K h\<tau>K h\<sigma>_cap_\<tau>_ne by (by100 blast)
    (** Get vertex set of \<sigma> and the subset W such that \<sigma> \<inter> \<tau> = conv W. **)
    obtain V\<^sub>\<sigma> W where hV\<^sub>\<sigma>: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>" and hWne: "W \<noteq> {}"
                   and hWV\<^sub>\<sigma>: "W \<subseteq> V\<^sub>\<sigma>"
                   and h\<sigma>\<tau>_hull: "\<sigma> \<inter> \<tau> = geotop_convex_hull W"
      using h_face_\<sigma> unfolding geotop_is_face_def by (by100 blast)
    have h\<sigma>\<tau>_hullHOL: "\<sigma> \<inter> \<tau> = convex hull W"
      using h\<sigma>\<tau>_hull geotop_convex_hull_eq_HOL by (by100 simp)
    have h\<sigma>_hullHOL: "\<sigma> = convex hull V\<^sub>\<sigma>"
      using hV\<^sub>\<sigma> geotop_convex_hull_eq_HOL
      unfolding geotop_simplex_vertices_def by (by100 blast)
    have hV\<^sub>\<sigma>_ai: "\<not> affine_dependent V\<^sub>\<sigma>"
      by (rule geotop_general_position_imp_aff_indep[OF hV\<^sub>\<sigma>])
    have h_face_HOL: "(\<sigma> \<inter> \<tau>) face_of \<sigma>"
    proof -
      have "(\<sigma> \<inter> \<tau>) face_of (convex hull V\<^sub>\<sigma>)"
        using hV\<^sub>\<sigma>_ai hWV\<^sub>\<sigma> h\<sigma>\<tau>_hullHOL
        face_of_convex_hull_affine_independent[OF hV\<^sub>\<sigma>_ai, of "\<sigma> \<inter> \<tau>"]
        by (by100 blast)
      thus ?thesis using h\<sigma>_hullHOL by (by100 simp)
    qed
    (** Case (a): \<sigma> \<inter> \<tau> = \<sigma>, i.e., \<sigma> \<subseteq> \<tau>. Then v \<in> \<sigma> \<subseteq> \<tau>, contradicting v \<notin> \<tau>. **)
    show False
    proof (cases "\<sigma> \<inter> \<tau> = \<sigma>")
      case True
      then have h\<sigma>_sub_\<tau>: "\<sigma> \<subseteq> \<tau>" by (by100 blast)
      have "v \<in> \<tau>" using hv\<sigma> h\<sigma>_sub_\<tau> by (by100 blast)
      thus False using h\<tau>nv by (by100 blast)
    next
      case False
      (** Proper face, disjoint from rel_interior \<sigma>. **)
      have h_disj: "(\<sigma> \<inter> \<tau>) \<inter> rel_interior \<sigma> = {}"
        using face_of_disjoint_rel_interior[OF h_face_HOL False] by (by100 blast)
      have hx_in: "x \<in> (\<sigma> \<inter> \<tau>) \<inter> rel_interior \<sigma>"
        using hx\<sigma> hx\<tau> hx_rel by (by100 blast)
      thus False using h_disj by (by100 blast)
    qed
  qed
  show "x \<in> geotop_polyhedron K - geotop_open_star K v"
    using hxK hx_not_star by (by100 blast)
qed

(** For finite \<open>K\<close>, the complement is closed (finite union of closed simplices),
    hence \<open>star_K(v)\<close> is relatively open in \<open>|K|\<close>. Proof via
    \<open>geotop_open_star_complement\<close> + finite closed simplices + compact-imp-closed. **)
(** E-support infrastructure: extract the intersection-face → HOL-face-of bridge.
    For σ, τ ∈ K (complex) with σ ∩ τ ≠ {}, σ ∩ τ is a HOL face_of σ.
    This enables face_of_disjoint_rel_interior-based disjointness arguments. **)
lemma geotop_complex_inter_face_HOL:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K" and h\<tau>K: "\<tau> \<in> K"
  assumes hne: "\<sigma> \<inter> \<tau> \<noteq> {}"
  shows "(\<sigma> \<inter> \<tau>) face_of \<sigma>"
proof -
  have hK_inter: "\<forall>\<sigma>'\<in>K. \<forall>\<tau>'\<in>K. \<sigma>' \<inter> \<tau>' \<noteq> {} \<longrightarrow>
                      geotop_is_face (\<sigma>' \<inter> \<tau>') \<sigma>' \<and> geotop_is_face (\<sigma>' \<inter> \<tau>') \<tau>'"
    using conjunct1[OF conjunct2[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]]]
    by (by100 blast)
  have h_face_geotop: "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma>"
    using hK_inter h\<sigma>K h\<tau>K hne by (by100 blast)
  obtain V\<^sub>\<sigma> W where hV\<^sub>\<sigma>: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>"
                 and hW_ne: "W \<noteq> {}" and hW_V\<^sub>\<sigma>: "W \<subseteq> V\<^sub>\<sigma>"
                 and h\<sigma>\<tau>_hull: "\<sigma> \<inter> \<tau> = geotop_convex_hull W"
    using h_face_geotop unfolding geotop_is_face_def by (by100 blast)
  have h\<sigma>\<tau>_hullHOL: "\<sigma> \<inter> \<tau> = convex hull W"
    using h\<sigma>\<tau>_hull geotop_convex_hull_eq_HOL by (by100 simp)
  have h\<sigma>_hullHOL: "\<sigma> = convex hull V\<^sub>\<sigma>"
    using hV\<^sub>\<sigma> geotop_convex_hull_eq_HOL
    unfolding geotop_simplex_vertices_def by (by100 blast)
  have hV\<^sub>\<sigma>_ai: "\<not> affine_dependent V\<^sub>\<sigma>"
    by (rule geotop_general_position_imp_aff_indep[OF hV\<^sub>\<sigma>])
  have h_face_V: "(\<sigma> \<inter> \<tau>) face_of (convex hull V\<^sub>\<sigma>)"
    using hV\<^sub>\<sigma>_ai hW_V\<^sub>\<sigma> h\<sigma>\<tau>_hullHOL
          face_of_convex_hull_affine_independent[OF hV\<^sub>\<sigma>_ai, of "\<sigma> \<inter> \<tau>"]
    by (by100 blast)
  show ?thesis using h_face_V h\<sigma>_hullHOL by (by100 simp)
qed

(** E-support: rel_interior disjointness for distinct simplices in a complex,
    restricted to the case where they intersect (so the face is proper in both). **)
lemma geotop_complex_rel_interior_disjoint_distinct:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K" and h\<tau>K: "\<tau> \<in> K"
  assumes h_ne: "\<sigma> \<noteq> \<tau>"
  shows "rel_interior \<sigma> \<inter> rel_interior \<tau> = {}"
proof (cases "\<sigma> \<inter> \<tau> = {}")
  case True
  have "rel_interior \<sigma> \<subseteq> \<sigma>" by (rule rel_interior_subset)
  moreover have "rel_interior \<tau> \<subseteq> \<tau>" by (rule rel_interior_subset)
  ultimately show ?thesis using True by (by100 blast)
next
  case h_int_ne: False
  have h_face_\<sigma>: "(\<sigma> \<inter> \<tau>) face_of \<sigma>"
    by (rule geotop_complex_inter_face_HOL[OF hK h\<sigma>K h\<tau>K h_int_ne])
  have h_face_\<tau>: "(\<sigma> \<inter> \<tau>) face_of \<tau>"
  proof -
    have h_eq: "\<sigma> \<inter> \<tau> = \<tau> \<inter> \<sigma>" by (by100 blast)
    have h_ne2: "\<tau> \<inter> \<sigma> \<noteq> {}" using h_int_ne by (by100 blast)
    have "(\<tau> \<inter> \<sigma>) face_of \<tau>"
      by (rule geotop_complex_inter_face_HOL[OF hK h\<tau>K h\<sigma>K h_ne2])
    thus ?thesis using h_eq by (by100 simp)
  qed
  (** If σ ∩ τ = σ, then σ ⊆ τ. Face-of gives σ is proper face of τ or equal. **)
  show ?thesis
  proof (cases "\<sigma> \<inter> \<tau> = \<sigma>")
    case h_eq_\<sigma>: True
    have h\<sigma>_sub: "\<sigma> \<subseteq> \<tau>" using h_eq_\<sigma> by (by100 blast)
    have h\<sigma>_face_\<tau>: "\<sigma> face_of \<tau>" using h_face_\<tau> h_eq_\<sigma> by (by100 simp)
    have h\<sigma>_ne_\<tau>: "\<sigma> \<noteq> \<tau>" by (rule h_ne)
    have h_\<sigma>_disj_int_\<tau>: "\<sigma> \<inter> rel_interior \<tau> = {}"
      by (rule face_of_disjoint_rel_interior[OF h\<sigma>_face_\<tau> h\<sigma>_ne_\<tau>])
    have h_ri_\<sigma>_sub: "rel_interior \<sigma> \<subseteq> \<sigma>" by (rule rel_interior_subset)
    show ?thesis using h_\<sigma>_disj_int_\<tau> h_ri_\<sigma>_sub by (by100 blast)
  next
    case h_ne_\<sigma>: False
    (** σ ∩ τ is a PROPER face of σ. **)
    have h_cap_disj: "(\<sigma> \<inter> \<tau>) \<inter> rel_interior \<sigma> = {}"
      by (rule face_of_disjoint_rel_interior[OF h_face_\<sigma> h_ne_\<sigma>])
    (** rel_interior σ ∩ rel_interior τ ⊆ σ ∩ τ ⊆ σ, then disjoint. **)
    have h_ri_\<sigma>_sub: "rel_interior \<sigma> \<subseteq> \<sigma>" by (rule rel_interior_subset)
    have h_ri_\<tau>_sub: "rel_interior \<tau> \<subseteq> \<tau>" by (rule rel_interior_subset)
    have h_sub_cap: "rel_interior \<sigma> \<inter> rel_interior \<tau> \<subseteq> \<sigma> \<inter> \<tau>"
      using h_ri_\<sigma>_sub h_ri_\<tau>_sub by (by100 blast)
    have h_sub_int: "rel_interior \<sigma> \<inter> rel_interior \<tau>
                      \<subseteq> (\<sigma> \<inter> \<tau>) \<inter> rel_interior \<sigma>"
      using h_sub_cap h_ri_\<sigma>_sub by (by100 blast)
    show ?thesis using h_sub_int h_cap_disj by (by100 blast)
  qed
qed

(** E-support: a convex subset of the open_star that contains a point of
    rel_interior σ (for σ ∋ v) is ⊆ σ, provided the convex subset stays
    within {rel_interior σ} (single simplex case). This trivial corollary
    exposes the key constraint; the full "T ⊆ open_star ⟹ T ⊆ σ" requires
    the sup-of-path argument and is still deferred. **)
lemma geotop_complex_point_in_unique_rel_interior:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>\<^sub>1K: "\<sigma>\<^sub>1 \<in> K" and h\<sigma>\<^sub>2K: "\<sigma>\<^sub>2 \<in> K"
  assumes hx\<^sub>1: "x \<in> rel_interior \<sigma>\<^sub>1"
  assumes hx\<^sub>2: "x \<in> rel_interior \<sigma>\<^sub>2"
  shows "\<sigma>\<^sub>1 = \<sigma>\<^sub>2"
proof (rule ccontr)
  assume h_ne: "\<sigma>\<^sub>1 \<noteq> \<sigma>\<^sub>2"
  have h_disj: "rel_interior \<sigma>\<^sub>1 \<inter> rel_interior \<sigma>\<^sub>2 = {}"
    by (rule geotop_complex_rel_interior_disjoint_distinct[OF hK h\<sigma>\<^sub>1K h\<sigma>\<^sub>2K h_ne])
  have hx_in: "x \<in> rel_interior \<sigma>\<^sub>1 \<inter> rel_interior \<sigma>\<^sub>2" using hx\<^sub>1 hx\<^sub>2 by (by100 blast)
  thus False using h_disj by (by100 blast)
qed

(** E-support: if x ∈ rel_interior σ and x ∈ σ' (both simplices of a complex),
    then σ ⊆ σ'. I.e., the "smallest simplex whose rel_interior contains x"
    is a face of every σ' ∈ K containing x. Key classical fact. **)
lemma geotop_complex_rel_interior_imp_subset:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K" and h\<sigma>'K: "\<sigma>' \<in> K"
  assumes hx_rel: "x \<in> rel_interior \<sigma>"
  assumes hx\<sigma>': "x \<in> \<sigma>'"
  shows "\<sigma> \<subseteq> \<sigma>'"
proof -
  have hx\<sigma>: "x \<in> \<sigma>" using hx_rel rel_interior_subset by (by100 blast)
  have h_int_ne: "\<sigma> \<inter> \<sigma>' \<noteq> {}" using hx\<sigma> hx\<sigma>' by (by100 blast)
  have h_face_HOL: "(\<sigma> \<inter> \<sigma>') face_of \<sigma>"
    by (rule geotop_complex_inter_face_HOL[OF hK h\<sigma>K h\<sigma>'K h_int_ne])
  show ?thesis
  proof (cases "\<sigma> \<inter> \<sigma>' = \<sigma>")
    case True
    thus ?thesis by (by100 blast)
  next
    case h_proper: False
    have h_disj: "(\<sigma> \<inter> \<sigma>') \<inter> rel_interior \<sigma> = {}"
      by (rule face_of_disjoint_rel_interior[OF h_face_HOL h_proper])
    have hx_in: "x \<in> (\<sigma> \<inter> \<sigma>') \<inter> rel_interior \<sigma>"
      using hx\<sigma> hx\<sigma>' hx_rel by (by100 blast)
    have "False" using hx_in h_disj by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
qed

lemma geotop_open_star_open_in_subspace:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K" and hKfin: "finite K"
  shows "geotop_open_star K v
           \<in> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
proof -
  (** Complement of star is finite union of closed simplices. **)
  define C where "C = \<Union>{\<tau> \<in> K. v \<notin> \<tau>}"
  have hC_eq: "geotop_polyhedron K - geotop_open_star K v = C"
    unfolding C_def by (rule geotop_open_star_complement[OF hK])
  have hK_simp: "\<forall>\<tau>\<in>K. geotop_is_simplex \<tau>"
    using conjunct1[OF hK[unfolded geotop_is_complex_def]] by (by100 blast)
  have hK_closed: "\<forall>\<tau>\<in>K. closed \<tau>"
  proof
    fix \<tau> assume h\<tau>K: "\<tau> \<in> K"
    have h\<tau>_simp: "geotop_is_simplex \<tau>" using h\<tau>K hK_simp by (by100 blast)
    obtain V where hV_fin: "finite V" and h\<tau>_hull: "\<tau> = geotop_convex_hull V"
      using h\<tau>_simp unfolding geotop_is_simplex_def by (by100 blast)
    have h\<tau>_hullHOL: "\<tau> = convex hull V"
      using h\<tau>_hull geotop_convex_hull_eq_HOL by (by100 simp)
    have "compact \<tau>"
      using h\<tau>_hullHOL hV_fin finite_imp_compact_convex_hull by (by100 simp)
    thus "closed \<tau>" using compact_imp_closed by (by100 blast)
  qed
  have hCfin: "finite {\<tau> \<in> K. v \<notin> \<tau>}" using hKfin by (by100 simp)
  have hC_closed: "closed C"
    unfolding C_def using hCfin hK_closed by (by100 blast)
  have hstar_eq: "geotop_open_star K v = geotop_polyhedron K \<inter> (UNIV - C)"
    using hC_eq geotop_open_star_subset[of K v] by (by100 blast)
  have hUC_open_HOL: "open (UNIV - C)"
  proof -
    have "open (- C)" using hC_closed open_Compl[of C] by (by100 blast)
    moreover have "- C = UNIV - C" by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  (** \<open>UNIV \<setminus> C\<close> is open (HOL sense); we need it in \<open>geotop_euclidean_topology\<close>.
      Use the fact (proved later) that \<open>geotop_euclidean_topology\<close> equals
      \<open>top1_open_sets\<close> (which is the HOL-open sets).
      Rather than forward-referencing the bridge, we unfold
      \<open>geotop_euclidean_topology\<close> directly and reduce to the metric topology. **)
  have hUC_top1: "UNIV - C \<in> geotop_euclidean_topology"
    using hUC_open_HOL
    unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  show ?thesis
    unfolding subspace_topology_def
    using hstar_eq hUC_top1 by (by100 blast)
qed

(** from early.tex Lemma 4.13: the vertex open stars cover \<open>|K|\<close>.
    Proof: for \<open>x \<in> \<sigma> \<in> K\<close> with vertex set \<open>V\<close> (finite, affinely indep), write
    \<open>x = \<Sum>_v u_v v\<close> (barycentric). Let \<open>W = {v \<in> V : u_v > 0}\<close> (nonempty, subset
    of \<open>V\<close>). Then \<open>x \<in> rel_interior (conv W)\<close> by HOL's
    \<open>rel_interior_convex_hull_explicit\<close>. \<open>conv W\<close> is a face of \<sigma>, hence in \<open>K\<close>
    by face-closure; any \<open>v \<in> W\<close> belongs to both \<open>conv W\<close> and \<open>vertices K\<close>.
    So \<open>x \<in> geotop_open_star K v\<close>. **)
lemma geotop_vertex_stars_cover:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_polyhedron K
           \<subseteq> \<Union>{geotop_open_star K v |v. v \<in> geotop_complex_vertices K}"
proof
  fix x assume hx: "x \<in> geotop_polyhedron K"
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K" and hx\<sigma>: "x \<in> \<sigma>"
    using hx unfolding geotop_polyhedron_def by (by100 blast)
  (** \<sigma> is a simplex with affinely independent vertex set \<open>V\<close>. **)
  have h\<sigma>_simp: "geotop_is_simplex \<sigma>"
    using h\<sigma>K conjunct1[OF hK[unfolded geotop_is_complex_def]] by (by100 blast)
  obtain V m n where hVfin: "finite V" and hVcard: "card V = n+1"
                  and hnm: "n \<le> m" and hVgp: "geotop_general_position V m"
                  and h\<sigma>_hull: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>_simp unfolding geotop_is_simplex_def by (by100 blast)
  have hVsv: "geotop_simplex_vertices \<sigma> V"
    unfolding geotop_simplex_vertices_def
    using hVfin hVcard hnm hVgp h\<sigma>_hull by (by100 blast)
  have h\<sigma>_hullHOL: "\<sigma> = convex hull V"
    using h\<sigma>_hull geotop_convex_hull_eq_HOL by (by100 simp)
  have hV_indep: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF hVsv])
  (** Barycentric expression of x. **)
  have hx_hull: "x \<in> convex hull V" using hx\<sigma> h\<sigma>_hullHOL by (by100 simp)
  obtain u where hu_nn: "\<forall>v\<in>V. 0 \<le> u v"
             and hu_sum: "sum u V = 1"
             and hx_eq: "(\<Sum>v\<in>V. u v *\<^sub>R v) = x"
    using hx_hull hVfin convex_hull_finite[of V] by (by100 blast)
  (** Support \<open>W = {v : u_v > 0}\<close> is nonempty. **)
  define W where "W = {v \<in> V. u v > 0}"
  have hWV: "W \<subseteq> V" unfolding W_def by (by100 blast)
  have hWfin: "finite W"
    unfolding W_def using hVfin finite_subset by (by100 fastforce)
  have hWne: "W \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> W \<noteq> {}"
    then have hWemp: "\<forall>v\<in>V. u v \<le> 0" unfolding W_def by (by100 force)
    have "\<forall>v\<in>V. u v = 0" using hWemp hu_nn by (by100 fastforce)
    then have "sum u V = 0" by (by100 simp)
    thus False using hu_sum by (by100 simp)
  qed
  (** \<open>x = \<Sum>_W u_v v\<close> since \<open>u_v = 0\<close> on \<open>V \<setminus> W\<close>. **)
  have hx_W: "(\<Sum>v\<in>W. u v *\<^sub>R v) = x"
  proof -
    have hzero: "\<forall>v\<in>V - W. u v *\<^sub>R v = 0"
      unfolding W_def using hu_nn by (by100 fastforce)
    have hsum_W: "(\<Sum>v\<in>W. u v *\<^sub>R v) = (\<Sum>v\<in>V. u v *\<^sub>R v)"
      using hVfin hWV hzero sum.mono_neutral_left[of V W "\<lambda>v. u v *\<^sub>R v"]
      by (by100 blast)
    show ?thesis using hsum_W hx_eq by (by100 simp)
  qed
  have hsum_uW: "sum u W = 1"
  proof -
    have hzero_u: "\<forall>v\<in>V - W. u v = 0"
      unfolding W_def using hu_nn by (by100 fastforce)
    have "sum u W = sum u V"
      using hVfin hWV hzero_u sum.mono_neutral_left[of V W u] by (by100 blast)
    thus ?thesis using hu_sum by (by100 simp)
  qed
  have hu_pos_W: "\<forall>v\<in>W. 0 < u v" unfolding W_def by (by100 simp)
  (** \<open>W\<close> is affinely independent (subset of \<open>V\<close> which is). **)
  have hW_indep: "\<not> affine_dependent W"
    using hV_indep hWV affine_dependent_subset by (by100 blast)
  (** \<open>x \<in> rel_interior(conv W)\<close>. **)
  have hx_rel_int: "x \<in> rel_interior (convex hull W)"
    using hW_indep hu_pos_W hsum_uW hx_W
    unfolding rel_interior_convex_hull_explicit[OF hW_indep]
    by (by100 blast)
  (** \<open>conv W\<close> is a face of \<sigma>, so in \<open>K\<close>. **)
  define \<tau> where "\<tau> = convex hull W"
  have h\<tau>_face: "geotop_is_face \<tau> \<sigma>"
    unfolding geotop_is_face_def \<tau>_def
    apply (rule exI[of _ V])
    apply (rule exI[of _ W])
    using hVsv hWne hWV geotop_convex_hull_eq_HOL[of W] by (by100 simp)
  have hK_fc: "\<forall>\<sigma>'\<in>K. \<forall>\<tau>'. geotop_is_face \<tau>' \<sigma>' \<longrightarrow> \<tau>' \<in> K"
    using conjunct1[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]]
    by (by100 blast)
  have h\<tau>K: "\<tau> \<in> K" using hK_fc h\<sigma>K h\<tau>_face by (by100 blast)
  (** Pick any \<open>v \<in> W\<close>. Then \<open>v \<in> \<tau>\<close> and \<open>v \<in> vertices K\<close>. **)
  obtain v where hvW: "v \<in> W" using hWne by (by100 blast)
  have hvV: "v \<in> V" using hvW hWV by (by100 blast)
  have hv_vertices: "v \<in> geotop_complex_vertices K"
    unfolding geotop_complex_vertices_def using h\<sigma>K hVsv hvV by (by100 blast)
  have hv_\<tau>: "v \<in> \<tau>"
    unfolding \<tau>_def using hvW hull_inc[of v W] by (by100 simp)
  (** \<open>x \<in> rel_interior \<tau>\<close> and \<open>v \<in> \<tau>\<close> with \<open>\<tau> \<in> K\<close>, so \<open>x \<in> st_K(v)\<close>. **)
  have hx_rel_\<tau>: "x \<in> rel_interior \<tau>"
    unfolding \<tau>_def using hx_rel_int by (by100 simp)
  have hx_st: "x \<in> geotop_open_star K v"
    unfolding geotop_open_star_def
    using h\<tau>K hv_\<tau> hx_rel_\<tau> by (by100 blast)
  show "x \<in> \<Union>{geotop_open_star K v |v. v \<in> geotop_complex_vertices K}"
    using hv_vertices hx_st by (by100 blast)
qed

lemma geotop_simplex_dim_unique:
  fixes \<sigma> :: "'a::euclidean_space set"
  assumes h1: "geotop_simplex_dim \<sigma> k1"
  assumes h2: "geotop_simplex_dim \<sigma> k2"
  shows "k1 = k2"
proof -
  obtain V1 m1 where hV1fin: "finite V1" and hV1card: "card V1 = k1 + 1"
                  and hV1eq: "\<sigma> = geotop_convex_hull V1"
                  and hV1gp: "geotop_general_position V1 m1"
                  and hV1m: "k1 \<le> m1"
    using h1 unfolding geotop_simplex_dim_def by (by100 blast)
  obtain V2 m2 where hV2fin: "finite V2" and hV2card: "card V2 = k2 + 1"
                  and hV2eq: "\<sigma> = geotop_convex_hull V2"
                  and hV2gp: "geotop_general_position V2 m2"
                  and hV2m: "k2 \<le> m2"
    using h2 unfolding geotop_simplex_dim_def by (by100 blast)
  have hV1_sv: "geotop_simplex_vertices \<sigma> V1"
    unfolding geotop_simplex_vertices_def
    using hV1fin hV1card hV1eq hV1gp hV1m by (by100 blast)
  have hV2_sv: "geotop_simplex_vertices \<sigma> V2"
    unfolding geotop_simplex_vertices_def
    using hV2fin hV2card hV2eq hV2gp hV2m by (by100 blast)
  have hV_eq: "V1 = V2" by (rule geotop_simplex_vertices_unique[OF hV1_sv hV2_sv])
  show "k1 = k2" using hV1card hV2card hV_eq by (by100 simp)
qed

lemma geotop_simplex_dim_set_finite:
  fixes \<sigma> :: "'a::euclidean_space set"
  shows "finite {k::nat. geotop_simplex_dim \<sigma> k}"
proof (cases "\<exists>k. geotop_simplex_dim \<sigma> k")
  case False
  then have "{k::nat. geotop_simplex_dim \<sigma> k} = {}" by (by100 blast)
  thus ?thesis by (by100 simp)
next
  case True
  then obtain k0 where hk0: "geotop_simplex_dim \<sigma> k0" by (by100 blast)
  have h_sub: "{k::nat. geotop_simplex_dim \<sigma> k} \<subseteq> {k0}"
    using hk0 geotop_simplex_dim_unique by (by100 blast)
  have h_sing_fin: "finite ({k0}::nat set)" by (by100 simp)
  show ?thesis by (rule finite_subset[OF h_sub h_sing_fin])
qed

(** Local duplicate of simplex compactness (used here before its full declaration
    at ~line 6031). **)
lemma geotop_is_simplex_compact_early:
  fixes \<sigma> :: "'a::real_normed_vector set"
  assumes "geotop_is_simplex \<sigma>"
  shows "compact \<sigma>"
proof -
  obtain V m n where hV: "finite V" and h\<sigma>: "\<sigma> = geotop_convex_hull V"
    using assms unfolding geotop_is_simplex_def by (by100 blast)
  have "\<sigma> = convex hull V" using h\<sigma> geotop_convex_hull_eq_HOL by (by100 simp)
  thus ?thesis using hV finite_imp_compact_convex_hull by (by100 simp)
qed

(** Bounded case of diameter_norm_nonneg (suffices for finite complexes). **)
lemma geotop_diameter_norm_nonneg_bdd:
  fixes M :: "'a::real_normed_vector set"
  assumes hne: "M \<noteq> {}"
  assumes hbdd: "bdd_above ((\<lambda>P. (SUP Q\<in>M. norm (P - Q))) ` M)"
  assumes hbdd_inner: "\<And>P. P \<in> M \<Longrightarrow> bdd_above ((\<lambda>Q. norm (P - Q)) ` M)"
  shows "0 \<le> geotop_diameter (\<lambda>x y. norm (x - y)) M"
proof -
  obtain P0 where hP0: "P0 \<in> M" using hne by (by100 blast)
  have h_inner_ge_0: "0 \<le> (SUP Q\<in>M. norm (P0 - Q))"
  proof -
    have h_zero: "norm (P0 - P0) = 0" by (by100 simp)
    have h_upper: "norm (P0 - P0) \<le> (SUP Q\<in>M. norm (P0 - Q))"
      using cSUP_upper[OF hP0 hbdd_inner[OF hP0]] by (by100 simp)
    show ?thesis using h_zero h_upper by (by100 simp)
  qed
  have h_outer: "(SUP Q\<in>M. norm (P0 - Q)) \<le> (SUP P\<in>M. (SUP Q\<in>M. norm (P - Q)))"
    using cSUP_upper[OF hP0 hbdd] by (by100 simp)
  have h_ge_0: "0 \<le> (SUP P\<in>M. (SUP Q\<in>M. norm (P - Q)))"
    using h_inner_ge_0 h_outer by (by100 simp)
  thus ?thesis unfolding geotop_diameter_def using hne by (by100 simp)
qed

(** Note: the unrestricted diameter_norm_nonneg is not provable without
    additional hypothesis (unbounded M case can give arbitrary cSup).
    Use geotop_diameter_norm_nonneg_bdd above for bounded M. **)

(** Diameter of a simplex is nonneg via compactness (bounded argument). **)
lemma geotop_simplex_diameter_nonneg:
  fixes \<sigma> :: "'a::real_normed_vector set"
  assumes h\<sigma>_sim: "geotop_is_simplex \<sigma>"
  shows "0 \<le> geotop_diameter (\<lambda>x y. norm (x - y)) \<sigma>"
proof -
  have h\<sigma>_compact: "compact \<sigma>" by (rule geotop_is_simplex_compact_early[OF h\<sigma>_sim])
  have h\<sigma>_bdd: "bounded \<sigma>" using h\<sigma>_compact compact_imp_bounded by (by100 blast)
  have h\<sigma>_ne: "\<sigma> \<noteq> {}"
  proof -
    obtain V m n where hVfin: "finite V" and hVcard: "card V = n + 1"
                   and h\<sigma>eq: "\<sigma> = geotop_convex_hull V"
      using h\<sigma>_sim unfolding geotop_is_simplex_def by (by100 blast)
    have hVne: "V \<noteq> {}" using hVcard by (by100 auto)
    have h_HOL: "\<sigma> = convex hull V" using h\<sigma>eq geotop_convex_hull_eq_HOL by (by100 simp)
    have "V \<subseteq> \<sigma>" using h_HOL hull_subset by (by100 simp)
    thus ?thesis using hVne by (by100 blast)
  qed
  obtain r where hr: "\<forall>x\<in>\<sigma>. norm x \<le> r" using h\<sigma>_bdd bounded_iff by (by100 blast)
  have h_tri_sigma: "\<And>P Q. P \<in> \<sigma> \<Longrightarrow> Q \<in> \<sigma> \<Longrightarrow> norm (P - Q) \<le> 2 * r"
  proof -
    fix P Q assume hP: "P \<in> \<sigma>" and hQ: "Q \<in> \<sigma>"
    have hnP: "norm P \<le> r" using hP hr by (by100 blast)
    have hnQ: "norm Q \<le> r" using hQ hr by (by100 blast)
    have h_tri: "norm (P - Q) \<le> norm P + norm Q" by (rule norm_triangle_ineq4)
    show "norm (P - Q) \<le> 2 * r" using h_tri hnP hnQ by (by100 simp)
  qed
  have h_bdd_inner: "\<And>P. P \<in> \<sigma> \<Longrightarrow> bdd_above ((\<lambda>Q. norm (P - Q)) ` \<sigma>)"
    unfolding bdd_above_def using h_tri_sigma by (by100 blast)
  have h_bdd_outer: "bdd_above ((\<lambda>P. (SUP Q\<in>\<sigma>. norm (P - Q))) ` \<sigma>)"
  proof -
    have h_each: "\<And>P. P \<in> \<sigma> \<Longrightarrow> (SUP Q\<in>\<sigma>. norm (P - Q)) \<le> 2 * r"
    proof -
      fix P assume hP: "P \<in> \<sigma>"
      have h_bound: "\<And>Q. Q \<in> \<sigma> \<Longrightarrow> norm (P - Q) \<le> 2 * r"
        using h_tri_sigma hP by (by100 blast)
      show "(SUP Q\<in>\<sigma>. norm (P - Q)) \<le> 2 * r"
        by (rule cSUP_least[OF h\<sigma>_ne h_bound])
    qed
    show ?thesis unfolding bdd_above_def using h_each by (by100 blast)
  qed
  show ?thesis
    by (rule geotop_diameter_norm_nonneg_bdd[OF h\<sigma>_ne h_bdd_outer h_bdd_inner])
qed

lemma geotop_mesh_norm_nonneg:
  fixes G :: "'a::real_normed_vector set set"
  assumes hGfin: "finite G"
  assumes h_diam_nn: "\<forall>g\<in>G. 0 \<le> geotop_diameter (\<lambda>x y. norm (x - y)) g"
  shows "0 \<le> geotop_mesh (\<lambda>x y. norm (x - y)) G"
proof (cases "G = {}")
  case True
  then show ?thesis unfolding geotop_mesh_def by (by100 simp)
next
  case False
  then obtain g0 where hg0: "g0 \<in> G" by (by100 blast)
  have h_bdd: "bdd_above ((\<lambda>g. geotop_diameter (\<lambda>x y. norm (x - y)) g) ` G)"
    using hGfin by (by100 simp)
  have h_lb: "geotop_diameter (\<lambda>x y. norm (x - y)) g0
              \<le> (SUP g\<in>G. geotop_diameter (\<lambda>x y. norm (x - y)) g)"
    by (rule cSUP_upper[OF hg0 h_bdd])
  have h_diam_g0: "0 \<le> geotop_diameter (\<lambda>x y. norm (x - y)) g0"
    using h_diam_nn hg0 by (by100 blast)
  have "0 \<le> (SUP g\<in>G. geotop_diameter (\<lambda>x y. norm (x - y)) g)"
    using h_diam_g0 h_lb by (by100 simp)
  thus ?thesis unfolding geotop_mesh_def using False by (by100 simp)
qed
(** Finiteness transfers across subdivision: if \<open>K\<close> is a finite complex and
    \<open>K' < K\<close>, then \<open>K'\<close> is finite. The proof uses \<open>K.3\<close> local-finiteness of
    \<open>K'\<close> + compactness of each \<open>\<sigma> \<in> K\<close> (implicit in simplex being a compact
    convex hull) to conclude that only finitely many simplexes of \<open>K'\<close> meet
    each \<open>\<sigma> \<in> K\<close>; finite \<open>K\<close> then gives finite \<open>K'\<close>. **)
lemma geotop_subdivision_of_finite_is_finite:
  fixes K K' :: "'a::real_normed_vector set set"
  assumes hKfin: "finite K"
  assumes hK'K: "geotop_is_subdivision K' K"
  shows "finite K'"
proof -
  have hKcomp: "geotop_is_complex K"
    using hK'K unfolding geotop_is_subdivision_def by (by100 blast)
  have hK'comp: "geotop_is_complex K'"
    using hK'K unfolding geotop_is_subdivision_def by (by100 blast)
  have hpolyeq: "geotop_polyhedron K' = geotop_polyhedron K"
    using hK'K unfolding geotop_is_subdivision_def by (by100 blast)
  (** |K| is compact: finite union of simplexes, each compact. **)
  have hK_simp: "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
    using conjunct1[OF hKcomp[unfolded geotop_is_complex_def]] by (by100 blast)
  have hK_comp_all: "\<forall>\<sigma>\<in>K. compact \<sigma>"
  proof
    fix \<sigma> assume h\<sigma>K: "\<sigma> \<in> K"
    have h\<sigma>_simp: "geotop_is_simplex \<sigma>" using h\<sigma>K hK_simp by (by100 blast)
    obtain V where hV_fin: "finite V" and h\<sigma>_hull: "\<sigma> = geotop_convex_hull V"
      using h\<sigma>_simp unfolding geotop_is_simplex_def by (by100 blast)
    have h\<sigma>_hullHOL: "\<sigma> = convex hull V"
      using h\<sigma>_hull geotop_convex_hull_eq_HOL by (by100 simp)
    show "compact \<sigma>"
      using h\<sigma>_hullHOL hV_fin finite_imp_compact_convex_hull by (by100 simp)
  qed
  have hK_poly_comp: "compact (geotop_polyhedron K)"
    unfolding geotop_polyhedron_def using hKfin hK_comp_all by (by100 blast)
  have hK'_poly_comp: "compact (geotop_polyhedron K')"
    using hK_poly_comp hpolyeq by (by100 simp)
  (** K.3 for K': each \<tau> \<in> K' has an open nbhd with finitely many K' simplexes. **)
  have hK'_locfin: "\<forall>\<tau>\<in>K'. \<exists>U. open U \<and> \<tau> \<subseteq> U \<and> finite {\<tau>'\<in>K'. \<tau>' \<inter> U \<noteq> {}}"
    using hK'comp unfolding geotop_is_complex_def by (by100 blast)
  (** For each \<tau> \<in> K' pick such a \<open>U_\<tau>\<close>. Use \<open>Axiom of Choice\<close> / \<open>SOME\<close> via
      obtain. **)
  define Uf :: "'a set \<Rightarrow> 'a set" where
    "Uf \<tau> = (SOME U. open U \<and> \<tau> \<subseteq> U \<and> finite {\<tau>'\<in>K'. \<tau>' \<inter> U \<noteq> {}})" for \<tau>
  have hUf_spec: "\<forall>\<tau>\<in>K'. open (Uf \<tau>) \<and> \<tau> \<subseteq> Uf \<tau>
                          \<and> finite {\<tau>'\<in>K'. \<tau>' \<inter> Uf \<tau> \<noteq> {}}"
  proof
    fix \<tau> assume h\<tau>K': "\<tau> \<in> K'"
    have hex: "\<exists>U. open U \<and> \<tau> \<subseteq> U \<and> finite {\<tau>'\<in>K'. \<tau>' \<inter> U \<noteq> {}}"
      using hK'_locfin h\<tau>K' by (by100 blast)
    show "open (Uf \<tau>) \<and> \<tau> \<subseteq> Uf \<tau> \<and> finite {\<tau>'\<in>K'. \<tau>' \<inter> Uf \<tau> \<noteq> {}}"
      unfolding Uf_def using someI_ex[OF hex] by (by100 blast)
  qed
  (** The U_\<tau>'s cover |K'|: any point is in some simplex \<tau> \<in> K', which sits in U_\<tau>. **)
  have hcover: "geotop_polyhedron K' \<subseteq> (\<Union>\<tau>\<in>K'. Uf \<tau>)"
  proof
    fix x assume hx: "x \<in> geotop_polyhedron K'"
    obtain \<tau> where h\<tau>K': "\<tau> \<in> K'" and hx\<tau>: "x \<in> \<tau>"
      using hx unfolding geotop_polyhedron_def by (by100 blast)
    have hx_Uf: "x \<in> Uf \<tau>" using hx\<tau> h\<tau>K' hUf_spec by (by100 blast)
    show "x \<in> (\<Union>\<tau>\<in>K'. Uf \<tau>)" using h\<tau>K' hx_Uf by (by100 blast)
  qed
  (** By compactness, finite subcover. **)
  have hUf_open_img: "\<forall>B\<in>Uf ` K'. open B"
    using hUf_spec by (by100 blast)
  have hcover_img: "geotop_polyhedron K' \<subseteq> \<Union>(Uf ` K')"
    using hcover by (by100 blast)
  have hcover_fin: "\<exists>\<T>'\<subseteq>Uf ` K'. finite \<T>' \<and> geotop_polyhedron K' \<subseteq> \<Union>\<T>'"
  proof (rule compactE[OF hK'_poly_comp hcover_img])
    fix B assume "B \<in> Uf ` K'"
    thus "open B" using hUf_open_img by (by100 blast)
  next
    fix \<T>' assume "\<T>' \<subseteq> Uf ` K'" "finite \<T>'" "geotop_polyhedron K' \<subseteq> \<Union>\<T>'"
    thus "\<exists>\<T>'\<subseteq>Uf ` K'. finite \<T>' \<and> geotop_polyhedron K' \<subseteq> \<Union>\<T>'"
      by (by100 blast)
  qed
  obtain \<T>' where h\<T>'_sub: "\<T>' \<subseteq> Uf ` K'" and h\<T>'fin: "finite \<T>'"
              and h\<T>'_cover: "geotop_polyhedron K' \<subseteq> \<Union>\<T>'"
    using hcover_fin by (by100 blast)
  (** Each element of \<T>' is \<open>Uf \<tau>\<close> for some \<tau> \<in> K'. Pick such \<tau>'s. **)
  define S where "S = (\<lambda>B. SOME \<tau>. \<tau> \<in> K' \<and> B = Uf \<tau>) ` \<T>'"
  have hSfin: "finite S" unfolding S_def using h\<T>'fin by (by100 blast)
  have hS_sub: "S \<subseteq> K'"
  proof
    fix \<tau> assume h\<tau>S: "\<tau> \<in> S"
    then obtain B where hBT: "B \<in> \<T>'"
      and h\<tau>_some: "\<tau> = (SOME \<tau>'. \<tau>' \<in> K' \<and> B = Uf \<tau>')"
      unfolding S_def by (by100 blast)
    have hB_img: "B \<in> Uf ` K'" using hBT h\<T>'_sub by (by100 blast)
    have hex_some: "\<exists>\<tau>'. \<tau>' \<in> K' \<and> B = Uf \<tau>'" using hB_img by (by100 blast)
    show "\<tau> \<in> K'" using h\<tau>_some someI_ex[OF hex_some] by (by100 blast)
  qed
  have hS_cover: "geotop_polyhedron K' \<subseteq> (\<Union>\<tau>\<in>S. Uf \<tau>)"
  proof
    fix x assume hx: "x \<in> geotop_polyhedron K'"
    obtain B where hBT: "B \<in> \<T>'" and hxB: "x \<in> B"
      using hx h\<T>'_cover by (by100 blast)
    have hB_img: "B \<in> Uf ` K'" using hBT h\<T>'_sub by (by100 blast)
    have hex_some: "\<exists>\<tau>'. \<tau>' \<in> K' \<and> B = Uf \<tau>'" using hB_img by (by100 blast)
    define \<tau> where "\<tau> = (SOME \<tau>'. \<tau>' \<in> K' \<and> B = Uf \<tau>')"
    have h\<tau>_props: "\<tau> \<in> K' \<and> B = Uf \<tau>"
      unfolding \<tau>_def using someI_ex[OF hex_some] by (by100 blast)
    have h\<tau>S: "\<tau> \<in> S" unfolding S_def using hBT \<tau>_def by (by100 blast)
    show "x \<in> (\<Union>\<tau>\<in>S. Uf \<tau>)" using h\<tau>S h\<tau>_props hxB by (by100 blast)
  qed
  (** Every \<tau>' \<in> K' is contained in |K'|, so meets some Uf \<tau> with \<tau> \<in> S. **)
  have h\<tau>'_S: "\<forall>\<tau>'\<in>K'. \<exists>\<tau>\<in>S. \<tau>' \<inter> Uf \<tau> \<noteq> {}"
  proof
    fix \<tau>' assume h\<tau>'K': "\<tau>' \<in> K'"
    have hK'_simp_all: "\<forall>\<sigma>\<in>K'. geotop_is_simplex \<sigma>"
      using conjunct1[OF hK'comp[unfolded geotop_is_complex_def]] by (by100 blast)
    have h\<tau>'_simp: "geotop_is_simplex \<tau>'"
      using h\<tau>'K' hK'_simp_all by (by100 blast)
    (** Simplex nonempty: \<open>\<sigma> = conv V\<close> with \<open>card V \<ge> 1\<close>, hence \<open>V \<noteq> {}\<close>. **)
    have h\<tau>'ne: "\<tau>' \<noteq> {}"
    proof -
      obtain V m n where hV_fin: "finite V" and hVcard: "card V = n + 1"
                  and h\<tau>'_hull: "\<tau>' = geotop_convex_hull V"
        using h\<tau>'_simp unfolding geotop_is_simplex_def by (by100 blast)
      have hVne: "V \<noteq> {}"
        using hV_fin hVcard card_gt_0_iff by (by100 fastforce)
      obtain v where hv: "v \<in> V" using hVne by (by100 blast)
      have hvhull: "v \<in> convex hull V" using hv hull_inc[of v V] by (by100 simp)
      have h\<tau>'_hullHOL: "\<tau>' = convex hull V"
        using h\<tau>'_hull geotop_convex_hull_eq_HOL by (by100 simp)
      show "\<tau>' \<noteq> {}" using hvhull h\<tau>'_hullHOL by (by100 blast)
    qed
    obtain x where hx\<tau>': "x \<in> \<tau>'" using h\<tau>'ne by (by100 blast)
    have hx_K'poly: "x \<in> geotop_polyhedron K'"
      using h\<tau>'K' hx\<tau>' unfolding geotop_polyhedron_def by (by100 blast)
    obtain \<tau> where h\<tau>S: "\<tau> \<in> S" and hx_Uf\<tau>: "x \<in> Uf \<tau>"
      using hS_cover hx_K'poly by (by100 blast)
    have hmeet: "\<tau>' \<inter> Uf \<tau> \<noteq> {}" using hx\<tau>' hx_Uf\<tau> by (by100 blast)
    show "\<exists>\<tau>\<in>S. \<tau>' \<inter> Uf \<tau> \<noteq> {}" using h\<tau>S hmeet by (by100 blast)
  qed
  (** K' = union over \<tau> \<in> S of {\<tau>'. \<tau>' ∩ Uf \<tau> \<noteq> {}}. **)
  have hK'_sub: "K' \<subseteq> (\<Union>\<tau>\<in>S. {\<tau>'\<in>K'. \<tau>' \<inter> Uf \<tau> \<noteq> {}})"
  proof
    fix \<tau>' assume h\<tau>'K': "\<tau>' \<in> K'"
    have h\<tau>'_meet: "\<exists>\<tau>\<in>S. \<tau>' \<inter> Uf \<tau> \<noteq> {}"
      using h\<tau>'_S h\<tau>'K' by (by100 blast)
    obtain \<tau> where h\<tau>S: "\<tau> \<in> S" and hmeet: "\<tau>' \<inter> Uf \<tau> \<noteq> {}"
      using h\<tau>'_meet by (by100 blast)
    show "\<tau>' \<in> (\<Union>\<tau>\<in>S. {\<tau>'\<in>K'. \<tau>' \<inter> Uf \<tau> \<noteq> {}})"
      using h\<tau>S h\<tau>'K' hmeet by (by100 blast)
  qed
  have hSfin_sub: "finite (\<Union>\<tau>\<in>S. {\<tau>'\<in>K'. \<tau>' \<inter> Uf \<tau> \<noteq> {}})"
  proof (rule finite_UN_I[OF hSfin])
    fix \<tau> assume h\<tau>S: "\<tau> \<in> S"
    have h\<tau>K': "\<tau> \<in> K'" using h\<tau>S hS_sub by (by100 blast)
    show "finite {\<tau>'\<in>K'. \<tau>' \<inter> Uf \<tau> \<noteq> {}}" using hUf_spec h\<tau>K' by (by100 blast)
  qed
  show "finite K'"
    using hK'_sub hSfin_sub finite_subset by (by100 blast)
qed


(** from early.tex Cor 4.16: for a finite complex, mesh of iterated barycentric
    subdivision tends to 0. Proof via the shrinkage bound
    \<open>mesh(Sd K) \<le> (n/(n+1)) \<cdot> mesh K\<close> (Moise Lemma 4.11) from
    \<open>geotop_Sd_mesh_shrinkage\<close>. **)
lemma geotop_mesh_iterated_Sd_tends_to_zero:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K" and hKfin: "finite K"
  shows "(\<lambda>m. geotop_mesh (\<lambda>x y. norm (x - y))
               (geotop_iterated_Sd m K)) \<longlonglongrightarrow> 0"
proof -
  (** (1) For finite K, there exists a uniform dimension bound \<open>n\<close>.
      Proof: For each \<sigma>, the set of dims \<open>{k. geotop_simplex_dim \<sigma> k}\<close> is a
      finite (in fact, singleton) set of naturals. The union over \<sigma>\<in>K is
      finite since K is finite, so has a max. **)
  have h_dim_bound:
    "\<exists>n::nat. \<forall>\<sigma>\<in>K. \<forall>k. geotop_simplex_dim \<sigma> k \<longrightarrow> k \<le> n"
  proof -
    define D where "D = {k::nat. \<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> k}"
    have hD_sub: "D \<subseteq> (\<Union>\<sigma>\<in>K. {k. geotop_simplex_dim \<sigma> k})"
      unfolding D_def by (by100 blast)
    have h_sigma_fin: "\<And>\<sigma>::'a set. finite {k::nat. geotop_simplex_dim \<sigma> k}"
      by (rule geotop_simplex_dim_set_finite)
    have h_union_fin: "finite (\<Union>\<sigma>\<in>K. {k. geotop_simplex_dim \<sigma> k})"
      using hKfin h_sigma_fin by (by100 blast)
    have hD_fin: "finite D" using hD_sub h_union_fin finite_subset by (by100 blast)
    show ?thesis
    proof (cases "D = {}")
      case True
      then have "\<forall>\<sigma>\<in>K. \<forall>k. geotop_simplex_dim \<sigma> k \<longrightarrow> k \<le> 0"
        unfolding D_def by (by100 blast)
      thus ?thesis by (by100 blast)
    next
      case False
      define n where "n = Max D"
      have hn_ub: "\<forall>k\<in>D. k \<le> n"
        unfolding n_def using hD_fin by (by100 simp)
      have hn_prop: "\<forall>\<sigma>\<in>K. \<forall>k. geotop_simplex_dim \<sigma> k \<longrightarrow> k \<le> n"
      proof (intro ballI allI impI)
        fix \<sigma> assume h\<sigma>: "\<sigma> \<in> K"
        fix k assume hk: "geotop_simplex_dim \<sigma> k"
        have "k \<in> D" unfolding D_def using h\<sigma> hk by (by100 blast)
        thus "k \<le> n" using hn_ub by (by100 blast)
      qed
      thus ?thesis by (by100 blast)
    qed
  qed
  then obtain n where hn: "\<forall>\<sigma>\<in>K. \<forall>k. geotop_simplex_dim \<sigma> k \<longrightarrow> k \<le> n"
    by (by100 blast)
  (** (2) Induction on m: \<open>Sd^m(K)\<close> has the same dim bound, and
      \<open>mesh(Sd^m K) \<le> (n/(n+1))^m \<cdot> mesh K\<close>. **)
  define q where "q = real n / real (Suc n)"
  have h_q_pos: "0 \<le> q" unfolding q_def by (by100 simp)
  have h_q_lt_1: "q < 1" unfolding q_def
    by (by100 simp)
  define M where "M = geotop_mesh (\<lambda>x y. norm (x - y)) K"
  have h_K_simp: "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
    using conjunct1[OF hK[unfolded geotop_is_complex_def]] by (by100 blast)
  have h_K_diam_nn: "\<forall>\<sigma>\<in>K. 0 \<le> geotop_diameter (\<lambda>x y. norm (x - y)) \<sigma>"
    using h_K_simp geotop_simplex_diameter_nonneg by (by100 blast)
  have h_M_nn: "0 \<le> M"
    unfolding M_def by (rule geotop_mesh_norm_nonneg[OF hKfin h_K_diam_nn])
  have h_step: "\<And>m. geotop_is_complex (geotop_iterated_Sd m K)
                    \<and> (\<forall>\<sigma>\<in>geotop_iterated_Sd m K.
                         \<forall>k. geotop_simplex_dim \<sigma> k \<longrightarrow> k \<le> n)
                    \<and> geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd m K)
                      \<le> q^m * M"
  proof -
    fix m
    show "geotop_is_complex (geotop_iterated_Sd m K)
        \<and> (\<forall>\<sigma>\<in>geotop_iterated_Sd m K.
             \<forall>k. geotop_simplex_dim \<sigma> k \<longrightarrow> k \<le> n)
        \<and> geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd m K)
          \<le> q^m * M"
    proof (induct m)
      case 0
      have hSd0_eq: "geotop_iterated_Sd 0 K = K" by (by100 simp)
      have hSd0_comp: "geotop_is_complex (geotop_iterated_Sd 0 K)"
        using hSd0_eq hK by (by100 simp)
      have hSd0_dim: "\<forall>\<sigma>\<in>geotop_iterated_Sd 0 K.
                         \<forall>k. geotop_simplex_dim \<sigma> k \<longrightarrow> k \<le> n"
        using hSd0_eq hn by (by100 simp)
      have hSd0_mesh: "geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd 0 K)
                         \<le> q^0 * M"
        unfolding M_def using hSd0_eq by (by100 simp)
      show ?case using hSd0_comp hSd0_dim hSd0_mesh by (by100 blast)
    next
      case (Suc m)
      (** IH parts. **)
      have hIH_comp: "geotop_is_complex (geotop_iterated_Sd m K)" using Suc by (by100 blast)
      have hIH_dim: "\<forall>\<sigma>\<in>geotop_iterated_Sd m K.
                        \<forall>k. geotop_simplex_dim \<sigma> k \<longrightarrow> k \<le> n"
        using Suc by (by100 blast)
      have hIH_mesh: "geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd m K)
                        \<le> q^m * M"
        using Suc by (by100 blast)
      (** Apply shrinkage. **)
      have h_shr: "(\<forall>\<sigma>'\<in>geotop_Sd (geotop_iterated_Sd m K).
                       \<forall>k. geotop_simplex_dim \<sigma>' k \<longrightarrow> k \<le> n)
                 \<and> geotop_mesh (\<lambda>x y. norm (x - y))
                      (geotop_Sd (geotop_iterated_Sd m K))
                   \<le> (real n / real (Suc n))
                    * geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd m K)"
        by (rule geotop_Sd_mesh_shrinkage[OF hIH_comp hIH_dim])
      have hSuc_eq: "geotop_iterated_Sd (Suc m) K = geotop_Sd (geotop_iterated_Sd m K)"
        by (by100 simp)
      (** Complex from subdivision. **)
      have h_sub: "geotop_is_subdivision (geotop_Sd (geotop_iterated_Sd m K))
                                           (geotop_iterated_Sd m K)"
        by (rule geotop_Sd_is_subdivision[OF hIH_comp])
      have h_Sdm_comp: "geotop_is_complex (geotop_Sd (geotop_iterated_Sd m K))"
        using h_sub unfolding geotop_is_subdivision_def by (by100 blast)
      have hSuc_comp: "geotop_is_complex (geotop_iterated_Sd (Suc m) K)"
        using h_Sdm_comp hSuc_eq by (by100 simp)
      (** Dim bound preserved. **)
      have hSuc_dim: "\<forall>\<sigma>\<in>geotop_iterated_Sd (Suc m) K.
                         \<forall>k. geotop_simplex_dim \<sigma> k \<longrightarrow> k \<le> n"
        using h_shr hSuc_eq by (by100 simp)
      (** Mesh bound. **)
      have h_mesh_Suc: "geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd (Suc m) K)
                          \<le> q * geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd m K)"
        using h_shr hSuc_eq unfolding q_def by (by100 simp)
      have h_mult_ih: "q * geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd m K)
                         \<le> q * (q^m * M)"
        using h_q_pos hIH_mesh mult_left_mono by (by100 blast)
      have h_pow_eq: "q * (q^m * M) = q^(Suc m) * M" by (by100 simp)
      have hSuc_mesh: "geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd (Suc m) K)
                         \<le> q^(Suc m) * M"
        using h_mesh_Suc h_mult_ih h_pow_eq by (by100 simp)
      show ?case using hSuc_comp hSuc_dim hSuc_mesh by (by100 blast)
    qed
  qed
  (** (3) \<open>q^m \<to> 0\<close> since \<open>0 \<le> q < 1\<close>. **)
  have h_qm_lim: "(\<lambda>m. q^m) \<longlonglongrightarrow> 0"
    using LIMSEQ_realpow_zero[of q] h_q_pos h_q_lt_1 by (by100 simp)
  have h_qmM_lim: "(\<lambda>m. q^m * M) \<longlonglongrightarrow> 0"
  proof -
    have h_mult: "(\<lambda>m. q^m * M) \<longlonglongrightarrow> 0 * M"
      using tendsto_mult[OF h_qm_lim tendsto_const[of M sequentially]] by (by100 simp)
    thus ?thesis by (by100 simp)
  qed
  (** (4) Squeeze: mesh is nonneg and \<le> q^m M. **)
  have h_Sdm_sub: "\<And>m. geotop_is_subdivision (geotop_iterated_Sd m K) K"
    by (rule geotop_iterated_Sd_is_subdivision[OF hK])
  have h_Sdm_fin: "\<And>m. finite (geotop_iterated_Sd m K)"
    using geotop_subdivision_of_finite_is_finite[OF hKfin] h_Sdm_sub by (by100 blast)
  have h_Sdm_comp: "\<And>m. geotop_is_complex (geotop_iterated_Sd m K)"
    using h_step by (by100 blast)
  have h_Sdm_simp: "\<And>m. \<forall>\<sigma>\<in>geotop_iterated_Sd m K. geotop_is_simplex \<sigma>"
    using conjunct1[OF h_Sdm_comp[unfolded geotop_is_complex_def]] by (by100 blast)
  have h_Sdm_diam_nn: "\<And>m. \<forall>\<sigma>\<in>geotop_iterated_Sd m K.
                             0 \<le> geotop_diameter (\<lambda>x y. norm (x - y)) \<sigma>"
    using h_Sdm_simp geotop_simplex_diameter_nonneg by (by100 blast)
  have h_mesh_nn: "\<And>m. 0 \<le> geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd m K)"
    by (rule geotop_mesh_norm_nonneg[OF h_Sdm_fin h_Sdm_diam_nn])
  have h_mesh_ub: "\<And>m. geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd m K)
                       \<le> q^m * M"
    using h_step by (by100 blast)
  have h_zero_lim: "(\<lambda>m::nat. 0::real) \<longlonglongrightarrow> 0" by (by100 simp)
  show ?thesis
  proof (rule real_tendsto_sandwich[OF _ _ h_zero_lim h_qmM_lim])
    show "\<forall>\<^sub>F m in sequentially. 0 \<le> geotop_mesh (\<lambda>x y. norm (x - y))
                                       (geotop_iterated_Sd m K)"
      using h_mesh_nn by (by100 simp)
  next
    show "\<forall>\<^sub>F m in sequentially. geotop_mesh (\<lambda>x y. norm (x - y))
                                       (geotop_iterated_Sd m K) \<le> q^m * M"
      using h_mesh_ub by (by100 simp)
  qed
qed


(** For a finite non-empty collection \<open>G\<close>, each member's diameter is bounded
    by the mesh. Direct from the SUP def of \<open>geotop_mesh\<close>. **)
lemma geotop_diameter_le_mesh:
  fixes G :: "'a set set" and d :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes hGfin: "finite G"
  assumes h\<tau>G: "\<tau> \<in> G"
  shows "geotop_diameter d \<tau> \<le> geotop_mesh d G"
proof -
  have hGne: "G \<noteq> {}" using h\<tau>G by (by100 blast)
  have hbdd: "bdd_above ((\<lambda>g. geotop_diameter d g) ` G)"
    using hGfin by (by100 simp)
  have "geotop_diameter d \<tau> \<le> (SUP g\<in>G. geotop_diameter d g)"
    using cSUP_upper[OF h\<tau>G hbdd] by (by100 blast)
  also have "(SUP g\<in>G. geotop_diameter d g) = geotop_mesh d G"
    unfolding geotop_mesh_def using hGne by (by100 simp)
  finally show ?thesis .
qed

(** from early.tex Lemma 4.17 (key refinement lemma): if \<open>K'\<close> is a subdivision
    of \<open>K\<close>, then for some \<open>m\<close>, \<open>Sd^m(K)\<close> is a subdivision of \<open>K'\<close>.
    Proof following early.tex \<S>4.5:
      (a) Finite open cover: vertex-stars \<open>st_{K'}(v)\<close>, \<open>v \<in> K'^0\<close>, cover \<open>|K|\<close>
          (Lemma \<open>geotop_vertex_stars_cover\<close>).
      (b) Compactness + Lebesgue number: pick \<open>\<delta> > 0\<close> such that every subset of
          \<open>|K|\<close> of diameter \<open>< \<delta>\<close> is contained in some \<open>st_{K'}(v)\<close>.
      (c) Mesh shrinkage: pick \<open>m\<close> so that every simplex of \<open>Sd^m(K)\<close> has
          diameter \<open>< \<delta>\<close> (Lemma \<open>geotop_mesh_iterated_Sd_tends_to_zero\<close>).
      (d) Assignment: every \<open>\<tau> \<in> Sd^m(K)\<close> lies in some \<open>st_{K'}(v)\<close>; use interior
          disjointness in \<open>K'\<close> to conclude \<open>\<tau>\<close> is contained in a single simplex
          of \<open>K'\<close>. **)
lemma geotop_iterated_Sd_refines_subdivision:
  fixes K K' :: "'a::euclidean_space set set"
  assumes hK: "finite K"
  assumes hsub: "geotop_is_subdivision K' K"
  shows "\<exists>m. geotop_is_subdivision (geotop_iterated_Sd m K) K'"
proof -
  have hKcomp: "geotop_is_complex K"
    using hsub unfolding geotop_is_subdivision_def by (by100 blast)
  have hK'comp: "geotop_is_complex K'"
    using hsub unfolding geotop_is_subdivision_def by (by100 blast)
  (** (a) Finite vertex-stars of \<open>K'\<close> form an open cover of \<open>|K|\<close>. The underlying
      polyhedra coincide: \<open>|K'| = |K|\<close>. **)
  have hpolyeq: "geotop_polyhedron K' = geotop_polyhedron K"
    using hsub unfolding geotop_is_subdivision_def by (by100 blast)
  have hK'fin: "finite K'"
    by (rule geotop_subdivision_of_finite_is_finite[OF hK hsub])
  (** (b) Lebesgue number \<open>\<delta>\<close> for the vertex-star cover of \<open>|K|\<close>. Needs compactness
      of \<open>|K|\<close> (from finite \<open>K\<close> + each simplex compact) and HOL's compact Lebesgue
      number lemma. Structured decomposition (for euclidean_space narrowing elsewhere): **)
  (** (b.1) |K| is compact (finite union of compact simplexes). Each simplex is a
         convex hull of a finite set, hence compact (via HOL \<open>compact_convex_hull\<close>
         + \<open>finite_imp_compact\<close>; both require euclidean_space). **)
  have hK_simp_compact: "\<forall>\<sigma>\<in>K. compact \<sigma>"
  proof (rule ballI)
    fix \<sigma> assume h\<sigma>: "\<sigma> \<in> K"
    have hsim_all: "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
      by (rule conjunct1[OF hKcomp[unfolded geotop_is_complex_def]])
    have hsim: "geotop_is_simplex \<sigma>" using hsim_all h\<sigma> by (by100 blast)
    obtain V m n where hVfin: "finite V"
                   and hV_hull: "\<sigma> = geotop_convex_hull V"
      using hsim unfolding geotop_is_simplex_def by (by100 blast)
    have hV_HOL: "\<sigma> = convex hull V"
      using hV_hull geotop_convex_hull_eq_HOL by (by100 simp)
    have hV_compact: "compact V" using hVfin by (rule finite_imp_compact)
    have h_hull_compact: "compact (convex hull V)"
      by (rule compact_convex_hull[OF hV_compact])
    show "compact \<sigma>" using hV_HOL h_hull_compact by (by100 simp)
  qed
  have hK_compact: "compact (geotop_polyhedron K)"
    unfolding geotop_polyhedron_def
    using hK hK_simp_compact by (by100 blast)
  (** (b.2) Apply HOL's Lebesgue number lemma to |K| + the vertex-star cover to get
          a \<delta>-bound; then tighten 'S in star(v)' to 'S in some \<sigma> \<ni> v'. Structured: **)
  (** (b.2.i) Each vertex star of K' is open in subspace(|K'|) = subspace(|K|),
           via \<open>geotop_open_star_open_in_subspace\<close>. Extract ambient open witness. **)
  have h_stars_subspace_open:
    "\<forall>v\<in>geotop_complex_vertices K'.
       geotop_open_star K' v \<in> subspace_topology UNIV geotop_euclidean_topology
                                 (geotop_polyhedron K')"
    using geotop_open_star_open_in_subspace[OF hK'comp hK'fin] by (by100 blast)
  have h_stars_amb_witness:
    "\<forall>v\<in>geotop_complex_vertices K'. \<exists>U. open U \<and>
       geotop_open_star K' v = geotop_polyhedron K' \<inter> U"
  proof (rule ballI)
    fix v assume hv: "v \<in> geotop_complex_vertices K'"
    have h1: "geotop_open_star K' v
                \<in> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K')"
      using h_stars_subspace_open hv by (by100 blast)
    then obtain U where h_U_in: "U \<in> geotop_euclidean_topology"
                    and h_eq: "geotop_open_star K' v = geotop_polyhedron K' \<inter> U"
      unfolding subspace_topology_def by (by100 blast)
    have h_eq_opens: "geotop_euclidean_topology = {S. open S}"
      unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def by (by100 simp)
    have h_U_in_coll: "U \<in> {S. open S}" using h_U_in h_eq_opens by (by100 blast)
    have h_U_open: "open U" using h_U_in_coll by (by100 blast)
    show "\<exists>U. open U \<and> geotop_open_star K' v = geotop_polyhedron K' \<inter> U"
      using h_U_open h_eq by (by100 blast)
  qed
  (** (b.2.ii) Pick ambient witnesses U_v; \<open>\<Union>{U_v}\<close> is an open cover of |K|. **)
  define U_fn :: "'a \<Rightarrow> 'a set" where
    "U_fn v = (SOME U. open U \<and> geotop_open_star K' v = geotop_polyhedron K' \<inter> U)"
    for v :: 'a
  define C :: "'a set set" where
    "C = U_fn ` geotop_complex_vertices K'"
  have h_U_fn_prop: "\<forall>v\<in>geotop_complex_vertices K'. open (U_fn v) \<and>
                       geotop_open_star K' v = geotop_polyhedron K' \<inter> U_fn v"
  proof (rule ballI)
    fix v assume hv: "v \<in> geotop_complex_vertices K'"
    have h_ex: "\<exists>U. open U \<and> geotop_open_star K' v = geotop_polyhedron K' \<inter> U"
      using h_stars_amb_witness hv by (by100 blast)
    show "open (U_fn v) \<and> geotop_open_star K' v = geotop_polyhedron K' \<inter> U_fn v"
      unfolding U_fn_def using someI_ex[OF h_ex] by (by100 blast)
  qed
  have hC_open: "\<forall>U\<in>C. open U"
    unfolding C_def using h_U_fn_prop by (by100 blast)
  have hC_covers: "geotop_polyhedron K \<subseteq> \<Union>C"
  proof
    fix x assume hx: "x \<in> geotop_polyhedron K"
    have hx_K': "x \<in> geotop_polyhedron K'" using hx hpolyeq by (by100 simp)
    (** x is in some vertex star. **)
    have hcover: "geotop_polyhedron K'
                     \<subseteq> \<Union>{geotop_open_star K' v | v. v \<in> geotop_complex_vertices K'}"
      by (rule geotop_vertex_stars_cover[OF hK'comp])
    have "x \<in> \<Union>{geotop_open_star K' v | v. v \<in> geotop_complex_vertices K'}"
      using hcover hx_K' by (by100 blast)
    then obtain v where hv: "v \<in> geotop_complex_vertices K'"
                    and hx_star: "x \<in> geotop_open_star K' v" by (by100 blast)
    have h_star_eq: "geotop_open_star K' v = geotop_polyhedron K' \<inter> U_fn v"
      using h_U_fn_prop hv by (by100 blast)
    have hx_U: "x \<in> U_fn v" using hx_star h_star_eq by (by100 blast)
    have hU_C: "U_fn v \<in> C" unfolding C_def using hv by (by100 blast)
    show "x \<in> \<Union>C" using hx_U hU_C by (by100 blast)
  qed
  (** (b.2.iii) Apply Lebesgue_number_lemma when C is nonempty; handle empty case
               separately at the obtain below. **)
  have h_leb_raw: "C \<noteq> {} \<Longrightarrow> \<exists>\<delta>::real>0. \<forall>T \<subseteq> geotop_polyhedron K.
                     diameter T < \<delta> \<longrightarrow> (\<exists>B\<in>C. T \<subseteq> B)"
  proof -
    assume hC_ne: "C \<noteq> {}"
    obtain \<delta>' :: real where h\<delta>'pos: "0 < \<delta>'"
       and h\<delta>'prop: "\<And>T. T \<subseteq> geotop_polyhedron K \<Longrightarrow> diameter T < \<delta>'
                             \<Longrightarrow> \<exists>B\<in>C. T \<subseteq> B"
      using Lebesgue_number_lemma[OF hK_compact hC_ne hC_covers] hC_open by (by100 blast)
    show ?thesis
      using h\<delta>'pos h\<delta>'prop by (by100 blast)
  qed
  (** (b.2.iv) Translate: T \<subseteq> U_v \<and> T \<subseteq> |K| \<Longrightarrow> T \<subseteq> star(v) \<subseteq> \<sigma> \<ni> v.
               The last step needs connectedness or interior-disjointness; since we
               apply this to simplexes of Sd^m(K), T is always a simplex (connected,
               closed), hence T \<subseteq> single simplex of K'. **)
  obtain \<delta>::real where h\<delta>pos: "\<delta> > 0"
                    and h\<delta>prop: "\<forall>S \<subseteq> geotop_polyhedron K.
                         geotop_diameter (\<lambda>x y. norm (x - y)) S < \<delta> \<longrightarrow>
                         (\<exists>v\<in>geotop_complex_vertices K'. \<exists>\<sigma>\<in>K'. v \<in> \<sigma> \<and> S \<subseteq> \<sigma>)"
    sorry \<comment> \<open>Combines h_leb_raw + geotop_diameter_eq_HOL_diameter bridge
              + star-to-simplex tightening (simplex case via connectedness).\<close>
  (** (c) Mesh shrinkage: pick \<open>m\<close> so that mesh(\<open>Sd^m(K)\<close>) \<open>< \<delta>\<close>, then bound each
      \<open>\<tau>\<close>'s diameter via \<open>geotop_diameter_le_mesh\<close>. **)
  have hmesh_lim: "(\<lambda>m. geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd m K))
                    \<longlonglongrightarrow> 0"
    by (rule geotop_mesh_iterated_Sd_tends_to_zero[OF hKcomp hK])
  have hm_ex: "\<exists>m::nat. geotop_mesh (\<lambda>x y. norm (x - y))
                           (geotop_iterated_Sd m K) < \<delta>"
  proof -
    have hLIMD: "\<exists>no::nat. \<forall>n\<ge>no. norm (geotop_mesh (\<lambda>x y. norm (x - y))
                                          (geotop_iterated_Sd n K) - 0) < \<delta>"
      using LIMSEQ_D[OF hmesh_lim h\<delta>pos] by (by100 blast)
    obtain N where hN:
      "\<forall>n\<ge>N. norm (geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd n K) - 0) < \<delta>"
      using hLIMD by (by100 blast)
    have hN_N:
      "norm (geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd N K) - 0) < \<delta>"
      using hN by (by100 blast)
    then have hnorm: "\<bar>geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd N K)\<bar>
                       < \<delta>"
      by (by100 simp)
    have "geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd N K) < \<delta>"
      using hnorm by (by100 linarith)
    then show ?thesis by (by100 blast)
  qed
  obtain m where hm_mesh_bd:
    "geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd m K) < \<delta>"
    using hm_ex by (by100 blast)
  have hSd_m_fin: "finite (geotop_iterated_Sd m K)"
    by (rule geotop_subdivision_of_finite_is_finite[OF hK
          geotop_iterated_Sd_is_subdivision[OF hKcomp]])
  have hm_mesh: "\<forall>\<tau>\<in>geotop_iterated_Sd m K.
                   geotop_diameter (\<lambda>x y. norm (x - y)) \<tau> < \<delta>"
  proof
    fix \<tau> assume h\<tau>: "\<tau> \<in> geotop_iterated_Sd m K"
    have h1: "geotop_diameter (\<lambda>x y. norm (x - y)) \<tau>
                \<le> geotop_mesh (\<lambda>x y. norm (x - y)) (geotop_iterated_Sd m K)"
      by (rule geotop_diameter_le_mesh[OF hSd_m_fin h\<tau>])
    from h1 hm_mesh_bd show "geotop_diameter (\<lambda>x y. norm (x - y)) \<tau> < \<delta>"
      by (by100 linarith)
  qed
  (** (d) Every simplex of \<open>Sd^m(K)\<close> is contained in a simplex of \<open>K'\<close>. Combining
      (b) and (c): every \<open>\<tau> \<in> Sd^m(K)\<close> has diameter \<open>< \<delta>\<close>, hence is contained in
      some \<open>\<sigma> \<in> K'\<close> containing a vertex \<open>v\<close> of \<open>K'\<close>. **)
  (** Each \<tau> \<in> Sd^m K has diameter < \<delta> (from (c)) and lies inside |K| (since Sd^m
      refines K, each \<tau> sits inside some \<sigma> \<in> K, hence in |K|). Apply (b). **)
  have hSdm_sub_K: "geotop_is_subdivision (geotop_iterated_Sd m K) K"
    by (rule geotop_iterated_Sd_is_subdivision[OF hKcomp])
  have hSdm_refines_K: "geotop_refines (geotop_iterated_Sd m K) K"
    using hSdm_sub_K unfolding geotop_is_subdivision_def by (by100 blast)
  have hSdm_in_K': "\<forall>\<tau>\<in>geotop_iterated_Sd m K. \<exists>\<sigma>\<in>K'. \<tau> \<subseteq> \<sigma>"
  proof
    fix \<tau> assume h\<tau>: "\<tau> \<in> geotop_iterated_Sd m K"
    (** \<tau> \<subseteq> |K|: \<tau> is refined by some \<sigma> \<in> K. **)
    obtain \<sigma>\<^sub>K where h\<sigma>\<^sub>K: "\<sigma>\<^sub>K \<in> K" and h\<tau>\<sigma>\<^sub>K: "\<tau> \<subseteq> \<sigma>\<^sub>K"
      using h\<tau> hSdm_refines_K unfolding geotop_refines_def by (by100 blast)
    have h\<tau>_sub_K: "\<tau> \<subseteq> geotop_polyhedron K"
      using h\<sigma>\<^sub>K h\<tau>\<sigma>\<^sub>K unfolding geotop_polyhedron_def by (by100 blast)
    have h\<tau>_diam: "geotop_diameter (\<lambda>x y. norm (x - y)) \<tau> < \<delta>"
      using h\<tau> hm_mesh by (by100 blast)
    have hstar: "\<exists>v\<in>geotop_complex_vertices K'. \<exists>\<sigma>\<in>K'. v \<in> \<sigma> \<and> \<tau> \<subseteq> \<sigma>"
      using h\<delta>prop h\<tau>_sub_K h\<tau>_diam by (by100 blast)
    show "\<exists>\<sigma>\<in>K'. \<tau> \<subseteq> \<sigma>" using hstar by (by100 blast)
  qed
  (** (e) Putting it together: \<open>Sd^m(K) < K'\<close>, since it refines \<open>K'\<close> and
      \<open>|Sd^m(K)| = |K| = |K'|\<close>. **)
  have hSdm_comp: "geotop_is_complex (geotop_iterated_Sd m K)"
    using hSdm_sub_K unfolding geotop_is_subdivision_def by (by100 blast)
  have hSdm_poly: "geotop_polyhedron (geotop_iterated_Sd m K) = geotop_polyhedron K'"
    using hSdm_sub_K hsub unfolding geotop_is_subdivision_def by (by100 simp)
  have hSdm_ref: "geotop_refines (geotop_iterated_Sd m K) K'"
    unfolding geotop_refines_def using hSdm_in_K' by (by100 blast)
  have "geotop_is_subdivision (geotop_iterated_Sd m K) K'"
    unfolding geotop_is_subdivision_def
    using hSdm_comp hK'comp hSdm_ref hSdm_poly by (by100 blast)
  then show ?thesis by (by100 blast)
qed

(** from Introduction: Theorem 1 (geotop.tex:172).
    LATEX VERSION: Every two subdivisions of the same complex have a common subdivision.

    FAITHFULNESS FIX: We add the \<open>finite K\<close> assumption. Moise implicitly assumes
    this in his main applications (the argument uses compactness of \<open>|K|\<close> via
    a Lebesgue-number argument on the finite open-star cover of \<open>|K|\<close> by vertex
    stars of a refinement, see early.tex \<S>4.5). A locally-finite generalisation
    requires a separate simplex-by-simplex argument and is left for future work.

    Proof following early.tex Theorem 1 via iterated barycentric subdivision. **)
theorem Theorem_GT_1:
  fixes K L1 L2 :: "'a::euclidean_space set set"
  assumes hKfin: "finite K"
  assumes hL1: "geotop_is_subdivision L1 K"
  assumes hL2: "geotop_is_subdivision L2 K"
  shows "\<exists>L. geotop_is_subdivision L L1 \<and> geotop_is_subdivision L L2"
proof -
  (** (1) K is a complex (from the subdivision hypothesis). **)
  have hK: "geotop_is_complex K"
    using hL1 unfolding geotop_is_subdivision_def by (by100 blast)
  (** (2) By early.tex Lemma 4.17, \<open>Sd^m(K)\<close> eventually refines \<open>L1\<close>, and
         \<open>Sd^n(K)\<close> eventually refines \<open>L2\<close>. **)
  obtain m where hm: "geotop_is_subdivision (geotop_iterated_Sd m K) L1"
    using geotop_iterated_Sd_refines_subdivision[OF hKfin hL1] by (by100 blast)
  obtain n where hn: "geotop_is_subdivision (geotop_iterated_Sd n K) L2"
    using geotop_iterated_Sd_refines_subdivision[OF hKfin hL2] by (by100 blast)
  (** (3) Let \<open>N = max m n\<close>. By monotonicity, \<open>Sd^N(K)\<close> is a subdivision of
         \<open>Sd^m(K)\<close> and of \<open>Sd^n(K)\<close>; by transitivity of subdivision it is a
         subdivision of both \<open>L1\<close> and \<open>L2\<close>. **)
  define N where "N = max m n"
  have hmN: "m \<le> N" unfolding N_def by (by100 simp)
  have hnN: "n \<le> N" unfolding N_def by (by100 simp)
  have hN_ref_m: "geotop_is_subdivision (geotop_iterated_Sd N K) (geotop_iterated_Sd m K)"
    by (rule geotop_iterated_Sd_mono[OF hK hmN])
  have hN_ref_n: "geotop_is_subdivision (geotop_iterated_Sd N K) (geotop_iterated_Sd n K)"
    by (rule geotop_iterated_Sd_mono[OF hK hnN])
  have hN_L1: "geotop_is_subdivision (geotop_iterated_Sd N K) L1"
    by (rule geotop_is_subdivision_trans[OF hm hN_ref_m])
  have hN_L2: "geotop_is_subdivision (geotop_iterated_Sd N K) L2"
    by (rule geotop_is_subdivision_trans[OF hn hN_ref_n])
  (** (4) Witness by \<open>L := Sd^N(K)\<close>. **)
  show ?thesis
    using hN_L1 hN_L2 by (by100 blast)
qed

subsection \<open>Continuous and piecewise linear maps between polyhedra\<close>

(** from Introduction: simplicial mapping between complexes (geotop.tex:176)
    LATEX VERSION: Let K and L be complexes, and let f be a mapping |K| \<rightarrow> |L|. If each mapping
      f|\<sigma> (\<sigma> \<in> K) is simplicial, then f is simplicial. **)
definition geotop_simplicial_map :: "'a::real_normed_vector set set \<Rightarrow> 'b::real_normed_vector set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "geotop_simplicial_map K L f \<longleftrightarrow>
    (\<forall>\<sigma>\<in>K. \<exists>\<tau>\<in>L. (\<forall>x\<in>\<sigma>. f x \<in> \<tau>) \<and> geotop_simplicial_on \<sigma> f \<tau>)"

(** from Introduction: piecewise linear map (geotop.tex:176)
    LATEX VERSION: If there is a subdivision K' of K such that each mapping f|\<sigma> (\<sigma> \<in> K')
      maps \<sigma> linearly into a simplex of L, then f is piecewise linear. **)
definition geotop_PL_map :: "'a::real_normed_vector set set \<Rightarrow> 'b::real_normed_vector set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "geotop_PL_map K L f \<longleftrightarrow>
    (\<exists>K'. geotop_is_subdivision K' K \<and>
      (\<forall>\<sigma>\<in>K'. \<exists>\<tau>\<in>L. (\<forall>x\<in>\<sigma>. f x \<in> \<tau>) \<and> geotop_linear_on \<sigma> f))"

text \<open>PLH = piecewise linear homeomorphism.\<close>
definition geotop_PLH :: "'a::real_normed_vector set set \<Rightarrow> 'b::real_normed_vector set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "geotop_PLH K L f \<longleftrightarrow>
    geotop_PL_map K L f \<and> bij_betw f (geotop_polyhedron K) (geotop_polyhedron L)
    \<and> geotop_PL_map L K (inv_into (geotop_polyhedron K) f)"

subsection \<open>Isomorphism and combinatorial equivalence\<close>

(** from Introduction: isomorphism of complexes (geotop.tex:178)
    LATEX VERSION: Let K and L be complexes, let \<phi> be a bijection K^0 \<leftrightarrow> L^0, and for each
      v \<in> K^0, let v' = \<phi>(v). If v_0 v_1 ... v_n \<in> K, then v_0' v_1' ... v_n' \<in> L,
      and conversely. Then \<phi> is an isomorphism. **)
definition geotop_isomorphism :: "'a::real_normed_vector set set \<Rightarrow> 'b::real_normed_vector set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "geotop_isomorphism K L \<phi> \<longleftrightarrow>
    bij_betw \<phi> (geotop_complex_vertices K) (geotop_complex_vertices L)
    \<and> (\<forall>V. V \<subseteq> geotop_complex_vertices K \<longrightarrow>
         (geotop_convex_hull V \<in> K \<longleftrightarrow> geotop_convex_hull (\<phi> ` V) \<in> L))"

definition geotop_isomorphic :: "'a::real_normed_vector set set \<Rightarrow> 'b::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_isomorphic K L \<longleftrightarrow> (\<exists>\<phi>. geotop_isomorphism K L \<phi>)"

(** from Introduction: combinatorial equivalence (geotop.tex:178)
    LATEX VERSION: If K and L are complexes, and have subdivisions K', L' which are isomorphic,
      then K and L are combinatorially equivalent, written K \<sim>_c L.
    FAITHFULNESS FIX: We restrict to finite complexes (needed for transp via
    Theorem_GT_1 common-subdivision lemma; Moise's book implicitly assumes
    finite complexes throughout). **)
definition geotop_comb_equiv :: "'a::real_normed_vector set set \<Rightarrow> 'b::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_comb_equiv K L \<longleftrightarrow>
    finite K \<and> finite L \<and>
    (\<exists>K' L'. geotop_is_subdivision K' K \<and> geotop_is_subdivision L' L \<and> geotop_isomorphic K' L')"

(** from early.tex Lemma 5 (iso-induces-PLH): every simplicial isomorphism
    \<open>\<phi>: K \<cong> L\<close> induces a PL homeomorphism \<open>|\<phi>|: |K| \<leftrightarrow> |L|\<close>, defined by
    extending barycentrically on each simplex.
    Construction: for \<open>x \<in> \<sigma> = [v\<^sub>0, \<dots>, v\<^sub>n] \<in> K\<close>, write \<open>x = \<Sum> t_i v_i\<close> in
    barycentric coords and set \<open>f(x) = \<Sum> t_i \<phi>(v_i)\<close>.
    Correctness needs:
      (a) Well-definedness on overlaps (barycentric coords match on faces).
      (b) Linearity on each simplex of \<open>K\<close> (so \<open>K\<close> witnesses PL).
      (c) Image of each \<open>\<sigma>\<close> is a simplex of \<open>L\<close> (since \<open>\<phi>(\<sigma>)\<close> is the
          corresponding simplex).
      (d) Bijectivity \<open>|K| \<leftrightarrow> |L|\<close> (from bijectivity of \<open>\<phi>\<close> on vertices
          lifted to polyhedra).
      (e) The inverse is the barycentric extension of \<open>\<phi>\<^sup>-\<^sup>1\<close>, also PL. **)
lemma geotop_isomorphism_induces_PLH:
  fixes K :: "'a::euclidean_space set set"
  fixes L :: "'b::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes hL: "geotop_is_complex L"
  assumes hiso: "geotop_isomorphism K L \<phi>"
  shows "\<exists>f::'a \<Rightarrow> 'b.
            geotop_PLH K L f \<and>
            f ` (geotop_polyhedron K) = geotop_polyhedron L \<and>
            (\<forall>v\<in>geotop_complex_vertices K. f v = \<phi> v) \<and>
            (\<forall>\<sigma>\<in>K. geotop_linear_on \<sigma> f) \<and>
            (\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) f))"
proof -
  (** Unpack the iso. **)
  have hbij\<phi>: "bij_betw \<phi> (geotop_complex_vertices K) (geotop_complex_vertices L)"
    using hiso unfolding geotop_isomorphism_def by (by100 blast)
  have h\<phi>cond: "\<forall>V. V \<subseteq> geotop_complex_vertices K \<longrightarrow>
                  (geotop_convex_hull V \<in> K \<longleftrightarrow> geotop_convex_hull (\<phi> ` V) \<in> L)"
    using hiso unfolding geotop_isomorphism_def by (by100 blast)
  (** STRENGTHENED CONSTRUCTION: define \<open>f\<close> as SOME g satisfying the FULL bundle
      of properties. The additional conjunct
        \<open>\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into |K| g)\<close>
      (inverse linear on each L-simplex) is needed by \<open>geotop_transport_subdivision\<close>
      to avoid the common-refinement loop through Theorem_GT_1. This is the
      symmetric counterpart of \<open>\<forall>\<sigma>\<in>K. linear_on \<sigma> g\<close>, and is provided by
      the classical barycentric extension. **)
  define f :: "'a \<Rightarrow> 'b" where
    "f = (SOME g. (\<forall>v\<in>geotop_complex_vertices K. g v = \<phi> v) \<and>
                   (\<forall>\<sigma>\<in>K. geotop_linear_on \<sigma> g) \<and>
                   (\<forall>\<sigma>\<in>K. \<exists>\<tau>\<in>L. \<forall>x\<in>\<sigma>. g x \<in> \<tau>) \<and>
                   bij_betw g (geotop_polyhedron K) (geotop_polyhedron L) \<and>
                   geotop_PL_map L K (inv_into (geotop_polyhedron K) g) \<and>
                   (\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) g)))"
  (** (1) Existence of such \<open>g\<close> — the classical barycentric-extension construction.
      This is the remaining deep sorry, replacing the earlier five separate ones plus
      the new \<open>inv_into\<close> linearity. **)
  have h_f_exists:
    "\<exists>g::'a\<Rightarrow>'b. (\<forall>v\<in>geotop_complex_vertices K. g v = \<phi> v) \<and>
                  (\<forall>\<sigma>\<in>K. geotop_linear_on \<sigma> g) \<and>
                  (\<forall>\<sigma>\<in>K. \<exists>\<tau>\<in>L. \<forall>x\<in>\<sigma>. g x \<in> \<tau>) \<and>
                  bij_betw g (geotop_polyhedron K) (geotop_polyhedron L) \<and>
                  geotop_PL_map L K (inv_into (geotop_polyhedron K) g) \<and>
                  (\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) g))"
    sorry
  (** (2) Extract all six properties from SOME. **)
  have h_f_prop:
    "(\<forall>v\<in>geotop_complex_vertices K. f v = \<phi> v) \<and>
     (\<forall>\<sigma>\<in>K. geotop_linear_on \<sigma> f) \<and>
     (\<forall>\<sigma>\<in>K. \<exists>\<tau>\<in>L. \<forall>x\<in>\<sigma>. f x \<in> \<tau>) \<and>
     bij_betw f (geotop_polyhedron K) (geotop_polyhedron L) \<and>
     geotop_PL_map L K (inv_into (geotop_polyhedron K) f) \<and>
     (\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) f))"
    unfolding f_def using someI_ex[OF h_f_exists] by (by100 blast)
  (** (3) Project each sub-property. **)
  have hagree: "\<forall>v\<in>geotop_complex_vertices K. f v = \<phi> v"
    using h_f_prop by (by100 blast)
  have hlin: "\<forall>\<sigma>\<in>K. geotop_linear_on \<sigma> f"
    using h_f_prop by (by100 blast)
  have himg: "\<forall>\<sigma>\<in>K. \<exists>\<tau>\<in>L. (\<forall>x\<in>\<sigma>. f x \<in> \<tau>)"
    using h_f_prop by (by100 blast)
  have hbij: "bij_betw f (geotop_polyhedron K) (geotop_polyhedron L)"
    using h_f_prop by (by100 blast)
  have hPL_inv: "geotop_PL_map L K (inv_into (geotop_polyhedron K) f)"
    using h_f_prop by (by100 blast)
  have hinv_lin: "\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) f)"
    using h_f_prop by (by100 blast)
  (** (4) \<open>K\<close> is a subdivision of itself (reflexivity); this gives a PL-map witness. **)
  have hK_sub: "geotop_is_subdivision K K"
    by (rule geotop_is_subdivision_refl[OF hK])
  have hK_lin_img:
    "\<forall>\<sigma>\<in>K. \<exists>\<tau>\<in>L. (\<forall>x\<in>\<sigma>. f x \<in> \<tau>) \<and> geotop_linear_on \<sigma> f"
  proof
    fix \<sigma> assume h\<sigma>: "\<sigma> \<in> K"
    have h\<sigma>img: "\<exists>\<tau>\<in>L. (\<forall>x\<in>\<sigma>. f x \<in> \<tau>)" using himg h\<sigma> by (by100 blast)
    have hlin\<sigma>: "geotop_linear_on \<sigma> f" using hlin h\<sigma> by (by100 blast)
    show "\<exists>\<tau>\<in>L. (\<forall>x\<in>\<sigma>. f x \<in> \<tau>) \<and> geotop_linear_on \<sigma> f"
      using h\<sigma>img hlin\<sigma> by (by100 blast)
  qed
  have hPL: "geotop_PL_map K L f"
    unfolding geotop_PL_map_def
    using hK_sub hK_lin_img by (by100 blast)
  have himg_poly: "f ` (geotop_polyhedron K) = geotop_polyhedron L"
    using hbij unfolding bij_betw_def by (by100 blast)
  have hPLH: "geotop_PLH K L f"
    unfolding geotop_PLH_def using hPL hbij hPL_inv by (by100 blast)
  have h_full: "geotop_PLH K L f \<and>
                f ` (geotop_polyhedron K) = geotop_polyhedron L \<and>
                (\<forall>v\<in>geotop_complex_vertices K. f v = \<phi> v) \<and>
                (\<forall>\<sigma>\<in>K. geotop_linear_on \<sigma> f) \<and>
                (\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) f))"
    using hPLH himg_poly hagree hlin hinv_lin by (by100 blast)
  show ?thesis by (rule exI[where x=f], rule h_full)
qed

(** Strengthened iso induces PLH: also gives simplex-image structure for g_inv. **)
lemma geotop_isomorphic_induces_PLH_strong:
  fixes K :: "'a::euclidean_space set set"
  fixes L :: "'b::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes hL: "geotop_is_complex L"
  assumes hiso: "geotop_isomorphic K L"
  shows "\<exists>f::'a \<Rightarrow> 'b. geotop_PLH K L f
                    \<and> f ` (geotop_polyhedron K) = geotop_polyhedron L
                    \<and> (\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) f))
                    \<and> (\<forall>\<tau>\<in>L. inv_into (geotop_polyhedron K) f ` \<tau> \<in> K)"
proof -
  obtain \<phi> where h\<phi>: "geotop_isomorphism K L \<phi>"
    using hiso unfolding geotop_isomorphic_def by (by100 blast)
  have hex_full: "\<exists>f::'a\<Rightarrow>'b.
        geotop_PLH K L f
         \<and> f ` (geotop_polyhedron K) = geotop_polyhedron L
         \<and> (\<forall>v\<in>geotop_complex_vertices K. f v = \<phi> v)
         \<and> (\<forall>\<sigma>\<in>K. geotop_linear_on \<sigma> f)
         \<and> (\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) f))"
    by (rule geotop_isomorphism_induces_PLH[OF hK hL h\<phi>])
  then obtain f where hf1: "geotop_PLH K L f"
                  and hf2: "f ` (geotop_polyhedron K) = geotop_polyhedron L"
                  and hf3: "\<forall>v\<in>geotop_complex_vertices K. f v = \<phi> v"
                  and hf5: "\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) f)"
    by (by100 meson)
  (** Additional property: f_inv \<tau> \<in> K for each \<tau> \<in> L. **)
  (** Unpack iso def. **)
  have h\<phi>_bij: "bij_betw \<phi> (geotop_complex_vertices K) (geotop_complex_vertices L)"
    using h\<phi> unfolding geotop_isomorphism_def by (by100 blast)
  have h\<phi>_simp: "\<forall>V. V \<subseteq> geotop_complex_vertices K \<longrightarrow>
                     (geotop_convex_hull V \<in> K \<longleftrightarrow> geotop_convex_hull (\<phi> ` V) \<in> L)"
    using h\<phi> unfolding geotop_isomorphism_def by (by100 blast)
  have hf_bij_poly: "bij_betw f (geotop_polyhedron K) (geotop_polyhedron L)"
    using hf1 unfolding geotop_PLH_def by (by100 blast)
  have hf_inv_bij_poly: "bij_betw (inv_into (geotop_polyhedron K) f)
                                     (geotop_polyhedron L) (geotop_polyhedron K)"
    by (rule bij_betw_inv_into[OF hf_bij_poly])
  have hf_inv_inj_L: "inj_on (inv_into (geotop_polyhedron K) f) (geotop_polyhedron L)"
    using hf_inv_bij_poly unfolding bij_betw_def by (by100 blast)
  (** For v \<in> V(L): f_inv v = phi_inv v (where phi_inv = inv_into V(K) phi). **)
  have hVK_sub_polyK: "geotop_complex_vertices K \<subseteq> geotop_polyhedron K"
  proof
    fix v assume hv: "v \<in> geotop_complex_vertices K"
    obtain V' where hV'sv: "\<exists>\<sigma>\<in>K. geotop_simplex_vertices \<sigma> V'" and hvV': "v \<in> V'"
      using hv unfolding geotop_complex_vertices_def by (by100 blast)
    obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K" and h\<sigma>sv: "geotop_simplex_vertices \<sigma> V'"
      using hV'sv by (by100 blast)
    have hV'_sub: "V' \<subseteq> geotop_convex_hull V'"
      unfolding geotop_convex_hull_def hull_def by (by100 blast)
    have h\<sigma>_eq: "\<sigma> = geotop_convex_hull V'"
      using h\<sigma>sv unfolding geotop_simplex_vertices_def by (by100 blast)
    have hv_hull: "v \<in> geotop_convex_hull V'" using hvV' hV'_sub by (by100 blast)
    have hv_\<sigma>: "v \<in> \<sigma>" using hv_hull h\<sigma>_eq by (by100 simp)
    show "v \<in> geotop_polyhedron K"
      unfolding geotop_polyhedron_def using h\<sigma>K hv_\<sigma> by (by100 blast)
  qed
  have h\<phi>_inj: "inj_on \<phi> (geotop_complex_vertices K)"
    using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
  have hf_inj_polyK: "inj_on f (geotop_polyhedron K)"
    using hf_bij_poly unfolding bij_betw_def by (by100 blast)
  have hf_inv_eq_\<phi>_inv: "\<forall>v\<in>geotop_complex_vertices L.
                           inv_into (geotop_polyhedron K) f v
                           = inv_into (geotop_complex_vertices K) \<phi> v"
  proof
    fix v assume hvVL: "v \<in> geotop_complex_vertices L"
    have hv_img: "v \<in> \<phi> ` geotop_complex_vertices K"
      using hvVL h\<phi>_bij unfolding bij_betw_def by (by100 simp)
    obtain u where huVK: "u \<in> geotop_complex_vertices K" and h\<phi>u: "\<phi> u = v"
      using hv_img by (by100 blast)
    have huK: "u \<in> geotop_polyhedron K" using huVK hVK_sub_polyK by (by100 blast)
    have hfu: "f u = v" using hf3 huVK h\<phi>u by (by100 simp)
    have hfi_v: "inv_into (geotop_polyhedron K) f v = u"
      using inv_into_f_f[OF hf_inj_polyK huK] hfu by (by100 simp)
    have h\<phi>i_v: "inv_into (geotop_complex_vertices K) \<phi> v = u"
      using inv_into_f_f[OF h\<phi>_inj huVK] h\<phi>u by (by100 simp)
    show "inv_into (geotop_polyhedron K) f v
           = inv_into (geotop_complex_vertices K) \<phi> v"
      using hfi_v h\<phi>i_v by (by100 simp)
  qed
  have hf_inv_sim: "\<forall>\<tau>\<in>L. inv_into (geotop_polyhedron K) f ` \<tau> \<in> K"
  proof (rule ballI)
    fix \<tau> assume h\<tau>L: "\<tau> \<in> L"
    (** tau is a simplex with vertex set V_tau. **)
    have h\<tau>_sim: "geotop_is_simplex \<tau>"
      using h\<tau>L conjunct1[OF hL[unfolded geotop_is_complex_def]] by (by100 blast)
    obtain V\<tau> where hV\<tau>sv: "geotop_simplex_vertices \<tau> V\<tau>"
      using h\<tau>_sim unfolding geotop_is_simplex_def geotop_simplex_vertices_def
      by (by100 blast)
    have hV\<tau>_ai: "\<not> affine_dependent V\<tau>"
      by (rule geotop_general_position_imp_aff_indep[OF hV\<tau>sv])
    obtain m n where hV\<tau>fin: "finite V\<tau>" and hV\<tau>card: "card V\<tau> = n + 1"
                 and hV\<tau>nm: "n \<le> m" and hV\<tau>gp: "geotop_general_position V\<tau> m"
                 and h\<tau>hull: "\<tau> = geotop_convex_hull V\<tau>"
      using hV\<tau>sv unfolding geotop_simplex_vertices_def by (by100 blast)
    have h\<tau>_HOL: "\<tau> = convex hull V\<tau>"
      using h\<tau>hull geotop_convex_hull_eq_HOL by (by100 simp)
    (** V_tau in V(L). **)
    have hV\<tau>_sub_VL: "V\<tau> \<subseteq> geotop_complex_vertices L"
    proof
      fix v assume hvV\<tau>: "v \<in> V\<tau>"
      show "v \<in> geotop_complex_vertices L"
        unfolding geotop_complex_vertices_def using h\<tau>L hV\<tau>sv hvV\<tau> by (by100 blast)
    qed
    (** f_inv = phi_inv on V_tau. **)
    have hfi_eq_\<phi>i_V\<tau>: "\<forall>v\<in>V\<tau>. inv_into (geotop_polyhedron K) f v
                             = inv_into (geotop_complex_vertices K) \<phi> v"
      using hf_inv_eq_\<phi>_inv hV\<tau>_sub_VL by (by100 blast)
    (** f_inv image on V_tau equals phi_inv image on V_tau. **)
    have hfi_img_V\<tau>: "inv_into (geotop_polyhedron K) f ` V\<tau>
                        = inv_into (geotop_complex_vertices K) \<phi> ` V\<tau>"
      using hfi_eq_\<phi>i_V\<tau> by (by100 force)
    (** phi_inv V_tau subseteq V(K). **)
    have h\<phi>i_V\<tau>_sub_VK: "inv_into (geotop_complex_vertices K) \<phi> ` V\<tau>
                         \<subseteq> geotop_complex_vertices K"
    proof
      fix v assume hv: "v \<in> inv_into (geotop_complex_vertices K) \<phi> ` V\<tau>"
      obtain w where hwV\<tau>: "w \<in> V\<tau>"
                  and hv_eq: "v = inv_into (geotop_complex_vertices K) \<phi> w"
        using hv by (by100 blast)
      have hw_VL: "w \<in> geotop_complex_vertices L" using hwV\<tau> hV\<tau>_sub_VL by (by100 blast)
      have hw_img: "w \<in> \<phi> ` geotop_complex_vertices K"
        using hw_VL h\<phi>_bij unfolding bij_betw_def by (by100 simp)
      have "inv_into (geotop_complex_vertices K) \<phi> w \<in> geotop_complex_vertices K"
        by (rule inv_into_into[OF hw_img])
      thus "v \<in> geotop_complex_vertices K" using hv_eq by (by100 simp)
    qed
    (** Reconstruct: phi applied to phi_inv V_tau = V_tau (bij). **)
    have h\<phi>_\<phi>i_V\<tau>: "\<phi> ` (inv_into (geotop_complex_vertices K) \<phi> ` V\<tau>) = V\<tau>"
    proof (rule set_eqI)
      fix w
      show "(w \<in> \<phi> ` (inv_into (geotop_complex_vertices K) \<phi> ` V\<tau>)) = (w \<in> V\<tau>)"
      proof
        assume "w \<in> \<phi> ` (inv_into (geotop_complex_vertices K) \<phi> ` V\<tau>)"
        then obtain w' where hw'V\<tau>: "w' \<in> V\<tau>"
                          and hw_eq: "w = \<phi> (inv_into (geotop_complex_vertices K) \<phi> w')"
          by (by100 blast)
        have hw'_VL: "w' \<in> geotop_complex_vertices L" using hw'V\<tau> hV\<tau>_sub_VL by (by100 blast)
        have hw'_img: "w' \<in> \<phi> ` geotop_complex_vertices K"
          using hw'_VL h\<phi>_bij unfolding bij_betw_def by (by100 simp)
        have h_round: "\<phi> (inv_into (geotop_complex_vertices K) \<phi> w') = w'"
          by (rule f_inv_into_f[OF hw'_img])
        thus "w \<in> V\<tau>" using hw_eq hw'V\<tau> by (by100 simp)
      next
        assume hwV\<tau>: "w \<in> V\<tau>"
        have hw_VL: "w \<in> geotop_complex_vertices L" using hwV\<tau> hV\<tau>_sub_VL by (by100 blast)
        have hw_img: "w \<in> \<phi> ` geotop_complex_vertices K"
          using hw_VL h\<phi>_bij unfolding bij_betw_def by (by100 simp)
        have h_round: "\<phi> (inv_into (geotop_complex_vertices K) \<phi> w) = w"
          by (rule f_inv_into_f[OF hw_img])
        have "\<phi> (inv_into (geotop_complex_vertices K) \<phi> w)
               \<in> \<phi> ` (inv_into (geotop_complex_vertices K) \<phi> ` V\<tau>)"
          using hwV\<tau> by (by100 blast)
        thus "w \<in> \<phi> ` (inv_into (geotop_complex_vertices K) \<phi> ` V\<tau>)"
          using h_round by (by100 simp)
      qed
    qed
    (** By iso def applied with W = phi_inv V_tau: conv W \<in> K iff conv(phi W) \<in> L.
        phi W = V_tau, conv V_tau = tau \<in> L, so conv W = conv(phi_inv V_tau) \<in> K. **)
    have h_conv_\<phi>i_in_K:
      "geotop_convex_hull (inv_into (geotop_complex_vertices K) \<phi> ` V\<tau>) \<in> K"
    proof -
      have h_iso_at: "geotop_convex_hull (inv_into (geotop_complex_vertices K) \<phi> ` V\<tau>) \<in> K
                       \<longleftrightarrow> geotop_convex_hull (\<phi> ` (inv_into (geotop_complex_vertices K) \<phi> ` V\<tau>)) \<in> L"
        using h\<phi>_simp h\<phi>i_V\<tau>_sub_VK by (by100 blast)
      have h_\<tau>_in_L: "geotop_convex_hull (\<phi> ` (inv_into (geotop_complex_vertices K) \<phi> ` V\<tau>)) \<in> L"
        using h\<phi>_\<phi>i_V\<tau> h\<tau>hull h\<tau>L by (by100 simp)
      show ?thesis using h_iso_at h_\<tau>_in_L by (by100 simp)
    qed
    (** Apply hull_eq to get f_inv tau = conv(f_inv V_tau). **)
    have h\<tau>_sub_polyL: "\<tau> \<subseteq> geotop_polyhedron L"
      unfolding geotop_polyhedron_def using h\<tau>L by (by100 blast)
    have h_inj_\<tau>: "inj_on (inv_into (geotop_polyhedron K) f) \<tau>"
      using hf_inv_inj_L h\<tau>_sub_polyL inj_on_subset by (by100 blast)
    have hV\<tau>_sub_\<tau>: "V\<tau> \<subseteq> \<tau>"
    proof -
      have "V\<tau> \<subseteq> convex hull V\<tau>" by (rule hull_subset)
      thus ?thesis using h\<tau>_HOL by (by100 simp)
    qed
    have h_inj_V\<tau>: "inj_on (inv_into (geotop_polyhedron K) f) V\<tau>"
      using h_inj_\<tau> hV\<tau>_sub_\<tau> inj_on_subset by (by100 blast)
    (** Bary on V_tau via linear_on tau. **)
    have h_lin_\<tau>: "geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) f)"
      using hf5 h\<tau>L by (by100 blast)
    obtain V\<tau>' where hV\<tau>'sv: "geotop_simplex_vertices \<tau> V\<tau>'"
                 and h_prop_lin: "\<forall>\<alpha>. (\<forall>v\<in>V\<tau>'. 0 \<le> \<alpha> v) \<and> sum \<alpha> V\<tau>' = 1 \<longrightarrow>
                                     inv_into (geotop_polyhedron K) f
                                        (\<Sum>v\<in>V\<tau>'. \<alpha> v *\<^sub>R v)
                                     = (\<Sum>v\<in>V\<tau>'. \<alpha> v *\<^sub>R
                                         inv_into (geotop_polyhedron K) f v)"
      using h_lin_\<tau> unfolding geotop_linear_on_def by (by100 blast)
    have hV\<tau>'_eq: "V\<tau>' = V\<tau>" by (rule geotop_simplex_vertices_unique[OF hV\<tau>'sv hV\<tau>sv])
    have h_bary_V\<tau>: "\<And>\<alpha>. (\<forall>v\<in>V\<tau>. 0 \<le> \<alpha> v) \<Longrightarrow> sum \<alpha> V\<tau> = 1 \<Longrightarrow>
                         inv_into (geotop_polyhedron K) f (\<Sum>v\<in>V\<tau>. \<alpha> v *\<^sub>R v)
                         = (\<Sum>v\<in>V\<tau>. \<alpha> v *\<^sub>R inv_into (geotop_polyhedron K) f v)"
      using h_prop_lin hV\<tau>'_eq by (by100 blast)
    have h_hull_eq: "inv_into (geotop_polyhedron K) f ` (convex hull V\<tau>)
                      = convex hull (inv_into (geotop_polyhedron K) f ` V\<tau>)"
      by (rule geotop_bary_lin_inj_image_hull_eq[OF hV\<tau>fin h_inj_V\<tau> h_bary_V\<tau>])
    have h_fi_\<tau>_HOL: "inv_into (geotop_polyhedron K) f ` \<tau>
                      = convex hull (inv_into (geotop_polyhedron K) f ` V\<tau>)"
      using h_hull_eq h\<tau>_HOL by (by100 simp)
    have h_geo_bridge: "geotop_convex_hull (inv_into (geotop_polyhedron K) f ` V\<tau>)
                         = convex hull (inv_into (geotop_polyhedron K) f ` V\<tau>)"
      by (rule geotop_convex_hull_eq_HOL)
    have h_fi_\<tau>_geo: "inv_into (geotop_polyhedron K) f ` \<tau>
                      = geotop_convex_hull (inv_into (geotop_polyhedron K) f ` V\<tau>)"
      using h_fi_\<tau>_HOL h_geo_bridge by (by100 simp)
    (** Combine: f_inv tau = conv(f_inv V_tau) = conv(phi_inv V_tau) \<in> K. **)
    have h_fi_\<tau>_phi: "inv_into (geotop_polyhedron K) f ` \<tau>
                      = geotop_convex_hull (inv_into (geotop_complex_vertices K) \<phi> ` V\<tau>)"
      using h_fi_\<tau>_geo hfi_img_V\<tau> by (by100 simp)
    show "inv_into (geotop_polyhedron K) f ` \<tau> \<in> K"
      using h_fi_\<tau>_phi h_conv_\<phi>i_in_K by (by100 simp)
  qed
  show "\<exists>f::'a \<Rightarrow> 'b. geotop_PLH K L f
                    \<and> f ` (geotop_polyhedron K) = geotop_polyhedron L
                    \<and> (\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) f))
                    \<and> (\<forall>\<tau>\<in>L. inv_into (geotop_polyhedron K) f ` \<tau> \<in> K)"
    by (rule exI[where x=f], intro conjI, rule hf1, rule hf2, rule hf5, rule hf_inv_sim)
qed

(** Corollary: combinatorial equivalence via isomorphic subdivisions gives a
    PLH between the underlying polyhedra. **)
lemma geotop_isomorphic_induces_PLH:
  fixes K :: "'a::euclidean_space set set"
  fixes L :: "'b::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes hL: "geotop_is_complex L"
  assumes hiso: "geotop_isomorphic K L"
  shows "\<exists>f::'a \<Rightarrow> 'b. geotop_PLH K L f
                    \<and> f ` (geotop_polyhedron K) = geotop_polyhedron L
                    \<and> (\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) f))"
proof -
  obtain \<phi> where h\<phi>: "geotop_isomorphism K L \<phi>"
    using hiso unfolding geotop_isomorphic_def by (by100 blast)
  have hex_full: "\<exists>f::'a\<Rightarrow>'b.
        geotop_PLH K L f
         \<and> f ` (geotop_polyhedron K) = geotop_polyhedron L
         \<and> (\<forall>v\<in>geotop_complex_vertices K. f v = \<phi> v)
         \<and> (\<forall>\<sigma>\<in>K. geotop_linear_on \<sigma> f)
         \<and> (\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) f))"
    by (rule geotop_isomorphism_induces_PLH[OF hK hL h\<phi>])
  then obtain f where hf1: "geotop_PLH K L f"
                  and hf2: "f ` (geotop_polyhedron K) = geotop_polyhedron L"
                  and hf5: "\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) f)"
    by (by100 meson)
  have h_out: "geotop_PLH K L f
               \<and> f ` (geotop_polyhedron K) = geotop_polyhedron L
               \<and> (\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) f))"
    using hf1 hf2 hf5 by (by100 blast)
  show ?thesis by (rule exI[where x=f], rule h_out)
qed

(** PL-map lifting across refinement: if \<open>f\<close> is a PL map of \<open>K' \<to> L'\<close> and
    \<open>K' < K\<close>, \<open>L' < L\<close>, then \<open>f\<close> is a PL map of \<open>K \<to> L\<close>.
    Proof: unfold the PL-map witness \<open>K_0 < K'\<close>; by transitivity \<open>K_0 < K\<close>;
    for each simplex \<open>\<sigma> \<in> K_0\<close>, \<open>f(\<sigma>) \<subseteq> \<tau>\<close> for some \<open>\<tau> \<in> L'\<close>, and by refinement
    \<open>\<tau> \<subseteq> \<tilde>\<tau>\<close> for some \<open>\<tilde>\<tau> \<in> L\<close>, giving \<open>f(\<sigma>) \<subseteq> \<tilde>\<tau>\<close>. Linearity carries. **)
lemma geotop_PL_map_lift:
  fixes K :: "'a::real_normed_vector set set"
  fixes L :: "'b::real_normed_vector set set"
  fixes K' :: "'a set set" and L' :: "'b set set" and f :: "'a \<Rightarrow> 'b"
  assumes hK'K: "geotop_is_subdivision K' K"
  assumes hL'L: "geotop_is_subdivision L' L"
  assumes hPL: "geotop_PL_map K' L' f"
  shows "geotop_PL_map K L f"
proof -
  (** (1) Extract a common witness \<open>K\<^sub>0 < K'\<close> on which \<open>f\<close> is linear into \<open>L'\<close>. **)
  obtain K\<^sub>0 where hK\<^sub>0K': "geotop_is_subdivision K\<^sub>0 K'"
               and hK\<^sub>0_lin:
                 "\<forall>\<sigma>\<in>K\<^sub>0. \<exists>\<tau>\<in>L'. (\<forall>x\<in>\<sigma>. f x \<in> \<tau>) \<and> geotop_linear_on \<sigma> f"
    using hPL unfolding geotop_PL_map_def by (by100 blast)
  (** (2) By transitivity of subdivision, \<open>K\<^sub>0 < K\<close>. **)
  have hK\<^sub>0K: "geotop_is_subdivision K\<^sub>0 K"
    by (rule geotop_is_subdivision_trans[OF hK'K hK\<^sub>0K'])
  (** (3) For each \<sigma> \<in> K\<^sub>0, the target simplex in L' lifts to a simplex of L containing it. **)
  have hL'_ref: "geotop_refines L' L"
    using hL'L unfolding geotop_is_subdivision_def by (by100 blast)
  have hK\<^sub>0_lin_L:
    "\<forall>\<sigma>\<in>K\<^sub>0. \<exists>\<tau>\<in>L. (\<forall>x\<in>\<sigma>. f x \<in> \<tau>) \<and> geotop_linear_on \<sigma> f"
  proof
    fix \<sigma> :: "'a set" assume h\<sigma>K\<^sub>0: "\<sigma> \<in> K\<^sub>0"
    have hex: "\<exists>\<tau>\<in>L'. (\<forall>x\<in>\<sigma>. f x \<in> \<tau>) \<and> geotop_linear_on \<sigma> f"
      using hK\<^sub>0_lin h\<sigma>K\<^sub>0 by (by100 blast)
    then obtain \<tau>' where h\<tau>'L': "\<tau>' \<in> L'"
                      and hrange\<tau>': "\<forall>x\<in>\<sigma>. f x \<in> \<tau>'"
                      and hlin: "geotop_linear_on \<sigma> f"
      by (by100 blast)
    obtain \<tau> where h\<tau>L: "\<tau> \<in> L" and h\<tau>'\<tau>: "\<tau>' \<subseteq> \<tau>"
      using hL'_ref h\<tau>'L' unfolding geotop_refines_def by (by100 blast)
    have hrange\<tau>: "\<forall>x\<in>\<sigma>. f x \<in> \<tau>" using hrange\<tau>' h\<tau>'\<tau> by (by100 blast)
    show "\<exists>\<tau>\<in>L. (\<forall>x\<in>\<sigma>. f x \<in> \<tau>) \<and> geotop_linear_on \<sigma> f"
      using h\<tau>L hrange\<tau> hlin by (by100 blast)
  qed
  show ?thesis
    unfolding geotop_PL_map_def
    using hK\<^sub>0K hK\<^sub>0_lin_L by (by100 blast)
qed

(** PLH lifting across refinement: combines \<open>geotop_PL_map_lift\<close> in both
    directions with polyhedron equality to transport \<open>geotop_PLH K' L' f\<close> to
    \<open>geotop_PLH K L f\<close>. **)
lemma geotop_PLH_lift:
  fixes K :: "'a::real_normed_vector set set"
  fixes L :: "'b::real_normed_vector set set"
  fixes K' :: "'a set set" and L' :: "'b set set" and f :: "'a \<Rightarrow> 'b"
  assumes hK'K: "geotop_is_subdivision K' K"
  assumes hL'L: "geotop_is_subdivision L' L"
  assumes hPLH: "geotop_PLH K' L' f"
  shows "geotop_PLH K L f"
proof -
  (** Unfold the three conjuncts of PLH, lift each via \<open>geotop_PL_map_lift\<close>
      and polyhedron equality. **)
  have hPL_fwd: "geotop_PL_map K' L' f"
    using hPLH unfolding geotop_PLH_def by (by100 blast)
  have hbij: "bij_betw f (geotop_polyhedron K') (geotop_polyhedron L')"
    using hPLH unfolding geotop_PLH_def by (by100 blast)
  have hPL_bwd: "geotop_PL_map L' K' (inv_into (geotop_polyhedron K') f)"
    using hPLH unfolding geotop_PLH_def by (by100 blast)
  have hKpoly: "geotop_polyhedron K' = geotop_polyhedron K"
    using hK'K unfolding geotop_is_subdivision_def by (by100 blast)
  have hLpoly: "geotop_polyhedron L' = geotop_polyhedron L"
    using hL'L unfolding geotop_is_subdivision_def by (by100 blast)
  have hPL_fwd': "geotop_PL_map K L f"
    by (rule geotop_PL_map_lift[OF hK'K hL'L hPL_fwd])
  have hbij': "bij_betw f (geotop_polyhedron K) (geotop_polyhedron L)"
    using hbij hKpoly hLpoly by (by100 simp)
  (** For the inverse direction, \<open>inv_into (polyhedron K') f = inv_into (polyhedron K) f\<close>
      since the polyhedra coincide. Then we lift the PL_map across L < L' \<to> K < K'. **)
  have hinv_eq: "inv_into (geotop_polyhedron K') f = inv_into (geotop_polyhedron K) f"
    using hKpoly by (by100 simp)
  have hPL_bwd': "geotop_PL_map L K (inv_into (geotop_polyhedron K) f)"
    using geotop_PL_map_lift[OF hL'L hK'K hPL_bwd] hinv_eq by (by100 simp)
  show ?thesis
    unfolding geotop_PLH_def using hPL_fwd' hbij' hPL_bwd' by (by100 blast)
qed

(** from early.tex Lemma 8.1 (iso-symmetric): the inverse of a simplicial
    isomorphism is a simplicial isomorphism. **)
lemma geotop_isomorphic_sym:
  fixes K :: "'a::real_normed_vector set set" and L :: "'b::real_normed_vector set set"
  assumes hiso: "geotop_isomorphic K L"
  shows "geotop_isomorphic L K"
proof -
  obtain \<phi> where hisoKL: "geotop_isomorphism K L \<phi>"
    using hiso unfolding geotop_isomorphic_def by (by100 blast)
  let ?\<psi> = "inv_into (geotop_complex_vertices K) \<phi>"
  have h\<phi>bij: "bij_betw \<phi> (geotop_complex_vertices K) (geotop_complex_vertices L)"
    using hisoKL unfolding geotop_isomorphism_def by (by100 blast)
  have h\<psi>bij: "bij_betw ?\<psi> (geotop_complex_vertices L) (geotop_complex_vertices K)"
    by (rule bij_betw_inv_into[OF h\<phi>bij])
  have h\<phi>cond: "\<forall>V. V \<subseteq> geotop_complex_vertices K \<longrightarrow>
                  (geotop_convex_hull V \<in> K \<longleftrightarrow> geotop_convex_hull (\<phi> ` V) \<in> L)"
    using hisoKL unfolding geotop_isomorphism_def by (by100 blast)
  have h\<phi>inv_right: "\<forall>w\<in>geotop_complex_vertices L. \<phi> (?\<psi> w) = w"
    using bij_betw_inv_into_right[OF h\<phi>bij] by (by100 blast)
  have h\<psi>cond: "\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
                  (geotop_convex_hull W \<in> L \<longleftrightarrow> geotop_convex_hull (?\<psi> ` W) \<in> K)"
  proof (intro allI impI)
    fix W assume hWL: "W \<subseteq> geotop_complex_vertices L"
    have h\<psi>W: "?\<psi> ` W \<subseteq> geotop_complex_vertices K"
      using h\<psi>bij hWL unfolding bij_betw_def by (by100 blast)
    have h\<phi>\<psi>W: "\<phi> ` (?\<psi> ` W) = W"
    proof (rule set_eqI, rule iffI)
      fix y assume "y \<in> \<phi> ` (?\<psi> ` W)"
      then obtain w where hw: "w \<in> W" and hy: "y = \<phi> (?\<psi> w)"
        by (by100 blast)
      have hwL: "w \<in> geotop_complex_vertices L" using hw hWL by (by100 blast)
      have "\<phi> (?\<psi> w) = w" using h\<phi>inv_right hwL by (by100 blast)
      then show "y \<in> W" using hy hw by (by100 simp)
    next
      fix w assume hwW: "w \<in> W"
      have hwL: "w \<in> geotop_complex_vertices L" using hwW hWL by (by100 blast)
      have h\<phi>\<psi>w: "\<phi> (?\<psi> w) = w" using h\<phi>inv_right hwL by (by100 blast)
      show "w \<in> \<phi> ` (?\<psi> ` W)" using hwW h\<phi>\<psi>w by (by100 force)
    qed
    have "geotop_convex_hull (?\<psi> ` W) \<in> K \<longleftrightarrow> geotop_convex_hull (\<phi> ` (?\<psi> ` W)) \<in> L"
      using h\<phi>cond h\<psi>W by (by100 blast)
    then show "geotop_convex_hull W \<in> L \<longleftrightarrow> geotop_convex_hull (?\<psi> ` W) \<in> K"
      using h\<phi>\<psi>W by (by100 simp)
  qed
  have h\<psi>iso: "geotop_isomorphism L K ?\<psi>"
    unfolding geotop_isomorphism_def using h\<psi>bij h\<psi>cond by (by100 blast)
  show ?thesis
    unfolding geotop_isomorphic_def using h\<psi>iso by (by100 blast)
qed

(** from early.tex Lemma 8.2 (iso-transitive): the composition of two simplicial
    isomorphisms is a simplicial isomorphism. **)
lemma geotop_isomorphic_trans:
  fixes K :: "'a::real_normed_vector set set"
  fixes L :: "'b::real_normed_vector set set"
  fixes M :: "'c::real_normed_vector set set"
  assumes hKL: "geotop_isomorphic K L"
  assumes hLM: "geotop_isomorphic L M"
  shows "geotop_isomorphic K M"
proof -
  obtain \<phi> where h\<phi>: "geotop_isomorphism K L \<phi>"
    using hKL unfolding geotop_isomorphic_def by (by100 blast)
  obtain \<psi> where h\<psi>: "geotop_isomorphism L M \<psi>"
    using hLM unfolding geotop_isomorphic_def by (by100 blast)
  let ?\<chi> = "\<psi> \<circ> \<phi>"
  have h\<phi>bij: "bij_betw \<phi> (geotop_complex_vertices K) (geotop_complex_vertices L)"
    using h\<phi> unfolding geotop_isomorphism_def by (by100 blast)
  have h\<psi>bij: "bij_betw \<psi> (geotop_complex_vertices L) (geotop_complex_vertices M)"
    using h\<psi> unfolding geotop_isomorphism_def by (by100 blast)
  have h\<chi>bij: "bij_betw ?\<chi> (geotop_complex_vertices K) (geotop_complex_vertices M)"
    by (rule bij_betw_trans[OF h\<phi>bij h\<psi>bij])
  have h\<phi>cond: "\<forall>V. V \<subseteq> geotop_complex_vertices K \<longrightarrow>
                  (geotop_convex_hull V \<in> K \<longleftrightarrow> geotop_convex_hull (\<phi> ` V) \<in> L)"
    using h\<phi> unfolding geotop_isomorphism_def by (by100 blast)
  have h\<psi>cond: "\<forall>W. W \<subseteq> geotop_complex_vertices L \<longrightarrow>
                  (geotop_convex_hull W \<in> L \<longleftrightarrow> geotop_convex_hull (\<psi> ` W) \<in> M)"
    using h\<psi> unfolding geotop_isomorphism_def by (by100 blast)
  have h\<chi>cond: "\<forall>V. V \<subseteq> geotop_complex_vertices K \<longrightarrow>
                  (geotop_convex_hull V \<in> K \<longleftrightarrow> geotop_convex_hull (?\<chi> ` V) \<in> M)"
  proof (intro allI impI)
    fix V assume hVK: "V \<subseteq> geotop_complex_vertices K"
    (** \<open>\<phi> ` V \<subseteq> vertices L\<close> because \<open>\<phi>\<close> is a bijection vertices K \<to> vertices L. **)
    have h\<phi>V: "\<phi> ` V \<subseteq> geotop_complex_vertices L"
      using h\<phi>bij hVK unfolding bij_betw_def by (by100 blast)
    have h\<chi>img: "?\<chi> ` V = \<psi> ` (\<phi> ` V)" by (rule image_comp[symmetric])
    have "geotop_convex_hull V \<in> K \<longleftrightarrow> geotop_convex_hull (\<phi> ` V) \<in> L"
      using h\<phi>cond hVK by (by100 blast)
    also have "\<dots> \<longleftrightarrow> geotop_convex_hull (\<psi> ` (\<phi> ` V)) \<in> M"
      using h\<psi>cond h\<phi>V by (by100 blast)
    finally show "geotop_convex_hull V \<in> K \<longleftrightarrow> geotop_convex_hull (?\<chi> ` V) \<in> M"
      using h\<chi>img by (by100 simp)
  qed
  have h\<chi>iso: "geotop_isomorphism K M ?\<chi>"
    unfolding geotop_isomorphism_def using h\<chi>bij h\<chi>cond by (by100 blast)
  show ?thesis
    unfolding geotop_isomorphic_def using h\<chi>iso by (by100 blast)
qed

(** from early.tex Lemma 6 (transport subdivision): given \<open>K \<cong> L\<close> and a subdivision
    \<open>L'\<close> of \<open>L\<close>, there is a subdivision \<open>K'\<close> of \<open>K\<close> with \<open>K' \<cong> L'\<close>.
    Proof idea (early.tex): \<open>\<phi>\<close> induces a PL homeomorphism \<open>|\<phi>|: |K| \<leftrightarrow> |L|\<close>;
    pull back each simplex of \<open>L'\<close> through \<open>|\<phi>|\<^sup>-\<^sup>1\<close> to a simplex in \<open>K\<close>.
    Structure:
      (1) apply \<open>iso_induces_PLH\<close> to \<open>\<phi>\<close> to get PLH \<open>g: |K| \<leftrightarrow> |L|\<close>;
      (2) define \<open>K' = {g\<^sup>-\<^sup>1(\<tau>) : \<tau> \<in> L'}\<close> (plus face-closure);
      (3) check \<open>K'\<close> is a complex (face-closed, intersection-compatible)
          using \<open>g\<^sup>-\<^sup>1\<close> is bijective and linear on simplexes of some subdivision of \<open>L\<close>;
      (4) check \<open>|K'| = g\<^sup>-\<^sup>1(|L'|) = g\<^sup>-\<^sup>1(|L|) = |K|\<close>, so \<open>K' < K\<close>;
      (5) construct vertex iso \<open>K' \<cong> L'\<close> via \<open>\<tau> \<mapsto> g\<^sup>-\<^sup>1(\<tau>)\<close>. **)
lemma geotop_transport_subdivision:
  fixes K :: "'a::euclidean_space set set"
  fixes L :: "'b::euclidean_space set set"
  fixes L' :: "'b set set"
  assumes hKcomp: "geotop_is_complex K"
  assumes hLfin: "finite L"
  assumes hiso: "geotop_isomorphic K L"
  assumes hL'L: "geotop_is_subdivision L' L"
  shows "\<exists>K'::'a set set. geotop_is_subdivision K' K \<and> geotop_isomorphic K' L'"
proof -
  (** (1) Extract the PLH \<open>g: |K| \<leftrightarrow> |L|\<close> induced by \<phi>. Requires \<open>K\<close>, \<open>L\<close> complexes. **)
  have hLcomp: "geotop_is_complex L"
    using hL'L unfolding geotop_is_subdivision_def by (by100 blast)
  have hg_strong_ex:
    "\<exists>g :: 'a \<Rightarrow> 'b. geotop_PLH K L g
                   \<and> g ` (geotop_polyhedron K) = geotop_polyhedron L
                   \<and> (\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) g))
                   \<and> (\<forall>\<tau>\<in>L. inv_into (geotop_polyhedron K) g ` \<tau> \<in> K)"
    by (rule geotop_isomorphic_induces_PLH_strong[OF hKcomp hLcomp hiso])
  define gwit :: "'a \<Rightarrow> 'b" where
    "gwit = (SOME g. geotop_PLH K L g \<and>
                    g ` (geotop_polyhedron K) = geotop_polyhedron L \<and>
                    (\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) g)) \<and>
                    (\<forall>\<tau>\<in>L. inv_into (geotop_polyhedron K) g ` \<tau> \<in> K))"
  have hgwit: "geotop_PLH K L gwit \<and>
               gwit ` (geotop_polyhedron K) = geotop_polyhedron L \<and>
               (\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) gwit)) \<and>
               (\<forall>\<tau>\<in>L. inv_into (geotop_polyhedron K) gwit ` \<tau> \<in> K)"
    unfolding gwit_def using someI_ex[OF hg_strong_ex] by (by100 blast)
  obtain g :: "'a \<Rightarrow> 'b" where hg_all:
    "geotop_PLH K L g \<and> g ` (geotop_polyhedron K) = geotop_polyhedron L \<and>
     (\<forall>\<tau>\<in>L. geotop_linear_on \<tau> (inv_into (geotop_polyhedron K) g)) \<and>
     (\<forall>\<tau>\<in>L. inv_into (geotop_polyhedron K) g ` \<tau> \<in> K)"
    using hgwit by (by100 blast)
  have hg: "geotop_PLH K L g" using hg_all by (by100 blast)
  have hg_img: "g ` (geotop_polyhedron K) = geotop_polyhedron L"
    using hg_all by (by100 blast)
  have hg_inv_lin_L: "\<forall>\<tau>\<in>L. geotop_linear_on \<tau>
                                (inv_into (geotop_polyhedron K) g)"
    using hg_all by (by100 blast)
  have hg_inv_L_sim: "\<forall>\<tau>\<in>L. inv_into (geotop_polyhedron K) g ` \<tau> \<in> K"
    using hg_all by (by100 blast)
  have hg_bij: "bij_betw g (geotop_polyhedron K) (geotop_polyhedron L)"
    using hg unfolding geotop_PLH_def by (by100 blast)
  (** (2) Pull back each simplex of \<open>L'\<close> through \<open>g\<^sup>-\<^sup>1\<close>. **)
  let ?g_inv = "inv_into (geotop_polyhedron K) g"
  define K' :: "'a set set" where "K' = (\<lambda>\<tau>. ?g_inv ` \<tau>) ` L'"
  (** (3) \<open>K'\<close> is a complex: \<open>g\<^sup>-\<^sup>1\<close> is bijective and linear on each simplex
      of a suitable subdivision, so it maps simplexes to simplexes coherently.
      The four complex conditions K.0, K.1, K.2, K.3 decompose as: **)
  have hL'_comp: "geotop_is_complex L'"
    using hL'L unfolding geotop_is_subdivision_def by (by100 blast)
  (** Extract g_inv's PL structure: there is a subdivision \<open>L*\<close> of \<open>L\<close> such that
      \<open>g_inv\<close> is linear on each simplex of \<open>L*\<close>. **)
  have hg_inv_PL: "geotop_PL_map L K ?g_inv"
    using hg unfolding geotop_PLH_def by (by100 blast)
  obtain L_star where hL_star_sub: "geotop_is_subdivision L_star L"
                  and hL_star_lin: "\<forall>\<tau>\<in>L_star. \<exists>\<sigma>\<in>K.
                                       (\<forall>x\<in>\<tau>. ?g_inv x \<in> \<sigma>)
                                       \<and> geotop_linear_on \<tau> ?g_inv"
    using hg_inv_PL unfolding geotop_PL_map_def by (by100 blast)
  (** \<open>g_inv\<close> is injective on \<open>|L|\<close> since \<open>g\<close> is bijective. **)
  have hg_inv_bij: "bij_betw ?g_inv (geotop_polyhedron L) (geotop_polyhedron K)"
    by (rule bij_betw_inv_into[OF hg_bij])
  have hg_inv_inj: "inj_on ?g_inv (geotop_polyhedron L)"
    using hg_inv_bij unfolding bij_betw_def by (by100 blast)
  (** (3a) K.0: every \<sigma> \<in> K' is a simplex. \<sigma> = g_inv(\<tau>) for some \<tau> \<in> L'.
      Strategy: common refinement of L' and L_star; in the common refinement
      each \<tau>' \<subseteq> \<tau> has g_inv linear + inj, so g_inv(\<tau>') is a simplex by
      geotop_linear_inj_image_is_simplex. Assemble \<sigma> = g_inv(\<tau>) from the
      pieces via sub_simplex / face-preservation. **)
  have hK'_K0: "\<forall>\<sigma>\<in>K'. geotop_is_simplex \<sigma>"
  proof (rule ballI)
    fix \<sigma> assume h\<sigma>K': "\<sigma> \<in> K'"
    (** Unpack: \<sigma> = g_inv \<tau> for some \<tau> \<in> L'. **)
    obtain \<tau> where h\<tau>L': "\<tau> \<in> L'" and h\<sigma>_eq: "\<sigma> = ?g_inv ` \<tau>"
      using h\<sigma>K' unfolding K'_def by (by100 blast)
    (** \<tau> is a simplex via K.0 of L'. **)
    have h\<tau>_sim: "geotop_is_simplex \<tau>"
      using h\<tau>L' conjunct1[OF hL'_comp[unfolded geotop_is_complex_def]] by (by100 blast)
    (** \<tau> \<in> L' \<subseteq> some \<sigma>\<^sub>L \<in> L via refinement; \<open>g_inv\<close> is linear on \<sigma>\<^sub>L by the
        strengthened iso_induces_PLH conclusion. Restrict via sub_simplex. **)
    have h_lin_\<tau>: "geotop_linear_on \<tau> ?g_inv"
    proof -
      have hL'_refines_L: "geotop_refines L' L"
        using hL'L unfolding geotop_is_subdivision_def by (by100 blast)
      obtain \<sigma>\<^sub>L where h\<sigma>\<^sub>L: "\<sigma>\<^sub>L \<in> L" and h\<tau>_sub: "\<tau> \<subseteq> \<sigma>\<^sub>L"
        using hL'_refines_L h\<tau>L' unfolding geotop_refines_def by (by100 blast)
      have h_lin_\<sigma>\<^sub>L: "geotop_linear_on \<sigma>\<^sub>L ?g_inv"
        using hg_inv_lin_L h\<sigma>\<^sub>L by (by100 blast)
      show ?thesis
        by (rule geotop_linear_on_sub_simplex[OF h_lin_\<sigma>\<^sub>L h\<tau>_sim h\<tau>_sub])
    qed
    have h_inj_\<tau>: "inj_on ?g_inv \<tau>"
    proof -
      have h\<tau>_poly: "\<tau> \<subseteq> geotop_polyhedron L"
        using h\<tau>L' hL'L unfolding geotop_is_subdivision_def geotop_refines_def
        geotop_polyhedron_def by (by100 blast)
      show ?thesis using hg_inv_inj h\<tau>_poly inj_on_subset by (by100 blast)
    qed
    have "geotop_is_simplex (?g_inv ` \<tau>)"
      by (rule geotop_linear_inj_image_is_simplex[OF h_lin_\<tau> h_inj_\<tau> h\<tau>_sim])
    thus "geotop_is_simplex \<sigma>" using h\<sigma>_eq by (by100 simp)
  qed
  (** (3b) K.1: K' closed under faces. For \<sigma> \<in> K', \<sigma> = g_inv(\<tau>), \<tau> \<in> L';
      face \<sigma>' of \<sigma> pulls back via face_preimage to a face \<tau>' of \<tau>; K.1 on L'
      gives \<tau>' \<in> L', so \<sigma>' = g_inv(\<tau>') \<in> K'. **)
  have hK'_K1: "\<forall>\<sigma>\<in>K'. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K'"
  proof (intro ballI allI impI)
    fix \<sigma> \<sigma>' assume h\<sigma>K': "\<sigma> \<in> K'" and h\<sigma>'_face: "geotop_is_face \<sigma>' \<sigma>"
    obtain \<tau> where h\<tau>L': "\<tau> \<in> L'" and h\<sigma>_eq: "\<sigma> = ?g_inv ` \<tau>"
      using h\<sigma>K' unfolding K'_def by (by100 blast)
    have h\<tau>_sim: "geotop_is_simplex \<tau>"
      using h\<tau>L' conjunct1[OF hL'_comp[unfolded geotop_is_complex_def]] by (by100 blast)
    have h_lin_\<tau>: "geotop_linear_on \<tau> ?g_inv"
    proof -
      have hL'_refines_L: "geotop_refines L' L"
        using hL'L unfolding geotop_is_subdivision_def by (by100 blast)
      obtain \<sigma>\<^sub>L where h\<sigma>\<^sub>L: "\<sigma>\<^sub>L \<in> L" and h\<tau>_sub: "\<tau> \<subseteq> \<sigma>\<^sub>L"
        using hL'_refines_L h\<tau>L' unfolding geotop_refines_def by (by100 blast)
      have h_lin_\<sigma>\<^sub>L: "geotop_linear_on \<sigma>\<^sub>L ?g_inv"
        using hg_inv_lin_L h\<sigma>\<^sub>L by (by100 blast)
      show ?thesis
        by (rule geotop_linear_on_sub_simplex[OF h_lin_\<sigma>\<^sub>L h\<tau>_sim h\<tau>_sub])
    qed
    have h_inj_\<tau>: "inj_on ?g_inv \<tau>"
    proof -
      have h\<tau>_poly: "\<tau> \<subseteq> geotop_polyhedron L"
        using h\<tau>L' hL'L unfolding geotop_is_subdivision_def geotop_refines_def
        geotop_polyhedron_def by (by100 blast)
      show ?thesis using hg_inv_inj h\<tau>_poly inj_on_subset by (by100 blast)
    qed
    have h\<sigma>'_in_img_face: "geotop_is_face \<sigma>' (?g_inv ` \<tau>)"
      using h\<sigma>'_face h\<sigma>_eq by (by100 simp)
    obtain \<tau>' where h\<tau>'_face: "geotop_is_face \<tau>' \<tau>" and h\<sigma>'_eq: "\<sigma>' = ?g_inv ` \<tau>'"
      using geotop_linear_inj_image_face_preimage[OF h_lin_\<tau> h_inj_\<tau> h\<tau>_sim h\<sigma>'_in_img_face]
      by (by100 blast)
    have hL'_face_closed: "\<forall>\<sigma>\<in>L'. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> L'"
      using conjunct1[OF conjunct2[OF hL'_comp[unfolded geotop_is_complex_def]]]
      by (by100 blast)
    have h\<tau>'L': "\<tau>' \<in> L'"
      using h\<tau>'_face h\<tau>L' hL'_face_closed by (by100 blast)
    show "\<sigma>' \<in> K'" unfolding K'_def using h\<tau>'L' h\<sigma>'_eq by (by100 blast)
  qed
  (** (3c) K.2: intersections are faces. For \<sigma>_1 = g_inv(\<tau>_1), \<sigma>_2 = g_inv(\<tau>_2),
      \<sigma>_1 \<inter> \<sigma>_2 = g_inv(\<tau>_1 \<inter> \<tau>_2) (bijection), which is a face by face-preservation. **)
  have hK'_K2: "\<forall>\<sigma>\<in>K'. \<forall>\<tau>\<in>K'. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                 geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
  proof (intro ballI impI)
    fix \<sigma>_1 \<sigma>_2 assume h\<sigma>_1K': "\<sigma>_1 \<in> K'" and h\<sigma>_2K': "\<sigma>_2 \<in> K'"
    assume h_ne: "\<sigma>_1 \<inter> \<sigma>_2 \<noteq> {}"
    obtain \<tau>_1 where h\<tau>_1L': "\<tau>_1 \<in> L'" and h\<sigma>_1_eq: "\<sigma>_1 = ?g_inv ` \<tau>_1"
      using h\<sigma>_1K' unfolding K'_def by (by100 blast)
    obtain \<tau>_2 where h\<tau>_2L': "\<tau>_2 \<in> L'" and h\<sigma>_2_eq: "\<sigma>_2 = ?g_inv ` \<tau>_2"
      using h\<sigma>_2K' unfolding K'_def by (by100 blast)
    (** \<tau>_1, \<tau>_2 \<subseteq> |L'| = |L|. g_inv is inj on |L|, hence on \<tau>_1 \<union> \<tau>_2. **)
    have h\<tau>_1_poly: "\<tau>_1 \<subseteq> geotop_polyhedron L"
      using h\<tau>_1L' hL'L unfolding geotop_is_subdivision_def geotop_refines_def
      geotop_polyhedron_def by (by100 blast)
    have h\<tau>_2_poly: "\<tau>_2 \<subseteq> geotop_polyhedron L"
      using h\<tau>_2L' hL'L unfolding geotop_is_subdivision_def geotop_refines_def
      geotop_polyhedron_def by (by100 blast)
    (** g_inv(\<tau>_1 \<inter> \<tau>_2) = g_inv(\<tau>_1) \<inter> g_inv(\<tau>_2) = \<sigma>_1 \<inter> \<sigma>_2 via inj_on_image_Int. **)
    have h_inj_union: "inj_on ?g_inv (\<tau>_1 \<union> \<tau>_2)"
    proof -
      have h_sub: "\<tau>_1 \<union> \<tau>_2 \<subseteq> geotop_polyhedron L"
        using h\<tau>_1_poly h\<tau>_2_poly by (by100 blast)
      show ?thesis using hg_inv_inj h_sub inj_on_subset by (by100 blast)
    qed
    have h_img_int: "?g_inv ` (\<tau>_1 \<inter> \<tau>_2) = ?g_inv ` \<tau>_1 \<inter> ?g_inv ` \<tau>_2"
      using inj_on_image_Int[OF h_inj_union] by (by100 simp)
    have h_img_ne: "?g_inv ` (\<tau>_1 \<inter> \<tau>_2) \<noteq> {}"
      using h_ne h_img_int h\<sigma>_1_eq h\<sigma>_2_eq by (by100 simp)
    have h_inter_ne: "\<tau>_1 \<inter> \<tau>_2 \<noteq> {}"
      using h_img_ne by (by100 blast)
    (** K.2 of L' gives \<tau>_1 \<inter> \<tau>_2 is a face of both. **)
    have hL'_K2: "\<forall>\<sigma>\<in>L'. \<forall>\<tau>\<in>L'. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                    geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
      using conjunct1[OF conjunct2[OF conjunct2[OF hL'_comp[unfolded geotop_is_complex_def]]]]
      by (by100 blast)
    have h_face_\<tau>_1: "geotop_is_face (\<tau>_1 \<inter> \<tau>_2) \<tau>_1"
      using hL'_K2 h\<tau>_1L' h\<tau>_2L' h_inter_ne by (by100 blast)
    have h_face_\<tau>_2: "geotop_is_face (\<tau>_1 \<inter> \<tau>_2) \<tau>_2"
      using hL'_K2 h\<tau>_1L' h\<tau>_2L' h_inter_ne by (by100 blast)
    (** Apply preserves_face to pull through g_inv. Linearity from strengthened
        iso_induces_PLH + sub_simplex descent via refinement. **)
    have hL'_refines_L_2: "geotop_refines L' L"
      using hL'L unfolding geotop_is_subdivision_def by (by100 blast)
    have h\<tau>_1_sim: "geotop_is_simplex \<tau>_1"
      using h\<tau>_1L' conjunct1[OF hL'_comp[unfolded geotop_is_complex_def]] by (by100 blast)
    have h\<tau>_2_sim: "geotop_is_simplex \<tau>_2"
      using h\<tau>_2L' conjunct1[OF hL'_comp[unfolded geotop_is_complex_def]] by (by100 blast)
    have h_lin_\<tau>_1: "geotop_linear_on \<tau>_1 ?g_inv"
    proof -
      obtain \<sigma>\<^sub>L where h\<sigma>\<^sub>L: "\<sigma>\<^sub>L \<in> L" and h\<tau>_sub: "\<tau>_1 \<subseteq> \<sigma>\<^sub>L"
        using hL'_refines_L_2 h\<tau>_1L' unfolding geotop_refines_def by (by100 blast)
      have h_lin_\<sigma>\<^sub>L: "geotop_linear_on \<sigma>\<^sub>L ?g_inv"
        using hg_inv_lin_L h\<sigma>\<^sub>L by (by100 blast)
      show ?thesis
        by (rule geotop_linear_on_sub_simplex[OF h_lin_\<sigma>\<^sub>L h\<tau>_1_sim h\<tau>_sub])
    qed
    have h_lin_\<tau>_2: "geotop_linear_on \<tau>_2 ?g_inv"
    proof -
      obtain \<sigma>\<^sub>L where h\<sigma>\<^sub>L: "\<sigma>\<^sub>L \<in> L" and h\<tau>_sub: "\<tau>_2 \<subseteq> \<sigma>\<^sub>L"
        using hL'_refines_L_2 h\<tau>_2L' unfolding geotop_refines_def by (by100 blast)
      have h_lin_\<sigma>\<^sub>L: "geotop_linear_on \<sigma>\<^sub>L ?g_inv"
        using hg_inv_lin_L h\<sigma>\<^sub>L by (by100 blast)
      show ?thesis
        by (rule geotop_linear_on_sub_simplex[OF h_lin_\<sigma>\<^sub>L h\<tau>_2_sim h\<tau>_sub])
    qed
    have h_inj_\<tau>_1: "inj_on ?g_inv \<tau>_1"
      using hg_inv_inj h\<tau>_1_poly inj_on_subset by (by100 blast)
    have h_inj_\<tau>_2: "inj_on ?g_inv \<tau>_2"
      using hg_inv_inj h\<tau>_2_poly inj_on_subset by (by100 blast)
    have h_face_\<sigma>_1: "geotop_is_face (?g_inv ` (\<tau>_1 \<inter> \<tau>_2)) (?g_inv ` \<tau>_1)"
      by (rule geotop_linear_inj_image_preserves_face[OF h_lin_\<tau>_1 h_inj_\<tau>_1 h_face_\<tau>_1])
    have h_face_\<sigma>_2: "geotop_is_face (?g_inv ` (\<tau>_1 \<inter> \<tau>_2)) (?g_inv ` \<tau>_2)"
      by (rule geotop_linear_inj_image_preserves_face[OF h_lin_\<tau>_2 h_inj_\<tau>_2 h_face_\<tau>_2])
    have h_inter_eq: "\<sigma>_1 \<inter> \<sigma>_2 = ?g_inv ` (\<tau>_1 \<inter> \<tau>_2)"
      using h_img_int h\<sigma>_1_eq h\<sigma>_2_eq by (by100 simp)
    have h_face_1: "geotop_is_face (\<sigma>_1 \<inter> \<sigma>_2) \<sigma>_1"
      using h_face_\<sigma>_1 h_inter_eq h\<sigma>_1_eq by (by100 simp)
    have h_face_2: "geotop_is_face (\<sigma>_1 \<inter> \<sigma>_2) \<sigma>_2"
      using h_face_\<sigma>_2 h_inter_eq h\<sigma>_2_eq by (by100 simp)
    show "geotop_is_face (\<sigma>_1 \<inter> \<sigma>_2) \<sigma>_1 \<and> geotop_is_face (\<sigma>_1 \<inter> \<sigma>_2) \<sigma>_2"
      using h_face_1 h_face_2 by (by100 blast)
  qed
  (** (3d) K.3: local finiteness. For finite K', U = UNIV suffices. **)
  have hL'fin: "finite L'"
    by (rule geotop_subdivision_of_finite_is_finite[OF hLfin hL'L])
  have hK'fin: "finite K'" unfolding K'_def using hL'fin by (by100 simp)
  have hK'_K3: "\<forall>\<sigma>\<in>K'. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K'. \<tau> \<inter> U \<noteq> {}}"
  proof (rule ballI)
    fix \<sigma> assume h\<sigma>: "\<sigma> \<in> K'"
    have h_sub_fin: "finite {\<tau>\<in>K'. \<tau> \<inter> UNIV \<noteq> {}}" using hK'fin by (by100 simp)
    have h_open: "open (UNIV :: 'a set)" by (by100 simp)
    show "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K'. \<tau> \<inter> U \<noteq> {}}"
      using h_open h_sub_fin by (by100 blast)
  qed
  have hK'_comp: "geotop_is_complex K'"
    unfolding geotop_is_complex_def
    using hK'_K0 hK'_K1 hK'_K2 hK'_K3 by (by100 blast)
  (** (4) \<open>|K'| = |K|\<close>: apply \<open>g\<^sup>-\<^sup>1\<close> to \<open>|L'| = |L|\<close>. **)
  have hL'L_poly: "geotop_polyhedron L' = geotop_polyhedron L"
    using hL'L unfolding geotop_is_subdivision_def by (by100 blast)
  (** \<open>|K'| = \<Union>K' = \<Union>{g\<^sup>-\<^sup>1(\<tau>) | \<tau>\<in>L'} = g\<^sup>-\<^sup>1(\<Union>L') = g\<^sup>-\<^sup>1(|L|) = |K|\<close>. **)
  have hK'_poly_step1: "geotop_polyhedron K' = ?g_inv ` (geotop_polyhedron L')"
    unfolding K'_def geotop_polyhedron_def by (by100 blast)
  have hginv_bij: "bij_betw ?g_inv (geotop_polyhedron L) (geotop_polyhedron K)"
    by (rule bij_betw_inv_into[OF hg_bij])
  have hginv_img: "?g_inv ` (geotop_polyhedron L) = geotop_polyhedron K"
    using hginv_bij unfolding bij_betw_def by (by100 blast)
  have hK'_poly: "geotop_polyhedron K' = geotop_polyhedron K"
    using hK'_poly_step1 hL'L_poly hginv_img by (by100 simp)
  (** (5) \<open>K' < K\<close>: each simplex of \<open>K'\<close> is \<open>g\<^sup>-\<^sup>1(\<tau>)\<close> for some \<open>\<tau> \<in> L'\<close>,
      which sits inside \<open>g\<^sup>-\<^sup>1\<close> of the corresponding simplex of \<open>L\<close>, a subset of \<open>|K|\<close>
      lying in some \<sigma> \<in> K. Structured decomposition: **)
  (** (5i) g_inv is PL L \<rightarrow> K, so there is a subdivision L_1 < L on which
           g_inv is linear, mapping each L_1-simplex into some K-simplex. **)
  have hg_inv_PL: "geotop_PL_map L K ?g_inv"
    using hg unfolding geotop_PLH_def by (by100 blast)
  (** Direct proof via strengthened iso_induces_PLH: g_inv maps L-simplexes to K-simplexes.
      For \<sigma>' = g_inv \<tau>' \<in> K' with \<tau>' \<in> L', use L' < L to find \<tau> \<in> L with \<tau>' \<subseteq> \<tau>,
      then g_inv \<tau> \<in> K (from hg_inv_L_sim), and g_inv \<tau>' \<subseteq> g_inv \<tau>. **)
  have hK'_ref: "geotop_refines K' K"
    unfolding geotop_refines_def
  proof (rule ballI)
    fix \<sigma>' assume h\<sigma>'K': "\<sigma>' \<in> K'"
    obtain \<tau>' where h\<tau>'L': "\<tau>' \<in> L'" and h\<sigma>'_eq: "\<sigma>' = ?g_inv ` \<tau>'"
      using h\<sigma>'K' unfolding K'_def by (by100 blast)
    have hL'_ref_L: "geotop_refines L' L"
      using hL'L unfolding geotop_is_subdivision_def by (by100 blast)
    obtain \<tau> where h\<tau>L: "\<tau> \<in> L" and h\<tau>'_sub: "\<tau>' \<subseteq> \<tau>"
      using h\<tau>'L' hL'_ref_L unfolding geotop_refines_def by (by100 blast)
    have hg_inv_\<tau>_K: "?g_inv ` \<tau> \<in> K" using h\<tau>L hg_inv_L_sim by (by100 blast)
    have h\<sigma>'_sub: "\<sigma>' \<subseteq> ?g_inv ` \<tau>"
      using h\<sigma>'_eq h\<tau>'_sub by (by100 blast)
    show "\<exists>\<sigma>\<in>K. \<sigma>' \<subseteq> \<sigma>" using hg_inv_\<tau>_K h\<sigma>'_sub by (by100 blast)
  qed
  have hK'_K: "geotop_is_subdivision K' K"
    unfolding geotop_is_subdivision_def
    using hK'_comp hKcomp hK'_ref hK'_poly by (by100 blast)
  (** (6) Build the vertex iso \<open>K' \<cong> L'\<close> via \<open>\<tau> \<mapsto> g\<^sup>-\<^sup>1(\<tau>)\<close>, descending to
      vertex-level. Decomposed into: **)
  (** (6a) Vertex bijection: g_inv maps vertices of L' to vertices of K' bijectively.
      Same pattern as hiso_vert in GT_2 backward: use complex_vertices_eq_0_simplexes
      to rewrite vertex sets as {v : {v} \<in> complex}, then show g_inv-image structure. **)
  have hV_L'_eq: "geotop_complex_vertices L' = {v. {v} \<in> L'}"
    by (rule geotop_complex_vertices_eq_0_simplexes[OF hL'_comp])
  have hV_K'_eq: "geotop_complex_vertices K' = {v. {v} \<in> K'}"
    by (rule geotop_complex_vertices_eq_0_simplexes[OF hK'_comp])
  have hg_inv_inj_L: "inj_on ?g_inv (geotop_polyhedron L)"
    using hginv_bij unfolding bij_betw_def by (by100 blast)
  (** {v} \<in> K' iff v = g_inv(w) for some w with {w} \<in> L'. **)
  have hK'_singletons: "{v. {v} \<in> K'} = ?g_inv ` {w. {w} \<in> L'}"
  proof (rule set_eqI, rule iffI)
    fix v assume hv: "v \<in> {v. {v} \<in> K'}"
    hence hv_K': "{v} \<in> K'" by (by100 simp)
    obtain \<sigma> where h\<sigma>L': "\<sigma> \<in> L'" and h\<sigma>_eq: "{v} = ?g_inv ` \<sigma>"
      using hv_K' unfolding K'_def by (by100 blast)
    have h\<sigma>_in_L: "\<sigma> \<subseteq> geotop_polyhedron L"
      using h\<sigma>L' hL'L_poly unfolding geotop_polyhedron_def by (by100 blast)
    have hg_inv_inj_\<sigma>: "inj_on ?g_inv \<sigma>"
      using hg_inv_inj_L h\<sigma>_in_L inj_on_subset by (by100 blast)
    have h_img_card: "card (?g_inv ` \<sigma>) = card \<sigma>"
      by (rule card_image[OF hg_inv_inj_\<sigma>])
    have h_target_card: "card (?g_inv ` \<sigma>) = card {v}"
      using h\<sigma>_eq by (by100 simp)
    have h_v_card: "card ({v}::'a set) = 1" by (by100 simp)
    have h\<sigma>_card: "card \<sigma> = 1"
      using h_img_card h_target_card h_v_card by (by100 simp)
    have h\<sigma>_fin: "finite \<sigma>" using h\<sigma>_card card_gt_0_iff by (by100 fastforce)
    obtain w where h\<sigma>_sing: "\<sigma> = {w}"
      using h\<sigma>_card card_1_singletonE[of \<sigma>] h\<sigma>_fin by (by100 blast)
    have hw_L': "{w} \<in> L'" using h\<sigma>L' h\<sigma>_sing by (by100 simp)
    have hv_eq: "v = ?g_inv w" using h\<sigma>_eq h\<sigma>_sing by (by100 simp)
    show "v \<in> ?g_inv ` {w. {w} \<in> L'}" using hw_L' hv_eq by (by100 blast)
  next
    fix v assume hv: "v \<in> ?g_inv ` {w. {w} \<in> L'}"
    obtain w where hw_L': "{w} \<in> L'" and hvw: "v = ?g_inv w" using hv by (by100 blast)
    have h_img: "?g_inv ` {w} = {v}" using hvw by (by100 simp)
    have h_img_in_K': "?g_inv ` {w} \<in> K'" using hw_L' unfolding K'_def by (by100 blast)
    show "v \<in> {v. {v} \<in> K'}" using h_img h_img_in_K' by (by100 simp)
  qed
  have hV_K'_img: "geotop_complex_vertices K' = ?g_inv ` geotop_complex_vertices L'"
    using hV_L'_eq hV_K'_eq hK'_singletons by (by100 simp)
  (** V(L') \<subseteq> |L'| = |L| (vertices in polyhedron). **)
  have hV_L'_in_L: "geotop_complex_vertices L' \<subseteq> geotop_polyhedron L"
  proof
    fix v assume hv: "v \<in> geotop_complex_vertices L'"
    hence hv_sing: "{v} \<in> L'" using hV_L'_eq by (by100 simp)
    hence hv_in_L': "v \<in> geotop_polyhedron L'"
      unfolding geotop_polyhedron_def by (by100 blast)
    show "v \<in> geotop_polyhedron L" using hv_in_L' hL'L_poly by (by100 simp)
  qed
  have hg_inv_inj_VL': "inj_on ?g_inv (geotop_complex_vertices L')"
    using hg_inv_inj_L hV_L'_in_L inj_on_subset by (by100 blast)
  have hiso_K'L'_vert: "bij_betw ?g_inv (geotop_complex_vertices L')
                                          (geotop_complex_vertices K')"
    unfolding bij_betw_def
    using hg_inv_inj_VL' hV_K'_img by (by100 simp)
  (** (6b) Simplex correspondence under convex hull. For V \<subseteq> V(L'):
      conv V \<in> L' \<longleftrightarrow> conv (g_inv V) \<in> K'.
      (\<Rightarrow>) If conv V = \<tau> \<in> L', then g_inv(\<tau>) \<in> K' by def of K'. Need
          g_inv(\<tau>) = conv(g_inv V): since \<tau> = conv V and g_inv linear on \<tau>
          via refinement, apply our hull_eq helper.
      (\<Leftarrow>) If conv(g_inv V) \<in> K', unfold K': \<exists>\<tau> \<in> L'. conv(g_inv V) = g_inv \<tau>.
          Apply g to both sides: g(conv(g_inv V)) = g(g_inv \<tau>) = \<tau>. And
          g(conv(g_inv V)) = conv V via linearity + bijection. So conv V = \<tau> \<in> L'. **)
  have hiso_K'L'_simp: "\<forall>V. V \<subseteq> geotop_complex_vertices L' \<longrightarrow>
                          (geotop_convex_hull V \<in> L' \<longleftrightarrow>
                           geotop_convex_hull (?g_inv ` V) \<in> K')"
  proof (intro allI impI)
    fix V\<^sub>0 assume hV\<^sub>0: "V\<^sub>0 \<subseteq> geotop_complex_vertices L'"
    show "geotop_convex_hull V\<^sub>0 \<in> L' \<longleftrightarrow>
          geotop_convex_hull (?g_inv ` V\<^sub>0) \<in> K'"
    proof (rule iffI)
      assume h_in_L': "geotop_convex_hull V\<^sub>0 \<in> L'"
      have h_img_K': "?g_inv ` (geotop_convex_hull V\<^sub>0) \<in> K'"
        unfolding K'_def using h_in_L' by (by100 blast)
      (** Obtain vertex set W_0 of conv V_0 from simplex_vertices. **)
      have h_convV0_sim: "geotop_is_simplex (geotop_convex_hull V\<^sub>0)"
        using h_in_L' conjunct1[OF hL'_comp[unfolded geotop_is_complex_def]]
        by (by100 blast)
      obtain W\<^sub>0 where hW\<^sub>0sv: "geotop_simplex_vertices (geotop_convex_hull V\<^sub>0) W\<^sub>0"
        using h_convV0_sim unfolding geotop_is_simplex_def
              geotop_simplex_vertices_def by (by100 blast)
      obtain m_W n_W where hW\<^sub>0fin: "finite W\<^sub>0" and hW\<^sub>0card: "card W\<^sub>0 = n_W + 1"
                       and hW\<^sub>0nm: "n_W \<le> m_W"
                       and hW\<^sub>0gp: "geotop_general_position W\<^sub>0 m_W"
                       and hW\<^sub>0hull: "geotop_convex_hull V\<^sub>0 = geotop_convex_hull W\<^sub>0"
        using hW\<^sub>0sv unfolding geotop_simplex_vertices_def by (by100 blast)
      (** W_0 is AI. **)
      have hW\<^sub>0_ai: "\<not> affine_dependent W\<^sub>0"
        by (rule geotop_general_position_imp_aff_indep[OF hW\<^sub>0sv])
      (** conv V_0 = conv W_0 in HOL sense. **)
      have h_conv_eq: "convex hull V\<^sub>0 = convex hull W\<^sub>0"
      proof -
        have h1: "convex hull V\<^sub>0 = geotop_convex_hull V\<^sub>0"
          by (rule geotop_convex_hull_eq_HOL[symmetric])
        have h2: "geotop_convex_hull W\<^sub>0 = convex hull W\<^sub>0"
          by (rule geotop_convex_hull_eq_HOL)
        show ?thesis using h1 hW\<^sub>0hull h2 by (by100 simp)
      qed
      (** W_0 = extreme points of conv W_0 = extreme points of conv V_0. Both \<subseteq> V_0. **)
      have hW\<^sub>0_sub_V\<^sub>0: "W\<^sub>0 \<subseteq> V\<^sub>0"
      proof
        fix w assume hw: "w \<in> W\<^sub>0"
        have h_extr_W: "w extreme_point_of (convex hull W\<^sub>0)"
          using extreme_point_of_convex_hull_affine_independent[OF hW\<^sub>0_ai] hw
          by (by100 blast)
        have h_extr_V: "w extreme_point_of (convex hull V\<^sub>0)"
          using h_extr_W h_conv_eq by (by100 simp)
        show "w \<in> V\<^sub>0" by (rule extreme_point_of_convex_hull[OF h_extr_V])
      qed
      (** Bary-preservation on W_0 via strengthened iso_induces_PLH
          + refinement + sub_simplex. **)
      have hL'_refines_L_fwd: "geotop_refines L' L"
        using hL'L unfolding geotop_is_subdivision_def by (by100 blast)
      obtain \<sigma>\<^sub>L where h\<sigma>\<^sub>LL: "\<sigma>\<^sub>L \<in> L"
                  and h_conv_sub_\<sigma>: "geotop_convex_hull V\<^sub>0 \<subseteq> \<sigma>\<^sub>L"
        using hL'_refines_L_fwd h_in_L' unfolding geotop_refines_def by (by100 blast)
      have h_lin_\<sigma>\<^sub>L: "geotop_linear_on \<sigma>\<^sub>L ?g_inv"
        using hg_inv_lin_L h\<sigma>\<^sub>LL by (by100 blast)
      have h_lin_convV\<^sub>0: "geotop_linear_on (geotop_convex_hull V\<^sub>0) ?g_inv"
        by (rule geotop_linear_on_sub_simplex[OF h_lin_\<sigma>\<^sub>L h_convV0_sim h_conv_sub_\<sigma>])
      (** From linear_on (conv V_0), extract bary on W_0 (= simplex_vertices(conv V_0)). **)
      obtain V\<^sub>L where hV\<^sub>Lsv: "geotop_simplex_vertices (geotop_convex_hull V\<^sub>0) V\<^sub>L"
                  and h_prop_lin: "\<forall>\<alpha>. (\<forall>v\<in>V\<^sub>L. 0 \<le> \<alpha> v) \<and> sum \<alpha> V\<^sub>L = 1 \<longrightarrow>
                                      ?g_inv (\<Sum>v\<in>V\<^sub>L. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>V\<^sub>L. \<alpha> v *\<^sub>R ?g_inv v)"
        using h_lin_convV\<^sub>0 unfolding geotop_linear_on_def by (by100 blast)
      have hVL_eq_W: "V\<^sub>L = W\<^sub>0"
        by (rule geotop_simplex_vertices_unique[OF hV\<^sub>Lsv hW\<^sub>0sv])
      have h_bary_W\<^sub>0: "\<And>\<alpha>. (\<forall>v\<in>W\<^sub>0. 0 \<le> \<alpha> v) \<Longrightarrow> sum \<alpha> W\<^sub>0 = 1 \<Longrightarrow>
                         ?g_inv (\<Sum>v\<in>W\<^sub>0. \<alpha> v *\<^sub>R v) = (\<Sum>v\<in>W\<^sub>0. \<alpha> v *\<^sub>R ?g_inv v)"
        using h_prop_lin hVL_eq_W by (by100 blast)
      (** Inj on W_0 (W_0 \<subseteq> conv V_0 \<subseteq> |L|, g_inv inj on |L|). **)
      have h_convV\<^sub>0_sub_L: "geotop_convex_hull V\<^sub>0 \<subseteq> geotop_polyhedron L"
      proof -
        have h_sub: "\<sigma>\<^sub>L \<subseteq> geotop_polyhedron L"
          unfolding geotop_polyhedron_def using h\<sigma>\<^sub>LL by (by100 blast)
        show ?thesis using h_conv_sub_\<sigma> h_sub by (by100 blast)
      qed
      have h_W\<^sub>0_sub_L: "W\<^sub>0 \<subseteq> geotop_polyhedron L"
      proof -
        have hW_conv: "W\<^sub>0 \<subseteq> geotop_convex_hull W\<^sub>0"
          unfolding geotop_convex_hull_def hull_def by (by100 blast)
        have "W\<^sub>0 \<subseteq> geotop_convex_hull V\<^sub>0" using hW_conv hW\<^sub>0hull by (by100 simp)
        thus ?thesis using h_convV\<^sub>0_sub_L by (by100 blast)
      qed
      have h_inj_W\<^sub>0: "inj_on ?g_inv W\<^sub>0"
        using hg_inv_inj h_W\<^sub>0_sub_L inj_on_subset by (by100 blast)
      (** Apply hull_eq on W_0. **)
      have h_hull_eq_W\<^sub>0: "?g_inv ` (convex hull W\<^sub>0) = convex hull (?g_inv ` W\<^sub>0)"
        by (rule geotop_bary_lin_inj_image_hull_eq[OF hW\<^sub>0fin h_inj_W\<^sub>0 h_bary_W\<^sub>0])
      (** g_inv(conv V_0) = conv(g_inv W_0). **)
      have h_img_geo_HOL: "?g_inv ` (geotop_convex_hull V\<^sub>0) = convex hull (?g_inv ` W\<^sub>0)"
      proof -
        have hgv_eq_hw: "geotop_convex_hull V\<^sub>0 = convex hull W\<^sub>0"
        proof -
          have "geotop_convex_hull V\<^sub>0 = convex hull V\<^sub>0"
            by (rule geotop_convex_hull_eq_HOL)
          also have "\<dots> = convex hull W\<^sub>0" by (rule h_conv_eq)
          finally show ?thesis .
        qed
        have h1: "?g_inv ` (geotop_convex_hull V\<^sub>0) = ?g_inv ` (convex hull W\<^sub>0)"
          using hgv_eq_hw by (by100 simp)
        show ?thesis using h1 h_hull_eq_W\<^sub>0 by (by100 simp)
      qed
      (** conv(g_inv V_0) = conv(g_inv W_0) via W_0 \<subseteq> V_0 + V_0 \<subseteq> conv V_0. **)
      have h_gV\<^sub>0_sub_conv: "?g_inv ` V\<^sub>0 \<subseteq> convex hull (?g_inv ` W\<^sub>0)"
      proof -
        have "V\<^sub>0 \<subseteq> geotop_convex_hull V\<^sub>0"
          unfolding geotop_convex_hull_def hull_def by (by100 blast)
        hence "?g_inv ` V\<^sub>0 \<subseteq> ?g_inv ` (geotop_convex_hull V\<^sub>0)" by (by100 blast)
        thus ?thesis using h_img_geo_HOL by (by100 simp)
      qed
      have h_gW\<^sub>0_sub_V\<^sub>0: "?g_inv ` W\<^sub>0 \<subseteq> ?g_inv ` V\<^sub>0" using hW\<^sub>0_sub_V\<^sub>0 by (by100 blast)
      have h_conv_ge: "convex hull (?g_inv ` W\<^sub>0) \<subseteq> convex hull (?g_inv ` V\<^sub>0)"
        by (rule hull_mono[OF h_gW\<^sub>0_sub_V\<^sub>0])
      have h_conv_le: "convex hull (?g_inv ` V\<^sub>0) \<subseteq> convex hull (?g_inv ` W\<^sub>0)"
        using h_gV\<^sub>0_sub_conv convex_convex_hull
              hull_minimal[of "?g_inv ` V\<^sub>0" "convex hull (?g_inv ` W\<^sub>0)" convex]
        by (by100 simp)
      have h_conv_final: "convex hull (?g_inv ` V\<^sub>0) = convex hull (?g_inv ` W\<^sub>0)"
        using h_conv_ge h_conv_le by (by100 blast)
      have h_geo_final: "geotop_convex_hull (?g_inv ` V\<^sub>0) = ?g_inv ` (geotop_convex_hull V\<^sub>0)"
      proof -
        have h_a: "geotop_convex_hull (?g_inv ` V\<^sub>0) = convex hull (?g_inv ` V\<^sub>0)"
          by (rule geotop_convex_hull_eq_HOL)
        from h_a have s1: "geotop_convex_hull (?g_inv ` V\<^sub>0) = convex hull (?g_inv ` V\<^sub>0)" .
        also from h_conv_final have "\<dots> = convex hull (?g_inv ` W\<^sub>0)" .
        also from h_img_geo_HOL have "\<dots> = ?g_inv ` (geotop_convex_hull V\<^sub>0)" by (by100 simp)
        finally show ?thesis .
      qed
      show "geotop_convex_hull (?g_inv ` V\<^sub>0) \<in> K'"
        using h_geo_final h_img_K' by (by100 simp)
    next
      assume h_img_in_K': "geotop_convex_hull (?g_inv ` V\<^sub>0) \<in> K'"
      obtain \<tau> where h\<tau>L': "\<tau> \<in> L'"
                 and h_eq: "geotop_convex_hull (?g_inv ` V\<^sub>0) = ?g_inv ` \<tau>"
        using h_img_in_K' unfolding K'_def by (by100 blast)
      (** V_0 \<subseteq> \<tau>: V_0 \<subseteq> |L|, g(g_inv v) = v. g_inv V_0 \<subseteq> g_inv \<tau>. **)
      have hV\<^sub>0_sub_L: "V\<^sub>0 \<subseteq> geotop_polyhedron L"
        using hV\<^sub>0 hV_L'_in_L by (by100 blast)
      have h\<tau>_sub_L: "\<tau> \<subseteq> geotop_polyhedron L"
        using h\<tau>L' hL'L unfolding geotop_is_subdivision_def
        geotop_refines_def geotop_polyhedron_def by (by100 blast)
      have hV\<^sub>0_sub_\<tau>: "V\<^sub>0 \<subseteq> \<tau>"
      proof
        fix v assume hv_in: "v \<in> V\<^sub>0"
        have hvL: "v \<in> geotop_polyhedron L" using hv_in hV\<^sub>0_sub_L by (by100 blast)
        (** g_inv v \<in> g_inv V_0. **)
        have hgivV\<^sub>0: "?g_inv v \<in> ?g_inv ` V\<^sub>0" using hv_in by (by100 blast)
        (** g_inv V_0 \<subseteq> conv(g_inv V_0) = g_inv \<tau>. **)
        have h_giV_sub: "?g_inv ` V\<^sub>0 \<subseteq> geotop_convex_hull (?g_inv ` V\<^sub>0)"
          unfolding geotop_convex_hull_def hull_def by (by100 blast)
        have h_gi\<tau>: "?g_inv ` V\<^sub>0 \<subseteq> ?g_inv ` \<tau>"
          using h_giV_sub h_eq by (by100 simp)
        have hgiv_in_\<tau>: "?g_inv v \<in> ?g_inv ` \<tau>" using hgivV\<^sub>0 h_gi\<tau> by (by100 blast)
        (** g_inv is inj on |L|, so this gives v \<in> \<tau>. **)
        obtain w where hw\<tau>: "w \<in> \<tau>" and hgiw: "?g_inv v = ?g_inv w"
          using hgiv_in_\<tau> by (by100 blast)
        have hwL: "w \<in> geotop_polyhedron L" using hw\<tau> h\<tau>_sub_L by (by100 blast)
        have hvw: "v = w"
          using inj_onD[OF hg_inv_inj hgiw hvL hwL] by (by100 simp)
        show "v \<in> \<tau>" using hvw hw\<tau> by (by100 simp)
      qed
      (** \<tau> is a simplex (K.0 of L') with some vertex set V_\<tau>. **)
      have h\<tau>_sim: "geotop_is_simplex \<tau>"
        using h\<tau>L' conjunct1[OF hL'_comp[unfolded geotop_is_complex_def]]
        by (by100 blast)
      obtain V\<tau> where hV\<tau>sv: "geotop_simplex_vertices \<tau> V\<tau>"
        using h\<tau>_sim unfolding geotop_is_simplex_def
              geotop_simplex_vertices_def by (by100 blast)
      have hV\<tau>_ai: "\<not> affine_dependent V\<tau>"
        by (rule geotop_general_position_imp_aff_indep[OF hV\<tau>sv])
      have h\<tau>_hull: "\<tau> = convex hull V\<tau>"
      proof -
        have "\<tau> = geotop_convex_hull V\<tau>"
          using hV\<tau>sv unfolding geotop_simplex_vertices_def by (by100 blast)
        also have "\<dots> = convex hull V\<tau>" by (rule geotop_convex_hull_eq_HOL)
        finally show ?thesis .
      qed
      (** V_0 \<subseteq> V_\<tau>: any L'-vertex in \<tau> must be a V_\<tau>-vertex (extreme point). **)
      have hV\<^sub>0_sub_V\<tau>: "V\<^sub>0 \<subseteq> V\<tau>"
      proof
        fix v assume hvV\<^sub>0: "v \<in> V\<^sub>0"
        have hv\<tau>: "v \<in> \<tau>" using hvV\<^sub>0 hV\<^sub>0_sub_\<tau> by (by100 blast)
        have hvVL': "v \<in> geotop_complex_vertices L'" using hvV\<^sub>0 hV\<^sub>0 by (by100 blast)
        obtain \<sigma> W_\<sigma> where h\<sigma>L': "\<sigma> \<in> L'"
                      and hW\<sigma>sv: "geotop_simplex_vertices \<sigma> W_\<sigma>" and hvW\<sigma>: "v \<in> W_\<sigma>"
          using hvVL' unfolding geotop_complex_vertices_def by (by100 blast)
        (** v \<in> \<sigma> (vertex is in simplex). **)
        have h\<sigma>_eq: "\<sigma> = geotop_convex_hull W_\<sigma>"
          using hW\<sigma>sv unfolding geotop_simplex_vertices_def by (by100 blast)
        have h_sub: "W_\<sigma> \<subseteq> convex hull W_\<sigma>" by (rule hull_subset)
        have h\<sigma>_HOL_pre: "\<sigma> = convex hull W_\<sigma>"
          using h\<sigma>_eq geotop_convex_hull_eq_HOL by (by100 simp)
        have hv\<sigma>: "v \<in> \<sigma>"
          using hvW\<sigma> h_sub h\<sigma>_HOL_pre by (by100 blast)
        (** \<sigma> \<inter> \<tau> is a face of \<tau> via K.2 of L'. **)
        have h_inter_ne: "\<sigma> \<inter> \<tau> \<noteq> {}" using hv\<sigma> hv\<tau> by (by100 blast)
        have hL'_K2: "\<forall>\<sigma>\<in>L'. \<forall>\<tau>\<in>L'. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                        geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
          using conjunct1[OF conjunct2[OF conjunct2[OF hL'_comp[unfolded geotop_is_complex_def]]]]
          by (by100 blast)
        have h_face_\<tau>: "geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
          using hL'_K2 h\<sigma>L' h\<tau>L' h_inter_ne by (by100 blast)
        have h_face_\<sigma>: "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma>"
          using hL'_K2 h\<sigma>L' h\<tau>L' h_inter_ne by (by100 blast)
        (** Face \<tau> \<inter> \<sigma> = conv W for some W \<subseteq> V_\<tau>. **)
        obtain V\<tau>' W where hV\<tau>'sv: "geotop_simplex_vertices \<tau> V\<tau>'"
                       and hW_ne: "W \<noteq> {}" and hWV\<tau>': "W \<subseteq> V\<tau>'"
                       and h_inter_hull: "\<sigma> \<inter> \<tau> = geotop_convex_hull W"
          using h_face_\<tau> unfolding geotop_is_face_def by (by100 blast)
        have hV\<tau>'_eq: "V\<tau>' = V\<tau>" by (rule geotop_simplex_vertices_unique[OF hV\<tau>'sv hV\<tau>sv])
        have hWV\<tau>: "W \<subseteq> V\<tau>" using hWV\<tau>' hV\<tau>'_eq by (by100 simp)
        (** Also need W \<subseteq> W_\<sigma>: via face of \<sigma>. **)
        obtain W_\<sigma>' W' where hW_\<sigma>'sv: "geotop_simplex_vertices \<sigma> W_\<sigma>'"
                         and hW'_ne: "W' \<noteq> {}" and hW'W\<sigma>: "W' \<subseteq> W_\<sigma>'"
                         and h_inter_hull': "\<sigma> \<inter> \<tau> = geotop_convex_hull W'"
          using h_face_\<sigma> unfolding geotop_is_face_def by (by100 blast)
        have hW_\<sigma>'_eq: "W_\<sigma>' = W_\<sigma>"
          by (rule geotop_simplex_vertices_unique[OF hW_\<sigma>'sv hW\<sigma>sv])
        (** conv W = conv W' (both = \<sigma> \<inter> \<tau>). **)
        have h_W_W': "geotop_convex_hull W = geotop_convex_hull W'"
          using h_inter_hull h_inter_hull' by (by100 simp)
        (** By AI vertex uniqueness on sub-simplex, W = W'. Need AI of W_\<sigma>
            and W, W' \<subseteq> W_\<sigma>, conv W = conv W' \<Rightarrow> W = W'. **)
        have hW'W\<sigma>_final: "W' \<subseteq> W_\<sigma>" using hW'W\<sigma> hW_\<sigma>'_eq by (by100 simp)
        (** Use AI to conclude W' spans uniquely: conv W = conv W' with both W, W'
            AI subsets of V_\<tau>, V_\<sigma> respectively. Actually simpler: apply
            simplex_vertices_unique on \<sigma> \<inter> \<tau>. **)
        have hW_ai_early: "\<not> affine_dependent W"
          using hV\<tau>_ai hWV\<tau> affine_dependent_subset by (by100 blast)
        have hV\<tau>fin: "finite V\<tau>"
          using hV\<tau>sv unfolding geotop_simplex_vertices_def by (by100 blast)
        have hWfin: "finite W" using hWV\<tau> hV\<tau>fin finite_subset by (by100 blast)
        have hW_pos: "0 < card W" using hW_ne hWfin card_gt_0_iff by (by100 blast)
        have hW_card_eq: "card W = (card W - 1) + 1" using hW_pos by (by100 simp)
        have hW_gp: "geotop_general_position W (card W - 1)"
          by (rule geotop_ai_imp_general_position[OF hWfin hW_card_eq hW_ai_early])
        have hWsv: "geotop_simplex_vertices (\<sigma> \<inter> \<tau>) W"
          unfolding geotop_simplex_vertices_def
          using hWfin hW_card_eq hW_gp h_inter_hull by (by100 blast)
        have hW_\<sigma>_fin: "finite W_\<sigma>"
          using hW\<sigma>sv unfolding geotop_simplex_vertices_def by (by100 blast)
        have hW'fin: "finite W'" using hW'W\<sigma>_final hW_\<sigma>_fin finite_subset by (by100 blast)
        have hW\<sigma>_ai_early: "\<not> affine_dependent W_\<sigma>"
          by (rule geotop_general_position_imp_aff_indep[OF hW\<sigma>sv])
        have hW'_ai: "\<not> affine_dependent W'"
          using hW\<sigma>_ai_early hW'W\<sigma>_final affine_dependent_subset by (by100 blast)
        have hW'_pos: "0 < card W'" using hW'_ne hW'fin card_gt_0_iff by (by100 blast)
        have hW'_card_eq: "card W' = (card W' - 1) + 1" using hW'_pos by (by100 simp)
        have hW'_gp: "geotop_general_position W' (card W' - 1)"
          by (rule geotop_ai_imp_general_position[OF hW'fin hW'_card_eq hW'_ai])
        have hW'sv: "geotop_simplex_vertices (\<sigma> \<inter> \<tau>) W'"
          unfolding geotop_simplex_vertices_def
          using hW'fin hW'_card_eq hW'_gp h_inter_hull' by (by100 blast)
        have hWW': "W = W'" by (rule geotop_simplex_vertices_unique[OF hWsv hW'sv])
        have hWW\<sigma>: "W \<subseteq> W_\<sigma>" using hWW' hW'W\<sigma>_final by (by100 simp)
        (** W AI: W \<subseteq> V_\<tau>, V_\<tau> AI (since \<tau> is simplex), AI is closed under subsets. **)
        have hW_ai: "\<not> affine_dependent W"
          using hV\<tau>_ai hWV\<tau> affine_dependent_subset by (by100 blast)
        (** v \<in> \<sigma> \<inter> \<tau> = conv W. **)
        have hv_in_inter: "v \<in> \<sigma> \<inter> \<tau>" using hv\<sigma> hv\<tau> by (by100 blast)
        have hv_hullW: "v \<in> geotop_convex_hull W"
          using hv_in_inter h_inter_hull by (by100 simp)
        have h_W_eq_HOL: "geotop_convex_hull W = convex hull W"
          by (rule geotop_convex_hull_eq_HOL)
        have hv_hullW_HOL: "v \<in> convex hull W"
          using hv_hullW h_W_eq_HOL by (by100 simp)
        (** v is extreme in \<sigma>, hence in \<sigma> \<inter> \<tau> = conv W. **)
        have hW\<sigma>_ai: "\<not> affine_dependent W_\<sigma>"
          by (rule geotop_general_position_imp_aff_indep[OF hW\<sigma>sv])
        have hv_extr_W\<sigma>: "v extreme_point_of (convex hull W_\<sigma>)"
          using extreme_point_of_convex_hull_affine_independent[OF hW\<sigma>_ai] hvW\<sigma>
          by (by100 blast)
        (** v extreme in convex hull W_\<sigma> = \<sigma>, and v \<in> convex hull W \<subseteq> \<sigma>. **)
        have h\<sigma>_HOL: "\<sigma> = convex hull W_\<sigma>"
        proof -
          have "\<sigma> = geotop_convex_hull W_\<sigma>"
            using hW\<sigma>sv unfolding geotop_simplex_vertices_def by (by100 blast)
          also have "\<dots> = convex hull W_\<sigma>" by (rule geotop_convex_hull_eq_HOL)
          finally show ?thesis .
        qed
        have h_inter_sub_\<sigma>: "convex hull W \<subseteq> convex hull W_\<sigma>"
        proof -
          have h_int: "\<sigma> \<inter> \<tau> \<subseteq> \<sigma>" by (by100 blast)
          have "geotop_convex_hull W \<subseteq> \<sigma>" using h_int h_inter_hull by (by100 simp)
          hence h1: "geotop_convex_hull W \<subseteq> convex hull W_\<sigma>"
            using h\<sigma>_HOL by (by100 simp)
          have h_W_HOL: "geotop_convex_hull W = convex hull W"
            by (rule geotop_convex_hull_eq_HOL)
          show ?thesis using h1 h_W_HOL by (by100 simp)
        qed
        (** conv W face_of conv W_\<sigma> via face_of_convex_hull_affine_independent + W \<subseteq> W_\<sigma>. **)
        have h_face_HOL: "convex hull W face_of convex hull W_\<sigma>"
          using face_of_convex_hull_affine_independent[OF hW\<sigma>_ai_early] hWW\<sigma>
          by (by100 blast)
        (** v extreme in conv W (via extreme_point_of_face). **)
        have hv_extr_W: "v extreme_point_of (convex hull W)"
          using extreme_point_of_face[OF h_face_HOL] hv_extr_W\<sigma> hv_hullW_HOL
          by (by100 blast)
        have hvW: "v \<in> W"
          using extreme_point_of_convex_hull_affine_independent[OF hW_ai] hv_extr_W
          by (by100 blast)
        show "v \<in> V\<tau>" using hvW hWV\<tau> by (by100 blast)
      qed
      (** V_0 \<noteq> {}: from conv(g_inv V_0) being a simplex in K', nonempty. **)
      have h_convgV\<^sub>0_sim: "geotop_is_simplex (geotop_convex_hull (?g_inv ` V\<^sub>0))"
        using h_img_in_K' conjunct1[OF hK'_comp[unfolded geotop_is_complex_def]]
        by (by100 blast)
      have h_convgV\<^sub>0_ne: "geotop_convex_hull (?g_inv ` V\<^sub>0) \<noteq> {}"
      proof -
        obtain VV m n where hVV_card: "card VV = n + 1" and hVV_hull:
          "geotop_convex_hull (?g_inv ` V\<^sub>0) = geotop_convex_hull VV"
          using h_convgV\<^sub>0_sim unfolding geotop_is_simplex_def by (by100 blast)
        have hVV_ne: "VV \<noteq> {}" using hVV_card by (by100 auto)
        have "geotop_convex_hull VV \<noteq> {}"
          unfolding geotop_convex_hull_def hull_def using hVV_ne by (by100 blast)
        thus ?thesis using hVV_hull by (by100 simp)
      qed
      have hV\<^sub>0_ne: "V\<^sub>0 \<noteq> {}"
      proof
        assume h_empty: "V\<^sub>0 = {}"
        have h_giV_empty: "?g_inv ` V\<^sub>0 = {}" using h_empty by (by100 simp)
        have h_conv_eq: "geotop_convex_hull (?g_inv ` V\<^sub>0) = convex hull (?g_inv ` V\<^sub>0)"
          by (rule geotop_convex_hull_eq_HOL)
        have h_HOL_empty: "convex hull (?g_inv ` V\<^sub>0) = {}"
          using h_giV_empty by (by100 simp)
        have h_conv_empty: "geotop_convex_hull (?g_inv ` V\<^sub>0) = {}"
          using h_conv_eq h_HOL_empty by (by100 simp)
        show False using h_conv_empty h_convgV\<^sub>0_ne by (by100 simp)
      qed
      (** conv V_0 is a face of \<tau> (subset of vertices \<Rightarrow> face, nonempty). **)
      have h_face: "geotop_is_face (geotop_convex_hull V\<^sub>0) \<tau>"
        unfolding geotop_is_face_def
        using hV\<tau>sv hV\<^sub>0_ne hV\<^sub>0_sub_V\<tau> by (by100 blast)
      (** K.1 of L' (face-closed): face of \<tau> \<in> L' is in L'. **)
      have hL'_face_closed: "\<forall>\<sigma>\<in>L'. \<forall>\<tau>'. geotop_is_face \<tau>' \<sigma> \<longrightarrow> \<tau>' \<in> L'"
        using conjunct1[OF conjunct2[OF hL'_comp[unfolded geotop_is_complex_def]]]
        by (by100 blast)
      show "geotop_convex_hull V\<^sub>0 \<in> L'"
        using hL'_face_closed h\<tau>L' h_face by (by100 blast)
    qed
  qed
  have hiso_L'K': "geotop_isomorphic L' K'"
    unfolding geotop_isomorphic_def geotop_isomorphism_def
    using hiso_K'L'_vert hiso_K'L'_simp by (by100 blast)
  have hiso_K'L': "geotop_isomorphic K' L'"
    by (rule geotop_isomorphic_sym[OF hiso_L'K'])
  show ?thesis using hK'_K hiso_K'L' by (by100 blast)
qed

(** from Introduction: Theorem 2 (geotop.tex:184)
    LATEX VERSION: K \<sim>_c L iff |K| is the image of |L| under a PLH.
    Proof following early.tex Theorem 2: the (\<Rightarrow>) direction uses
    \<open>iso_induces_PLH\<close> applied to the common-subdivisions isomorphism; the
    (\<Leftarrow>) direction uses Theorem_GT_1 to merge the two PL-induced subdivisions
    into a common subdivision on which \<open>f\<close> is simplicially linear. **)
theorem Theorem_GT_2:
  fixes K :: "'a::euclidean_space set set" and L :: "'a set set"
  assumes hKfin: "finite K"
  assumes hLfin: "finite L"
  shows "geotop_comb_equiv K L
         \<longleftrightarrow> (\<exists>f. geotop_PLH L K f \<and> f ` (geotop_polyhedron L) = geotop_polyhedron K)"
proof -
  (** (\<Rightarrow>) K \<sim>_c L means subdivisions \<open>K' < K\<close>, \<open>L' < L\<close> with \<open>K' \<cong> L'\<close>. By
      \<open>iso_induces_PLH\<close> (applied to \<open>L' \<cong> K'\<close>), there is a PLH \<open>f: |L'| \<leftrightarrow> |K'|\<close>;
      because \<open>|L'| = |L|\<close> and \<open>|K'| = |K|\<close>, this is a PLH \<open>L \<leftrightarrow> K\<close>. **)
  have h_forward:
    "geotop_comb_equiv K L \<longrightarrow>
       (\<exists>f. geotop_PLH L K f \<and> f ` (geotop_polyhedron L) = geotop_polyhedron K)"
  proof
    assume hKL: "geotop_comb_equiv K L"
    obtain K' L' where hK'K: "geotop_is_subdivision K' K"
                   and hL'L: "geotop_is_subdivision L' L"
                   and hiso: "geotop_isomorphic K' L'"
      using hKL unfolding geotop_comb_equiv_def by (by100 blast)
    have hL'K': "geotop_isomorphic L' K'"
      by (rule geotop_isomorphic_sym[OF hiso])
    have hL'comp: "geotop_is_complex L'"
      using hL'L unfolding geotop_is_subdivision_def by (by100 blast)
    have hK'comp: "geotop_is_complex K'"
      using hK'K unfolding geotop_is_subdivision_def by (by100 blast)
    obtain f where hf_PLH: "geotop_PLH L' K' f"
               and hf_img: "f ` (geotop_polyhedron L') = geotop_polyhedron K'"
      using geotop_isomorphic_induces_PLH[OF hL'comp hK'comp hL'K'] by (by100 blast)
    have hpolyL: "geotop_polyhedron L' = geotop_polyhedron L"
      using hL'L unfolding geotop_is_subdivision_def by (by100 blast)
    have hpolyK: "geotop_polyhedron K' = geotop_polyhedron K"
      using hK'K unfolding geotop_is_subdivision_def by (by100 blast)
    (** Lift PLH L' \<leftrightarrow> K' to L \<leftrightarrow> K via \<open>geotop_PLH_lift\<close>. **)
    have hPLH_lift: "geotop_PLH L K f"
      by (rule geotop_PLH_lift[OF hL'L hK'K hf_PLH])
    have himg: "f ` (geotop_polyhedron L) = geotop_polyhedron K"
      using hf_img hpolyL hpolyK by (by100 simp)
    show "\<exists>f. geotop_PLH L K f \<and> f ` (geotop_polyhedron L) = geotop_polyhedron K"
      using hPLH_lift himg by (by100 blast)
  qed
  (** (\<Leftarrow>) Given a PLH \<open>f: |L| \<leftrightarrow> |K|\<close>, PL structure provides subdivisions \<open>L_1 < L\<close>
      on which \<open>f\<close> is linear into simplexes of K, and \<open>K_1 < K\<close> on which \<open>f^{-1}\<close> is
      linear into simplexes of L. Push \<open>L_1\<close> forward by \<open>f\<close> to a subdivision \<open>f(L_1) < K\<close>,
      apply Theorem_GT_1 to get a common refinement \<open>K_3 < f(L_1), K_1\<close>, pull back
      through \<open>f\<close> to \<open>L_3 < L_1\<close>, and note \<open>f: L_3 \<cong> K_3\<close>. Hence \<open>K \<sim>_c L\<close>. **)
  have h_backward:
    "(\<exists>f. geotop_PLH L K f \<and> f ` (geotop_polyhedron L) = geotop_polyhedron K) \<longrightarrow>
       geotop_comb_equiv K L"
  proof
    assume hexf: "\<exists>f. geotop_PLH L K f \<and> f ` (geotop_polyhedron L) = geotop_polyhedron K"
    obtain f where hf_PLH: "geotop_PLH L K f"
               and hf_img: "f ` (geotop_polyhedron L) = geotop_polyhedron K"
      using hexf by (by100 blast)
    (** (1) Extract forward/backward PL subdivisions witnessing linearity. **)
    have hf_PL_fwd: "geotop_PL_map L K f"
      using hf_PLH unfolding geotop_PLH_def by (by100 blast)
    obtain L\<^sub>1 where hL\<^sub>1L: "geotop_is_subdivision L\<^sub>1 L"
                 and hL\<^sub>1_lin: "\<forall>\<sigma>\<in>L\<^sub>1. \<exists>\<tau>\<in>K. (\<forall>x\<in>\<sigma>. f x \<in> \<tau>) \<and> geotop_linear_on \<sigma> f"
      using hf_PL_fwd unfolding geotop_PL_map_def by (by100 blast)
    (** (2) The image complex \<open>f(L\<^sub>1) = {f(\<sigma>) | \<sigma>\<in>L\<^sub>1}\<close> is a subdivision of K
          (push linear images of simplexes; f bij gives intersection compatibility). **)
    define fL\<^sub>1 where "fL\<^sub>1 = (\<lambda>\<sigma>. f ` \<sigma>) ` L\<^sub>1"
    (** Subdivision decomposes into three components: complex, refinement, polyhedron. **)
    (** (2a) |fL_1| = |K|: f(|L_1|) = f(|L|) = |K| (via bijection and |L_1|=|L|). **)
    have hL\<^sub>1_poly_L: "geotop_polyhedron L\<^sub>1 = geotop_polyhedron L"
      using hL\<^sub>1L unfolding geotop_is_subdivision_def by (by100 blast)
    have hf_bij_LK: "bij_betw f (geotop_polyhedron L) (geotop_polyhedron K)"
      using hf_PLH unfolding geotop_PLH_def by (by100 blast)
    have hf_img_L_K: "f ` (geotop_polyhedron L) = geotop_polyhedron K"
      using hf_bij_LK unfolding bij_betw_def by (by100 blast)
    have hfL\<^sub>1_poly_step1: "geotop_polyhedron fL\<^sub>1 = f ` (geotop_polyhedron L\<^sub>1)"
      unfolding fL\<^sub>1_def geotop_polyhedron_def by (by100 blast)
    have hfL\<^sub>1_poly: "geotop_polyhedron fL\<^sub>1 = geotop_polyhedron K"
      using hfL\<^sub>1_poly_step1 hL\<^sub>1_poly_L hf_img_L_K by (by100 simp)
    (** (2b) fL_1 is a complex: deferred. Decomposed into the four K-conditions
            (K.0 simplex, K.1 face-closed, K.2 intersections, K.3 local finiteness). **)
    have hL\<^sub>1_comp: "geotop_is_complex L\<^sub>1"
      using hL\<^sub>1L unfolding geotop_is_subdivision_def by (by100 blast)
    (** (b0) K.0: f(\<sigma>) is a simplex when f is linear on \<sigma> and \<sigma> is a simplex. **)
    have hfL\<^sub>1_K0: "\<forall>\<sigma>\<in>fL\<^sub>1. geotop_is_simplex \<sigma>"
    proof (rule ballI)
      fix \<sigma> assume h\<sigma>: "\<sigma> \<in> fL\<^sub>1"
      obtain \<sigma>_L where h\<sigma>_L_L\<^sub>1: "\<sigma>_L \<in> L\<^sub>1" and h\<sigma>_eq: "\<sigma> = f ` \<sigma>_L"
        using h\<sigma> unfolding fL\<^sub>1_def by (by100 blast)
      (** \<sigma>_L is a simplex (L_1 complex). **)
      have h_L\<^sub>1_simp_all: "\<forall>\<sigma>\<in>L\<^sub>1. geotop_is_simplex \<sigma>"
        by (rule conjunct1[OF hL\<^sub>1_comp[unfolded geotop_is_complex_def]])
      have h\<sigma>_L_sim: "geotop_is_simplex \<sigma>_L"
        using h_L\<^sub>1_simp_all h\<sigma>_L_L\<^sub>1 by (by100 blast)
      (** f is linear on \<sigma>_L (from hL_1_lin). **)
      have h\<sigma>_L_lin_raw: "\<exists>\<tau>\<in>K. (\<forall>x\<in>\<sigma>_L. f x \<in> \<tau>) \<and> geotop_linear_on \<sigma>_L f"
        using hL\<^sub>1_lin h\<sigma>_L_L\<^sub>1 by (by100 blast)
      have h\<sigma>_L_lin: "geotop_linear_on \<sigma>_L f"
        using h\<sigma>_L_lin_raw by (by100 blast)
      (** \<sigma>_L \<subseteq> |L_1| = |L|, so f inj on \<sigma>_L (from f bij |L| \<leftrightarrow> |K|). **)
      have h\<sigma>_L_in_L: "\<sigma>_L \<subseteq> geotop_polyhedron L"
        using h\<sigma>_L_L\<^sub>1 hL\<^sub>1_poly_L unfolding geotop_polyhedron_def by (by100 blast)
      have hf_inj_L: "inj_on f (geotop_polyhedron L)"
        using hf_bij_LK unfolding bij_betw_def by (by100 blast)
      have hf_inj_\<sigma>_L: "inj_on f \<sigma>_L"
        using hf_inj_L h\<sigma>_L_in_L inj_on_subset by (by100 blast)
      show "geotop_is_simplex \<sigma>"
        using h\<sigma>_eq geotop_linear_inj_image_is_simplex[OF h\<sigma>_L_lin hf_inj_\<sigma>_L h\<sigma>_L_sim]
        by (by100 simp)
    qed
    (** (b1) K.1: fL_1 is closed under faces. Use geotop_linear_inj_image_face_preimage
            to pull back a face of f(\<sigma>_L) to a face of \<sigma>_L in L_1, then push it forward. **)
    have h_L\<^sub>1_face_closed: "\<forall>\<sigma>\<in>L\<^sub>1. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> L\<^sub>1"
      by (rule conjunct1[OF conjunct2[OF hL\<^sub>1_comp[unfolded geotop_is_complex_def]]])
    have h_L\<^sub>1_simp_all_for_K1: "\<forall>\<sigma>\<in>L\<^sub>1. geotop_is_simplex \<sigma>"
      by (rule conjunct1[OF hL\<^sub>1_comp[unfolded geotop_is_complex_def]])
    have hfL\<^sub>1_K1: "\<forall>\<sigma>\<in>fL\<^sub>1. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> fL\<^sub>1"
    proof (intro ballI allI impI)
      fix \<sigma> \<tau>
      assume h\<sigma>: "\<sigma> \<in> fL\<^sub>1" and h_face: "geotop_is_face \<tau> \<sigma>"
      obtain \<sigma>_L where h\<sigma>_L_L\<^sub>1: "\<sigma>_L \<in> L\<^sub>1" and h\<sigma>_eq: "\<sigma> = f ` \<sigma>_L"
        using h\<sigma> unfolding fL\<^sub>1_def by (by100 blast)
      have h\<sigma>_L_sim: "geotop_is_simplex \<sigma>_L"
        using h_L\<^sub>1_simp_all_for_K1 h\<sigma>_L_L\<^sub>1 by (by100 blast)
      have h\<sigma>_L_lin_raw: "\<exists>\<tau>'\<in>K. (\<forall>x\<in>\<sigma>_L. f x \<in> \<tau>') \<and> geotop_linear_on \<sigma>_L f"
        using hL\<^sub>1_lin h\<sigma>_L_L\<^sub>1 by (by100 blast)
      have h\<sigma>_L_lin: "geotop_linear_on \<sigma>_L f" using h\<sigma>_L_lin_raw by (by100 blast)
      have h\<sigma>_L_in_L: "\<sigma>_L \<subseteq> geotop_polyhedron L"
        using h\<sigma>_L_L\<^sub>1 hL\<^sub>1_poly_L unfolding geotop_polyhedron_def by (by100 blast)
      have hf_inj_L: "inj_on f (geotop_polyhedron L)"
        using hf_bij_LK unfolding bij_betw_def by (by100 blast)
      have hf_inj_\<sigma>_L: "inj_on f \<sigma>_L"
        using hf_inj_L h\<sigma>_L_in_L inj_on_subset by (by100 blast)
      (** Pull back \<tau> (a face of f(\<sigma>_L)) to a face of \<sigma>_L. **)
      have h_face_sub: "geotop_is_face \<tau> (f ` \<sigma>_L)"
        using h_face h\<sigma>_eq by (by100 simp)
      obtain \<tau>_L where h\<tau>_L_face: "geotop_is_face \<tau>_L \<sigma>_L"
                   and h\<tau>_eq: "\<tau> = f ` \<tau>_L"
        using geotop_linear_inj_image_face_preimage[OF h\<sigma>_L_lin hf_inj_\<sigma>_L h\<sigma>_L_sim h_face_sub]
        by (by100 blast)
      have h\<tau>_L_L\<^sub>1: "\<tau>_L \<in> L\<^sub>1" using h_L\<^sub>1_face_closed h\<sigma>_L_L\<^sub>1 h\<tau>_L_face by (by100 blast)
      show "\<tau> \<in> fL\<^sub>1" unfolding fL\<^sub>1_def using h\<tau>_L_L\<^sub>1 h\<tau>_eq by (by100 blast)
    qed
    (** (b2) K.2: f(\<sigma>_L1) \<inter> f(\<sigma>_L2) = f(\<sigma>_L1 \<inter> \<sigma>_L2) via f inj;
            \<sigma>_L1 \<inter> \<sigma>_L2 is face of both (K.2 of L_1); apply
            geotop_linear_inj_image_preserves_face. **)
    have h_L\<^sub>1_K2: "\<forall>\<sigma>\<in>L\<^sub>1. \<forall>\<tau>\<in>L\<^sub>1. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                     geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
      by (rule conjunct1[OF conjunct2[OF conjunct2[OF
              hL\<^sub>1_comp[unfolded geotop_is_complex_def]]]])
    have hfL\<^sub>1_K2: "\<forall>\<sigma>\<in>fL\<^sub>1. \<forall>\<tau>\<in>fL\<^sub>1. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                     geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    proof (intro ballI impI)
      fix \<sigma> \<tau> assume h\<sigma>: "\<sigma> \<in> fL\<^sub>1" and h\<tau>: "\<tau> \<in> fL\<^sub>1"
      assume h_nonempty: "\<sigma> \<inter> \<tau> \<noteq> {}"
      obtain \<sigma>_L where h\<sigma>_L_L\<^sub>1: "\<sigma>_L \<in> L\<^sub>1" and h\<sigma>_eq: "\<sigma> = f ` \<sigma>_L"
        using h\<sigma> unfolding fL\<^sub>1_def by (by100 blast)
      obtain \<tau>_L where h\<tau>_L_L\<^sub>1: "\<tau>_L \<in> L\<^sub>1" and h\<tau>_eq: "\<tau> = f ` \<tau>_L"
        using h\<tau> unfolding fL\<^sub>1_def by (by100 blast)
      (** Simplex status for \<sigma>_L, \<tau>_L. **)
      have h_L\<^sub>1_simp_all: "\<forall>\<sigma>\<in>L\<^sub>1. geotop_is_simplex \<sigma>"
        by (rule conjunct1[OF hL\<^sub>1_comp[unfolded geotop_is_complex_def]])
      have h\<sigma>_L_sim: "geotop_is_simplex \<sigma>_L"
        using h_L\<^sub>1_simp_all h\<sigma>_L_L\<^sub>1 by (by100 blast)
      have h\<tau>_L_sim: "geotop_is_simplex \<tau>_L"
        using h_L\<^sub>1_simp_all h\<tau>_L_L\<^sub>1 by (by100 blast)
      (** Linearity on \<sigma>_L, \<tau>_L. **)
      have h\<sigma>_L_lin_raw: "\<exists>\<tau>'\<in>K. (\<forall>x\<in>\<sigma>_L. f x \<in> \<tau>') \<and> geotop_linear_on \<sigma>_L f"
        using hL\<^sub>1_lin h\<sigma>_L_L\<^sub>1 by (by100 blast)
      have h\<sigma>_L_lin: "geotop_linear_on \<sigma>_L f" using h\<sigma>_L_lin_raw by (by100 blast)
      have h\<tau>_L_lin_raw: "\<exists>\<tau>'\<in>K. (\<forall>x\<in>\<tau>_L. f x \<in> \<tau>') \<and> geotop_linear_on \<tau>_L f"
        using hL\<^sub>1_lin h\<tau>_L_L\<^sub>1 by (by100 blast)
      have h\<tau>_L_lin: "geotop_linear_on \<tau>_L f" using h\<tau>_L_lin_raw by (by100 blast)
      (** \<sigma>_L, \<tau>_L \<subseteq> |L|; f inj on union. **)
      have h\<sigma>_L_in_L: "\<sigma>_L \<subseteq> geotop_polyhedron L"
        using h\<sigma>_L_L\<^sub>1 hL\<^sub>1_poly_L unfolding geotop_polyhedron_def by (by100 blast)
      have h\<tau>_L_in_L: "\<tau>_L \<subseteq> geotop_polyhedron L"
        using h\<tau>_L_L\<^sub>1 hL\<^sub>1_poly_L unfolding geotop_polyhedron_def by (by100 blast)
      have hf_inj_L: "inj_on f (geotop_polyhedron L)"
        using hf_bij_LK unfolding bij_betw_def by (by100 blast)
      have hf_inj_\<sigma>_L: "inj_on f \<sigma>_L"
        using hf_inj_L h\<sigma>_L_in_L inj_on_subset by (by100 blast)
      have hf_inj_\<tau>_L: "inj_on f \<tau>_L"
        using hf_inj_L h\<tau>_L_in_L inj_on_subset by (by100 blast)
      (** f(\<sigma>_L) \<inter> f(\<tau>_L) = f(\<sigma>_L \<inter> \<tau>_L) via inj_on_image_Int. **)
      have h_image_int_raw: "f ` (\<sigma>_L \<inter> \<tau>_L) = f ` \<sigma>_L \<inter> f ` \<tau>_L"
        by (rule inj_on_image_Int[OF hf_inj_L h\<sigma>_L_in_L h\<tau>_L_in_L])
      have h_image_int: "f ` \<sigma>_L \<inter> f ` \<tau>_L = f ` (\<sigma>_L \<inter> \<tau>_L)"
        using h_image_int_raw by (by100 simp)
      have h_sigma_tau_nonempty: "\<sigma>_L \<inter> \<tau>_L \<noteq> {}"
        using h_nonempty h\<sigma>_eq h\<tau>_eq h_image_int by (by100 auto)
      (** K.2 for L_1: \<sigma>_L \<inter> \<tau>_L is face of both \<sigma>_L, \<tau>_L. **)
      have h_intface_\<sigma>_L: "geotop_is_face (\<sigma>_L \<inter> \<tau>_L) \<sigma>_L"
        using h_L\<^sub>1_K2 h\<sigma>_L_L\<^sub>1 h\<tau>_L_L\<^sub>1 h_sigma_tau_nonempty by (by100 blast)
      have h_intface_\<tau>_L: "geotop_is_face (\<sigma>_L \<inter> \<tau>_L) \<tau>_L"
        using h_L\<^sub>1_K2 h\<sigma>_L_L\<^sub>1 h\<tau>_L_L\<^sub>1 h_sigma_tau_nonempty by (by100 blast)
      (** Image of face is face. **)
      have h_face_\<sigma>: "geotop_is_face (f ` (\<sigma>_L \<inter> \<tau>_L)) (f ` \<sigma>_L)"
        by (rule geotop_linear_inj_image_preserves_face[OF h\<sigma>_L_lin hf_inj_\<sigma>_L h_intface_\<sigma>_L])
      have h_face_\<tau>: "geotop_is_face (f ` (\<sigma>_L \<inter> \<tau>_L)) (f ` \<tau>_L)"
        by (rule geotop_linear_inj_image_preserves_face[OF h\<tau>_L_lin hf_inj_\<tau>_L h_intface_\<tau>_L])
      have h_int_eq: "\<sigma> \<inter> \<tau> = f ` (\<sigma>_L \<inter> \<tau>_L)"
        using h\<sigma>_eq h\<tau>_eq h_image_int by (by100 simp)
      show "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
        using h_int_eq h\<sigma>_eq h\<tau>_eq h_face_\<sigma> h_face_\<tau> by (by100 simp)
    qed
    (** (b3) K.3: local finiteness. f is continuous (PL-homeomorphism),
            so pull back L_1's local-finiteness witness through f. **)
    (** For finite fL_1, local finiteness is trivial: take U = UNIV. **)
    have hL\<^sub>1fin: "finite L\<^sub>1"
      by (rule geotop_subdivision_of_finite_is_finite[OF hLfin hL\<^sub>1L])
    have hfL\<^sub>1fin: "finite fL\<^sub>1" unfolding fL\<^sub>1_def using hL\<^sub>1fin by (by100 simp)
    have hfL\<^sub>1_K3: "\<forall>\<sigma>\<in>fL\<^sub>1. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>fL\<^sub>1. \<tau> \<inter> U \<noteq> {}}"
    proof (rule ballI)
      fix \<sigma> assume h\<sigma>: "\<sigma> \<in> fL\<^sub>1"
      have h_sub_fin: "finite {\<tau>\<in>fL\<^sub>1. \<tau> \<inter> UNIV \<noteq> {}}"
        using hfL\<^sub>1fin by (by100 simp)
      have h_open: "open (UNIV :: 'a set)" by (by100 simp)
      show "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>fL\<^sub>1. \<tau> \<inter> U \<noteq> {}}"
        using h_open h_sub_fin by (by100 blast)
    qed
    have hfL\<^sub>1_comp: "geotop_is_complex fL\<^sub>1"
      unfolding geotop_is_complex_def
      using hfL\<^sub>1_K0 hfL\<^sub>1_K1 hfL\<^sub>1_K2 hfL\<^sub>1_K3 by (by100 blast)
    (** (2c) fL_1 refines K: each f(\<sigma>) for \<sigma> \<in> L_1 sits in some \<tau> \<in> K (from hL_1_lin). **)
    have hfL\<^sub>1_ref: "geotop_refines fL\<^sub>1 K"
    proof -
      have h_elem: "\<And>s. s \<in> fL\<^sub>1 \<Longrightarrow> \<exists>\<sigma>\<in>L\<^sub>1. s = f ` \<sigma>"
        unfolding fL\<^sub>1_def by (by100 blast)
      have h_map: "\<And>\<sigma>. \<sigma> \<in> L\<^sub>1 \<Longrightarrow> \<exists>\<tau>\<in>K. \<forall>x\<in>\<sigma>. f x \<in> \<tau>"
        using hL\<^sub>1_lin by (by100 meson)
      show ?thesis
        unfolding geotop_refines_def
      proof (rule ballI)
        fix s assume hs: "s \<in> fL\<^sub>1"
        from h_elem[OF hs] obtain \<sigma> where h\<sigma>: "\<sigma> \<in> L\<^sub>1" and hs_eq: "s = f ` \<sigma>"
          by (by100 blast)
        from h_map[OF h\<sigma>] obtain \<tau> where h\<tau>: "\<tau> \<in> K" and hfx: "\<forall>x\<in>\<sigma>. f x \<in> \<tau>"
          by (by100 blast)
        have hfimg: "f ` \<sigma> \<subseteq> \<tau>" using hfx by (by100 blast)
        show "\<exists>h\<in>K. s \<subseteq> h" using h\<tau> hfimg hs_eq by (by100 blast)
      qed
    qed
    have hfL\<^sub>1_sub: "geotop_is_subdivision fL\<^sub>1 K"
    proof -
      have hKcomp_local: "geotop_is_complex K"
        using hf_PLH unfolding geotop_PLH_def geotop_PL_map_def
              geotop_is_subdivision_def by (by100 blast)
      show ?thesis
        unfolding geotop_is_subdivision_def
        using hfL\<^sub>1_comp hKcomp_local hfL\<^sub>1_ref hfL\<^sub>1_poly by (by100 blast)
    qed
    (** (3) Similarly obtain a subdivision \<open>K\<^sub>1 < K\<close> on which \<open>f^{-1}\<close> is linear. **)
    have hf_PL_bwd: "geotop_PL_map K L (inv_into (geotop_polyhedron L) f)"
      using hf_PLH unfolding geotop_PLH_def by (by100 blast)
    obtain K\<^sub>1 where hK\<^sub>1K: "geotop_is_subdivision K\<^sub>1 K"
                and hK\<^sub>1_lin: "\<forall>\<sigma>\<in>K\<^sub>1. \<exists>\<tau>\<in>L.
                                  (\<forall>x\<in>\<sigma>. inv_into (geotop_polyhedron L) f x \<in> \<tau>)
                                  \<and> geotop_linear_on \<sigma> (inv_into (geotop_polyhedron L) f)"
      using hf_PL_bwd unfolding geotop_PL_map_def by (by100 blast)
    (** (4) Apply Theorem_GT_1 to get a common subdivision \<open>K\<^sub>3\<close> of \<open>fL\<^sub>1\<close> and \<open>K\<^sub>1\<close>
          (uses \<open>finite K\<close> hypothesis). **)
    obtain K\<^sub>3 where hK\<^sub>3_fL\<^sub>1: "geotop_is_subdivision K\<^sub>3 fL\<^sub>1"
                 and hK\<^sub>3_K\<^sub>1: "geotop_is_subdivision K\<^sub>3 K\<^sub>1"
      using Theorem_GT_1[OF hKfin hfL\<^sub>1_sub hK\<^sub>1K] by (by100 blast)
    (** (5) Pull \<open>K\<^sub>3\<close> back through \<open>f\<close> to get \<open>L\<^sub>3 < L\<^sub>1\<close> with \<open>f: L\<^sub>3 \<cong> K\<^sub>3\<close>. **)
    define L\<^sub>3 where "L\<^sub>3 = (\<lambda>\<sigma>. inv_into (geotop_polyhedron L) f ` \<sigma>) ` K\<^sub>3"
    (** L_3 is a subdivision of L: decomposed into (i) complex, (ii)
        polyhedron equality, (iii) refinement. **)
    (** L_3 is a complex: L_3 = f_inv ` K_3, K_3 is a complex, and f_inv
        is a bijective PL map. Decompose into K.0/K.1/K.2/K.3. **)
    have hK\<^sub>3_comp: "geotop_is_complex K\<^sub>3"
      using hK\<^sub>3_K\<^sub>1 unfolding geotop_is_subdivision_def by (by100 blast)
    (** (i) K.0: each f_inv(\<sigma>) is a simplex. \<sigma> \<in> K_3 is a simplex, f_inv is
           linear on K_1-simplex \<supseteq> \<sigma> (via K_3 < K_1 + linear_on_sub_simplex),
           f_inv inj globally \<Rightarrow> use geotop_linear_inj_image_is_simplex. **)
    have hK\<^sub>3_ref_K\<^sub>1_ref: "geotop_refines K\<^sub>3 K\<^sub>1"
      using hK\<^sub>3_K\<^sub>1 unfolding geotop_is_subdivision_def by (by100 blast)
    have hL\<^sub>3_K0: "\<forall>\<sigma>\<in>L\<^sub>3. geotop_is_simplex \<sigma>"
    proof (rule ballI)
      fix \<sigma> assume h\<sigma>L\<^sub>3: "\<sigma> \<in> L\<^sub>3"
      obtain \<sigma>_K where h\<sigma>_K_K\<^sub>3: "\<sigma>_K \<in> K\<^sub>3"
                  and h\<sigma>_eq: "\<sigma> = inv_into (geotop_polyhedron L) f ` \<sigma>_K"
        using h\<sigma>L\<^sub>3 unfolding L\<^sub>3_def by (by100 blast)
      (** \<sigma>_K is a simplex (K_3 complex). **)
      have h_K\<^sub>3_simp_all: "\<forall>\<sigma>\<in>K\<^sub>3. geotop_is_simplex \<sigma>"
        by (rule conjunct1[OF hK\<^sub>3_comp[unfolded geotop_is_complex_def]])
      have h\<sigma>_K_sim: "geotop_is_simplex \<sigma>_K"
        using h_K\<^sub>3_simp_all h\<sigma>_K_K\<^sub>3 by (by100 blast)
      (** \<sigma>_K \<subseteq> some \<sigma>_1 \<in> K_1 (K_3 refines K_1). **)
      obtain \<sigma>_1 where h\<sigma>_1_K\<^sub>1: "\<sigma>_1 \<in> K\<^sub>1" and h\<sigma>_K_sub: "\<sigma>_K \<subseteq> \<sigma>_1"
        using h\<sigma>_K_K\<^sub>3 hK\<^sub>3_ref_K\<^sub>1_ref unfolding geotop_refines_def by (by100 blast)
      (** f_inv linear on \<sigma>_1 (from hK_1_lin). **)
      have h\<sigma>_1_lin_raw: "\<exists>\<tau>\<in>L. (\<forall>x\<in>\<sigma>_1. inv_into (geotop_polyhedron L) f x \<in> \<tau>) \<and>
                            geotop_linear_on \<sigma>_1 (inv_into (geotop_polyhedron L) f)"
        using hK\<^sub>1_lin h\<sigma>_1_K\<^sub>1 by (by100 blast)
      have h\<sigma>_1_lin: "geotop_linear_on \<sigma>_1 (inv_into (geotop_polyhedron L) f)"
        using h\<sigma>_1_lin_raw by (by100 blast)
      (** f_inv linear on \<sigma>_K (via sub_simplex from \<sigma>_1). **)
      have h\<sigma>_K_lin: "geotop_linear_on \<sigma>_K (inv_into (geotop_polyhedron L) f)"
        by (rule geotop_linear_on_sub_simplex[OF h\<sigma>_1_lin h\<sigma>_K_sim h\<sigma>_K_sub])
      (** f_inv inj on \<sigma>_K (from global bij |K| \<leftrightarrow> |L|). **)
      have hK\<^sub>3_K_sub: "geotop_is_subdivision K\<^sub>3 K"
        by (rule geotop_is_subdivision_trans[OF hK\<^sub>1K hK\<^sub>3_K\<^sub>1])
      have hK\<^sub>3_poly: "geotop_polyhedron K\<^sub>3 = geotop_polyhedron K"
        using hK\<^sub>3_K_sub unfolding geotop_is_subdivision_def by (by100 blast)
      have h\<sigma>_K_in_K: "\<sigma>_K \<subseteq> geotop_polyhedron K"
        using h\<sigma>_K_K\<^sub>3 hK\<^sub>3_poly unfolding geotop_polyhedron_def by (by100 blast)
      have hf_inv_bij_local: "bij_betw (inv_into (geotop_polyhedron L) f)
                                         (geotop_polyhedron K) (geotop_polyhedron L)"
        by (rule bij_betw_inv_into[OF hf_bij_LK])
      have hf_inv_inj_K: "inj_on (inv_into (geotop_polyhedron L) f) (geotop_polyhedron K)"
        using hf_inv_bij_local unfolding bij_betw_def by (by100 blast)
      have hf_inv_inj_\<sigma>_K: "inj_on (inv_into (geotop_polyhedron L) f) \<sigma>_K"
        using hf_inv_inj_K h\<sigma>_K_in_K inj_on_subset by (by100 blast)
      show "geotop_is_simplex \<sigma>"
        using h\<sigma>_eq geotop_linear_inj_image_is_simplex[OF h\<sigma>_K_lin hf_inv_inj_\<sigma>_K h\<sigma>_K_sim]
        by (by100 simp)
    qed
    (** (ii) K.1: L_3 closed under faces. Pull back via face_preimage helper. **)
    have h_K\<^sub>3_face_closed: "\<forall>\<sigma>\<in>K\<^sub>3. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K\<^sub>3"
      by (rule conjunct1[OF conjunct2[OF hK\<^sub>3_comp[unfolded geotop_is_complex_def]]])
    have hK\<^sub>3_ref_K\<^sub>1_ref_K1: "geotop_refines K\<^sub>3 K\<^sub>1"
      using hK\<^sub>3_K\<^sub>1 unfolding geotop_is_subdivision_def by (by100 blast)
    have h_K\<^sub>3_simp_all_K1: "\<forall>\<sigma>\<in>K\<^sub>3. geotop_is_simplex \<sigma>"
      by (rule conjunct1[OF hK\<^sub>3_comp[unfolded geotop_is_complex_def]])
    have hK\<^sub>3_K_sub_K1: "geotop_is_subdivision K\<^sub>3 K"
      by (rule geotop_is_subdivision_trans[OF hK\<^sub>1K hK\<^sub>3_K\<^sub>1])
    have hK\<^sub>3_poly_K1: "geotop_polyhedron K\<^sub>3 = geotop_polyhedron K"
      using hK\<^sub>3_K_sub_K1 unfolding geotop_is_subdivision_def by (by100 blast)
    have hf_inv_bij_local_K1: "bij_betw (inv_into (geotop_polyhedron L) f)
                                         (geotop_polyhedron K) (geotop_polyhedron L)"
      by (rule bij_betw_inv_into[OF hf_bij_LK])
    have hf_inv_inj_K_K1: "inj_on (inv_into (geotop_polyhedron L) f) (geotop_polyhedron K)"
      using hf_inv_bij_local_K1 unfolding bij_betw_def by (by100 blast)
    have hL\<^sub>3_K1: "\<forall>\<sigma>\<in>L\<^sub>3. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> L\<^sub>3"
    proof (intro ballI allI impI)
      fix \<sigma> \<tau>
      assume h\<sigma>: "\<sigma> \<in> L\<^sub>3" and h_face: "geotop_is_face \<tau> \<sigma>"
      obtain \<sigma>_K where h\<sigma>_K_K\<^sub>3: "\<sigma>_K \<in> K\<^sub>3"
                  and h\<sigma>_eq: "\<sigma> = inv_into (geotop_polyhedron L) f ` \<sigma>_K"
        using h\<sigma> unfolding L\<^sub>3_def by (by100 blast)
      have h\<sigma>_K_sim: "geotop_is_simplex \<sigma>_K"
        using h_K\<^sub>3_simp_all_K1 h\<sigma>_K_K\<^sub>3 by (by100 blast)
      obtain \<sigma>_1 where h\<sigma>_1_K\<^sub>1: "\<sigma>_1 \<in> K\<^sub>1" and h\<sigma>_K_sub: "\<sigma>_K \<subseteq> \<sigma>_1"
        using h\<sigma>_K_K\<^sub>3 hK\<^sub>3_ref_K\<^sub>1_ref_K1 unfolding geotop_refines_def by (by100 blast)
      have h\<sigma>_1_lin_raw: "\<exists>\<tau>'\<in>L. (\<forall>x\<in>\<sigma>_1. inv_into (geotop_polyhedron L) f x \<in> \<tau>') \<and>
                            geotop_linear_on \<sigma>_1 (inv_into (geotop_polyhedron L) f)"
        using hK\<^sub>1_lin h\<sigma>_1_K\<^sub>1 by (by100 blast)
      have h\<sigma>_1_lin: "geotop_linear_on \<sigma>_1 (inv_into (geotop_polyhedron L) f)"
        using h\<sigma>_1_lin_raw by (by100 blast)
      have h\<sigma>_K_lin: "geotop_linear_on \<sigma>_K (inv_into (geotop_polyhedron L) f)"
        by (rule geotop_linear_on_sub_simplex[OF h\<sigma>_1_lin h\<sigma>_K_sim h\<sigma>_K_sub])
      have h\<sigma>_K_in_K: "\<sigma>_K \<subseteq> geotop_polyhedron K"
        using h\<sigma>_K_K\<^sub>3 hK\<^sub>3_poly_K1 unfolding geotop_polyhedron_def by (by100 blast)
      have hf_inv_inj_\<sigma>_K: "inj_on (inv_into (geotop_polyhedron L) f) \<sigma>_K"
        using hf_inv_inj_K_K1 h\<sigma>_K_in_K inj_on_subset by (by100 blast)
      (** Pull back face via helper. **)
      have h_face_sub: "geotop_is_face \<tau> (inv_into (geotop_polyhedron L) f ` \<sigma>_K)"
        using h_face h\<sigma>_eq by (by100 simp)
      obtain \<tau>_K where h\<tau>_K_face: "geotop_is_face \<tau>_K \<sigma>_K"
                   and h\<tau>_eq: "\<tau> = inv_into (geotop_polyhedron L) f ` \<tau>_K"
        using geotop_linear_inj_image_face_preimage[OF h\<sigma>_K_lin hf_inv_inj_\<sigma>_K h\<sigma>_K_sim h_face_sub]
        by (by100 blast)
      have h\<tau>_K_K\<^sub>3: "\<tau>_K \<in> K\<^sub>3" using h_K\<^sub>3_face_closed h\<sigma>_K_K\<^sub>3 h\<tau>_K_face by (by100 blast)
      show "\<tau> \<in> L\<^sub>3" unfolding L\<^sub>3_def using h\<tau>_K_K\<^sub>3 h\<tau>_eq by (by100 blast)
    qed
    (** (iii) K.2: pairwise intersections are faces. Same pattern as hfL_1_K2
             but with f_inv on K_3 side (f_inv linear on K_1 \<supseteq> K_3 via sub_simplex). **)
    have h_K\<^sub>3_K2: "\<forall>\<sigma>\<in>K\<^sub>3. \<forall>\<tau>\<in>K\<^sub>3. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                     geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
      by (rule conjunct1[OF conjunct2[OF conjunct2[OF
              hK\<^sub>3_comp[unfolded geotop_is_complex_def]]]])
    have hK\<^sub>3_ref_K\<^sub>1_ref_b: "geotop_refines K\<^sub>3 K\<^sub>1"
      using hK\<^sub>3_K\<^sub>1 unfolding geotop_is_subdivision_def by (by100 blast)
    have h_K\<^sub>3_simp_all: "\<forall>\<sigma>\<in>K\<^sub>3. geotop_is_simplex \<sigma>"
      by (rule conjunct1[OF hK\<^sub>3_comp[unfolded geotop_is_complex_def]])
    have hK\<^sub>3_K_sub_b: "geotop_is_subdivision K\<^sub>3 K"
      by (rule geotop_is_subdivision_trans[OF hK\<^sub>1K hK\<^sub>3_K\<^sub>1])
    have hK\<^sub>3_poly_b: "geotop_polyhedron K\<^sub>3 = geotop_polyhedron K"
      using hK\<^sub>3_K_sub_b unfolding geotop_is_subdivision_def by (by100 blast)
    have hf_inv_bij_local_b: "bij_betw (inv_into (geotop_polyhedron L) f)
                                         (geotop_polyhedron K) (geotop_polyhedron L)"
      by (rule bij_betw_inv_into[OF hf_bij_LK])
    have hf_inv_inj_K_b: "inj_on (inv_into (geotop_polyhedron L) f) (geotop_polyhedron K)"
      using hf_inv_bij_local_b unfolding bij_betw_def by (by100 blast)
    have hL\<^sub>3_K2: "\<forall>\<sigma>\<in>L\<^sub>3. \<forall>\<tau>\<in>L\<^sub>3. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                    geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    proof (intro ballI impI)
      fix \<sigma> \<tau> assume h\<sigma>: "\<sigma> \<in> L\<^sub>3" and h\<tau>: "\<tau> \<in> L\<^sub>3"
      assume h_nonempty: "\<sigma> \<inter> \<tau> \<noteq> {}"
      obtain \<sigma>_K where h\<sigma>_K_K\<^sub>3: "\<sigma>_K \<in> K\<^sub>3"
                  and h\<sigma>_eq: "\<sigma> = inv_into (geotop_polyhedron L) f ` \<sigma>_K"
        using h\<sigma> unfolding L\<^sub>3_def by (by100 blast)
      obtain \<tau>_K where h\<tau>_K_K\<^sub>3: "\<tau>_K \<in> K\<^sub>3"
                  and h\<tau>_eq: "\<tau> = inv_into (geotop_polyhedron L) f ` \<tau>_K"
        using h\<tau> unfolding L\<^sub>3_def by (by100 blast)
      have h\<sigma>_K_sim: "geotop_is_simplex \<sigma>_K"
        using h_K\<^sub>3_simp_all h\<sigma>_K_K\<^sub>3 by (by100 blast)
      (** f_inv linear on \<sigma>_K, \<tau>_K via sub_simplex from their K_1-supersets. **)
      obtain \<sigma>_1 where h\<sigma>_1_K\<^sub>1: "\<sigma>_1 \<in> K\<^sub>1" and h\<sigma>_K_sub: "\<sigma>_K \<subseteq> \<sigma>_1"
        using h\<sigma>_K_K\<^sub>3 hK\<^sub>3_ref_K\<^sub>1_ref_b unfolding geotop_refines_def by (by100 blast)
      obtain \<tau>_1 where h\<tau>_1_K\<^sub>1: "\<tau>_1 \<in> K\<^sub>1" and h\<tau>_K_sub: "\<tau>_K \<subseteq> \<tau>_1"
        using h\<tau>_K_K\<^sub>3 hK\<^sub>3_ref_K\<^sub>1_ref_b unfolding geotop_refines_def by (by100 blast)
      have h\<sigma>_1_lin_raw: "\<exists>\<tau>'\<in>L. (\<forall>x\<in>\<sigma>_1. inv_into (geotop_polyhedron L) f x \<in> \<tau>') \<and>
                            geotop_linear_on \<sigma>_1 (inv_into (geotop_polyhedron L) f)"
        using hK\<^sub>1_lin h\<sigma>_1_K\<^sub>1 by (by100 blast)
      have h\<sigma>_1_lin: "geotop_linear_on \<sigma>_1 (inv_into (geotop_polyhedron L) f)"
        using h\<sigma>_1_lin_raw by (by100 blast)
      have h\<sigma>_K_lin: "geotop_linear_on \<sigma>_K (inv_into (geotop_polyhedron L) f)"
        by (rule geotop_linear_on_sub_simplex[OF h\<sigma>_1_lin h\<sigma>_K_sim h\<sigma>_K_sub])
      have h\<sigma>_K_in_K: "\<sigma>_K \<subseteq> geotop_polyhedron K"
        using h\<sigma>_K_K\<^sub>3 hK\<^sub>3_poly_b unfolding geotop_polyhedron_def by (by100 blast)
      have h\<tau>_K_in_K: "\<tau>_K \<subseteq> geotop_polyhedron K"
        using h\<tau>_K_K\<^sub>3 hK\<^sub>3_poly_b unfolding geotop_polyhedron_def by (by100 blast)
      have hf_inv_inj_\<sigma>_K: "inj_on (inv_into (geotop_polyhedron L) f) \<sigma>_K"
        using hf_inv_inj_K_b h\<sigma>_K_in_K inj_on_subset by (by100 blast)
      (** f_inv(\<sigma>_K) \<inter> f_inv(\<tau>_K) = f_inv(\<sigma>_K \<inter> \<tau>_K) via inj_on_image_Int. **)
      have h_image_int_raw: "inv_into (geotop_polyhedron L) f ` (\<sigma>_K \<inter> \<tau>_K)
                               = inv_into (geotop_polyhedron L) f ` \<sigma>_K
                                 \<inter> inv_into (geotop_polyhedron L) f ` \<tau>_K"
        by (rule inj_on_image_Int[OF hf_inv_inj_K_b h\<sigma>_K_in_K h\<tau>_K_in_K])
      have h_sigma_tau_K_nonempty: "\<sigma>_K \<inter> \<tau>_K \<noteq> {}"
        using h_nonempty h\<sigma>_eq h\<tau>_eq h_image_int_raw by (by100 auto)
      have h_intface_\<sigma>_K: "geotop_is_face (\<sigma>_K \<inter> \<tau>_K) \<sigma>_K"
        using h_K\<^sub>3_K2 h\<sigma>_K_K\<^sub>3 h\<tau>_K_K\<^sub>3 h_sigma_tau_K_nonempty by (by100 blast)
      (** Image of face is face. Apply the helper for \<sigma>_K. **)
      have h_face_\<sigma>: "geotop_is_face (inv_into (geotop_polyhedron L) f ` (\<sigma>_K \<inter> \<tau>_K))
                                       (inv_into (geotop_polyhedron L) f ` \<sigma>_K)"
        by (rule geotop_linear_inj_image_preserves_face[OF h\<sigma>_K_lin hf_inv_inj_\<sigma>_K h_intface_\<sigma>_K])
      (** And for \<tau>_K. **)
      have h\<tau>_1_lin_raw: "\<exists>\<tau>'\<in>L. (\<forall>x\<in>\<tau>_1. inv_into (geotop_polyhedron L) f x \<in> \<tau>') \<and>
                            geotop_linear_on \<tau>_1 (inv_into (geotop_polyhedron L) f)"
        using hK\<^sub>1_lin h\<tau>_1_K\<^sub>1 by (by100 blast)
      have h\<tau>_1_lin: "geotop_linear_on \<tau>_1 (inv_into (geotop_polyhedron L) f)"
        using h\<tau>_1_lin_raw by (by100 blast)
      have h\<tau>_K_sim: "geotop_is_simplex \<tau>_K"
        using h_K\<^sub>3_simp_all h\<tau>_K_K\<^sub>3 by (by100 blast)
      have h\<tau>_K_lin: "geotop_linear_on \<tau>_K (inv_into (geotop_polyhedron L) f)"
        by (rule geotop_linear_on_sub_simplex[OF h\<tau>_1_lin h\<tau>_K_sim h\<tau>_K_sub])
      have hf_inv_inj_\<tau>_K: "inj_on (inv_into (geotop_polyhedron L) f) \<tau>_K"
        using hf_inv_inj_K_b h\<tau>_K_in_K inj_on_subset by (by100 blast)
      have h_intface_\<tau>_K: "geotop_is_face (\<sigma>_K \<inter> \<tau>_K) \<tau>_K"
        using h_K\<^sub>3_K2 h\<sigma>_K_K\<^sub>3 h\<tau>_K_K\<^sub>3 h_sigma_tau_K_nonempty by (by100 blast)
      have h_face_\<tau>: "geotop_is_face (inv_into (geotop_polyhedron L) f ` (\<sigma>_K \<inter> \<tau>_K))
                                       (inv_into (geotop_polyhedron L) f ` \<tau>_K)"
        by (rule geotop_linear_inj_image_preserves_face[OF h\<tau>_K_lin hf_inv_inj_\<tau>_K h_intface_\<tau>_K])
      have h_int_eq: "\<sigma> \<inter> \<tau> = inv_into (geotop_polyhedron L) f ` (\<sigma>_K \<inter> \<tau>_K)"
        using h\<sigma>_eq h\<tau>_eq h_image_int_raw by (by100 simp)
      show "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
        using h_int_eq h\<sigma>_eq h\<tau>_eq h_face_\<sigma> h_face_\<tau> by (by100 simp)
    qed
    (** (iv) K.3: local finiteness. For finite L_3, U = UNIV suffices. **)
    have hK\<^sub>1fin: "finite K\<^sub>1"
      by (rule geotop_subdivision_of_finite_is_finite[OF hKfin hK\<^sub>1K])
    have hK\<^sub>3fin: "finite K\<^sub>3"
      by (rule geotop_subdivision_of_finite_is_finite[OF hK\<^sub>1fin hK\<^sub>3_K\<^sub>1])
    have hL\<^sub>3fin: "finite L\<^sub>3" unfolding L\<^sub>3_def using hK\<^sub>3fin by (by100 simp)
    have hL\<^sub>3_K3: "\<forall>\<sigma>\<in>L\<^sub>3. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>L\<^sub>3. \<tau> \<inter> U \<noteq> {}}"
    proof (rule ballI)
      fix \<sigma> assume h\<sigma>: "\<sigma> \<in> L\<^sub>3"
      have h_sub_fin: "finite {\<tau>\<in>L\<^sub>3. \<tau> \<inter> UNIV \<noteq> {}}"
        using hL\<^sub>3fin by (by100 simp)
      have h_open: "open (UNIV :: 'a set)" by (by100 simp)
      show "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>L\<^sub>3. \<tau> \<inter> U \<noteq> {}}"
        using h_open h_sub_fin by (by100 blast)
    qed
    have hL\<^sub>3_complex: "geotop_is_complex L\<^sub>3"
      unfolding geotop_is_complex_def
      using hL\<^sub>3_K0 hL\<^sub>3_K1 hL\<^sub>3_K2 hL\<^sub>3_K3 by (by100 blast)
    (** Polyhedron equality: \<open>|L_3| = f_inv(|K_3|) = f_inv(|K|) = |L|\<close>. **)
    have hK\<^sub>3_K: "geotop_is_subdivision K\<^sub>3 K"
      by (rule geotop_is_subdivision_trans[OF hK\<^sub>1K hK\<^sub>3_K\<^sub>1])
    have hK\<^sub>3_poly_eq_K: "geotop_polyhedron K\<^sub>3 = geotop_polyhedron K"
      using hK\<^sub>3_K unfolding geotop_is_subdivision_def by (by100 blast)
    have hf_bij: "bij_betw f (geotop_polyhedron L) (geotop_polyhedron K)"
      using hf_PLH unfolding geotop_PLH_def by (by100 blast)
    have hf_inv_bij: "bij_betw (inv_into (geotop_polyhedron L) f)
                                  (geotop_polyhedron K) (geotop_polyhedron L)"
      by (rule bij_betw_inv_into[OF hf_bij])
    have hf_inv_img_K: "(inv_into (geotop_polyhedron L) f) ` (geotop_polyhedron K)
                          = geotop_polyhedron L"
      using hf_inv_bij unfolding bij_betw_def by (by100 blast)
    have hL\<^sub>3_poly_step: "geotop_polyhedron L\<^sub>3 =
                         (inv_into (geotop_polyhedron L) f) ` (geotop_polyhedron K\<^sub>3)"
      unfolding L\<^sub>3_def geotop_polyhedron_def by (by100 blast)
    have hL\<^sub>3_poly: "geotop_polyhedron L\<^sub>3 = geotop_polyhedron L"
      using hL\<^sub>3_poly_step hK\<^sub>3_poly_eq_K hf_inv_img_K by (by100 simp)
    (** Each simplex of L_3 sits in some simplex of L via the PL structure.
        Proof: K_3 refines K_1 (subdivision), and f_inv is linear on each simplex
        of K_1 mapping into some simplex of L. Hence each s_3 \<in> K_3 satisfies
        s_3 \<subseteq> s_1 \<in> K_1 for some s_1, and f_inv(s_3) \<subseteq> f_inv(s_1) \<subseteq> \<tau> \<in> L. **)
    have hK\<^sub>3_ref_K\<^sub>1: "geotop_refines K\<^sub>3 K\<^sub>1"
      using hK\<^sub>3_K\<^sub>1 unfolding geotop_is_subdivision_def by (by100 blast)
    have hL\<^sub>3_ref: "geotop_refines L\<^sub>3 L"
    proof -
      (** (i) Each element of L_3 is f_inv(\<sigma>_3) for some \<sigma>_3 \<in> K_3. **)
      have h_elem: "\<And>s. s \<in> L\<^sub>3 \<Longrightarrow>
                       \<exists>\<sigma>\<^sub>3\<in>K\<^sub>3. s = inv_into (geotop_polyhedron L) f ` \<sigma>\<^sub>3"
        unfolding L\<^sub>3_def by (by100 blast)
      (** (ii) Each \<sigma>_3 \<in> K_3 sits in some \<sigma>_1 \<in> K_1 (from K_3 refines K_1). **)
      have h_refK: "\<And>\<sigma>\<^sub>3. \<sigma>\<^sub>3 \<in> K\<^sub>3 \<Longrightarrow> \<exists>\<sigma>\<^sub>1\<in>K\<^sub>1. \<sigma>\<^sub>3 \<subseteq> \<sigma>\<^sub>1"
        using hK\<^sub>3_ref_K\<^sub>1 unfolding geotop_refines_def by (by100 blast)
      (** (iii) f_inv maps each \<sigma>_1 \<in> K_1 into some \<tau> \<in> L. **)
      have h_mapL: "\<And>\<sigma>\<^sub>1. \<sigma>\<^sub>1 \<in> K\<^sub>1 \<Longrightarrow>
                       \<exists>\<tau>\<in>L. \<forall>x\<in>\<sigma>\<^sub>1. inv_into (geotop_polyhedron L) f x \<in> \<tau>"
        using hK\<^sub>1_lin by (by100 meson)
      (** (iv) Combine: each s \<in> L_3 sits in some \<tau> \<in> L. **)
      show ?thesis
        unfolding geotop_refines_def
      proof (rule ballI)
        fix s assume hs: "s \<in> L\<^sub>3"
        from h_elem[OF hs] obtain \<sigma>\<^sub>3
          where h\<sigma>\<^sub>3: "\<sigma>\<^sub>3 \<in> K\<^sub>3"
            and hs_eq: "s = inv_into (geotop_polyhedron L) f ` \<sigma>\<^sub>3" by (by100 blast)
        from h_refK[OF h\<sigma>\<^sub>3] obtain \<sigma>\<^sub>1
          where h\<sigma>\<^sub>1: "\<sigma>\<^sub>1 \<in> K\<^sub>1" and hsub: "\<sigma>\<^sub>3 \<subseteq> \<sigma>\<^sub>1" by (by100 blast)
        from h_mapL[OF h\<sigma>\<^sub>1] obtain \<tau>
          where h\<tau>: "\<tau> \<in> L"
            and hg_into: "\<forall>x\<in>\<sigma>\<^sub>1. inv_into (geotop_polyhedron L) f x \<in> \<tau>" by (by100 blast)
        have hg_img: "inv_into (geotop_polyhedron L) f ` \<sigma>\<^sub>3 \<subseteq> \<tau>"
          using hg_into hsub by (by100 blast)
        show "\<exists>h\<in>L. s \<subseteq> h"
          using h\<tau> hg_img hs_eq by (by100 blast)
      qed
    qed
    have hLcomp: "geotop_is_complex L"
      using hf_PL_fwd unfolding geotop_PL_map_def geotop_is_subdivision_def
      by (by100 blast)
    have hL\<^sub>3_L: "geotop_is_subdivision L\<^sub>3 L"
      unfolding geotop_is_subdivision_def
      using hL\<^sub>3_complex hLcomp hL\<^sub>3_ref hL\<^sub>3_poly by (by100 blast)
    (** L_3 \<cong> K_3 via f restricted to vertices. L_3 = f_inv \<sup>\` K_3, so
        vertices of L_3 are f_inv-images of vertices of K_3. f is a bijection
        |L| \<leftrightarrow> |K| mapping each vertex of L_3 to a vertex of K_3. **)
    (** (a) vertex bijection: f maps vertices of L_3 to vertices of K_3 bijectively.
        Key steps:
        1. V(L_3) = {v : {v} \<in> L_3} = {f_inv w : {w} \<in> K_3} = f_inv \`\` V(K_3)
        2. f restricted to f_inv \`\` V(K_3) bijects to V(K_3) (since f is inverse of
           f_inv on |K|). **)
    have hV_L\<^sub>3_eq: "geotop_complex_vertices L\<^sub>3 = {v. {v} \<in> L\<^sub>3}"
      by (rule geotop_complex_vertices_eq_0_simplexes[OF hL\<^sub>3_complex])
    have hV_K\<^sub>3_eq: "geotop_complex_vertices K\<^sub>3 = {v. {v} \<in> K\<^sub>3}"
      by (rule geotop_complex_vertices_eq_0_simplexes[OF hK\<^sub>3_comp])
    (** Characterize 0-simplexes of L_3 as f_inv images of 0-simplexes of K_3. **)
    have hf_inv_inj_K: "inj_on (inv_into (geotop_polyhedron L) f) (geotop_polyhedron K)"
      using hf_inv_bij unfolding bij_betw_def by (by100 blast)
    have hL\<^sub>3_singletons: "{v. {v} \<in> L\<^sub>3}
                            = inv_into (geotop_polyhedron L) f ` {w. {w} \<in> K\<^sub>3}"
    proof (rule set_eqI, rule iffI)
      fix v assume hv: "v \<in> {v. {v} \<in> L\<^sub>3}"
      hence hv_L\<^sub>3: "{v} \<in> L\<^sub>3" by (by100 simp)
      (** L_3 = (\<lambda>\<sigma>. f_inv \`\` \<sigma>) \`\` K_3. **)
      obtain \<sigma> where h\<sigma>K\<^sub>3: "\<sigma> \<in> K\<^sub>3"
                  and h\<sigma>_eq: "{v} = inv_into (geotop_polyhedron L) f ` \<sigma>"
        using hv_L\<^sub>3 unfolding L\<^sub>3_def by (by100 blast)
      (** \<sigma> \<subseteq> |K_3| = |K|; f_inv is injective on |K|, so |f_inv(\<sigma>)| = |\<sigma>|. **)
      have h\<sigma>_in_K: "\<sigma> \<subseteq> geotop_polyhedron K"
        using h\<sigma>K\<^sub>3 hK\<^sub>3_poly_eq_K unfolding geotop_polyhedron_def by (by100 blast)
      have hf_inv_inj_\<sigma>: "inj_on (inv_into (geotop_polyhedron L) f) \<sigma>"
        using hf_inv_inj_K h\<sigma>_in_K inj_on_subset by (by100 blast)
      have h_img_card: "card (inv_into (geotop_polyhedron L) f ` \<sigma>) = card \<sigma>"
        by (rule card_image[OF hf_inv_inj_\<sigma>])
      have h\<sigma>_card: "card \<sigma> = card {v}"
        using h_img_card h\<sigma>_eq by (by100 simp)
      have h\<sigma>_single_card: "card \<sigma> = 1" using h\<sigma>_card by (by100 simp)
      have h\<sigma>_fin: "finite \<sigma>" using h\<sigma>_single_card card_gt_0_iff by (by100 fastforce)
      obtain w where h\<sigma>_sing: "\<sigma> = {w}"
        using h\<sigma>_single_card card_1_singletonE[of \<sigma>] h\<sigma>_fin by (by100 blast)
      have hw_K\<^sub>3: "{w} \<in> K\<^sub>3" using h\<sigma>K\<^sub>3 h\<sigma>_sing by (by100 simp)
      have hv_eq: "v = inv_into (geotop_polyhedron L) f w"
        using h\<sigma>_eq h\<sigma>_sing by (by100 simp)
      show "v \<in> inv_into (geotop_polyhedron L) f ` {w. {w} \<in> K\<^sub>3}"
        using hw_K\<^sub>3 hv_eq by (by100 blast)
    next
      fix v assume hv: "v \<in> inv_into (geotop_polyhedron L) f ` {w. {w} \<in> K\<^sub>3}"
      obtain w where hw_K\<^sub>3: "{w} \<in> K\<^sub>3"
                 and hvw: "v = inv_into (geotop_polyhedron L) f w"
        using hv by (by100 blast)
      have h_img: "inv_into (geotop_polyhedron L) f ` {w} = {v}"
        using hvw by (by100 simp)
      have h_img_in_L\<^sub>3: "inv_into (geotop_polyhedron L) f ` {w} \<in> L\<^sub>3"
        using hw_K\<^sub>3 unfolding L\<^sub>3_def by (by100 blast)
      show "v \<in> {v. {v} \<in> L\<^sub>3}"
        using h_img h_img_in_L\<^sub>3 by (by100 simp)
    qed
    have hV_L\<^sub>3_img: "geotop_complex_vertices L\<^sub>3 =
                       inv_into (geotop_polyhedron L) f ` geotop_complex_vertices K\<^sub>3"
      using hV_L\<^sub>3_eq hV_K\<^sub>3_eq hL\<^sub>3_singletons by (by100 simp)
    (** V(K_3) \<subseteq> |K_3| = |K| (vertices lie in polyhedron). **)
    have hV_K\<^sub>3_in_K: "geotop_complex_vertices K\<^sub>3 \<subseteq> geotop_polyhedron K"
    proof
      fix v assume hv: "v \<in> geotop_complex_vertices K\<^sub>3"
      hence hv_sing: "{v} \<in> K\<^sub>3" using hV_K\<^sub>3_eq by (by100 simp)
      hence hv_in_K\<^sub>3: "v \<in> geotop_polyhedron K\<^sub>3"
        unfolding geotop_polyhedron_def by (by100 blast)
      show "v \<in> geotop_polyhedron K"
        using hv_in_K\<^sub>3 hK\<^sub>3_poly_eq_K by (by100 simp)
    qed
    (** f_inv is bijective |K| \<leftrightarrow> |L|; restricts to V(K_3) \<to> V(L_3) bij. **)
    have hf_inv_inj_K: "inj_on (inv_into (geotop_polyhedron L) f) (geotop_polyhedron K)"
      using hf_inv_bij unfolding bij_betw_def by (by100 blast)
    have hf_inv_inj_VK\<^sub>3: "inj_on (inv_into (geotop_polyhedron L) f) (geotop_complex_vertices K\<^sub>3)"
      using hf_inv_inj_K hV_K\<^sub>3_in_K inj_on_subset by (by100 blast)
    have hf_inv_bij_V: "bij_betw (inv_into (geotop_polyhedron L) f)
                                   (geotop_complex_vertices K\<^sub>3)
                                   (geotop_complex_vertices L\<^sub>3)"
      unfolding bij_betw_def
      using hf_inv_inj_VK\<^sub>3 hV_L\<^sub>3_img by (by100 simp)
    (** f is inverse of f_inv on the relevant sets. **)
    have h_inv_of_inv_bij:
      "bij_betw (inv_into (geotop_complex_vertices K\<^sub>3)
                          (inv_into (geotop_polyhedron L) f))
                (geotop_complex_vertices L\<^sub>3)
                (geotop_complex_vertices K\<^sub>3)"
      by (rule bij_betw_inv_into[OF hf_inv_bij_V])
    (** Show the double inverse acts as f on V(L_3). **)
    have h_agree: "\<forall>v\<in>geotop_complex_vertices L\<^sub>3.
                     inv_into (geotop_complex_vertices K\<^sub>3)
                              (inv_into (geotop_polyhedron L) f) v = f v"
    proof (rule ballI)
      fix v assume hv: "v \<in> geotop_complex_vertices L\<^sub>3"
      obtain w where hwK\<^sub>3: "w \<in> geotop_complex_vertices K\<^sub>3"
                 and hvw: "v = inv_into (geotop_polyhedron L) f w"
        using hv hV_L\<^sub>3_img by (by100 blast)
      have hw_K: "w \<in> geotop_polyhedron K" using hwK\<^sub>3 hV_K\<^sub>3_in_K by (by100 blast)
      (** inv_into V(K_3) f_inv v = w (since v = f_inv w and f_inv inj on V(K_3)). **)
      have h_double_step: "inv_into (geotop_complex_vertices K\<^sub>3)
                                    (inv_into (geotop_polyhedron L) f)
                                    (inv_into (geotop_polyhedron L) f w) = w"
        using hf_inv_inj_VK\<^sub>3 hwK\<^sub>3 inv_into_f_f[of "inv_into (geotop_polyhedron L) f"
                                                   "geotop_complex_vertices K\<^sub>3" w]
        by (by100 blast)
      have h_double: "inv_into (geotop_complex_vertices K\<^sub>3)
                               (inv_into (geotop_polyhedron L) f) v = w"
        using h_double_step hvw by (by100 simp)
      (** f v = f (f_inv w) = w. **)
      have h_fv_step: "f (inv_into (geotop_polyhedron L) f w) = w"
        using bij_betw_inv_into_right[OF hf_bij hw_K] by (by100 simp)
      have h_fv: "f v = w" using h_fv_step hvw by (by100 simp)
      show "inv_into (geotop_complex_vertices K\<^sub>3)
                     (inv_into (geotop_polyhedron L) f) v = f v"
        using h_double h_fv by (by100 simp)
    qed
    have h_agree_single: "\<And>v. v \<in> geotop_complex_vertices L\<^sub>3 \<Longrightarrow>
                            inv_into (geotop_complex_vertices K\<^sub>3)
                                     (inv_into (geotop_polyhedron L) f) v = f v"
      using h_agree by (by100 blast)
    have h_cong_eq: "bij_betw (inv_into (geotop_complex_vertices K\<^sub>3)
                                        (inv_into (geotop_polyhedron L) f))
                              (geotop_complex_vertices L\<^sub>3)
                              (geotop_complex_vertices K\<^sub>3)
                       = bij_betw f (geotop_complex_vertices L\<^sub>3) (geotop_complex_vertices K\<^sub>3)"
      by (rule bij_betw_cong[OF h_agree_single])
    have hiso_vert: "bij_betw f (geotop_complex_vertices L\<^sub>3) (geotop_complex_vertices K\<^sub>3)"
      using h_inv_of_inv_bij h_cong_eq by (by100 simp)
    (** (b) simplex correspondence: conv V \<in> L_3 \<longleftrightarrow> conv (f\<sup>\`V) \<in> K_3.
        Key idea: V \<subseteq> V(L_3) = f_inv \<sup>\` V(K_3), so W = f V \<subseteq> V(K_3), V = f_inv \<sup>\` W.
        Conv V = f_inv \<sup>\` conv W via hull_eq (f_inv linear on K_1-simplex \<supseteq> \<tau>).
        Then conv V \<in> L_3 = f_inv \<sup>\` K_3 iff conv W \<in> K_3 (bijective correspondence). **)
    (** f_inv is injective on |K| (bij inverse). **)
    have hf_inv_inj_K_hsimp: "inj_on (inv_into (geotop_polyhedron L) f) (geotop_polyhedron K)"
      using hf_inv_bij unfolding bij_betw_def by (by100 blast)
    have hiso_simp: "\<forall>V. V \<subseteq> geotop_complex_vertices L\<^sub>3 \<longrightarrow>
                       (geotop_convex_hull V \<in> L\<^sub>3 \<longleftrightarrow> geotop_convex_hull (f ` V) \<in> K\<^sub>3)"
    proof (intro allI impI)
      fix V assume hV_sub: "V \<subseteq> geotop_complex_vertices L\<^sub>3"
      (** Auxiliary: W = f V, and V = f_inv ` W, W \<subseteq> V(K_3). **)
      have hf_V_sub_VK\<^sub>3: "f ` V \<subseteq> geotop_complex_vertices K\<^sub>3"
      proof
        fix w assume hw: "w \<in> f ` V"
        obtain v where hvV: "v \<in> V" and hwv: "w = f v" using hw by (by100 blast)
        have hv_VL\<^sub>3: "v \<in> geotop_complex_vertices L\<^sub>3" using hvV hV_sub by (by100 blast)
        have hv_fimg: "v \<in> inv_into (geotop_polyhedron L) f ` geotop_complex_vertices K\<^sub>3"
          using hv_VL\<^sub>3 hV_L\<^sub>3_img by (by100 simp)
        obtain w0 where hw0: "w0 \<in> geotop_complex_vertices K\<^sub>3"
                    and hv_eq: "v = inv_into (geotop_polyhedron L) f w0"
          using hv_fimg by (by100 blast)
        have hw0_K: "w0 \<in> geotop_polyhedron K" using hw0 hV_K\<^sub>3_in_K by (by100 blast)
        have hfv: "f v = w0"
          using bij_betw_inv_into_right[OF hf_bij hw0_K] hv_eq by (by100 simp)
        show "w \<in> geotop_complex_vertices K\<^sub>3" using hwv hfv hw0 by (by100 simp)
      qed
      show "geotop_convex_hull V \<in> L\<^sub>3 \<longleftrightarrow> geotop_convex_hull (f ` V) \<in> K\<^sub>3"
      proof (rule iffI)
        assume hV_L\<^sub>3: "geotop_convex_hull V \<in> L\<^sub>3"
        obtain \<tau> where h\<tau>K\<^sub>3: "\<tau> \<in> K\<^sub>3"
                    and h_conv_eq_geo: "geotop_convex_hull V = inv_into (geotop_polyhedron L) f ` \<tau>"
          using hV_L\<^sub>3 unfolding L\<^sub>3_def by (by100 blast)
        (** \<tau> is a simplex (K.0 of K_3). **)
        have h\<tau>_sim: "geotop_is_simplex \<tau>"
          using h\<tau>K\<^sub>3 conjunct1[OF hK\<^sub>3_comp[unfolded geotop_is_complex_def]]
          by (by100 blast)
        (** f V \<subseteq> \<tau>: V \<subseteq> conv V = f_inv \<tau>, applying f gives V \<subseteq> f(f_inv \<tau>) = \<tau>. **)
        have hfV_sub_\<tau>: "f ` V \<subseteq> \<tau>"
        proof
          fix w assume hw: "w \<in> f ` V"
          obtain v where hvV: "v \<in> V" and hwv: "w = f v" using hw by (by100 blast)
          have hv_hull: "v \<in> geotop_convex_hull V"
            unfolding geotop_convex_hull_def hull_def using hvV by (by100 blast)
          have hv_in_fi: "v \<in> inv_into (geotop_polyhedron L) f ` \<tau>"
            using hv_hull h_conv_eq_geo by (by100 simp)
          obtain w' where hw'\<tau>: "w' \<in> \<tau>"
                      and hv_eq: "v = inv_into (geotop_polyhedron L) f w'"
            using hv_in_fi by (by100 blast)
          have h\<tau>_sub_K: "\<tau> \<subseteq> geotop_polyhedron K"
            using h\<tau>K\<^sub>3 hK\<^sub>3_poly_eq_K unfolding geotop_polyhedron_def by (by100 blast)
          have hw'_K: "w' \<in> geotop_polyhedron K" using hw'\<tau> h\<tau>_sub_K by (by100 blast)
          have hfv_eq: "f v = w'"
            using bij_betw_inv_into_right[OF hf_bij hw'_K] hv_eq by (by100 simp)
          show "w \<in> \<tau>" using hwv hfv_eq hw'\<tau> by (by100 simp)
        qed
        (** conv(f V) \<subseteq> \<tau> (\<tau> is convex as a simplex). **)
        have h\<tau>_convex: "convex \<tau>"
        proof -
          obtain V\<tau> m n where h_V\<tau>_eq: "\<tau> = geotop_convex_hull V\<tau>"
            using h\<tau>_sim unfolding geotop_is_simplex_def by (by100 blast)
          have "\<tau> = convex hull V\<tau>"
            using h_V\<tau>_eq geotop_convex_hull_eq_HOL by (by100 simp)
          thus ?thesis using convex_convex_hull by (by100 simp)
        qed
        have h\<tau>_geo_conv: "geotop_convex \<tau>"
          using h\<tau>_convex geotop_convex_iff_HOL_convex[of \<tau>] by (by100 simp)
        have h_convfV_sub_\<tau>: "geotop_convex_hull (f ` V) \<subseteq> \<tau>"
          unfolding geotop_convex_hull_def hull_def using hfV_sub_\<tau> h\<tau>_geo_conv
          by (by100 blast)
        (** conv V is a simplex in L_3. Extract its vertex set V_L_3 \<subseteq> V (extreme pts). **)
        have h_convV_simp: "geotop_is_simplex (geotop_convex_hull V)"
          using hV_L\<^sub>3 conjunct1[OF hL\<^sub>3_complex[unfolded geotop_is_complex_def]]
          by (by100 blast)
        obtain V_L\<^sub>3 where hV_L\<^sub>3sv: "geotop_simplex_vertices (geotop_convex_hull V) V_L\<^sub>3"
          using h_convV_simp unfolding geotop_is_simplex_def
                geotop_simplex_vertices_def by (by100 blast)
        have hV_L\<^sub>3_ai: "\<not> affine_dependent V_L\<^sub>3"
          by (rule geotop_general_position_imp_aff_indep[OF hV_L\<^sub>3sv])
        have h_V_L\<^sub>3_hull: "geotop_convex_hull V = geotop_convex_hull V_L\<^sub>3"
          using hV_L\<^sub>3sv unfolding geotop_simplex_vertices_def by (by100 blast)
        have h_HOL_hulls_eq: "convex hull V = convex hull V_L\<^sub>3"
        proof -
          have h1: "convex hull V = geotop_convex_hull V"
            by (rule geotop_convex_hull_eq_HOL[symmetric])
          have h2: "geotop_convex_hull V_L\<^sub>3 = convex hull V_L\<^sub>3"
            by (rule geotop_convex_hull_eq_HOL)
          show ?thesis using h1 h_V_L\<^sub>3_hull h2 by (by100 simp)
        qed
        have hV_L\<^sub>3_sub_V: "V_L\<^sub>3 \<subseteq> V"
        proof
          fix v assume hv: "v \<in> V_L\<^sub>3"
          have h_extr_VL: "v extreme_point_of (convex hull V_L\<^sub>3)"
            using extreme_point_of_convex_hull_affine_independent[OF hV_L\<^sub>3_ai] hv
            by (by100 blast)
          have h_extr_V: "v extreme_point_of (convex hull V)"
            using h_extr_VL h_HOL_hulls_eq by (by100 simp)
          show "v \<in> V" by (rule extreme_point_of_convex_hull[OF h_extr_V])
        qed
        (** Extract V_\<tau> = simplex_vertices of \<tau>. **)
        obtain V\<tau> where hV\<tau>sv: "geotop_simplex_vertices \<tau> V\<tau>"
          using h\<tau>_sim unfolding geotop_is_simplex_def
                geotop_simplex_vertices_def by (by100 blast)
        have hV\<tau>_ai: "\<not> affine_dependent V\<tau>"
          by (rule geotop_general_position_imp_aff_indep[OF hV\<tau>sv])
        obtain mV nV where hV\<tau>fin: "finite V\<tau>" and hV\<tau>card: "card V\<tau> = nV + 1"
                       and hV\<tau>nm: "nV \<le> mV" and hV\<tau>gp: "geotop_general_position V\<tau> mV"
                       and h\<tau>hull: "\<tau> = geotop_convex_hull V\<tau>"
          using hV\<tau>sv unfolding geotop_simplex_vertices_def by (by100 blast)
        (** f_inv linear on \<tau>: \<tau> \<in> K_3 < K_1, each K_3-simplex \<subseteq> K_1-simplex. **)
        have hK\<^sub>3_ref_K\<^sub>1: "geotop_refines K\<^sub>3 K\<^sub>1"
          using hK\<^sub>3_K\<^sub>1 unfolding geotop_is_subdivision_def by (by100 blast)
        obtain \<sigma>\<^sub>K\<^sub>1 where h\<sigma>K1: "\<sigma>\<^sub>K\<^sub>1 \<in> K\<^sub>1" and h\<tau>_sub_K1: "\<tau> \<subseteq> \<sigma>\<^sub>K\<^sub>1"
          using h\<tau>K\<^sub>3 hK\<^sub>3_ref_K\<^sub>1 unfolding geotop_refines_def by (by100 blast)
        have h_lin_\<sigma>\<^sub>K\<^sub>1: "geotop_linear_on \<sigma>\<^sub>K\<^sub>1 (inv_into (geotop_polyhedron L) f)"
          using hK\<^sub>1_lin h\<sigma>K1 by (by100 blast)
        have h_lin_\<tau>: "geotop_linear_on \<tau> (inv_into (geotop_polyhedron L) f)"
          by (rule geotop_linear_on_sub_simplex[OF h_lin_\<sigma>\<^sub>K\<^sub>1 h\<tau>_sim h\<tau>_sub_K1])
        (** Bary-preservation of f_inv on V_\<tau>. **)
        obtain V\<tau>' where hV\<tau>'sv: "geotop_simplex_vertices \<tau> V\<tau>'"
                     and h_prop_lin\<tau>: "\<forall>\<alpha>. (\<forall>v\<in>V\<tau>'. 0 \<le> \<alpha> v) \<and> sum \<alpha> V\<tau>' = 1 \<longrightarrow>
                                           inv_into (geotop_polyhedron L) f
                                              (\<Sum>v\<in>V\<tau>'. \<alpha> v *\<^sub>R v)
                                           = (\<Sum>v\<in>V\<tau>'. \<alpha> v *\<^sub>R
                                                inv_into (geotop_polyhedron L) f v)"
          using h_lin_\<tau> unfolding geotop_linear_on_def by (by100 blast)
        have hV\<tau>'_eq: "V\<tau>' = V\<tau>" by (rule geotop_simplex_vertices_unique[OF hV\<tau>'sv hV\<tau>sv])
        have h_bary_V\<tau>: "\<And>\<alpha>. (\<forall>v\<in>V\<tau>. 0 \<le> \<alpha> v) \<Longrightarrow> sum \<alpha> V\<tau> = 1 \<Longrightarrow>
                             inv_into (geotop_polyhedron L) f (\<Sum>v\<in>V\<tau>. \<alpha> v *\<^sub>R v)
                             = (\<Sum>v\<in>V\<tau>. \<alpha> v *\<^sub>R inv_into (geotop_polyhedron L) f v)"
          using h_prop_lin\<tau> hV\<tau>'_eq by (by100 blast)
        (** f_inv inj on conv V_\<tau> = \<tau> (\<subseteq> |K|). **)
        have h\<tau>_sub_K_simp: "\<tau> \<subseteq> geotop_polyhedron K"
          using h\<tau>K\<^sub>3 hK\<^sub>3_poly_eq_K unfolding geotop_polyhedron_def by (by100 blast)
        have h_inj_\<tau>: "inj_on (inv_into (geotop_polyhedron L) f) \<tau>"
          using hf_inv_inj_K h\<tau>_sub_K_simp inj_on_subset by (by100 blast)
        have h\<tau>_conv_hull: "\<tau> = convex hull V\<tau>"
        proof -
          have "\<tau> = geotop_convex_hull V\<tau>" by (rule h\<tau>hull)
          also have "\<dots> = convex hull V\<tau>" by (rule geotop_convex_hull_eq_HOL)
          finally show ?thesis .
        qed
        have h_inj_convVt: "inj_on (inv_into (geotop_polyhedron L) f) (convex hull V\<tau>)"
          using h_inj_\<tau> h\<tau>_conv_hull by (by100 simp)
        (** Apply preserves_ai: f_inv V_\<tau> is AI. **)
        have h_fiVt_ai: "\<not> affine_dependent (inv_into (geotop_polyhedron L) f ` V\<tau>)"
          by (rule geotop_bary_lin_inj_preserves_ai[OF hV\<tau>fin h_inj_convVt hV\<tau>_ai h_bary_V\<tau>])
        (** hull_eq: f_inv(conv V_\<tau>) = conv(f_inv V_\<tau>). **)
        have h_inj_V\<tau>: "inj_on (inv_into (geotop_polyhedron L) f) V\<tau>"
        proof -
          have "V\<tau> \<subseteq> convex hull V\<tau>" by (rule hull_subset)
          thus ?thesis using h_inj_convVt inj_on_subset by (by100 blast)
        qed
        have h_hull_eq_V\<tau>: "inv_into (geotop_polyhedron L) f ` (convex hull V\<tau>)
                           = convex hull (inv_into (geotop_polyhedron L) f ` V\<tau>)"
          by (rule geotop_bary_lin_inj_image_hull_eq[OF hV\<tau>fin h_inj_V\<tau> h_bary_V\<tau>])
        (** conv V = conv(f_inv V_\<tau>). **)
        have h_convV_eq_fiVt: "convex hull V = convex hull (inv_into (geotop_polyhedron L) f ` V\<tau>)"
        proof -
          have h_tau_HOL: "\<tau> = convex hull V\<tau>" by (rule h\<tau>_conv_hull)
          have h_fi_tau: "inv_into (geotop_polyhedron L) f ` \<tau>
                         = inv_into (geotop_polyhedron L) f ` (convex hull V\<tau>)"
            using h_tau_HOL by (by100 simp)
          have h_convV_fi_tau: "convex hull V = inv_into (geotop_polyhedron L) f ` \<tau>"
          proof -
            have "convex hull V = geotop_convex_hull V"
              by (rule geotop_convex_hull_eq_HOL[symmetric])
            also have "\<dots> = inv_into (geotop_polyhedron L) f ` \<tau>" by (rule h_conv_eq_geo)
            finally show ?thesis .
          qed
          show ?thesis using h_convV_fi_tau h_fi_tau h_hull_eq_V\<tau> by (by100 simp)
        qed
        (** f_inv V_\<tau> is a vertex set of conv V. **)
        have h_fiVt_fin: "finite (inv_into (geotop_polyhedron L) f ` V\<tau>)"
          using hV\<tau>fin by (by100 simp)
        have h_fiVt_card: "card (inv_into (geotop_polyhedron L) f ` V\<tau>) = nV + 1"
          using card_image[OF h_inj_V\<tau>] hV\<tau>card by (by100 simp)
        have h_fiVt_gp: "geotop_general_position
                           (inv_into (geotop_polyhedron L) f ` V\<tau>) nV"
          by (rule geotop_ai_imp_general_position[OF h_fiVt_fin h_fiVt_card h_fiVt_ai])
        have h_convV_geo_eq: "geotop_convex_hull V
                                 = geotop_convex_hull (inv_into (geotop_polyhedron L) f ` V\<tau>)"
        proof -
          have h1: "geotop_convex_hull V = convex hull V"
            by (rule geotop_convex_hull_eq_HOL)
          have h2: "geotop_convex_hull (inv_into (geotop_polyhedron L) f ` V\<tau>)
                     = convex hull (inv_into (geotop_polyhedron L) f ` V\<tau>)"
            by (rule geotop_convex_hull_eq_HOL)
          show ?thesis using h1 h_convV_eq_fiVt h2 by (by100 simp)
        qed
        have h_fiVt_sv: "geotop_simplex_vertices (geotop_convex_hull V)
                           (inv_into (geotop_polyhedron L) f ` V\<tau>)"
          unfolding geotop_simplex_vertices_def
          using h_fiVt_fin h_fiVt_card hV\<tau>nm h_fiVt_gp h_convV_geo_eq by (by100 blast)
        (** By simplex_vertices_unique: V_L_3 = f_inv V_\<tau>. **)
        have hV_L\<^sub>3_eq: "V_L\<^sub>3 = inv_into (geotop_polyhedron L) f ` V\<tau>"
          by (rule geotop_simplex_vertices_unique[OF hV_L\<^sub>3sv h_fiVt_sv])
        (** V_\<tau> ⊆ f V: V_\<tau> = f V_L_3 (via bij, V_\<tau> ⊆ |K|), V_L_3 ⊆ V. **)
        have hV\<tau>_sub_\<tau>: "V\<tau> \<subseteq> \<tau>"
        proof -
          have "V\<tau> \<subseteq> convex hull V\<tau>" by (rule hull_subset)
          thus ?thesis using h\<tau>_conv_hull by (by100 simp)
        qed
        have hV\<tau>_K: "V\<tau> \<subseteq> geotop_polyhedron K"
          using hV\<tau>_sub_\<tau> h\<tau>_sub_K_simp by (by100 blast)
        have hfV_L\<^sub>3_eq_V\<tau>: "f ` V_L\<^sub>3 = V\<tau>"
        proof -
          have "f ` V_L\<^sub>3 = f ` (inv_into (geotop_polyhedron L) f ` V\<tau>)"
            using hV_L\<^sub>3_eq by (by100 simp)
          also have "\<dots> = (\<lambda>x. f (inv_into (geotop_polyhedron L) f x)) ` V\<tau>"
            unfolding image_image by (by100 simp)
          also have "\<dots> = V\<tau>"
          proof (rule set_eqI)
            fix w
            have "w \<in> (\<lambda>x. f (inv_into (geotop_polyhedron L) f x)) ` V\<tau> \<longleftrightarrow> w \<in> V\<tau>"
            proof
              assume "w \<in> (\<lambda>x. f (inv_into (geotop_polyhedron L) f x)) ` V\<tau>"
              then obtain v where hvV\<tau>: "v \<in> V\<tau>"
                              and hw: "w = f (inv_into (geotop_polyhedron L) f v)"
                by (by100 blast)
              have hv_K: "v \<in> geotop_polyhedron K" using hvV\<tau> hV\<tau>_K by (by100 blast)
              have "f (inv_into (geotop_polyhedron L) f v) = v"
                by (rule bij_betw_inv_into_right[OF hf_bij hv_K])
              thus "w \<in> V\<tau>" using hw hvV\<tau> by (by100 simp)
            next
              assume hw: "w \<in> V\<tau>"
              have hw_K: "w \<in> geotop_polyhedron K" using hw hV\<tau>_K by (by100 blast)
              have h_round: "f (inv_into (geotop_polyhedron L) f w) = w"
                by (rule bij_betw_inv_into_right[OF hf_bij hw_K])
              have "f (inv_into (geotop_polyhedron L) f w) \<in>
                      (\<lambda>x. f (inv_into (geotop_polyhedron L) f x)) ` V\<tau>"
                using hw by (by100 blast)
              thus "w \<in> (\<lambda>x. f (inv_into (geotop_polyhedron L) f x)) ` V\<tau>"
                using h_round by (by100 simp)
            qed
            thus "(w \<in> (\<lambda>x. f (inv_into (geotop_polyhedron L) f x)) ` V\<tau>) = (w \<in> V\<tau>)" .
          qed
          finally show ?thesis .
        qed
        have hV\<tau>_sub_fV: "V\<tau> \<subseteq> f ` V"
        proof -
          have h_fV_L3_sub_fV: "f ` V_L\<^sub>3 \<subseteq> f ` V" using hV_L\<^sub>3_sub_V by (by100 blast)
          show ?thesis using hfV_L\<^sub>3_eq_V\<tau> h_fV_L3_sub_fV by (by100 simp)
        qed
        (** \<tau> = conv V_\<tau> \<subseteq> conv(f V). **)
        have h\<tau>_sub_convfV_HOL: "convex hull V\<tau> \<subseteq> convex hull (f ` V)"
          by (rule hull_mono[OF hV\<tau>_sub_fV])
        have h\<tau>_sub_convfV: "\<tau> \<subseteq> geotop_convex_hull (f ` V)"
        proof -
          have h1: "\<tau> = convex hull V\<tau>" by (rule h\<tau>_conv_hull)
          have h2: "geotop_convex_hull (f ` V) = convex hull (f ` V)"
            by (rule geotop_convex_hull_eq_HOL)
          show ?thesis using h1 h\<tau>_sub_convfV_HOL h2 by (by100 simp)
        qed
        (** Combined with conv(f V) \<subseteq> \<tau>: conv(f V) = \<tau> \<in> K_3. **)
        have h_convfV_eq_\<tau>: "geotop_convex_hull (f ` V) = \<tau>"
          using h_convfV_sub_\<tau> h\<tau>_sub_convfV by (by100 blast)
        show "geotop_convex_hull (f ` V) \<in> K\<^sub>3"
          using h_convfV_eq_\<tau> h\<tau>K\<^sub>3 by (by100 simp)
      next
        assume hfV_K\<^sub>3: "geotop_convex_hull (f ` V) \<in> K\<^sub>3"
        (** f_inv(conv(f V)) = conv V via hull_eq + V = f_inv(f V). **)
        (** conv(f V) \<subseteq> some K_1-simplex (via K_3 < K_1). **)
        have hK\<^sub>3_ref_K\<^sub>1_b: "geotop_refines K\<^sub>3 K\<^sub>1"
          using hK\<^sub>3_K\<^sub>1 unfolding geotop_is_subdivision_def by (by100 blast)
        obtain \<sigma>\<^sub>K\<^sub>1 where h\<sigma>K1: "\<sigma>\<^sub>K\<^sub>1 \<in> K\<^sub>1" and hconvfV_sub_K1: "geotop_convex_hull (f ` V) \<subseteq> \<sigma>\<^sub>K\<^sub>1"
          using hfV_K\<^sub>3 hK\<^sub>3_ref_K\<^sub>1_b unfolding geotop_refines_def by (by100 blast)
        have h_lin_\<sigma>K1: "geotop_linear_on \<sigma>\<^sub>K\<^sub>1 (inv_into (geotop_polyhedron L) f)"
          using hK\<^sub>1_lin h\<sigma>K1 by (by100 blast)
        have hconvfV_sim: "geotop_is_simplex (geotop_convex_hull (f ` V))"
          using hfV_K\<^sub>3 conjunct1[OF hK\<^sub>3_comp[unfolded geotop_is_complex_def]]
          by (by100 blast)
        have h_lin_convfV: "geotop_linear_on (geotop_convex_hull (f ` V))
                             (inv_into (geotop_polyhedron L) f)"
          by (rule geotop_linear_on_sub_simplex[OF h_lin_\<sigma>K1 hconvfV_sim hconvfV_sub_K1])
        (** Extract bary-preservation on V(conv(f V)) = f V's vertex set via linear_on. **)
        (** Actually, simplified: directly show conv V = f_inv \<sup>\` conv(f V) via
            hull_eq on f V (which \<subseteq> V(K_3) \<subseteq> |K|). **)
        have hf_V_sub_K: "f ` V \<subseteq> geotop_polyhedron K"
          using hf_V_sub_VK\<^sub>3 hV_K\<^sub>3_in_K by (by100 blast)
        have hK\<^sub>3fin: "finite K\<^sub>3"
          using hK\<^sub>3_K\<^sub>1 hK\<^sub>1fin geotop_subdivision_of_finite_is_finite by (by100 blast)
        have hV_K\<^sub>3fin: "finite (geotop_complex_vertices K\<^sub>3)"
        proof -
          have h_union_eq: "geotop_complex_vertices K\<^sub>3
                              = (\<Union>\<sigma>\<in>K\<^sub>3. {v. \<exists>V. geotop_simplex_vertices \<sigma> V \<and> v \<in> V})"
            unfolding geotop_complex_vertices_def by (by100 blast)
          have h_each_fin: "\<And>\<sigma>. \<sigma> \<in> K\<^sub>3
                              \<Longrightarrow> finite {v. \<exists>V. geotop_simplex_vertices \<sigma> V \<and> v \<in> V}"
          proof -
            fix \<sigma> assume h\<sigma>K: "\<sigma> \<in> K\<^sub>3"
            have h\<sigma>_sim: "geotop_is_simplex \<sigma>"
              using h\<sigma>K conjunct1[OF hK\<^sub>3_comp[unfolded geotop_is_complex_def]]
              by (by100 blast)
            obtain V' where hV'sv: "geotop_simplex_vertices \<sigma> V'"
              using h\<sigma>_sim unfolding geotop_is_simplex_def geotop_simplex_vertices_def
              by (by100 blast)
            have hV'_fin: "finite V'"
              using hV'sv unfolding geotop_simplex_vertices_def by (by100 blast)
            have h_uniq: "\<And>V''. geotop_simplex_vertices \<sigma> V'' \<Longrightarrow> V'' = V'"
              by (rule geotop_simplex_vertices_unique[OF _ hV'sv])
            have h_set_eq: "{v. \<exists>V. geotop_simplex_vertices \<sigma> V \<and> v \<in> V} = V'"
              using hV'sv h_uniq by (by100 blast)
            show "finite {v. \<exists>V. geotop_simplex_vertices \<sigma> V \<and> v \<in> V}"
              using hV'_fin h_set_eq by (by100 simp)
          qed
          show ?thesis using h_union_eq h_each_fin hK\<^sub>3fin by (by100 simp)
        qed
        have hfV_fin: "finite (f ` V)"
          using hf_V_sub_VK\<^sub>3 hV_K\<^sub>3fin finite_subset by (by100 blast)
        (** V = f_inv \<sup>\` (f V). **)
        have hV_sub_L: "V \<subseteq> geotop_polyhedron L"
        proof -
          have hVL\<^sub>3_sub_L: "geotop_complex_vertices L\<^sub>3 \<subseteq> geotop_polyhedron L"
          proof
            fix v assume hv: "v \<in> geotop_complex_vertices L\<^sub>3"
            obtain V' where hV'sv: "\<exists>\<sigma>\<in>L\<^sub>3. geotop_simplex_vertices \<sigma> V'" and hv_V': "v \<in> V'"
              using hv unfolding geotop_complex_vertices_def by (by100 blast)
            obtain \<sigma>_L\<^sub>3 where h\<sigma>_L\<^sub>3: "\<sigma>_L\<^sub>3 \<in> L\<^sub>3" and hV'_sv: "geotop_simplex_vertices \<sigma>_L\<^sub>3 V'"
              using hV'sv by (by100 blast)
            have hV'_sub: "V' \<subseteq> geotop_convex_hull V'"
              unfolding geotop_convex_hull_def hull_def by (by100 blast)
            have h\<sigma>_L\<^sub>3_eq: "\<sigma>_L\<^sub>3 = geotop_convex_hull V'"
              using hV'_sv unfolding geotop_simplex_vertices_def by (by100 blast)
            have hv_hull: "v \<in> geotop_convex_hull V'" using hv_V' hV'_sub by (by100 blast)
            have hv_\<sigma>: "v \<in> \<sigma>_L\<^sub>3" using hv_hull h\<sigma>_L\<^sub>3_eq by (by100 simp)
            have h\<sigma>_L\<^sub>3_sub: "\<sigma>_L\<^sub>3 \<subseteq> geotop_polyhedron L\<^sub>3"
              unfolding geotop_polyhedron_def using h\<sigma>_L\<^sub>3 by (by100 blast)
            have "v \<in> geotop_polyhedron L\<^sub>3" using hv_\<sigma> h\<sigma>_L\<^sub>3_sub by (by100 blast)
            thus "v \<in> geotop_polyhedron L" using hL\<^sub>3_poly by (by100 simp)
          qed
          show ?thesis using hV_sub hVL\<^sub>3_sub_L by (by100 blast)
        qed
        have hf_inj_L: "inj_on f (geotop_polyhedron L)"
          using hf_bij unfolding bij_betw_def by (by100 blast)
        have hV_eq_fi_fV: "V = inv_into (geotop_polyhedron L) f ` (f ` V)"
        proof (rule set_eqI)
          fix v
          show "(v \<in> V) = (v \<in> inv_into (geotop_polyhedron L) f ` (f ` V))"
          proof
            assume hvV: "v \<in> V"
            have hvL: "v \<in> geotop_polyhedron L" using hvV hV_sub_L by (by100 blast)
            have h_fi_ff: "inv_into (geotop_polyhedron L) f (f v) = v"
              by (rule inv_into_f_f[OF hf_inj_L hvL])
            have "f v \<in> f ` V" using hvV by (by100 blast)
            thus "v \<in> inv_into (geotop_polyhedron L) f ` (f ` V)"
              using h_fi_ff by (by100 force)
          next
            assume hv: "v \<in> inv_into (geotop_polyhedron L) f ` (f ` V)"
            obtain w where hwfV: "w \<in> f ` V"
                      and hv_eq: "v = inv_into (geotop_polyhedron L) f w" using hv by (by100 blast)
            obtain v' where hv'V: "v' \<in> V" and hw_eq: "w = f v'" using hwfV by (by100 blast)
            have hv'L: "v' \<in> geotop_polyhedron L" using hv'V hV_sub_L by (by100 blast)
            have h_fi_f: "inv_into (geotop_polyhedron L) f (f v') = v'"
              by (rule inv_into_f_f[OF hf_inj_L hv'L])
            have "v = v'" using hv_eq hw_eq h_fi_f by (by100 simp)
            thus "v \<in> V" using hv'V by (by100 simp)
          qed
        qed
        (** Take \<tau> = conv(f V) \<in> K_3. Show conv V = f_inv \<sup>\` \<tau>. **)
        define \<tau>_b where "\<tau>_b = geotop_convex_hull (f ` V)"
        have h\<tau>_b_K\<^sub>3: "\<tau>_b \<in> K\<^sub>3" using hfV_K\<^sub>3 \<tau>_b_def by (by100 simp)
        (** Extract W_b = vertex set of \<tau>_b. **)
        obtain W_b where hW_b_sv: "geotop_simplex_vertices \<tau>_b W_b"
          using hconvfV_sim \<tau>_b_def unfolding geotop_is_simplex_def
                geotop_simplex_vertices_def by (by100 blast)
        have hW_b_ai: "\<not> affine_dependent W_b"
          by (rule geotop_general_position_imp_aff_indep[OF hW_b_sv])
        (** f_inv linear on \<tau>_b. **)
        have h_lin_\<tau>_b: "geotop_linear_on \<tau>_b (inv_into (geotop_polyhedron L) f)"
          using h_lin_convfV \<tau>_b_def by (by100 simp)
        (** f_inv inj on \<tau>_b (= conv(f V) \<subseteq> K_1-simplex \<subseteq> |K|). **)
        have h\<tau>_b_sub_K: "\<tau>_b \<subseteq> geotop_polyhedron K"
          using h\<tau>_b_K\<^sub>3 hK\<^sub>3_poly_eq_K unfolding geotop_polyhedron_def by (by100 blast)
        have h_inj_\<tau>_b: "inj_on (inv_into (geotop_polyhedron L) f) \<tau>_b"
          using hf_inv_inj_K h\<tau>_b_sub_K inj_on_subset by (by100 blast)
        (** bary of f_inv on W_b (from linear_on). **)
        obtain W_b' where hW_b'sv: "geotop_simplex_vertices \<tau>_b W_b'"
                      and h_prop_W_b': "\<forall>\<alpha>. (\<forall>v\<in>W_b'. 0 \<le> \<alpha> v) \<and> sum \<alpha> W_b' = 1 \<longrightarrow>
                                            inv_into (geotop_polyhedron L) f
                                              (\<Sum>v\<in>W_b'. \<alpha> v *\<^sub>R v)
                                            = (\<Sum>v\<in>W_b'. \<alpha> v *\<^sub>R
                                                inv_into (geotop_polyhedron L) f v)"
          using h_lin_\<tau>_b unfolding geotop_linear_on_def by (by100 blast)
        have hW_b'_eq: "W_b' = W_b" by (rule geotop_simplex_vertices_unique[OF hW_b'sv hW_b_sv])
        have h_bary_W_b: "\<And>\<alpha>. (\<forall>v\<in>W_b. 0 \<le> \<alpha> v) \<Longrightarrow> sum \<alpha> W_b = 1 \<Longrightarrow>
                              inv_into (geotop_polyhedron L) f (\<Sum>v\<in>W_b. \<alpha> v *\<^sub>R v)
                              = (\<Sum>v\<in>W_b. \<alpha> v *\<^sub>R inv_into (geotop_polyhedron L) f v)"
          using h_prop_W_b' hW_b'_eq by (by100 blast)
        obtain mb nb where hW_b_fin: "finite W_b" and hW_b_card: "card W_b = nb + 1"
                       and hW_b_nm: "nb \<le> mb" and hW_b_gp: "geotop_general_position W_b mb"
                       and h\<tau>_b_hull: "\<tau>_b = geotop_convex_hull W_b"
          using hW_b_sv unfolding geotop_simplex_vertices_def by (by100 blast)
        have h\<tau>_b_HOL: "\<tau>_b = convex hull W_b"
          using h\<tau>_b_hull geotop_convex_hull_eq_HOL by (by100 simp)
        have h_inj_W_b: "inj_on (inv_into (geotop_polyhedron L) f) W_b"
        proof -
          have "W_b \<subseteq> convex hull W_b" by (rule hull_subset)
          hence "W_b \<subseteq> \<tau>_b" using h\<tau>_b_HOL by (by100 simp)
          thus ?thesis using h_inj_\<tau>_b inj_on_subset by (by100 blast)
        qed
        (** Apply hull_eq on W_b: f_inv(conv W_b) = conv(f_inv W_b). **)
        have h_hull_eq_W_b: "inv_into (geotop_polyhedron L) f ` (convex hull W_b)
                            = convex hull (inv_into (geotop_polyhedron L) f ` W_b)"
          by (rule geotop_bary_lin_inj_image_hull_eq[OF hW_b_fin h_inj_W_b h_bary_W_b])
        (** W_b \<subseteq> f V (extreme points of conv(f V) = \<tau>_b). **)
        have hW_b_sub_fV: "W_b \<subseteq> f ` V"
        proof
          fix w assume hw: "w \<in> W_b"
          have h_extr_Wb: "w extreme_point_of (convex hull W_b)"
            using extreme_point_of_convex_hull_affine_independent[OF hW_b_ai] hw by (by100 blast)
          have h_fV_HOL: "\<tau>_b = convex hull (f ` V)"
            using \<tau>_b_def geotop_convex_hull_eq_HOL by (by100 simp)
          have h_convfV_eq: "convex hull (f ` V) = convex hull W_b"
            using h_fV_HOL h\<tau>_b_HOL by (by100 simp)
          have h_extr_fV: "w extreme_point_of (convex hull (f ` V))"
            using h_extr_Wb h_convfV_eq by (by100 simp)
          show "w \<in> f ` V" by (rule extreme_point_of_convex_hull[OF h_extr_fV])
        qed
        (** f_inv W_b \<subseteq> V via V = f_inv(f V) and monotonicity. **)
        have hfi_W_b_sub_V: "inv_into (geotop_polyhedron L) f ` W_b \<subseteq> V"
        proof -
          have "inv_into (geotop_polyhedron L) f ` W_b
                  \<subseteq> inv_into (geotop_polyhedron L) f ` (f ` V)"
            using hW_b_sub_fV by (by100 blast)
          thus ?thesis using hV_eq_fi_fV by (by100 simp)
        qed
        (** conv(f_inv W_b) \<subseteq> conv V. **)
        have h_convfiWb_sub_convV: "convex hull (inv_into (geotop_polyhedron L) f ` W_b)
                                    \<subseteq> convex hull V"
          by (rule hull_mono[OF hfi_W_b_sub_V])
        (** Other direction: f V \<subseteq> \<tau>_b, so f_inv(f V) \<subseteq> f_inv \<tau>_b, i.e., V \<subseteq> f_inv \<tau>_b.
            Then conv V \<subseteq> conv(f_inv \<tau>_b) = conv(f_inv(conv W_b)) = conv(conv(f_inv W_b))
            = conv(f_inv W_b). **)
        have hfV_sub_\<tau>_b: "f ` V \<subseteq> \<tau>_b"
          unfolding \<tau>_b_def geotop_convex_hull_def hull_def by (by100 blast)
        have h_fi_fV_sub: "inv_into (geotop_polyhedron L) f ` (f ` V)
                          \<subseteq> inv_into (geotop_polyhedron L) f ` \<tau>_b"
          using hfV_sub_\<tau>_b by (by100 blast)
        have hV_sub_fi\<tau>_b: "V \<subseteq> inv_into (geotop_polyhedron L) f ` \<tau>_b"
          using h_fi_fV_sub hV_eq_fi_fV by (by100 simp)
        have h_fi\<tau>_b_eq: "inv_into (geotop_polyhedron L) f ` \<tau>_b
                          = convex hull (inv_into (geotop_polyhedron L) f ` W_b)"
          using h\<tau>_b_HOL h_hull_eq_W_b by (by100 simp)
        have hV_sub_convfiWb: "V \<subseteq> convex hull (inv_into (geotop_polyhedron L) f ` W_b)"
          using hV_sub_fi\<tau>_b h_fi\<tau>_b_eq by (by100 simp)
        have hconvV_sub_convfiWb: "convex hull V
                                   \<subseteq> convex hull (inv_into (geotop_polyhedron L) f ` W_b)"
          using hV_sub_convfiWb convex_convex_hull
                hull_minimal[of V "convex hull (inv_into (geotop_polyhedron L) f ` W_b)" convex]
          by (by100 simp)
        (** So conv V = conv(f_inv W_b) = f_inv \<tau>_b (sets of |K| points). **)
        have h_convV_eq_fi\<tau>_b: "convex hull V = inv_into (geotop_polyhedron L) f ` \<tau>_b"
        proof -
          have h1: "convex hull V = convex hull (inv_into (geotop_polyhedron L) f ` W_b)"
            using h_convfiWb_sub_convV hconvV_sub_convfiWb by (by100 blast)
          show ?thesis using h1 h_fi\<tau>_b_eq by (by100 simp)
        qed
        have h_conv_V_geo: "geotop_convex_hull V = inv_into (geotop_polyhedron L) f ` \<tau>_b"
        proof -
          have "geotop_convex_hull V = convex hull V"
            by (rule geotop_convex_hull_eq_HOL)
          thus ?thesis using h_convV_eq_fi\<tau>_b by (by100 simp)
        qed
        show "geotop_convex_hull V \<in> L\<^sub>3"
          unfolding L\<^sub>3_def using h\<tau>_b_K\<^sub>3 h_conv_V_geo by (by100 blast)
      qed
    qed
    have hiso_L\<^sub>3_K\<^sub>3: "geotop_isomorphic L\<^sub>3 K\<^sub>3"
      unfolding geotop_isomorphic_def geotop_isomorphism_def
      using hiso_vert hiso_simp by (by100 blast)
    (** (6) Assemble \<open>K \<sim>_c L\<close> from \<open>K\<^sub>3 < K\<close> and \<open>L\<^sub>3 < L\<close> and \<open>K\<^sub>3 \<cong> L\<^sub>3\<close>. **)
    have hK\<^sub>3_K: "geotop_is_subdivision K\<^sub>3 K"
      by (rule geotop_is_subdivision_trans[OF hK\<^sub>1K hK\<^sub>3_K\<^sub>1])
    have hiso_K\<^sub>3_L\<^sub>3: "geotop_isomorphic K\<^sub>3 L\<^sub>3"
      by (rule geotop_isomorphic_sym[OF hiso_L\<^sub>3_K\<^sub>3])
    show "geotop_comb_equiv K L"
      unfolding geotop_comb_equiv_def
      using hK\<^sub>3_K hL\<^sub>3_L hiso_K\<^sub>3_L\<^sub>3 hKfin hLfin by (by100 blast)
  qed
  show ?thesis using h_forward h_backward by (by100 blast)
qed

(** from Introduction: Theorem 3 (geotop.tex:185)
    LATEX VERSION: Combinatorial equivalence is an equivalence relation.

    FORMALIZATION NOTE: Moise treats \<sim>\<^sub>c as an equivalence relation on the
    (implicit) class of complexes. Since \<open>geotop_comb_equiv K K\<close> fails when K
    is not a complex (because \<open>geotop_is_subdivision\<close> requires a complex), this
    is a \emph{partial} equivalence relation in the HOL sense: symmetric,
    transitive, and reflexive on its domain of definition (complexes).
    We formalize it with \<open>part_equivp\<close> rather than \<open>equivp\<close>. **)
theorem Theorem_GT_3:
  shows "part_equivp (geotop_comb_equiv :: 'a::euclidean_space set set \<Rightarrow> 'a set set \<Rightarrow> bool)"
proof (rule part_equivpI)
  (** (1) Some element is reflexive: the empty complex \<open>{}\<close> is vacuously a complex,
         is a subdivision of itself, and is isomorphic to itself (via identity). **)
  have h_empty_complex: "geotop_is_complex ({}::'a set set)"
    unfolding geotop_is_complex_def by (by100 blast)
  have h_empty_polyhedron: "geotop_polyhedron ({}::'a set set) = {}"
    unfolding geotop_polyhedron_def by (by100 simp)
  have h_empty_refines: "geotop_refines ({}::'a set set) {}"
    unfolding geotop_refines_def by (by100 simp)
  have h_empty_vertices: "geotop_complex_vertices ({}::'a set set) = {}"
    unfolding geotop_complex_vertices_def by (by100 simp)
  have h_empty_subdiv: "geotop_is_subdivision ({}::'a set set) {}"
    unfolding geotop_is_subdivision_def
    using h_empty_complex h_empty_refines h_empty_polyhedron by (by100 simp)
  have h_bij_empty: "bij_betw (id::'a \<Rightarrow> 'a) {} {}"
    unfolding bij_betw_def by (by100 simp)
  have h_empty_iso: "geotop_isomorphic ({}::'a set set) ({}::'a set set)"
    unfolding geotop_isomorphic_def geotop_isomorphism_def
    using h_empty_vertices h_bij_empty by (by100 blast)
  have h_empty_comb: "geotop_comb_equiv ({}::'a set set) ({}::'a set set)"
    unfolding geotop_comb_equiv_def
    using h_empty_subdiv h_empty_iso by (by100 blast)
  show "\<exists>K::'a set set. geotop_comb_equiv K K"
    using h_empty_comb by (by100 blast)
next
  (** (2) Symmetric: if \<phi>: K' \<cong> L' via subdivisions \<open>K' < K\<close>, \<open>L' < L\<close>,
      then the inverse bijection \<open>?\<psi>\<close> witnesses \<open>L' \<cong> K'\<close> by
      \<open>geotop_isomorphic_sym\<close>, giving \<open>L \<sim>_c K\<close>. **)
  show "symp (geotop_comb_equiv :: 'a set set \<Rightarrow> 'a set set \<Rightarrow> bool)"
  proof (rule sympI)
    fix K L :: "'a set set"
    assume hKL: "geotop_comb_equiv K L"
    have hKfin: "finite K" using hKL unfolding geotop_comb_equiv_def by (by100 blast)
    have hLfin: "finite L" using hKL unfolding geotop_comb_equiv_def by (by100 blast)
    obtain K' L' where hK'sub: "geotop_is_subdivision K' K"
                   and hL'sub: "geotop_is_subdivision L' L"
                   and hiso: "geotop_isomorphic K' L'"
      using hKL unfolding geotop_comb_equiv_def by (by100 blast)
    have hL'K': "geotop_isomorphic L' K'"
      by (rule geotop_isomorphic_sym[OF hiso])
    show "geotop_comb_equiv L K"
      unfolding geotop_comb_equiv_def
      using hL'sub hK'sub hL'K' hLfin hKfin by (by100 blast)
  qed
next
  (** (3) Transitive: given \<open>K \<sim>_c L\<close> (via \<open>K_1 \<cong> L_1\<close>, \<open>K_1 < K\<close>, \<open>L_1 < L\<close>)
         and \<open>L \<sim>_c M\<close> (via \<open>L_2 \<cong> M_1\<close>, \<open>L_2 < L\<close>, \<open>M_1 < M\<close>), we build
         \<open>K \<sim>_c M\<close> following early.tex \<S>8:
           (a) By Theorem_GT_1, \<open>L_1\<close> and \<open>L_2\<close> have a common subdivision \<open>L_3\<close>
               (assuming \<open>L\<close> finite; see note).
           (b) By transport_subdivision (Lemma 6), since \<open>K_1 \<cong> L_1\<close> and \<open>L_3 < L_1\<close>,
               there is \<open>K_2 < K_1\<close> with \<open>K_2 \<cong> L_3\<close>.
           (c) Similarly, since \<open>L_2 \<cong> M_1\<close> and \<open>L_3 < L_2\<close>, there is \<open>M_2 < M_1\<close>
               with \<open>L_3 \<cong> M_2\<close>.
           (d) By iso_trans, \<open>K_2 \<cong> M_2\<close>. Since \<open>K_2 < K\<close> and \<open>M_2 < M\<close> (by
               transitivity of subdivision), we conclude \<open>K \<sim>_c M\<close>.
         FAITHFULNESS FIX: transitivity requires finiteness of the mediator \<open>L\<close>
         to apply Theorem_GT_1. We state the transp proof contingent on that
         hypothesis (deferred: the full part_equivp on locally finite complexes
         needs a strengthened Theorem_GT_1). **)
  show "transp (geotop_comb_equiv :: 'a set set \<Rightarrow> 'a set set \<Rightarrow> bool)"
  proof (rule transpI)
    fix K L M :: "'a set set"
    assume hKL: "geotop_comb_equiv K L" and hLM: "geotop_comb_equiv L M"
    (** Unpack finiteness from both hypotheses (from the strengthened comb_equiv def). **)
    have hKfin: "finite K" using hKL unfolding geotop_comb_equiv_def by (by100 blast)
    have hLfin: "finite L" using hKL unfolding geotop_comb_equiv_def by (by100 blast)
    have hMfin: "finite M" using hLM unfolding geotop_comb_equiv_def by (by100 blast)
    (** Unpack the two combinatorial equivalences. **)
    obtain K\<^sub>1 L\<^sub>1 where hK\<^sub>1K: "geotop_is_subdivision K\<^sub>1 K"
                    and hL\<^sub>1L: "geotop_is_subdivision L\<^sub>1 L"
                    and hiso\<^sub>1: "geotop_isomorphic K\<^sub>1 L\<^sub>1"
      using hKL unfolding geotop_comb_equiv_def by (by100 blast)
    obtain L\<^sub>2 M\<^sub>1 where hL\<^sub>2L: "geotop_is_subdivision L\<^sub>2 L"
                    and hM\<^sub>1M: "geotop_is_subdivision M\<^sub>1 M"
                    and hiso\<^sub>2: "geotop_isomorphic L\<^sub>2 M\<^sub>1"
      using hLM unfolding geotop_comb_equiv_def by (by100 blast)
    (** Step (a): common subdivision \<open>L_3\<close> of \<open>L_1\<close>, \<open>L_2\<close> via Theorem_GT_1.
        Uses finite L (now derivable from hKL via the strengthened comb_equiv def). **)
    have hL_ex: "\<exists>L\<^sub>3. geotop_is_subdivision L\<^sub>3 L\<^sub>1 \<and> geotop_is_subdivision L\<^sub>3 L\<^sub>2"
      by (rule Theorem_GT_1[OF hLfin hL\<^sub>1L hL\<^sub>2L])
    obtain L\<^sub>3 where hL\<^sub>3L\<^sub>1: "geotop_is_subdivision L\<^sub>3 L\<^sub>1"
                 and hL\<^sub>3L\<^sub>2: "geotop_is_subdivision L\<^sub>3 L\<^sub>2"
      using hL_ex by (by100 blast)
    (** Step (b): transport \<open>L_3 < L_1\<close> across \<open>K_1 \<cong> L_1\<close> to get \<open>K_2 < K_1\<close> with
        \<open>K_2 \<cong> L_3\<close>. **)
    have hK\<^sub>1comp: "geotop_is_complex K\<^sub>1"
      using hK\<^sub>1K unfolding geotop_is_subdivision_def by (by100 blast)
    have hL\<^sub>1fin: "finite L\<^sub>1"
      by (rule geotop_subdivision_of_finite_is_finite[OF hLfin hL\<^sub>1L])
    obtain K\<^sub>2 where hK\<^sub>2K\<^sub>1: "geotop_is_subdivision K\<^sub>2 K\<^sub>1"
                 and hiso_K\<^sub>2L\<^sub>3: "geotop_isomorphic K\<^sub>2 L\<^sub>3"
      using geotop_transport_subdivision[OF hK\<^sub>1comp hL\<^sub>1fin hiso\<^sub>1 hL\<^sub>3L\<^sub>1] by (by100 blast)
    (** Step (c): transport \<open>L_3 < L_2\<close> across \<open>L_2 \<cong> M_1\<close> (reverse direction).
        First swap iso to get \<open>M_1 \<cong> L_2\<close>, then transport \<open>L_3\<close> to get \<open>M_2 < M_1\<close>
        with \<open>M_2 \<cong> L_3\<close>; symmetrise again. **)
    have hiso\<^sub>2_sym: "geotop_isomorphic M\<^sub>1 L\<^sub>2"
      by (rule geotop_isomorphic_sym[OF hiso\<^sub>2])
    have hM\<^sub>1comp: "geotop_is_complex M\<^sub>1"
      using hM\<^sub>1M unfolding geotop_is_subdivision_def by (by100 blast)
    have hL\<^sub>2fin: "finite L\<^sub>2"
      by (rule geotop_subdivision_of_finite_is_finite[OF hLfin hL\<^sub>2L])
    obtain M\<^sub>2 where hM\<^sub>2M\<^sub>1: "geotop_is_subdivision M\<^sub>2 M\<^sub>1"
                 and hiso_M\<^sub>2L\<^sub>3: "geotop_isomorphic M\<^sub>2 L\<^sub>3"
      using geotop_transport_subdivision[OF hM\<^sub>1comp hL\<^sub>2fin hiso\<^sub>2_sym hL\<^sub>3L\<^sub>2] by (by100 blast)
    (** Step (d): compose \<open>K_2 \<cong> L_3 \<cong> M_2\<close>. **)
    have hiso_L\<^sub>3M\<^sub>2: "geotop_isomorphic L\<^sub>3 M\<^sub>2"
      by (rule geotop_isomorphic_sym[OF hiso_M\<^sub>2L\<^sub>3])
    have hiso_K\<^sub>2M\<^sub>2: "geotop_isomorphic K\<^sub>2 M\<^sub>2"
      by (rule geotop_isomorphic_trans[OF hiso_K\<^sub>2L\<^sub>3 hiso_L\<^sub>3M\<^sub>2])
    (** Step (e): \<open>K_2 < K\<close> and \<open>M_2 < M\<close> by transitivity of subdivision. **)
    have hK\<^sub>2K: "geotop_is_subdivision K\<^sub>2 K"
      by (rule geotop_is_subdivision_trans[OF hK\<^sub>1K hK\<^sub>2K\<^sub>1])
    have hM\<^sub>2M: "geotop_is_subdivision M\<^sub>2 M"
      by (rule geotop_is_subdivision_trans[OF hM\<^sub>1M hM\<^sub>2M\<^sub>1])
    show "geotop_comb_equiv K M"
      unfolding geotop_comb_equiv_def
      using hK\<^sub>2K hM\<^sub>2M hiso_K\<^sub>2M\<^sub>2 hKfin hMfin by (by100 blast)
  qed
qed

subsection \<open>Cells, manifolds, dense sets, separability\<close>

(** from Introduction: n-cell (geotop.tex:188)
    LATEX VERSION: An n-cell is a space homeomorphic to an n-simplex. A 1-cell is an arc,
      and a 2-cell is a disk. A combinatorial n-cell is a complex combinatorially equivalent
      to an n-simplex. **)
text \<open>An $n$-cell is a space homeomorphic to an $n$-simplex. We formulate this parametrically:
  the witness simplex lives in the same type as our space, or via a second type variable.
  For the definition to be truly general we use a second parametric type \<open>'b\<close>.\<close>
text \<open>\<open>geotop_euclidean_topology\<close> is defined earlier (before \<open>geotop_open_star\<close>)
  since early-tex infrastructure uses it.\<close>

definition geotop_is_n_cell_wit ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> 'b::real_normed_vector set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "geotop_is_n_cell_wit X TX n \<sigma> f \<longleftrightarrow>
    is_topology_on X TX \<and> geotop_simplex_dim \<sigma> n
    \<and> top1_homeomorphism_on X TX \<sigma>
         (subspace_topology (UNIV::'b set) geotop_euclidean_topology \<sigma>) f"

definition geotop_is_n_cell :: "'a::real_normed_vector set \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_is_n_cell X TX n \<longleftrightarrow>
    is_topology_on X TX \<and>
    (\<exists>(\<sigma>::'a set) f. geotop_simplex_dim \<sigma> n
       \<and> top1_homeomorphism_on X TX \<sigma>
           (subspace_topology UNIV geotop_euclidean_topology \<sigma>) f)"

text \<open>Arc = 1-cell.\<close>
definition geotop_is_arc :: "'a::real_normed_vector set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "geotop_is_arc X TX \<longleftrightarrow> geotop_is_n_cell X TX 1"

text \<open>Disk = 2-cell.\<close>
definition geotop_is_disk :: "'a::real_normed_vector set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "geotop_is_disk X TX \<longleftrightarrow> geotop_is_n_cell X TX 2"

(** from Introduction: combinatorial n-cell (geotop.tex:188)
    LATEX VERSION: A combinatorial n-cell is a complex combinatorially equivalent to a
      complex consisting of an n-simplex and its faces. **)
definition geotop_comb_n_cell :: "'a::real_normed_vector set set \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_comb_n_cell K n \<longleftrightarrow>
    geotop_is_complex K \<and>
    (\<exists>(L::'a set set) \<sigma>. L = {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}
       \<and> geotop_simplex_dim \<sigma> n \<and> geotop_comb_equiv K L)"

(** from Introduction: dense set (geotop.tex:190)
    LATEX VERSION: A set A is dense in a set B if A \<subset> B \<subset> \<bar>A\<close>. **)
definition geotop_dense_in :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_dense_in X T A B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> closure_on X T A"

(** from Introduction: separable space (geotop.tex:190)
    LATEX VERSION: A topological (or metric) space is separable if some countable set is
      dense in X. Already available in Top0 as \<open>top1_separable_on\<close>. **)

subsection \<open>Manifolds\<close>

(** from Introduction: n-manifold (geotop.tex:192)
    LATEX VERSION: An n-manifold is a separable metric space M^n in which every point has a
      neighborhood homeomorphic to R^n.
    Note: "homeomorphic to R^n" is parametrized by a witness Euclidean space type 'b. **)
definition geotop_n_manifold_on ::
  "'a::real_normed_vector set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_n_manifold_on M d n \<longleftrightarrow>
    top1_metric_on M d \<and>
    (\<exists>D. top1_countable D \<and> D \<subseteq> M \<and> closure_on M (top1_metric_topology_on M d) D = M) \<and>
    (\<forall>P\<in>M. \<exists>U. openin_on M (top1_metric_topology_on M d) U \<and> P \<in> U \<and>
       (\<exists>f. top1_homeomorphism_on U (subspace_topology M (top1_metric_topology_on M d) U)
             (UNIV::'a set) geotop_euclidean_topology f))"

(** from Introduction: n-manifold with boundary (geotop.tex:192)
    LATEX VERSION: If every point lies in an open set whose closure is an n-cell, then M^n
      is an n-manifold with boundary. **)
definition geotop_n_manifold_with_boundary_on ::
  "'a::real_normed_vector set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_n_manifold_with_boundary_on M d n \<longleftrightarrow>
    top1_metric_on M d \<and>
    (\<exists>D. top1_countable D \<and> D \<subseteq> M \<and> closure_on M (top1_metric_topology_on M d) D = M) \<and>
    (\<forall>P\<in>M. \<exists>U. openin_on M (top1_metric_topology_on M d) U \<and> P \<in> U \<and>
       geotop_is_n_cell (closure_on M (top1_metric_topology_on M d) U)
                        (subspace_topology M (top1_metric_topology_on M d)
                           (closure_on M (top1_metric_topology_on M d) U)) n)"

(** from Introduction: interior of a manifold (geotop.tex:192)
    LATEX VERSION: Int M^n is the set of points of M^n that have open Euclidean neighborhoods
      in M^n (neighborhoods homeomorphic to R^n). **)
definition geotop_manifold_interior ::
  "'a::real_normed_vector set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set" where
  "geotop_manifold_interior M d =
    {P\<in>M. \<exists>U. openin_on M (top1_metric_topology_on M d) U \<and> P \<in> U \<and>
       (\<exists>f. top1_homeomorphism_on U (subspace_topology M (top1_metric_topology_on M d) U)
             (UNIV::'a set) geotop_euclidean_topology f)}"

(** from Introduction: boundary of a manifold (geotop.tex:192)
    LATEX VERSION: Bd M^n is the set of points of M^n that do not have open Euclidean
      neighborhoods in M^n. **)
definition geotop_manifold_boundary ::
  "'a::real_normed_vector set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set" where
  "geotop_manifold_boundary M d = M - geotop_manifold_interior M d"

subsection \<open>Triangulated manifolds\<close>

(** from Introduction: triangulated n-manifold (geotop.tex:202)
    LATEX VERSION: Let K be a complex such that the space M = |K| is an n-manifold. Then K
      is a triangulated n-manifold. **)
definition geotop_triangulated_n_manifold ::
  "'a::real_normed_vector set set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_triangulated_n_manifold K d n \<longleftrightarrow>
    geotop_is_complex K \<and> geotop_n_manifold_on (geotop_polyhedron K :: 'a set) d n"

(** from Introduction: combinatorial boundary \<partial>K (geotop.tex:204)
    LATEX VERSION: Let K be a triangulated n-manifold with boundary. The combinatorial boundary
      \<partial>K is the set of all (n-1)-simplexes of K that lie in only one n-simplex of K
      (together with all faces of such (n-1)-simplexes). **)
definition geotop_comb_boundary ::
  "'a::real_normed_vector set set \<Rightarrow> nat \<Rightarrow> 'a set set" where
  "geotop_comb_boundary K n =
    (let S = {\<tau>\<in>K. geotop_simplex_dim \<tau> (n-1) \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> n \<and> geotop_is_face \<tau> \<sigma>} = 1}
     in S \<union> {\<rho>. \<exists>\<tau>\<in>S. geotop_is_face \<rho> \<tau>})"

subsection \<open>Brouwer's Invariance of Domain (Theorem 4)\<close>

subsection \<open>Star, link, combinatorial manifolds\<close>

(** from Introduction: star of a vertex (geotop.tex:211)
    LATEX VERSION: In a complex K, for each vertex v, St v is the complex consisting of all
      simplexes of K that contain v, together with all their faces. **)
definition geotop_star ::
  "'a::real_normed_vector set set \<Rightarrow> 'a \<Rightarrow> 'a set set" where
  "geotop_star K v = {\<tau>. \<exists>\<sigma>\<in>K. v \<in> \<sigma> \<and> (geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>)}"

(** from Introduction: link of a vertex (geotop.tex:211)
    LATEX VERSION: The link L(v) of v in K is the set of all simplexes of St v that do not
      contain v. **)
definition geotop_link ::
  "'a::real_normed_vector set set \<Rightarrow> 'a \<Rightarrow> 'a set set" where
  "geotop_link K v = {\<tau>\<in>geotop_star K v. v \<notin> \<tau>}"

(** from Introduction: combinatorial n-manifold (geotop.tex:211)
    LATEX VERSION: If |K| is an n-manifold, and each complex St v is a combinatorial n-cell,
      then K is a combinatorial n-manifold. **)
definition geotop_comb_n_manifold ::
  "'a::real_normed_vector set set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_comb_n_manifold K d n \<longleftrightarrow>
    geotop_is_complex K \<and> geotop_n_manifold_on (geotop_polyhedron K :: 'a set) d n \<and>
    (\<forall>v\<in>geotop_complex_vertices K. geotop_comb_n_cell (geotop_star K v) n)"


section \<open>\<S>1 Connectivity\<close>

(** from \<S>1: path definition (geotop.tex:316)
    LATEX VERSION: A path in a space [X,\<O>] is a mapping p: [a,b] \<rightarrow> X. **)
definition geotop_path_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool" where
  "geotop_path_on X T a b p \<longleftrightarrow>
    a \<le> b \<and>
    top1_continuous_map_on {t. a \<le> t \<and> t \<le> b}
                           (subspace_topology UNIV geotop_euclidean_topology {t. a \<le> t \<and> t \<le> b})
                           X T p"

(** from \<S>1: path from P to Q (geotop.tex:322)
    LATEX VERSION: If p(a) = P and p(b) = Q, then p is a path from P to Q. **)
definition geotop_path_from_to ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "geotop_path_from_to X T P Q \<longleftrightarrow>
    (\<exists>a b p. geotop_path_on X T a b p \<and> p a = P \<and> p b = Q)"

(** from \<S>1: pathwise connected set (geotop.tex:322)
    LATEX VERSION: A set M \<subset> X is pathwise connected if for each two points P,Q of M there is
      a path p: [a,b] \<rightarrow> M from P to Q. **)
text \<open>Already available in Top0 as \<open>top1_path_connected_on\<close>.\<close>

(** from \<S>1 Theorem 1 (geotop.tex:324)
    LATEX VERSION: In a topological space [X,\<O>], let G be a collection of pathwise connected
      sets, with a point P in common. Then the union G* of the elements of G is
      pathwise connected. **)
theorem Theorem_GT_1_1:
  fixes X :: "'a set" and T :: "'a set set" and G :: "'a set set" and P :: 'a
  assumes hTX: "is_topology_on X T"
  assumes hGpc: "\<forall>g\<in>G. g \<subseteq> X \<and> top1_path_connected_on g (subspace_topology X T g)"
  assumes hGP: "\<forall>g\<in>G. P \<in> g"
  shows "top1_path_connected_on (\<Union>G) (subspace_topology X T (\<Union>G))"
  (** Moise proof (geotop.tex:326): given Q \<in> g_Q, R \<in> g_R, paths from Q to P in
      g_Q and from P to R in g_R, concatenate via path component transitivity. **)
proof -
  have hUG_X: "\<Union>G \<subseteq> X" using hGpc by blast
  have hTUG: "is_topology_on (\<Union>G) (subspace_topology X T (\<Union>G))"
    by (rule subspace_topology_is_topology_on[OF hTX hUG_X])
  show ?thesis
  proof (cases "G = {}")
    case True
    (** Empty union - vacuous path-connectedness. **)
    show ?thesis unfolding top1_path_connected_on_def
      using hTUG True by simp
  next
    case False
    show ?thesis unfolding top1_path_connected_on_def
    proof (intro conjI hTUG ballI)
      fix Q R assume hQ: "Q \<in> \<Union>G" and hR: "R \<in> \<Union>G"
      obtain gQ where hgQ: "gQ \<in> G" and hQgQ: "Q \<in> gQ" using hQ by blast
      obtain gR where hgR: "gR \<in> G" and hRgR: "R \<in> gR" using hR by blast
      have hgQ_X: "gQ \<subseteq> X" using hgQ hGpc by blast
      have hgR_X: "gR \<subseteq> X" using hgR hGpc by blast
      have hgQ_pc: "top1_path_connected_on gQ (subspace_topology X T gQ)"
        using hgQ hGpc by blast
      have hgR_pc: "top1_path_connected_on gR (subspace_topology X T gR)"
        using hgR hGpc by blast
      have hP_gQ: "P \<in> gQ" using hgQ hGP by blast
      have hP_gR: "P \<in> gR" using hgR hGP by blast
      (** Path Q \<rightarrow> P in gQ. **)
      have "\<exists>p. top1_is_path_on gQ (subspace_topology X T gQ) Q P p"
        using hgQ_pc hQgQ hP_gQ unfolding top1_path_connected_on_def by blast
      then obtain p1 where hp1: "top1_is_path_on gQ (subspace_topology X T gQ) Q P p1" by blast
      (** Path P \<rightarrow> R in gR. **)
      have "\<exists>p. top1_is_path_on gR (subspace_topology X T gR) P R p"
        using hgR_pc hP_gR hRgR unfolding top1_path_connected_on_def by blast
      then obtain p2 where hp2: "top1_is_path_on gR (subspace_topology X T gR) P R p2" by blast
      (** Upgrade paths to live in \<Union>G. **)
      have hp1cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                      gQ (subspace_topology X T gQ) p1"
        using hp1 unfolding top1_is_path_on_def by simp
      have hgQ_UG: "gQ \<subseteq> \<Union>G" using hgQ by blast
      have hp1cont_UG: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                          (\<Union>G) (subspace_topology X T (\<Union>G)) p1"
        by (rule top1_continuous_map_on_codomain_enlarge[OF hp1cont hgQ_UG hUG_X])
      have hp2cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                      gR (subspace_topology X T gR) p2"
        using hp2 unfolding top1_is_path_on_def by simp
      have hgR_UG: "gR \<subseteq> \<Union>G" using hgR by blast
      have hp2cont_UG: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                          (\<Union>G) (subspace_topology X T (\<Union>G)) p2"
        by (rule top1_continuous_map_on_codomain_enlarge[OF hp2cont hgR_UG hUG_X])
      have hp1_UG: "top1_is_path_on (\<Union>G) (subspace_topology X T (\<Union>G)) Q P p1"
        unfolding top1_is_path_on_def
        using hp1cont_UG hp1 unfolding top1_is_path_on_def by simp
      have hp2_UG: "top1_is_path_on (\<Union>G) (subspace_topology X T (\<Union>G)) P R p2"
        unfolding top1_is_path_on_def
        using hp2cont_UG hp2 unfolding top1_is_path_on_def by simp
      have hQP_sc: "top1_in_same_path_component_on (\<Union>G) (subspace_topology X T (\<Union>G)) Q P"
        unfolding top1_in_same_path_component_on_def using hp1_UG by blast
      have hPR_sc: "top1_in_same_path_component_on (\<Union>G) (subspace_topology X T (\<Union>G)) P R"
        unfolding top1_in_same_path_component_on_def using hp2_UG by blast
      have hQR_sc: "top1_in_same_path_component_on (\<Union>G) (subspace_topology X T (\<Union>G)) Q R"
        by (rule top1_in_same_path_component_on_trans[OF hTUG hQP_sc hPR_sc])
      thus "\<exists>g. top1_is_path_on (\<Union>G) (subspace_topology X T (\<Union>G)) Q R g"
        unfolding top1_in_same_path_component_on_def by blast
    qed
  qed
qed

(** from \<S>1 Theorem 2 (geotop.tex:330)
    LATEX VERSION: Pathwise connectivity is preserved by surjective mappings. **)
theorem Theorem_GT_1_2:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hcont: "top1_continuous_map_on X TX Y TY f"
  assumes hsurj: "f ` X = Y"
  assumes hXpc: "top1_path_connected_on X TX"
  shows "top1_path_connected_on Y TY"
  (** Moise proof (geotop.tex:332): given P,Q \<in> Y, take P',Q' \<in> X with f(P')=P,
      f(Q')=Q. Get path p in X from P' to Q'. Then f \<circ> p is a path in Y from P to Q. **)
proof (unfold top1_path_connected_on_def, intro conjI hTY ballI)
  fix P Q
  assume hP: "P \<in> Y" and hQ: "Q \<in> Y"
  obtain P' where hP': "P' \<in> X" and hfP': "f P' = P"
    using hsurj hP by blast
  obtain Q' where hQ': "Q' \<in> X" and hfQ': "f Q' = Q"
    using hsurj hQ by blast
  have "\<exists>p. top1_is_path_on X TX P' Q' p"
    using hXpc hP' hQ' unfolding top1_path_connected_on_def by blast
  then obtain p where hp: "top1_is_path_on X TX P' Q' p" by blast
  have hpcont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX p"
    using hp unfolding top1_is_path_on_def by simp
  have hp0: "p 0 = P'" using hp unfolding top1_is_path_on_def by simp
  have hp1: "p 1 = Q'" using hp unfolding top1_is_path_on_def by simp
  have hfpcont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology Y TY (f \<circ> p)"
    by (rule top1_continuous_map_on_comp[OF hpcont hcont])
  have hfp0: "(f \<circ> p) 0 = P" using hp0 hfP' by simp
  have hfp1: "(f \<circ> p) 1 = Q" using hp1 hfQ' by simp
  have "top1_is_path_on Y TY P Q (f \<circ> p)"
    unfolding top1_is_path_on_def using hfpcont hfp0 hfp1 by simp
  thus "\<exists>g. top1_is_path_on Y TY P Q g" by blast
qed

(** from \<S>1: connected complex (geotop.tex:334)
    LATEX VERSION: A complex K is connected if it is not the union of two disjoint nonempty
      complexes. **)
definition geotop_complex_connected :: "'a::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_complex_connected K \<longleftrightarrow>
    geotop_is_complex K \<and>
    \<not>(\<exists>K1 K2. K1 \<noteq> {} \<and> K2 \<noteq> {} \<and> K1 \<inter> K2 = {} \<and> K = K1 \<union> K2
          \<and> geotop_is_complex K1 \<and> geotop_is_complex K2)"

(** Projections of the four conjuncts of \<open>geotop_is_complex\<close>, useful as
    cheap simp-callable lemmas (avoids re-unfolding the full def which has 4 conjuncts
    and blows by100 budget). **)
lemma geotop_is_complex_simplex:
  assumes "geotop_is_complex K"
  shows "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
  by (rule conjunct1[OF assms[unfolded geotop_is_complex_def]])

lemma geotop_is_complex_face_closed:
  assumes "geotop_is_complex K"
  shows "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
  by (rule conjunct1[OF conjunct2[OF assms[unfolded geotop_is_complex_def]]])

lemma geotop_is_complex_intersection:
  assumes "geotop_is_complex K"
  shows "\<forall>\<sigma>\<in>K. \<forall>\<tau>\<in>K. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
              geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
  by (rule conjunct1[OF conjunct2[OF conjunct2[OF assms[unfolded geotop_is_complex_def]]]])

lemma geotop_is_complex_locally_finite:
  assumes "geotop_is_complex K"
  shows "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
  by (rule conjunct2[OF conjunct2[OF conjunct2[OF assms[unfolded geotop_is_complex_def]]]])

(** Helper for Theorem 12 (Moise's proof of (3)\<Rightarrow>(1)): if K1, K2 are disjoint
    subcomplexes of a complex K, then the point-sets \<bar>K1\<close> and \<bar>K2\<close> are disjoint.
    Uses K.2 (intersection compatibility) plus face-closure in K1 and K2. **)
lemma geotop_disjoint_subcomplex_polyhedra_disjoint:
  fixes K K1 K2 :: "'a::real_normed_vector set set"
  assumes hK: "geotop_is_complex K"
  assumes hK1: "geotop_is_complex K1" and hK1sub: "K1 \<subseteq> K"
  assumes hK2: "geotop_is_complex K2" and hK2sub: "K2 \<subseteq> K"
  assumes hdisj: "K1 \<inter> K2 = {}"
  shows "geotop_polyhedron K1 \<inter> geotop_polyhedron K2 = {}"
proof (rule ccontr)
  assume "geotop_polyhedron K1 \<inter> geotop_polyhedron K2 \<noteq> {}"
  then obtain P where hP: "P \<in> geotop_polyhedron K1 \<inter> geotop_polyhedron K2"
    by (by100 blast)
  obtain \<sigma> where h\<sigma>K1: "\<sigma> \<in> K1" and hP\<sigma>: "P \<in> \<sigma>"
    using hP unfolding geotop_polyhedron_def by (by100 blast)
  obtain \<tau> where h\<tau>K2: "\<tau> \<in> K2" and hP\<tau>: "P \<in> \<tau>"
    using hP unfolding geotop_polyhedron_def by (by100 blast)
  have h\<sigma>K: "\<sigma> \<in> K" using h\<sigma>K1 hK1sub by (by100 blast)
  have h\<tau>K: "\<tau> \<in> K" using h\<tau>K2 hK2sub by (by100 blast)
  have hintne: "\<sigma> \<inter> \<tau> \<noteq> {}" using hP\<sigma> hP\<tau> by (by100 blast)
  have hface_\<sigma>: "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma>"
    using h\<sigma>K h\<tau>K hintne geotop_is_complex_intersection[OF hK] by (by100 blast)
  have hface_\<tau>: "geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    using h\<sigma>K h\<tau>K hintne geotop_is_complex_intersection[OF hK] by (by100 blast)
  have hinter_K1: "\<sigma> \<inter> \<tau> \<in> K1"
    using h\<sigma>K1 hface_\<sigma> geotop_is_complex_face_closed[OF hK1] by (by100 blast)
  have hinter_K2: "\<sigma> \<inter> \<tau> \<in> K2"
    using h\<tau>K2 hface_\<tau> geotop_is_complex_face_closed[OF hK2] by (by100 blast)
  have "\<sigma> \<inter> \<tau> \<in> K1 \<inter> K2" using hinter_K1 hinter_K2 by (by100 blast)
  then show False using hdisj by (by100 blast)
qed

(** A simplex is nonempty (V has card \<ge> 1, contained in the hull). **)
lemma geotop_is_simplex_nonempty:
  fixes \<sigma> :: "'a::real_vector set"
  assumes "geotop_is_simplex \<sigma>"
  shows "\<sigma> \<noteq> {}"
proof -
  obtain V n where hfin: "finite V" and hcard: "card V = n + 1"
              and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using assms unfolding geotop_is_simplex_def by (by100 blast)
  have hVne: "V \<noteq> {}" using hcard by (by100 auto)
  have hV_in_hull: "V \<subseteq> geotop_convex_hull V"
    unfolding geotop_convex_hull_eq_HOL by (rule hull_subset)
  have "V \<subseteq> \<sigma>" using h\<sigma>_eq hV_in_hull by (by100 simp)
  then show ?thesis using hVne by (by100 blast)
qed

(** A simplex is closed in \<open>real_normed_vector\<close> (compact = convex hull of finite points). **)
lemma geotop_is_simplex_closed:
  fixes \<sigma> :: "'a::real_normed_vector set"
  assumes "geotop_is_simplex \<sigma>"
  shows "closed \<sigma>"
proof -
  obtain V m n where hV: "finite V" and "\<sigma> = geotop_convex_hull V"
    using assms unfolding geotop_is_simplex_def by (by100 blast)
  then have h\<sigma>_eq: "\<sigma> = convex hull V"
    using geotop_convex_hull_eq_HOL by (by100 simp)
  have hcpt: "compact \<sigma>" using hV h\<sigma>_eq finite_imp_compact_convex_hull by (by100 simp)
  then show ?thesis using compact_imp_closed by (by100 blast)
qed

(** A simplex is compact. **)
lemma geotop_is_simplex_compact:
  fixes \<sigma> :: "'a::real_normed_vector set"
  assumes "geotop_is_simplex \<sigma>"
  shows "compact \<sigma>"
proof -
  obtain V m n where hV: "finite V" and "\<sigma> = geotop_convex_hull V"
    using assms unfolding geotop_is_simplex_def by (by100 blast)
  then have "\<sigma> = convex hull V"
    using geotop_convex_hull_eq_HOL by (by100 simp)
  then show ?thesis using hV finite_imp_compact_convex_hull by (by100 simp)
qed

(** Key technical lemma for GT_1_12 (3)\<Rightarrow>(1): for P \<in> a simplex of a complex K,
    every simplex of K that does not contain P stays at positive distance from P.
    Uses K.4 (local finiteness) plus compactness of finitely many simplexes.
    Moise's observation: no point v \<in> \<bar>K\<close> is a limit point of \<union>{\<tau>\<in>K: v\<notin>\<tau>}.

    PROOF STRATEGY (deferred): use locally finiteness to extract finite collection
    {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}} around \<sigma>. Among these, the ones not containing P are
    finite closed sets not containing P, so \<open>infdist P \<tau> > 0\<close>. Taking min over a
    finite set plus a bound for the ambient U-neighborhood ball gives \<epsilon>. **)
(** Helper 1: a closed set not containing a point has a ball-avoiding neighborhood. **)
lemma geotop_ball_avoids_closed_not_containing:
  fixes C :: "'a::metric_space set" and P :: 'a
  assumes hC_closed: "closed C" and hC_ne: "C \<noteq> {}" and hP: "P \<notin> C"
  shows "\<exists>d>0. ball P d \<inter> C = {}"
proof -
  have hpos: "infdist P C > 0"
  proof -
    have hne0: "infdist P C \<noteq> 0"
      using in_closed_iff_infdist_zero[OF hC_closed hC_ne] hP by (by100 blast)
    have "infdist P C \<ge> 0" by (rule infdist_nonneg)
    then show ?thesis using hne0 by (by100 linarith)
  qed
  have hlb: "\<forall>x\<in>C. dist P x \<ge> infdist P C"
    using infdist_le by (by100 blast)
  have hball: "ball P (infdist P C) \<inter> C = {}"
  proof (rule ccontr)
    assume "ball P (infdist P C) \<inter> C \<noteq> {}"
    then obtain x where hxC: "x \<in> C" and hxball: "x \<in> ball P (infdist P C)"
      by (by100 blast)
    have "dist P x < infdist P C" using hxball unfolding ball_def by (by100 simp)
    moreover have "dist P x \<ge> infdist P C" using hlb hxC by (by100 blast)
    ultimately show False by (by100 linarith)
  qed
  show ?thesis using hpos hball by (by100 blast)
qed

(** Helper 2: for a simplex \<tau> not containing P, exists d > 0 avoiding \<tau> in ball P d. **)
lemma geotop_ball_avoids_simplex:
  fixes \<tau> :: "'a::real_normed_vector set" and P :: 'a
  assumes h\<tau>: "geotop_is_simplex \<tau>" and hP: "P \<notin> \<tau>"
  shows "\<exists>d>0. ball P d \<inter> \<tau> = {}"
  by (rule geotop_ball_avoids_closed_not_containing
           [OF geotop_is_simplex_closed[OF h\<tau>]
               geotop_is_simplex_nonempty[OF h\<tau>]
               hP])

(** Helper 3: for a finite union of sets, each with positive avoidance radius,
    take the min to get positive avoidance for the union. **)
lemma geotop_ball_avoids_finite_union:
  fixes \<S> :: "'a::metric_space set set" and P :: 'a
  assumes hfin: "finite \<S>"
  assumes havoid: "\<forall>s\<in>\<S>. \<exists>d>0. ball P d \<inter> s = {}"
  shows "\<exists>d>0. ball P d \<inter> \<Union>\<S> = {}"
proof -
  have hf: "\<exists>f. \<forall>s\<in>\<S>. f s > 0 \<and> ball P (f s) \<inter> s = {}"
    using havoid by (by100 metis)
  then obtain f where hf: "\<forall>s\<in>\<S>. f s > 0 \<and> ball P (f s) \<inter> s = {}"
    by (by100 blast)
  show ?thesis
  proof (cases "\<S> = {}")
    case True
    have h1: "(1::real) > 0" by (by100 simp)
    have h2: "ball P 1 \<inter> \<Union>\<S> = {}" unfolding True by (by100 simp)
    show ?thesis using h1 h2 by (by100 blast)
  next
    case False
    have hfinS: "finite (f ` \<S>)" using hfin by (by100 simp)
    have hneS: "f ` \<S> \<noteq> {}" using False by (by100 simp)
    have hposall: "\<forall>x\<in>f ` \<S>. x > 0" using hf by (by100 blast)
    let ?d = "Min (f ` \<S>)"
    have hd_pos: "?d > 0" using Min_gr_iff[OF hfinS hneS] hposall by (by100 blast)
    have hd_le: "\<forall>s\<in>\<S>. ?d \<le> f s" using Min_le[OF hfinS] by (by100 blast)
    have havoid_all: "ball P ?d \<inter> \<Union>\<S> = {}"
    proof (rule ccontr)
      assume "ball P ?d \<inter> \<Union>\<S> \<noteq> {}"
      then obtain x s where hx: "x \<in> ball P ?d" and hs: "s \<in> \<S>" and hxs: "x \<in> s"
        by (by100 blast)
      have "ball P ?d \<subseteq> ball P (f s)"
        using hd_le[rule_format, OF hs] by (rule subset_ball)
      then have hxfs: "x \<in> ball P (f s)" using hx by (by100 blast)
      have "ball P (f s) \<inter> s = {}" using hf hs by (by100 blast)
      then show False using hxfs hxs by (by100 blast)
    qed
    show ?thesis using hd_pos havoid_all by (by100 blast)
  qed
qed

(** Key technical lemma for GT_1_12 (3)\<Rightarrow>(1): for P in a simplex \<sigma> of a complex K,
    every simplex of K that does not contain P stays at positive distance from P.
    Uses local finiteness + Helper 2 + Helper 3. **)
lemma geotop_complex_point_avoidance:
  fixes K :: "'a::real_normed_vector set set"
  fixes \<sigma> :: "'a set" and P :: 'a
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K" and hP\<sigma>: "P \<in> \<sigma>"
  shows "\<exists>\<epsilon>>0. ball P \<epsilon> \<inter> \<Union>{\<tau>\<in>K. P \<notin> \<tau>} = {}"
proof -
  have hLF: "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    using geotop_is_complex_locally_finite[OF hK] h\<sigma>K by (by100 blast)
  (** Step 1: get a locally-finite open neighborhood U around \<sigma>. **)
  obtain U where hUopen: "open U" and hU\<sigma>: "\<sigma> \<subseteq> U"
           and hUfin: "finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    using hLF by (by100 blast)
  have hPU: "P \<in> U" using hP\<sigma> hU\<sigma> by (by100 blast)
  (** Step 2: pick a ball of radius r0 around P inside U. **)
  have "\<exists>r>0. ball P r \<subseteq> U"
    using hUopen hPU open_contains_ball by (by100 blast)
  then obtain r0 where hr0: "r0 > 0" and hr0U: "ball P r0 \<subseteq> U"
    by (by100 blast)
  (** Step 3: let ?N be the finite collection of simplexes meeting U but not
     containing P; each has a positive avoidance radius by Helper 2. **)
  let ?N = "{\<tau>\<in>K. \<tau> \<inter> U \<noteq> {} \<and> P \<notin> \<tau>}"
  have hNfin: "finite ?N"
    using hUfin rev_finite_subset[of "{\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}" ?N] by (by100 blast)
  have hNavoid: "\<forall>\<tau>\<in>?N. \<exists>d>0. ball P d \<inter> \<tau> = {}"
  proof
    fix \<tau> assume h\<tau>N: "\<tau> \<in> ?N"
    have "\<tau> \<in> K" and "P \<notin> \<tau>" using h\<tau>N by (by100 auto)
    then show "\<exists>d>0. ball P d \<inter> \<tau> = {}"
      using geotop_ball_avoids_simplex geotop_is_complex_simplex[OF hK]
      by (by100 blast)
  qed
  (** Step 4: take the min avoidance radius via Helper 3. **)
  have havoidN: "\<exists>d>0. ball P d \<inter> \<Union>?N = {}"
    by (rule geotop_ball_avoids_finite_union[OF hNfin hNavoid])
  then obtain d1 where hd1: "d1 > 0" and hd1N: "ball P d1 \<inter> \<Union>?N = {}"
    by (by100 auto)
  (** Step 5: take \<epsilon> = min(r0, d1). Inside ball P \<epsilon>, points are in U AND avoid all of ?N. **)
  let ?\<epsilon> = "min r0 d1"
  have h\<epsilon>pos: "?\<epsilon> > 0" using hr0 hd1 by (by100 simp)
  have h\<epsilon>_r0: "?\<epsilon> \<le> r0" by (by100 simp)
  have h\<epsilon>_d1: "?\<epsilon> \<le> d1" by (by100 simp)
  have h\<epsilon>sub_r0: "ball P ?\<epsilon> \<subseteq> ball P r0"
    by (rule subset_ball[OF h\<epsilon>_r0])
  have h\<epsilon>sub_d1: "ball P ?\<epsilon> \<subseteq> ball P d1"
    by (rule subset_ball[OF h\<epsilon>_d1])
  have h\<epsilon>sub_U: "ball P ?\<epsilon> \<subseteq> U" using h\<epsilon>sub_r0 hr0U by (by100 blast)
  have h\<epsilon>avoidN: "ball P ?\<epsilon> \<inter> \<Union>?N = {}" using h\<epsilon>sub_d1 hd1N by (by100 blast)
  (** Step 6: any simplex \<tau> \<in> K not containing P, if it meets ball P ?\<epsilon>, belongs to ?N
     (since ball P ?\<epsilon> \<subseteq> U). **)
  have h\<epsilon>final: "ball P ?\<epsilon> \<inter> \<Union>{\<tau>\<in>K. P \<notin> \<tau>} = {}"
  proof (rule ccontr)
    assume "ball P ?\<epsilon> \<inter> \<Union>{\<tau>\<in>K. P \<notin> \<tau>} \<noteq> {}"
    then obtain x \<tau>' where hx: "x \<in> ball P ?\<epsilon>" and h\<tau>'K: "\<tau>' \<in> K"
                and hPnotin: "P \<notin> \<tau>'" and hx\<tau>': "x \<in> \<tau>'"
      by (by100 blast)
    have hxU: "x \<in> U" using hx h\<epsilon>sub_U by (by100 blast)
    have h\<tau>'_meets: "\<tau>' \<inter> U \<noteq> {}" using hxU hx\<tau>' by (by100 blast)
    have h\<tau>'N: "\<tau>' \<in> ?N" using h\<tau>'K hPnotin h\<tau>'_meets by (by100 simp)
    have hxU_N: "x \<in> \<Union>?N" using h\<tau>'N hx\<tau>' by (by100 blast)
    then show False using hx h\<epsilon>avoidN by (by100 blast)
  qed
  show ?thesis using h\<epsilon>pos h\<epsilon>final by (by100 blast)
qed

text \<open>Moise's \<S>1 Theorem 3: every simplex is pathwise connected, because
  it is convex, and the straight-line path between any two points of a
  convex set is continuous.\<close>

(** The convex hull of a set is convex in Moise's sense. **)
lemma geotop_convex_hull_is_convex:
  fixes V :: "'a::real_vector set"
  shows "geotop_convex (geotop_convex_hull V)"
  unfolding geotop_convex_hull_def geotop_convex_def geotop_segment_def by blast

(** A simplex is convex (as a convex hull of its vertex set). **)
lemma geotop_simplex_is_convex:
  fixes \<sigma> :: "'a::real_vector set"
  assumes "geotop_is_simplex \<sigma>"
  shows "geotop_convex \<sigma>"
  by (metis assms geotop_convex_hull_is_convex geotop_is_simplex_def)

(** Every vertex of a simplex belongs to the simplex. **)
lemma geotop_simplex_vertices_subset:
  fixes V :: "'a::real_vector set"
  shows "V \<subseteq> geotop_convex_hull V"
  by (metis geotop_convex_hull_eq_HOL hull_subset)

(** A simplex is nonempty (it contains its vertices). **)
lemma geotop_simplex_nonempty:
  fixes \<sigma> :: "'a::real_vector set"
  assumes "geotop_is_simplex \<sigma>"
  shows "\<sigma> \<noteq> {}"
proof -
  obtain V m n where hV: "finite V" "card V = n + 1"
                    "\<sigma> = geotop_convex_hull V"
    using assms unfolding geotop_is_simplex_def by blast
  have hVne: "V \<noteq> {}" using hV(2) by force
  have hsub: "V \<subseteq> \<sigma>"
    by (simp add: geotop_simplex_vertices_subset hV(3))
  show ?thesis using hVne hsub by blast
qed

(** A simplex is always a face of itself. **)
lemma geotop_is_face_refl_of_simplex:
  fixes \<sigma> :: "'a::real_vector set"
  assumes "geotop_is_simplex \<sigma>"
  shows "geotop_is_face \<sigma> \<sigma>"
proof -
  obtain V m n where hV: "finite V" "card V = n + 1" "n \<le> m"
                     "geotop_general_position V m" "\<sigma> = geotop_convex_hull V"
    using assms unfolding geotop_is_simplex_def by blast
  have hVne: "V \<noteq> {}" using hV(2) by force
  have hSV: "geotop_simplex_vertices \<sigma> V"
    unfolding geotop_simplex_vertices_def using hV by blast
  show ?thesis
    unfolding geotop_is_face_def
    using hSV hVne hV(5) by blast
qed

(** A \<sigma> with a known simplex-dimension is in particular a simplex. **)
lemma geotop_simplex_dim_imp_is_simplex:
  fixes \<sigma> :: "'a::real_vector set"
  assumes "geotop_simplex_dim \<sigma> k"
  shows "geotop_is_simplex \<sigma>"
  using assms unfolding geotop_is_simplex_def geotop_simplex_dim_def by blast

(** Moise's \`geotop_segment\` agrees with HOL's \`closed_segment\`. **)
lemma geotop_segment_eq_closed_segment:
  fixes v w :: "'a::real_vector"
  shows "geotop_segment v w = closed_segment v w"
proof
  show "geotop_segment v w \<subseteq> closed_segment v w"
  proof
    fix u assume "u \<in> geotop_segment v w"
    then obtain \<alpha> \<beta> where h\<alpha>: "\<alpha> \<ge> 0" and h\<beta>: "\<beta> \<ge> 0" and hsum: "\<alpha> + \<beta> = 1"
                      and hu: "u = \<alpha> *\<^sub>R v + \<beta> *\<^sub>R w"
      unfolding geotop_segment_def by blast
    have h\<beta>1: "\<beta> \<le> 1" using h\<alpha> hsum by linarith
    have h\<alpha>eq: "\<alpha> = 1 - \<beta>" using hsum by simp
    have "u = (1 - \<beta>) *\<^sub>R v + \<beta> *\<^sub>R w" using hu h\<alpha>eq by simp
    thus "u \<in> closed_segment v w"
      unfolding closed_segment_def using h\<beta> h\<beta>1 by blast
  qed
next
  show "closed_segment v w \<subseteq> geotop_segment v w"
  proof
    fix u assume "u \<in> closed_segment v w"
    then obtain t where ht0: "0 \<le> t" and ht1: "t \<le> 1"
                    and hu: "u = (1 - t) *\<^sub>R v + t *\<^sub>R w"
      unfolding closed_segment_def by blast
    have h1mt: "(1 - t) \<ge> 0" using ht1 by simp
    have hsum: "(1 - t) + t = 1" by simp
    show "u \<in> geotop_segment v w"
      unfolding geotop_segment_def using h1mt ht0 hsum hu by blast
  qed
qed

(** If W is a nonempty subset of a vertex set of \<sigma>, then the convex hull of W
    is a face of \<sigma>. **)
lemma geotop_is_face_of_subset:
  fixes \<sigma> :: "'a::real_vector set" and V W :: "'a set"
  assumes hSV: "geotop_simplex_vertices \<sigma> V"
  assumes hWne: "W \<noteq> {}"
  assumes hWsub: "W \<subseteq> V"
  shows "geotop_is_face (geotop_convex_hull W) \<sigma>"
  unfolding geotop_is_face_def using hSV hWne hWsub by blast

(** The only vertex-witness of a singleton simplex is the singleton itself. **)
lemma geotop_singleton_simplex_vertices:
  fixes P :: "'a::real_normed_vector" and V :: "'a set"
  assumes "geotop_simplex_vertices {P} V"
  shows "V = {P}"
proof -
  from assms obtain m n where hV: "finite V" "card V = n + 1" "n \<le> m"
                          "geotop_general_position V m" "{P} = geotop_convex_hull V"
    unfolding geotop_simplex_vertices_def by blast
  have hVne: "V \<noteq> {}" using hV(2) by force
  have hVsub: "V \<subseteq> geotop_convex_hull V"
    by (rule geotop_simplex_vertices_subset)
  have hVsubP: "V \<subseteq> {P}" using hV(5) hVsub by simp
  show "V = {P}" using hVne hVsubP by blast
qed

(** The only vertex-witness of a closed-segment simplex (with distinct endpoints)
    is the endpoint pair \<open>{P, Q}\<close>. Requires `euclidean_space` so that HOL's
    `closed_segment_eq` (nondegenerate segments have unique endpoint pairs) applies. **)
lemma geotop_segment_simplex_vertices:
  fixes P Q :: "'a::euclidean_space" and V :: "'a set"
  assumes hne: "P \<noteq> Q"
  assumes hSV: "geotop_simplex_vertices (closed_segment P Q) V"
  shows "V = {P, Q}"
proof -
  from hSV obtain m n where hV_fin: "finite V" and hV_card: "card V = n + 1"
                        and hnm: "n \<le> m" and hgp: "geotop_general_position V m"
                        and hV_cvx: "closed_segment P Q = geotop_convex_hull V"
    unfolding geotop_simplex_vertices_def by blast
  (** V \<subseteq> closed_segment P Q. **)
  have hVsub: "V \<subseteq> closed_segment P Q"
    using geotop_simplex_vertices_subset hV_cvx by metis
  (** V is nonempty, card \<ge> 1. **)
  have hVne: "V \<noteq> {}" using hV_card by force
  (** Step 1: card V \<ge> 2 (else convex_hull V = singleton, not closed_segment). **)
  have hcard_ge2: "card V \<ge> 2"
  proof (rule ccontr)
    assume hnot2: "\<not> 2 \<le> card V"
    have hcard_le1: "card V \<le> 1" using hnot2 by simp
    have hcard_ge1: "card V \<ge> 1" using hVne hV_fin by (simp add: Suc_leI card_gt_0_iff)
    have hcard1: "card V = 1" using hcard_le1 hcard_ge1 by linarith
    obtain v where hVv: "V = {v}" using hcard1 card_1_singletonE by metis
    have hhull_HOL: "geotop_convex_hull V = convex hull V"
      by (rule geotop_convex_hull_eq_HOL)
    have hcvx_sing: "convex hull {v} = {v}" by simp
    have hhull_sing: "geotop_convex_hull V = {v}"
      using hhull_HOL hVv hcvx_sing by simp
    have hseg_sing: "closed_segment P Q = {v}" using hV_cvx hhull_sing by simp
    have hPinseg: "P \<in> closed_segment P Q" by simp
    have "P = v" using hPinseg hseg_sing by blast
    moreover have "Q = v" using hseg_sing by auto
    ultimately show False using hne by simp
  qed
  (** Step 2: card V \<le> 2. Suppose card V \<ge> 3, i.e., n \<ge> 2, so m \<ge> 2.
      The 1-dim hyperplane through P, Q contains V (all collinear). general_position
      with k=1 < m says |V \<inter> H| \<le> 2, but |V \<inter> H| = |V| \<ge> 3. **)
  have hcard_le2: "card V \<le> 2"
  proof (rule ccontr)
    assume hnot: "\<not> card V \<le> 2"
    have hcard3: "card V \<ge> 3" using hnot by simp
    have hn2: "n \<ge> 2" using hV_card hcard3 by linarith
    have hm2: "m \<ge> 2" using hnm hn2 by linarith
    (** Build the 1-dim hyperplane H containing P, Q. **)
    define H :: "'a set" where "H = (\<lambda>v. v + P) ` span {Q - P}"
    have hsub_span: "subspace (span {Q - P})" by (rule subspace_span)
    have hQP_nz: "Q - P \<noteq> 0" using hne by simp
    have hB_indep: "independent {Q - P}"
      using hQP_nz by (metis dependent_single empty_subsetI independent_empty independent_insert insert_Diff insert_absorb2)
    have hB_fin: "finite {Q - P}" by simp
    have hB_card: "card {Q - P} = 1" by simp
    have hB_span: "span {Q - P} = span {Q - P}" by simp
    have hhyp1: "geotop_hyperplane_dim H 1"
      unfolding geotop_hyperplane_dim_def H_def
      using hsub_span hB_indep hB_fin hB_card hB_span by blast
    (** V \<subseteq> H: every v \<in> V is on line through P, Q. **)
    have hVsubH: "V \<subseteq> H"
    proof
      fix v assume hvV: "v \<in> V"
      have hvseg: "v \<in> closed_segment P Q" using hVsub hvV by blast
      then obtain t where ht: "0 \<le> t" "t \<le> 1" and hv_eq: "v = (1 - t) *\<^sub>R P + t *\<^sub>R Q"
        unfolding closed_segment_def by blast
      have hv_alt: "v = P + t *\<^sub>R (Q - P)"
        using hv_eq by (simp add: scaleR_diff_right scaleR_left_diff_distrib)
      have ht_span: "t *\<^sub>R (Q - P) \<in> span {Q - P}"
        by (rule span_mul[OF span_base[of "Q - P" "{Q - P}"]]) simp
      have "v \<in> (\<lambda>u. u + P) ` span {Q - P}"
        using hv_alt ht_span by (simp add: image_iff add.commute)
      thus "v \<in> H" unfolding H_def by simp
    qed
    have hVint: "V \<inter> H = V" using hVsubH by blast
    have hcard_int: "card (V \<inter> H) = card V" using hVint by simp
    have hk_lt_m: "(1::nat) < m" using hm2 by simp
    have hgp_bound: "card (V \<inter> H) \<le> 1 + 1"
      using hgp hhyp1 hk_lt_m unfolding geotop_general_position_def by blast
    have "card V \<le> 2" using hcard_int hgp_bound by simp
    thus False using hcard3 by simp
  qed
  (** Hence card V = 2. **)
  have hcard2: "card V = 2" using hcard_ge2 hcard_le2 by linarith
  (** Step 3: write V = {a, b}, a \<noteq> b; show {a, b} = {P, Q} via `closed_segment_eq`. **)
  obtain a b where hV_eq: "V = {a, b}" and hab_ne: "a \<noteq> b"
    using hcard2 by (metis card_2_iff)
  have hhull_ab: "geotop_convex_hull V = convex hull {a, b}"
    unfolding hV_eq by (rule geotop_convex_hull_eq_HOL)
  have hhull_ab_seg: "convex hull {a, b} = closed_segment a b"
    by (simp add: segment_convex_hull)
  have hseg_eq: "closed_segment a b = closed_segment P Q"
    using hV_cvx hhull_ab hhull_ab_seg by simp
  have hab_set: "{a, b} = {P, Q}"
    using hseg_eq closed_segment_eq by blast
  show "V = {P, Q}" using hV_eq hab_set by simp
qed

text \<open>\<open>top1_ball_on_UNIV_norm_eq_ball\<close> and \<open>geotop_euclidean_topology_eq_open_sets\<close>
  moved earlier in the file (right after \<open>geotop_euclidean_topology\<close> def) so the
  early.tex infrastructure can use them.\<close>

(** Vertex set is a subset of the convex hull. **)
lemma geotop_convex_hull_contains_V: "V \<subseteq> geotop_convex_hull V"
  unfolding geotop_convex_hull_def by blast

(** The identity is a homeomorphism from any topology to itself. **)
lemma top1_homeomorphism_on_id:
  assumes hT: "is_topology_on X TX"
  shows "top1_homeomorphism_on X TX X TX id"
  unfolding top1_homeomorphism_on_def
proof (intro conjI)
  show "is_topology_on X TX" using hT .
  show "is_topology_on X TX" using hT .
  show "bij_betw id X X" unfolding bij_betw_def by simp
  have hX_in: "X \<in> TX"
    using hT unfolding is_topology_on_def by blast
  have h_finint: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TX \<longrightarrow> \<Inter>F \<in> TX"
    using hT unfolding is_topology_on_def by blast
  have h_id_cont: "top1_continuous_map_on X TX X TX id"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>X. id x \<in> X" by simp
    show "\<forall>V\<in>TX. {x\<in>X. id x \<in> V} \<in> TX"
    proof
      fix V assume hV: "V \<in> TX"
      have h_eq: "{x\<in>X. id x \<in> V} = X \<inter> V" by auto
      have h_finF: "finite {X, V}" by simp
      have h_ne: "{X, V} \<noteq> {}" by simp
      have h_sub: "{X, V} \<subseteq> TX" using hX_in hV by simp
      have h_int: "\<Inter>{X, V} \<in> TX"
        using h_finint h_finF h_ne h_sub by blast
      have h_int_eq: "\<Inter>{X, V} = X \<inter> V" by auto
      show "{x\<in>X. id x \<in> V} \<in> TX" using h_eq h_int h_int_eq by simp
    qed
  qed
  show "top1_continuous_map_on X TX X TX id"
    using h_id_cont .
  show "top1_continuous_map_on X TX X TX (inv_into X id)"
  proof -
    have hinj: "inj_on id X" by simp
    have h_eq: "\<forall>x\<in>X. inv_into X id x = x"
    proof
      fix x assume hxX: "x \<in> X"
      have "id x = x" by simp
      hence "inv_into X id (id x) = x"
        using hxX hinj inv_into_f_f[of id X x] by simp
      thus "inv_into X id x = x" by simp
    qed
    show ?thesis
      using top1_continuous_map_on_cong[OF h_eq] h_id_cont by (simp add: id_def)
  qed
qed

(** A simplex of dim n is an n-cell (identity is the witness homeomorphism). **)
lemma geotop_simplex_is_n_cell:
  fixes \<sigma> :: "'a::real_normed_vector set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> n"
  shows "geotop_is_n_cell \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) n"
proof -
  have h_Teucl: "is_topology_on (UNIV::'a set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have h\<sigma>_sub: "\<sigma> \<subseteq> UNIV" by simp
  have h\<sigma>_top: "is_topology_on \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>)"
    by (rule subspace_topology_is_topology_on[OF h_Teucl h\<sigma>_sub])
  have h_id: "top1_homeomorphism_on \<sigma>
         (subspace_topology UNIV geotop_euclidean_topology \<sigma>)
         \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) id"
    by (rule top1_homeomorphism_on_id[OF h\<sigma>_top])
  show ?thesis
    unfolding geotop_is_n_cell_def
    using h\<sigma>_top h\<sigma> h_id by (by100 blast)
qed

(** Composition of homeomorphisms is a homeomorphism. **)
lemma top1_homeomorphism_on_comp:
  assumes hf: "top1_homeomorphism_on X TX Y TY f"
  assumes hg: "top1_homeomorphism_on Y TY Z TZ g"
  shows "top1_homeomorphism_on X TX Z TZ (g \<circ> f)"
  unfolding top1_homeomorphism_on_def
proof (intro conjI)
  show "is_topology_on X TX"
    using hf unfolding top1_homeomorphism_on_def by blast
  show "is_topology_on Z TZ"
    using hg unfolding top1_homeomorphism_on_def by blast
  have hbijf: "bij_betw f X Y"
    using hf unfolding top1_homeomorphism_on_def by blast
  have hbijg: "bij_betw g Y Z"
    using hg unfolding top1_homeomorphism_on_def by blast
  show "bij_betw (g \<circ> f) X Z"
    using hbijf hbijg bij_betw_trans by blast
  have hfcont: "top1_continuous_map_on X TX Y TY f"
    using hf unfolding top1_homeomorphism_on_def by blast
  have hgcont: "top1_continuous_map_on Y TY Z TZ g"
    using hg unfolding top1_homeomorphism_on_def by blast
  show "top1_continuous_map_on X TX Z TZ (g \<circ> f)"
    by (rule top1_continuous_map_on_comp[OF hfcont hgcont])
  (** Inverse of g \<circ> f is (inv f) \<circ> (inv g), which is continuous. **)
  have hinvf: "top1_continuous_map_on Y TY X TX (inv_into X f)"
    using hf unfolding top1_homeomorphism_on_def by blast
  have hinvg: "top1_continuous_map_on Z TZ Y TY (inv_into Y g)"
    using hg unfolding top1_homeomorphism_on_def by blast
  have hinv_comp: "top1_continuous_map_on Z TZ X TX (inv_into X f \<circ> inv_into Y g)"
    by (rule top1_continuous_map_on_comp[OF hinvg hinvf])
  have h_inv_eq: "\<forall>z\<in>Z. inv_into X (g \<circ> f) z = (inv_into X f \<circ> inv_into Y g) z"
  proof
    fix z assume hzZ: "z \<in> Z"
    have hbij_comp: "bij_betw (g \<circ> f) X Z"
      using hbijf hbijg bij_betw_trans by blast
    obtain x where hxX: "x \<in> X" and hgfx: "(g \<circ> f) x = z"
      using hzZ hbij_comp unfolding bij_betw_def by blast
    have hinv_comp_z: "inv_into X (g \<circ> f) z = x"
      using hxX hgfx hbij_comp unfolding bij_betw_def
      by (metis inv_into_f_f)
    have hfxY: "f x \<in> Y" using hxX hbijf unfolding bij_betw_def by blast
    have hg_fx: "g (f x) = z" using hgfx by simp
    have hinv_g: "inv_into Y g z = f x"
      using hfxY hg_fx hbijg unfolding bij_betw_def
      by (metis inv_into_f_f)
    have hinv_f: "inv_into X f (f x) = x"
      using hxX hbijf unfolding bij_betw_def
      by (metis inv_into_f_f)
    show "inv_into X (g \<circ> f) z = (inv_into X f \<circ> inv_into Y g) z"
      using hinv_comp_z hinv_g hinv_f by simp
  qed
  show "top1_continuous_map_on Z TZ X TX (inv_into X (g \<circ> f))"
    using top1_continuous_map_on_cong[OF h_inv_eq] hinv_comp by blast
qed

(** Homeomorphism is symmetric: the inverse of a homeomorphism is a homeomorphism. **)
lemma top1_homeomorphism_on_sym:
  assumes hf: "top1_homeomorphism_on X TX Y TY f"
  shows "top1_homeomorphism_on Y TY X TX (inv_into X f)"
  unfolding top1_homeomorphism_on_def
proof (intro conjI)
  show "is_topology_on Y TY"
    using hf unfolding top1_homeomorphism_on_def by blast
  show "is_topology_on X TX"
    using hf unfolding top1_homeomorphism_on_def by blast
  have hbij: "bij_betw f X Y"
    using hf unfolding top1_homeomorphism_on_def by blast
  show "bij_betw (inv_into X f) Y X"
    using hbij bij_betw_inv_into by blast
  show "top1_continuous_map_on Y TY X TX (inv_into X f)"
    using hf unfolding top1_homeomorphism_on_def by blast
  (** The inverse of the inverse equals f on X. **)
  have hfcont: "top1_continuous_map_on X TX Y TY f"
    using hf unfolding top1_homeomorphism_on_def by blast
  have hbij_fX: "f ` X = Y"
    using hbij unfolding bij_betw_def by blast
  have hinv_inv_eq: "\<forall>x\<in>X. inv_into Y (inv_into X f) x = f x"
  proof
    fix x assume hxX: "x \<in> X"
    have hbij_inv: "bij_betw (inv_into X f) Y X"
      using hbij bij_betw_inv_into by blast
    have h1: "inv_into Y (inv_into X f) x = inv_into Y (inv_into X f) x" by simp
    have "inv_into X f (f x) = x"
      using hxX hbij unfolding bij_betw_def by (metis inv_into_f_f)
    moreover have "f x \<in> Y" using hxX hbij_fX by blast
    ultimately show "inv_into Y (inv_into X f) x = f x"
      using hbij_inv by (metis bij_betw_inv_into_left \<open>f x \<in> Y\<close>)
  qed
  show "top1_continuous_map_on X TX Y TY (inv_into Y (inv_into X f))"
    using top1_continuous_map_on_cong[OF hinv_inv_eq] hfcont by blast
qed

(** The \<epsilon>-neighborhood of a set A in a real_normed_vector space is open
    in the Euclidean topology. **)
lemma geotop_nbhd_set_open_in_euclidean:
  fixes A :: "'a::real_normed_vector set" and \<epsilon> :: real
  assumes h\<epsilon>: "\<epsilon> > 0"
  shows "geotop_nbhd_set UNIV (\<lambda>x y. norm (x - y)) A \<epsilon> \<in> geotop_euclidean_topology"
proof -
  have h_set_eq: "geotop_nbhd_set UNIV (\<lambda>x y. norm (x - y)) A \<epsilon>
                  = (\<Union>P\<in>A. ball P \<epsilon>)"
    unfolding geotop_nbhd_set_def dist_norm
    by (auto simp: dist_norm)
  have h_open: "open (\<Union>P\<in>A. ball P \<epsilon>)" by (rule open_UN) auto
  have h_in_open_sets: "(\<Union>P\<in>A. ball P \<epsilon>) \<in> top1_open_sets"
    using h_open unfolding top1_open_sets_def by simp
  show ?thesis
    using h_set_eq h_in_open_sets
    unfolding geotop_euclidean_topology_eq_open_sets by simp
qed

(** Continuous maps from a real subspace into a real_normed_vector subspace
    (via the top1_open_sets topology). Mirror of
    \<open>top1_continuous_map_on_real_subspace_open_sets\<close> but with
    real_normed_vector codomain. **)
lemma top1_continuous_map_on_real_to_normed_subspace_open_sets:
  fixes S :: "real set" and T :: "'a::real_normed_vector set"
  fixes f :: "real \<Rightarrow> 'a"
  assumes hmap: "\<And>x. x \<in> S \<Longrightarrow> f x \<in> T"
  assumes hcont: "continuous_on UNIV f"
  shows "top1_continuous_map_on S (subspace_topology UNIV top1_open_sets S)
                                T (subspace_topology UNIV top1_open_sets T) f"
  unfolding top1_continuous_map_on_def
proof (intro conjI)
  show "\<forall>x\<in>S. f x \<in> T" using hmap by blast
  show "\<forall>V \<in> subspace_topology UNIV top1_open_sets T.
          {x \<in> S. f x \<in> V} \<in> subspace_topology UNIV top1_open_sets S"
  proof (intro ballI)
    fix V assume hV: "V \<in> subspace_topology UNIV top1_open_sets T"
    obtain U where hU: "U \<in> top1_open_sets" and hVeq: "V = T \<inter> U"
      using hV unfolding subspace_topology_def by blast
    have hopenU: "open U" using hU unfolding top1_open_sets_def by simp
    have hopen_pre: "open (f -` U)" by (rule open_vimage[OF hopenU hcont])
    have hpre_mem: "f -` U \<in> top1_open_sets"
      unfolding top1_open_sets_def using hopen_pre by simp
    have hEq: "{x \<in> S. f x \<in> V} = S \<inter> (f -` U)"
      unfolding hVeq using hmap by blast
    show "{x \<in> S. f x \<in> V} \<in> subspace_topology UNIV top1_open_sets S"
      unfolding subspace_topology_def
      apply (rule CollectI)
      apply (rule exI[where x="f -` U"])
      apply (intro conjI)
       apply (simp add: hEq Int_commute Int_left_commute Int_assoc)
      apply (rule hpre_mem)
      done
  qed
qed

(** The straight-line path t \<mapsto> (1-t)P + tQ is continuous into the subspace
    topology induced by geotop_euclidean_topology, for any convex target. **)
lemma geotop_straight_line_path_continuous:
  fixes P Q :: "'a::real_normed_vector" and S :: "'a set"
  assumes hconv: "convex S" and hP: "P \<in> S" and hQ: "Q \<in> S"
  shows "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
           S (subspace_topology UNIV geotop_euclidean_topology S)
           (\<lambda>t. (1-t) *\<^sub>R P + t *\<^sub>R Q)"
proof -
  let ?f = "\<lambda>t::real. (1-t) *\<^sub>R P + t *\<^sub>R Q"
  have hmap: "\<And>t. t \<in> top1_unit_interval \<Longrightarrow> ?f t \<in> S"
    by (metis atLeastAtMost_iff convex_alt hP hQ hconv top1_unit_interval_def)
  have hcont_HOL: "continuous_on UNIV ?f"
    by (intro continuous_intros)
  have hcont_op: "top1_continuous_map_on top1_unit_interval
                    (subspace_topology UNIV top1_open_sets top1_unit_interval)
                    S (subspace_topology UNIV top1_open_sets S) ?f"
    by (rule top1_continuous_map_on_real_to_normed_subspace_open_sets[OF hmap hcont_HOL])
  have hbridge: "(geotop_euclidean_topology :: 'a set set) = top1_open_sets"
    by (rule geotop_euclidean_topology_eq_open_sets)
  show ?thesis
    unfolding top1_unit_interval_topology_def hbridge
    using hcont_op by simp
qed

(** Bridge: top1_connected_on w.r.t. geotop_euclidean_topology is equivalent
    to HOL-Analysis connectedness. **)
lemma top1_connected_on_geotop_iff_connected:
  fixes S :: "'a::real_normed_vector set"
  shows "top1_connected_on S (subspace_topology UNIV geotop_euclidean_topology S)
         \<longleftrightarrow> connected S"
  by (simp add: geotop_euclidean_topology_eq_open_sets
                top1_connected_on_subspace_open_iff_connected)

(** Every convex nonempty set in a real_normed_vector is path-connected in
    Top0's sense (via geotop_euclidean_topology). **)
lemma top1_path_connected_on_HOL_convex:
  fixes S :: "'a::real_normed_vector set"
  assumes hconv: "convex S" and hne: "S \<noteq> {}"
  shows "top1_path_connected_on S (subspace_topology UNIV geotop_euclidean_topology S)"
  unfolding top1_path_connected_on_def
proof (intro conjI ballI)
  have hTeucl: "is_topology_on (UNIV::'a set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have hSUNIV: "S \<subseteq> UNIV" by simp
  show "is_topology_on S (subspace_topology UNIV geotop_euclidean_topology S)"
    by (rule subspace_topology_is_topology_on[OF hTeucl hSUNIV])
next
  fix P Q assume hP: "P \<in> S" and hQ: "Q \<in> S"
  let ?f = "\<lambda>t::real. (1-t) *\<^sub>R P + t *\<^sub>R Q"
  have hcont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                 S (subspace_topology UNIV geotop_euclidean_topology S) ?f"
    by (rule geotop_straight_line_path_continuous[OF hconv hP hQ])
  have hf0: "?f 0 = P" by simp
  have hf1: "?f 1 = Q" by simp
  have "top1_is_path_on S (subspace_topology UNIV geotop_euclidean_topology S) P Q ?f"
    unfolding top1_is_path_on_def using hcont hf0 hf1 by simp
  thus "\<exists>f. top1_is_path_on S (subspace_topology UNIV geotop_euclidean_topology S) P Q f"
    by blast
qed

(** Bridge: top1_continuous_map_on (w.r.t. geotop_euclidean subspaces) implies
    HOL-Analysis continuous_on. **)
lemma top1_continuous_map_on_geotop_imp_continuous_on:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes hcont: "top1_continuous_map_on S
                    (subspace_topology UNIV geotop_euclidean_topology S)
                    T (subspace_topology UNIV geotop_euclidean_topology T) f"
  shows "continuous_on S f"
  unfolding continuous_on_open_invariant
proof (intro allI impI)
  fix B :: "'b set" assume hBopen: "open B"
  have hBopen_T1: "B \<in> (top1_open_sets :: 'b set set)"
    unfolding top1_open_sets_def using hBopen by simp
  have hGeoEq_b: "(geotop_euclidean_topology :: 'b set set) = top1_open_sets"
    by (rule geotop_euclidean_topology_eq_open_sets)
  have hBopen_geotop: "B \<in> (geotop_euclidean_topology :: 'b set set)"
    using hBopen_T1 hGeoEq_b by simp
  have hfT: "\<forall>x\<in>S. f x \<in> T"
    using hcont unfolding top1_continuous_map_on_def by blast
  (** T \<inter> B is in the subspace topology of T. **)
  have hTB_in_subspace: "T \<inter> B \<in> subspace_topology UNIV geotop_euclidean_topology T"
    unfolding subspace_topology_def using hBopen_geotop by blast
  (** By continuity, preimage is in subspace topology of S. **)
  have hpre_in: "{x \<in> S. f x \<in> T \<inter> B} \<in> subspace_topology UNIV geotop_euclidean_topology S"
    using hcont hTB_in_subspace unfolding top1_continuous_map_on_def by blast
  (** Extract the underlying open set. **)
  obtain A where hA_geotop: "A \<in> geotop_euclidean_topology"
             and hpre_eq: "{x \<in> S. f x \<in> T \<inter> B} = S \<inter> A"
    using hpre_in unfolding subspace_topology_def by blast
  have hGeoEq_a: "(geotop_euclidean_topology :: 'a set set) = top1_open_sets"
    by (rule geotop_euclidean_topology_eq_open_sets)
  have hA_top1: "A \<in> top1_open_sets"
    using hA_geotop hGeoEq_a by simp
  have hA_open: "open A"
    using hA_top1 unfolding top1_open_sets_def by simp
  (** Since f x \<in> T for x \<in> S, T \<inter> B ∩ image = B ∩ image. **)
  have hpre_eq2: "{x \<in> S. f x \<in> T \<inter> B} = {x \<in> S. f x \<in> B}"
    using hfT by blast
  have hfinal: "A \<inter> S = f -` B \<inter> S"
    using hpre_eq hpre_eq2 by fastforce
  show "\<exists>A. open A \<and> A \<inter> S = f -` B \<inter> S"
    using hA_open hfinal by blast
qed

(** Bridge: top1_path_connected_on w.r.t. geotop_euclidean_topology implies
    HOL-Analysis path-connectedness. **)
lemma top1_path_connected_on_geotop_imp_path_connected:
  fixes S :: "'a::real_normed_vector set"
  assumes hpc: "top1_path_connected_on S (subspace_topology UNIV geotop_euclidean_topology S)"
  shows "path_connected S"
  unfolding path_connected_def
proof (intro ballI)
  fix x y assume hx: "x \<in> S" and hy: "y \<in> S"
  from hpc have "\<exists>f. top1_is_path_on S (subspace_topology UNIV geotop_euclidean_topology S) x y f"
    using hx hy unfolding top1_path_connected_on_def by (by100 blast)
  then obtain f :: "real \<Rightarrow> 'a"
    where hf: "top1_is_path_on S (subspace_topology UNIV geotop_euclidean_topology S) x y f"
    by (by100 blast)
  have hfcont_top1: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                       S (subspace_topology UNIV geotop_euclidean_topology S) f"
    using hf unfolding top1_is_path_on_def by (by100 blast)
  have hf0: "f 0 = x" and hf1: "f 1 = y"
    using hf unfolding top1_is_path_on_def by (by100 simp)+
  have hfS: "\<forall>t\<in>top1_unit_interval. f t \<in> S"
    using hfcont_top1 unfolding top1_continuous_map_on_def by (by100 blast)
  have heq: "top1_unit_interval_topology
              = subspace_topology UNIV geotop_euclidean_topology top1_unit_interval"
    unfolding top1_unit_interval_topology_def geotop_euclidean_topology_eq_open_sets
    by (by100 simp)
  have hfcont_geo: "top1_continuous_map_on top1_unit_interval
                      (subspace_topology UNIV geotop_euclidean_topology top1_unit_interval)
                      S (subspace_topology UNIV geotop_euclidean_topology S) f"
    using hfcont_top1 heq by (by100 simp)
  have hfcont_HOL: "continuous_on top1_unit_interval f"
    by (rule top1_continuous_map_on_geotop_imp_continuous_on[OF hfcont_geo])
  have hpath: "path f"
    using hfcont_HOL unfolding path_def top1_unit_interval_def by (by100 simp)
  have hpim: "path_image f \<subseteq> S"
    using hfS unfolding path_image_def top1_unit_interval_def by (by100 blast)
  have hstart: "pathstart f = x"
    unfolding pathstart_def using hf0 by (by100 simp)
  have hfinish: "pathfinish f = y"
    unfolding pathfinish_def using hf1 by (by100 simp)
  show "\<exists>g. path g \<and> path_image g \<subseteq> S \<and> pathstart g = x \<and> pathfinish g = y"
    using hpath hpim hstart hfinish by (by100 blast)
qed

(** Specialised form via \<open>top1_path_connected_on_HOL_convex\<close> and related:
    every path in a HOL-sense connected subset lifts to a top1-sense path. **)
lemma top1_is_path_on_of_HOL_path:
  fixes S :: "'a::real_normed_vector set" and g :: "real \<Rightarrow> 'a"
  assumes hg_path: "path g"
  assumes hg_im: "path_image g \<subseteq> S"
  assumes hg_start: "pathstart g = x" and hg_finish: "pathfinish g = y"
  shows "top1_is_path_on S (subspace_topology UNIV geotop_euclidean_topology S) x y g"
proof -
  have hg_cont: "continuous_on {0..1} g" using hg_path unfolding path_def .
  have hg_maps: "\<forall>t\<in>top1_unit_interval. g t \<in> S"
    using hg_im unfolding path_image_def top1_unit_interval_def by (by100 blast)
  have hpre_open: "\<forall>V \<in> subspace_topology UNIV geotop_euclidean_topology S.
                     {t\<in>top1_unit_interval. g t \<in> V} \<in> top1_unit_interval_topology"
  proof
    fix V assume hV: "V \<in> subspace_topology UNIV geotop_euclidean_topology S"
    then obtain U where hU_eq: "V = S \<inter> U" and hU_top: "U \<in> geotop_euclidean_topology"
      unfolding subspace_topology_def by (by100 blast)
    have hU_open: "open U"
      using hU_top unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    (** continuous_on + HOL gives open preimage relative to [0,1]: there's W open with
        \<open>{0..1} \<inter> g -` U = {0..1} \<inter> W\<close>. **)
    have hpre_HOL: "openin (top_of_set {0..1}) ({0..1} \<inter> g -` U)"
      by (rule continuous_openin_preimage_gen[OF hg_cont hU_open])
    then obtain W where hW_open: "open W"
                    and hWeq: "{0..1} \<inter> g -` U = {0..1} \<inter> W"
      unfolding openin_open by (by100 blast)
    (** The preimage \<open>{t\<in>[0,1]. g t \<in> V}\<close> equals \<open>{t\<in>[0,1]. g t \<in> U}\<close> since \<open>g\<close>
        maps into \<open>S\<close>. **)
    have hpre_eq: "{t\<in>top1_unit_interval. g t \<in> V} = {t\<in>top1_unit_interval. g t \<in> U}"
      using hU_eq hg_maps unfolding top1_unit_interval_def by (by100 blast)
    also have "\<dots> = {0..1} \<inter> g -` U"
      unfolding top1_unit_interval_def by (by100 blast)
    also have "\<dots> = {0..1} \<inter> W" using hWeq .
    also have "\<dots> = top1_unit_interval \<inter> W"
      unfolding top1_unit_interval_def by (by100 simp)
    finally have hpre_final:
      "{t\<in>top1_unit_interval. g t \<in> V} = top1_unit_interval \<inter> W" .
    have hW_top: "W \<in> geotop_euclidean_topology"
      using hW_open unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    have hW_opensets: "W \<in> top1_open_sets"
      using hW_open unfolding top1_open_sets_def by (by100 simp)
    have hinter_in: "top1_unit_interval \<inter> W \<in> top1_unit_interval_topology"
      unfolding top1_unit_interval_topology_def subspace_topology_def
      using hW_opensets by (by100 blast)
    show "{t\<in>top1_unit_interval. g t \<in> V} \<in> top1_unit_interval_topology"
      using hpre_final hinter_in by (by100 simp)
  qed
  have hcont_top1: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                       S (subspace_topology UNIV geotop_euclidean_topology S) g"
    unfolding top1_continuous_map_on_def using hg_maps hpre_open by (by100 blast)
  have hg0: "g 0 = x" using hg_start unfolding pathstart_def .
  have hg1: "g 1 = y" using hg_finish unfolding pathfinish_def .
  show ?thesis
    unfolding top1_is_path_on_def using hcont_top1 hg0 hg1 by (by100 simp)
qed

(** Reverse bridge: HOL \<open>path_connected S\<close> \<Longrightarrow> \<open>top1_path_connected_on S\<close>
    in the geotop-Euclidean subspace topology. **)
lemma path_connected_imp_top1_path_connected_on_geotop:
  fixes S :: "'a::real_normed_vector set"
  assumes hpc: "path_connected S"
  shows "top1_path_connected_on S (subspace_topology UNIV geotop_euclidean_topology S)"
  unfolding top1_path_connected_on_def
proof (intro conjI ballI)
  have hTeucl: "is_topology_on (UNIV::'a set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have hSUNIV: "S \<subseteq> UNIV" by (by100 simp)
  show "is_topology_on S (subspace_topology UNIV geotop_euclidean_topology S)"
    by (rule subspace_topology_is_topology_on[OF hTeucl hSUNIV])
next
  fix x y assume hx: "x \<in> S" and hy: "y \<in> S"
  from hpc obtain g where hg_path: "path g"
                      and hg_im: "path_image g \<subseteq> S"
                      and hg_start: "pathstart g = x"
                      and hg_finish: "pathfinish g = y"
    using hx hy unfolding path_connected_def by (by100 blast)
  have "top1_is_path_on S (subspace_topology UNIV geotop_euclidean_topology S) x y g"
    by (rule top1_is_path_on_of_HOL_path[OF hg_path hg_im hg_start hg_finish])
  then show "\<exists>f. top1_is_path_on S (subspace_topology UNIV geotop_euclidean_topology S) x y f"
    by (by100 blast)
qed

(** Corollary: path-connected (geotop-sense) \<Longrightarrow> connected (geotop-sense). **)
lemma top1_path_connected_on_geotop_imp_connected:
  fixes S :: "'a::real_normed_vector set"
  assumes "top1_path_connected_on S (subspace_topology UNIV geotop_euclidean_topology S)"
  shows "top1_connected_on S (subspace_topology UNIV geotop_euclidean_topology S)"
  by (rule iffD2[OF top1_connected_on_geotop_iff_connected
                    path_connected_imp_connected[OF
                      top1_path_connected_on_geotop_imp_path_connected[OF assms]]])

(** Bridge: every geotop-arc B in a real_normed_vector space gives rise to an
    HOL-Analysis arc \<gamma> with path_image \<gamma> = B. The simplex witness for the arc
    is a segment (1-simplex = convex hull of two points), so we can parametrize
    by t \<mapsto> f((1-t) v\<^sub>0 + t v\<^sub>1) composed with the inverse of the geotop homeomorphism. **)
lemma geotop_is_arc_imp_HOL_arc:
  fixes B :: "'a::real_normed_vector set"
  assumes hB: "geotop_is_arc B (subspace_topology UNIV geotop_euclidean_topology B)"
  shows "\<exists>\<gamma>::real \<Rightarrow> 'a. arc \<gamma> \<and> path_image \<gamma> = B"
proof -
  have hB_ncell: "geotop_is_n_cell B (subspace_topology UNIV geotop_euclidean_topology B) 1"
    using hB unfolding geotop_is_arc_def by blast
  obtain \<sigma> f where hdim: "geotop_simplex_dim (\<sigma>::'a set) 1"
               and hhomeo: "top1_homeomorphism_on B
                             (subspace_topology UNIV geotop_euclidean_topology B)
                             \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) f"
    using hB_ncell unfolding geotop_is_n_cell_def by blast
  obtain V m where hV_fin: "finite V" and hV_card: "card V = 2"
               and hV_gp: "geotop_general_position V m"
               and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using hdim unfolding geotop_simplex_dim_def by auto
  obtain v0 v1 where hV_eq: "V = {v0, v1}" and hv_ne: "v0 \<noteq> v1"
    using hV_card by (metis card_2_iff)
  have h\<sigma>_segment: "\<sigma> = closed_segment v0 v1"
    by (simp add: geotop_convex_hull_eq_HOL hV_eq h\<sigma>_eq segment_convex_hull)
  have hf_bij: "bij_betw f B \<sigma>"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  let ?finv = "inv_into B f"
  have hfinv_cont_top1: "top1_continuous_map_on \<sigma>
                          (subspace_topology UNIV geotop_euclidean_topology \<sigma>)
                          B (subspace_topology UNIV geotop_euclidean_topology B) ?finv"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hfinv_cont: "continuous_on \<sigma> ?finv"
    using hfinv_cont_top1 top1_continuous_map_on_geotop_imp_continuous_on by blast
  let ?g = "\<lambda>t::real. (1-t) *\<^sub>R v0 + t *\<^sub>R v1"
  let ?\<gamma> = "?finv \<circ> ?g"
  have hg_cont: "continuous_on {0..1} ?g"
    by (intro continuous_intros)
  have hg_image: "?g ` {0..1} = \<sigma>"
    using closed_segment_image_interval h\<sigma>_segment by blast
  have hg_inj: "inj_on ?g {0..1}"
    by (metis hv_ne inj_segment)
  have h\<gamma>_cont: "continuous_on {0..1} ?\<gamma>"
    using continuous_on_compose hfinv_cont hg_cont hg_image by blast
  have hfinv_inj: "inj_on ?finv \<sigma>"
    by (metis bij_betw_def bij_betw_inv_into hf_bij)
  have h\<gamma>_inj: "inj_on ?\<gamma> {0..1}"
    using comp_inj_on hfinv_inj hg_image hg_inj by blast
  have h\<gamma>_arc: "arc ?\<gamma>"
    using h\<gamma>_cont h\<gamma>_inj unfolding arc_def path_def by blast
  have h\<gamma>_pim: "path_image ?\<gamma> = B"
    by (metis (lifting) bij_betw_def bij_betw_inv_into hf_bij hg_image
              path_image_compose path_image_def)
  show ?thesis using h\<gamma>_arc h\<gamma>_pim by blast
qed

(** Bridge: HOL continuous_on → top1_continuous_map_on. General reverse
    direction of \<open>top1_continuous_map_on_geotop_imp_continuous_on\<close>.
    For a function \<open>f : S \<to> T\<close> continuous on \<open>S\<close> (HOL sense) that maps
    \<open>S\<close> into \<open>T\<close>, \<open>f\<close> is a top1 continuous map between the geotop
    subspace topologies. **)
lemma geotop_continuous_on_imp_top1_continuous_map_on:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes hcont: "continuous_on S f" and himg: "f ` S \<subseteq> T"
  shows "top1_continuous_map_on S
                 (subspace_topology UNIV geotop_euclidean_topology S)
                 T (subspace_topology UNIV geotop_euclidean_topology T) f"
proof -
  have h_Teucl_a: "is_topology_on (UNIV::'a set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have h_Teucl_b: "is_topology_on (UNIV::'b set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have hTS: "is_topology_on S (subspace_topology UNIV geotop_euclidean_topology S)"
    by (rule subspace_topology_is_topology_on[OF h_Teucl_a subset_UNIV])
  have hTT: "is_topology_on T (subspace_topology UNIV geotop_euclidean_topology T)"
    by (rule subspace_topology_is_topology_on[OF h_Teucl_b subset_UNIV])
  have h_maps: "\<forall>x\<in>S. f x \<in> T"
    using himg by (by100 blast)
  have h_pre: "\<forall>V \<in> subspace_topology UNIV geotop_euclidean_topology T.
                   {x\<in>S. f x \<in> V} \<in> subspace_topology UNIV geotop_euclidean_topology S"
  proof
    fix V assume hV: "V \<in> subspace_topology UNIV geotop_euclidean_topology T"
    then obtain U where hU_eq: "V = T \<inter> U" and hU_top: "U \<in> geotop_euclidean_topology"
      unfolding subspace_topology_def by (by100 blast)
    have hU_open: "open U"
      using hU_top unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    (** continuous_on + HOL gives open preimage relative to S. **)
    have hpre_HOL: "openin (top_of_set S) (S \<inter> f -` U)"
      by (rule continuous_openin_preimage_gen[OF hcont hU_open])
    then obtain W where hW_open: "open W"
                    and hWeq: "S \<inter> f -` U = S \<inter> W"
      unfolding openin_open by (by100 blast)
    have hpre_eq: "{x\<in>S. f x \<in> V} = {x\<in>S. f x \<in> U}"
      using hU_eq h_maps by (by100 blast)
    also have "\<dots> = S \<inter> f -` U" by (by100 blast)
    also have "\<dots> = S \<inter> W" using hWeq .
    finally have hpre_final: "{x\<in>S. f x \<in> V} = S \<inter> W" .
    have hW_top: "W \<in> geotop_euclidean_topology"
      using hW_open unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    have hinter_in: "S \<inter> W \<in> subspace_topology UNIV geotop_euclidean_topology S"
      unfolding subspace_topology_def using hW_top by (by100 blast)
    show "{x\<in>S. f x \<in> V} \<in> subspace_topology UNIV geotop_euclidean_topology S"
      using hpre_final hinter_in by (by100 simp)
  qed
  show ?thesis
    unfolding top1_continuous_map_on_def
    using hTS hTT h_maps h_pre by (by100 blast)
qed

(** Bridge: HOL homeomorphic \<rightarrow> top1_homeomorphism_on with geotop subspace
    topologies. Reverse direction of \<open>top1_homeomorphism_on_geotop_imp_HOL_homeomorphic\<close>. **)
lemma geotop_HOL_homeomorphic_imp_top1_homeomorphism_on:
  fixes X Y :: "'a::real_normed_vector set"
  assumes hHomeo: "X homeomorphic Y"
  shows "\<exists>f. top1_homeomorphism_on X
              (subspace_topology UNIV geotop_euclidean_topology X)
              Y (subspace_topology UNIV geotop_euclidean_topology Y) f"
proof -
  obtain f g where hfg_homeo: "homeomorphism X Y f g"
    using hHomeo unfolding homeomorphic_def by (by100 blast)
  have hf_cont_HOL: "continuous_on X f"
    using hfg_homeo unfolding homeomorphism_def by (by100 blast)
  have hg_cont_HOL: "continuous_on Y g"
    using hfg_homeo unfolding homeomorphism_def by (by100 blast)
  have hf_img_eq: "f ` X = Y"
    using hfg_homeo unfolding homeomorphism_def by (by100 blast)
  have hg_img_eq: "g ` Y = X"
    using hfg_homeo unfolding homeomorphism_def by (by100 blast)
  have hfg_id: "\<forall>x\<in>X. g (f x) = x"
    using hfg_homeo unfolding homeomorphism_def by (by100 blast)
  have hgf_id: "\<forall>y\<in>Y. f (g y) = y"
    using hfg_homeo unfolding homeomorphism_def by (by100 blast)
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
  have hf_homeo: "top1_homeomorphism_on X
                    (subspace_topology UNIV geotop_euclidean_topology X)
                    Y (subspace_topology UNIV geotop_euclidean_topology Y) f"
    unfolding top1_homeomorphism_on_def
    using hTX hTY hf_bij hf_top1 h_invf_top1 by (by100 blast)
  show ?thesis using hf_homeo by (by100 blast)
qed

(** Reverse bridge: a HOL arc's image is a geotop \<open>is_arc\<close> set.
    Proof: path_image \<gamma> is homeomorphic to [0,1] (compact-Hausdorff injection),
    and [0,1] is in turn homeomorphic to any 1-simplex (closed_segment 0 b for
    b in Basis). Hence path_image \<gamma> is an n-cell with n=1. **)
lemma geotop_HOL_arc_imp_geotop_is_arc:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  assumes harc: "arc \<gamma>"
  shows "geotop_is_arc (path_image \<gamma>)
          (subspace_topology UNIV geotop_euclidean_topology (path_image \<gamma>))"
proof -
  (** (1) Pick 1-simplex \<sigma> = closed_segment 0 b for b \<in> Basis. **)
  obtain b :: 'a where hb_basis: "b \<in> Basis" using nonempty_Basis by (by100 blast)
  have hb_ne: "(0::'a) \<noteq> b" using hb_basis nonzero_Basis by (by100 blast)
  let ?\<sigma> = "closed_segment (0::'a) b"
  (** Inline proof of geotop_simplex_dim ?\<sigma> 1 to avoid forward reference. **)
  have h\<sigma>_dim: "geotop_simplex_dim ?\<sigma> 1"
    unfolding geotop_simplex_dim_def
  proof (intro exI[of _ "{0::'a, b}"] exI[of _ "1::nat"] conjI)
    show "finite {0::'a, b}" by (by100 simp)
    show "card {0::'a, b} = 1 + 1" using hb_ne by (by100 simp)
    show "(1::nat) \<le> 1" by (by100 simp)
    show "geotop_general_position {0::'a, b} 1"
      unfolding geotop_general_position_def
    proof (intro allI impI)
      fix H :: "'a set" and k :: nat
      assume hassm: "geotop_hyperplane_dim H k \<and> k < 1"
      have hk: "k = 0" using hassm by (by100 simp)
      have hhyp: "geotop_hyperplane_dim H 0" using hassm hk by (by100 simp)
      have hH_sing: "\<exists>v0. H = {v0}"
      proof -
        have hHk_raw:
          "\<exists>V v0. subspace V
                \<and> (\<exists>B. independent B \<and> finite B \<and> card B = 0 \<and> span B = V)
                \<and> H = (\<lambda>v. v + v0) ` V"
          using hhyp unfolding geotop_hyperplane_dim_def by (by100 simp)
        obtain V v0 where hV: "subspace V"
                      and hV_basis: "\<exists>B. independent B \<and> finite B \<and> card B = 0 \<and> span B = V"
                      and hH': "H = (\<lambda>v. v + v0) ` V"
          using hHk_raw by (by100 fast)
        obtain B where hB_fin: "finite B" and hB_card: "card B = 0"
                   and hB_span: "span B = V"
          using hV_basis by (by100 blast)
        have hBempty: "B = {}" using hB_fin hB_card by (by100 simp)
        have hVzero: "V = {0}" using hBempty hB_span by (by100 simp)
        have "H = {0 + v0}" using hH' hVzero by (by100 simp)
        thus ?thesis by (by100 blast)
      qed
      then obtain v0 where hH_eq: "H = {v0}" by (by100 blast)
      have hinter: "{0::'a, b} \<inter> H \<subseteq> {v0}" using hH_eq by (by100 blast)
      have h1: "finite ({0::'a, b} \<inter> H)" using hinter
        by (meson finite.emptyI finite.insertI finite_subset)
      have h2: "card ({0::'a, b} \<inter> H) \<le> 1"
        using hinter card_mono[of "{v0}"] by (by100 simp)
      show "finite ({0::'a, b} \<inter> H) \<and> card ({0::'a, b} \<inter> H) \<le> k + 1"
        using h1 h2 hk by (by100 simp)
    qed
    show "closed_segment (0::'a) b = geotop_convex_hull {0, b}"
    proof -
      have h_seg: "closed_segment (0::'a) b = convex hull {0, b}"
        by (rule segment_convex_hull)
      have h_hull: "geotop_convex_hull {0::'a, b} = convex hull {0, b}"
        by (rule geotop_convex_hull_eq_HOL)
      show ?thesis using h_seg h_hull by (by100 simp)
    qed
  qed
  (** (2) Via HOL: path_image \<gamma> is homeomorphic to [0,1]. **)
  have h_pim_homeo: "path_image \<gamma> homeomorphic {0::real..1}"
  proof -
    have "(0::real) < 1" by (by100 simp)
    thus ?thesis by (rule homeomorphic_arc_image_interval[OF harc])
  qed
  (** (3) [0,1] is homeomorphic to \<sigma> via t \<mapsto> t *\<^sub>R b. **)
  let ?h = "\<lambda>t::real. t *\<^sub>R b"
  have hh_cont: "continuous_on {0..1} ?h" by (intro continuous_intros)
  have hh_image: "?h ` {0..1} = ?\<sigma>"
  proof -
    have heq: "closed_segment (0::'a) b = (\<lambda>u. (1 - u) *\<^sub>R 0 + u *\<^sub>R b) ` {0..1}"
      by (rule closed_segment_image_interval)
    also have "(\<lambda>u::real. (1 - u) *\<^sub>R (0::'a) + u *\<^sub>R b) = (\<lambda>u. u *\<^sub>R b)"
      by (by100 simp)
    finally show ?thesis by (by100 simp)
  qed
  have hh_inj: "inj_on ?h {0..1}" using hb_ne by (simp add: inj_on_def)
  have h_01_homeo_\<sigma>: "{0::real..1} homeomorphic ?\<sigma>"
    by (rule homeomorphic_compact[OF _ hh_cont hh_image hh_inj]) simp
  (** (4) Combine: path_image \<gamma> homeomorphic \<sigma>. **)
  have h_pim_homeo_\<sigma>: "path_image \<gamma> homeomorphic ?\<sigma>"
    by (rule homeomorphic_trans[OF h_pim_homeo h_01_homeo_\<sigma>])
  (** (5) Lift HOL homeomorphism to top1_homeomorphism_on via the bridge. **)
  have h_top1_homeo: "\<exists>f. top1_homeomorphism_on (path_image \<gamma>)
                    (subspace_topology UNIV geotop_euclidean_topology (path_image \<gamma>))
                    ?\<sigma> (subspace_topology UNIV geotop_euclidean_topology ?\<sigma>) f"
    by (rule geotop_HOL_homeomorphic_imp_top1_homeomorphism_on[OF h_pim_homeo_\<sigma>])
  then obtain f where hf_homeo: "top1_homeomorphism_on (path_image \<gamma>)
                    (subspace_topology UNIV geotop_euclidean_topology (path_image \<gamma>))
                    ?\<sigma> (subspace_topology UNIV geotop_euclidean_topology ?\<sigma>) f"
    by (by100 blast)
  (** (6) Package as geotop_is_n_cell (n = 1 \<Rightarrow> is_arc). **)
  have h_Teucl: "is_topology_on (UNIV::'a set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have h_pim_top: "is_topology_on (path_image \<gamma>)
                    (subspace_topology UNIV geotop_euclidean_topology (path_image \<gamma>))"
    by (rule subspace_topology_is_topology_on[OF h_Teucl subset_UNIV])
  show ?thesis
    unfolding geotop_is_arc_def geotop_is_n_cell_def
    using h_pim_top h\<sigma>_dim hf_homeo by (by100 blast)
qed

(** Helper: complement of a geotop-arc in R^n (n \<ge> 2) is connected. **)
lemma top1_connected_complement_of_geotop_arc:
  fixes A :: "'a::euclidean_space set"
  assumes hA: "geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A)"
  assumes hdim: "2 \<le> DIM('a)"
  shows "top1_connected_on (UNIV - A)
           (subspace_topology UNIV geotop_euclidean_topology (UNIV - A))"
proof -
  obtain \<gamma> where harc: "arc \<gamma>" and hpim: "path_image \<gamma> = A"
    using hA geotop_is_arc_imp_HOL_arc by blast
  have hconnC: "connected (- A)"
    using harc hpim hdim connected_arc_complement[of \<gamma>] by simp
  have hconnD: "connected (UNIV - A)"
    by (metis Compl_eq_Diff_UNIV hconnC)
  show ?thesis
    by (simp add: hconnD top1_connected_on_geotop_iff_connected)
qed

(** Bridge: top1_homeomorphism_on (w.r.t. geotop_euclidean subspaces) implies
    HOL-Analysis `homeomorphic`. **)
lemma top1_homeomorphism_on_geotop_imp_HOL_homeomorphic:
  fixes S :: "'a::real_normed_vector set" and T :: "'b::real_normed_vector set"
  fixes f :: "'a \<Rightarrow> 'b"
  assumes hhomeo: "top1_homeomorphism_on S
                    (subspace_topology UNIV geotop_euclidean_topology S)
                    T (subspace_topology UNIV geotop_euclidean_topology T) f"
  shows "S homeomorphic T"
proof -
  have hcont_f: "top1_continuous_map_on S
                   (subspace_topology UNIV geotop_euclidean_topology S)
                   T (subspace_topology UNIV geotop_euclidean_topology T) f"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hf_HOL: "continuous_on S f"
    using hcont_f top1_continuous_map_on_geotop_imp_continuous_on by blast
  have hbij: "bij_betw f S T"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  let ?finv = "inv_into S f"
  have hcont_finv: "top1_continuous_map_on T
                     (subspace_topology UNIV geotop_euclidean_topology T)
                     S (subspace_topology UNIV geotop_euclidean_topology S) ?finv"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hfinv_HOL: "continuous_on T ?finv"
    using hcont_finv top1_continuous_map_on_geotop_imp_continuous_on by blast
  have hfS: "f ` S = T" using hbij unfolding bij_betw_def by blast
  have hfinvT: "?finv ` T = S"
    by (metis hbij bij_betw_inv_into bij_betw_def)
  have hfinvf: "\<forall>x\<in>S. ?finv (f x) = x"
    by (meson bij_betw_inv_into_left hbij)
  have hfinv_f: "\<forall>y\<in>T. f (?finv y) = y"
    by (metis hbij bij_betw_inv_into_right)
  show "S homeomorphic T"
    by (metis hfS hf_HOL hfinvT hfinv_HOL hfinv_f hfinvf homeomorphicI)
qed

(** from Introduction: Theorem 4 - Invariance of domain (geotop.tex:206)
    LATEX VERSION: Let U be a subset of R^n, such that U is homeomorphic to R^n. Then U is open.
    Positioned here (rather than in the Introduction) so that the HOL-Analysis bridge lemmas
    \<open>geotop_euclidean_topology_eq_open_sets\<close>,
    \<open>top1_continuous_map_on_geotop_imp_continuous_on\<close>, and
    \<open>subspace_topology_self_carrier\<close> are in scope. The proof uses HOL's
    \<open>invariance_of_domain_gen\<close> on the inverse g = f\<^sup>-\<^sup>1: \<bbbR>\<^sup>n \<rightarrow> U. **)
theorem Theorem_GT_4_invariance_of_domain:
  fixes U :: "'a::euclidean_space set"
  assumes hhomeo: "top1_homeomorphism_on U
             (subspace_topology (UNIV::'a set) geotop_euclidean_topology U)
             (UNIV::'a set) geotop_euclidean_topology f"
  shows "U \<in> geotop_euclidean_topology"
proof -
  have hbij: "bij_betw f U UNIV"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  define g where "g = inv_into U f"
  have hg_bij: "bij_betw g UNIV U"
    unfolding g_def using hbij by (rule bij_betw_inv_into)
  have hU_img: "g ` UNIV = U"
    using hg_bij unfolding bij_betw_def by blast
  have hg_inj: "inj_on g UNIV"
    using hg_bij unfolding bij_betw_def by blast
  have hg_cont_top1: "top1_continuous_map_on (UNIV::'a set) geotop_euclidean_topology
                         U (subspace_topology UNIV geotop_euclidean_topology U) g"
    using hhomeo unfolding top1_homeomorphism_on_def g_def by blast
  have hsubUNIV: "subspace_topology (UNIV::'a set) geotop_euclidean_topology UNIV
                   = geotop_euclidean_topology"
    by (rule subspace_topology_self_carrier) simp
  have hg_cont_sub: "top1_continuous_map_on (UNIV::'a set)
                       (subspace_topology UNIV geotop_euclidean_topology UNIV)
                       U (subspace_topology UNIV geotop_euclidean_topology U) g"
    using hg_cont_top1 hsubUNIV by simp
  have hg_cont_HOL: "continuous_on UNIV g"
    using hg_cont_sub top1_continuous_map_on_geotop_imp_continuous_on by blast
  have hopenUNIV: "open (UNIV :: 'a set)" by simp
  have hdim: "DIM('a) \<le> DIM('a)" by simp
  have hUopen_img: "open (g ` (UNIV::'a set))"
    using invariance_of_domain_gen[OF hopenUNIV hg_cont_HOL hg_inj hdim] .
  have hU_open: "open U" using hUopen_img hU_img by simp
  show "U \<in> geotop_euclidean_topology"
    by (metis hU_open geotop_euclidean_topology_eq_open_sets
              mem_Collect_eq top1_open_sets_def)
qed

(** Bridge: closed sets in our geotop_euclidean topology coincide with
    HOL-Analysis `closed` sets on real_normed_vector. **)
lemma closedin_on_geotop_UNIV_iff_closed:
  fixes C :: "'a::real_normed_vector set"
  shows "closedin_on UNIV geotop_euclidean_topology C \<longleftrightarrow> closed C"
  unfolding closedin_on_def
  using geotop_euclidean_topology_eq_open_sets
  unfolding top1_open_sets_def
  by (metis Compl_eq_Diff_UNIV closed_open mem_Collect_eq subset_UNIV)

(** Bridge: closure_on (w.r.t. geotop_euclidean_topology on UNIV) equals
    HOL-Analysis `closure`. **)
lemma closure_on_geotop_UNIV_eq_closure:
  fixes A :: "'a::real_normed_vector set"
  shows "closure_on UNIV geotop_euclidean_topology A = closure A"
  unfolding closure_on_def closure_hull hull_def
  using closedin_on_geotop_UNIV_iff_closed by blast

(** Bridge: geotop_frontier (w.r.t. geotop_euclidean_topology on UNIV) equals
    HOL-Analysis `frontier`. **)
lemma geotop_frontier_UNIV_eq_frontier:
  fixes U :: "'a::real_normed_vector set"
  shows "geotop_frontier UNIV geotop_euclidean_topology U = frontier U"
  by (simp add: Compl_eq_Diff_UNIV closure_on_geotop_UNIV_eq_closure
                frontier_closures geotop_frontier_def)

(** from \<S>1 Theorem 3 (geotop.tex:338)
    LATEX VERSION: Every simplex is pathwise connected. **)
theorem Theorem_GT_1_3:
  fixes \<sigma> :: "'a::real_normed_vector set"
  assumes "geotop_is_simplex \<sigma>"
  shows "top1_path_connected_on \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>)"
  (** Moise proof (geotop.tex:338): a simplex is convex (as a convex hull),
      and every convex set is path-connected via straight-line paths. **)
proof -
  have hconv: "convex \<sigma>"
    using geotop_simplex_is_convex[OF assms] geotop_convex_iff_HOL_convex by blast
  have hne: "\<sigma> \<noteq> {}" by (rule geotop_simplex_nonempty[OF assms])
  show ?thesis by (rule top1_path_connected_on_HOL_convex[OF hconv hne])
qed

(** from \<S>1 Theorem 4 (geotop.tex:341)
    LATEX VERSION: Let K be a complex. If K is connected, then |K| is pathwise connected. **)
(** Helper: complex-connected \<open>K\<close> implies HOL-path-connected \<open>|K|\<close>.
    Proof outline (Moise Thm 4 in HOL form):
      (1) Vertex-level reachability: for any two vertices \<open>v, w \<in> K^0\<close>, there is a
          HOL-path \<open>g: [0,1] \<to> |K|\<close> with start \<open>v\<close>, finish \<open>w\<close>. Proof follows Moise
          Steps 1-7: fix \<open>v_0\<close>; \<open>V = reachable vertices from v_0 via 1-skeleton\<close>;
          \<open>K_1 = subcomplex on V\<close>, \<open>K_2 = K \<setminus> K_1\<close>; \<open>K_1 \<inter> K_2 = {}\<close>, \<open>K = K_1 \<cup> K_2\<close>
          (Step 4: any edge between \<open>V\<close> and \<open>V\<^sup>c\<close> would propagate reachability);
          complex-connected K forces \<open>K_2 = \<emptyset>\<close>; hence \<open>V = K^0\<close>.
      (2) For any \<open>P \<in> |K|\<close>, pick \<open>\<sigma>_P \<in> K\<close> with \<open>P \<in> \<sigma>_P\<close> and a vertex \<open>v_P \<in> \<sigma>_P\<close>;
          the straight-line segment in \<open>\<sigma>_P\<close> (convex, hence HOL-path-connected) gives
          a HOL-path \<open>P \<to> v_P\<close>.
      (3) Concatenate \<open>P \<to> v_P \<to> v_Q \<to> Q\<close> via HOL's \<open>+++\<close>. **)
lemma geotop_complex_connected_imp_HOL_vertex_reachable:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_complex_connected K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hw: "w \<in> geotop_complex_vertices K"
  shows "\<exists>g. path g \<and> path_image g \<subseteq> geotop_polyhedron K \<and>
               pathstart g = v \<and> pathfinish g = w"
proof -
  have hKcomp: "geotop_is_complex K"
    using hK unfolding geotop_complex_connected_def by (by100 blast)
  (** Define \<open>V\<close> = vertices HOL-path-reachable from \<open>v\<close> through \<open>|K|\<close>. **)
  define V where
    "V = {u \<in> geotop_complex_vertices K. \<exists>g. path g \<and> path_image g \<subseteq> geotop_polyhedron K
                                               \<and> pathstart g = v \<and> pathfinish g = u}"
  (** Step 1: \<open>v \<in> V\<close> via the constant path. **)
  have hv_V: "v \<in> V"
  proof -
    let ?g = "\<lambda>t::real. v"
    have h_path: "path ?g" unfolding path_def by (by100 simp)
    have h_im_sub: "path_image ?g \<subseteq> {v}"
      unfolding path_image_def by (by100 blast)
    (** \<open>v \<in> |K|\<close>: any vertex of \<open>K\<close> lies in some simplex of \<open>K\<close>. **)
    obtain \<sigma>\<^sub>v V\<^sub>v where h\<sigma>\<^sub>v: "\<sigma>\<^sub>v \<in> K" and hV\<^sub>v: "geotop_simplex_vertices \<sigma>\<^sub>v V\<^sub>v"
                     and hv_in_V\<^sub>v: "v \<in> V\<^sub>v"
      using hv unfolding geotop_complex_vertices_def by (by100 blast)
    have h\<sigma>\<^sub>v_eq: "\<sigma>\<^sub>v = convex hull V\<^sub>v"
      using hV\<^sub>v geotop_convex_hull_eq_HOL
      unfolding geotop_simplex_vertices_def by (by100 blast)
    have hv_hull: "v \<in> convex hull V\<^sub>v"
      using hv_in_V\<^sub>v hull_inc[of v V\<^sub>v] by (by100 simp)
    have hv_\<sigma>\<^sub>v: "v \<in> \<sigma>\<^sub>v" using hv_hull h\<sigma>\<^sub>v_eq by (by100 simp)
    have hv_K: "v \<in> geotop_polyhedron K"
      using hv_\<sigma>\<^sub>v h\<sigma>\<^sub>v unfolding geotop_polyhedron_def by (by100 blast)
    have h_im_K: "path_image ?g \<subseteq> geotop_polyhedron K"
      using h_im_sub hv_K by (by100 blast)
    have h_s: "pathstart ?g = v" unfolding pathstart_def by (by100 simp)
    have h_f: "pathfinish ?g = v" unfolding pathfinish_def by (by100 simp)
    show ?thesis
      unfolding V_def using hv h_path h_im_K h_s h_f by (by100 blast)
  qed
  (** Step 2-6: define subcomplexes \<open>K_1\<close>, \<open>K_2\<close> and derive contradiction from
      \<open>complex_connected K\<close> if \<open>K_2 \<noteq> \<emptyset>\<close>. Steps 3-5 (K_1, K_2 are complexes) and
      Step 4 (vertex bipartition) require an edge-crossing lemma to propagate
      reachability across edges. **)
  define K\<^sub>1 where "K\<^sub>1 = {\<sigma>\<in>K. \<exists>V\<sigma>. geotop_simplex_vertices \<sigma> V\<sigma> \<and> V\<sigma> \<subseteq> V}"
  define K\<^sub>2 where "K\<^sub>2 = {\<sigma>\<in>K. \<exists>V\<sigma>. geotop_simplex_vertices \<sigma> V\<sigma>
                                     \<and> V\<sigma> \<inter> V = {}}"
  (** Step 3: \<open>K\<^sub>1\<close> is a subcomplex of \<open>K\<close>. Structure:
        (K.1) All simplexes: \<open>K\<^sub>1 \<subseteq> K\<close>, inherit from \<open>K\<close>.
        (K.2) Face-closed: face \<open>\<tau>\<close> of \<open>\<sigma> \<in> K\<^sub>1\<close> has vertices \<open>W \<subseteq> V\<^sub>\<sigma> \<subseteq> V\<close>;
              \<open>\<tau> \<in> K\<close> by \<open>K\<close>-face-closure; \<open>\<tau>\<close> has simplex-vertices \<open>W\<close>
              (general-position descends to subsets). So \<open>\<tau> \<in> K\<^sub>1\<close>.
        (K.3) Intersection: \<open>\<sigma>, \<sigma>'\<in> K\<^sub>1\<close> have \<open>\<sigma> \<inter> \<sigma>'\<close> a face of both (in K), and
              its vertices \<open>\<subseteq> V\<close> (again via descent).
        (K.4) Local finiteness: \<open>K\<^sub>1 \<subseteq> K\<close>, so the finite nbhd works. **)
  have hK\<^sub>1_subK: "K\<^sub>1 \<subseteq> K" unfolding K\<^sub>1_def by (by100 blast)
  have hK\<^sub>2_subK: "K\<^sub>2 \<subseteq> K" unfolding K\<^sub>2_def by (by100 blast)
  (** Helpers: \<open>K\<^sub>1\<close>'s four complex axioms. **)
  have hK_simp: "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
    using hKcomp by (rule geotop_is_complex_simplex)
  have hK_fc: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    using hKcomp by (rule geotop_is_complex_face_closed)
  have hK_inter: "\<forall>\<sigma>\<in>K. \<forall>\<tau>\<in>K. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                    geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    using hKcomp unfolding geotop_is_complex_def by (by100 blast)
  have hK_locfin: "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    using hKcomp unfolding geotop_is_complex_def by (by100 blast)
  have hK\<^sub>1_K1: "\<forall>\<sigma>\<in>K\<^sub>1. geotop_is_simplex \<sigma>"
    using hK\<^sub>1_subK hK_simp by (by100 blast)
  have hK\<^sub>1_K4: "\<forall>\<sigma>\<in>K\<^sub>1. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K\<^sub>1. \<tau> \<inter> U \<noteq> {}}"
  proof
    fix \<sigma> assume h\<sigma>: "\<sigma> \<in> K\<^sub>1"
    have h\<sigma>K: "\<sigma> \<in> K" using h\<sigma> hK\<^sub>1_subK by (by100 blast)
    have h_ex_U: "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using hK_locfin h\<sigma>K by (by100 blast)
    obtain U where hU_open: "open U" and h\<sigma>U: "\<sigma> \<subseteq> U"
                  and hUfin: "finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using h_ex_U by (by100 blast)
    have h_sub: "{\<tau>\<in>K\<^sub>1. \<tau> \<inter> U \<noteq> {}} \<subseteq> {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using hK\<^sub>1_subK by (by100 blast)
    have hfin: "finite {\<tau>\<in>K\<^sub>1. \<tau> \<inter> U \<noteq> {}}"
      using finite_subset[OF h_sub hUfin] by (by100 blast)
    show "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K\<^sub>1. \<tau> \<inter> U \<noteq> {}}"
      using hU_open h\<sigma>U hfin by (by100 blast)
  qed
  have hK\<^sub>1_K3: "\<forall>\<sigma>\<in>K\<^sub>1. \<forall>\<tau>\<in>K\<^sub>1. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                  geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    using hK\<^sub>1_subK hK_inter by (by100 blast)
  (** K_1's face-closure: use vertex-uniqueness + general-position descent. **)
  have hK\<^sub>1_K2: "\<forall>\<sigma>\<in>K\<^sub>1. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K\<^sub>1"
  proof (intro ballI allI impI)
    fix \<sigma> \<tau> assume h\<sigma>: "\<sigma> \<in> K\<^sub>1" and hface: "geotop_is_face \<tau> \<sigma>"
    have h\<sigma>K: "\<sigma> \<in> K" using h\<sigma> hK\<^sub>1_subK by (by100 blast)
    (** Extract \<sigma>'s vertex set and \<open>V\<^sub>\<sigma> \<subseteq> V\<close>. **)
    obtain V\<^sub>\<sigma> where hV\<^sub>\<sigma>sv: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>" and hV\<^sub>\<sigma>V: "V\<^sub>\<sigma> \<subseteq> V"
      using h\<sigma> unfolding K\<^sub>1_def by (by100 blast)
    (** Extract \<tau>'s vertex set \<open>W\<close> from the face definition. **)
    obtain V' W where hV'sv: "geotop_simplex_vertices \<sigma> V'" and hWne: "W \<noteq> {}"
                  and hWV': "W \<subseteq> V'" and h\<tau>eq: "\<tau> = geotop_convex_hull W"
      using hface unfolding geotop_is_face_def by (by100 blast)
    (** Vertex-uniqueness: \<open>V' = V\<^sub>\<sigma>\<close>. **)
    have hV'eq: "V' = V\<^sub>\<sigma>"
      by (rule geotop_simplex_vertices_unique[OF hV'sv hV\<^sub>\<sigma>sv])
    have hWV\<^sub>\<sigma>: "W \<subseteq> V\<^sub>\<sigma>" using hWV' hV'eq by (by100 simp)
    have hWV: "W \<subseteq> V" using hWV\<^sub>\<sigma> hV\<^sub>\<sigma>V by (by100 blast)
    (** \<open>\<tau> \<in> K\<close> by K's face-closure. **)
    have h\<tau>K: "\<tau> \<in> K" using hK_fc h\<sigma>K hface by (by100 blast)
    (** Build \<open>simplex_vertices \<tau> W\<close>. **)
    obtain m n where hV\<^sub>\<sigma>_unp: "finite V\<^sub>\<sigma>" and hV\<^sub>\<sigma>card: "card V\<^sub>\<sigma> = n+1"
                   and hnm: "n \<le> m" and hV\<^sub>\<sigma>gp: "geotop_general_position V\<^sub>\<sigma> m"
      using hV\<^sub>\<sigma>sv unfolding geotop_simplex_vertices_def by (by100 blast)
    have hWfin: "finite W" using hWV\<^sub>\<sigma> hV\<^sub>\<sigma>_unp finite_subset by (by100 blast)
    have hWgp: "geotop_general_position W m"
      by (rule geotop_general_position_mono[OF hV\<^sub>\<sigma>gp hWV\<^sub>\<sigma> hWfin])
    have hWcard_pos: "card W > 0"
      using hWne hWfin card_gt_0_iff by (by100 blast)
    have hWcard_ex: "\<exists>n'. card W = n' + 1" using hWcard_pos by (by100 presburger)
    obtain n' where hWcard: "card W = n' + 1" using hWcard_ex by (by100 blast)
    have hcard_leq: "card W \<le> card V\<^sub>\<sigma>"
      using hWV\<^sub>\<sigma> hV\<^sub>\<sigma>_unp card_mono by (by100 blast)
    have hn'_bound: "n' \<le> m"
      using hcard_leq hWcard hV\<^sub>\<sigma>card hnm by (by100 linarith)
    have h\<tau>_hull_W: "\<tau> = geotop_convex_hull W" using h\<tau>eq .
    have h\<tau>sv: "geotop_simplex_vertices \<tau> W"
      unfolding geotop_simplex_vertices_def
      apply (rule exI[of _ m])
      apply (rule exI[of _ n'])
      using hWfin hWcard hn'_bound hWgp h\<tau>_hull_W by (by100 blast)
    show "\<tau> \<in> K\<^sub>1"
      unfolding K\<^sub>1_def using h\<tau>K h\<tau>sv hWV by (by100 blast)
  qed
  have hK\<^sub>1_complex: "geotop_is_complex K\<^sub>1"
    unfolding geotop_is_complex_def
    using hK\<^sub>1_K1 hK\<^sub>1_K2 hK\<^sub>1_K3 hK\<^sub>1_K4 by (by100 blast)
  (** Step 5: \<open>K\<^sub>2\<close> is a subcomplex of \<open>K\<close> (analogous to Step 3). **)
  have hK\<^sub>2_K1: "\<forall>\<sigma>\<in>K\<^sub>2. geotop_is_simplex \<sigma>"
    using hK\<^sub>2_subK hK_simp by (by100 blast)
  have hK\<^sub>2_K4: "\<forall>\<sigma>\<in>K\<^sub>2. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K\<^sub>2. \<tau> \<inter> U \<noteq> {}}"
  proof
    fix \<sigma> assume h\<sigma>: "\<sigma> \<in> K\<^sub>2"
    have h\<sigma>K: "\<sigma> \<in> K" using h\<sigma> hK\<^sub>2_subK by (by100 blast)
    have h_ex_U: "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using hK_locfin h\<sigma>K by (by100 blast)
    obtain U where hU_open: "open U" and h\<sigma>U: "\<sigma> \<subseteq> U"
                  and hUfin: "finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using h_ex_U by (by100 blast)
    have h_sub: "{\<tau>\<in>K\<^sub>2. \<tau> \<inter> U \<noteq> {}} \<subseteq> {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using hK\<^sub>2_subK by (by100 blast)
    have hfin: "finite {\<tau>\<in>K\<^sub>2. \<tau> \<inter> U \<noteq> {}}"
      using finite_subset[OF h_sub hUfin] by (by100 blast)
    show "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K\<^sub>2. \<tau> \<inter> U \<noteq> {}}"
      using hU_open h\<sigma>U hfin by (by100 blast)
  qed
  have hK\<^sub>2_K3: "\<forall>\<sigma>\<in>K\<^sub>2. \<forall>\<tau>\<in>K\<^sub>2. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                  geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    using hK\<^sub>2_subK hK_inter by (by100 blast)
  have hK\<^sub>2_K2: "\<forall>\<sigma>\<in>K\<^sub>2. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K\<^sub>2"
  proof (intro ballI allI impI)
    fix \<sigma> \<tau> assume h\<sigma>: "\<sigma> \<in> K\<^sub>2" and hface: "geotop_is_face \<tau> \<sigma>"
    have h\<sigma>K: "\<sigma> \<in> K" using h\<sigma> hK\<^sub>2_subK by (by100 blast)
    obtain V\<^sub>\<sigma> where hV\<^sub>\<sigma>sv: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>" and hV\<^sub>\<sigma>V: "V\<^sub>\<sigma> \<inter> V = {}"
      using h\<sigma> unfolding K\<^sub>2_def by (by100 blast)
    obtain V' W where hV'sv: "geotop_simplex_vertices \<sigma> V'" and hWne: "W \<noteq> {}"
                  and hWV': "W \<subseteq> V'" and h\<tau>eq: "\<tau> = geotop_convex_hull W"
      using hface unfolding geotop_is_face_def by (by100 blast)
    have hV'eq: "V' = V\<^sub>\<sigma>"
      by (rule geotop_simplex_vertices_unique[OF hV'sv hV\<^sub>\<sigma>sv])
    have hWV\<^sub>\<sigma>: "W \<subseteq> V\<^sub>\<sigma>" using hWV' hV'eq by (by100 simp)
    have hWV: "W \<inter> V = {}" using hWV\<^sub>\<sigma> hV\<^sub>\<sigma>V by (by100 blast)
    have h\<tau>K: "\<tau> \<in> K" using hK_fc h\<sigma>K hface by (by100 blast)
    obtain m n where hV\<^sub>\<sigma>_unp: "finite V\<^sub>\<sigma>" and hV\<^sub>\<sigma>card: "card V\<^sub>\<sigma> = n+1"
                   and hnm: "n \<le> m" and hV\<^sub>\<sigma>gp: "geotop_general_position V\<^sub>\<sigma> m"
      using hV\<^sub>\<sigma>sv unfolding geotop_simplex_vertices_def by (by100 blast)
    have hWfin: "finite W" using hWV\<^sub>\<sigma> hV\<^sub>\<sigma>_unp finite_subset by (by100 blast)
    have hWgp: "geotop_general_position W m"
      by (rule geotop_general_position_mono[OF hV\<^sub>\<sigma>gp hWV\<^sub>\<sigma> hWfin])
    have hWcard_pos: "card W > 0"
      using hWne hWfin card_gt_0_iff by (by100 blast)
    have hWcard_ex: "\<exists>n'. card W = n' + 1" using hWcard_pos by (by100 presburger)
    obtain n' where hWcard: "card W = n' + 1" using hWcard_ex by (by100 blast)
    have hcard_leq: "card W \<le> card V\<^sub>\<sigma>"
      using hWV\<^sub>\<sigma> hV\<^sub>\<sigma>_unp card_mono by (by100 blast)
    have hn'_bound: "n' \<le> m"
      using hcard_leq hWcard hV\<^sub>\<sigma>card hnm by (by100 linarith)
    have h\<tau>sv: "geotop_simplex_vertices \<tau> W"
      unfolding geotop_simplex_vertices_def
      apply (rule exI[of _ m])
      apply (rule exI[of _ n'])
      using hWfin hWcard hn'_bound hWgp h\<tau>eq by (by100 blast)
    show "\<tau> \<in> K\<^sub>2"
      unfolding K\<^sub>2_def using h\<tau>K h\<tau>sv hWV by (by100 blast)
  qed
  have hK\<^sub>2_complex: "geotop_is_complex K\<^sub>2"
    unfolding geotop_is_complex_def
    using hK\<^sub>2_K1 hK\<^sub>2_K2 hK\<^sub>2_K3 hK\<^sub>2_K4 by (by100 blast)
  (** Step 4: bipartition — any simplex has all or no vertices in \<open>V\<close>.
      Proof: if \<sigma>\<in>K has vertex in \<open>V\<close> and vertex not in \<open>V\<close>, the edge between
      them lifts vertex-reachability to the "not-in-V" endpoint, a contradiction. **)
  have hK\<^sub>1\<^sub>2_cover: "K\<^sub>1 \<union> K\<^sub>2 = K"
  proof
    show "K\<^sub>1 \<union> K\<^sub>2 \<subseteq> K" unfolding K\<^sub>1_def K\<^sub>2_def by (by100 blast)
  next
    show "K \<subseteq> K\<^sub>1 \<union> K\<^sub>2"
    proof
      fix \<sigma> assume h\<sigma>K: "\<sigma> \<in> K"
      have h\<sigma>_simp: "geotop_is_simplex \<sigma>"
        using h\<sigma>K geotop_is_complex_simplex[OF hKcomp] by (by100 blast)
      have h\<sigma>_svx_ex: "\<exists>V. geotop_simplex_vertices \<sigma> V"
        using h\<sigma>_simp
        unfolding geotop_is_simplex_def geotop_simplex_vertices_def by (by100 blast)
      obtain V\<^sub>\<sigma> where hV\<^sub>\<sigma>sv: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>"
        using h\<sigma>_svx_ex by (by100 blast)
      (** Bipartition dichotomy: either \<open>V\<^sub>\<sigma> \<subseteq> V\<close> or \<open>V\<^sub>\<sigma> \<inter> V = {}\<close>.
          Suppose a mixed case: \<open>v' \<in> V\<^sub>\<sigma> \<inter> V\<close> and \<open>w \<in> V\<^sub>\<sigma> \<setminus> V\<close>.
          Then the edge \<open>conv {v', w}\<close> is a 1-face of \<sigma>, in \<open>K\<close> by face-closure.
          The segment \<open>v' \<to> w\<close> is a HOL path inside \<open>|K|\<close>; extending the
          \<open>v \<to> v'\<close> path (from \<open>v' \<in> V\<close>) gives \<open>v \<to> w\<close>, so \<open>w \<in> V\<close>,
          contradicting \<open>w \<notin> V\<close>. **)
      have h_dichotomy: "V\<^sub>\<sigma> \<subseteq> V \<or> V\<^sub>\<sigma> \<inter> V = {}"
      proof (rule ccontr)
        assume hneg: "\<not> (V\<^sub>\<sigma> \<subseteq> V \<or> V\<^sub>\<sigma> \<inter> V = {})"
        then have hmix: "\<not> V\<^sub>\<sigma> \<subseteq> V \<and> V\<^sub>\<sigma> \<inter> V \<noteq> {}" by (by100 blast)
        obtain v' where hv'_V\<^sub>\<sigma>: "v' \<in> V\<^sub>\<sigma>" and hv'_V: "v' \<in> V" using hmix by (by100 blast)
        obtain w where hw_V\<^sub>\<sigma>: "w \<in> V\<^sub>\<sigma>" and hw_nV: "w \<notin> V" using hmix by (by100 blast)
        (** The edge \<open>conv {v', w}\<close> is a face of \<sigma>, hence in \<open>K\<close>. **)
        have hvw_sub: "{v', w} \<subseteq> V\<^sub>\<sigma>" using hv'_V\<^sub>\<sigma> hw_V\<^sub>\<sigma> by (by100 blast)
        have hvw_ne: "({v', w}::'a set) \<noteq> {}" by (by100 simp)
        have h_hull_vw: "geotop_convex_hull ({v', w}::'a set) = convex hull {v', w}"
          by (rule geotop_convex_hull_eq_HOL)
        define e where "e = convex hull ({v', w}::'a set)"
        have he_eq_geo: "e = geotop_convex_hull ({v', w}::'a set)"
          unfolding e_def using h_hull_vw by (by100 simp)
        have h_e_face: "geotop_is_face e \<sigma>"
          unfolding geotop_is_face_def
          apply (rule exI[of _ V\<^sub>\<sigma>])
          apply (rule exI[of _ "{v', w}"])
          using hV\<^sub>\<sigma>sv hvw_ne hvw_sub he_eq_geo by (by100 blast)
        have hK_fc: "\<forall>\<sigma>'\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma>' \<longrightarrow> \<tau> \<in> K"
          using hKcomp by (rule geotop_is_complex_face_closed)
        have he_K: "e \<in> K" using hK_fc h\<sigma>K h_e_face by (by100 blast)
        (** \<open>v' \<in> V\<close> gives HOL path \<open>v \<to> v'\<close> in \<open>|K|\<close>. **)
        obtain g\<^sub>0 where hg\<^sub>0_path: "path g\<^sub>0"
                     and hg\<^sub>0_im: "path_image g\<^sub>0 \<subseteq> geotop_polyhedron K"
                     and hg\<^sub>0_s: "pathstart g\<^sub>0 = v" and hg\<^sub>0_f: "pathfinish g\<^sub>0 = v'"
          using hv'_V unfolding V_def by (by100 blast)
        (** Straight-line path \<open>v' \<to> w\<close> in \<open>e = conv {v', w}\<close>. **)
        have he_conv: "convex e" unfolding e_def by (by100 simp)
        have hv'_e: "v' \<in> e" unfolding e_def using hull_inc[of v' "{v', w}"] by (by100 simp)
        have hw_e: "w \<in> e" unfolding e_def using hull_inc[of w "{v', w}"] by (by100 simp)
        have he_pc: "path_connected e" by (rule convex_imp_path_connected[OF he_conv])
        obtain g\<^sub>1 where hg\<^sub>1_path: "path g\<^sub>1" and hg\<^sub>1_im: "path_image g\<^sub>1 \<subseteq> e"
                     and hg\<^sub>1_s: "pathstart g\<^sub>1 = v'" and hg\<^sub>1_f: "pathfinish g\<^sub>1 = w"
          using he_pc hv'_e hw_e unfolding path_connected_def by (by100 blast)
        have he_sub_K: "e \<subseteq> geotop_polyhedron K"
          using he_K unfolding geotop_polyhedron_def by (by100 blast)
        have hg\<^sub>1_im_K: "path_image g\<^sub>1 \<subseteq> geotop_polyhedron K"
          using hg\<^sub>1_im he_sub_K by (by100 blast)
        (** Concatenate \<open>g\<^sub>0 +++ g\<^sub>1\<close>. **)
        have h_join: "pathfinish g\<^sub>0 = pathstart g\<^sub>1" using hg\<^sub>0_f hg\<^sub>1_s by (by100 simp)
        define g where "g = g\<^sub>0 +++ g\<^sub>1"
        have hg_path: "path g"
          unfolding g_def by (rule path_join_imp[OF hg\<^sub>0_path hg\<^sub>1_path h_join])
        have hg_s: "pathstart g = v" unfolding g_def using hg\<^sub>0_s by (by100 simp)
        have hg_f: "pathfinish g = w" unfolding g_def using hg\<^sub>1_f by (by100 simp)
        have hg_im_eq: "path_image g = path_image g\<^sub>0 \<union> path_image g\<^sub>1"
          unfolding g_def by (rule path_image_join[OF h_join])
        have hg_im: "path_image g \<subseteq> geotop_polyhedron K"
          using hg_im_eq hg\<^sub>0_im hg\<^sub>1_im_K by (by100 blast)
        (** \<open>w\<close> is a vertex of \<open>\<sigma> \<in> K\<close>, hence a vertex of \<open>K\<close>. **)
        have hw_K: "w \<in> geotop_complex_vertices K"
          unfolding geotop_complex_vertices_def using h\<sigma>K hV\<^sub>\<sigma>sv hw_V\<^sub>\<sigma> by (by100 blast)
        (** So \<open>w \<in> V\<close>, contradicting \<open>w \<notin> V\<close>. **)
        have hw_V_from_path: "w \<in> V"
          unfolding V_def using hw_K hg_path hg_im hg_s hg_f by (by100 blast)
        show False using hw_V_from_path hw_nV by (by100 blast)
      qed
      show "\<sigma> \<in> K\<^sub>1 \<union> K\<^sub>2"
        using h\<sigma>K hV\<^sub>\<sigma>sv h_dichotomy
        unfolding K\<^sub>1_def K\<^sub>2_def by (by100 blast)
    qed
  qed
  have hK\<^sub>1\<^sub>2_disjoint: "K\<^sub>1 \<inter> K\<^sub>2 = {}"
  proof (rule equals0I)
    fix \<sigma> assume h\<sigma>12: "\<sigma> \<in> K\<^sub>1 \<inter> K\<^sub>2"
    then obtain V\<^sub>1 where hV\<^sub>1: "geotop_simplex_vertices \<sigma> V\<^sub>1" and hV\<^sub>1V: "V\<^sub>1 \<subseteq> V"
      unfolding K\<^sub>1_def by (by100 blast)
    obtain V\<^sub>2 where hV\<^sub>2: "geotop_simplex_vertices \<sigma> V\<^sub>2" and hV\<^sub>2V: "V\<^sub>2 \<inter> V = {}"
      using h\<sigma>12 unfolding K\<^sub>2_def by (by100 blast)
    (** Both vertex sets determine \<sigma> by convex hull; \<open>V\<^sub>1, V\<^sub>2\<close> are in general position
        so \<open>convex_hull V\<^sub>1 = convex_hull V\<^sub>2 \<Rightarrow> V\<^sub>1 = V\<^sub>2\<close>. Deferred vertex-uniqueness
        argument; here we just derive the contradiction from the weak claim that
        \<open>V\<^sub>1 \<subseteq> V\<^sub>2\<close> or vice versa (even with distinct vertex sets, they'd both be
        subsets of the extreme points and intersect in common extreme points). **)
    have hV12_eq: "V\<^sub>1 = V\<^sub>2"
      by (rule geotop_simplex_vertices_unique[OF hV\<^sub>1 hV\<^sub>2])
    have hV\<^sub>1_empty: "V\<^sub>1 = {}" using hV\<^sub>1V hV\<^sub>2V hV12_eq by (by100 blast)
    have hV\<^sub>1_card: "card V\<^sub>1 \<ge> 1"
      using hV\<^sub>1 unfolding geotop_simplex_vertices_def by (by100 fastforce)
    show False using hV\<^sub>1_empty hV\<^sub>1_card by (by100 simp)
  qed
  (** Step 6: \<open>K\<^sub>1 \<noteq> \<emptyset>\<close> because \<open>{v}\<close> is a 0-simplex in \<open>K\<^sub>1\<close>.
      Use: \<open>v \<in> \<sigma>\<^sub>v \<in> K\<close> with vertex set \<open>V\<^sub>v \<ni> v\<close>; then \<open>{v}\<close> is a face of \<open>\<sigma>\<^sub>v\<close>,
      and by K.2 face-closure \<open>{v} \<in> K\<close>. Since \<open>v \<in> V\<close> (Step 1), \<open>{v} \<in> K\<^sub>1\<close>. **)
  have hK\<^sub>1_nonempty: "K\<^sub>1 \<noteq> {}"
  proof -
    (** Repeat the \<sigma>_v setup for this scope. **)
    obtain \<sigma>\<^sub>v V\<^sub>v where h\<sigma>\<^sub>v: "\<sigma>\<^sub>v \<in> K" and hV\<^sub>v: "geotop_simplex_vertices \<sigma>\<^sub>v V\<^sub>v"
                     and hv_in_V\<^sub>v: "v \<in> V\<^sub>v"
      using hv unfolding geotop_complex_vertices_def by (by100 blast)
    (** \<open>{v}\<close> is a face of \<open>\<sigma>\<^sub>v\<close>. **)
    have h_hull_v1: "geotop_convex_hull ({v}::'a set) = {v}"
      using geotop_convex_hull_eq_HOL[of "{v}::'a set"] by (by100 simp)
    have h_face: "geotop_is_face {v} \<sigma>\<^sub>v"
      unfolding geotop_is_face_def
      using hV\<^sub>v hv_in_V\<^sub>v h_hull_v1
      by (by100 blast)
    have hK_fc: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
      using hKcomp by (rule geotop_is_complex_face_closed)
    have h_vset_K: "{v} \<in> K"
      using hK_fc h\<sigma>\<^sub>v h_face by (by100 blast)
    (** \<open>{v}\<close> is a simplex with vertex set \<open>{v}\<close>. **)
    have h_gp_trivial: "geotop_general_position ({v}::'a set) 0"
      unfolding geotop_general_position_def by (by100 blast)
    have h_vset_svx: "geotop_simplex_vertices {v} {v}"
      unfolding geotop_simplex_vertices_def
      apply (rule exI[of _ "0::nat"])
      apply (rule exI[of _ "0::nat"])
      using h_hull_v1 h_gp_trivial by (by100 simp)
    have h_vsub: "({v}::'a set) \<subseteq> V"
      using hv_V by (by100 simp)
    show "K\<^sub>1 \<noteq> {}"
      unfolding K\<^sub>1_def using h_vset_K h_vset_svx h_vsub by (by100 blast)
  qed
  (** Step 7: by \<open>complex_connected K\<close>, \<open>K\<^sub>2 = \<emptyset>\<close>, so every simplex of \<open>K\<close> has
      all vertices in \<open>V\<close>. Hence \<open>w \<in> V\<close>. **)
  (** Step 7: From complex-connectedness, \<open>K_2 = \<emptyset>\<close>. **)
  have hK\<^sub>2_empty: "K\<^sub>2 = {}"
  proof (rule ccontr)
    assume hK\<^sub>2ne: "K\<^sub>2 \<noteq> {}"
    have hK_union: "K = K\<^sub>1 \<union> K\<^sub>2" using hK\<^sub>1\<^sub>2_cover by (by100 blast)
    have hnot_conn: "\<exists>Ka Kb. Ka \<noteq> {} \<and> Kb \<noteq> {} \<and> Ka \<inter> Kb = {} \<and> K = Ka \<union> Kb
                          \<and> geotop_is_complex Ka \<and> geotop_is_complex Kb"
      apply (rule exI[of _ K\<^sub>1])
      apply (rule exI[of _ K\<^sub>2])
      using hK\<^sub>1_nonempty hK\<^sub>2ne hK\<^sub>1\<^sub>2_disjoint hK_union hK\<^sub>1_complex hK\<^sub>2_complex
      by (by100 blast)
    show False
      using hnot_conn hK unfolding geotop_complex_connected_def by (by100 blast)
  qed
  (** Hence every simplex of K is in K_1, i.e., all vertices lie in V. **)
  have hK_is_K\<^sub>1: "K = K\<^sub>1"
    using hK\<^sub>1\<^sub>2_cover hK\<^sub>2_empty by (by100 blast)
  have hV_all: "geotop_complex_vertices K \<subseteq> V"
    unfolding geotop_complex_vertices_def
  proof (rule Union_least)
    fix W assume hW_class: "W \<in> {V'. \<exists>\<sigma>\<in>K. geotop_simplex_vertices \<sigma> V'}"
    then obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K" and hWsv: "geotop_simplex_vertices \<sigma> W"
      by (by100 blast)
    have h\<sigma>K\<^sub>1: "\<sigma> \<in> K\<^sub>1" using h\<sigma>K hK_is_K\<^sub>1 by (by100 simp)
    then obtain V\<^sub>\<sigma> where hV\<^sub>\<sigma>sv: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>" and hV\<^sub>\<sigma>V: "V\<^sub>\<sigma> \<subseteq> V"
      unfolding K\<^sub>1_def by (by100 blast)
    have hW_eq: "W = V\<^sub>\<sigma>"
      by (rule geotop_simplex_vertices_unique[OF hWsv hV\<^sub>\<sigma>sv])
    show "W \<subseteq> V" using hV\<^sub>\<sigma>V hW_eq by (by100 simp)
  qed
  have hw_V: "w \<in> V" using hV_all hw by (by100 blast)
  show ?thesis using hw_V unfolding V_def by (by100 blast)
qed

lemma geotop_complex_connected_imp_HOL_path_connected:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_complex_connected K"
  shows "path_connected (geotop_polyhedron K)"
  unfolding path_connected_def
proof (intro ballI)
  fix P Q assume hP: "P \<in> geotop_polyhedron K" and hQ: "Q \<in> geotop_polyhedron K"
  have hKcomp: "geotop_is_complex K"
    using hK unfolding geotop_complex_connected_def by (by100 blast)
  (** Pick simplexes \<sigma>_P, \<sigma>_Q containing P, Q respectively. **)
  obtain \<sigma>P where h\<sigma>P: "\<sigma>P \<in> K" and hP\<sigma>P: "P \<in> \<sigma>P"
    using hP unfolding geotop_polyhedron_def by (by100 blast)
  obtain \<sigma>Q where h\<sigma>Q: "\<sigma>Q \<in> K" and hQ\<sigma>Q: "Q \<in> \<sigma>Q"
    using hQ unfolding geotop_polyhedron_def by (by100 blast)
  (** Each simplex is a convex hull of its vertex set. Pick any vertex of each. **)
  have hall_simp: "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
    using hKcomp by (rule geotop_is_complex_simplex)
  have h\<sigma>P_simp: "geotop_is_simplex \<sigma>P" using hall_simp h\<sigma>P by (by100 blast)
  have h\<sigma>Q_simp: "geotop_is_simplex \<sigma>Q" using hall_simp h\<sigma>Q by (by100 blast)
  obtain VP where hVP: "geotop_simplex_vertices \<sigma>P VP"
    using h\<sigma>P_simp
    unfolding geotop_is_simplex_def geotop_simplex_vertices_def by (by100 blast)
  obtain VQ where hVQ: "geotop_simplex_vertices \<sigma>Q VQ"
    using h\<sigma>Q_simp
    unfolding geotop_is_simplex_def geotop_simplex_vertices_def by (by100 blast)
  have hVP_card: "\<exists>n. finite VP \<and> card VP = n + 1"
    using hVP unfolding geotop_simplex_vertices_def by (by100 blast)
  have hVPne: "VP \<noteq> {}"
    using hVP_card by (by100 fastforce)
  have hVQ_card: "\<exists>n. finite VQ \<and> card VQ = n + 1"
    using hVQ unfolding geotop_simplex_vertices_def by (by100 blast)
  have hVQne: "VQ \<noteq> {}"
    using hVQ_card by (by100 fastforce)
  obtain vP where hvP: "vP \<in> VP" using hVPne by (by100 blast)
  obtain vQ where hvQ: "vQ \<in> VQ" using hVQne by (by100 blast)
  (** Each vertex is in vertices K. **)
  have hvP_K: "vP \<in> geotop_complex_vertices K"
    unfolding geotop_complex_vertices_def using h\<sigma>P hVP hvP by (by100 blast)
  have hvQ_K: "vQ \<in> geotop_complex_vertices K"
    unfolding geotop_complex_vertices_def using h\<sigma>Q hVQ hvQ by (by100 blast)
  (** \<sigma>_P and \<sigma>_Q are convex. **)
  have h\<sigma>P_conv: "convex \<sigma>P"
    using geotop_simplex_is_convex[OF h\<sigma>P_simp] geotop_convex_iff_HOL_convex by (by100 blast)
  have h\<sigma>Q_conv: "convex \<sigma>Q"
    using geotop_simplex_is_convex[OF h\<sigma>Q_simp] geotop_convex_iff_HOL_convex by (by100 blast)
  have h\<sigma>P_eq: "\<sigma>P = convex hull VP"
    using hVP geotop_convex_hull_eq_HOL
    unfolding geotop_simplex_vertices_def by (by100 blast)
  have h\<sigma>Q_eq: "\<sigma>Q = convex hull VQ"
    using hVQ geotop_convex_hull_eq_HOL
    unfolding geotop_simplex_vertices_def by (by100 blast)
  have hvP_hull: "vP \<in> convex hull VP"
    using hvP hull_inc[of vP VP] by (by100 simp)
  have hvQ_hull: "vQ \<in> convex hull VQ"
    using hvQ hull_inc[of vQ VQ] by (by100 simp)
  have hvP_in_\<sigma>P: "vP \<in> \<sigma>P" using hvP_hull h\<sigma>P_eq by (by100 simp)
  have hvQ_in_\<sigma>Q: "vQ \<in> \<sigma>Q" using hvQ_hull h\<sigma>Q_eq by (by100 simp)
  (** Path from P to vP in \<sigma>_P (straight line). **)
  have h\<sigma>P_pc: "path_connected \<sigma>P"
    by (rule convex_imp_path_connected[OF h\<sigma>P_conv])
  obtain g1 where hg1_path: "path g1" and hg1_im: "path_image g1 \<subseteq> \<sigma>P"
              and hg1_s: "pathstart g1 = P" and hg1_f: "pathfinish g1 = vP"
    using h\<sigma>P_pc hP\<sigma>P hvP_in_\<sigma>P unfolding path_connected_def by (by100 blast)
  (** Path from vP to vQ via vertex reachability. **)
  obtain g2 where hg2_path: "path g2"
              and hg2_im: "path_image g2 \<subseteq> geotop_polyhedron K"
              and hg2_s: "pathstart g2 = vP" and hg2_f: "pathfinish g2 = vQ"
    using geotop_complex_connected_imp_HOL_vertex_reachable[OF hK hvP_K hvQ_K]
    by (by100 blast)
  (** Path from vQ to Q in \<sigma>_Q. **)
  have h\<sigma>Q_pc: "path_connected \<sigma>Q"
    by (rule convex_imp_path_connected[OF h\<sigma>Q_conv])
  obtain g3 where hg3_path: "path g3" and hg3_im: "path_image g3 \<subseteq> \<sigma>Q"
              and hg3_s: "pathstart g3 = vQ" and hg3_f: "pathfinish g3 = Q"
    using h\<sigma>Q_pc hvQ_in_\<sigma>Q hQ\<sigma>Q unfolding path_connected_def by (by100 blast)
  (** Concatenate g1 +++ g2 +++ g3. **)
  have h\<sigma>P_sub_K: "\<sigma>P \<subseteq> geotop_polyhedron K"
    using h\<sigma>P unfolding geotop_polyhedron_def by (by100 blast)
  have h\<sigma>Q_sub_K: "\<sigma>Q \<subseteq> geotop_polyhedron K"
    using h\<sigma>Q unfolding geotop_polyhedron_def by (by100 blast)
  have hg1_im_K: "path_image g1 \<subseteq> geotop_polyhedron K"
    using hg1_im h\<sigma>P_sub_K by (by100 blast)
  have hg3_im_K: "path_image g3 \<subseteq> geotop_polyhedron K"
    using hg3_im h\<sigma>Q_sub_K by (by100 blast)
  (** \<open>+++\<close> is right-associative in HOL-Analysis, so \<open>g1 +++ g2 +++ g3\<close>
      parses as \<open>g1 +++ (g2 +++ g3)\<close>. Join \<open>g2\<close> with \<open>g3\<close> first, then \<open>g1\<close>. **)
  define g23 where "g23 = g2 +++ g3"
  have h23_join: "pathfinish g2 = pathstart g3" using hg2_f hg3_s by (by100 simp)
  have h23_path: "path g23"
    unfolding g23_def by (rule path_join_imp[OF hg2_path hg3_path h23_join])
  have h23_s: "pathstart g23 = vP" unfolding g23_def using hg2_s by (by100 simp)
  have h23_f: "pathfinish g23 = Q" unfolding g23_def using hg3_f by (by100 simp)
  have h23_im_eq: "path_image g23 = path_image g2 \<union> path_image g3"
    unfolding g23_def by (rule path_image_join[OF h23_join])
  have h23_im_K: "path_image g23 \<subseteq> geotop_polyhedron K"
    using h23_im_eq hg2_im hg3_im_K by (by100 blast)
  define g where "g = g1 +++ g23"
  have h1_23_join: "pathfinish g1 = pathstart g23"
    using hg1_f h23_s by (by100 simp)
  have hg_path: "path g"
    unfolding g_def by (rule path_join_imp[OF hg1_path h23_path h1_23_join])
  have hg_s: "pathstart g = P" unfolding g_def using hg1_s by (by100 simp)
  have hg_f: "pathfinish g = Q" unfolding g_def using h23_f by (by100 simp)
  have hg_im_eq: "path_image g = path_image g1 \<union> path_image g23"
    unfolding g_def by (rule path_image_join[OF h1_23_join])
  have hg_im: "path_image g \<subseteq> geotop_polyhedron K"
    using hg_im_eq hg1_im_K h23_im_K by (by100 blast)
  show "\<exists>g. path g \<and> path_image g \<subseteq> geotop_polyhedron K
            \<and> pathstart g = P \<and> pathfinish g = Q"
    using hg_path hg_im hg_s hg_f by (by100 blast)
qed

theorem Theorem_GT_1_4:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_complex_connected K"
  shows "top1_path_connected_on (geotop_polyhedron K)
           (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
  (** Moise proof (geotop.tex:343). Structured following the book:
      Step 1: Fix any vertex v0 of K.
      Step 2: Let V = {v in vertices(K): exists path in |1-skeleton| from v0 to v}.
      Step 3: Let K1 = {sigma in K: all vertices of sigma in V}. Then K1 is a subcomplex.
      Step 4: Every simplex of K has either all vertices in V or none in V.
              (Else an edge from V to vertices - V would force its far endpoint into V.)
      Step 5: Hence K2 = K - K1 = {sigma in K: no vertex of sigma in V} is a subcomplex.
      Step 6: K1 inter K2 = {}, K = K1 union K2, K1 nonempty. By complex_connected K, K2 = {}.
      Step 7: Hence V = vertices(K): every two vertices path-connected through |1-skeleton|.
      Step 8: For arbitrary P, Q in |K|, take sigma_P with P, sigma_Q with Q. Paths:
              P to vP in sigma_P (convex), vP to vQ (in 1-skel), vQ to Q in sigma_Q (convex). **)
proof -
  (** Use the HOL path-connectedness helper and lift via the bridge. **)
  have hHOL_pc: "path_connected (geotop_polyhedron K)"
    by (rule geotop_complex_connected_imp_HOL_path_connected[OF hK])
  show ?thesis
    by (rule path_connected_imp_top1_path_connected_on_geotop[OF hHOL_pc])
qed

(** from \<S>1: connected topological space (geotop.tex:349)
    LATEX VERSION: A topological space [X,\<O>] is connected if X is not the union of two
      disjoint nonempty open sets. Already available in Top0 as \<open>top1_connected_on\<close>. **)

(** from \<S>1: separated sets (geotop.tex:351)
    LATEX VERSION: Two sets H,K are separated if \<bar>H\<close> \<inter> K = H \<inter> \<bar>K\<close> = \<emptyset>. **)
definition geotop_separated ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_separated X T H K \<longleftrightarrow>
    H \<subseteq> X \<and> K \<subseteq> X \<and>
    closure_on X T H \<inter> K = {} \<and> H \<inter> closure_on X T K = {}"

(** from \<S>1 Theorem 5 (geotop.tex:359)
    LATEX VERSION: Given M \<subset> X, M = H \<union> K. Then (1) H and K are separated iff
      (2) H, K \<in> \<O>|M and H \<inter> K = \<emptyset>. **)
theorem Theorem_GT_1_5:
  assumes hTX: "is_topology_on X T"
  assumes hMX: "M \<subseteq> X"
  assumes hHM: "H \<subseteq> M"
  assumes hKM: "K \<subseteq> M"
  assumes hMHK: "M = H \<union> K"
  shows "geotop_separated X T H K \<longleftrightarrow>
    (H \<in> subspace_topology X T M \<and> K \<in> subspace_topology X T M \<and> H \<inter> K = {})"
  (** Standard topology result (Munkres \<S>23.3 / Moise 1.5, no proof shown). **)
proof (rule iffI)
  (** FORWARD: separated \<Longrightarrow> both clopen in subspace + disjoint. **)
  assume hsep: "geotop_separated X T H K"
  from hsep have hHX: "H \<subseteq> X" and hKX: "K \<subseteq> X"
      and hclHK: "closure_on X T H \<inter> K = {}"
      and hHclK: "H \<inter> closure_on X T K = {}"
    unfolding geotop_separated_def by simp_all
  have hKclK: "K \<subseteq> closure_on X T K" by (rule subset_closure_on)
  have hHK_disj: "H \<inter> K = {}" using hHclK hKclK by fast
  (** H = M \<inter> (X - closure_X K). **)
  have hH_eq: "H = M \<inter> (X - closure_on X T K)"
  proof (rule set_eqI, rule iffI)
    fix x assume hxH: "x \<in> H"
    have hxM: "x \<in> M" using hxH hHM by fast
    have hx_notK: "x \<notin> closure_on X T K" using hxH hHclK by fast
    have hxX: "x \<in> X" using hxM hMX by fast
    show "x \<in> M \<inter> (X - closure_on X T K)" using hxM hx_notK hxX by fast
  next
    fix x assume hxMK: "x \<in> M \<inter> (X - closure_on X T K)"
    then have hxM: "x \<in> M" and hxnotclK: "x \<notin> closure_on X T K" by auto
    have "x \<in> H \<or> x \<in> K" using hxM hMHK by fast
    moreover have "x \<notin> K" using hxnotclK hKclK by fast
    ultimately show "x \<in> H" by simp
  qed
  (** Symmetric: K = M \<inter> (X - closure_X H). **)
  have hK_eq: "K = M \<inter> (X - closure_on X T H)"
  proof (rule set_eqI, rule iffI)
    fix x assume hxK: "x \<in> K"
    have hxM: "x \<in> M" using hxK hKM by fast
    have hx_notclH: "x \<notin> closure_on X T H" using hxK hclHK by fast
    show "x \<in> M \<inter> (X - closure_on X T H)" using hxM hx_notclH hMX by fast
  next
    fix x assume hxMH: "x \<in> M \<inter> (X - closure_on X T H)"
    then have hxM: "x \<in> M" and hxnotclH: "x \<notin> closure_on X T H" by auto
    have "x \<in> H \<or> x \<in> K" using hxM hMHK by fast
    moreover have hHclH: "H \<subseteq> closure_on X T H" by (rule subset_closure_on)
    ultimately show "x \<in> K" using hxnotclH by fast
  qed
  (** Both closure_X K and closure_X H are closed in X; their complements (in X) are open. **)
  have hclK_closed: "closedin_on X T (closure_on X T K)"
    using hKX closure_on_closed[OF hTX hKX] by simp
  have hXminusClK_open: "X - closure_on X T K \<in> T"
    using hclK_closed unfolding closedin_on_def by simp
  have hclH_closed: "closedin_on X T (closure_on X T H)"
    using hHX closure_on_closed[OF hTX hHX] by simp
  have hXminusClH_open: "X - closure_on X T H \<in> T"
    using hclH_closed unfolding closedin_on_def by simp
  (** H is in subspace topology. **)
  have hH_sub: "H \<in> subspace_topology X T M"
    unfolding subspace_topology_def
    using hXminusClK_open hH_eq by blast
  have hK_sub: "K \<in> subspace_topology X T M"
    unfolding subspace_topology_def
    using hXminusClH_open hK_eq by blast
  show "H \<in> subspace_topology X T M \<and> K \<in> subspace_topology X T M \<and> H \<inter> K = {}"
    using hH_sub hK_sub hHK_disj by simp
next
  (** REVERSE: both in subspace + disjoint \<Longrightarrow> separated. **)
  assume hhyp: "H \<in> subspace_topology X T M \<and> K \<in> subspace_topology X T M \<and> H \<inter> K = {}"
  then have hH_sub: "H \<in> subspace_topology X T M"
      and hK_sub: "K \<in> subspace_topology X T M"
      and hHK_disj: "H \<inter> K = {}"
    by auto
  obtain U where hU: "U \<in> T" and hHU: "H = M \<inter> U"
    using hH_sub unfolding subspace_topology_def by blast
  obtain V where hV: "V \<in> T" and hKV: "K = M \<inter> V"
    using hK_sub unfolding subspace_topology_def by blast
  (** K = M - H since M = H \<union> K and H \<inter> K = {}. **)
  have hK_compl_H: "K = M - H"
    using hMHK hHK_disj by blast
  have hH_compl_K: "H = M - K"
    using hMHK hHK_disj by blast
  (** K = M \<inter> (X - U): from K ⊆ M and K ∩ H = ∅ i.e. K ∩ U ∩ M = ∅, so K ⊆ M - U. **)
  have hK_complU_inM: "K \<subseteq> M \<inter> (X - U)"
  proof (rule subsetI)
    fix x assume hxK: "x \<in> K"
    have hxM: "x \<in> M" using hxK hKM by fast
    have "x \<notin> H" using hxK hHK_disj by fast
    hence "x \<notin> M \<inter> U" using hHU by simp
    hence "x \<notin> U" using hxM by simp
    thus "x \<in> M \<inter> (X - U)" using hxM hMX by fast
  qed
  (** closure_M K = K (K is closed in M). We use the subspace closure theorem. **)
  have hKclosed_in_M: "closedin_on M (subspace_topology X T M) K"
  proof -
    have "H = (M \<inter> U)" using hHU by simp
    have "M - K = H" using hH_compl_K by simp
    hence "M - K = M \<inter> U" using hHU by simp
    have "M - K \<in> subspace_topology X T M" using hH_sub hH_compl_K by simp
    thus ?thesis unfolding closedin_on_def
      using hKM by simp
  qed
  have hHclosed_in_M: "closedin_on M (subspace_topology X T M) H"
  proof -
    have "M - H = K" using hK_compl_H by simp
    hence "M - H \<in> subspace_topology X T M" using hK_sub by simp
    thus ?thesis unfolding closedin_on_def
      using hHM by simp
  qed
  (** Closure of K in subspace = K (since K closed in M). **)
  have hclK_M: "closure_on M (subspace_topology X T M) K = K"
  proof (rule equalityI)
    show "closure_on M (subspace_topology X T M) K \<subseteq> K"
      by (rule closure_on_subset_of_closed[OF hKclosed_in_M]) simp
    show "K \<subseteq> closure_on M (subspace_topology X T M) K"
      by (rule subset_closure_on)
  qed
  have hclH_M: "closure_on M (subspace_topology X T M) H = H"
  proof (rule equalityI)
    show "closure_on M (subspace_topology X T M) H \<subseteq> H"
      by (rule closure_on_subset_of_closed[OF hHclosed_in_M]) simp
    show "H \<subseteq> closure_on M (subspace_topology X T M) H"
      by (rule subset_closure_on)
  qed
  (** By Theorem_17_4: closure_M X = closure_X X \<inter> M. **)
  have hclK_trans: "closure_on M (subspace_topology X T M) K = closure_on X T K \<inter> M"
    by (rule Theorem_17_4[OF hTX hKM hMX])
  have hclH_trans: "closure_on M (subspace_topology X T M) H = closure_on X T H \<inter> M"
    by (rule Theorem_17_4[OF hTX hHM hMX])
  (** So K = closure_X K \<inter> M. **)
  have hK_eq_cl: "K = closure_on X T K \<inter> M"
    using hclK_M hclK_trans by simp
  have hH_eq_cl: "H = closure_on X T H \<inter> M"
    using hclH_M hclH_trans by simp
  (** closure_X H \<inter> K = ? Since K \<subseteq> M, K \<inter> closure_X H = closure_X H \<inter> M \<inter> K = H \<inter> K = \<emptyset>. **)
  have hclH_K_disj: "closure_on X T H \<inter> K = {}"
  proof -
    have "closure_on X T H \<inter> K = closure_on X T H \<inter> M \<inter> K"
      using hKM by fast
    also have "\<dots> = H \<inter> K" using hH_eq_cl by simp
    also have "\<dots> = {}" using hHK_disj by simp
    finally show ?thesis .
  qed
  have hH_clK_disj: "H \<inter> closure_on X T K = {}"
  proof -
    have "H \<inter> closure_on X T K = closure_on X T K \<inter> M \<inter> H"
      using hHM by fast
    also have "\<dots> = K \<inter> H" using hK_eq_cl by simp
    also have "\<dots> = {}" using hHK_disj by fast
    finally show ?thesis .
  qed
  have hHX: "H \<subseteq> X" using hHM hMX by fast
  have hKX: "K \<subseteq> X" using hKM hMX by fast
  show "geotop_separated X T H K"
    unfolding geotop_separated_def
    using hHX hKX hclH_K_disj hH_clK_disj by simp
qed

(** from \<S>1 Theorem 6 (geotop.tex:365)
    LATEX VERSION: A set M \<subset> X is connected iff M is not the union of two nonempty
      separated sets. **)
theorem Theorem_GT_1_6:
  assumes hT: "is_topology_on X T" and hMX: "M \<subseteq> X"
  shows "top1_connected_on M (subspace_topology X T M) \<longleftrightarrow>
    \<not>(\<exists>H K. H \<noteq> {} \<and> K \<noteq> {} \<and> M = H \<union> K \<and> geotop_separated X T H K)"
proof -
  have hTM: "is_topology_on M (subspace_topology X T M)"
    by (rule subspace_topology_is_topology_on[OF hT hMX])
  show ?thesis
  proof
    assume hconn: "top1_connected_on M (subspace_topology X T M)"
    show "\<not>(\<exists>H K. H \<noteq> {} \<and> K \<noteq> {} \<and> M = H \<union> K \<and> geotop_separated X T H K)"
    proof (intro notI, elim exE conjE)
      fix H K assume hHne: "H \<noteq> {}" and hKne: "K \<noteq> {}"
        and hMHK: "M = H \<union> K" and hsep: "geotop_separated X T H K"
      have hHM: "H \<subseteq> M" and hKM: "K \<subseteq> M" using hMHK by (by100 auto)
      have hsplit: "H \<in> subspace_topology X T M \<and> K \<in> subspace_topology X T M
                     \<and> H \<inter> K = {}"
        using Theorem_GT_1_5[OF hT hMX hHM hKM hMHK] hsep by (by100 blast)
      show False
        using hconn hHne hKne hMHK hsplit
        unfolding top1_connected_on_def by (by100 blast)
    qed
  next
    assume hno_sep:
      "\<not>(\<exists>H K. H \<noteq> {} \<and> K \<noteq> {} \<and> M = H \<union> K \<and> geotop_separated X T H K)"
    show "top1_connected_on M (subspace_topology X T M)"
      unfolding top1_connected_on_def
    proof (intro conjI notI, rule hTM, elim exE conjE)
      fix U V assume hU: "U \<in> subspace_topology X T M" and hV: "V \<in> subspace_topology X T M"
        and hUne: "U \<noteq> {}" and hVne: "V \<noteq> {}"
        and hUV: "U \<inter> V = {}" and hUVM: "U \<union> V = M"
      have hUM: "U \<subseteq> M" and hVM: "V \<subseteq> M" using hUVM by (by100 auto)
      have hMUV: "M = U \<union> V" using hUVM by (by100 simp)
      have hsep: "geotop_separated X T U V"
        using Theorem_GT_1_5[OF hT hMX hUM hVM hMUV] hU hV hUV by (by100 blast)
      show False using hno_sep hUne hVne hMUV hsep by (by100 blast)
    qed
  qed
qed

(** from \<S>1 Theorem 7 (geotop.tex:369)
    LATEX VERSION: For spaces, connectivity is preserved by surjective mappings. **)
theorem Theorem_GT_1_7:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hcont: "top1_continuous_map_on X TX Y TY f"
  assumes hsurj: "f ` X = Y"
  assumes hXconn: "top1_connected_on X TX"
  shows "top1_connected_on Y TY"
  (** Moise proof (geotop.tex:369): standard, by Top0 Theorem_23_5. Bridge:
      connectedness in subspace(Y,TY,Y) implies connectedness in TY because any
      separation U,V \<in> TY of Y must satisfy U,V \<subseteq> Y (since U \<union> V = Y), hence
      Y \<inter> U = U and Y \<inter> V = V are separating opens in the subspace too. **)
proof (unfold top1_connected_on_def, intro conjI hTY)
  show "\<nexists>U V. U \<in> TY \<and> V \<in> TY \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = Y"
  proof (rule notI)
    assume "\<exists>U V. U \<in> TY \<and> V \<in> TY \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = Y"
    then obtain U V where hU: "U \<in> TY" and hV: "V \<in> TY"
        and hUne: "U \<noteq> {}" and hVne: "V \<noteq> {}"
        and hUV_disj: "U \<inter> V = {}" and hUV_cover: "U \<union> V = Y" by blast
    (** f \<^sup>{-1}(U), f \<^sup>{-1}(V) are open in X by continuity. **)
    have hfU: "{x\<in>X. f x \<in> U} \<in> TX"
      using hcont hU unfolding top1_continuous_map_on_def by blast
    have hfV: "{x\<in>X. f x \<in> V} \<in> TX"
      using hcont hV unfolding top1_continuous_map_on_def by blast
    have hfU_in_Y: "\<forall>x\<in>X. f x \<in> Y"
      using hcont unfolding top1_continuous_map_on_def by blast
    (** Preimages cover X (since f `X = Y = U \<union> V). **)
    have hpreimgs_cover: "{x\<in>X. f x \<in> U} \<union> {x\<in>X. f x \<in> V} = X"
      using hfU_in_Y hUV_cover by blast
    (** Preimages are disjoint. **)
    have hpreimgs_disj: "{x\<in>X. f x \<in> U} \<inter> {x\<in>X. f x \<in> V} = {}"
      using hUV_disj by blast
    (** Preimages are nonempty (via surjectivity). **)
    from hUne obtain y where hyU: "y \<in> U" by blast
    have hyY: "y \<in> Y" using hyU hUV_cover by blast
    then obtain x where hxX: "x \<in> X" and hfx: "f x = y"
      using hsurj by blast
    have hpreimg_U_ne: "{x\<in>X. f x \<in> U} \<noteq> {}"
      using hxX hfx hyU by blast
    from hVne obtain y2 where hy2V: "y2 \<in> V" by blast
    have hy2Y: "y2 \<in> Y" using hy2V hUV_cover by blast
    then obtain x2 where hx2X: "x2 \<in> X" and hfx2: "f x2 = y2"
      using hsurj by blast
    have hpreimg_V_ne: "{x\<in>X. f x \<in> V} \<noteq> {}"
      using hx2X hfx2 hy2V by blast
    (** Now we have a separation of X, contradicting X connected. **)
    have "\<exists>U' V'. U' \<in> TX \<and> V' \<in> TX \<and> U' \<noteq> {} \<and> V' \<noteq> {} \<and> U' \<inter> V' = {} \<and> U' \<union> V' = X"
      apply (rule exI[of _ "{x\<in>X. f x \<in> U}"])
      apply (rule exI[of _ "{x\<in>X. f x \<in> V}"])
      using hfU hfV hpreimg_U_ne hpreimg_V_ne hpreimgs_cover hpreimgs_disj by simp
    thus False
      using hXconn unfolding top1_connected_on_def by blast
  qed
qed

(** from \<S>1 Theorem 8 (geotop.tex:373)
    LATEX VERSION: For sets, connectivity is preserved by surjective mappings. **)
theorem Theorem_GT_1_8:
  assumes "is_topology_on X TX" "is_topology_on Y TY"
  assumes "top1_continuous_map_on X TX Y TY f"
  assumes "M \<subseteq> X" "f ` M = N"
  assumes "top1_connected_on M (subspace_topology X TX M)"
  shows "top1_connected_on N (subspace_topology Y TY N)"
  by (metis Lemma_23_1 Theorem_23_5 assms(2,3,4,5,6)
    top1_continuous_map_on_restrict_domain_simple)

(** from \<S>1 Theorem 9 (geotop.tex:375)
    LATEX VERSION: Every closed interval in R is connected. **)
theorem Theorem_GT_1_9:
  fixes a b :: real
  assumes "a \<le> b"
  shows "top1_connected_on {t. a \<le> t \<and> t \<le> b}
           (subspace_topology UNIV geotop_euclidean_topology {t. a \<le> t \<and> t \<le> b})"
  (** Moise proof (geotop.tex:373): the closed interval is connected. In our setup,
      we reduce via the bridge geotop_euclidean_topology = top1_open_sets to
      Top0's subspace-open characterization, which then reduces to
      HOL-Analysis's \<open>connected_Icc\<close>. **)
proof -
  have heq: "{t::real. a \<le> t \<and> t \<le> b} = {a..b}" by (by100 auto)
  have hconn: "connected {t::real. a \<le> t \<and> t \<le> b}"
    unfolding heq by (rule connected_Icc)
  have hbridge: "(geotop_euclidean_topology :: real set set) = top1_open_sets"
    by (rule geotop_euclidean_topology_eq_open_sets)
  show ?thesis
    unfolding hbridge
    using hconn top1_connected_on_subspace_openI by blast
qed

(** from \<S>1 Theorem 10 (geotop.tex:384)
    LATEX VERSION: If H and K are separated, then every connected subset M of H \<union> K lies
      either in H or in K. **)
theorem Theorem_GT_1_10:
  assumes hTX: "is_topology_on X T"
  assumes hsepHK: "geotop_separated X T H K"
  assumes hMHK: "M \<subseteq> H \<union> K"
  assumes hMconn: "top1_connected_on M (subspace_topology X T M)"
  shows "M \<subseteq> H \<or> M \<subseteq> K"
proof (rule ccontr)
  assume hcc: "\<not>(M \<subseteq> H \<or> M \<subseteq> K)"
  have hHX: "H \<subseteq> X" using hsepHK unfolding geotop_separated_def by simp
  have hKX: "K \<subseteq> X" using hsepHK unfolding geotop_separated_def by simp
  have hclHK: "closure_on X T H \<inter> K = {}"
    using hsepHK unfolding geotop_separated_def by simp
  have hHclK: "H \<inter> closure_on X T K = {}"
    using hsepHK unfolding geotop_separated_def by simp
  have hMX: "M \<subseteq> X" using hMHK hHX hKX by fast
  have hMHK_union: "M = (M \<inter> H) \<union> (M \<inter> K)" using hMHK by fast
  have hMHne: "M \<inter> H \<noteq> {}" using hcc hMHK_union by fast
  have hMKne: "M \<inter> K \<noteq> {}" using hcc hMHK_union by fast
  have hcl_MH: "closure_on X T (M \<inter> H) \<subseteq> closure_on X T H"
    by (rule closure_on_mono) fast
  have hcl_MK: "closure_on X T (M \<inter> K) \<subseteq> closure_on X T K"
    by (rule closure_on_mono) fast
  have hint1: "closure_on X T (M \<inter> H) \<inter> (M \<inter> K) = {}"
    using hcl_MH hclHK by fast
  have hint2: "(M \<inter> H) \<inter> closure_on X T (M \<inter> K) = {}"
    using hcl_MK hHclK by fast
  have hMH_X: "M \<inter> H \<subseteq> X" using hHX by fast
  have hMK_X: "M \<inter> K \<subseteq> X" using hKX by fast
  have hsep: "geotop_separated X T (M \<inter> H) (M \<inter> K)"
    unfolding geotop_separated_def
    using hMH_X hMK_X hint1 hint2 by simp
  have hconn_iff: "top1_connected_on M (subspace_topology X T M) \<longleftrightarrow>
    \<not>(\<exists>H' K'. H' \<noteq> {} \<and> K' \<noteq> {} \<and> M = H' \<union> K' \<and> geotop_separated X T H' K')"
    by (rule Theorem_GT_1_6[OF hTX hMX])
  have "\<exists>H' K'. H' \<noteq> {} \<and> K' \<noteq> {} \<and> M = H' \<union> K' \<and> geotop_separated X T H' K'"
    apply (rule exI[of _ "M \<inter> H"])
    apply (rule exI[of _ "M \<inter> K"])
    using hMHne hMKne hMHK_union hsep by simp
  thus False
    using hconn_iff hMconn by simp
qed

(** from \<S>1 Theorem 11 (geotop.tex:388)
    LATEX VERSION: Every pathwise connected set is connected. **)
theorem Theorem_GT_1_11:
  assumes hTX: "is_topology_on X T"
  assumes hMX: "M \<subseteq> X"
  assumes hMpc: "top1_path_connected_on M (subspace_topology X T M)"
  shows "top1_connected_on M (subspace_topology X T M)"
  (** Moise proof (geotop.tex:388): suppose not, M = H \<union> K (separated, nonempty).
      Take P\<in>H, Q\<in>K, path f from P to Q in M. Image f(UI) connected (Theorem_23_5
      + top1_unit_interval_connected). By Theorem 1.10 image lies in H or K,
      contradicting P = f(0) \<in> H and Q = f(1) \<in> K. **)
proof (rule ccontr)
  assume hnc: "\<not> top1_connected_on M (subspace_topology X T M)"
  have hconn_iff: "top1_connected_on M (subspace_topology X T M) \<longleftrightarrow>
    \<not>(\<exists>H K. H \<noteq> {} \<and> K \<noteq> {} \<and> M = H \<union> K \<and> geotop_separated X T H K)"
    by (rule Theorem_GT_1_6[OF hTX hMX])
  from hnc hconn_iff
  have hsep_ex: "\<exists>H K. H \<noteq> {} \<and> K \<noteq> {} \<and> M = H \<union> K \<and> geotop_separated X T H K"
    by blast
  then obtain H K where hHne: "H \<noteq> {}" and hKne: "K \<noteq> {}"
        and hMHK: "M = H \<union> K" and hsep: "geotop_separated X T H K" by blast
  from hHne obtain P where hPH: "P \<in> H" by blast
  from hKne obtain Q where hQK: "Q \<in> K" by blast
  have hPM: "P \<in> M" using hPH hMHK by fast
  have hQM: "Q \<in> M" using hQK hMHK by fast
  have hpath_ex: "\<exists>f. top1_is_path_on M (subspace_topology X T M) P Q f"
    using hMpc hPM hQM unfolding top1_path_connected_on_def by blast
  then obtain f where hf: "top1_is_path_on M (subspace_topology X T M) P Q f" by blast
  have hfcont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  M (subspace_topology X T M) f"
    using hf unfolding top1_is_path_on_def by simp
  have hf0: "f 0 = P" using hf unfolding top1_is_path_on_def by simp
  have hf1: "f 1 = Q" using hf unfolding top1_is_path_on_def by simp
  have hTUI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTM: "is_topology_on M (subspace_topology X T M)"
    by (rule subspace_topology_is_topology_on[OF hTX hMX])
  have hUIconn: "top1_connected_on top1_unit_interval top1_unit_interval_topology"
    by (rule top1_unit_interval_connected)
  have hImg_conn_M: "top1_connected_on (f ` top1_unit_interval)
      (subspace_topology M (subspace_topology X T M) (f ` top1_unit_interval))"
    by (rule Theorem_23_5[OF hTUI hTM hUIconn hfcont])
  (** Image is subset of M. **)
  have hImg_sub_M: "f ` top1_unit_interval \<subseteq> M"
    using hfcont unfolding top1_continuous_map_on_def by blast
  have hImg_sub_X: "f ` top1_unit_interval \<subseteq> X" using hImg_sub_M hMX by fast
  (** Subspace topology transitivity: subspace M (subspace X T M) (f`UI) = subspace X T (f`UI). **)
  have hsub_trans: "subspace_topology M (subspace_topology X T M) (f ` top1_unit_interval)
                 = subspace_topology X T (f ` top1_unit_interval)"
    by (rule subspace_topology_trans[OF hImg_sub_M])
  have hImg_conn: "top1_connected_on (f ` top1_unit_interval)
      (subspace_topology X T (f ` top1_unit_interval))"
    using hImg_conn_M hsub_trans by simp
  (** Apply Theorem 1.10: image ⊆ H ∪ K, image connected, image ⊆ H or ⊆ K. **)
  have hImg_sub_HK: "f ` top1_unit_interval \<subseteq> H \<union> K"
    using hImg_sub_M hMHK by simp
  have hImg_HK: "f ` top1_unit_interval \<subseteq> H \<or> f ` top1_unit_interval \<subseteq> K"
    by (rule Theorem_GT_1_10[OF hTX hsep hImg_sub_HK hImg_conn])
  have hP_img: "P \<in> f ` top1_unit_interval"
    using hf0 unfolding top1_unit_interval_def by auto
  have hQ_img: "Q \<in> f ` top1_unit_interval"
    using hf1 unfolding top1_unit_interval_def by auto
  have hHX_geo: "H \<subseteq> X" using hsep unfolding geotop_separated_def by simp
  have hclHK_geo: "closure_on X T H \<inter> K = {}" using hsep unfolding geotop_separated_def by simp
  have hH_clH: "H \<subseteq> closure_on X T H" by (rule subset_closure_on)
  have hHKdisj: "H \<inter> K = {}" using hH_clH hclHK_geo by fast
  from hImg_HK show False
  proof
    assume "f ` top1_unit_interval \<subseteq> H"
    hence "Q \<in> H" using hQ_img by fast
    thus False using hQK hHKdisj by fast
  next
    assume "f ` top1_unit_interval \<subseteq> K"
    hence "P \<in> K" using hP_img by fast
    thus False using hPH hHKdisj by fast
  qed
qed

(** from \<S>1 Theorem 12 (geotop.tex:391)
    LATEX VERSION: Let K be a complex. TFAE: (1) K is connected; (2) |K| is pathwise connected;
      (3) |K| is connected. **)
theorem Theorem_GT_1_12:
  fixes K :: "'a::euclidean_space set set"
  assumes hK_complex: "geotop_is_complex K"
  shows "geotop_complex_connected K \<longleftrightarrow>
    top1_path_connected_on (geotop_polyhedron K)
        (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
    and "top1_path_connected_on (geotop_polyhedron K)
           (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) \<longleftrightarrow>
         top1_connected_on (geotop_polyhedron K)
           (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
proof -
  (** (1) K connected (combinatorial sense: adjacency graph of simplexes connected)
         implies |K| path-connected: for any two points P, Q \<in> |K|, join them by a chain
         of simplexes. Within each simplex, any two points are joined by a linear segment
         (simplexes are convex). **)
  have h_comb_to_path:
    "geotop_complex_connected K \<longrightarrow>
       top1_path_connected_on (geotop_polyhedron K)
          (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
    using Theorem_GT_1_4 by (by100 blast)
  (** (2) Path-connected \<Rightarrow> connected: standard result (continuous image of [0, 1]
         connected, hence |K| cannot be split into two non-empty open pieces). **)
  have h_path_to_conn:
    "top1_path_connected_on (geotop_polyhedron K)
        (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) \<longrightarrow>
     top1_connected_on (geotop_polyhedron K)
        (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
    by (rule impI, erule top1_path_connected_on_geotop_imp_connected)
  (** (3) Connected \<Rightarrow> combinatorially connected: if the adjacency graph were disconnected,
         partition K into (K_1, K_2) such that no vertex is shared; then |K| = |K_1| \<cup> |K_2|
         would be a disconnection of |K|. **)
  have h_conn_to_comb:
    "top1_connected_on (geotop_polyhedron K)
        (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) \<longrightarrow>
     geotop_complex_connected K"
  proof (rule impI, rule ccontr)
    assume hconn: "top1_connected_on (geotop_polyhedron K)
                      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
    assume hnotcc: "\<not> geotop_complex_connected K"
    have hex_split: "\<exists>K1 K2. K1 \<noteq> {} \<and> K2 \<noteq> {} \<and> K1 \<inter> K2 = {} \<and> K = K1 \<union> K2
                              \<and> geotop_is_complex K1 \<and> geotop_is_complex K2"
      using hnotcc hK_complex unfolding geotop_complex_connected_def by (by100 blast)
    define K1 where "K1 = (SOME K1. \<exists>K2. K1 \<noteq> {} \<and> K2 \<noteq> {} \<and> K1 \<inter> K2 = {} \<and> K = K1 \<union> K2
                              \<and> geotop_is_complex K1 \<and> geotop_is_complex K2)"
    define K2 where "K2 = (SOME K2. K1 \<noteq> {} \<and> K2 \<noteq> {} \<and> K1 \<inter> K2 = {} \<and> K = K1 \<union> K2
                              \<and> geotop_is_complex K1 \<and> geotop_is_complex K2)"
    have hK1_all: "\<exists>K2. K1 \<noteq> {} \<and> K2 \<noteq> {} \<and> K1 \<inter> K2 = {} \<and> K = K1 \<union> K2
                        \<and> geotop_is_complex K1 \<and> geotop_is_complex K2"
      unfolding K1_def using hex_split someI_ex[of "\<lambda>K1'. \<exists>K2'. K1' \<noteq> {} \<and> K2' \<noteq> {} \<and> K1' \<inter> K2' = {} \<and> K = K1' \<union> K2' \<and> geotop_is_complex K1' \<and> geotop_is_complex K2'"]
      by (by100 blast)
    have hK2_all: "K1 \<noteq> {} \<and> K2 \<noteq> {} \<and> K1 \<inter> K2 = {} \<and> K = K1 \<union> K2
                      \<and> geotop_is_complex K1 \<and> geotop_is_complex K2"
      unfolding K2_def using hK1_all someI_ex[of "\<lambda>K2'. K1 \<noteq> {} \<and> K2' \<noteq> {} \<and> K1 \<inter> K2' = {} \<and> K = K1 \<union> K2' \<and> geotop_is_complex K1 \<and> geotop_is_complex K2'"]
      by (by100 blast)
    have hK1ne: "K1 \<noteq> {}" using hK2_all by (by100 blast)
    have hK2ne: "K2 \<noteq> {}" using hK2_all by (by100 blast)
    have hdisj: "K1 \<inter> K2 = {}" using hK2_all by (by100 blast)
    have hKu: "K = K1 \<union> K2" using hK2_all by (by100 blast)
    have hK1: "geotop_is_complex K1" using hK2_all by (by100 blast)
    have hK2: "geotop_is_complex K2" using hK2_all by (by100 blast)
    have hK1sub: "K1 \<subseteq> K" using hKu by (by100 blast)
    have hK2sub: "K2 \<subseteq> K" using hKu by (by100 blast)
    (** |K| = |K1| \<union> |K2|, and |K1| \<inter> |K2| = {}. **)
    have hpoly_K: "geotop_polyhedron K = geotop_polyhedron K1 \<union> geotop_polyhedron K2"
      unfolding geotop_polyhedron_def using hKu by (by100 blast)
    have hpoly_disj: "geotop_polyhedron K1 \<inter> geotop_polyhedron K2 = {}"
      by (rule geotop_disjoint_subcomplex_polyhedra_disjoint
                [OF hK_complex hK1 hK1sub hK2 hK2sub hdisj])
    have hK1ne_poly: "geotop_polyhedron K1 \<noteq> {}"
    proof -
      obtain \<sigma> where "\<sigma> \<in> K1" using hK1ne by (by100 blast)
      moreover have "\<sigma> \<noteq> {}"
        using \<open>\<sigma> \<in> K1\<close> geotop_is_complex_simplex[OF hK1] geotop_is_simplex_nonempty
        by (by100 blast)
      ultimately show ?thesis unfolding geotop_polyhedron_def by (by100 blast)
    qed
    have hK2ne_poly: "geotop_polyhedron K2 \<noteq> {}"
    proof -
      obtain \<tau> where "\<tau> \<in> K2" using hK2ne by (by100 blast)
      moreover have "\<tau> \<noteq> {}"
        using \<open>\<tau> \<in> K2\<close> geotop_is_complex_simplex[OF hK2] geotop_is_simplex_nonempty
        by (by100 blast)
      ultimately show ?thesis unfolding geotop_polyhedron_def by (by100 blast)
    qed
    (** Key claim: |K1|, |K2| are both open in |K| (subspace topology).
        Proof: for P \<in> |K1|, avoidance lemma gives ball P \<epsilon> \<inter> |K2| = {}. **)
    have hK1_open: "\<exists>V\<in>geotop_euclidean_topology.
                     geotop_polyhedron K \<inter> V = geotop_polyhedron K1"
    proof -
      let ?V = "\<Union>P\<in>geotop_polyhedron K1. {Q. \<exists>\<epsilon>>0. ball P \<epsilon> \<inter> geotop_polyhedron K2 = {} \<and> Q \<in> ball P \<epsilon>}"
      (** This is getting complex. Let me simplify: show |K1| is a union of open balls each
         avoiding |K2|. Equivalently, for each P \<in> |K1|, \<exists>\<epsilon> with B(P, \<epsilon>) \<inter> |K2| = {}. **)
      have hwit: "\<forall>P\<in>geotop_polyhedron K1. \<exists>\<epsilon>>0. ball P \<epsilon> \<inter> geotop_polyhedron K2 = {}"
      proof
        fix P assume hP: "P \<in> geotop_polyhedron K1"
        obtain \<sigma> where h\<sigma>K1: "\<sigma> \<in> K1" and hP\<sigma>: "P \<in> \<sigma>"
          using hP unfolding geotop_polyhedron_def by (by100 blast)
        have h\<sigma>K: "\<sigma> \<in> K" using h\<sigma>K1 hK1sub by (by100 blast)
        obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" and h\<epsilon>avoid:
            "ball P \<epsilon> \<inter> \<Union>{\<tau>\<in>K. P \<notin> \<tau>} = {}"
          using geotop_complex_point_avoidance[OF hK_complex h\<sigma>K hP\<sigma>] by (by100 blast)
        have hP_notin_K2: "\<forall>\<tau>\<in>K2. P \<notin> \<tau>"
        proof (intro ballI)
          fix \<tau> assume h\<tau>K2: "\<tau> \<in> K2"
          show "P \<notin> \<tau>"
          proof (rule ccontr)
            assume "\<not> P \<notin> \<tau>"
            then have hP\<tau>: "P \<in> \<tau>" by (by100 simp)
            have "P \<in> geotop_polyhedron K2"
              unfolding geotop_polyhedron_def using h\<tau>K2 hP\<tau> by (by100 blast)
            then show False using hP hpoly_disj by (by100 blast)
          qed
        qed
        have hK2_sub_avoid: "geotop_polyhedron K2 \<subseteq> \<Union>{\<tau>\<in>K. P \<notin> \<tau>}"
        proof
          fix x assume "x \<in> geotop_polyhedron K2"
          then obtain \<tau> where h\<tau>: "\<tau> \<in> K2" and hx: "x \<in> \<tau>"
            unfolding geotop_polyhedron_def by (by100 blast)
          have h\<tau>K: "\<tau> \<in> K" using h\<tau> hK2sub by (by100 blast)
          have "P \<notin> \<tau>" using h\<tau> hP_notin_K2 by (by100 blast)
          then show "x \<in> \<Union>{\<tau>\<in>K. P \<notin> \<tau>}" using h\<tau>K hx by (by100 blast)
        qed
        have "ball P \<epsilon> \<inter> geotop_polyhedron K2 = {}"
          using h\<epsilon>avoid hK2_sub_avoid by (by100 blast)
        then show "\<exists>\<epsilon>>0. ball P \<epsilon> \<inter> geotop_polyhedron K2 = {}"
          using h\<epsilon> by (by100 blast)
      qed
      (** From pointwise witnesses, construct the open set V = union of balls. **)
      define V where "V = (\<Union>P\<in>geotop_polyhedron K1. \<Union>{ball P \<epsilon> |\<epsilon>. \<epsilon> > 0 \<and> ball P \<epsilon> \<inter> geotop_polyhedron K2 = {}})"
      have hVopen: "open V"
        unfolding V_def by (by100 auto)
      have hVgeo: "V \<in> geotop_euclidean_topology"
        using hVopen
        unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
        by (by100 simp)
      have hK1_in_V: "geotop_polyhedron K1 \<subseteq> V"
      proof
        fix P assume hP: "P \<in> geotop_polyhedron K1"
        obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" and h\<epsilon>avoid: "ball P \<epsilon> \<inter> geotop_polyhedron K2 = {}"
          using hwit hP by (by100 blast)
        have hP_in_ball: "P \<in> ball P \<epsilon>" using h\<epsilon> by (by100 simp)
        let ?BP = "{ball P \<epsilon>' |\<epsilon>'. \<epsilon>' > 0 \<and> ball P \<epsilon>' \<inter> geotop_polyhedron K2 = {}}"
        have hBin: "ball P \<epsilon> \<in> ?BP" using h\<epsilon> h\<epsilon>avoid by (by100 blast)
        have hPinUnion: "P \<in> \<Union>?BP" using hBin hP_in_ball by (by100 blast)
        show "P \<in> V" unfolding V_def using hP hPinUnion by (by100 blast)
      qed
      have hV_avoids_K2: "V \<inter> geotop_polyhedron K2 = {}"
        unfolding V_def by (by100 blast)
      have hPK_cap_V: "geotop_polyhedron K \<inter> V = geotop_polyhedron K1"
      proof (rule set_eqI, rule iffI)
        fix x assume hx: "x \<in> geotop_polyhedron K \<inter> V"
        then have hxK: "x \<in> geotop_polyhedron K" and hxV: "x \<in> V" by (by100 auto)
        have "x \<in> geotop_polyhedron K1 \<or> x \<in> geotop_polyhedron K2"
          using hxK hpoly_K by (by100 blast)
        moreover have "x \<notin> geotop_polyhedron K2" using hxV hV_avoids_K2 by (by100 blast)
        ultimately show "x \<in> geotop_polyhedron K1" by (by100 blast)
      next
        fix x assume "x \<in> geotop_polyhedron K1"
        then have hxK1: "x \<in> geotop_polyhedron K1" by (by100 blast)
        have hxK: "x \<in> geotop_polyhedron K" using hxK1 hpoly_K by (by100 blast)
        have hxV: "x \<in> V" using hxK1 hK1_in_V by (by100 blast)
        show "x \<in> geotop_polyhedron K \<inter> V" using hxK hxV by (by100 blast)
      qed
      show ?thesis using hVgeo hPK_cap_V by (by100 blast)
    qed
    have hK1_subsp: "geotop_polyhedron K1 \<in>
        subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
      using hK1_open unfolding subspace_topology_def by (by100 blast)
    (** By symmetric argument, |K2| is also open in the subspace. **)
    have hK2_open: "\<exists>V\<in>geotop_euclidean_topology.
                     geotop_polyhedron K \<inter> V = geotop_polyhedron K2"
    proof -
      have hwit: "\<forall>P\<in>geotop_polyhedron K2. \<exists>\<epsilon>>0. ball P \<epsilon> \<inter> geotop_polyhedron K1 = {}"
      proof
        fix P assume hP: "P \<in> geotop_polyhedron K2"
        obtain \<sigma> where h\<sigma>K2: "\<sigma> \<in> K2" and hP\<sigma>: "P \<in> \<sigma>"
          using hP unfolding geotop_polyhedron_def by (by100 blast)
        have h\<sigma>K: "\<sigma> \<in> K" using h\<sigma>K2 hK2sub by (by100 blast)
        obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" and h\<epsilon>avoid:
            "ball P \<epsilon> \<inter> \<Union>{\<tau>\<in>K. P \<notin> \<tau>} = {}"
          using geotop_complex_point_avoidance[OF hK_complex h\<sigma>K hP\<sigma>] by (by100 blast)
        have hP_notin_K1: "\<forall>\<tau>\<in>K1. P \<notin> \<tau>"
        proof (intro ballI)
          fix \<tau> assume h\<tau>K1: "\<tau> \<in> K1"
          show "P \<notin> \<tau>"
          proof (rule ccontr)
            assume "\<not> P \<notin> \<tau>"
            then have hP\<tau>: "P \<in> \<tau>" by (by100 simp)
            have "P \<in> geotop_polyhedron K1"
              unfolding geotop_polyhedron_def using h\<tau>K1 hP\<tau> by (by100 blast)
            then show False using hP hpoly_disj by (by100 blast)
          qed
        qed
        have hK1_sub_avoid: "geotop_polyhedron K1 \<subseteq> \<Union>{\<tau>\<in>K. P \<notin> \<tau>}"
        proof
          fix x assume "x \<in> geotop_polyhedron K1"
          then obtain \<tau> where h\<tau>: "\<tau> \<in> K1" and hx: "x \<in> \<tau>"
            unfolding geotop_polyhedron_def by (by100 blast)
          have h\<tau>K: "\<tau> \<in> K" using h\<tau> hK1sub by (by100 blast)
          have "P \<notin> \<tau>" using h\<tau> hP_notin_K1 by (by100 blast)
          then show "x \<in> \<Union>{\<tau>\<in>K. P \<notin> \<tau>}" using h\<tau>K hx by (by100 blast)
        qed
        have "ball P \<epsilon> \<inter> geotop_polyhedron K1 = {}"
          using h\<epsilon>avoid hK1_sub_avoid by (by100 blast)
        then show "\<exists>\<epsilon>>0. ball P \<epsilon> \<inter> geotop_polyhedron K1 = {}"
          using h\<epsilon> by (by100 blast)
      qed
      define V where "V = (\<Union>P\<in>geotop_polyhedron K2. \<Union>{ball P \<epsilon> |\<epsilon>. \<epsilon> > 0 \<and> ball P \<epsilon> \<inter> geotop_polyhedron K1 = {}})"
      have hVopen: "open V"
        unfolding V_def by (by100 auto)
      have hVgeo: "V \<in> geotop_euclidean_topology"
        using hVopen
        unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
        by (by100 simp)
      have hK2_in_V: "geotop_polyhedron K2 \<subseteq> V"
      proof
        fix P assume hP: "P \<in> geotop_polyhedron K2"
        obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" and h\<epsilon>avoid: "ball P \<epsilon> \<inter> geotop_polyhedron K1 = {}"
          using hwit hP by (by100 blast)
        have hP_in_ball: "P \<in> ball P \<epsilon>" using h\<epsilon> by (by100 simp)
        let ?BP = "{ball P \<epsilon>' |\<epsilon>'. \<epsilon>' > 0 \<and> ball P \<epsilon>' \<inter> geotop_polyhedron K1 = {}}"
        have hBin: "ball P \<epsilon> \<in> ?BP" using h\<epsilon> h\<epsilon>avoid by (by100 blast)
        have hPinUnion: "P \<in> \<Union>?BP" using hBin hP_in_ball by (by100 blast)
        show "P \<in> V" unfolding V_def using hP hPinUnion by (by100 blast)
      qed
      have hV_avoids_K1: "V \<inter> geotop_polyhedron K1 = {}"
        unfolding V_def by (by100 blast)
      have hPK_cap_V: "geotop_polyhedron K \<inter> V = geotop_polyhedron K2"
      proof (rule set_eqI, rule iffI)
        fix x assume hx: "x \<in> geotop_polyhedron K \<inter> V"
        then have hxK: "x \<in> geotop_polyhedron K" and hxV: "x \<in> V" by (by100 auto)
        have "x \<in> geotop_polyhedron K1 \<or> x \<in> geotop_polyhedron K2"
          using hxK hpoly_K by (by100 blast)
        moreover have "x \<notin> geotop_polyhedron K1" using hxV hV_avoids_K1 by (by100 blast)
        ultimately show "x \<in> geotop_polyhedron K2" by (by100 blast)
      next
        fix x assume "x \<in> geotop_polyhedron K2"
        then have hxK2: "x \<in> geotop_polyhedron K2" by (by100 blast)
        have hxK: "x \<in> geotop_polyhedron K" using hxK2 hpoly_K by (by100 blast)
        have hxV: "x \<in> V" using hxK2 hK2_in_V by (by100 blast)
        show "x \<in> geotop_polyhedron K \<inter> V" using hxK hxV by (by100 blast)
      qed
      show ?thesis using hVgeo hPK_cap_V by (by100 blast)
    qed
    have hK2_subsp: "geotop_polyhedron K2 \<in>
        subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
      using hK2_open unfolding subspace_topology_def by (by100 blast)
    (** |K1| and |K2| form a separation of |K|, contradicting connectedness. **)
    have hsep:
      "geotop_polyhedron K1 \<in> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)
       \<and> geotop_polyhedron K2 \<in> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)
       \<and> geotop_polyhedron K1 \<noteq> {} \<and> geotop_polyhedron K2 \<noteq> {}
       \<and> geotop_polyhedron K1 \<inter> geotop_polyhedron K2 = {}
       \<and> geotop_polyhedron K1 \<union> geotop_polyhedron K2 = geotop_polyhedron K"
      using hK1_subsp hK2_subsp hK1ne_poly hK2ne_poly hpoly_disj hpoly_K
      by (by100 blast)
    then show False
      using hconn unfolding top1_connected_on_def by (by100 blast)
  qed
  show "geotop_complex_connected K \<longleftrightarrow>
        top1_path_connected_on (geotop_polyhedron K)
           (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
    using h_comb_to_path h_path_to_conn h_conn_to_comb by (by100 blast)
  show "top1_path_connected_on (geotop_polyhedron K)
           (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) \<longleftrightarrow>
        top1_connected_on (geotop_polyhedron K)
           (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
    using h_comb_to_path h_path_to_conn h_conn_to_comb by (by100 blast)
qed

(** from \<S>1: arc (geotop.tex:401)
    LATEX VERSION: An arc is a 1-cell. **)
text \<open>Already defined above as \<open>geotop_is_arc\<close>.\<close>

(** Predicate: complex K is at most 1-dimensional (every simplex is a
    0-simplex or 1-simplex). Moise's broken-line is faithfully 1-dim;
    any 2+-dim simplex would contradict the arc-homeomorphism anyway. **)
definition geotop_complex_is_1dim :: "'a::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_complex_is_1dim K \<longleftrightarrow>
    (\<forall>\<sigma>\<in>K. \<exists>n::nat. n \<le> 1 \<and> geotop_simplex_dim \<sigma> n)"

(** from \<S>1: broken line (geotop.tex:401)
    LATEX VERSION: A broken line is a polyhedral arc.
    Strengthened to require the witnessing complex to be 1-dimensional,
    faithful to Moise's intent (any 2+-dim simplex would contradict the
    arc property via invariance of domain; this strengthening makes the
    sub-complex constructions formally tractable). **)
definition geotop_is_broken_line :: "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_broken_line B \<longleftrightarrow>
    (\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = B
       \<and> geotop_complex_is_1dim K
       \<and> geotop_is_arc B (subspace_topology UNIV geotop_euclidean_topology B))"

(** Helper: a closed segment between two distinct points is a 1-simplex (and hence
    both an arc and a polyhedron; i.e., a broken line). **)
lemma geotop_closed_segment_is_simplex:
  fixes P Q :: "'a::real_normed_vector"
  assumes hne: "P \<noteq> Q"
  shows "geotop_simplex_dim (closed_segment P Q) 1"
  unfolding geotop_simplex_dim_def
proof (intro exI[of _ "{P, Q}"] exI[of _ "1::nat"] conjI)
  show "finite {P, Q}" by simp
  show "card {P, Q} = 1 + 1" using hne by simp
  show "(1::nat) \<le> 1" by simp
  show "geotop_general_position {P, Q} 1"
    unfolding geotop_general_position_def
  proof (intro allI impI)
    fix H :: "'a set" and k :: nat
    assume hassm: "geotop_hyperplane_dim H k \<and> k < 1"
    then have hk: "k = 0" by simp
    have hhyp: "geotop_hyperplane_dim H 0" using hassm hk by simp
    (** 0-dim hyperplane is a singleton. **)
    have hH_sing: "\<exists>v0. H = {v0}"
    proof -
      obtain V v0 B where hV: "subspace V"
                      and hB: "independent B" "finite B" "card B = 0" "span B = V"
                      and hH': "H = (\<lambda>v. v + v0) ` V"
        using hhyp unfolding geotop_hyperplane_dim_def by blast
      have hBempty: "B = {}" using hB(2) hB(3) by simp
      have hVzero: "V = {0}" using hBempty hB(4) by simp
      have "H = {0 + v0}" using hH' hVzero by simp
      thus ?thesis by blast
    qed
    then obtain v0 where hH_eq: "H = {v0}" by blast
    have hinter: "{P, Q} \<inter> H \<subseteq> {v0}" using hH_eq by blast
    have h1: "finite ({P, Q} \<inter> H)" using hinter by (meson finite.emptyI finite.insertI finite_subset)
    have h2: "card ({P, Q} \<inter> H) \<le> 1"
      using hinter card_mono[of "{v0}"] by (simp)
    show "finite ({P, Q} \<inter> H) \<and> card ({P, Q} \<inter> H) \<le> k + 1"
      using h1 h2 hk by simp
  qed
  show "closed_segment P Q = geotop_convex_hull {P, Q}"
    by (simp add: geotop_convex_hull_eq_HOL segment_convex_hull)
qed

(** Helper: a closed segment between distinct points is an arc. **)
lemma geotop_closed_segment_is_arc:
  fixes P Q :: "'a::real_normed_vector"
  assumes hne: "P \<noteq> Q"
  shows "geotop_is_arc (closed_segment P Q)
           (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q))"
proof -
  have hTeucl: "is_topology_on (UNIV::'a set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have hTsub: "is_topology_on (closed_segment P Q)
                 (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q))"
    by (rule subspace_topology_is_topology_on[OF hTeucl subset_UNIV])
  have hsimplex: "geotop_simplex_dim (closed_segment P Q) 1"
    by (rule geotop_closed_segment_is_simplex[OF hne])
  have hcont_id: "top1_continuous_map_on (closed_segment P Q)
                    (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q))
                    (closed_segment P Q)
                    (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q)) id"
    by (rule top1_continuous_map_on_id[OF hTsub])
  have hinv_id: "\<forall>x\<in>closed_segment P Q. inv_into (closed_segment P Q) id x = id x"
  proof
    fix x assume "x \<in> closed_segment P Q"
    thus "inv_into (closed_segment P Q) id x = id x"
      by (metis inj_on_id inv_into_f_f id_apply)
  qed
  have hcont_inv: "top1_continuous_map_on (closed_segment P Q)
                    (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q))
                    (closed_segment P Q)
                    (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q))
                    (inv_into (closed_segment P Q) id)"
    using hcont_id top1_continuous_map_on_cong[OF hinv_id] by blast
  have hbij: "bij_betw id (closed_segment P Q) (closed_segment P Q)" by simp
  have hhomeo: "top1_homeomorphism_on (closed_segment P Q)
                  (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q))
                  (closed_segment P Q)
                  (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q)) id"
    unfolding top1_homeomorphism_on_def
    using hTsub hbij hcont_id hcont_inv by blast
  (** Package into the n_cell existential form. **)
  have hncell: "geotop_is_n_cell (closed_segment P Q)
                  (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q)) 1"
    unfolding geotop_is_n_cell_def
    apply (rule conjI[OF hTsub])
    apply (rule exI[where x = "closed_segment P Q"])
    apply (rule exI[where x = "id :: 'a \<Rightarrow> 'a"])
    apply (rule conjI[OF hsimplex])
    apply (rule hhomeo)
    done
  show ?thesis unfolding geotop_is_arc_def using hncell .
qed

(** Helper: the singleton {P} is a 0-simplex. **)
lemma geotop_singleton_is_simplex:
  fixes P :: "'a::real_normed_vector"
  shows "geotop_simplex_dim {P} 0"
  unfolding geotop_simplex_dim_def
proof (intro exI[of _ "{P}"] exI[of _ "0::nat"] conjI)
  show "finite {P}" by simp
  show "card {P} = 0 + 1" by simp
  show "(0::nat) \<le> 0" by simp
  show "geotop_general_position {P} 0"
    unfolding geotop_general_position_def by simp
  show "{P} = geotop_convex_hull {P}"
    by (simp add: geotop_convex_hull_eq_HOL)
qed

(** The closed segment [P, Q] between distinct points in a Euclidean space is a
    broken line. Witness complex: K = {{P}, {Q}, closed_segment P Q}. **)
lemma geotop_closed_segment_is_broken_line:
  fixes P Q :: "'a::euclidean_space"
  assumes hne: "P \<noteq> Q"
  shows "geotop_is_broken_line (closed_segment P Q)"
proof -
  define K :: "'a set set" where "K = {{P}, {Q}, closed_segment P Q}"
  (** Element-wise simplicity. **)
  have hP_simp: "geotop_is_simplex {P}"
    using geotop_singleton_is_simplex[of P]
    unfolding geotop_is_simplex_def geotop_simplex_dim_def by blast
  have hQ_simp: "geotop_is_simplex {Q}"
    using geotop_singleton_is_simplex[of Q]
    unfolding geotop_is_simplex_def geotop_simplex_dim_def by blast
  have hS_simp: "geotop_is_simplex (closed_segment P Q)"
    using geotop_closed_segment_is_simplex[OF hne]
    unfolding geotop_is_simplex_def geotop_simplex_dim_def by blast
  have hK_simplexes: "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
    unfolding K_def using hP_simp hQ_simp hS_simp by blast
  (** K is closed under faces. **)
  have hK_faces: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
  proof (intro ballI allI impI)
    fix \<sigma> \<tau> assume h\<sigma>K: "\<sigma> \<in> K" and h\<tau>face: "geotop_is_face \<tau> \<sigma>"
    from h\<tau>face obtain V W where hSV: "geotop_simplex_vertices \<sigma> V"
                            and hWne: "W \<noteq> {}" and hWsub: "W \<subseteq> V"
                            and h\<tau>eq: "\<tau> = geotop_convex_hull W"
      unfolding geotop_is_face_def by blast
    from h\<sigma>K consider (sP) "\<sigma> = {P}" | (sQ) "\<sigma> = {Q}" | (sS) "\<sigma> = closed_segment P Q"
      unfolding K_def by blast
    then show "\<tau> \<in> K"
    proof cases
      case sP
      have hV: "V = {P}"
        using hSV geotop_singleton_simplex_vertices sP by metis
      have hW: "W = {P}" using hV hWne hWsub by blast
      have "\<tau> = geotop_convex_hull {P}" using h\<tau>eq hW by simp
      also have "... = convex hull {P}" by (rule geotop_convex_hull_eq_HOL)
      also have "... = {P}" by simp
      finally have "\<tau> = {P}" .
      thus "\<tau> \<in> K" unfolding K_def by blast
    next
      case sQ
      have hV: "V = {Q}"
        using hSV geotop_singleton_simplex_vertices sQ by metis
      have hW: "W = {Q}" using hV hWne hWsub by blast
      have "\<tau> = geotop_convex_hull {Q}" using h\<tau>eq hW by simp
      also have "... = convex hull {Q}" by (rule geotop_convex_hull_eq_HOL)
      also have "... = {Q}" by simp
      finally have "\<tau> = {Q}" .
      thus "\<tau> \<in> K" unfolding K_def by blast
    next
      case sS
      have hV: "V = {P, Q}"
        using hSV geotop_segment_simplex_vertices[OF hne] sS by metis
      have hW_cases: "W \<in> {{P}, {Q}, {P, Q}}"
        using hV hWne hWsub by blast
      from hW_cases consider "W = {P}" | "W = {Q}" | "W = {P, Q}" by blast
      thus "\<tau> \<in> K"
      proof cases
        assume "W = {P}"
        then have "\<tau> = geotop_convex_hull {P}" using h\<tau>eq by simp
        also have "... = convex hull {P}" by (rule geotop_convex_hull_eq_HOL)
        also have "... = {P}" by simp
        finally have "\<tau> = {P}" .
        thus "\<tau> \<in> K" unfolding K_def by blast
      next
        assume "W = {Q}"
        then have "\<tau> = geotop_convex_hull {Q}" using h\<tau>eq by simp
        also have "... = convex hull {Q}" by (rule geotop_convex_hull_eq_HOL)
        also have "... = {Q}" by simp
        finally have "\<tau> = {Q}" .
        thus "\<tau> \<in> K" unfolding K_def by blast
      next
        assume hW_PQ: "W = {P, Q}"
        have "\<tau> = geotop_convex_hull {P, Q}" using h\<tau>eq hW_PQ by simp
        also have "... = convex hull {P, Q}" by (rule geotop_convex_hull_eq_HOL)
        also have "... = closed_segment P Q" by (simp add: segment_convex_hull)
        finally have "\<tau> = closed_segment P Q" .
        thus "\<tau> \<in> K" unfolding K_def by blast
      qed
    qed
  qed
  (** Intersection property. **)
  (** Package the three segment vertex witnesses for face-of-subset lookups. **)
  have hSV_P: "geotop_simplex_vertices {P} {P}"
    unfolding geotop_simplex_vertices_def
    apply (rule exI[of _ "0::nat"], rule exI[of _ "0::nat"])
    apply (intro conjI)
    apply simp
    apply simp
    apply simp
    apply (simp add: geotop_general_position_def)
    apply (simp add: geotop_convex_hull_eq_HOL)
    done
  have hSV_Q: "geotop_simplex_vertices {Q} {Q}"
    unfolding geotop_simplex_vertices_def
    apply (rule exI[of _ "0::nat"], rule exI[of _ "0::nat"])
    apply (intro conjI)
    apply simp
    apply simp
    apply simp
    apply (simp add: geotop_general_position_def)
    apply (simp add: geotop_convex_hull_eq_HOL)
    done
  have hSV_S: "geotop_simplex_vertices (closed_segment P Q) {P, Q}"
  proof -
    have hsimp_dim: "geotop_simplex_dim (closed_segment P Q) 1"
      by (rule geotop_closed_segment_is_simplex[OF hne])
    from hsimp_dim obtain V m where hV: "finite V" "card V = 1 + 1" "1 \<le> m"
                                "geotop_general_position V m"
                                "closed_segment P Q = geotop_convex_hull V"
      unfolding geotop_simplex_dim_def by blast
    have hSV_V: "geotop_simplex_vertices (closed_segment P Q) V"
      unfolding geotop_simplex_vertices_def
      using hV by blast
    have hVPQ: "V = {P, Q}"
      using geotop_segment_simplex_vertices[OF hne hSV_V] .
    show ?thesis using hSV_V hVPQ by simp
  qed
  (** Face-of-\<sigma> facts for each element of K, to reuse in intersection cases. **)
  have hface_P_in_S: "geotop_is_face {P} (closed_segment P Q)"
  proof -
    have hhull_P: "geotop_convex_hull {P} = {P}"
      by (simp add: geotop_convex_hull_eq_HOL)
    have "geotop_is_face (geotop_convex_hull {P}) (closed_segment P Q)"
      by (rule geotop_is_face_of_subset[OF hSV_S]) auto
    thus ?thesis using hhull_P by simp
  qed
  have hface_Q_in_S: "geotop_is_face {Q} (closed_segment P Q)"
  proof -
    have hhull_Q: "geotop_convex_hull {Q} = {Q}"
      by (simp add: geotop_convex_hull_eq_HOL)
    have "geotop_is_face (geotop_convex_hull {Q}) (closed_segment P Q)"
      by (rule geotop_is_face_of_subset[OF hSV_S]) auto
    thus ?thesis using hhull_Q by simp
  qed
  have hface_P_in_P: "geotop_is_face {P} {P}"
    by (rule geotop_is_face_refl_of_simplex[OF hP_simp])
  have hface_Q_in_Q: "geotop_is_face {Q} {Q}"
    by (rule geotop_is_face_refl_of_simplex[OF hQ_simp])
  have hface_S_in_S: "geotop_is_face (closed_segment P Q) (closed_segment P Q)"
    by (rule geotop_is_face_refl_of_simplex[OF hS_simp])
  (** Compute the six nontrivial intersections. **)
  have hP_in_seg: "P \<in> closed_segment P Q" by simp
  have hQ_in_seg: "Q \<in> closed_segment P Q" by simp
  have hPsegQ: "{P} \<inter> {Q} = {}" using hne by simp
  have hPseg_inter: "{P} \<inter> closed_segment P Q = {P}" using hP_in_seg by blast
  have hQseg_inter: "{Q} \<inter> closed_segment P Q = {Q}" using hQ_in_seg by blast
  (** Now the intersection case analysis. **)
  have hK_inter: "\<forall>\<sigma>\<in>K. \<forall>\<tau>\<in>K. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                     geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
  proof (intro ballI impI)
    fix \<sigma> \<tau> assume h\<sigma>K: "\<sigma> \<in> K" and h\<tau>K: "\<tau> \<in> K" and hne_inter: "\<sigma> \<inter> \<tau> \<noteq> {}"
    from h\<sigma>K consider (sP) "\<sigma> = {P}" | (sQ) "\<sigma> = {Q}" | (sS) "\<sigma> = closed_segment P Q"
      unfolding K_def by blast
    then show "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    proof cases
      case sP
      from h\<tau>K consider "\<tau> = {P}" | "\<tau> = {Q}" | "\<tau> = closed_segment P Q"
        unfolding K_def by blast
      thus ?thesis
      proof cases
        assume "\<tau> = {P}"
        then show ?thesis using sP hface_P_in_P by simp
      next
        assume "\<tau> = {Q}"
        then show ?thesis using sP hPsegQ hne_inter by simp
      next
        assume h\<tau>S: "\<tau> = closed_segment P Q"
        have hint: "\<sigma> \<inter> \<tau> = {P}" using sP h\<tau>S hPseg_inter by simp
        show ?thesis using hint sP h\<tau>S hface_P_in_P hface_P_in_S by simp
      qed
    next
      case sQ
      from h\<tau>K consider "\<tau> = {P}" | "\<tau> = {Q}" | "\<tau> = closed_segment P Q"
        unfolding K_def by blast
      thus ?thesis
      proof cases
        assume "\<tau> = {P}"
        then show ?thesis using sQ hPsegQ hne_inter by simp
      next
        assume "\<tau> = {Q}"
        then show ?thesis using sQ hface_Q_in_Q by simp
      next
        assume h\<tau>S: "\<tau> = closed_segment P Q"
        have hint: "\<sigma> \<inter> \<tau> = {Q}" using sQ h\<tau>S hQseg_inter by simp
        show ?thesis using hint sQ h\<tau>S hface_Q_in_Q hface_Q_in_S by simp
      qed
    next
      case sS
      from h\<tau>K consider "\<tau> = {P}" | "\<tau> = {Q}" | "\<tau> = closed_segment P Q"
        unfolding K_def by blast
      thus ?thesis
      proof cases
        assume h\<tau>P: "\<tau> = {P}"
        have hint: "\<sigma> \<inter> \<tau> = {P}" using sS h\<tau>P hPseg_inter by blast
        show ?thesis using hint sS h\<tau>P hface_P_in_S hface_P_in_P by simp
      next
        assume h\<tau>Q: "\<tau> = {Q}"
        have hint: "\<sigma> \<inter> \<tau> = {Q}" using sS h\<tau>Q hQseg_inter by blast
        show ?thesis using hint sS h\<tau>Q hface_Q_in_S hface_Q_in_Q by simp
      next
        assume h\<tau>S: "\<tau> = closed_segment P Q"
        show ?thesis using sS h\<tau>S hface_S_in_S by simp
      qed
    qed
  qed
  (** Neighborhood finiteness: take U = UNIV and note |K| is finite (3 elements). **)
  have hK_fin: "finite K" unfolding K_def by simp
  have hK_nbhd: "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
  proof
    fix \<sigma> assume "\<sigma> \<in> K"
    have hfin: "finite {\<tau>\<in>K. \<tau> \<inter> UNIV \<noteq> {}}"
      using hK_fin by simp
    have hopen: "open (UNIV::'a set)" by simp
    have hsub: "\<sigma> \<subseteq> UNIV" by simp
    show "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using hopen hsub hfin by blast
  qed
  (** Combine: K is a complex. **)
  have hK_complex: "geotop_is_complex K"
    unfolding geotop_is_complex_def using hK_simplexes hK_faces hK_inter hK_nbhd by blast
  (** |K| = closed_segment P Q (since P, Q \<in> closed_segment P Q). **)
  have hK_poly: "geotop_polyhedron K = closed_segment P Q"
  proof -
    have hunion: "\<Union>K = {P} \<union> {Q} \<union> closed_segment P Q"
      unfolding K_def by blast
    have hP_in: "P \<in> closed_segment P Q" by simp
    have hQ_in: "Q \<in> closed_segment P Q" by simp
    have hsing_sub_P: "{P} \<subseteq> closed_segment P Q" using hP_in by simp
    have hsing_sub_Q: "{Q} \<subseteq> closed_segment P Q" using hQ_in by simp
    have hunion_eq: "\<Union>K = closed_segment P Q"
      using hunion hsing_sub_P hsing_sub_Q by blast
    thus ?thesis unfolding geotop_polyhedron_def .
  qed
  (** Already proven: closed_segment is an arc. **)
  have harc: "geotop_is_arc (closed_segment P Q)
                (subspace_topology UNIV geotop_euclidean_topology (closed_segment P Q))"
    by (rule geotop_closed_segment_is_arc[OF hne])
  (** K is 1-dimensional: all three simplices are 0 or 1. **)
  have hK_1dim: "geotop_complex_is_1dim K"
    unfolding geotop_complex_is_1dim_def K_def
  proof (intro ballI)
    fix \<sigma> assume h\<sigma>K: "\<sigma> \<in> {{P}, {Q}, closed_segment P Q}"
    then consider (P_sing) "\<sigma> = {P}" | (Q_sing) "\<sigma> = {Q}" | (seg) "\<sigma> = closed_segment P Q"
      by blast
    thus "\<exists>n \<le> 1. geotop_simplex_dim \<sigma> n"
    proof cases
      case P_sing
      have "geotop_simplex_dim {P} 0" by (rule geotop_singleton_is_simplex)
      thus ?thesis unfolding P_sing by blast
    next
      case Q_sing
      have "geotop_simplex_dim {Q} 0" by (rule geotop_singleton_is_simplex)
      thus ?thesis unfolding Q_sing by blast
    next
      case seg
      have "geotop_simplex_dim (closed_segment P Q) 1"
        by (rule geotop_closed_segment_is_simplex[OF hne])
      thus ?thesis unfolding seg by blast
    qed
  qed
  show ?thesis
    unfolding geotop_is_broken_line_def
    using hK_complex hK_poly hK_1dim harc by blast
qed

(** ===== Phase 1 (PLAN1.md) — Sub-complex infrastructure =====

    Key fact: if K is a 1-complex containing an edge e and a point R \<in> e,
    we can subdivide e at R to produce a 1-complex K' with |K'| = |K| and
    R as a 0-simplex. This is the workhorse lemma for proving that sub-arcs
    and arc-unions of broken lines are themselves polyhedral. **)

(** Phase 1.1: subdivide a single 1-simplex e at a point R \<in> e. **)
(** Helper: in a 1-dim complex, every simplex has dim \<le> 1, so two distinct
    1-simplices meet at most in a shared vertex (0-simplex), by K.2. **)
lemma geotop_1dim_complex_simp_dim_le_1:
  fixes K :: "'a::real_normed_vector set set"
  assumes hK1dim: "geotop_complex_is_1dim K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  shows "\<exists>n\<le>1. geotop_simplex_dim \<sigma> n"
  using hK1dim h\<sigma>K unfolding geotop_complex_is_1dim_def by (by100 blast)

(** Helper: in a 1-dim complex, every simplex is either a singleton
    (dim 0) or a closed segment between two distinct points (dim 1). **)
lemma geotop_1dim_simplex_cases:
  fixes K :: "'a::euclidean_space set set"
  assumes hK1dim: "geotop_complex_is_1dim K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  shows "(\<exists>v. \<sigma> = {v}) \<or> (\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b)"
proof -
  obtain n where hn_le: "n \<le> 1" and h\<sigma>_dim: "geotop_simplex_dim \<sigma> n"
    using geotop_1dim_complex_simp_dim_le_1[OF hK1dim h\<sigma>K] by (by100 blast)
  obtain V m where hV_fin: "finite V" and hV_card: "card V = n + 1"
                and hnm: "n \<le> m" and hV_gp: "geotop_general_position V m"
                and h\<sigma>_hull: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>_dim unfolding geotop_simplex_dim_def by (by100 blast)
  have h_n_cases: "n = 0 \<or> n = 1" using hn_le by (by100 linarith)
  show ?thesis
  proof (rule disjE[OF h_n_cases])
    assume h_n0: "n = 0"
    have hV_card1: "card V = 1" using hV_card h_n0 by (by100 simp)
    have "\<exists>v. V = {v}"
      using hV_card1 card_1_singletonE by (by100 metis)
    then obtain v where hVv: "V = {v}" by (by100 blast)
    have "\<sigma> = geotop_convex_hull {v}" using h\<sigma>_hull hVv by (by100 simp)
    also have "\<dots> = convex hull {v}" by (rule geotop_convex_hull_eq_HOL)
    also have "\<dots> = {v}" by (by100 simp)
    finally have "\<sigma> = {v}" .
    thus ?thesis by (by100 blast)
  next
    assume h_n1: "n = 1"
    have hV_card2: "card V = 2" using hV_card h_n1 by (by100 simp)
    have "\<exists>a b. a \<noteq> b \<and> V = {a, b}"
      using hV_card2 card_2_iff by (by100 metis)
    then obtain a b where hab_ne: "a \<noteq> b" and hVab: "V = {a, b}" by (by100 blast)
    have "\<sigma> = geotop_convex_hull {a, b}" using h\<sigma>_hull hVab by (by100 simp)
    also have "\<dots> = convex hull {a, b}" by (rule geotop_convex_hull_eq_HOL)
    also have "\<dots> = closed_segment a b" by (rule segment_convex_hull[symmetric])
    finally have "\<sigma> = closed_segment a b" .
    thus ?thesis using hab_ne by (by100 blast)
  qed
qed

(** Helper: closed_segment P Q has vertex set {P, Q} when P ≠ Q. **)
lemma geotop_closed_segment_simplex_vertices:
  fixes P Q :: "'a::euclidean_space"
  assumes hne: "P \<noteq> Q"
  shows "geotop_simplex_vertices (closed_segment P Q) {P, Q}"
proof -
  have h_dim: "geotop_simplex_dim (closed_segment P Q) 1"
    by (rule geotop_closed_segment_is_simplex[OF hne])
  obtain V1 m1 where h_V1_fin: "finite V1" and h_V1_card: "card V1 = 1 + 1"
                 and h_nm1: "1 \<le> m1" and h_gp1: "geotop_general_position V1 m1"
                 and h_V1_hull: "closed_segment P Q = geotop_convex_hull V1"
    using h_dim unfolding geotop_simplex_dim_def by (by100 blast)
  (** simplex_vertices via the witness V1. **)
  have h_sv_V1: "geotop_simplex_vertices (closed_segment P Q) V1"
    unfolding geotop_simplex_vertices_def
    using h_V1_fin h_V1_card h_nm1 h_gp1 h_V1_hull by (by100 blast)
  have h_V1_PQ: "V1 = {P, Q}"
    by (rule geotop_segment_simplex_vertices[OF hne h_sv_V1])
  (** Now fold back. **)
  have h_final_hull: "closed_segment P Q = geotop_convex_hull {P, Q}"
    using h_V1_hull h_V1_PQ by (by100 simp)
  have h_PQ_fin: "finite {P, Q}" by (by100 simp)
  have h_PQ_card: "card {P, Q} = 1 + 1" using hne by (by100 simp)
  show ?thesis unfolding geotop_simplex_vertices_def
    using h_PQ_fin h_PQ_card h_nm1 h_gp1 h_V1_PQ h_final_hull by (by100 blast)
qed

(** Phase 1.1 helper — singleton ≠ e when e has 2 distinct vertices. **)
lemma geotop_subdivide_edge_singleton_ne_e:
  fixes e :: "'a::euclidean_space set"
  assumes hV_verts: "geotop_simplex_vertices e V"
  assumes hVeq: "V = {v\<^sub>0, v\<^sub>1}" and hv01_ne: "v\<^sub>0 \<noteq> v\<^sub>1"
  shows "{v\<^sub>0} \<noteq> e \<and> {v\<^sub>1} \<noteq> e"
proof -
  have hV_fin: "finite V" using hVeq by (by100 simp)
  have he_eq_V: "e = geotop_convex_hull V"
    using hV_verts unfolding geotop_simplex_vertices_def by (by100 blast)
  have he_HOL: "e = convex hull V"
    using he_eq_V geotop_convex_hull_eq_HOL by (by100 simp)
  have hv0_in_V: "v\<^sub>0 \<in> V" using hVeq by (by100 simp)
  have hv1_in_V: "v\<^sub>1 \<in> V" using hVeq by (by100 simp)
  have hV_sub_hull: "V \<subseteq> convex hull V" by (rule hull_subset)
  have hv0_in_hull: "v\<^sub>0 \<in> convex hull V"
    using hv0_in_V hV_sub_hull by (by100 blast)
  have hv1_in_hull: "v\<^sub>1 \<in> convex hull V"
    using hv1_in_V hV_sub_hull by (by100 blast)
  have hv0_in_e: "v\<^sub>0 \<in> e" using hv0_in_hull he_HOL by (by100 simp)
  have hv1_in_e: "v\<^sub>1 \<in> e" using hv1_in_hull he_HOL by (by100 simp)
  have h_v0_ne: "{v\<^sub>0} \<noteq> e"
  proof
    assume h_eq: "{v\<^sub>0} = e"
    have "v\<^sub>1 \<in> {v\<^sub>0}" using hv1_in_e h_eq by (by100 simp)
    hence "v\<^sub>1 = v\<^sub>0" by (by100 simp)
    thus False using hv01_ne by (by100 blast)
  qed
  have h_v1_ne: "{v\<^sub>1} \<noteq> e"
  proof
    assume h_eq: "{v\<^sub>1} = e"
    have "v\<^sub>0 \<in> {v\<^sub>1}" using hv0_in_e h_eq by (by100 simp)
    hence "v\<^sub>0 = v\<^sub>1" by (by100 simp)
    thus False using hv01_ne by (by100 blast)
  qed
  show ?thesis using h_v0_ne h_v1_ne by (by100 blast)
qed

(** Phase 1.1 helper — all simplexes in the subdivided complex.
    Proof is fully decomposed into small by100-simp steps using explicit
    rule applications, avoiding flaky disjunctive-eliminations. **)
lemma geotop_subdivide_edge_simplexes:
  fixes K :: "'a::euclidean_space set set"
  assumes hKcomp: "geotop_is_complex K"
  assumes hR_v0: "R \<noteq> v\<^sub>0" and hR_v1: "R \<noteq> v\<^sub>1"
  shows "\<forall>\<sigma>\<in>(K - {e}) \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}.
           geotop_is_simplex \<sigma>"
proof
  fix \<sigma>
  assume h\<sigma>: "\<sigma> \<in> (K - {e}) \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
  have hK_simp: "\<forall>\<tau>\<in>K. geotop_is_simplex \<tau>"
    using conjunct1[OF hKcomp[unfolded geotop_is_complex_def]] by (by100 blast)
  have hR_sim: "geotop_is_simplex {R}"
    by (rule geotop_simplex_dim_imp_is_simplex[OF geotop_singleton_is_simplex])
  have hseg_v0R: "geotop_is_simplex (closed_segment v\<^sub>0 R)"
    by (rule geotop_simplex_dim_imp_is_simplex
             [OF geotop_closed_segment_is_simplex[OF hR_v0[symmetric]]])
  have hseg_Rv1: "geotop_is_simplex (closed_segment R v\<^sub>1)"
    by (rule geotop_simplex_dim_imp_is_simplex
             [OF geotop_closed_segment_is_simplex[OF hR_v1]])
  show "geotop_is_simplex \<sigma>"
  proof (rule UnE[OF h\<sigma>])
    assume h\<sigma>_L: "\<sigma> \<in> K - {e}"
    have "\<sigma> \<in> K" using h\<sigma>_L by (by100 simp)
    thus ?thesis using hK_simp by (by100 blast)
  next
    assume h\<sigma>_R: "\<sigma> \<in> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
    have h_ins: "\<sigma> = {R} \<or> \<sigma> \<in> {closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
      using h\<sigma>_R by (by100 simp)
    show ?thesis
    proof (rule disjE[OF h_ins])
      assume "\<sigma> = {R}" thus ?thesis using hR_sim by (by100 simp)
    next
      assume h\<sigma>_R2: "\<sigma> \<in> {closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
      have h_ins2: "\<sigma> = closed_segment v\<^sub>0 R \<or> \<sigma> = closed_segment R v\<^sub>1"
        using h\<sigma>_R2 by (by100 simp)
      show ?thesis
      proof (rule disjE[OF h_ins2])
        assume "\<sigma> = closed_segment v\<^sub>0 R" thus ?thesis using hseg_v0R by (by100 simp)
      next
        assume "\<sigma> = closed_segment R v\<^sub>1" thus ?thesis using hseg_Rv1 by (by100 simp)
      qed
    qed
  qed
qed

(** Phase 1.1 helper — {v\<^sub>0} and {v\<^sub>1} are in K (face-closure). **)
lemma geotop_subdivide_edge_vertices_in_K:
  fixes K :: "'a::euclidean_space set set"
  assumes hKcomp: "geotop_is_complex K"
  assumes he_K: "e \<in> K"
  assumes hV_verts: "geotop_simplex_vertices e V"
  assumes hVeq: "V = {v\<^sub>0, v\<^sub>1}"
  shows "{v\<^sub>0} \<in> K \<and> {v\<^sub>1} \<in> K"
proof -
  have hv0_V: "{v\<^sub>0} \<subseteq> V" using hVeq by (by100 simp)
  have hv0_ne: "{v\<^sub>0} \<noteq> {}" by (by100 simp)
  have h_sing_v0: "{v\<^sub>0} = geotop_convex_hull {v\<^sub>0}"
    using geotop_convex_hull_eq_HOL[of "{v\<^sub>0}"] by (by100 simp)
  have h_face_v0: "geotop_is_face {v\<^sub>0} e"
    unfolding geotop_is_face_def
    using hV_verts hv0_V hv0_ne h_sing_v0 by (by100 blast)
  have hv1_V: "{v\<^sub>1} \<subseteq> V" using hVeq by (by100 simp)
  have hv1_ne: "{v\<^sub>1} \<noteq> {}" by (by100 simp)
  have h_sing_v1: "{v\<^sub>1} = geotop_convex_hull {v\<^sub>1}"
    using geotop_convex_hull_eq_HOL[of "{v\<^sub>1}"] by (by100 simp)
  have h_face_v1: "geotop_is_face {v\<^sub>1} e"
    unfolding geotop_is_face_def
    using hV_verts hv1_V hv1_ne h_sing_v1 by (by100 blast)
  have hK_faces: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    using conjunct1[OF conjunct2[OF hKcomp[unfolded geotop_is_complex_def]]]
    by (by100 blast)
  have hv0_in_K: "{v\<^sub>0} \<in> K" using hK_faces he_K h_face_v0 by (by100 blast)
  have hv1_in_K: "{v\<^sub>1} \<in> K" using hK_faces he_K h_face_v1 by (by100 blast)
  show ?thesis using hv0_in_K hv1_in_K by (by100 blast)
qed

(** Phase 1.1 helper — K.1 (face closure) for the subdivided complex.
    Requires knowing {v\<^sub>0}, {v\<^sub>1} \<in> K (from vertices_in_K).
    Additionally requires K 1-dim and that v\<^sub>0 \<noteq> v\<^sub>1 so we can rule
    out τ = e when σ ∈ K-{e}. **)
lemma geotop_subdivide_edge_face_closed:
  fixes K :: "'a::euclidean_space set set"
  assumes hKcomp: "geotop_is_complex K"
  assumes hK1dim: "geotop_complex_is_1dim K"
  assumes he_K: "e \<in> K"
  assumes hV_verts: "geotop_simplex_vertices e V"
  assumes hVeq: "V = {v\<^sub>0, v\<^sub>1}" and hv01_ne: "v\<^sub>0 \<noteq> v\<^sub>1"
  assumes hv0_K: "{v\<^sub>0} \<in> K" and hv1_K: "{v\<^sub>1} \<in> K"
  assumes hR_v0: "R \<noteq> v\<^sub>0" and hR_v1: "R \<noteq> v\<^sub>1"
  shows "\<forall>\<sigma>\<in>(K - {e}) \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}.
           \<forall>\<tau>. geotop_is_face \<tau> \<sigma>
              \<longrightarrow> \<tau> \<in> (K - {e}) \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
proof (intro ballI allI impI)
  fix \<sigma> \<tau>
  let ?K' = "(K - {e}) \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
  assume h\<sigma>: "\<sigma> \<in> ?K'"
  assume h_face: "geotop_is_face \<tau> \<sigma>"
  have hK_face: "\<forall>\<sigma>'\<in>K. \<forall>\<tau>'. geotop_is_face \<tau>' \<sigma>' \<longrightarrow> \<tau>' \<in> K"
    using conjunct1[OF conjunct2[OF hKcomp[unfolded geotop_is_complex_def]]]
    by (by100 blast)
  have h_v0_ne_e: "{v\<^sub>0} \<noteq> e \<and> {v\<^sub>1} \<noteq> e"
    by (rule geotop_subdivide_edge_singleton_ne_e[OF hV_verts hVeq hv01_ne])
  have h_v0_ne: "{v\<^sub>0} \<noteq> e" using h_v0_ne_e by (by100 blast)
  have h_v1_ne: "{v\<^sub>1} \<noteq> e" using h_v0_ne_e by (by100 blast)
  show "\<tau> \<in> ?K'"
  proof (rule UnE[OF h\<sigma>])
    assume h\<sigma>_old: "\<sigma> \<in> K - {e}"
    have h\<sigma>_K: "\<sigma> \<in> K" using h\<sigma>_old by (by100 simp)
    have h\<sigma>_ne_e: "\<sigma> \<noteq> e" using h\<sigma>_old by (by100 simp)
    have h\<tau>_K: "\<tau> \<in> K" using hK_face h\<sigma>_K h_face by (by100 blast)
    (** Need τ ≠ e. Argue by the 1-dim constraint. **)
    have h\<sigma>_1dim: "\<exists>n\<le>1. geotop_simplex_dim \<sigma> n"
      using hK1dim h\<sigma>_K unfolding geotop_complex_is_1dim_def by (by100 blast)
    obtain n\<sigma> where hn\<sigma>_le: "n\<sigma> \<le> 1" and h\<sigma>_dim: "geotop_simplex_dim \<sigma> n\<sigma>"
      using h\<sigma>_1dim by (by100 blast)
    obtain V\<sigma> m\<sigma> where hV\<sigma>_fin: "finite V\<sigma>" and hV\<sigma>_card: "card V\<sigma> = n\<sigma> + 1"
                   and hn\<sigma>m\<sigma>: "n\<sigma> \<le> m\<sigma>" and hV\<sigma>_gp: "geotop_general_position V\<sigma> m\<sigma>"
                   and h\<sigma>_hull: "\<sigma> = geotop_convex_hull V\<sigma>"
      using h\<sigma>_dim unfolding geotop_simplex_dim_def by (by100 blast)
    have hV\<sigma>_sv: "geotop_simplex_vertices \<sigma> V\<sigma>"
      unfolding geotop_simplex_vertices_def
      using hV\<sigma>_fin hV\<sigma>_card hn\<sigma>m\<sigma> hV\<sigma>_gp h\<sigma>_hull by (by100 blast)
    have hV\<sigma>_card_le: "card V\<sigma> \<le> 2" using hV\<sigma>_card hn\<sigma>_le by (by100 simp)
    (** Extract τ's face-structure. **)
    obtain V' W' where hV'_sv: "geotop_simplex_vertices \<sigma> V'"
                    and hW'_ne: "W' \<noteq> {}" and hW'_V': "W' \<subseteq> V'"
                    and h\<tau>_hull: "\<tau> = geotop_convex_hull W'"
      using h_face unfolding geotop_is_face_def by (by100 blast)
    have hV'_eq: "V' = V\<sigma>"
      by (rule geotop_simplex_vertices_unique[OF hV'_sv hV\<sigma>_sv])
    have hW'_sub_V\<sigma>: "W' \<subseteq> V\<sigma>" using hW'_V' hV'_eq by (by100 simp)
    have hW'_fin: "finite W'" by (rule finite_subset[OF hW'_sub_V\<sigma> hV\<sigma>_fin])
    have hW'_card_mono: "card W' \<le> card V\<sigma>" by (rule card_mono[OF hV\<sigma>_fin hW'_sub_V\<sigma>])
    have hW'_card_le: "card W' \<le> 2" using hW'_card_mono hV\<sigma>_card_le by (by100 simp)
    have hW'_card_ne_0: "card W' \<noteq> 0"
    proof
      assume "card W' = 0"
      hence "W' = {}" using hW'_fin card_0_eq by (by100 blast)
      thus False using hW'_ne by (by100 blast)
    qed
    have hW'_card_ge: "card W' \<ge> 1" using hW'_card_ne_0 by (by100 simp)
    (** Contradiction if τ = e: analyze |W'|. **)
    have h\<tau>_ne_e: "\<tau> \<noteq> e"
    proof
      assume h\<tau>_eq_e: "\<tau> = e"
      (** |W'| ∈ {1, 2}. **)
      have hW'_card_1_or_2: "card W' = 1 \<or> card W' = 2"
      proof -
        have h1: "card W' \<le> 2" by (rule hW'_card_le)
        have h2: "card W' \<ge> 1" by (rule hW'_card_ge)
        from h1 h2 show ?thesis by (by100 linarith)
      qed
      show False
      proof (rule disjE[OF hW'_card_1_or_2])
        assume hcard1: "card W' = 1"
        (** W' = {w} for some w. τ = conv{w} = {w}. **)
        have "\<exists>w. W' = {w}"
          using hcard1 card_1_singletonE by (by100 metis)
        then obtain w where hW'_w: "W' = {w}" by (by100 blast)
        have h\<tau>_sing: "\<tau> = {w}"
        proof -
          have "\<tau> = geotop_convex_hull {w}" using h\<tau>_hull hW'_w by (by100 simp)
          also have "\<dots> = convex hull {w}" by (rule geotop_convex_hull_eq_HOL)
          also have "\<dots> = {w}" by (by100 simp)
          finally show ?thesis .
        qed
        (** But e contains both v0 and v1. If e = {w}, v0 = v1 = w. Contradiction. **)
        have h_v0_in_e: "v\<^sub>0 \<in> e"
        proof -
          have hV_sub_hull: "V \<subseteq> convex hull V" by (rule hull_subset)
          have hv0_V: "v\<^sub>0 \<in> V" using hVeq by (by100 simp)
          have hv0_hull: "v\<^sub>0 \<in> convex hull V" using hv0_V hV_sub_hull by (by100 blast)
          have he_V: "e = geotop_convex_hull V"
            using hV_verts unfolding geotop_simplex_vertices_def by (by100 blast)
          have he_hull: "e = convex hull V"
            using he_V geotop_convex_hull_eq_HOL by (by100 simp)
          show ?thesis using hv0_hull he_hull by (by100 simp)
        qed
        have h_v1_in_e: "v\<^sub>1 \<in> e"
        proof -
          have hV_sub_hull: "V \<subseteq> convex hull V" by (rule hull_subset)
          have hv1_V: "v\<^sub>1 \<in> V" using hVeq by (by100 simp)
          have hv1_hull: "v\<^sub>1 \<in> convex hull V" using hv1_V hV_sub_hull by (by100 blast)
          have he_V: "e = geotop_convex_hull V"
            using hV_verts unfolding geotop_simplex_vertices_def by (by100 blast)
          have he_hull: "e = convex hull V"
            using he_V geotop_convex_hull_eq_HOL by (by100 simp)
          show ?thesis using hv1_hull he_hull by (by100 simp)
        qed
        have h_v0_w: "v\<^sub>0 = w" using h_v0_in_e h\<tau>_eq_e h\<tau>_sing by (by100 blast)
        have h_v1_w: "v\<^sub>1 = w" using h_v1_in_e h\<tau>_eq_e h\<tau>_sing by (by100 blast)
        have "v\<^sub>0 = v\<^sub>1" using h_v0_w h_v1_w by (by100 simp)
        thus False using hv01_ne by (by100 blast)
      next
        assume hcard2: "card W' = 2"
        (** W' has 2 elements, W' ⊆ V_σ, |V_σ| ≤ 2 → W' = V_σ. **)
        have hV\<sigma>_card_eq_2: "card V\<sigma> = 2"
          using hcard2 hW'_card_mono hV\<sigma>_card_le by (by100 simp)
        have hW'_eq_V\<sigma>: "W' = V\<sigma>"
        proof -
          have h_card_eq: "card W' = card V\<sigma>" using hcard2 hV\<sigma>_card_eq_2 by (by100 simp)
          show ?thesis by (rule card_subset_eq[OF hV\<sigma>_fin hW'_sub_V\<sigma> h_card_eq])
        qed
        have h\<tau>_eq_\<sigma>: "\<tau> = \<sigma>"
        proof -
          have "\<tau> = geotop_convex_hull W'" by (rule h\<tau>_hull)
          also have "\<dots> = geotop_convex_hull V\<sigma>" using hW'_eq_V\<sigma> by (by100 simp)
          also have "\<dots> = \<sigma>" using h\<sigma>_hull by (by100 simp)
          finally show ?thesis .
        qed
        have "\<sigma> = e" using h\<tau>_eq_\<sigma> h\<tau>_eq_e by (by100 simp)
        thus False using h\<sigma>_ne_e by (by100 blast)
      qed
    qed
    have h\<tau>_Ke: "\<tau> \<in> K - {e}" using h\<tau>_K h\<tau>_ne_e by (by100 simp)
    show "\<tau> \<in> ?K'" using h\<tau>_Ke by (by100 blast)
  next
    assume h\<sigma>_new: "\<sigma> \<in> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
    have h_ins: "\<sigma> = {R} \<or> \<sigma> \<in> {closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
      using h\<sigma>_new by (by100 simp)
    show "\<tau> \<in> ?K'"
    proof (rule disjE[OF h_ins])
      assume h\<sigma>_R: "\<sigma> = {R}"
      (** Face of {R} is {R}. **)
      have h_dim_R: "geotop_simplex_dim {R} 0" by (rule geotop_singleton_is_simplex)
      have h_sv_R: "geotop_simplex_vertices {R} {R}"
      proof -
        obtain V1 m1 where h_V1_fin: "finite V1" and h_V1_card: "card V1 = 0 + 1"
                       and h_nm1: "0 \<le> m1" and h_gp1: "geotop_general_position V1 m1"
                       and h_R_hull1: "{R} = geotop_convex_hull V1"
          using h_dim_R unfolding geotop_simplex_dim_def by (by100 blast)
        have h_V1_card_1: "card V1 = 1" using h_V1_card by (by100 simp)
        have h_V1_R: "V1 = {R}"
        proof -
          have h_hull_HOL: "{R} = convex hull V1"
            using h_R_hull1 geotop_convex_hull_eq_HOL by (by100 simp)
          have h_V1_sing: "\<exists>x. V1 = {x}"
            using h_V1_card_1 card_1_singletonE by (by100 metis)
          obtain x where h_V1_x: "V1 = {x}" using h_V1_sing by (by100 blast)
          have h_x_R: "x = R"
          proof -
            have "convex hull {x} = {x}" by (by100 simp)
            hence "{R} = {x}" using h_hull_HOL h_V1_x by (by100 simp)
            thus ?thesis by (by100 blast)
          qed
          show ?thesis using h_V1_x h_x_R by (by100 simp)
        qed
        show ?thesis unfolding geotop_simplex_vertices_def
          using h_V1_fin h_V1_card h_nm1 h_gp1 h_R_hull1 h_V1_R by (by100 blast)
      qed
      obtain V' W' where hV'_sv: "geotop_simplex_vertices \<sigma> V'"
                      and hW'_ne: "W' \<noteq> {}" and hW'_V': "W' \<subseteq> V'"
                      and h\<tau>_hull: "\<tau> = geotop_convex_hull W'"
        using h_face unfolding geotop_is_face_def by (by100 blast)
      have hV'_sv_R: "geotop_simplex_vertices \<sigma> {R}"
        using h_sv_R h\<sigma>_R by (by100 simp)
      have hV'_eq: "V' = {R}"
        by (rule geotop_simplex_vertices_unique[OF hV'_sv hV'_sv_R])
      have hW'_sub_R: "W' \<subseteq> {R}" using hW'_V' hV'_eq by (by100 simp)
      have hW'_R: "W' = {R}" using hW'_ne hW'_sub_R by (by100 blast)
      have h\<tau>_R: "\<tau> = {R}"
      proof -
        have h_step1: "\<tau> = geotop_convex_hull {R}" using h\<tau>_hull hW'_R by (by100 simp)
        have h_step2: "geotop_convex_hull {R} = convex hull {R}"
          by (rule geotop_convex_hull_eq_HOL)
        have h_step3: "(convex hull {R}) = {R}" by (by100 simp)
        show ?thesis using h_step1 h_step2 h_step3 by (by100 simp)
      qed
      show "\<tau> \<in> ?K'" using h\<tau>_R by (by100 blast)
    next
      assume h\<sigma>_lr: "\<sigma> \<in> {closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
      have h_ins_lr: "\<sigma> = closed_segment v\<^sub>0 R \<or> \<sigma> = closed_segment R v\<^sub>1"
        using h\<sigma>_lr by (by100 simp)
      show "\<tau> \<in> ?K'"
      proof (rule disjE[OF h_ins_lr])
        assume h\<sigma>_el: "\<sigma> = closed_segment v\<^sub>0 R"
        (** V(σ) = {v_0, R}; face τ of σ has W ⊆ {v_0, R} nonempty. **)
        have hR_v0_sym: "v\<^sub>0 \<noteq> R" using hR_v0 by (by100 blast)
        have h_sv_el: "geotop_simplex_vertices (closed_segment v\<^sub>0 R) {v\<^sub>0, R}"
          by (rule geotop_closed_segment_simplex_vertices[OF hR_v0_sym])
        have h_sv_sigma: "geotop_simplex_vertices \<sigma> {v\<^sub>0, R}"
          using h_sv_el h\<sigma>_el by (by100 simp)
        obtain V' W' where hV'_sv: "geotop_simplex_vertices \<sigma> V'"
                        and hW'_ne: "W' \<noteq> {}" and hW'_V': "W' \<subseteq> V'"
                        and h\<tau>_hull: "\<tau> = geotop_convex_hull W'"
          using h_face unfolding geotop_is_face_def by (by100 blast)
        have hV'_eq: "V' = {v\<^sub>0, R}"
          by (rule geotop_simplex_vertices_unique[OF hV'_sv h_sv_sigma])
        have hW'_sub: "W' \<subseteq> {v\<^sub>0, R}" using hW'_V' hV'_eq by (by100 simp)
        (** W' is nonempty subset of 2-element set: W' ∈ {{v0}, {R}, {v0,R}}. **)
        have h_W'_cases: "W' = {v\<^sub>0} \<or> W' = {R} \<or> W' = {v\<^sub>0, R}"
          using hW'_ne hW'_sub by (by100 blast)
        show "\<tau> \<in> ?K'"
        proof (rule disjE[OF h_W'_cases])
          assume h_W'_v0: "W' = {v\<^sub>0}"
          have h\<tau>_eq_v0: "\<tau> = {v\<^sub>0}"
          proof -
            have "\<tau> = geotop_convex_hull {v\<^sub>0}" using h\<tau>_hull h_W'_v0 by (by100 simp)
            also have "\<dots> = convex hull {v\<^sub>0}" by (rule geotop_convex_hull_eq_HOL)
            also have "\<dots> = {v\<^sub>0}" by (by100 simp)
            finally show ?thesis .
          qed
          have h_v0_Ke: "{v\<^sub>0} \<in> K - {e}" using hv0_K h_v0_ne by (by100 simp)
          show "\<tau> \<in> ?K'" using h\<tau>_eq_v0 h_v0_Ke by (by100 blast)
        next
          assume h_W'_rest: "W' = {R} \<or> W' = {v\<^sub>0, R}"
          show "\<tau> \<in> ?K'"
          proof (rule disjE[OF h_W'_rest])
            assume h_W'_R: "W' = {R}"
            have h\<tau>_eq_R: "\<tau> = {R}"
            proof -
              have "\<tau> = geotop_convex_hull {R}" using h\<tau>_hull h_W'_R by (by100 simp)
              also have "\<dots> = convex hull {R}" by (rule geotop_convex_hull_eq_HOL)
              also have "\<dots> = {R}" by (by100 simp)
              finally show ?thesis .
            qed
            show "\<tau> \<in> ?K'" using h\<tau>_eq_R by (by100 blast)
          next
            assume h_W'_full: "W' = {v\<^sub>0, R}"
            have h\<tau>_eq_el: "\<tau> = closed_segment v\<^sub>0 R"
            proof -
              have "\<tau> = geotop_convex_hull {v\<^sub>0, R}"
                using h\<tau>_hull h_W'_full by (by100 simp)
              also have "\<dots> = convex hull {v\<^sub>0, R}" by (rule geotop_convex_hull_eq_HOL)
              also have "\<dots> = closed_segment v\<^sub>0 R" by (rule segment_convex_hull[symmetric])
              finally show ?thesis .
            qed
            show "\<tau> \<in> ?K'" using h\<tau>_eq_el by (by100 blast)
          qed
        qed
      next
        assume h\<sigma>_er: "\<sigma> = closed_segment R v\<^sub>1"
        have hR_v1_sym: "R \<noteq> v\<^sub>1" using hR_v1 by (by100 blast)
        have h_sv_er: "geotop_simplex_vertices (closed_segment R v\<^sub>1) {R, v\<^sub>1}"
          by (rule geotop_closed_segment_simplex_vertices[OF hR_v1_sym])
        have h_sv_sigma: "geotop_simplex_vertices \<sigma> {R, v\<^sub>1}"
          using h_sv_er h\<sigma>_er by (by100 simp)
        obtain V' W' where hV'_sv: "geotop_simplex_vertices \<sigma> V'"
                        and hW'_ne: "W' \<noteq> {}" and hW'_V': "W' \<subseteq> V'"
                        and h\<tau>_hull: "\<tau> = geotop_convex_hull W'"
          using h_face unfolding geotop_is_face_def by (by100 blast)
        have hV'_eq: "V' = {R, v\<^sub>1}"
          by (rule geotop_simplex_vertices_unique[OF hV'_sv h_sv_sigma])
        have hW'_sub: "W' \<subseteq> {R, v\<^sub>1}" using hW'_V' hV'_eq by (by100 simp)
        have h_W'_cases: "W' = {R} \<or> W' = {v\<^sub>1} \<or> W' = {R, v\<^sub>1}"
          using hW'_ne hW'_sub by (by100 blast)
        show "\<tau> \<in> ?K'"
        proof (rule disjE[OF h_W'_cases])
          assume h_W'_R: "W' = {R}"
          have h\<tau>_eq_R: "\<tau> = {R}"
          proof -
            have "\<tau> = geotop_convex_hull {R}" using h\<tau>_hull h_W'_R by (by100 simp)
            also have "\<dots> = convex hull {R}" by (rule geotop_convex_hull_eq_HOL)
            also have "\<dots> = {R}" by (by100 simp)
            finally show ?thesis .
          qed
          show "\<tau> \<in> ?K'" using h\<tau>_eq_R by (by100 blast)
        next
          assume h_W'_rest: "W' = {v\<^sub>1} \<or> W' = {R, v\<^sub>1}"
          show "\<tau> \<in> ?K'"
          proof (rule disjE[OF h_W'_rest])
            assume h_W'_v1: "W' = {v\<^sub>1}"
            have h\<tau>_eq_v1: "\<tau> = {v\<^sub>1}"
            proof -
              have "\<tau> = geotop_convex_hull {v\<^sub>1}" using h\<tau>_hull h_W'_v1 by (by100 simp)
              also have "\<dots> = convex hull {v\<^sub>1}" by (rule geotop_convex_hull_eq_HOL)
              also have "\<dots> = {v\<^sub>1}" by (by100 simp)
              finally show ?thesis .
            qed
            have h_v1_Ke: "{v\<^sub>1} \<in> K - {e}" using hv1_K h_v1_ne by (by100 simp)
            show "\<tau> \<in> ?K'" using h\<tau>_eq_v1 h_v1_Ke by (by100 blast)
          next
            assume h_W'_full: "W' = {R, v\<^sub>1}"
            have h\<tau>_eq_er: "\<tau> = closed_segment R v\<^sub>1"
            proof -
              have "\<tau> = geotop_convex_hull {R, v\<^sub>1}"
                using h\<tau>_hull h_W'_full by (by100 simp)
              also have "\<dots> = convex hull {R, v\<^sub>1}" by (rule geotop_convex_hull_eq_HOL)
              also have "\<dots> = closed_segment R v\<^sub>1" by (rule segment_convex_hull[symmetric])
              finally show ?thesis .
            qed
            show "\<tau> \<in> ?K'" using h\<tau>_eq_er by (by100 blast)
          qed
        qed
      qed
    qed
  qed
qed

(** Phase 1.1 helper — closed_segment v\<^sub>0 R and closed_segment R v\<^sub>1
    meet precisely at R, whenever R lies on closed_segment v\<^sub>0 v\<^sub>1.
    Uses the library lemma Int_closed_segment. **)
lemma geotop_subdivide_edge_el_inter_er:
  fixes v\<^sub>0 v\<^sub>1 R :: "'a::euclidean_space"
  assumes hR_cs: "R \<in> closed_segment v\<^sub>0 v\<^sub>1"
  shows "closed_segment v\<^sub>0 R \<inter> closed_segment R v\<^sub>1 = {R}"
  using hR_cs by (rule Int_closed_segment[OF disjI1])

(** Phase 1.1 helper — v\<^sub>0 \<notin> closed_segment R v\<^sub>1 when R \<in> closed_segment v\<^sub>0 v\<^sub>1
    and R \<noteq> v\<^sub>0. Derived from the exact intersection lemma. **)
lemma geotop_subdivide_edge_v0_notin_er:
  fixes v\<^sub>0 v\<^sub>1 R :: "'a::euclidean_space"
  assumes hR_cs: "R \<in> closed_segment v\<^sub>0 v\<^sub>1"
  assumes hR_v0: "R \<noteq> v\<^sub>0"
  shows "v\<^sub>0 \<notin> closed_segment R v\<^sub>1"
proof
  assume h_in_er: "v\<^sub>0 \<in> closed_segment R v\<^sub>1"
  have h_in_el: "v\<^sub>0 \<in> closed_segment v\<^sub>0 R" by (by100 simp)
  have h_in_both: "v\<^sub>0 \<in> closed_segment v\<^sub>0 R \<inter> closed_segment R v\<^sub>1"
    using h_in_el h_in_er by (by100 blast)
  have h_int_R: "closed_segment v\<^sub>0 R \<inter> closed_segment R v\<^sub>1 = {R}"
    by (rule geotop_subdivide_edge_el_inter_er[OF hR_cs])
  have "v\<^sub>0 \<in> {R}" using h_in_both h_int_R by (by100 simp)
  hence "v\<^sub>0 = R" by (by100 simp)
  thus False using hR_v0 by (by100 blast)
qed

(** Phase 1.1 helper — v\<^sub>1 \<notin> closed_segment v\<^sub>0 R. Symmetric to v0_notin_er. **)
lemma geotop_subdivide_edge_v1_notin_el:
  fixes v\<^sub>0 v\<^sub>1 R :: "'a::euclidean_space"
  assumes hR_cs: "R \<in> closed_segment v\<^sub>0 v\<^sub>1"
  assumes hR_v1: "R \<noteq> v\<^sub>1"
  shows "v\<^sub>1 \<notin> closed_segment v\<^sub>0 R"
proof
  assume h_in_el: "v\<^sub>1 \<in> closed_segment v\<^sub>0 R"
  have h_in_er: "v\<^sub>1 \<in> closed_segment R v\<^sub>1" by (by100 simp)
  have h_in_both: "v\<^sub>1 \<in> closed_segment v\<^sub>0 R \<inter> closed_segment R v\<^sub>1"
    using h_in_el h_in_er by (by100 blast)
  have h_int_R: "closed_segment v\<^sub>0 R \<inter> closed_segment R v\<^sub>1 = {R}"
    by (rule geotop_subdivide_edge_el_inter_er[OF hR_cs])
  have "v\<^sub>1 \<in> {R}" using h_in_both h_int_R by (by100 simp)
  hence "v\<^sub>1 = R" by (by100 simp)
  thus False using hR_v1[symmetric] by (by100 blast)
qed

(** Phase 1.1 helper — {x} is a face of {x} for any x. **)
lemma geotop_singleton_is_face_self:
  fixes x :: "'a::euclidean_space"
  shows "geotop_is_face {x} {x}"
proof -
  have h_dim: "geotop_simplex_dim {x} 0" by (rule geotop_singleton_is_simplex)
  obtain V1 m1 where h_V1_fin: "finite V1" and h_V1_card: "card V1 = 0 + 1"
                 and h_nm1: "0 \<le> m1" and h_gp1: "geotop_general_position V1 m1"
                 and h_V1_hull: "{x} = geotop_convex_hull V1"
    using h_dim unfolding geotop_simplex_dim_def by (by100 blast)
  have h_V1_card_1: "card V1 = 1" using h_V1_card by (by100 simp)
  have h_V1_sing: "\<exists>w. V1 = {w}"
    using h_V1_card_1 card_1_singletonE by (by100 metis)
  obtain w where h_V1_w: "V1 = {w}" using h_V1_sing by (by100 blast)
  have h_x_hull: "{x} = geotop_convex_hull {w}" using h_V1_hull h_V1_w by (by100 simp)
  have h_gcvh_w: "geotop_convex_hull {w} = convex hull {w}"
    by (rule geotop_convex_hull_eq_HOL)
  have h_x_hull_HOL: "{x} = convex hull {w}"
    using h_x_hull h_gcvh_w by (by100 simp)
  have h_w_x: "w = x"
  proof -
    have h_cvx_w: "convex hull {w} = {w}" by (by100 simp)
    have "{x} = {w}" using h_x_hull_HOL h_cvx_w by (by100 simp)
    thus ?thesis by (by100 blast)
  qed
  have h_V1_x: "V1 = {x}" using h_V1_w h_w_x by (by100 simp)
  have h_sv: "geotop_simplex_vertices {x} {x}"
    unfolding geotop_simplex_vertices_def
    using h_V1_fin h_V1_card h_nm1 h_gp1 h_V1_hull h_V1_x by (by100 blast)
  have h_sub: "{x} \<subseteq> {x}" by (by100 simp)
  have h_ne: "{x} \<noteq> ({}::'a set)" by (by100 simp)
  have h_hull_eq: "{x} = geotop_convex_hull {x}"
    using geotop_convex_hull_eq_HOL[of "{x}"] by (by100 simp)
  show ?thesis unfolding geotop_is_face_def
    using h_sv h_sub h_ne h_hull_eq by (by100 blast)
qed

(** Phase 1.1 helper — {v} is a face of closed_segment a b for v \<in> {a, b}, a \<noteq> b. **)
lemma geotop_closed_segment_is_face_endpoint:
  fixes a b v :: "'a::euclidean_space"
  assumes hab: "a \<noteq> b"
  assumes hv: "v = a \<or> v = b"
  shows "geotop_is_face {v} (closed_segment a b)"
proof -
  have h_sv: "geotop_simplex_vertices (closed_segment a b) {a, b}"
    by (rule geotop_closed_segment_simplex_vertices[OF hab])
  have h_v_ab: "v \<in> {a, b}" using hv by (by100 blast)
  have h_sub: "{v} \<subseteq> {a, b}" using h_v_ab by (by100 blast)
  have h_ne: "{v} \<noteq> ({}::'a set)" by (by100 simp)
  have h_hull_eq: "{v} = geotop_convex_hull {v}"
    using geotop_convex_hull_eq_HOL[of "{v}"] by (by100 simp)
  show ?thesis unfolding geotop_is_face_def
    using h_sv h_sub h_ne h_hull_eq by (by100 blast)
qed

(** Phase 1.1 helper — closed_segment a b is a face of itself, a \<noteq> b. **)
lemma geotop_closed_segment_is_face_self:
  fixes a b :: "'a::euclidean_space"
  assumes hab: "a \<noteq> b"
  shows "geotop_is_face (closed_segment a b) (closed_segment a b)"
proof -
  have h_sv: "geotop_simplex_vertices (closed_segment a b) {a, b}"
    by (rule geotop_closed_segment_simplex_vertices[OF hab])
  have h_sub: "{a, b} \<subseteq> {a, b}" by (by100 simp)
  have h_ne: "{a, b} \<noteq> ({}::'a set)" by (by100 simp)
  have h_hull_eq: "closed_segment a b = geotop_convex_hull {a, b}"
  proof -
    have "geotop_convex_hull {a, b} = convex hull {a, b}"
      by (rule geotop_convex_hull_eq_HOL)
    also have "\<dots> = closed_segment a b" by (rule segment_convex_hull[symmetric])
    finally show ?thesis by (by100 simp)
  qed
  have h_conj_inner:
    "geotop_simplex_vertices (closed_segment a b) {a,b}
      \<and> ({a,b}::'a set) \<noteq> {} \<and> ({a,b}::'a set) \<subseteq> {a,b}
      \<and> closed_segment a b = geotop_convex_hull {a,b}"
    using h_sv h_sub h_ne h_hull_eq by (by100 simp)
  have h_exists_W:
    "\<exists>W. geotop_simplex_vertices (closed_segment a b) {a,b}
         \<and> W \<noteq> {} \<and> W \<subseteq> {a,b} \<and> closed_segment a b = geotop_convex_hull W"
    by (rule exI[where x="{a,b}"]) (rule h_conj_inner)
  have h_exists:
    "\<exists>V W. geotop_simplex_vertices (closed_segment a b) V
         \<and> W \<noteq> {} \<and> W \<subseteq> V \<and> closed_segment a b = geotop_convex_hull W"
    by (rule exI[where x="{a,b}"]) (rule h_exists_W)
  show ?thesis unfolding geotop_is_face_def by (rule h_exists)
qed

(** Phase 1.1 helper — for σ ∈ K-{e} in a 1-dim complex K, σ ∩ e is
    one of {}, {v\<^sub>0}, {v\<^sub>1}. Derived from K.2 of K (faces of e are
    {v\<^sub>0}, {v\<^sub>1}, e) plus the 1-dim bound that rules out σ ∩ e = e. **)
lemma geotop_subdivide_edge_sigma_cap_e_cases:
  fixes K :: "'a::euclidean_space set set"
  assumes hKcomp: "geotop_is_complex K"
  assumes hK1dim: "geotop_complex_is_1dim K"
  assumes he_K: "e \<in> K"
  assumes hV_verts: "geotop_simplex_vertices e V"
  assumes hVeq: "V = {v\<^sub>0, v\<^sub>1}" and hv01_ne: "v\<^sub>0 \<noteq> v\<^sub>1"
  assumes h\<sigma>_Ke: "\<sigma> \<in> K - {e}"
  shows "\<sigma> \<inter> e = {} \<or> \<sigma> \<inter> e = {v\<^sub>0} \<or> \<sigma> \<inter> e = {v\<^sub>1}"
proof (cases "\<sigma> \<inter> e = {}")
  case True
  thus ?thesis by (by100 blast)
next
  case h_ne: False
  have h\<sigma>_K: "\<sigma> \<in> K" using h\<sigma>_Ke by (by100 simp)
  have h\<sigma>_ne_e: "\<sigma> \<noteq> e" using h\<sigma>_Ke by (by100 simp)
  (** K.2 of K: \<sigma> \<inter> e is face of e. **)
  have hK_inter_face: "\<forall>\<sigma>'\<in>K. \<forall>\<tau>'\<in>K. \<sigma>' \<inter> \<tau>' \<noteq> {} \<longrightarrow>
                      geotop_is_face (\<sigma>' \<inter> \<tau>') \<sigma>' \<and> geotop_is_face (\<sigma>' \<inter> \<tau>') \<tau>'"
    using conjunct1[OF conjunct2[OF conjunct2[OF hKcomp[unfolded geotop_is_complex_def]]]]
    by (by100 blast)
  have h_face_e: "geotop_is_face (\<sigma> \<inter> e) e"
    using hK_inter_face h\<sigma>_K he_K h_ne by (by100 blast)
  have h_face_\<sigma>: "geotop_is_face (\<sigma> \<inter> e) \<sigma>"
    using hK_inter_face h\<sigma>_K he_K h_ne by (by100 blast)
  (** Extract witness W for face-of-e. **)
  obtain V' W where hV'_sv: "geotop_simplex_vertices e V'"
                 and hW_ne: "W \<noteq> {}" and hW_V': "W \<subseteq> V'"
                 and h_cap_hull: "\<sigma> \<inter> e = geotop_convex_hull W"
    using h_face_e unfolding geotop_is_face_def by (by100 blast)
  have hV'_eq: "V' = V"
    by (rule geotop_simplex_vertices_unique[OF hV'_sv hV_verts])
  have hW_sub: "W \<subseteq> {v\<^sub>0, v\<^sub>1}" using hW_V' hV'_eq hVeq by (by100 simp)
  have hW_cases: "W = {v\<^sub>0} \<or> W = {v\<^sub>1} \<or> W = {v\<^sub>0, v\<^sub>1}"
    using hW_ne hW_sub by (by100 blast)
  show ?thesis
  proof (rule disjE[OF hW_cases])
    assume hW_v0: "W = {v\<^sub>0}"
    have "\<sigma> \<inter> e = geotop_convex_hull {v\<^sub>0}" using h_cap_hull hW_v0 by (by100 simp)
    also have "\<dots> = convex hull {v\<^sub>0}" by (rule geotop_convex_hull_eq_HOL)
    also have "\<dots> = {v\<^sub>0}" by (by100 simp)
    finally have "\<sigma> \<inter> e = {v\<^sub>0}" .
    thus ?thesis by (by100 blast)
  next
    assume hW_rest: "W = {v\<^sub>1} \<or> W = {v\<^sub>0, v\<^sub>1}"
    show ?thesis
    proof (rule disjE[OF hW_rest])
      assume hW_v1: "W = {v\<^sub>1}"
      have "\<sigma> \<inter> e = geotop_convex_hull {v\<^sub>1}" using h_cap_hull hW_v1 by (by100 simp)
      also have "\<dots> = convex hull {v\<^sub>1}" by (rule geotop_convex_hull_eq_HOL)
      also have "\<dots> = {v\<^sub>1}" by (by100 simp)
      finally have "\<sigma> \<inter> e = {v\<^sub>1}" .
      thus ?thesis by (by100 blast)
    next
      assume hW_full: "W = {v\<^sub>0, v\<^sub>1}"
      (** \<sigma> \<inter> e = convex hull V = e. Derive \<sigma> = e, contradiction. **)
      have h_cap_eq_e: "\<sigma> \<inter> e = e"
      proof -
        have h1: "\<sigma> \<inter> e = geotop_convex_hull V" using h_cap_hull hW_full hVeq by (by100 simp)
        have h2: "e = geotop_convex_hull V"
          using hV_verts unfolding geotop_simplex_vertices_def by (by100 blast)
        show ?thesis using h1 h2 by (by100 simp)
      qed
      have he_sub_\<sigma>: "e \<subseteq> \<sigma>" using h_cap_eq_e by (by100 blast)
      (** Use K.2 again to conclude e is a face of \<sigma>, then \<sigma> = e. **)
      have he_cap_\<sigma>: "e \<inter> \<sigma> = e" using he_sub_\<sigma> by (by100 blast)
      have h_ne2: "e \<inter> \<sigma> \<noteq> {}"
      proof -
        have hv0_V: "v\<^sub>0 \<in> V" using hVeq by (by100 simp)
        have hV_hull: "V \<subseteq> convex hull V" by (rule hull_subset)
        have hv0_hull: "v\<^sub>0 \<in> convex hull V" using hv0_V hV_hull by (by100 blast)
        have he_V: "e = geotop_convex_hull V"
          using hV_verts unfolding geotop_simplex_vertices_def by (by100 blast)
        have he_HOL: "e = convex hull V"
          using he_V geotop_convex_hull_eq_HOL by (by100 simp)
        have hv0_e: "v\<^sub>0 \<in> e" using hv0_hull he_HOL by (by100 simp)
        show ?thesis using hv0_e he_cap_\<sigma> by (by100 blast)
      qed
      have h_face_\<sigma>_e: "geotop_is_face (e \<inter> \<sigma>) \<sigma>"
        using hK_inter_face he_K h\<sigma>_K h_ne2 by (by100 blast)
      have h_face_e_of_\<sigma>: "geotop_is_face e \<sigma>"
        using h_face_\<sigma>_e he_cap_\<sigma> by (by100 simp)
      (** Now extract witnesses for e = geotop_convex_hull W'', W'' \<subseteq> V_\<sigma>. **)
      obtain V\<sigma> W'' where hV\<sigma>_sv: "geotop_simplex_vertices \<sigma> V\<sigma>"
                       and hW''_ne: "W'' \<noteq> {}" and hW''_V\<sigma>: "W'' \<subseteq> V\<sigma>"
                       and he_hull'': "e = geotop_convex_hull W''"
        using h_face_e_of_\<sigma> unfolding geotop_is_face_def by (by100 blast)
      (** |V_\<sigma>| \<le> 2 by 1-dim bound. **)
      have h\<sigma>_1dim: "\<exists>n\<le>1. geotop_simplex_dim \<sigma> n"
        using hK1dim h\<sigma>_K unfolding geotop_complex_is_1dim_def by (by100 blast)
      obtain n\<sigma> where hn\<sigma>_le: "n\<sigma> \<le> 1" and h\<sigma>_dim: "geotop_simplex_dim \<sigma> n\<sigma>"
        using h\<sigma>_1dim by (by100 blast)
      obtain V\<sigma>' m\<sigma> where hV\<sigma>'_fin: "finite V\<sigma>'" and hV\<sigma>'_card: "card V\<sigma>' = n\<sigma> + 1"
                     and hnm\<sigma>: "n\<sigma> \<le> m\<sigma>" and hV\<sigma>'_gp: "geotop_general_position V\<sigma>' m\<sigma>"
                     and h\<sigma>_hull: "\<sigma> = geotop_convex_hull V\<sigma>'"
        using h\<sigma>_dim unfolding geotop_simplex_dim_def by (by100 blast)
      have hV\<sigma>'_sv: "geotop_simplex_vertices \<sigma> V\<sigma>'"
        unfolding geotop_simplex_vertices_def
        using hV\<sigma>'_fin hV\<sigma>'_card hnm\<sigma> hV\<sigma>'_gp h\<sigma>_hull by (by100 blast)
      have hV\<sigma>_eq: "V\<sigma> = V\<sigma>'"
        by (rule geotop_simplex_vertices_unique[OF hV\<sigma>_sv hV\<sigma>'_sv])
      have hV\<sigma>_card: "card V\<sigma> \<le> 2" using hV\<sigma>'_card hn\<sigma>_le hV\<sigma>_eq by (by100 simp)
      have hW''_fin: "finite W''" using hW''_V\<sigma> hV\<sigma>_eq hV\<sigma>'_fin finite_subset by (by100 blast)
      have hW''_card: "card W'' \<le> 2"
        using card_mono[OF _ hW''_V\<sigma>] hV\<sigma>'_fin hV\<sigma>_eq hV\<sigma>_card by (by100 simp)
      have hW''_card_ne0: "card W'' \<noteq> 0"
      proof
        assume "card W'' = 0"
        hence "W'' = {}" using hW''_fin card_0_eq by (by100 blast)
        thus False using hW''_ne by (by100 blast)
      qed
      have hW''_card_ge1: "card W'' \<ge> 1" using hW''_card_ne0 by (by100 simp)
      have hW''_cases: "card W'' = 1 \<or> card W'' = 2"
        using hW''_card hW''_card_ge1 by (by100 linarith)
      (** If |W''| = 1, e = {w}, contradicting v0,v1 distinct both in e. **)
      have h_contra: False
      proof (rule disjE[OF hW''_cases])
        assume hc1: "card W'' = 1"
        have "\<exists>w. W'' = {w}" using hc1 card_1_singletonE by (by100 metis)
        then obtain w where hW''_w: "W'' = {w}" by (by100 blast)
        have he_sing: "e = {w}"
        proof -
          have "e = geotop_convex_hull {w}" using he_hull'' hW''_w by (by100 simp)
          also have "\<dots> = convex hull {w}" by (rule geotop_convex_hull_eq_HOL)
          also have "\<dots> = {w}" by (by100 simp)
          finally show ?thesis .
        qed
        have hv0_e: "v\<^sub>0 \<in> e"
        proof -
          have hv0_V: "v\<^sub>0 \<in> V" using hVeq by (by100 simp)
          have hV_hull: "V \<subseteq> convex hull V" by (rule hull_subset)
          have hv0_cvx: "v\<^sub>0 \<in> convex hull V" using hv0_V hV_hull by (by100 blast)
          have he_V: "e = geotop_convex_hull V"
            using hV_verts unfolding geotop_simplex_vertices_def by (by100 blast)
          have he_HOL: "e = convex hull V"
            using he_V geotop_convex_hull_eq_HOL by (by100 simp)
          show ?thesis using hv0_cvx he_HOL by (by100 simp)
        qed
        have hv1_e: "v\<^sub>1 \<in> e"
        proof -
          have hv1_V: "v\<^sub>1 \<in> V" using hVeq by (by100 simp)
          have hV_hull: "V \<subseteq> convex hull V" by (rule hull_subset)
          have hv1_cvx: "v\<^sub>1 \<in> convex hull V" using hv1_V hV_hull by (by100 blast)
          have he_V: "e = geotop_convex_hull V"
            using hV_verts unfolding geotop_simplex_vertices_def by (by100 blast)
          have he_HOL: "e = convex hull V"
            using he_V geotop_convex_hull_eq_HOL by (by100 simp)
          show ?thesis using hv1_cvx he_HOL by (by100 simp)
        qed
        have "v\<^sub>0 = w" using hv0_e he_sing by (by100 blast)
        moreover have "v\<^sub>1 = w" using hv1_e he_sing by (by100 blast)
        ultimately have "v\<^sub>0 = v\<^sub>1" by (by100 simp)
        thus False using hv01_ne by (by100 blast)
      next
        assume hc2: "card W'' = 2"
        have hV\<sigma>_card_eq2: "card V\<sigma> = 2"
          using hc2 card_mono[OF _ hW''_V\<sigma>] hV\<sigma>'_fin hV\<sigma>_eq hV\<sigma>_card by (by100 simp)
        have hV\<sigma>'_fin': "finite V\<sigma>" using hV\<sigma>'_fin hV\<sigma>_eq by (by100 simp)
        have hW''_eq_V\<sigma>: "W'' = V\<sigma>"
        proof -
          have h_card_eq: "card W'' = card V\<sigma>" using hc2 hV\<sigma>_card_eq2 by (by100 simp)
          show ?thesis by (rule card_subset_eq[OF hV\<sigma>'_fin' hW''_V\<sigma> h_card_eq])
        qed
        have he_\<sigma>: "e = \<sigma>"
        proof -
          have "e = geotop_convex_hull V\<sigma>" using he_hull'' hW''_eq_V\<sigma> by (by100 simp)
          also have "\<dots> = geotop_convex_hull V\<sigma>'" using hV\<sigma>_eq by (by100 simp)
          also have "\<dots> = \<sigma>" using h\<sigma>_hull by (by100 simp)
          finally show ?thesis .
        qed
        show False using he_\<sigma> h\<sigma>_ne_e by (by100 blast)
      qed
      show ?thesis using h_contra by (by100 blast)
    qed
  qed
qed

(** Phase 1.1 helper — K.2 (intersection is face of both) for K'.
    Classical case analysis: 4x4 matrix over {K-{e}, {R}, e_l, e_r}. **)
lemma geotop_subdivide_edge_inter_face:
  fixes K :: "'a::euclidean_space set set"
  assumes hKcomp: "geotop_is_complex K"
  assumes hK1dim: "geotop_complex_is_1dim K"
  assumes he_K: "e \<in> K"
  assumes hV_verts: "geotop_simplex_vertices e V"
  assumes hVeq: "V = {v\<^sub>0, v\<^sub>1}" and hv01_ne: "v\<^sub>0 \<noteq> v\<^sub>1"
  assumes hR_e: "R \<in> e" and hR_V: "R \<notin> V"
  shows "\<forall>\<sigma>\<in>(K - {e}) \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}.
         \<forall>\<tau>\<in>(K - {e}) \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}.
         \<sigma> \<inter> \<tau> \<noteq> {}
         \<longrightarrow> geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
proof (intro ballI impI)
  fix \<sigma> \<tau>
  let ?el = "closed_segment v\<^sub>0 R"
  let ?er = "closed_segment R v\<^sub>1"
  let ?K' = "(K - {e}) \<union> {{R}, ?el, ?er}"
  assume h\<sigma>: "\<sigma> \<in> ?K'"
  assume h\<tau>: "\<tau> \<in> ?K'"
  assume hne: "\<sigma> \<inter> \<tau> \<noteq> {}"
  (** Derived facts. **)
  have hR_v0: "R \<noteq> v\<^sub>0" using hR_V hVeq by (by100 simp)
  have hR_v1: "R \<noteq> v\<^sub>1" using hR_V hVeq by (by100 simp)
  have hK_inter_face: "\<forall>\<sigma>'\<in>K. \<forall>\<tau>'\<in>K. \<sigma>' \<inter> \<tau>' \<noteq> {} \<longrightarrow>
                      geotop_is_face (\<sigma>' \<inter> \<tau>') \<sigma>' \<and> geotop_is_face (\<sigma>' \<inter> \<tau>') \<tau>'"
    using conjunct1[OF conjunct2[OF conjunct2[OF hKcomp[unfolded geotop_is_complex_def]]]]
    by (by100 blast)
  show "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
  proof (rule UnE[OF h\<sigma>])
    assume h\<sigma>_old: "\<sigma> \<in> K - {e}"
    have h\<sigma>_K: "\<sigma> \<in> K" using h\<sigma>_old by (by100 simp)
    show "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    proof (rule UnE[OF h\<tau>])
      assume h\<tau>_old: "\<tau> \<in> K - {e}"
      have h\<tau>_K: "\<tau> \<in> K" using h\<tau>_old by (by100 simp)
      show "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
        using hK_inter_face h\<sigma>_K h\<tau>_K hne by (by100 blast)
    next
      assume h\<tau>_new: "\<tau> \<in> {{R}, ?el, ?er}"
      (** Cross case old × new. σ ∈ K-{e}, τ new. Use sigma_cap_e_cases. **)
      have h\<tau>_disj: "\<tau> = {R} \<or> \<tau> = ?el \<or> \<tau> = ?er" using h\<tau>_new by (by100 simp)
      (** Derived geometric facts. **)
      have he_V_hull: "e = geotop_convex_hull V"
        using hV_verts unfolding geotop_simplex_vertices_def by (by100 blast)
      have he_HOL: "e = convex hull V"
        using he_V_hull geotop_convex_hull_eq_HOL by (by100 simp)
      have he_cs: "e = closed_segment v\<^sub>0 v\<^sub>1"
      proof -
        have h1: "e = convex hull {v\<^sub>0, v\<^sub>1}" using he_HOL hVeq by (by100 simp)
        have h2: "convex hull {v\<^sub>0, v\<^sub>1} = closed_segment v\<^sub>0 v\<^sub>1"
          by (rule segment_convex_hull[symmetric])
        show ?thesis using h1 h2 by (by100 simp)
      qed
      have hR_cs: "R \<in> closed_segment v\<^sub>0 v\<^sub>1" using hR_e he_cs by (by100 simp)
      have hv0_cs: "v\<^sub>0 \<in> closed_segment v\<^sub>0 v\<^sub>1" by (by100 simp)
      have hv1_cs: "v\<^sub>1 \<in> closed_segment v\<^sub>0 v\<^sub>1" by (by100 simp)
      have hel_sub: "?el \<subseteq> closed_segment v\<^sub>0 v\<^sub>1"
        using hv0_cs hR_cs subset_closed_segment by (by100 blast)
      have hel_sub_e: "?el \<subseteq> e" using hel_sub he_cs by (by100 simp)
      have her_sub: "?er \<subseteq> closed_segment v\<^sub>0 v\<^sub>1"
        using hR_cs hv1_cs subset_closed_segment by (by100 blast)
      have her_sub_e: "?er \<subseteq> e" using her_sub he_cs by (by100 simp)
      have h_v0_notin_er: "v\<^sub>0 \<notin> ?er"
        by (rule geotop_subdivide_edge_v0_notin_er[OF hR_cs hR_v0])
      have h_v1_notin_el: "v\<^sub>1 \<notin> ?el"
        by (rule geotop_subdivide_edge_v1_notin_el[OF hR_cs hR_v1])
      have hv0R_ne: "v\<^sub>0 \<noteq> R" using hR_v0 by (by100 blast)
      have hRv1_ne: "R \<noteq> v\<^sub>1" using hR_v1 by (by100 blast)
      (** σ ∩ e classification. **)
      have h_cap_cases: "\<sigma> \<inter> e = {} \<or> \<sigma> \<inter> e = {v\<^sub>0} \<or> \<sigma> \<inter> e = {v\<^sub>1}"
        by (rule geotop_subdivide_edge_sigma_cap_e_cases
                 [OF hKcomp hK1dim he_K hV_verts hVeq hv01_ne h\<sigma>_old])
      (** K.2 of K applied to σ, e gives is_face (σ∩e) σ (when σ∩e ≠ {}). **)
      have h_face_sigma_cap_e:
        "\<sigma> \<inter> e \<noteq> {} \<Longrightarrow> geotop_is_face (\<sigma> \<inter> e) \<sigma>"
        using hK_inter_face h\<sigma>_K he_K by (by100 blast)
      show "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
      proof (rule disjE[OF h\<tau>_disj])
        assume h\<tau>_R: "\<tau> = {R}"
        (** σ ∩ {R} = {R} (since hne). So R ∈ σ ∩ e. But σ ∩ e ∈ {{},{v₀},{v₁}} and R ∉ {v₀,v₁}. Contradiction. **)
        have h_int_R: "\<sigma> \<inter> \<tau> = \<sigma> \<inter> {R}" using h\<tau>_R by (by100 simp)
        have hR_sigma: "R \<in> \<sigma>"
        proof -
          have "\<sigma> \<inter> {R} \<noteq> {}" using hne h_int_R by (by100 simp)
          thus ?thesis by (by100 blast)
        qed
        have hR_sigma_e: "R \<in> \<sigma> \<inter> e" using hR_sigma hR_e by (by100 blast)
        have h_contra: False
        proof (rule disjE[OF h_cap_cases])
          assume "\<sigma> \<inter> e = {}"
          thus False using hR_sigma_e by (by100 blast)
        next
          assume h_rest: "\<sigma> \<inter> e = {v\<^sub>0} \<or> \<sigma> \<inter> e = {v\<^sub>1}"
          show False
          proof (rule disjE[OF h_rest])
            assume h_v0: "\<sigma> \<inter> e = {v\<^sub>0}"
            have "R = v\<^sub>0" using hR_sigma_e h_v0 by (by100 blast)
            thus False using hR_v0 by (by100 blast)
          next
            assume h_v1: "\<sigma> \<inter> e = {v\<^sub>1}"
            have "R = v\<^sub>1" using hR_sigma_e h_v1 by (by100 blast)
            thus False using hR_v1 by (by100 blast)
          qed
        qed
        show ?thesis using h_contra by (by100 blast)
      next
        assume h\<tau>_rest: "\<tau> = ?el \<or> \<tau> = ?er"
        show ?thesis
        proof (rule disjE[OF h\<tau>_rest])
          assume h\<tau>_el: "\<tau> = ?el"
          (** σ ∩ ?el ⊆ σ ∩ e. σ ∩ ?el ≠ {} ⟹ σ ∩ e ≠ {} ⟹ σ ∩ e ∈ {{v₀},{v₁}}.
              If {v₁}: σ ∩ ?el ⊆ {v₁} ∩ ?el = {} (v₁ ∉ ?el), contradicting hne.
              So σ ∩ e = {v₀}, and σ ∩ ?el = {v₀}. **)
          have h_cap_sub: "\<sigma> \<inter> ?el \<subseteq> \<sigma> \<inter> e" using hel_sub_e by (by100 blast)
          have hne_cap_el: "\<sigma> \<inter> ?el \<noteq> {}" using hne h\<tau>_el by (by100 simp)
          have h_cap_v0: "\<sigma> \<inter> e = {v\<^sub>0}"
          proof (rule disjE[OF h_cap_cases])
            assume "\<sigma> \<inter> e = {}"
            hence "\<sigma> \<inter> ?el = {}" using h_cap_sub by (by100 blast)
            thus ?thesis using hne_cap_el by (by100 blast)
          next
            assume h_rest2: "\<sigma> \<inter> e = {v\<^sub>0} \<or> \<sigma> \<inter> e = {v\<^sub>1}"
            show ?thesis
            proof (rule disjE[OF h_rest2])
              assume h_v0: "\<sigma> \<inter> e = {v\<^sub>0}"
              show ?thesis by (rule h_v0)
            next
              assume h_v1: "\<sigma> \<inter> e = {v\<^sub>1}"
              have "\<sigma> \<inter> ?el \<subseteq> {v\<^sub>1}" using h_cap_sub h_v1 by (by100 blast)
              have h_cap_el_sub_el: "\<sigma> \<inter> ?el \<subseteq> ?el" by (by100 blast)
              have "\<sigma> \<inter> ?el \<subseteq> {v\<^sub>1} \<inter> ?el" using h_cap_sub h_v1 h_cap_el_sub_el by (by100 blast)
              hence "\<sigma> \<inter> ?el = {}" using h_v1_notin_el by (by100 blast)
              thus ?thesis using hne_cap_el by (by100 blast)
            qed
          qed
          have hv0_sigma: "v\<^sub>0 \<in> \<sigma>" using h_cap_v0 by (by100 blast)
          have hv0_el: "v\<^sub>0 \<in> ?el" by (by100 simp)
          have h_int_v0: "\<sigma> \<inter> \<tau> = {v\<^sub>0}"
          proof -
            have h_sub_v0: "\<sigma> \<inter> \<tau> \<subseteq> {v\<^sub>0}"
            proof -
              have "\<sigma> \<inter> \<tau> \<subseteq> \<sigma> \<inter> e" using h\<tau>_el hel_sub_e by (by100 blast)
              thus ?thesis using h_cap_v0 by (by100 simp)
            qed
            have h_v0_in: "v\<^sub>0 \<in> \<sigma> \<inter> \<tau>" using hv0_sigma hv0_el h\<tau>_el by (by100 simp)
            show ?thesis using h_sub_v0 h_v0_in by (by100 blast)
          qed
          have h_face_v0_sigma: "geotop_is_face {v\<^sub>0} \<sigma>"
          proof -
            have h_ne_cap_e: "\<sigma> \<inter> e \<noteq> {}" using h_cap_v0 by (by100 simp)
            have h_face: "geotop_is_face (\<sigma> \<inter> e) \<sigma>"
              using h_face_sigma_cap_e h_ne_cap_e by (by100 blast)
            show ?thesis using h_face h_cap_v0 by (by100 simp)
          qed
          have h_face_v0_el: "geotop_is_face {v\<^sub>0} ?el"
            by (rule geotop_closed_segment_is_face_endpoint[OF hv0R_ne]) (by100 simp)
          show ?thesis using h_int_v0 h\<tau>_el h_face_v0_sigma h_face_v0_el by (by100 simp)
        next
          assume h\<tau>_er: "\<tau> = ?er"
          (** Symmetric: σ ∩ e = {v₁}, σ ∩ ?er = {v₁}. **)
          have h_cap_sub: "\<sigma> \<inter> ?er \<subseteq> \<sigma> \<inter> e" using her_sub_e by (by100 blast)
          have hne_cap_er: "\<sigma> \<inter> ?er \<noteq> {}" using hne h\<tau>_er by (by100 simp)
          have h_cap_v1: "\<sigma> \<inter> e = {v\<^sub>1}"
          proof (rule disjE[OF h_cap_cases])
            assume "\<sigma> \<inter> e = {}"
            hence "\<sigma> \<inter> ?er = {}" using h_cap_sub by (by100 blast)
            thus ?thesis using hne_cap_er by (by100 blast)
          next
            assume h_rest2: "\<sigma> \<inter> e = {v\<^sub>0} \<or> \<sigma> \<inter> e = {v\<^sub>1}"
            show ?thesis
            proof (rule disjE[OF h_rest2])
              assume h_v0: "\<sigma> \<inter> e = {v\<^sub>0}"
              have h_cap_er_sub_er: "\<sigma> \<inter> ?er \<subseteq> ?er" by (by100 blast)
              have "\<sigma> \<inter> ?er \<subseteq> {v\<^sub>0} \<inter> ?er" using h_cap_sub h_v0 h_cap_er_sub_er by (by100 blast)
              hence "\<sigma> \<inter> ?er = {}" using h_v0_notin_er by (by100 blast)
              thus ?thesis using hne_cap_er by (by100 blast)
            next
              assume h_v1: "\<sigma> \<inter> e = {v\<^sub>1}"
              show ?thesis by (rule h_v1)
            qed
          qed
          have hv1_sigma: "v\<^sub>1 \<in> \<sigma>" using h_cap_v1 by (by100 blast)
          have hv1_er: "v\<^sub>1 \<in> ?er" by (by100 simp)
          have h_int_v1: "\<sigma> \<inter> \<tau> = {v\<^sub>1}"
          proof -
            have h_sub_v1: "\<sigma> \<inter> \<tau> \<subseteq> {v\<^sub>1}"
            proof -
              have "\<sigma> \<inter> \<tau> \<subseteq> \<sigma> \<inter> e" using h\<tau>_er her_sub_e by (by100 blast)
              thus ?thesis using h_cap_v1 by (by100 simp)
            qed
            have h_v1_in: "v\<^sub>1 \<in> \<sigma> \<inter> \<tau>" using hv1_sigma hv1_er h\<tau>_er by (by100 simp)
            show ?thesis using h_sub_v1 h_v1_in by (by100 blast)
          qed
          have h_face_v1_sigma: "geotop_is_face {v\<^sub>1} \<sigma>"
          proof -
            have h_ne_cap_e: "\<sigma> \<inter> e \<noteq> {}" using h_cap_v1 by (by100 simp)
            have h_face: "geotop_is_face (\<sigma> \<inter> e) \<sigma>"
              using h_face_sigma_cap_e h_ne_cap_e by (by100 blast)
            show ?thesis using h_face h_cap_v1 by (by100 simp)
          qed
          have h_face_v1_er: "geotop_is_face {v\<^sub>1} ?er"
            by (rule geotop_closed_segment_is_face_endpoint[OF hRv1_ne]) (by100 simp)
          show ?thesis using h_int_v1 h\<tau>_er h_face_v1_sigma h_face_v1_er by (by100 simp)
        qed
      qed
    qed
  next
    assume h\<sigma>_new: "\<sigma> \<in> {{R}, ?el, ?er}"
    show "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    proof (rule UnE[OF h\<tau>])
      assume h\<tau>_old: "\<tau> \<in> K - {e}"
      (** Cross case new × old: symmetric to old × new; swap σ ↔ τ in the argument. **)
      have h\<tau>_K: "\<tau> \<in> K" using h\<tau>_old by (by100 simp)
      have h\<sigma>_disj: "\<sigma> = {R} \<or> \<sigma> = ?el \<or> \<sigma> = ?er" using h\<sigma>_new by (by100 simp)
      (** Derived geometric facts (copy of old × new block). **)
      have he_V_hull: "e = geotop_convex_hull V"
        using hV_verts unfolding geotop_simplex_vertices_def by (by100 blast)
      have he_HOL: "e = convex hull V"
        using he_V_hull geotop_convex_hull_eq_HOL by (by100 simp)
      have he_cs: "e = closed_segment v\<^sub>0 v\<^sub>1"
      proof -
        have h1: "e = convex hull {v\<^sub>0, v\<^sub>1}" using he_HOL hVeq by (by100 simp)
        have h2: "convex hull {v\<^sub>0, v\<^sub>1} = closed_segment v\<^sub>0 v\<^sub>1"
          by (rule segment_convex_hull[symmetric])
        show ?thesis using h1 h2 by (by100 simp)
      qed
      have hR_cs: "R \<in> closed_segment v\<^sub>0 v\<^sub>1" using hR_e he_cs by (by100 simp)
      have hv0_cs: "v\<^sub>0 \<in> closed_segment v\<^sub>0 v\<^sub>1" by (by100 simp)
      have hv1_cs: "v\<^sub>1 \<in> closed_segment v\<^sub>0 v\<^sub>1" by (by100 simp)
      have hel_sub: "?el \<subseteq> closed_segment v\<^sub>0 v\<^sub>1"
        using hv0_cs hR_cs subset_closed_segment by (by100 blast)
      have hel_sub_e: "?el \<subseteq> e" using hel_sub he_cs by (by100 simp)
      have her_sub: "?er \<subseteq> closed_segment v\<^sub>0 v\<^sub>1"
        using hR_cs hv1_cs subset_closed_segment by (by100 blast)
      have her_sub_e: "?er \<subseteq> e" using her_sub he_cs by (by100 simp)
      have h_v0_notin_er: "v\<^sub>0 \<notin> ?er"
        by (rule geotop_subdivide_edge_v0_notin_er[OF hR_cs hR_v0])
      have h_v1_notin_el: "v\<^sub>1 \<notin> ?el"
        by (rule geotop_subdivide_edge_v1_notin_el[OF hR_cs hR_v1])
      have hv0R_ne: "v\<^sub>0 \<noteq> R" using hR_v0 by (by100 blast)
      have hRv1_ne: "R \<noteq> v\<^sub>1" using hR_v1 by (by100 blast)
      have h_cap_cases: "\<tau> \<inter> e = {} \<or> \<tau> \<inter> e = {v\<^sub>0} \<or> \<tau> \<inter> e = {v\<^sub>1}"
        by (rule geotop_subdivide_edge_sigma_cap_e_cases
                 [OF hKcomp hK1dim he_K hV_verts hVeq hv01_ne h\<tau>_old])
      have h_face_tau_cap_e:
        "\<tau> \<inter> e \<noteq> {} \<Longrightarrow> geotop_is_face (\<tau> \<inter> e) \<tau>"
        using hK_inter_face h\<tau>_K he_K by (by100 blast)
      show "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
      proof (rule disjE[OF h\<sigma>_disj])
        assume h\<sigma>_R: "\<sigma> = {R}"
        have h_int_R: "\<sigma> \<inter> \<tau> = {R} \<inter> \<tau>" using h\<sigma>_R by (by100 simp)
        have hR_tau: "R \<in> \<tau>"
        proof -
          have "{R} \<inter> \<tau> \<noteq> {}" using hne h_int_R by (by100 simp)
          thus ?thesis by (by100 blast)
        qed
        have hR_tau_e: "R \<in> \<tau> \<inter> e" using hR_tau hR_e by (by100 blast)
        have h_contra: False
        proof (rule disjE[OF h_cap_cases])
          assume "\<tau> \<inter> e = {}"
          thus False using hR_tau_e by (by100 blast)
        next
          assume h_rest: "\<tau> \<inter> e = {v\<^sub>0} \<or> \<tau> \<inter> e = {v\<^sub>1}"
          show False
          proof (rule disjE[OF h_rest])
            assume h_v0: "\<tau> \<inter> e = {v\<^sub>0}"
            have "R = v\<^sub>0" using hR_tau_e h_v0 by (by100 blast)
            thus False using hR_v0 by (by100 blast)
          next
            assume h_v1: "\<tau> \<inter> e = {v\<^sub>1}"
            have "R = v\<^sub>1" using hR_tau_e h_v1 by (by100 blast)
            thus False using hR_v1 by (by100 blast)
          qed
        qed
        show ?thesis using h_contra by (by100 blast)
      next
        assume h\<sigma>_rest: "\<sigma> = ?el \<or> \<sigma> = ?er"
        show ?thesis
        proof (rule disjE[OF h\<sigma>_rest])
          assume h\<sigma>_el: "\<sigma> = ?el"
          have h_cap_sub: "?el \<inter> \<tau> \<subseteq> e \<inter> \<tau>" using hel_sub_e by (by100 blast)
          have hne_cap_el: "?el \<inter> \<tau> \<noteq> {}" using hne h\<sigma>_el by (by100 simp)
          have h_tau_cap_v0: "\<tau> \<inter> e = {v\<^sub>0}"
          proof (rule disjE[OF h_cap_cases])
            assume h0: "\<tau> \<inter> e = {}"
            hence "e \<inter> \<tau> = {}" by (by100 blast)
            hence "?el \<inter> \<tau> = {}" using h_cap_sub by (by100 blast)
            thus ?thesis using hne_cap_el by (by100 blast)
          next
            assume h_rest2: "\<tau> \<inter> e = {v\<^sub>0} \<or> \<tau> \<inter> e = {v\<^sub>1}"
            show ?thesis
            proof (rule disjE[OF h_rest2])
              assume h_v0: "\<tau> \<inter> e = {v\<^sub>0}" thus ?thesis by (by100 simp)
            next
              assume h_v1: "\<tau> \<inter> e = {v\<^sub>1}"
              have h_el_sub_self: "?el \<inter> \<tau> \<subseteq> ?el" by (by100 blast)
              have "?el \<inter> \<tau> \<subseteq> ?el \<inter> {v\<^sub>1}" using h_cap_sub h_v1 h_el_sub_self by (by100 blast)
              hence "?el \<inter> \<tau> = {}" using h_v1_notin_el by (by100 blast)
              thus ?thesis using hne_cap_el by (by100 blast)
            qed
          qed
          have hv0_tau: "v\<^sub>0 \<in> \<tau>" using h_tau_cap_v0 by (by100 blast)
          have hv0_el: "v\<^sub>0 \<in> ?el" by (by100 simp)
          have h_int_v0: "\<sigma> \<inter> \<tau> = {v\<^sub>0}"
          proof -
            have h_sub: "\<sigma> \<inter> \<tau> \<subseteq> {v\<^sub>0}"
            proof -
              have "\<sigma> \<inter> \<tau> \<subseteq> e \<inter> \<tau>" using h\<sigma>_el hel_sub_e by (by100 blast)
              thus ?thesis using h_tau_cap_v0 by (by100 blast)
            qed
            have h_in: "v\<^sub>0 \<in> \<sigma> \<inter> \<tau>" using hv0_tau hv0_el h\<sigma>_el by (by100 simp)
            show ?thesis using h_sub h_in by (by100 blast)
          qed
          have h_face_v0_tau: "geotop_is_face {v\<^sub>0} \<tau>"
          proof -
            have h_ne_cap_e: "\<tau> \<inter> e \<noteq> {}" using h_tau_cap_v0 by (by100 simp)
            have h_face: "geotop_is_face (\<tau> \<inter> e) \<tau>"
              using h_face_tau_cap_e h_ne_cap_e by (by100 blast)
            show ?thesis using h_face h_tau_cap_v0 by (by100 simp)
          qed
          have h_face_v0_el: "geotop_is_face {v\<^sub>0} ?el"
            by (rule geotop_closed_segment_is_face_endpoint[OF hv0R_ne]) (by100 simp)
          show ?thesis using h_int_v0 h\<sigma>_el h_face_v0_el h_face_v0_tau by (by100 simp)
        next
          assume h\<sigma>_er: "\<sigma> = ?er"
          have h_cap_sub: "?er \<inter> \<tau> \<subseteq> e \<inter> \<tau>" using her_sub_e by (by100 blast)
          have hne_cap_er: "?er \<inter> \<tau> \<noteq> {}" using hne h\<sigma>_er by (by100 simp)
          have h_tau_cap_v1: "\<tau> \<inter> e = {v\<^sub>1}"
          proof (rule disjE[OF h_cap_cases])
            assume h0: "\<tau> \<inter> e = {}"
            hence "e \<inter> \<tau> = {}" by (by100 blast)
            hence "?er \<inter> \<tau> = {}" using h_cap_sub by (by100 blast)
            thus ?thesis using hne_cap_er by (by100 blast)
          next
            assume h_rest2: "\<tau> \<inter> e = {v\<^sub>0} \<or> \<tau> \<inter> e = {v\<^sub>1}"
            show ?thesis
            proof (rule disjE[OF h_rest2])
              assume h_v0: "\<tau> \<inter> e = {v\<^sub>0}"
              have h_er_sub_self: "?er \<inter> \<tau> \<subseteq> ?er" by (by100 blast)
              have "?er \<inter> \<tau> \<subseteq> ?er \<inter> {v\<^sub>0}" using h_cap_sub h_v0 h_er_sub_self by (by100 blast)
              hence "?er \<inter> \<tau> = {}" using h_v0_notin_er by (by100 blast)
              thus ?thesis using hne_cap_er by (by100 blast)
            next
              assume h_v1: "\<tau> \<inter> e = {v\<^sub>1}" thus ?thesis by (by100 simp)
            qed
          qed
          have hv1_tau: "v\<^sub>1 \<in> \<tau>" using h_tau_cap_v1 by (by100 blast)
          have hv1_er: "v\<^sub>1 \<in> ?er" by (by100 simp)
          have h_int_v1: "\<sigma> \<inter> \<tau> = {v\<^sub>1}"
          proof -
            have h_sub: "\<sigma> \<inter> \<tau> \<subseteq> {v\<^sub>1}"
            proof -
              have "\<sigma> \<inter> \<tau> \<subseteq> e \<inter> \<tau>" using h\<sigma>_er her_sub_e by (by100 blast)
              thus ?thesis using h_tau_cap_v1 by (by100 blast)
            qed
            have h_in: "v\<^sub>1 \<in> \<sigma> \<inter> \<tau>" using hv1_tau hv1_er h\<sigma>_er by (by100 simp)
            show ?thesis using h_sub h_in by (by100 blast)
          qed
          have h_face_v1_tau: "geotop_is_face {v\<^sub>1} \<tau>"
          proof -
            have h_ne_cap_e: "\<tau> \<inter> e \<noteq> {}" using h_tau_cap_v1 by (by100 simp)
            have h_face: "geotop_is_face (\<tau> \<inter> e) \<tau>"
              using h_face_tau_cap_e h_ne_cap_e by (by100 blast)
            show ?thesis using h_face h_tau_cap_v1 by (by100 simp)
          qed
          have h_face_v1_er: "geotop_is_face {v\<^sub>1} ?er"
            by (rule geotop_closed_segment_is_face_endpoint[OF hRv1_ne]) (by100 simp)
          show ?thesis using h_int_v1 h\<sigma>_er h_face_v1_er h_face_v1_tau by (by100 simp)
        qed
      qed
    next
      assume h\<tau>_new: "\<tau> \<in> {{R}, ?el, ?er}"
      (** New × new: 3×3 enumerable. **)
      have h\<sigma>_disj: "\<sigma> = {R} \<or> \<sigma> = ?el \<or> \<sigma> = ?er" using h\<sigma>_new by (by100 simp)
      have h\<tau>_disj: "\<tau> = {R} \<or> \<tau> = ?el \<or> \<tau> = ?er" using h\<tau>_new by (by100 simp)
      (** Derived geometric facts. **)
      have he_V_hull: "e = geotop_convex_hull V"
        using hV_verts unfolding geotop_simplex_vertices_def by (by100 blast)
      have he_HOL: "e = convex hull V"
        using he_V_hull geotop_convex_hull_eq_HOL by (by100 simp)
      have he_cs: "e = closed_segment v\<^sub>0 v\<^sub>1"
      proof -
        have h1: "e = convex hull {v\<^sub>0, v\<^sub>1}" using he_HOL hVeq by (by100 simp)
        have h2: "convex hull {v\<^sub>0, v\<^sub>1} = closed_segment v\<^sub>0 v\<^sub>1"
          by (rule segment_convex_hull[symmetric])
        show ?thesis using h1 h2 by (by100 simp)
      qed
      have hR_cs: "R \<in> closed_segment v\<^sub>0 v\<^sub>1" using hR_e he_cs by (by100 simp)
      have h_el_er: "?el \<inter> ?er = {R}"
        by (rule geotop_subdivide_edge_el_inter_er[OF hR_cs])
      have hR_el: "R \<in> ?el" by (by100 simp)
      have hR_er: "R \<in> ?er" by (by100 simp)
      (** Face facts. **)
      have h_R_R: "geotop_is_face {R} {R}" by (rule geotop_singleton_is_face_self)
      have hv0R_ne: "v\<^sub>0 \<noteq> R" using hR_v0 by (by100 blast)
      have hRv1_ne: "R \<noteq> v\<^sub>1" using hR_v1 by (by100 blast)
      have h_R_el: "geotop_is_face {R} ?el"
        by (rule geotop_closed_segment_is_face_endpoint[OF hv0R_ne]) (by100 simp)
      have h_R_er: "geotop_is_face {R} ?er"
        by (rule geotop_closed_segment_is_face_endpoint[OF hRv1_ne]) (by100 simp)
      have h_el_self: "geotop_is_face ?el ?el"
        by (rule geotop_closed_segment_is_face_self[OF hv0R_ne])
      have h_er_self: "geotop_is_face ?er ?er"
        by (rule geotop_closed_segment_is_face_self[OF hRv1_ne])
      show "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
      proof (rule disjE[OF h\<sigma>_disj])
        assume h\<sigma>_R: "\<sigma> = {R}"
        show ?thesis
        proof (rule disjE[OF h\<tau>_disj])
          assume h\<tau>_R: "\<tau> = {R}"
          have h_int: "\<sigma> \<inter> \<tau> = {R}" using h\<sigma>_R h\<tau>_R by (by100 simp)
          show ?thesis using h_int h\<sigma>_R h\<tau>_R h_R_R by (by100 simp)
        next
          assume h\<tau>_rest: "\<tau> = ?el \<or> \<tau> = ?er"
          show ?thesis
          proof (rule disjE[OF h\<tau>_rest])
            assume h\<tau>_el: "\<tau> = ?el"
            have h_int: "\<sigma> \<inter> \<tau> = {R}" using h\<sigma>_R h\<tau>_el hR_el by (by100 simp)
            show ?thesis using h_int h\<sigma>_R h\<tau>_el h_R_R h_R_el by (by100 simp)
          next
            assume h\<tau>_er: "\<tau> = ?er"
            have h_int: "\<sigma> \<inter> \<tau> = {R}" using h\<sigma>_R h\<tau>_er hR_er by (by100 simp)
            show ?thesis using h_int h\<sigma>_R h\<tau>_er h_R_R h_R_er by (by100 simp)
          qed
        qed
      next
        assume h\<sigma>_rest: "\<sigma> = ?el \<or> \<sigma> = ?er"
        show ?thesis
        proof (rule disjE[OF h\<sigma>_rest])
          assume h\<sigma>_el: "\<sigma> = ?el"
          show ?thesis
          proof (rule disjE[OF h\<tau>_disj])
            assume h\<tau>_R: "\<tau> = {R}"
            have h_int: "\<sigma> \<inter> \<tau> = {R}" using h\<sigma>_el h\<tau>_R hR_el by (by100 simp)
            show ?thesis using h_int h\<sigma>_el h\<tau>_R h_R_el h_R_R by (by100 simp)
          next
            assume h\<tau>_rest: "\<tau> = ?el \<or> \<tau> = ?er"
            show ?thesis
            proof (rule disjE[OF h\<tau>_rest])
              assume h\<tau>_el: "\<tau> = ?el"
              have h_int: "\<sigma> \<inter> \<tau> = ?el" using h\<sigma>_el h\<tau>_el by (by100 simp)
              show ?thesis using h_int h\<sigma>_el h\<tau>_el h_el_self by (by100 simp)
            next
              assume h\<tau>_er: "\<tau> = ?er"
              have h_int: "\<sigma> \<inter> \<tau> = {R}" using h\<sigma>_el h\<tau>_er h_el_er by (by100 simp)
              show ?thesis using h_int h\<sigma>_el h\<tau>_er h_R_el h_R_er by (by100 simp)
            qed
          qed
        next
          assume h\<sigma>_er: "\<sigma> = ?er"
          show ?thesis
          proof (rule disjE[OF h\<tau>_disj])
            assume h\<tau>_R: "\<tau> = {R}"
            have h_int: "\<sigma> \<inter> \<tau> = {R}" using h\<sigma>_er h\<tau>_R hR_er by (by100 simp)
            show ?thesis using h_int h\<sigma>_er h\<tau>_R h_R_er h_R_R by (by100 simp)
          next
            assume h\<tau>_rest: "\<tau> = ?el \<or> \<tau> = ?er"
            show ?thesis
            proof (rule disjE[OF h\<tau>_rest])
              assume h\<tau>_el: "\<tau> = ?el"
              have h_el_er_sym: "?er \<inter> ?el = {R}" using h_el_er by (by100 blast)
              have h_int: "\<sigma> \<inter> \<tau> = {R}" using h\<sigma>_er h\<tau>_el h_el_er_sym by (by100 simp)
              show ?thesis using h_int h\<sigma>_er h\<tau>_el h_R_er h_R_el by (by100 simp)
            next
              assume h\<tau>_er: "\<tau> = ?er"
              have h_int: "\<sigma> \<inter> \<tau> = ?er" using h\<sigma>_er h\<tau>_er by (by100 simp)
              show ?thesis using h_int h\<sigma>_er h\<tau>_er h_er_self by (by100 simp)
            qed
          qed
        qed
      qed
    qed
  qed
qed

(** Phase 1.1 helper — K.3 (local finiteness) via finite K'. **)
lemma geotop_subdivide_edge_locfin:
  fixes K :: "'a::euclidean_space set set"
  assumes hK'_fin: "finite K'"
  shows "\<forall>\<sigma>\<in>K'. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K'. \<tau> \<inter> U \<noteq> {}}"
proof
  fix \<sigma> assume h\<sigma>K': "\<sigma> \<in> K'"
  have hopen: "open (UNIV::'a set)" by (by100 simp)
  have hsub: "\<sigma> \<subseteq> UNIV" by (by100 simp)
  have hfin: "finite {\<tau>\<in>K'. \<tau> \<inter> UNIV \<noteq> {}}" using hK'_fin by (by100 simp)
  show "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K'. \<tau> \<inter> U \<noteq> {}}"
    using hopen hsub hfin by (by100 blast)
qed

(** Phase 1.1 helper — K.3 inheritance from K (without finite K).
    For each σ ∈ K', pick an open nbhd U: for σ ∈ K-{e}, use K.3 of K at σ;
    for new simplices, use K.3 of K at e (they sit inside e ⊆ U_e). **)
lemma geotop_subdivide_edge_locfin_inherit:
  fixes K :: "'a::euclidean_space set set"
  assumes hKcomp: "geotop_is_complex K"
  assumes he_K: "e \<in> K"
  assumes hel_sub_e: "closed_segment v\<^sub>0 R \<subseteq> e"
  assumes her_sub_e: "closed_segment R v\<^sub>1 \<subseteq> e"
  assumes hR_e: "R \<in> e"
  shows "\<forall>\<sigma>\<in>(K - {e}) \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}.
           \<exists>U. open U \<and> \<sigma> \<subseteq> U
             \<and> finite {\<tau>\<in>(K - {e}) \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}.
                        \<tau> \<inter> U \<noteq> {}}"
proof
  fix \<sigma>
  assume h\<sigma>: "\<sigma> \<in> (K - {e}) \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
  let ?K' = "(K - {e}) \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
  (** K.3 of K gives a nbhd function. **)
  have hK_locfin: "\<forall>\<tau>\<in>K. \<exists>U. open U \<and> \<tau> \<subseteq> U \<and> finite {\<tau>'\<in>K. \<tau>' \<inter> U \<noteq> {}}"
    using conjunct2[OF conjunct2[OF conjunct2[OF hKcomp[unfolded geotop_is_complex_def]]]]
    by (by100 blast)
  (** Main helper: given any U from K.3 of K (applied to some τ ∈ K),
      {σ ∈ K'. σ ∩ U ≠ {}} is finite. **)
  have h_finite_meet:
    "\<And>U. finite {\<tau>'\<in>K. \<tau>' \<inter> U \<noteq> {}}
        \<Longrightarrow> finite {\<tau>'\<in>?K'. \<tau>' \<inter> U \<noteq> {}}"
  proof -
    fix U :: "'a set"
    assume hU_fin: "finite {\<tau>'\<in>K. \<tau>' \<inter> U \<noteq> {}}"
    have h_sub: "{\<tau>'\<in>?K'. \<tau>' \<inter> U \<noteq> {}}
                   \<subseteq> {\<tau>'\<in>K. \<tau>' \<inter> U \<noteq> {}} \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
      by (by100 blast)
    have h_rhs_fin:
      "finite ({\<tau>'\<in>K. \<tau>' \<inter> U \<noteq> {}} \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1})"
      using hU_fin by (by100 simp)
    show "finite {\<tau>'\<in>?K'. \<tau>' \<inter> U \<noteq> {}}"
      by (rule finite_subset[OF h_sub h_rhs_fin])
  qed
  (** Case split on σ. **)
  show "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>?K'. \<tau> \<inter> U \<noteq> {}}"
  proof (rule UnE[OF h\<sigma>])
    assume h\<sigma>_L: "\<sigma> \<in> K - {e}"
    have h\<sigma>_K: "\<sigma> \<in> K" using h\<sigma>_L by (by100 simp)
    have h_U_ex: "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>'\<in>K. \<tau>' \<inter> U \<noteq> {}}"
      using hK_locfin h\<sigma>_K by (by100 blast)
    obtain U where hU_open: "open U" and hU_sub: "\<sigma> \<subseteq> U"
               and hU_fin: "finite {\<tau>'\<in>K. \<tau>' \<inter> U \<noteq> {}}"
      using h_U_ex by (by100 blast)
    have hU_fin': "finite {\<tau>'\<in>?K'. \<tau>' \<inter> U \<noteq> {}}"
      using h_finite_meet[OF hU_fin] by (by100 simp)
    show ?thesis using hU_open hU_sub hU_fin' by (by100 blast)
  next
    assume h\<sigma>_R: "\<sigma> \<in> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
    (** For new σ, take U_e from K.3 of K applied to e. σ ⊆ e ⊆ U_e. **)
    have h_Ue_ex: "\<exists>U. open U \<and> e \<subseteq> U \<and> finite {\<tau>'\<in>K. \<tau>' \<inter> U \<noteq> {}}"
      using hK_locfin he_K by (by100 blast)
    obtain Ue where hUe_open: "open Ue" and hUe_sub: "e \<subseteq> Ue"
                and hUe_fin: "finite {\<tau>'\<in>K. \<tau>' \<inter> Ue \<noteq> {}}"
      using h_Ue_ex by (by100 blast)
    have h\<sigma>_sub_e: "\<sigma> \<subseteq> e"
    proof -
      have h_ins: "\<sigma> = {R} \<or> \<sigma> \<in> {closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
        using h\<sigma>_R by (by100 simp)
      show ?thesis
      proof (rule disjE[OF h_ins])
        assume "\<sigma> = {R}"
        thus ?thesis using hR_e by (by100 simp)
      next
        assume h\<sigma>_R2: "\<sigma> \<in> {closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
        have h_ins2: "\<sigma> = closed_segment v\<^sub>0 R \<or> \<sigma> = closed_segment R v\<^sub>1"
          using h\<sigma>_R2 by (by100 simp)
        show ?thesis
        proof (rule disjE[OF h_ins2])
          assume "\<sigma> = closed_segment v\<^sub>0 R"
          thus ?thesis using hel_sub_e by (by100 simp)
        next
          assume "\<sigma> = closed_segment R v\<^sub>1"
          thus ?thesis using her_sub_e by (by100 simp)
        qed
      qed
    qed
    have h\<sigma>_sub_Ue: "\<sigma> \<subseteq> Ue" using h\<sigma>_sub_e hUe_sub by (by100 blast)
    have hUe_fin': "finite {\<tau>'\<in>?K'. \<tau>' \<inter> Ue \<noteq> {}}"
      using h_finite_meet[OF hUe_fin] by (by100 simp)
    show ?thesis using hUe_open h\<sigma>_sub_Ue hUe_fin' by (by100 blast)
  qed
qed

(** Phase 1.1 helper — polyhedron equality for the subdivided complex. **)
lemma geotop_subdivide_edge_polyhedron_eq:
  fixes K :: "'a::euclidean_space set set"
  assumes he_K: "e \<in> K"
  assumes he_split: "closed_segment v\<^sub>0 R \<union> closed_segment R v\<^sub>1 \<union> {R} = e"
  shows "geotop_polyhedron ((K - {e}) \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1})
         = geotop_polyhedron K"
proof -
  let ?K' = "(K - {e}) \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
  have h1: "\<Union>?K' = \<Union>(K - {e}) \<union> (closed_segment v\<^sub>0 R \<union> closed_segment R v\<^sub>1 \<union> {R})"
    by (by100 blast)
  have h3: "\<Union>?K' = \<Union>(K - {e}) \<union> e" using h1 he_split by (by100 simp)
  have h2: "\<Union>(K - {e}) \<union> e = \<Union>K" using he_K by (by100 blast)
  have heq: "\<Union>?K' = \<Union>K" using h2 h3 by (by100 simp)
  thus ?thesis unfolding geotop_polyhedron_def by (by100 simp)
qed

(** Phase 1.1 helper (interior case, top-level). Assembled from the
    individual axiom helpers: simplexes (K.0), face_closed (K.1),
    inter_face (K.2), locfin (K.3), polyhedron_eq. **)
lemma geotop_complex_subdivide_edge_interior:
  fixes K :: "'a::euclidean_space set set"
  assumes hKcomp: "geotop_is_complex K"
  assumes hK1dim: "geotop_complex_is_1dim K"
  assumes he_K: "e \<in> K"
  assumes hV_verts: "geotop_simplex_vertices e V"
  assumes hVeq: "V = {v\<^sub>0, v\<^sub>1}" and hv01_ne: "v\<^sub>0 \<noteq> v\<^sub>1"
  assumes hR_e: "R \<in> e" and hR_V: "R \<notin> V"
  shows "\<exists>K'. geotop_is_complex K' \<and> geotop_complex_is_1dim K'
            \<and> geotop_polyhedron K' = geotop_polyhedron K \<and> {R} \<in> K'
            \<and> K - {e} \<subseteq> K'
            \<and> (finite K \<longrightarrow> finite K')"
proof -
  have hR_v0: "R \<noteq> v\<^sub>0" using hR_V hVeq by (by100 blast)
  have hR_v1: "R \<noteq> v\<^sub>1" using hR_V hVeq by (by100 blast)
  (** Establish e = closed_segment v0 v1. **)
  have he_eq: "e = closed_segment v\<^sub>0 v\<^sub>1"
  proof -
    have h_hull_V: "e = geotop_convex_hull V"
      using hV_verts unfolding geotop_simplex_vertices_def by (by100 blast)
    have h_hull_HOL: "e = convex hull V"
      using h_hull_V geotop_convex_hull_eq_HOL by (by100 simp)
    have h_V_pair: "convex hull V = convex hull {v\<^sub>0, v\<^sub>1}" using hVeq by (by100 simp)
    have h_pair_seg: "convex hull {v\<^sub>0, v\<^sub>1} = closed_segment v\<^sub>0 v\<^sub>1"
      by (rule segment_convex_hull[symmetric])
    show ?thesis using h_hull_HOL h_V_pair h_pair_seg by (by100 simp)
  qed
  (** The split fact needed for polyhedron_eq. **)
  have he_split: "closed_segment v\<^sub>0 R \<union> closed_segment R v\<^sub>1 \<union> {R} = e"
  proof -
    have hR_seg: "R \<in> closed_segment v\<^sub>0 v\<^sub>1" using hR_e he_eq by (by100 simp)
    have h_seg_split:
      "closed_segment v\<^sub>0 R \<union> closed_segment R v\<^sub>1 = closed_segment v\<^sub>0 v\<^sub>1"
      by (rule Un_closed_segment[OF hR_seg])
    have hR_in_lhs: "R \<in> closed_segment v\<^sub>0 R" by (by100 simp)
    show ?thesis unfolding he_eq using h_seg_split hR_in_lhs by (by100 auto)
  qed
  let ?K' = "(K - {e}) \<union> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
  (** Polyhedron equality via helper. **)
  have hK'_poly: "geotop_polyhedron ?K' = geotop_polyhedron K"
    by (rule geotop_subdivide_edge_polyhedron_eq[OF he_K he_split])
  (** {R} is in K' trivially. **)
  have hR_K': "{R} \<in> ?K'" by (by100 blast)
  (** Finite preservation. **)
  have hK'_fin: "finite K \<longrightarrow> finite ?K'" by (by100 simp)
  (** K.0 (all simplexes) via helper. **)
  have hK'_sim: "\<forall>\<sigma>\<in>?K'. geotop_is_simplex \<sigma>"
    by (rule geotop_subdivide_edge_simplexes[OF hKcomp hR_v0 hR_v1])
  (** 1-dim preservation: each simplex is 0- or 1-dim. **)
  have hR_dim: "geotop_simplex_dim {R} 0" by (rule geotop_singleton_is_simplex)
  have he\<^sub>l_dim: "geotop_simplex_dim (closed_segment v\<^sub>0 R) 1"
    by (rule geotop_closed_segment_is_simplex[OF hR_v0[symmetric]])
  have he\<^sub>r_dim: "geotop_simplex_dim (closed_segment R v\<^sub>1) 1"
    by (rule geotop_closed_segment_is_simplex[OF hR_v1])
  have hK'_1dim: "geotop_complex_is_1dim ?K'"
    unfolding geotop_complex_is_1dim_def
  proof
    fix \<sigma> assume h\<sigma>K': "\<sigma> \<in> ?K'"
    show "\<exists>n\<le>1. geotop_simplex_dim \<sigma> n"
    proof (rule UnE[OF h\<sigma>K'])
      assume h\<sigma>_L: "\<sigma> \<in> K - {e}"
      have "\<sigma> \<in> K" using h\<sigma>_L by (by100 simp)
      thus ?thesis using hK1dim unfolding geotop_complex_is_1dim_def by (by100 blast)
    next
      assume h\<sigma>_R: "\<sigma> \<in> {{R}, closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
      have h_ins: "\<sigma> = {R} \<or> \<sigma> \<in> {closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
        using h\<sigma>_R by (by100 simp)
      show ?thesis
      proof (rule disjE[OF h_ins])
        assume "\<sigma> = {R}" thus ?thesis using hR_dim by (by100 blast)
      next
        assume h\<sigma>_R2: "\<sigma> \<in> {closed_segment v\<^sub>0 R, closed_segment R v\<^sub>1}"
        have h_ins2: "\<sigma> = closed_segment v\<^sub>0 R \<or> \<sigma> = closed_segment R v\<^sub>1"
          using h\<sigma>_R2 by (by100 simp)
        show ?thesis
        proof (rule disjE[OF h_ins2])
          assume "\<sigma> = closed_segment v\<^sub>0 R"
          thus ?thesis using he\<^sub>l_dim by (by100 blast)
        next
          assume "\<sigma> = closed_segment R v\<^sub>1"
          thus ?thesis using he\<^sub>r_dim by (by100 blast)
        qed
      qed
    qed
  qed
  (** K.1, K.2, K.3 via helpers. **)
  have hv01_in_K: "{v\<^sub>0} \<in> K \<and> {v\<^sub>1} \<in> K"
    by (rule geotop_subdivide_edge_vertices_in_K[OF hKcomp he_K hV_verts hVeq])
  have hv0_K: "{v\<^sub>0} \<in> K" using hv01_in_K by (by100 blast)
  have hv1_K: "{v\<^sub>1} \<in> K" using hv01_in_K by (by100 blast)
  have hK'_faces: "\<forall>\<sigma>\<in>?K'. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> ?K'"
    by (rule geotop_subdivide_edge_face_closed
               [OF hKcomp hK1dim he_K hV_verts hVeq hv01_ne hv0_K hv1_K hR_v0 hR_v1])
  have hK'_inter: "\<forall>\<sigma>\<in>?K'. \<forall>\<tau>\<in>?K'. \<sigma> \<inter> \<tau> \<noteq> {}
                      \<longrightarrow> geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    by (rule geotop_subdivide_edge_inter_face
               [OF hKcomp hK1dim he_K hV_verts hVeq hv01_ne hR_e hR_V])
  (** K.3: inherit from K's K.3 (even without finite K). **)
  have hel_sub_e: "closed_segment v\<^sub>0 R \<subseteq> e"
  proof -
    have hR_seg: "R \<in> closed_segment v\<^sub>0 v\<^sub>1" using hR_e he_eq by (by100 simp)
    have "closed_segment v\<^sub>0 R \<subseteq> closed_segment v\<^sub>0 v\<^sub>1"
      using hR_seg subset_closed_segment by (by100 blast)
    thus ?thesis using he_eq by (by100 simp)
  qed
  have her_sub_e: "closed_segment R v\<^sub>1 \<subseteq> e"
  proof -
    have hR_seg: "R \<in> closed_segment v\<^sub>0 v\<^sub>1" using hR_e he_eq by (by100 simp)
    have "closed_segment R v\<^sub>1 \<subseteq> closed_segment v\<^sub>0 v\<^sub>1"
      using hR_seg subset_closed_segment by (by100 blast)
    thus ?thesis using he_eq by (by100 simp)
  qed
  have hK'_locfin: "\<forall>\<sigma>\<in>?K'. \<exists>U. open U \<and> \<sigma> \<subseteq> U
                      \<and> finite {\<tau>\<in>?K'. \<tau> \<inter> U \<noteq> {}}"
    by (rule geotop_subdivide_edge_locfin_inherit
               [OF hKcomp he_K hel_sub_e her_sub_e hR_e])
  (** Assemble K.0, K.1, K.2, K.3 into is_complex via def unfold. **)
  have hK'_comp: "geotop_is_complex ?K'"
    unfolding geotop_is_complex_def
    using hK'_sim hK'_faces hK'_inter hK'_locfin by (by100 blast)
  have hK'_sup: "K - {e} \<subseteq> ?K'" by (by100 blast)
  have h_all: "geotop_is_complex ?K' \<and> geotop_complex_is_1dim ?K'
             \<and> geotop_polyhedron ?K' = geotop_polyhedron K \<and> {R} \<in> ?K'
             \<and> K - {e} \<subseteq> ?K'
             \<and> (finite K \<longrightarrow> finite ?K')"
    using hK'_comp hK'_1dim hK'_poly hR_K' hK'_sup hK'_fin by (by100 blast)
  show ?thesis using h_all by (rule exI)
qed

(** Phase 1.1 helper (vertex case): if R is a vertex of an edge e of K,
    then {R} is already in K by face-closure. **)
lemma geotop_complex_subdivide_edge_vertex:
  fixes K :: "'a::euclidean_space set set"
  assumes hKcomp: "geotop_is_complex K"
  assumes he_K: "e \<in> K" and he_dim: "geotop_simplex_dim e 1"
  assumes hV_verts: "geotop_simplex_vertices e V"
  assumes hR_V: "R \<in> V"
  shows "{R} \<in> K"
proof -
  have h_sing: "{R} = geotop_convex_hull {R}"
    using geotop_convex_hull_eq_HOL[of "{R}"] by (by100 simp)
  have hRs_V: "{R} \<subseteq> V" using hR_V by (by100 simp)
  have h_Rface: "geotop_is_face {R} e"
    unfolding geotop_is_face_def
    using hV_verts hRs_V h_sing by (by100 blast)
  have hK_faces: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    using conjunct1[OF conjunct2[OF hKcomp[unfolded geotop_is_complex_def]]]
    by (by100 blast)
  show "{R} \<in> K" using hK_faces he_K h_Rface by (by100 blast)
qed

(** Phase 1.1 main: subdivide a 1-simplex of K at a point R \<in> e.
    Also preserves finiteness when the input is finite. Returns K' that
    is a super-set of K - {e}, ensuring all 0-simplices of K survive. **)
lemma geotop_complex_subdivide_edge:
  fixes K :: "'a::euclidean_space set set"
  assumes hKcomp: "geotop_is_complex K"
  assumes hK1dim: "geotop_complex_is_1dim K"
  assumes he_K: "e \<in> K" and he_dim: "geotop_simplex_dim e 1"
  assumes hR_e: "R \<in> e"
  shows "\<exists>K'. geotop_is_complex K' \<and> geotop_complex_is_1dim K'
            \<and> geotop_polyhedron K' = geotop_polyhedron K \<and> {R} \<in> K'
            \<and> K - {e} \<subseteq> K'
            \<and> (finite K \<longrightarrow> finite K')"
proof -
  obtain V m where hVfin: "finite V" and hVcard: "card V = 1 + 1"
               and hnm: "1 \<le> m" and hVgp: "geotop_general_position V m"
               and he_hull: "e = geotop_convex_hull V"
    using he_dim unfolding geotop_simplex_dim_def by (by100 blast)
  have hV_verts: "geotop_simplex_vertices e V"
    unfolding geotop_simplex_vertices_def using hVfin hVcard hnm hVgp he_hull
    by (by100 blast)
  have hVcard2: "card V = 2" using hVcard by (by100 simp)
  have hV2ex: "\<exists>x y. V = {x, y} \<and> x \<noteq> y"
    using hVcard2 card_2_iff by (by100 blast)
  obtain v\<^sub>0 v\<^sub>1 where hVeq: "V = {v\<^sub>0, v\<^sub>1}" and hv01_ne: "v\<^sub>0 \<noteq> v\<^sub>1"
    using hV2ex by (by100 blast)
  show ?thesis
  proof (cases "R \<in> V")
    case True
    have hR_K: "{R} \<in> K"
      by (rule geotop_complex_subdivide_edge_vertex[OF hKcomp he_K he_dim hV_verts True])
    have hK_sub_self: "K - {e} \<subseteq> K" by (by100 blast)
    show ?thesis using hKcomp hK1dim hR_K hK_sub_self by (by100 blast)
  next
    case False
    show ?thesis
      by (rule geotop_complex_subdivide_edge_interior
              [OF hKcomp hK1dim he_K hV_verts hVeq hv01_ne hR_e False])
  qed
qed

(** Phase 1.2: subdivide a 1-complex at any point R \<in> |K| to make R a 0-simplex.
    Preserves finiteness. **)
lemma geotop_complex_subdivide_at:
  fixes K :: "'a::euclidean_space set set"
  assumes hKcomp: "geotop_is_complex K"
  assumes hK1dim: "geotop_complex_is_1dim K"
  assumes hR_poly: "R \<in> geotop_polyhedron K"
  shows "\<exists>K'. geotop_is_complex K' \<and> geotop_complex_is_1dim K'
            \<and> geotop_polyhedron K' = geotop_polyhedron K \<and> {R} \<in> K'
            \<and> (\<forall>v. {v} \<in> K \<longrightarrow> {v} \<in> K')
            \<and> (finite K \<longrightarrow> finite K')"
proof -
  (** Find σ ∈ K with R ∈ σ. **)
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K" and hR\<sigma>: "R \<in> \<sigma>"
    using hR_poly unfolding geotop_polyhedron_def by (by100 blast)
  (** σ is 0- or 1-dim (from K 1-dim). **)
  obtain n where hn_le: "n \<le> 1" and h\<sigma>_dim: "geotop_simplex_dim \<sigma> n"
    using hK1dim h\<sigma>K unfolding geotop_complex_is_1dim_def by (by100 blast)
  show ?thesis
  proof (cases n)
    case 0
    (** σ has dim 0, i.e., σ is a 0-simplex (singleton). R ∈ σ ⟹ σ = {R}. **)
    obtain V m where hVfin: "finite V" and hVcard: "card V = 0 + 1"
                 and hnm: "0 \<le> m" and hVgp: "geotop_general_position V m"
                 and h\<sigma>_hull: "\<sigma> = geotop_convex_hull V"
      using h\<sigma>_dim 0 unfolding geotop_simplex_dim_def by (by100 blast)
    have hVsing: "\<exists>v. V = {v}" using hVcard by (metis card_1_singletonE One_nat_def add.commute add_0)
    obtain v where hVeq: "V = {v}" using hVsing by (by100 blast)
    have h\<sigma>_sing: "\<sigma> = {v}"
      using h\<sigma>_hull hVeq geotop_convex_hull_eq_HOL[of "{v}"] by (by100 simp)
    have hR_v: "R = v" using hR\<sigma> h\<sigma>_sing by (by100 blast)
    have hR_K: "{R} \<in> K" using h\<sigma>K h\<sigma>_sing hR_v by (by100 simp)
    have h_all_preserve: "\<forall>v. {v} \<in> K \<longrightarrow> {v} \<in> K" by (by100 simp)
    show ?thesis using hKcomp hK1dim hR_K h_all_preserve by (by100 blast)
  next
    case (Suc k)
    have hn_eq_1: "n = 1" using hn_le Suc by (by100 simp)
    have h\<sigma>_dim1: "geotop_simplex_dim \<sigma> 1" using h\<sigma>_dim hn_eq_1 by (by100 simp)
    have h_ex_K': "\<exists>K'. geotop_is_complex K' \<and> geotop_complex_is_1dim K'
              \<and> geotop_polyhedron K' = geotop_polyhedron K \<and> {R} \<in> K'
              \<and> K - {\<sigma>} \<subseteq> K'
              \<and> (finite K \<longrightarrow> finite K')"
      by (rule geotop_complex_subdivide_edge[OF hKcomp hK1dim h\<sigma>K h\<sigma>_dim1 hR\<sigma>])
    obtain K' where hK'_comp: "geotop_is_complex K'" and hK'_1dim: "geotop_complex_is_1dim K'"
                 and hK'_poly: "geotop_polyhedron K' = geotop_polyhedron K"
                 and hR_K': "{R} \<in> K'" and hK'_sup: "K - {\<sigma>} \<subseteq> K'"
                 and hK'_fin: "finite K \<longrightarrow> finite K'"
      using h_ex_K' by (by100 blast)
    (** 0-simplex preservation: any {v} ∈ K is ≠ σ (dim mismatch) so {v} ∈ K-{σ} ⊆ K'. **)
    have h_preserve: "\<forall>v. {v} \<in> K \<longrightarrow> {v} \<in> K'"
    proof (intro allI impI)
      fix v assume hvK: "{v} \<in> K"
      have h_not_\<sigma>: "{v} \<noteq> \<sigma>"
      proof
        assume heq: "{v} = \<sigma>"
        have h_dim0: "geotop_simplex_dim {v} 0" by (rule geotop_singleton_is_simplex)
        have h_\<sigma>_dim0: "geotop_simplex_dim \<sigma> 0" using h_dim0 heq by (by100 simp)
        have h_01: "(0::nat) = 1" by (rule geotop_simplex_dim_unique[OF h_\<sigma>_dim0 h\<sigma>_dim1])
        have h_ne: "(0::nat) \<noteq> 1" by (by100 simp)
        show False using h_01 h_ne by (by100 blast)
      qed
      have "{v} \<in> K - {\<sigma>}" using hvK h_not_\<sigma> by (by100 simp)
      thus "{v} \<in> K'" using hK'_sup by (by100 blast)
    qed
    show ?thesis using hK'_comp hK'_1dim hK'_poly hR_K' h_preserve hK'_fin by (by100 blast)
  qed
qed

(** Phase 1.A infrastructure: subdivide K at two points X, Y, returning
    K'' with {X} ∈ K'' and {Y} ∈ K''. The 0-simplex preservation from
    subdivide_at is essential — after subdividing at X (potentially
    splitting an edge), {X} is a vertex; when we then subdivide at Y,
    {X} is a 0-simplex of the intermediate K' and must survive. **)
lemma geotop_complex_subdivide_at_two:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes hK1dim: "geotop_complex_is_1dim K"
  assumes hX_poly: "X \<in> geotop_polyhedron K"
  assumes hY_poly: "Y \<in> geotop_polyhedron K"
  shows "\<exists>K''. geotop_is_complex K'' \<and> geotop_complex_is_1dim K''
             \<and> geotop_polyhedron K'' = geotop_polyhedron K
             \<and> {X} \<in> K'' \<and> {Y} \<in> K''
             \<and> (finite K \<longrightarrow> finite K'')"
proof -
  (** Step 1: subdivide at X. **)
  have h_ex_K1: "\<exists>K'. geotop_is_complex K' \<and> geotop_complex_is_1dim K'
               \<and> geotop_polyhedron K' = geotop_polyhedron K \<and> {X} \<in> K'
               \<and> (\<forall>v. {v} \<in> K \<longrightarrow> {v} \<in> K')
               \<and> (finite K \<longrightarrow> finite K')"
    by (rule geotop_complex_subdivide_at[OF hK hK1dim hX_poly])
  obtain K' where hK'_comp: "geotop_is_complex K'"
               and hK'_1dim: "geotop_complex_is_1dim K'"
               and hK'_poly: "geotop_polyhedron K' = geotop_polyhedron K"
               and hX_K': "{X} \<in> K'"
               and hK'_preserve: "\<forall>v. {v} \<in> K \<longrightarrow> {v} \<in> K'"
               and hK'_fin: "finite K \<longrightarrow> finite K'"
    using h_ex_K1 by (by100 blast)
  (** Step 2: Y ∈ polyhedron K' = polyhedron K. Subdivide K' at Y. **)
  have hY_K': "Y \<in> geotop_polyhedron K'" using hY_poly hK'_poly by (by100 simp)
  have h_ex_K2: "\<exists>K''. geotop_is_complex K'' \<and> geotop_complex_is_1dim K''
               \<and> geotop_polyhedron K'' = geotop_polyhedron K' \<and> {Y} \<in> K''
               \<and> (\<forall>v. {v} \<in> K' \<longrightarrow> {v} \<in> K'')
               \<and> (finite K' \<longrightarrow> finite K'')"
    by (rule geotop_complex_subdivide_at[OF hK'_comp hK'_1dim hY_K'])
  obtain K'' where hK''_comp: "geotop_is_complex K''"
                and hK''_1dim: "geotop_complex_is_1dim K''"
                and hK''_poly: "geotop_polyhedron K'' = geotop_polyhedron K'"
                and hY_K'': "{Y} \<in> K''"
                and hK''_preserve: "\<forall>v. {v} \<in> K' \<longrightarrow> {v} \<in> K''"
                and hK''_fin: "finite K' \<longrightarrow> finite K''"
    using h_ex_K2 by (by100 blast)
  (** Derive {X} ∈ K'' via preservation. **)
  have hX_K'': "{X} \<in> K''" using hX_K' hK''_preserve by (by100 blast)
  have hK''_poly_K: "geotop_polyhedron K'' = geotop_polyhedron K"
    using hK''_poly hK'_poly by (by100 simp)
  have hK''_fin_K: "finite K \<longrightarrow> finite K''" using hK'_fin hK''_fin by (by100 blast)
  show ?thesis
    using hK''_comp hK''_1dim hK''_poly_K hX_K'' hY_K'' hK''_fin_K by (by100 blast)
qed

(** Phase 1.2b: broken line has a FINITE witness complex. Follows from
    compactness of the arc + K.3 local finiteness via subcover. **)
lemma geotop_broken_line_finite_witness:
  fixes B :: "'a::euclidean_space set"
  assumes hB: "geotop_is_broken_line B"
  shows "\<exists>K. geotop_is_complex K \<and> geotop_complex_is_1dim K
           \<and> geotop_polyhedron K = B \<and> finite K"
proof -
  obtain K where hKcomp: "geotop_is_complex K"
             and hKpoly: "geotop_polyhedron K = B"
             and hK1dim: "geotop_complex_is_1dim K"
             and hKarc: "geotop_is_arc B (subspace_topology UNIV geotop_euclidean_topology B)"
    using hB unfolding geotop_is_broken_line_def by (by100 blast)
  (** B is compact: it's a HOL arc (homeomorphic to [0,1]). **)
  obtain \<gamma> where harc: "arc \<gamma>" and hpim: "path_image \<gamma> = B"
    using geotop_is_arc_imp_HOL_arc[OF hKarc] by (by100 blast)
  have hB_compact: "compact B"
    using hpim harc compact_arc_image by (by100 blast)
  (** K.3: each σ ∈ K has open U_σ with σ ⊆ U_σ and finite {τ. τ ∩ U_σ ≠ {}}. **)
  have hK_locfin: "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    using conjunct2[OF conjunct2[OF conjunct2[OF hKcomp[unfolded geotop_is_complex_def]]]]
    by (by100 blast)
  (** Pick an open nbhd U_σ for each σ ∈ K via SOME. **)
  define Uf where "Uf \<sigma> = (SOME U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}})" for \<sigma>
  have hUf_spec: "\<forall>\<sigma>\<in>K. open (Uf \<sigma>) \<and> \<sigma> \<subseteq> Uf \<sigma> \<and> finite {\<tau>\<in>K. \<tau> \<inter> Uf \<sigma> \<noteq> {}}"
  proof
    fix \<sigma> assume h\<sigma>K: "\<sigma> \<in> K"
    have h_ex: "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using hK_locfin h\<sigma>K by (by100 blast)
    show "open (Uf \<sigma>) \<and> \<sigma> \<subseteq> Uf \<sigma> \<and> finite {\<tau>\<in>K. \<tau> \<inter> Uf \<sigma> \<noteq> {}}"
      unfolding Uf_def using someI_ex[OF h_ex] by (by100 blast)
  qed
  (** The {Uf σ} cover B = |K|. **)
  have hUf_open: "\<And>\<sigma>. \<sigma> \<in> K \<Longrightarrow> open (Uf \<sigma>)" using hUf_spec by (by100 blast)
  have hcover: "B \<subseteq> (\<Union>\<sigma>\<in>K. Uf \<sigma>)"
  proof
    fix x assume hxB: "x \<in> B"
    have "x \<in> geotop_polyhedron K" using hxB hKpoly by (by100 simp)
    then obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K" and hx\<sigma>: "x \<in> \<sigma>"
      unfolding geotop_polyhedron_def by (by100 blast)
    have hx_Uf: "x \<in> Uf \<sigma>" using hx\<sigma> hUf_spec h\<sigma>K by (by100 blast)
    show "x \<in> (\<Union>\<sigma>\<in>K. Uf \<sigma>)" using h\<sigma>K hx_Uf by (by100 blast)
  qed
  (** Apply HOL's compactE_image: finite subcover indexed by K. **)
  obtain S\<^sub>\<sigma> where hS\<^sub>\<sigma>_sub: "S\<^sub>\<sigma> \<subseteq> K" and hS\<^sub>\<sigma>_fin: "finite S\<^sub>\<sigma>"
              and hS\<^sub>\<sigma>_cover: "B \<subseteq> (\<Union>\<sigma>\<in>S\<^sub>\<sigma>. Uf \<sigma>)"
    using compactE_image[OF hB_compact hUf_open hcover] by (by100 blast)
  (** Each τ ∈ K meets some Uf σ with σ ∈ S_σ, since τ nonempty, τ ⊆ B ⊆ ⋃_σ Uf σ. **)
  have h_tau_in_sub: "\<And>\<tau>. \<tau> \<in> K \<Longrightarrow> \<exists>\<sigma>\<in>S\<^sub>\<sigma>. \<tau> \<inter> Uf \<sigma> \<noteq> {}"
  proof -
    fix \<tau> assume h\<tau>K: "\<tau> \<in> K"
    have h\<tau>_sim: "geotop_is_simplex \<tau>"
      using h\<tau>K conjunct1[OF hKcomp[unfolded geotop_is_complex_def]] by (by100 blast)
    have h\<tau>_ne: "\<tau> \<noteq> {}" by (rule geotop_is_simplex_nonempty[OF h\<tau>_sim])
    obtain x where hx\<tau>: "x \<in> \<tau>" using h\<tau>_ne by (by100 blast)
    have hxB: "x \<in> B" using hx\<tau> h\<tau>K hKpoly unfolding geotop_polyhedron_def by (by100 blast)
    obtain \<sigma> where h\<sigma>_S: "\<sigma> \<in> S\<^sub>\<sigma>" and hx_Uf: "x \<in> Uf \<sigma>"
      using hS\<^sub>\<sigma>_cover hxB by (by100 blast)
    show "\<exists>\<sigma>\<in>S\<^sub>\<sigma>. \<tau> \<inter> Uf \<sigma> \<noteq> {}"
      using h\<sigma>_S hx\<tau> hx_Uf by (by100 blast)
  qed
  (** K = ⋃_{σ ∈ S_σ} {τ ∈ K. τ ∩ Uf σ ≠ {}}, a finite union of finite sets. **)
  have hK_eq_fwd: "K \<subseteq> (\<Union>\<sigma>\<in>S\<^sub>\<sigma>. {\<tau>\<in>K. \<tau> \<inter> Uf \<sigma> \<noteq> {}})"
  proof
    fix \<tau> assume h\<tau>K: "\<tau> \<in> K"
    obtain \<sigma> where h\<sigma>S: "\<sigma> \<in> S\<^sub>\<sigma>" and h\<tau>U: "\<tau> \<inter> Uf \<sigma> \<noteq> {}"
      using h_tau_in_sub[OF h\<tau>K] by (by100 blast)
    show "\<tau> \<in> (\<Union>\<sigma>\<in>S\<^sub>\<sigma>. {\<tau>\<in>K. \<tau> \<inter> Uf \<sigma> \<noteq> {}})"
      using h\<sigma>S h\<tau>K h\<tau>U by (by100 blast)
  qed
  have hK_eq_bwd: "(\<Union>\<sigma>\<in>S\<^sub>\<sigma>. {\<tau>\<in>K. \<tau> \<inter> Uf \<sigma> \<noteq> {}}) \<subseteq> K" by (by100 blast)
  have hK_eq: "K = (\<Union>\<sigma>\<in>S\<^sub>\<sigma>. {\<tau>\<in>K. \<tau> \<inter> Uf \<sigma> \<noteq> {}})"
    using hK_eq_fwd hK_eq_bwd by (by100 blast)
  have hpieces_fin: "\<forall>\<sigma>\<in>S\<^sub>\<sigma>. finite {\<tau>\<in>K. \<tau> \<inter> Uf \<sigma> \<noteq> {}}"
    using hS\<^sub>\<sigma>_sub hUf_spec by (by100 blast)
  have hK_fin: "finite K"
  proof -
    have "finite (\<Union>\<sigma>\<in>S\<^sub>\<sigma>. {\<tau>\<in>K. \<tau> \<inter> Uf \<sigma> \<noteq> {}})"
      using hS\<^sub>\<sigma>_fin hpieces_fin by (by100 blast)
    thus ?thesis using hK_eq by (by100 simp)
  qed
  show ?thesis using hKcomp hK1dim hKpoly hK_fin by (by100 blast)
qed

(** Phase 1.3: any point on a broken line can be made a 0-simplex of a
    FINITE witness complex. Uses finite witness + Phase 1.2. **)
lemma geotop_broken_line_vertex_at:
  fixes B :: "'a::euclidean_space set"
  assumes hB: "geotop_is_broken_line B"
  assumes hR_B: "R \<in> B"
  shows "\<exists>K. geotop_is_complex K \<and> geotop_complex_is_1dim K
           \<and> geotop_polyhedron K = B \<and> {R} \<in> K \<and> finite K"
proof -
  obtain K where hK: "geotop_is_complex K" and hKpoly: "geotop_polyhedron K = B"
              and hK1: "geotop_complex_is_1dim K" and hKfin: "finite K"
    using geotop_broken_line_finite_witness[OF hB] by (by100 blast)
  have hR_poly: "R \<in> geotop_polyhedron K" using hR_B hKpoly by (by100 simp)
  obtain K' where hK'_comp: "geotop_is_complex K'" and hK'_1dim: "geotop_complex_is_1dim K'"
              and hK'_poly: "geotop_polyhedron K' = geotop_polyhedron K"
              and hR_K': "{R} \<in> K'"
              and hK'_fin_imp: "finite K \<longrightarrow> finite K'"
    using geotop_complex_subdivide_at[OF hK hK1 hR_poly] by (by100 blast)
  have hK'_B: "geotop_polyhedron K' = B" using hK'_poly hKpoly by (by100 simp)
  have hK'_fin: "finite K'" using hK'_fin_imp hKfin by (by100 simp)
  show ?thesis using hK'_comp hK'_1dim hK'_B hR_K' hK'_fin by (by100 blast)
qed

(** from \<S>1 Theorem 13 (geotop.tex:403)
    LATEX VERSION: In R^n, every connected open set U is broken-line-wise connected. **)
definition geotop_broken_line_connected :: "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_broken_line_connected U \<longleftrightarrow>
    (\<forall>P\<in>U. \<forall>Q\<in>U. \<exists>B. geotop_is_broken_line B \<and> B \<subseteq> U \<and> P \<in> B \<and> Q \<in> B)"

(** Partial progress on Theorem_GT_1_13: the convex open case in a euclidean space
    is broken-line-connected. Uses \<open>geotop_closed_segment_is_broken_line\<close> for the
    P \<noteq> Q case; for P = Q, picks an auxiliary point via the open-ball assumption. **)
lemma geotop_convex_open_broken_line_connected:
  fixes U :: "'a::euclidean_space set"
  assumes hopen: "U \<in> geotop_euclidean_topology"
  assumes hconv: "convex U"
  shows "geotop_broken_line_connected U"
  unfolding geotop_broken_line_connected_def
proof (intro ballI)
  fix P Q assume hP: "P \<in> U" and hQ: "Q \<in> U"
  have hU_open_HOL: "open U"
    using hopen geotop_euclidean_topology_eq_open_sets
    unfolding top1_open_sets_def by blast
  show "\<exists>B. geotop_is_broken_line B \<and> B \<subseteq> U \<and> P \<in> B \<and> Q \<in> B"
  proof (cases "P = Q")
    case False
    let ?B = "closed_segment P Q"
    have hbline: "geotop_is_broken_line ?B"
      by (rule geotop_closed_segment_is_broken_line[OF False])
    have hsub: "?B \<subseteq> U"
      by (rule closed_segment_subset[OF hP hQ hconv])
    show ?thesis using hbline hsub by auto
  next
    case True
    obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" and hball: "ball P \<epsilon> \<subseteq> U"
      using hU_open_HOL hP open_contains_ball by blast
    obtain b :: 'a where hb: "b \<in> Basis" using nonempty_Basis by blast
    have hb_norm: "norm b = 1" using hb by (rule norm_Basis)
    have hb_nz: "b \<noteq> 0" using hb_norm by auto
    define Q' :: 'a where "Q' = P + (\<epsilon>/2) *\<^sub>R b"
    have hPne: "P \<noteq> Q'"
      unfolding Q'_def using h\<epsilon> hb_nz by simp
    have hdist: "norm (Q' - P) = \<epsilon>/2"
      unfolding Q'_def using h\<epsilon> hb_norm by simp
    have hQ'ball: "Q' \<in> ball P \<epsilon>"
      unfolding ball_def dist_norm using hdist h\<epsilon> by (simp add: norm_minus_commute)
    have hQ'U: "Q' \<in> U" using hQ'ball hball by blast
    let ?B = "closed_segment P Q'"
    have hbline: "geotop_is_broken_line ?B"
      by (rule geotop_closed_segment_is_broken_line[OF hPne])
    have hsub: "?B \<subseteq> U"
      by (rule closed_segment_subset[OF hP hQ'U hconv])
    have hPB: "P \<in> ?B" by simp
    have hQB: "Q \<in> ?B" using True hPB by simp
    show ?thesis using hbline hsub hPB hQB by blast
  qed
qed

(** Corollary: every open ball in a Euclidean space is broken-line-connected. **)
corollary geotop_open_ball_broken_line_connected:
  fixes P :: "'a::euclidean_space" and r :: real
  shows "geotop_broken_line_connected (ball P r)"
proof -
  have hopen_HOL: "open (ball P r)" by simp
  have hopen: "ball P r \<in> geotop_euclidean_topology"
    by (metis hopen_HOL geotop_euclidean_topology_eq_open_sets
              mem_Collect_eq top1_open_sets_def)
  have hconv: "convex (ball P r)" by (rule convex_ball)
  show ?thesis
    by (rule geotop_convex_open_broken_line_connected[OF hopen hconv])
qed

(** Infrastructure for Phase 1.A: arc → homeomorphism [0,1] ↔ path_image. **)
lemma geotop_arc_homeomorphism_image:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  assumes harc: "arc \<gamma>"
  shows "\<exists>h. homeomorphism {0..1} (path_image \<gamma>) \<gamma> h"
proof -
  show ?thesis by (rule homeomorphism_arc[OF harc]) (rule exI)
qed

(** Infrastructure for Phase 1.A: for γ an arc and σ ⊆ path_image γ connected,
    the preimage {t ∈ [0,1]. γ t ∈ σ} is a closed interval in [0,1].
    This is the key step making γ behave well with 1-simplices of K: each
    simplex σ ⊆ B maps back to a sub-interval, so X, Y as vertices cut the
    parameter line at breakpoints. **)
lemma geotop_arc_preimage_is_interval:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  assumes harc: "arc \<gamma>"
  assumes h\<sigma>_sub: "\<sigma> \<subseteq> path_image \<gamma>"
  assumes h\<sigma>_conn: "connected \<sigma>"
  shows "is_interval {t\<in>{0..1}. \<gamma> t \<in> \<sigma>}"
proof -
  have h_ex_h: "\<exists>h. homeomorphism {0..1} (path_image \<gamma>) \<gamma> h"
    by (rule geotop_arc_homeomorphism_image[OF harc])
  obtain h where hhomeo: "homeomorphism {0..1} (path_image \<gamma>) \<gamma> h"
    using h_ex_h by (by100 blast)
  have hcont_h: "continuous_on (path_image \<gamma>) h"
    using hhomeo unfolding homeomorphism_def by (by100 blast)
  have hcont_h_\<sigma>: "continuous_on \<sigma> h"
    using hcont_h h\<sigma>_sub continuous_on_subset by (by100 blast)
  have h_conn_img: "connected (h ` \<sigma>)"
    by (rule connected_continuous_image[OF hcont_h_\<sigma> h\<sigma>_conn])
  (** Show the preimage set equals h ` σ. **)
  have h_set_eq: "{t\<in>{0..1}. \<gamma> t \<in> \<sigma>} = h ` \<sigma>"
  proof
    show "{t\<in>{0..1}. \<gamma> t \<in> \<sigma>} \<subseteq> h ` \<sigma>"
    proof
      fix t assume ht_mem: "t \<in> {t\<in>{0..1}. \<gamma> t \<in> \<sigma>}"
      have ht_01: "t \<in> {0..1}" using ht_mem by (by100 blast)
      have ht_\<sigma>: "\<gamma> t \<in> \<sigma>" using ht_mem by (by100 blast)
      have h_inv: "h (\<gamma> t) = t"
        using hhomeo ht_01 unfolding homeomorphism_def by (by100 blast)
      show "t \<in> h ` \<sigma>" using h_inv ht_\<sigma> by (by100 force)
    qed
    show "h ` \<sigma> \<subseteq> {t\<in>{0..1}. \<gamma> t \<in> \<sigma>}"
    proof
      fix t assume ht_img: "t \<in> h ` \<sigma>"
      obtain x where hx_\<sigma>: "x \<in> \<sigma>" and ht_eq: "t = h x" using ht_img by (by100 blast)
      have hx_B: "x \<in> path_image \<gamma>" using hx_\<sigma> h\<sigma>_sub by (by100 blast)
      have h_t_01: "t \<in> {0..1}"
      proof -
        have "h ` path_image \<gamma> = {0..1}"
          using hhomeo unfolding homeomorphism_def by (by100 blast)
        hence "h x \<in> {0..1}" using hx_B by (by100 blast)
        thus ?thesis using ht_eq by (by100 simp)
      qed
      have h_\<gamma>t_eq_x: "\<gamma> t = x"
      proof -
        have h_inv2: "\<gamma> (h x) = x"
          using hhomeo hx_B unfolding homeomorphism_def by (by100 blast)
        show ?thesis using h_inv2 ht_eq by (by100 simp)
      qed
      have h_\<gamma>t_\<sigma>: "\<gamma> t \<in> \<sigma>" using h_\<gamma>t_eq_x hx_\<sigma> by (by100 simp)
      show "t \<in> {t\<in>{0..1}. \<gamma> t \<in> \<sigma>}" using h_t_01 h_\<gamma>t_\<sigma> by (by100 blast)
    qed
  qed
  have h_conn_set: "connected {t\<in>{0..1}. \<gamma> t \<in> \<sigma>}"
    using h_set_eq h_conn_img by (by100 simp)
  show ?thesis using h_conn_set is_interval_connected_1 by (by100 blast)
qed

(** Phase 1.A key helper: if {v} is a vertex of a 1-dim complex K and v
    belongs to a simplex σ ∈ K, then {v} is a face of σ and (when σ is
    a 1-simplex) v is one of σ's two vertices. Derived from K.2 of K. **)
lemma geotop_1dim_vertex_in_simplex_is_face:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes hv\<sigma>: "v \<in> \<sigma>"
  shows "geotop_is_face {v} \<sigma>"
proof -
  have hK_inter: "\<forall>\<sigma>'\<in>K. \<forall>\<tau>'\<in>K. \<sigma>' \<inter> \<tau>' \<noteq> {} \<longrightarrow>
                  geotop_is_face (\<sigma>' \<inter> \<tau>') \<sigma>' \<and> geotop_is_face (\<sigma>' \<inter> \<tau>') \<tau>'"
    using conjunct1[OF conjunct2[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]]]
    by (by100 blast)
  have h_cap: "{v} \<inter> \<sigma> = {v}" using hv\<sigma> by (by100 blast)
  have h_cap_ne: "{v} \<inter> \<sigma> \<noteq> {}" using h_cap by (by100 simp)
  have h_face_cap: "geotop_is_face ({v} \<inter> \<sigma>) \<sigma>"
    using hK_inter hvK h\<sigma>K h_cap_ne by (by100 blast)
  show ?thesis using h_face_cap h_cap by (by100 simp)
qed

(** Phase 1.A corollary: if σ ∈ K (1-dim) is a 1-simplex with vertices {a, b}
    (where a ≠ b) and {v} ∈ K with v ∈ σ, then v ∈ {a, b}. **)
lemma geotop_1dim_vertex_in_1simplex_is_endpoint:
  fixes K :: "'a::euclidean_space set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>_eq: "\<sigma> = closed_segment a b" and hab: "a \<noteq> b"
  assumes hv\<sigma>: "v \<in> \<sigma>"
  shows "v = a \<or> v = b"
proof -
  have h_face: "geotop_is_face {v} \<sigma>"
    by (rule geotop_1dim_vertex_in_simplex_is_face[OF hK hvK h\<sigma>K hv\<sigma>])
  have h_sv: "geotop_simplex_vertices \<sigma> {a, b}"
    using h\<sigma>_eq geotop_closed_segment_simplex_vertices[OF hab] by (by100 simp)
  obtain V' W where hV'_sv: "geotop_simplex_vertices \<sigma> V'"
                and hW_ne: "W \<noteq> {}" and hW_V': "W \<subseteq> V'"
                and hv_hull: "{v} = geotop_convex_hull W"
    using h_face unfolding geotop_is_face_def by (by100 blast)
  have hV'_eq: "V' = {a, b}"
    by (rule geotop_simplex_vertices_unique[OF hV'_sv h_sv])
  have hW_sub: "W \<subseteq> {a, b}" using hW_V' hV'_eq by (by100 simp)
  have hv_HOL: "{v} = convex hull W"
    using hv_hull geotop_convex_hull_eq_HOL by (by100 simp)
  (** {v} is a singleton, so convex hull W = {v}. W nonempty subset of {a,b}.
      If W = {a}: conv{a} = {a} = {v} ⟹ v = a. Similarly W = {b} gives v = b.
      If W = {a, b}: conv{a,b} = closed_segment a b ≠ singleton (a ≠ b). **)
  have hW_cases: "W = {a} \<or> W = {b} \<or> W = {a, b}"
    using hW_ne hW_sub by (by100 blast)
  show ?thesis
  proof (rule disjE[OF hW_cases])
    assume hW_a: "W = {a}"
    have "{v} = convex hull {a}" using hv_HOL hW_a by (by100 simp)
    also have "\<dots> = {a}" by (by100 simp)
    finally have "{v} = {a}" .
    hence "v = a" by (by100 simp)
    thus ?thesis by (by100 blast)
  next
    assume hW_rest: "W = {b} \<or> W = {a, b}"
    show ?thesis
    proof (rule disjE[OF hW_rest])
      assume hW_b: "W = {b}"
      have "{v} = convex hull {b}" using hv_HOL hW_b by (by100 simp)
      also have "\<dots> = {b}" by (by100 simp)
      finally have "{v} = {b}" .
      hence "v = b" by (by100 simp)
      thus ?thesis by (by100 blast)
    next
      assume hW_ab: "W = {a, b}"
      have "{v} = convex hull {a, b}" using hv_HOL hW_ab by (by100 simp)
      also have "\<dots> = closed_segment a b" by (rule segment_convex_hull[symmetric])
      finally have h_v_seg: "{v} = closed_segment a b" .
      (** Singleton = segment of two distinct points — contradiction. **)
      have ha_seg: "a \<in> closed_segment a b" by (by100 simp)
      have hb_seg: "b \<in> closed_segment a b" by (by100 simp)
      have ha_v: "a \<in> {v}" using ha_seg h_v_seg by (by100 simp)
      have hb_v: "b \<in> {v}" using hb_seg h_v_seg by (by100 simp)
      have "a = v" using ha_v by (by100 simp)
      moreover have "b = v" using hb_v by (by100 simp)
      ultimately have "a = b" by (by100 simp)
      thus ?thesis using hab by (by100 blast)
    qed
  qed
qed

(** Specialisation: the preimage of any simplex of a 1-dim complex whose
    polyhedron is path_image γ is an interval. Key for Phase 1.A. **)
lemma geotop_arc_preimage_simplex_is_interval:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  assumes harc: "arc \<gamma>"
  assumes hK1dim: "geotop_complex_is_1dim K"
  assumes hpoly: "geotop_polyhedron K = path_image \<gamma>"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  shows "is_interval {t\<in>{0..1}. \<gamma> t \<in> \<sigma>}"
proof -
  have h\<sigma>_sub: "\<sigma> \<subseteq> path_image \<gamma>"
    using h\<sigma>K hpoly unfolding geotop_polyhedron_def by (by100 blast)
  (** σ is singleton or closed_segment — both connected. **)
  have h\<sigma>_conn: "connected \<sigma>"
  proof -
    have h_cases: "(\<exists>v. \<sigma> = {v}) \<or> (\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b)"
      by (rule geotop_1dim_simplex_cases[OF hK1dim h\<sigma>K])
    show ?thesis
    proof (rule disjE[OF h_cases])
      assume "\<exists>v. \<sigma> = {v}"
      then obtain v where h_v: "\<sigma> = {v}" by (by100 blast)
      have "connected {v}" by (by100 simp)
      thus ?thesis using h_v by (by100 simp)
    next
      assume "\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b"
      then obtain a b where h_ab: "\<sigma> = closed_segment a b" by (by100 blast)
      have "connected (closed_segment a b)" by (rule convex_connected[OF convex_closed_segment])
      thus ?thesis using h_ab by (by100 simp)
    qed
  qed
  show ?thesis
    by (rule geotop_arc_preimage_is_interval[OF harc h\<sigma>_sub h\<sigma>_conn])
qed

(** Infrastructure for Phase 1.A: if K is a complex and K' ⊆ K is closed
    under face-taking (within K), then K' is also a complex. This is the
    classical sub-complex construction. **)
lemma geotop_complex_subset_is_complex:
  fixes K K' :: "'a::euclidean_space set set"
  assumes hKcomp: "geotop_is_complex K"
  assumes hK'_sub: "K' \<subseteq> K"
  assumes hK'_face: "\<forall>\<sigma>\<in>K'. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K'"
  shows "geotop_is_complex K'"
proof -
  have hK_simp: "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
    using conjunct1[OF hKcomp[unfolded geotop_is_complex_def]] by (by100 blast)
  have hK_inter_face: "\<forall>\<sigma>'\<in>K. \<forall>\<tau>'\<in>K. \<sigma>' \<inter> \<tau>' \<noteq> {} \<longrightarrow>
                      geotop_is_face (\<sigma>' \<inter> \<tau>') \<sigma>' \<and> geotop_is_face (\<sigma>' \<inter> \<tau>') \<tau>'"
    using conjunct1[OF conjunct2[OF conjunct2[OF hKcomp[unfolded geotop_is_complex_def]]]]
    by (by100 blast)
  have hK_locfin: "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    using conjunct2[OF conjunct2[OF conjunct2[OF hKcomp[unfolded geotop_is_complex_def]]]]
    by (by100 blast)
  (** K.0 for K'. **)
  have hK'_simp: "\<forall>\<sigma>\<in>K'. geotop_is_simplex \<sigma>"
    using hK_simp hK'_sub by (by100 blast)
  (** K.2 for K'. **)
  have hK'_inter_face: "\<forall>\<sigma>\<in>K'. \<forall>\<tau>\<in>K'. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                       geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
  proof (intro ballI impI)
    fix \<sigma> \<tau> assume h\<sigma>K': "\<sigma> \<in> K'" and h\<tau>K': "\<tau> \<in> K'" and hne: "\<sigma> \<inter> \<tau> \<noteq> {}"
    have h\<sigma>K: "\<sigma> \<in> K" using h\<sigma>K' hK'_sub by (by100 blast)
    have h\<tau>K: "\<tau> \<in> K" using h\<tau>K' hK'_sub by (by100 blast)
    show "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
      using hK_inter_face h\<sigma>K h\<tau>K hne by (by100 blast)
  qed
  (** K.3 for K'. **)
  have hK'_locfin: "\<forall>\<sigma>\<in>K'. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K'. \<tau> \<inter> U \<noteq> {}}"
  proof
    fix \<sigma> assume h\<sigma>K': "\<sigma> \<in> K'"
    have h\<sigma>K: "\<sigma> \<in> K" using h\<sigma>K' hK'_sub by (by100 blast)
    have h_ex_U: "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using hK_locfin h\<sigma>K by (by100 blast)
    obtain U where hopen: "open U" and hsub: "\<sigma> \<subseteq> U"
               and hfin_K: "finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using h_ex_U by (by100 blast)
    have h_sub_sub: "{\<tau>\<in>K'. \<tau> \<inter> U \<noteq> {}} \<subseteq> {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using hK'_sub by (by100 blast)
    have hfin_K': "finite {\<tau>\<in>K'. \<tau> \<inter> U \<noteq> {}}"
      using finite_subset[OF h_sub_sub hfin_K] by (by100 blast)
    show "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K'. \<tau> \<inter> U \<noteq> {}}"
      using hopen hsub hfin_K' by (by100 blast)
  qed
  show ?thesis unfolding geotop_is_complex_def
    using hK'_simp hK'_face hK'_inter_face hK'_locfin by (by100 blast)
qed

(** Infrastructure for Phase 1.A: the restriction of a complex K to those
    simplices contained in an ambient set B' is automatically face-closed
    (faces are subsets of simplices, so inherit the B' containment), hence
    a complex by geotop_complex_subset_is_complex. **)
lemma geotop_complex_restrict_subset_is_complex:
  fixes K :: "'a::euclidean_space set set" and B' :: "'a set"
  assumes hKcomp: "geotop_is_complex K"
  shows "geotop_is_complex {\<sigma>\<in>K. \<sigma> \<subseteq> B'}"
proof -
  let ?K' = "{\<sigma>\<in>K. \<sigma> \<subseteq> B'}"
  have hK'_sub: "?K' \<subseteq> K" by (by100 blast)
  have hK_face: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    using conjunct1[OF conjunct2[OF hKcomp[unfolded geotop_is_complex_def]]]
    by (by100 blast)
  have hK'_face: "\<forall>\<sigma>\<in>?K'. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> ?K'"
  proof (intro ballI allI impI)
    fix \<sigma> \<tau> assume h\<sigma>K': "\<sigma> \<in> ?K'" and h_face: "geotop_is_face \<tau> \<sigma>"
    have h\<sigma>K: "\<sigma> \<in> K" using h\<sigma>K' by (by100 simp)
    have h\<sigma>_sub: "\<sigma> \<subseteq> B'" using h\<sigma>K' by (by100 simp)
    have h\<tau>_sub_\<sigma>: "\<tau> \<subseteq> \<sigma>"
    proof -
      obtain V W where hV_sv: "geotop_simplex_vertices \<sigma> V"
                   and hW_ne: "W \<noteq> {}" and hW_V: "W \<subseteq> V"
                   and h\<tau>_hull: "\<tau> = geotop_convex_hull W"
        using h_face unfolding geotop_is_face_def by (by100 blast)
      have h\<sigma>_hull: "\<sigma> = geotop_convex_hull V"
        using hV_sv unfolding geotop_simplex_vertices_def by (by100 blast)
      have h1: "\<tau> = convex hull W" using h\<tau>_hull geotop_convex_hull_eq_HOL by (by100 simp)
      have h2: "\<sigma> = convex hull V" using h\<sigma>_hull geotop_convex_hull_eq_HOL by (by100 simp)
      have h3: "convex hull W \<subseteq> convex hull V" using hW_V hull_mono by (by100 blast)
      show ?thesis using h1 h2 h3 by (by100 simp)
    qed
    have h\<tau>_K: "\<tau> \<in> K" using hK_face h\<sigma>K h_face by (by100 blast)
    have h\<tau>_sub: "\<tau> \<subseteq> B'" using h\<tau>_sub_\<sigma> h\<sigma>_sub by (by100 blast)
    show "\<tau> \<in> ?K'" using h\<tau>_K h\<tau>_sub by (by100 simp)
  qed
  show ?thesis
    by (rule geotop_complex_subset_is_complex[OF hKcomp hK'_sub hK'_face])
qed

(** Infrastructure for Phase 1.A: the restriction preserves 1-dim-ness. **)
lemma geotop_complex_restrict_preserves_1dim:
  fixes K :: "'a::euclidean_space set set" and B' :: "'a set"
  assumes hK1dim: "geotop_complex_is_1dim K"
  shows "geotop_complex_is_1dim {\<sigma>\<in>K. \<sigma> \<subseteq> B'}"
  using hK1dim unfolding geotop_complex_is_1dim_def by (by100 blast)

(** Phase 1.A: inner-product projection is injective on a closed segment
    between two distinct points. Key fact for endpoint-matching. **)
lemma geotop_inner_diff_inj_on_closed_segment:
  fixes a b :: "'a::euclidean_space"
  assumes hab: "a \<noteq> b"
  shows "inj_on (\<lambda>x. inner (b - a) x) (closed_segment a b)"
proof (rule inj_onI)
  fix x y assume hx: "x \<in> closed_segment a b" and hy: "y \<in> closed_segment a b"
  assume hxy: "inner (b - a) x = inner (b - a) y"
  obtain ux where hux_lb: "0 \<le> ux" and hux_ub: "ux \<le> 1"
              and hx_eq: "x = (1-ux) *\<^sub>R a + ux *\<^sub>R b"
    using hx unfolding closed_segment_def by (by100 blast)
  obtain uy where huy_lb: "0 \<le> uy" and huy_ub: "uy \<le> 1"
              and hy_eq: "y = (1-uy) *\<^sub>R a + uy *\<^sub>R b"
    using hy unfolding closed_segment_def by (by100 blast)
  have h_ba_pos: "0 < inner (b - a) (b - a)" using hab by (by100 simp)
  (** Compute π x and π y in closed form. **)
  have h_inner_add: "\<And>u::real. inner (b - a) ((1-u) *\<^sub>R a + u *\<^sub>R b)
        = inner (b - a) ((1-u) *\<^sub>R a) + inner (b - a) (u *\<^sub>R b)"
    by (rule inner_add_right)
  have h_sc1: "\<And>u::real. inner (b - a) ((1-u) *\<^sub>R a) = (1-u) * inner (b - a) a"
    by (rule inner_scaleR_right)
  have h_sc2: "\<And>u::real. inner (b - a) (u *\<^sub>R b) = u * inner (b - a) b"
    by (rule inner_scaleR_right)
  have h_\<pi>_x: "inner (b - a) x = (1-ux) * inner (b - a) a + ux * inner (b - a) b"
    using hx_eq h_inner_add h_sc1 h_sc2 by (by100 simp)
  have h_\<pi>_y: "inner (b - a) y = (1-uy) * inner (b - a) a + uy * inner (b - a) b"
    using hy_eq h_inner_add h_sc1 h_sc2 by (by100 simp)
  (** Set π x = π y, derive ux = uy. **)
  have h_coef1: "(1-ux) * inner (b - a) a + ux * inner (b - a) b = inner (b - a) x"
    using h_\<pi>_x by (by100 simp)
  have h_coef2: "inner (b - a) x = inner (b - a) y" using hxy by (by100 simp)
  have h_coef3: "inner (b - a) y = (1-uy) * inner (b - a) a + uy * inner (b - a) b"
    using h_\<pi>_y by (by100 simp)
  have h_coef: "(1-ux) * inner (b - a) a + ux * inner (b - a) b
              = (1-uy) * inner (b - a) a + uy * inner (b - a) b"
    using h_coef1 h_coef2 h_coef3 by (by100 simp)
  have h_diff_eq: "(ux - uy) * (inner (b - a) b - inner (b - a) a) = 0"
    using h_coef by (by100 argo)
  have h_ba_eq: "inner (b - a) (b - a) = inner (b - a) b - inner (b - a) a"
    by (rule inner_diff_right)
  have h_diff_pos: "inner (b - a) b - inner (b - a) a > 0"
    using h_ba_eq h_ba_pos by (by100 linarith)
  have h_diff_ne0: "inner (b - a) b - inner (b - a) a \<noteq> 0"
    using h_diff_pos by (by100 linarith)
  have h_uxy_zero: "ux - uy = 0"
  proof -
    have h_or: "ux - uy = 0 \<or> inner (b - a) b - inner (b - a) a = 0"
      using h_diff_eq by (by100 simp)
    show ?thesis using h_or h_diff_ne0 by (by100 blast)
  qed
  have h_uxy_eq: "ux = uy" using h_uxy_zero by (by100 simp)
  show "x = y" using hx_eq hy_eq h_uxy_eq by (by100 simp)
qed

(** Phase 1.A: inner-product projection image of a closed segment.
    The image is the real closed segment between the projected endpoints. **)
lemma geotop_inner_diff_image_closed_segment:
  fixes a b :: "'a::euclidean_space"
  assumes hab: "a \<noteq> b"
  shows "(\<lambda>x. inner (b - a) x) ` closed_segment a b
       = closed_segment (inner (b - a) a) (inner (b - a) b)"
proof -
  let ?\<pi> = "\<lambda>x. inner (b - a) x"
  have h_ba_pos: "0 < inner (b - a) (b - a)" using hab by (by100 simp)
  have h_ba_eq: "inner (b - a) (b - a) = inner (b - a) b - inner (b - a) a"
    by (rule inner_diff_right)
  have h_\<pi>_a_lt_b: "?\<pi> a < ?\<pi> b" using h_ba_eq h_ba_pos by (by100 linarith)
  (** Real closed_segment = interval. **)
  have h_cseg_piab: "closed_segment (?\<pi> a) (?\<pi> b) = {?\<pi> a..?\<pi> b}"
    using h_\<pi>_a_lt_b closed_segment_eq_real_ivl by (by100 simp)
  (** Parametrization identities. **)
  have h_inner_add: "\<And>u::real. inner (b - a) ((1-u) *\<^sub>R a + u *\<^sub>R b)
        = inner (b - a) ((1-u) *\<^sub>R a) + inner (b - a) (u *\<^sub>R b)"
    by (rule inner_add_right)
  have h_sc1: "\<And>u::real. inner (b - a) ((1-u) *\<^sub>R a) = (1-u) * inner (b - a) a"
    by (rule inner_scaleR_right)
  have h_sc2: "\<And>u::real. inner (b - a) (u *\<^sub>R b) = u * inner (b - a) b"
    by (rule inner_scaleR_right)
  have h_\<pi>_param: "\<And>u::real. ?\<pi> ((1-u) *\<^sub>R a + u *\<^sub>R b) = (1-u) * ?\<pi> a + u * ?\<pi> b"
    using h_inner_add h_sc1 h_sc2 by (by100 simp)
  show ?thesis
  proof
    show "?\<pi> ` closed_segment a b \<subseteq> closed_segment (?\<pi> a) (?\<pi> b)"
    proof
      fix y assume hy_img: "y \<in> ?\<pi> ` closed_segment a b"
      obtain x where hx_seg: "x \<in> closed_segment a b" and hyx: "y = ?\<pi> x"
        using hy_img by (by100 blast)
      obtain u where hu_lb: "0 \<le> u" and hu_ub: "u \<le> 1"
                 and hx_eq: "x = (1-u) *\<^sub>R a + u *\<^sub>R b"
        using hx_seg unfolding closed_segment_def by (by100 blast)
      have h_\<pi>_x_val: "?\<pi> x = (1-u) * ?\<pi> a + u * ?\<pi> b"
        using hx_eq h_\<pi>_param by (by100 simp)
      have h_y_val: "y = (1-u) * ?\<pi> a + u * ?\<pi> b" using hyx h_\<pi>_x_val by (by100 simp)
      have h_ba_ge: "?\<pi> b - ?\<pi> a \<ge> 0" using h_\<pi>_a_lt_b by (by100 linarith)
      have h_y_lb: "?\<pi> a \<le> y"
      proof -
        have h_diff_form: "y - ?\<pi> a = u * (?\<pi> b - ?\<pi> a)" using h_y_val by (by100 argo)
        have h_prod_nn: "u * (?\<pi> b - ?\<pi> a) \<ge> 0"
          by (rule mult_nonneg_nonneg[OF hu_lb h_ba_ge])
        have h_ya_nn: "y - ?\<pi> a \<ge> 0" using h_diff_form h_prod_nn by (by100 simp)
        show ?thesis using h_ya_nn by (by100 simp)
      qed
      have h_y_ub: "y \<le> ?\<pi> b"
      proof -
        have h_diff_form: "?\<pi> b - y = (1-u) * (?\<pi> b - ?\<pi> a)" using h_y_val by (by100 argo)
        have h_1mu_nn: "1 - u \<ge> 0" using hu_ub by (by100 simp)
        have h_prod_nn: "(1-u) * (?\<pi> b - ?\<pi> a) \<ge> 0"
          by (rule mult_nonneg_nonneg[OF h_1mu_nn h_ba_ge])
        have h_by_nn: "?\<pi> b - y \<ge> 0" using h_diff_form h_prod_nn by (by100 simp)
        show ?thesis using h_by_nn by (by100 simp)
      qed
      have h_y_ivl: "y \<in> {?\<pi> a..?\<pi> b}" using h_y_lb h_y_ub by (by100 simp)
      show "y \<in> closed_segment (?\<pi> a) (?\<pi> b)" using h_y_ivl h_cseg_piab by (by100 simp)
    qed
    show "closed_segment (?\<pi> a) (?\<pi> b) \<subseteq> ?\<pi> ` closed_segment a b"
    proof
      fix y assume hy: "y \<in> closed_segment (?\<pi> a) (?\<pi> b)"
      have h_y_ivl: "y \<in> {?\<pi> a..?\<pi> b}" using hy h_cseg_piab by (by100 simp)
      have h_y_lb: "?\<pi> a \<le> y" using h_y_ivl by (by100 simp)
      have h_y_ub: "y \<le> ?\<pi> b" using h_y_ivl by (by100 simp)
      have h_ba_pos_real: "?\<pi> b - ?\<pi> a > 0" using h_\<pi>_a_lt_b by (by100 linarith)
      define u where "u = (y - ?\<pi> a) / (?\<pi> b - ?\<pi> a)"
      have hu_lb: "0 \<le> u" unfolding u_def using h_y_lb h_ba_pos_real by (by100 simp)
      have hu_ub: "u \<le> 1"
      proof -
        have h_num_le: "y - ?\<pi> a \<le> ?\<pi> b - ?\<pi> a" using h_y_ub by (by100 simp)
        have h_div_le: "(y - ?\<pi> a) / (?\<pi> b - ?\<pi> a) \<le> 1"
          using h_num_le h_ba_pos_real divide_le_eq_1_pos by (by100 blast)
        show ?thesis unfolding u_def using h_div_le by (by100 simp)
      qed
      have h_y_from_u: "y = ?\<pi> a + u * (?\<pi> b - ?\<pi> a)"
        unfolding u_def using h_ba_pos_real by (by100 simp)
      have hy_param: "y = (1-u) * ?\<pi> a + u * ?\<pi> b" using h_y_from_u by (by100 argo)
      let ?x = "(1-u) *\<^sub>R a + u *\<^sub>R b"
      have h_x_seg: "?x \<in> closed_segment a b"
        unfolding closed_segment_def using hu_lb hu_ub by (by100 blast)
      have h_\<pi>_x: "?\<pi> ?x = (1-u) * ?\<pi> a + u * ?\<pi> b" by (rule h_\<pi>_param)
      have h_\<pi>_x_y: "?\<pi> ?x = y" using h_\<pi>_x hy_param by (by100 simp)
      show "y \<in> ?\<pi> ` closed_segment a b" using h_x_seg h_\<pi>_x_y by (by100 blast)
    qed
  qed
qed

(** Phase 1.A endpoint-matching: if γ is a continuous bijection {p..q} →
    closed_segment a b (with a ≠ b), then {γ p, γ q} = {a, b}.
    Uses the two projection helpers + continuous_injective_image_segment_1. **)
lemma geotop_homeomorphism_segment_endpoints:
  fixes p q :: real
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  fixes a b :: 'a
  assumes hpq: "p \<le> q"
  assumes hab: "a \<noteq> b"
  assumes h_cont: "continuous_on {p..q} \<gamma>"
  assumes h_inj: "inj_on \<gamma> {p..q}"
  assumes h_img: "\<gamma> ` {p..q} = closed_segment a b"
  shows "{\<gamma> p, \<gamma> q} = {a, b}"
proof -
  let ?\<pi> = "\<lambda>x. inner (b - a) x"
  have h\<pi>_cont: "continuous_on UNIV ?\<pi>" by (intro continuous_intros)
  have h\<pi>_inj_seg: "inj_on ?\<pi> (closed_segment a b)"
    by (rule geotop_inner_diff_inj_on_closed_segment[OF hab])
  have h\<pi>_img_seg: "?\<pi> ` closed_segment a b = closed_segment (?\<pi> a) (?\<pi> b)"
    by (rule geotop_inner_diff_image_closed_segment[OF hab])
  (** π ∘ γ is continuous injective on {p..q}. **)
  have h_\<pi>\<gamma>_cont: "continuous_on {p..q} (?\<pi> \<circ> \<gamma>)"
  proof -
    have h_cc: "continuous_on {p..q} \<gamma>
                \<and> continuous_on (\<gamma> ` {p..q}) ?\<pi>"
    proof
      show "continuous_on {p..q} \<gamma>" by (rule h_cont)
      show "continuous_on (\<gamma> ` {p..q}) ?\<pi>"
        using h\<pi>_cont continuous_on_subset by (by100 blast)
    qed
    show ?thesis using h_cc continuous_on_compose by (by100 blast)
  qed
  have h_\<pi>\<gamma>_inj: "inj_on (?\<pi> \<circ> \<gamma>) {p..q}"
  proof (rule inj_onI)
    fix s1 s2 assume hs1: "s1 \<in> {p..q}" and hs2: "s2 \<in> {p..q}"
    assume h_eq: "(?\<pi> \<circ> \<gamma>) s1 = (?\<pi> \<circ> \<gamma>) s2"
    have h\<gamma>s1_seg: "\<gamma> s1 \<in> closed_segment a b" using hs1 h_img by (by100 blast)
    have h\<gamma>s2_seg: "\<gamma> s2 \<in> closed_segment a b" using hs2 h_img by (by100 blast)
    have h_\<pi>_eq: "?\<pi> (\<gamma> s1) = ?\<pi> (\<gamma> s2)" using h_eq by (by100 simp)
    have h\<gamma>_eq: "\<gamma> s1 = \<gamma> s2"
      using h\<pi>_inj_seg h\<gamma>s1_seg h\<gamma>s2_seg h_\<pi>_eq unfolding inj_on_def by (by100 blast)
    show "s1 = s2" using h_inj hs1 hs2 h\<gamma>_eq unfolding inj_on_def by (by100 blast)
  qed
  (** {p..q} = closed_segment p q for real interval. **)
  have h_pq_seg: "closed_segment p q = {p..q}"
    using hpq closed_segment_eq_real_ivl by (by100 simp)
  have h_\<pi>\<gamma>_cont_seg: "continuous_on (closed_segment p q) (?\<pi> \<circ> \<gamma>)"
    using h_\<pi>\<gamma>_cont h_pq_seg by (by100 simp)
  have h_\<pi>\<gamma>_inj_seg: "inj_on (?\<pi> \<circ> \<gamma>) (closed_segment p q)"
    using h_\<pi>\<gamma>_inj h_pq_seg by (by100 simp)
  (** Apply library lemma. **)
  have h_\<pi>\<gamma>_img: "(?\<pi> \<circ> \<gamma>) ` closed_segment p q
                      = closed_segment ((?\<pi> \<circ> \<gamma>) p) ((?\<pi> \<circ> \<gamma>) q)"
    by (rule continuous_injective_image_segment_1[OF h_\<pi>\<gamma>_cont_seg h_\<pi>\<gamma>_inj_seg])
  (** Compute both sides. **)
  have h_lhs: "(?\<pi> \<circ> \<gamma>) ` closed_segment p q = ?\<pi> ` closed_segment a b"
  proof -
    have h_ic: "?\<pi> ` (\<gamma> ` {p..q}) = (?\<pi> \<circ> \<gamma>) ` {p..q}" by (rule image_comp)
    have h_subst1: "\<gamma> ` {p..q} = closed_segment a b" by (rule h_img)
    have h_subst2: "?\<pi> ` (\<gamma> ` {p..q}) = ?\<pi> ` closed_segment a b"
      using h_subst1 by (by100 simp)
    have h_chain: "(?\<pi> \<circ> \<gamma>) ` {p..q} = ?\<pi> ` closed_segment a b"
      using h_ic h_subst2 by (by100 simp)
    have h_seg_eq: "closed_segment p q = {p..q}" by (rule h_pq_seg)
    show ?thesis using h_chain h_seg_eq by (by100 simp)
  qed
  have h_rhs: "closed_segment ((?\<pi> \<circ> \<gamma>) p) ((?\<pi> \<circ> \<gamma>) q)
             = closed_segment (?\<pi> (\<gamma> p)) (?\<pi> (\<gamma> q))" by (by100 simp)
  have h_combined: "?\<pi> ` closed_segment a b = closed_segment (?\<pi> (\<gamma> p)) (?\<pi> (\<gamma> q))"
    using h_lhs h_rhs h_\<pi>\<gamma>_img by (by100 simp)
  have h_seg_eq_\<pi>: "closed_segment (?\<pi> (\<gamma> p)) (?\<pi> (\<gamma> q)) = closed_segment (?\<pi> a) (?\<pi> b)"
    using h_combined h\<pi>_img_seg by (by100 simp)
  (** From equal closed segments in ℝ: {endpoints} are equal as sets. **)
  have h_cseg_iff: "(closed_segment (?\<pi> (\<gamma> p)) (?\<pi> (\<gamma> q)) = closed_segment (?\<pi> a) (?\<pi> b))
                    = ({?\<pi> (\<gamma> p), ?\<pi> (\<gamma> q)} = {?\<pi> a, ?\<pi> b})"
    by (rule closed_segment_eq)
  have h_\<pi>_endpoints: "{?\<pi> (\<gamma> p), ?\<pi> (\<gamma> q)} = {?\<pi> a, ?\<pi> b}"
    using h_seg_eq_\<pi> h_cseg_iff by (by100 simp)
  (** γ p, γ q ∈ closed_segment a b. **)
  have hp_in_pq: "p \<in> {p..q}" using hpq by (by100 simp)
  have hq_in_pq: "q \<in> {p..q}" using hpq by (by100 simp)
  have h\<gamma>p_seg: "\<gamma> p \<in> closed_segment a b" using hp_in_pq h_img by (by100 blast)
  have h\<gamma>q_seg: "\<gamma> q \<in> closed_segment a b" using hq_in_pq h_img by (by100 blast)
  have ha_seg: "a \<in> closed_segment a b" by (by100 simp)
  have hb_seg: "b \<in> closed_segment a b" by (by100 simp)
  (** π inj on closed_segment a b: project equality back. **)
  have h_\<pi>\<gamma>p_in: "?\<pi> (\<gamma> p) \<in> {?\<pi> a, ?\<pi> b}"
    using h_\<pi>_endpoints by (by100 blast)
  have h_\<pi>\<gamma>q_in: "?\<pi> (\<gamma> q) \<in> {?\<pi> a, ?\<pi> b}"
    using h_\<pi>_endpoints by (by100 blast)
  have h_\<pi>a_in: "?\<pi> a \<in> {?\<pi> (\<gamma> p), ?\<pi> (\<gamma> q)}"
    using h_\<pi>_endpoints by (by100 blast)
  have h_\<pi>b_in: "?\<pi> b \<in> {?\<pi> (\<gamma> p), ?\<pi> (\<gamma> q)}"
    using h_\<pi>_endpoints by (by100 blast)
  have h\<pi>p_disj: "?\<pi> (\<gamma> p) = ?\<pi> a \<or> ?\<pi> (\<gamma> p) = ?\<pi> b"
    using h_\<pi>\<gamma>p_in by (by100 blast)
  have h\<pi>q_disj: "?\<pi> (\<gamma> q) = ?\<pi> a \<or> ?\<pi> (\<gamma> q) = ?\<pi> b"
    using h_\<pi>\<gamma>q_in by (by100 blast)
  (** π a < π b so they're distinct — use this to rule out both endpoints matching same. **)
  have h_ba_pos': "0 < inner (b - a) (b - a)" using hab by (by100 simp)
  have h_ba_eq': "inner (b - a) (b - a) = inner (b - a) b - inner (b - a) a"
    by (rule inner_diff_right)
  have h_\<pi>_a_lt_b: "?\<pi> a < ?\<pi> b" using h_ba_eq' h_ba_pos' by (by100 linarith)
  have h_\<pi>_ne: "?\<pi> a \<noteq> ?\<pi> b" using h_\<pi>_a_lt_b by (by100 linarith)
  have h_cases: "(?\<pi> (\<gamma> p) = ?\<pi> a \<and> ?\<pi> (\<gamma> q) = ?\<pi> b)
               \<or> (?\<pi> (\<gamma> p) = ?\<pi> b \<and> ?\<pi> (\<gamma> q) = ?\<pi> a)"
  proof (rule disjE[OF h\<pi>p_disj])
    assume h_p_a: "?\<pi> (\<gamma> p) = ?\<pi> a"
    have h_q_b: "?\<pi> (\<gamma> q) = ?\<pi> b"
    proof (rule disjE[OF h\<pi>q_disj])
      assume h_q_a: "?\<pi> (\<gamma> q) = ?\<pi> a"
      have h_set_small: "{?\<pi> (\<gamma> p), ?\<pi> (\<gamma> q)} = {?\<pi> a}"
        using h_p_a h_q_a by (by100 simp)
      have h_bab: "?\<pi> b \<in> {?\<pi> a}" using h_\<pi>b_in h_set_small by (by100 simp)
      have h_ba_eq: "?\<pi> b = ?\<pi> a" using h_bab by (by100 simp)
      have h_false: False using h_ba_eq h_\<pi>_ne by (by100 simp)
      show ?thesis using h_false by (by100 blast)
    next
      assume h_q_b: "?\<pi> (\<gamma> q) = ?\<pi> b" show ?thesis by (rule h_q_b)
    qed
    show ?thesis using h_p_a h_q_b by (by100 blast)
  next
    assume h_p_b: "?\<pi> (\<gamma> p) = ?\<pi> b"
    have h_q_a: "?\<pi> (\<gamma> q) = ?\<pi> a"
    proof (rule disjE[OF h\<pi>q_disj])
      assume h_q_a: "?\<pi> (\<gamma> q) = ?\<pi> a" show ?thesis by (rule h_q_a)
    next
      assume h_q_b: "?\<pi> (\<gamma> q) = ?\<pi> b"
      have h_set_small: "{?\<pi> (\<gamma> p), ?\<pi> (\<gamma> q)} = {?\<pi> b}"
        using h_p_b h_q_b by (by100 simp)
      have h_aab: "?\<pi> a \<in> {?\<pi> b}" using h_\<pi>a_in h_set_small by (by100 simp)
      have h_ab_eq: "?\<pi> a = ?\<pi> b" using h_aab by (by100 simp)
      have h_false: False using h_ab_eq h_\<pi>_ne by (by100 simp)
      show ?thesis using h_false by (by100 blast)
    qed
    show ?thesis using h_p_b h_q_a by (by100 blast)
  qed
  show "{\<gamma> p, \<gamma> q} = {a, b}"
  proof (rule disjE[OF h_cases])
    assume h_ord: "?\<pi> (\<gamma> p) = ?\<pi> a \<and> ?\<pi> (\<gamma> q) = ?\<pi> b"
    have h\<gamma>p_a: "\<gamma> p = a"
      using h\<pi>_inj_seg h\<gamma>p_seg ha_seg h_ord unfolding inj_on_def by (by100 blast)
    have h\<gamma>q_b: "\<gamma> q = b"
      using h\<pi>_inj_seg h\<gamma>q_seg hb_seg h_ord unfolding inj_on_def by (by100 blast)
    show ?thesis using h\<gamma>p_a h\<gamma>q_b by (by100 blast)
  next
    assume h_ord: "?\<pi> (\<gamma> p) = ?\<pi> b \<and> ?\<pi> (\<gamma> q) = ?\<pi> a"
    have h\<gamma>p_b: "\<gamma> p = b"
      using h\<pi>_inj_seg h\<gamma>p_seg hb_seg h_ord unfolding inj_on_def by (by100 blast)
    have h\<gamma>q_a: "\<gamma> q = a"
      using h\<pi>_inj_seg h\<gamma>q_seg ha_seg h_ord unfolding inj_on_def by (by100 blast)
    show ?thesis using h\<gamma>p_b h\<gamma>q_a by (by100 blast)
  qed
qed

(** Phase 1.A: for σ ∈ K a 1-simplex (closed_segment a b, a ≠ b) with
    K 1-dim and polyhedron K = path_image γ (γ arc), the preimage of σ
    under γ is a closed interval [p, q] such that γ p, γ q are exactly
    the vertices {a, b} of σ. Composes preimage_simplex_is_interval
    with homeomorphism_segment_endpoints. **)
lemma geotop_arc_1simplex_preimage_structure:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  fixes K :: "'a set set"
  fixes \<sigma> :: "'a set" and a b :: 'a
  assumes harc: "arc \<gamma>"
  assumes hK1dim: "geotop_complex_is_1dim K"
  assumes hKpoly: "geotop_polyhedron K = path_image \<gamma>"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>ab: "\<sigma> = closed_segment a b" and hab: "a \<noteq> b"
  shows "\<exists>p q. p \<le> q \<and> p \<in> {0..1} \<and> q \<in> {0..1}
           \<and> {s\<in>{0..1}. \<gamma> s \<in> \<sigma>} = {p..q}
           \<and> {\<gamma> p, \<gamma> q} = {a, b}"
proof -
  let ?I = "{s\<in>{0..1}. \<gamma> s \<in> \<sigma>}"
  have h_cont_\<gamma>: "continuous_on {0..1} \<gamma>"
    using harc unfolding arc_def path_def by (by100 blast)
  have h_inj_\<gamma>: "inj_on \<gamma> {0..1}"
    using harc unfolding arc_def by (by100 blast)
  have h_pre_int: "is_interval ?I"
    by (rule geotop_arc_preimage_simplex_is_interval[OF harc hK1dim hKpoly h\<sigma>K])
  have h_a_\<sigma>: "a \<in> \<sigma>" using h\<sigma>ab by (by100 simp)
  have h\<sigma>_sub_pim: "\<sigma> \<subseteq> path_image \<gamma>"
    using h\<sigma>K hKpoly unfolding geotop_polyhedron_def by (by100 blast)
  have h_a_pim: "a \<in> path_image \<gamma>" using h_a_\<sigma> h\<sigma>_sub_pim by (by100 blast)
  obtain sa where hsa_01: "sa \<in> {0..1}" and hsa_eq: "\<gamma> sa = a"
    using h_a_pim unfolding path_image_def by (by100 blast)
  have hsa_I: "sa \<in> ?I" using hsa_01 hsa_eq h_a_\<sigma> by (by100 simp)
  have h_I_ne: "?I \<noteq> {}" using hsa_I by (by100 blast)
  have h_I_sub_01: "?I \<subseteq> {0..1}" by (by100 blast)
  have h_\<sigma>_closed: "closed \<sigma>" using h\<sigma>ab by (by100 simp)
  have h_I_closed: "closed ?I"
  proof -
    have h_eq: "?I = \<gamma> -` \<sigma> \<inter> {0..1}" by (by100 blast)
    have h_01_closed: "closed ({0..1}::real set)" by (by100 simp)
    have h_cl: "closed (\<gamma> -` \<sigma> \<inter> {0..1})"
      using continuous_on_closed_vimage[OF h_01_closed] h_cont_\<gamma> h_\<sigma>_closed by (by100 blast)
    show ?thesis using h_eq h_cl by (by100 simp)
  qed
  have h_I_bd: "bounded ?I"
    using h_I_sub_01 bounded_closed_interval bounded_subset by (by100 blast)
  have h_I_bdd_below: "bdd_below ?I" by (rule bounded_imp_bdd_below[OF h_I_bd])
  have h_I_bdd_above: "bdd_above ?I" by (rule bounded_imp_bdd_above[OF h_I_bd])
  define p where "p = Inf ?I"
  define q where "q = Sup ?I"
  have hp_min: "p \<in> ?I"
    unfolding p_def by (rule closed_contains_Inf[OF h_I_ne h_I_bdd_below h_I_closed])
  have hq_max: "q \<in> ?I"
    unfolding q_def by (rule closed_contains_Sup[OF h_I_ne h_I_bdd_above h_I_closed])
  have hp_le: "\<forall>y\<in>?I. p \<le> y"
  proof
    fix y assume hy: "y \<in> ?I"
    show "p \<le> y" unfolding p_def by (rule cInf_lower[OF hy h_I_bdd_below])
  qed
  have hq_ge: "\<forall>y\<in>?I. y \<le> q"
  proof
    fix y assume hy: "y \<in> ?I"
    show "y \<le> q" unfolding q_def by (rule cSup_upper[OF hy h_I_bdd_above])
  qed
  have h_p_le_q: "p \<le> q" using hp_min hq_ge by (by100 blast)
  have hp_01: "p \<in> {0..1}" using hp_min by (by100 simp)
  have hq_01: "q \<in> {0..1}" using hq_max by (by100 simp)
  have h_I_sub_pq: "?I \<subseteq> {p..q}"
  proof
    fix y assume hy: "y \<in> ?I"
    have h1: "p \<le> y" using hp_le hy by (by100 blast)
    have h2: "y \<le> q" using hq_ge hy by (by100 blast)
    show "y \<in> {p..q}" using h1 h2 by (by100 simp)
  qed
  have h_pq_sub_I: "{p..q} \<subseteq> ?I"
  proof
    fix s assume hs: "s \<in> {p..q}"
    have h_s_ge: "p \<le> s" using hs by (by100 simp)
    have h_s_le: "s \<le> q" using hs by (by100 simp)
    show "s \<in> ?I" using h_pre_int hp_min hq_max h_s_ge h_s_le
      unfolding is_interval_1 by (by100 blast)
  qed
  have h_I_eq: "?I = {p..q}" using h_I_sub_pq h_pq_sub_I by (by100 blast)
  (** γ on {p..q} is cts inj with image σ. **)
  have h_pq_sub_01: "{p..q} \<subseteq> {0..1}" using h_I_eq h_I_sub_01 by (by100 simp)
  have h_cont_pq: "continuous_on {p..q} \<gamma>"
    using h_cont_\<gamma> h_pq_sub_01 continuous_on_subset by (by100 blast)
  have h_inj_pq: "inj_on \<gamma> {p..q}"
    using h_inj_\<gamma> h_pq_sub_01 inj_on_subset by (by100 blast)
  have h_\<gamma>_pq_eq_\<sigma>: "\<gamma> ` {p..q} = \<sigma>"
  proof
    show "\<gamma> ` {p..q} \<subseteq> \<sigma>"
    proof
      fix y assume "y \<in> \<gamma> ` {p..q}"
      then obtain s where hs: "s \<in> {p..q}" and hy: "y = \<gamma> s" by (by100 blast)
      have hs_I: "s \<in> ?I" using hs h_I_eq by (by100 simp)
      show "y \<in> \<sigma>" using hs_I hy by (by100 simp)
    qed
    show "\<sigma> \<subseteq> \<gamma> ` {p..q}"
    proof
      fix y assume hy: "y \<in> \<sigma>"
      have h_y_pim: "y \<in> path_image \<gamma>" using hy h\<sigma>_sub_pim by (by100 blast)
      obtain s where hs_01: "s \<in> {0..1}" and hs_y: "y = \<gamma> s"
        using h_y_pim unfolding path_image_def by (by100 blast)
      have hs_in_I: "s \<in> ?I" using hs_01 hs_y hy by (by100 simp)
      have hs_pq: "s \<in> {p..q}" using hs_in_I h_I_eq by (by100 simp)
      show "y \<in> \<gamma> ` {p..q}" using hs_pq hs_y by (by100 blast)
    qed
  qed
  (** Apply endpoint helper. **)
  have h_\<gamma>_img_ab: "\<gamma> ` {p..q} = closed_segment a b" using h_\<gamma>_pq_eq_\<sigma> h\<sigma>ab by (by100 simp)
  have h_endpoints: "{\<gamma> p, \<gamma> q} = {a, b}"
    by (rule geotop_homeomorphism_segment_endpoints
             [OF h_p_le_q hab h_cont_pq h_inj_pq h_\<gamma>_img_ab])
  show ?thesis using h_p_le_q hp_01 hq_01 h_I_eq h_endpoints by (by100 blast)
qed

(** Every broken line is compact (finite union of compact simplices). **)
lemma geotop_broken_line_compact:
  fixes B :: "'a::euclidean_space set"
  assumes hB: "geotop_is_broken_line B"
  shows "compact B"
proof -
  obtain K where hK: "geotop_is_complex K" and hK_1dim: "geotop_complex_is_1dim K"
              and hK_poly: "geotop_polyhedron K = B" and hK_fin: "finite K"
    using geotop_broken_line_finite_witness[OF hB] by (by100 blast)
  have hsim_all: "\<forall>\<tau>\<in>K. geotop_is_simplex \<tau>"
    by (rule conjunct1[OF hK[unfolded geotop_is_complex_def]])
  have hK_compact_all: "\<forall>\<sigma>\<in>K. compact \<sigma>"
  proof
    fix \<sigma> assume h\<sigma>K: "\<sigma> \<in> K"
    have hsim: "geotop_is_simplex \<sigma>" using hsim_all h\<sigma>K by (by100 blast)
    obtain V m n where hV_fin: "finite V" and h\<sigma>_hull: "\<sigma> = geotop_convex_hull V"
      using hsim unfolding geotop_is_simplex_def by (by100 blast)
    have h\<sigma>_hullHOL: "\<sigma> = convex hull V"
      using h\<sigma>_hull geotop_convex_hull_eq_HOL by (by100 simp)
    show "compact \<sigma>"
      using h\<sigma>_hullHOL hV_fin finite_imp_compact_convex_hull by (by100 simp)
  qed
  have hK_compact: "compact (geotop_polyhedron K)"
    unfolding geotop_polyhedron_def using hK_fin hK_compact_all by (by100 blast)
  show ?thesis using hK_compact hK_poly by (by100 simp)
qed

lemma geotop_broken_line_closed:
  fixes B :: "'a::euclidean_space set"
  assumes hB: "geotop_is_broken_line B"
  shows "closed B"
  using geotop_broken_line_compact[OF hB] compact_imp_closed by (by100 blast)

(** Phase 1.A main: the sub-arc image γ([s_lo, s_hi]) is the polyhedron
    of a 1-dim sub-complex. Construction: subdivide K at γ(s_lo), γ(s_hi)
    then restrict to simplices contained in γ([s_lo, s_hi]). **)
lemma geotop_subarc_polyhedron:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  fixes B :: "'a set"
  fixes s_lo s_hi :: real
  assumes hB: "geotop_is_broken_line B"
  assumes harc: "arc \<gamma>"
  assumes hpim: "path_image \<gamma> = B"
  assumes hs_lo: "s_lo \<in> {0..1}"
  assumes hs_hi: "s_hi \<in> {0..1}"
  assumes hs_lt: "s_lo < s_hi"
  shows "\<exists>K'. geotop_is_complex K' \<and> geotop_polyhedron K' = \<gamma> ` closed_segment s_lo s_hi
            \<and> geotop_complex_is_1dim K'"
proof -
  let ?X = "\<gamma> s_lo"
  let ?Y = "\<gamma> s_hi"
  let ?B' = "\<gamma> ` closed_segment s_lo s_hi"
  have h_seg_eq: "closed_segment s_lo s_hi = {s_lo..s_hi}"
    using hs_lt closed_segment_eq_real_ivl by (by100 simp)
  have hB'_eq: "?B' = \<gamma> ` {s_lo..s_hi}" using h_seg_eq by (by100 simp)
  (** Witnessing complex K. **)
  obtain K where hK: "geotop_is_complex K" and hK1: "geotop_complex_is_1dim K"
              and hKpoly: "geotop_polyhedron K = B"
    using hB unfolding geotop_is_broken_line_def by (by100 blast)
  have hX_B: "?X \<in> B"
    using hs_lo hpim unfolding path_image_def by (by100 blast)
  have hY_B: "?Y \<in> B"
    using hs_hi hpim unfolding path_image_def by (by100 blast)
  have hX_poly: "?X \<in> geotop_polyhedron K" using hX_B hKpoly by (by100 simp)
  have hY_poly: "?Y \<in> geotop_polyhedron K" using hY_B hKpoly by (by100 simp)
  (** Subdivide at X, Y. **)
  have h_ex_K'': "\<exists>K''. geotop_is_complex K'' \<and> geotop_complex_is_1dim K''
                \<and> geotop_polyhedron K'' = geotop_polyhedron K
                \<and> {?X} \<in> K'' \<and> {?Y} \<in> K''
                \<and> (finite K \<longrightarrow> finite K'')"
    by (rule geotop_complex_subdivide_at_two[OF hK hK1 hX_poly hY_poly])
  obtain K'' where hK''_comp: "geotop_is_complex K''"
                and hK''_1dim: "geotop_complex_is_1dim K''"
                and hK''_poly: "geotop_polyhedron K'' = geotop_polyhedron K"
                and hX_K'': "{?X} \<in> K''" and hY_K'': "{?Y} \<in> K''"
    using h_ex_K'' by (by100 blast)
  have hK''_poly_B: "geotop_polyhedron K'' = B"
    using hK''_poly hKpoly by (by100 simp)
  have hK''_poly_pim: "geotop_polyhedron K'' = path_image \<gamma>"
    using hK''_poly_B hpim by (by100 simp)
  (** K' = {σ ∈ K''. σ ⊆ ?B'}. 1-dim complex by helpers. **)
  let ?K' = "{\<sigma>\<in>K''. \<sigma> \<subseteq> ?B'}"
  have hK'_comp: "geotop_is_complex ?K'"
    by (rule geotop_complex_restrict_subset_is_complex[OF hK''_comp])
  have hK'_1dim: "geotop_complex_is_1dim ?K'"
    by (rule geotop_complex_restrict_preserves_1dim[OF hK''_1dim])
  (** polyhedron K' ⊆ ?B'. **)
  have hK'_sub_B': "geotop_polyhedron ?K' \<subseteq> ?B'"
  proof
    fix x assume hx: "x \<in> geotop_polyhedron ?K'"
    then obtain \<sigma> where h\<sigma>K': "\<sigma> \<in> ?K'" and hx\<sigma>: "x \<in> \<sigma>"
      unfolding geotop_polyhedron_def by (by100 blast)
    have h\<sigma>_sub_B': "\<sigma> \<subseteq> ?B'" using h\<sigma>K' by (by100 simp)
    show "x \<in> ?B'" using hx\<sigma> h\<sigma>_sub_B' by (by100 blast)
  qed
  (** ?B' ⊆ polyhedron K'. Key direction. **)
  have hB'_sub_K': "?B' \<subseteq> geotop_polyhedron ?K'"
  proof
    fix x assume hx: "x \<in> ?B'"
    obtain t where ht_mem: "t \<in> closed_segment s_lo s_hi" and hxt: "x = \<gamma> t"
      using hx by (by100 blast)
    have ht_seg: "t \<in> {s_lo..s_hi}" using ht_mem h_seg_eq by (by100 simp)
    have ht_lo: "s_lo \<le> t" using ht_seg by (by100 simp)
    have ht_hi: "t \<le> s_hi" using ht_seg by (by100 simp)
    have ht_01: "t \<in> {0..1}" using ht_seg hs_lo hs_hi by (by100 auto)
    (** Split on boundary vs interior. **)
    have h_tcases: "t = s_lo \<or> t = s_hi \<or> (s_lo < t \<and> t < s_hi)"
      using ht_lo ht_hi by (by100 linarith)
    show "x \<in> geotop_polyhedron ?K'"
    proof (rule disjE[OF h_tcases])
      assume h_tlo: "t = s_lo"
      have hx_X: "x = ?X" using hxt h_tlo by (by100 simp)
      have hX_B': "?X \<in> ?B'"
      proof -
        have hs_lo_seg: "s_lo \<in> closed_segment s_lo s_hi"
          using h_seg_eq ht_seg h_tlo by (by100 simp)
        show ?thesis using hs_lo_seg by (by100 blast)
      qed
      have hsing_sub: "{?X} \<subseteq> ?B'" using hX_B' by (by100 simp)
      have hsing_K': "{?X} \<in> ?K'" using hX_K'' hsing_sub by (by100 simp)
      have hx_sing: "x \<in> {?X}" using hx_X by (by100 simp)
      show ?thesis using hx_sing hsing_K'
        unfolding geotop_polyhedron_def by (by100 blast)
    next
      assume h_rest1: "t = s_hi \<or> (s_lo < t \<and> t < s_hi)"
      show ?thesis
      proof (rule disjE[OF h_rest1])
        assume h_thi: "t = s_hi"
        have hx_Y: "x = ?Y" using hxt h_thi by (by100 simp)
        have hY_B': "?Y \<in> ?B'"
        proof -
          have hs_hi_seg: "s_hi \<in> closed_segment s_lo s_hi"
            using h_seg_eq ht_seg h_thi by (by100 simp)
          show ?thesis using hs_hi_seg by (by100 blast)
        qed
        have hsing_sub: "{?Y} \<subseteq> ?B'" using hY_B' by (by100 simp)
        have hsing_K': "{?Y} \<in> ?K'" using hY_K'' hsing_sub by (by100 simp)
        have hx_sing: "x \<in> {?Y}" using hx_Y by (by100 simp)
        show ?thesis using hx_sing hsing_K'
          unfolding geotop_polyhedron_def by (by100 blast)
      next
        assume h_tint: "s_lo < t \<and> t < s_hi"
        have h_lo_lt_t: "s_lo < t" using h_tint by (by100 blast)
        have h_t_lt_hi: "t < s_hi" using h_tint by (by100 blast)
        have hx_B: "x \<in> B"
        proof -
          have "x \<in> path_image \<gamma>"
            using hxt ht_01 unfolding path_image_def by (by100 blast)
          thus ?thesis using hpim by (by100 simp)
        qed
        have hx_K'': "x \<in> geotop_polyhedron K''" using hx_B hK''_poly_B by (by100 simp)
        obtain \<sigma> where h\<sigma>_K'': "\<sigma> \<in> K''" and hx\<sigma>: "x \<in> \<sigma>"
          using hx_K'' unfolding geotop_polyhedron_def by (by100 blast)
        (** Show σ ⊆ ?B' using 1-simplex analysis. **)
        have h\<sigma>_cases: "(\<exists>w. \<sigma> = {w}) \<or> (\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b)"
          by (rule geotop_1dim_simplex_cases[OF hK''_1dim h\<sigma>_K''])
        have h\<sigma>_sub_B': "\<sigma> \<subseteq> ?B'"
        proof (rule disjE[OF h\<sigma>_cases])
          assume "\<exists>w. \<sigma> = {w}"
          then obtain w where h\<sigma>_w: "\<sigma> = {w}" by (by100 blast)
          have h_w_x: "w = x" using hx\<sigma> h\<sigma>_w by (by100 blast)
          have h_x_B': "x \<in> ?B'" using hx by (by100 blast)
          show "\<sigma> \<subseteq> ?B'" using h\<sigma>_w h_w_x h_x_B' by (by100 simp)
        next
          assume "\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b"
          then obtain a b where hab_ne: "a \<noteq> b" and h\<sigma>_ab: "\<sigma> = closed_segment a b"
            by (by100 blast)
          (** Apply preimage_structure. **)
          obtain p q where hpq_le: "p \<le> q" and hp_01: "p \<in> {0..1}" and hq_01: "q \<in> {0..1}"
                        and hI_eq: "{s\<in>{0..1}. \<gamma> s \<in> \<sigma>} = {p..q}"
                        and h_\<gamma>_ends: "{\<gamma> p, \<gamma> q} = {a, b}"
            using geotop_arc_1simplex_preimage_structure
                  [OF harc hK''_1dim hK''_poly_pim h\<sigma>_K'' h\<sigma>_ab hab_ne]
            by (by100 blast)
          have ht_in_I: "t \<in> {p..q}"
          proof -
            have ht_I: "t \<in> {s\<in>{0..1}. \<gamma> s \<in> \<sigma>}"
              using ht_01 hxt hx\<sigma> by (by100 blast)
            show ?thesis using ht_I hI_eq by (by100 simp)
          qed
          have hp_le_t: "p \<le> t" using ht_in_I by (by100 simp)
          have ht_le_q: "t \<le> q" using ht_in_I by (by100 simp)
          (** Show [p, q] ⊆ [s_lo, s_hi]. **)
          have hpq_sub_lohi: "{p..q} \<subseteq> {s_lo..s_hi}"
          proof (rule ccontr)
            assume h_not: "\<not> {p..q} \<subseteq> {s_lo..s_hi}"
            (** Then either p < s_lo or q > s_hi. **)
            have h_dir: "p < s_lo \<or> q > s_hi"
            proof -
              have h_ex: "\<exists>u\<in>{p..q}. u \<notin> {s_lo..s_hi}"
                using h_not by (by100 blast)
              obtain u where hu_pq: "u \<in> {p..q}" and hu_out: "u \<notin> {s_lo..s_hi}"
                using h_ex by (by100 blast)
              have hu_01_real: "u < s_lo \<or> u > s_hi" using hu_out by (by100 auto)
              have hup: "p \<le> u" using hu_pq by (by100 simp)
              have huq: "u \<le> q" using hu_pq by (by100 simp)
              show ?thesis
              proof (rule disjE[OF hu_01_real])
                assume "u < s_lo"
                hence "p < s_lo" using hup by (by100 linarith)
                thus ?thesis by (by100 blast)
              next
                assume "u > s_hi"
                hence "q > s_hi" using huq by (by100 linarith)
                thus ?thesis by (by100 blast)
              qed
            qed
            (** Derive contradiction from each case. **)
            show False
            proof (rule disjE[OF h_dir])
              assume hp_lo: "p < s_lo"
              have h_p_le_slo: "p \<le> s_lo" using hp_lo by (by100 linarith)
              have h_slo_le_q: "s_lo \<le> q" using ht_lo ht_le_q by (by100 linarith)
              have hs_lo_pq: "s_lo \<in> {p..q}"
                using h_p_le_slo h_slo_le_q by (by100 simp)
              have hs_lo_in_I: "s_lo \<in> {s\<in>{0..1}. \<gamma> s \<in> \<sigma>}"
                using hs_lo_pq hI_eq by (by100 simp)
              have h\<gamma>s_lo_\<sigma>: "\<gamma> s_lo \<in> \<sigma>" using hs_lo_in_I by (by100 simp)
              have hX_endpoint: "?X = a \<or> ?X = b"
                by (rule geotop_1dim_vertex_in_1simplex_is_endpoint
                         [OF hK''_comp hX_K'' h\<sigma>_K'' h\<sigma>_ab hab_ne h\<gamma>s_lo_\<sigma>])
              (** ?X ∈ {γ p, γ q} = {a, b}. By injectivity, s_lo = p or s_lo = q. **)
              have hX_pq: "?X \<in> {\<gamma> p, \<gamma> q}" using hX_endpoint h_\<gamma>_ends by (by100 blast)
              have h_cont_\<gamma>: "continuous_on {0..1} \<gamma>"
                using harc unfolding arc_def path_def by (by100 blast)
              have h_inj_\<gamma>: "inj_on \<gamma> {0..1}"
                using harc unfolding arc_def by (by100 blast)
              have hs_lo_in_01: "s_lo \<in> {0..1}" by (rule hs_lo)
              have hs_lo_pq_disj: "s_lo = p \<or> s_lo = q"
              proof -
                have h_or: "\<gamma> s_lo = \<gamma> p \<or> \<gamma> s_lo = \<gamma> q" using hX_pq by (by100 blast)
                show ?thesis
                proof (rule disjE[OF h_or])
                  assume "\<gamma> s_lo = \<gamma> p"
                  hence "s_lo = p" using h_inj_\<gamma> hs_lo_in_01 hp_01
                    unfolding inj_on_def by (by100 blast)
                  thus ?thesis by (by100 blast)
                next
                  assume "\<gamma> s_lo = \<gamma> q"
                  hence "s_lo = q" using h_inj_\<gamma> hs_lo_in_01 hq_01
                    unfolding inj_on_def by (by100 blast)
                  thus ?thesis by (by100 blast)
                qed
              qed
              show False
              proof (rule disjE[OF hs_lo_pq_disj])
                assume hs_p: "s_lo = p"
                show False using hp_lo hs_p by (by100 linarith)
              next
                assume hs_q: "s_lo = q"
                have ht_le_lo: "t \<le> s_lo" using ht_le_q hs_q by (by100 simp)
                show False using ht_le_lo h_lo_lt_t by (by100 linarith)
              qed
            next
              assume hq_hi: "q > s_hi"
              have h_shi_le_q: "s_hi \<le> q" using hq_hi by (by100 linarith)
              have h_p_le_shi: "p \<le> s_hi" using hp_le_t ht_hi by (by100 linarith)
              have hs_hi_pq: "s_hi \<in> {p..q}"
                using h_shi_le_q h_p_le_shi by (by100 simp)
              have hs_hi_in_I: "s_hi \<in> {s\<in>{0..1}. \<gamma> s \<in> \<sigma>}"
                using hs_hi_pq hI_eq by (by100 simp)
              have h\<gamma>s_hi_\<sigma>: "\<gamma> s_hi \<in> \<sigma>" using hs_hi_in_I by (by100 simp)
              have hY_endpoint: "?Y = a \<or> ?Y = b"
                by (rule geotop_1dim_vertex_in_1simplex_is_endpoint
                         [OF hK''_comp hY_K'' h\<sigma>_K'' h\<sigma>_ab hab_ne h\<gamma>s_hi_\<sigma>])
              have hY_pq: "?Y \<in> {\<gamma> p, \<gamma> q}" using hY_endpoint h_\<gamma>_ends by (by100 blast)
              have h_inj_\<gamma>: "inj_on \<gamma> {0..1}"
                using harc unfolding arc_def by (by100 blast)
              have hs_hi_in_01: "s_hi \<in> {0..1}" by (rule hs_hi)
              have hs_hi_pq_disj: "s_hi = p \<or> s_hi = q"
              proof -
                have h_or: "\<gamma> s_hi = \<gamma> p \<or> \<gamma> s_hi = \<gamma> q" using hY_pq by (by100 blast)
                show ?thesis
                proof (rule disjE[OF h_or])
                  assume "\<gamma> s_hi = \<gamma> p"
                  hence "s_hi = p" using h_inj_\<gamma> hs_hi_in_01 hp_01
                    unfolding inj_on_def by (by100 blast)
                  thus ?thesis by (by100 blast)
                next
                  assume "\<gamma> s_hi = \<gamma> q"
                  hence "s_hi = q" using h_inj_\<gamma> hs_hi_in_01 hq_01
                    unfolding inj_on_def by (by100 blast)
                  thus ?thesis by (by100 blast)
                qed
              qed
              show False
              proof (rule disjE[OF hs_hi_pq_disj])
                assume hs_p: "s_hi = p"
                have ht_ge_hi: "s_hi \<le> t" using hp_le_t hs_p by (by100 simp)
                show False using ht_ge_hi h_t_lt_hi by (by100 linarith)
              next
                assume hs_q: "s_hi = q"
                show False using hq_hi hs_q by (by100 linarith)
              qed
            qed
          qed
          (** σ = γ([p, q]) ⊆ γ([s_lo, s_hi]) = ?B'. **)
          have h\<sigma>_eq_im: "\<sigma> = \<gamma> ` {p..q}"
          proof -
            have h\<sigma>_sub_pim: "\<sigma> \<subseteq> path_image \<gamma>"
              using h\<sigma>_K'' hK''_poly_pim unfolding geotop_polyhedron_def by (by100 blast)
            show ?thesis
            proof
              show "\<sigma> \<subseteq> \<gamma> ` {p..q}"
              proof
                fix y assume hy: "y \<in> \<sigma>"
                have h_y_pim: "y \<in> path_image \<gamma>" using hy h\<sigma>_sub_pim by (by100 blast)
                obtain s where hs_01: "s \<in> {0..1}" and hs_y: "y = \<gamma> s"
                  using h_y_pim unfolding path_image_def by (by100 blast)
                have hs_in_I: "s \<in> {s\<in>{0..1}. \<gamma> s \<in> \<sigma>}"
                  using hs_01 hs_y hy by (by100 simp)
                have hs_pq: "s \<in> {p..q}" using hs_in_I hI_eq by (by100 simp)
                show "y \<in> \<gamma> ` {p..q}" using hs_pq hs_y by (by100 blast)
              qed
              show "\<gamma> ` {p..q} \<subseteq> \<sigma>"
              proof
                fix y assume "y \<in> \<gamma> ` {p..q}"
                then obtain s where hs_pq: "s \<in> {p..q}" and hy: "y = \<gamma> s" by (by100 blast)
                have hs_in_I: "s \<in> {s\<in>{0..1}. \<gamma> s \<in> \<sigma>}"
                  using hs_pq hI_eq by (by100 simp)
                show "y \<in> \<sigma>" using hs_in_I hy by (by100 simp)
              qed
            qed
          qed
          have h\<sigma>_sub_\<gamma>lohi: "\<sigma> \<subseteq> \<gamma> ` {s_lo..s_hi}"
          proof -
            have h_im_mono: "\<gamma> ` {p..q} \<subseteq> \<gamma> ` {s_lo..s_hi}"
              using hpq_sub_lohi by (by100 blast)
            show ?thesis using h\<sigma>_eq_im h_im_mono by (by100 simp)
          qed
          show "\<sigma> \<subseteq> ?B'" using h\<sigma>_sub_\<gamma>lohi hB'_eq by (by100 simp)
        qed
        have h\<sigma>_K': "\<sigma> \<in> ?K'" using h\<sigma>_K'' h\<sigma>_sub_B' by (by100 simp)
        show ?thesis using hx\<sigma> h\<sigma>_K'
          unfolding geotop_polyhedron_def by (by100 blast)
      qed
    qed
  qed
  have hK'_poly: "geotop_polyhedron ?K' = ?B'"
    using hK'_sub_B' hB'_sub_K' by (by100 blast)
  show ?thesis using hK'_comp hK'_poly hK'_1dim by (by100 blast)
qed

(** PL Helper 1: a sub-arc of a broken line between any two of its points
    is again a broken line. Proof: the arc parametrisation of \<open>B\<close> is a
    homeomorphism from \<open>[0,1]\<close> onto \<open>B\<close>, so the sub-arc is the image of a
    sub-interval. Since \<open>B\<close>'s complex is at most 1-dimensional (arc has
    dim 1), the sub-arc is the polyhedron of the restriction of the complex
    to vertices between the two parameter values (after possible edge
    subdivision at \<open>X\<close>, \<open>Y\<close>). **)
lemma geotop_broken_line_subarc:
  fixes B :: "'a::euclidean_space set"
  assumes hB: "geotop_is_broken_line B"
  assumes hX: "X \<in> B" and hY: "Y \<in> B"
  shows "\<exists>B'. geotop_is_broken_line B' \<and> B' \<subseteq> B \<and> X \<in> B' \<and> Y \<in> B'
            \<and> (X = Y \<or> (\<exists>\<gamma>'. arc \<gamma>' \<and> path_image \<gamma>' = B'
                           \<and> pathstart \<gamma>' = X \<and> pathfinish \<gamma>' = Y))"
proof (cases "X = Y")
  case True
  have hsub: "B \<subseteq> B" by (by100 blast)
  show ?thesis using hB hsub hX hY True by (by100 blast)
next
  case False
  (** (1) Extract HOL arc parametrisation of B. **)
  have hB_arc: "geotop_is_arc B (subspace_topology UNIV geotop_euclidean_topology B)"
    using hB unfolding geotop_is_broken_line_def by (by100 blast)
  obtain \<gamma> where harc: "arc \<gamma>" and hpim: "path_image \<gamma> = B"
    using geotop_is_arc_imp_HOL_arc[OF hB_arc] by (by100 blast)
  (** (2) Find parameters s_X, s_Y with \<gamma>(s_X) = X, \<gamma>(s_Y) = Y. **)
  obtain s\<^sub>X where hs\<^sub>X: "s\<^sub>X \<in> {0::real..1}" and hX_eq: "\<gamma> s\<^sub>X = X"
    using hX hpim unfolding path_image_def by (by100 blast)
  obtain s\<^sub>Y where hs\<^sub>Y: "s\<^sub>Y \<in> {0::real..1}" and hY_eq: "\<gamma> s\<^sub>Y = Y"
    using hY hpim unfolding path_image_def by (by100 blast)
  have hsne: "s\<^sub>X \<noteq> s\<^sub>Y" using hX_eq hY_eq False by (by100 blast)
  (** (3) Define endpoints-preserving subpath: pathstart = X, pathfinish = Y. **)
  define \<gamma>' where "\<gamma>' = subpath s\<^sub>X s\<^sub>Y \<gamma>"
  define s_lo where "s_lo = min s\<^sub>X s\<^sub>Y"
  define s_hi where "s_hi = max s\<^sub>X s\<^sub>Y"
  have hs\<^sub>X_lb: "0 \<le> s\<^sub>X" using hs\<^sub>X by (by100 simp)
  have hs\<^sub>X_ub: "s\<^sub>X \<le> 1" using hs\<^sub>X by (by100 simp)
  have hs\<^sub>Y_lb: "0 \<le> s\<^sub>Y" using hs\<^sub>Y by (by100 simp)
  have hs\<^sub>Y_ub: "s\<^sub>Y \<le> 1" using hs\<^sub>Y by (by100 simp)
  have hs_lo_lb: "0 \<le> s_lo" using hs\<^sub>X_lb hs\<^sub>Y_lb unfolding s_lo_def by (by100 simp)
  have hs_lo_ub: "s_lo \<le> 1" using hs\<^sub>X_ub hs\<^sub>Y_ub unfolding s_lo_def by (by100 simp)
  have hs_hi_lb: "0 \<le> s_hi" using hs\<^sub>X_lb hs\<^sub>Y_lb unfolding s_hi_def by (by100 simp)
  have hs_hi_ub: "s_hi \<le> 1" using hs\<^sub>X_ub hs\<^sub>Y_ub unfolding s_hi_def by (by100 simp)
  have hs_lo_range: "s_lo \<in> {0..1}" using hs_lo_lb hs_lo_ub by (by100 simp)
  have hs_hi_range: "s_hi \<in> {0..1}" using hs_hi_lb hs_hi_ub by (by100 simp)
  have hs_lt: "s_lo < s_hi"
    using hsne unfolding s_lo_def s_hi_def by (by100 simp)
  (** (4) Extract sub-arc from s_lo to s_hi via arc_subpath_arc. **)
  have hs_lo_ne_hi: "s_lo \<noteq> s_hi" using hs_lt by (by100 simp)
  have hsub_arc: "arc (subpath s_lo s_hi \<gamma>)"
    by (rule arc_subpath_arc[OF harc hs_lo_range hs_hi_range hs_lo_ne_hi])
  (** (5) Image of the sub-arc is contained in B. **)
  have hsub_image: "path_image (subpath s_lo s_hi \<gamma>) \<subseteq> B"
    using hpim path_image_subpath_subset[of s_lo s_hi \<gamma>] hs_lo_range hs_hi_range
    by (by100 blast)
  let ?B' = "path_image (subpath s_lo s_hi \<gamma>)"
  (** (6) Both X and Y are in ?B'. path_image of subpath is \<gamma> ` closed_segment s_lo s_hi. **)
  have hpim_eq: "?B' = \<gamma> ` closed_segment s_lo s_hi"
    by (rule path_image_subpath_gen)
  have h_seg_eq: "closed_segment s_lo s_hi = {s_lo..s_hi}"
    using hs_lt unfolding closed_segment_eq_real_ivl by (by100 simp)
  have hs\<^sub>X_seg: "s\<^sub>X \<in> closed_segment s_lo s_hi"
  proof -
    have "s\<^sub>X \<in> {s_lo..s_hi}" unfolding s_lo_def s_hi_def by (by100 simp)
    thus ?thesis using h_seg_eq by (by100 simp)
  qed
  have hs\<^sub>Y_seg: "s\<^sub>Y \<in> closed_segment s_lo s_hi"
  proof -
    have "s\<^sub>Y \<in> {s_lo..s_hi}" unfolding s_lo_def s_hi_def by (by100 simp)
    thus ?thesis using h_seg_eq by (by100 simp)
  qed
  have hX_in_B': "X \<in> ?B'"
    using hpim_eq hs\<^sub>X_seg hX_eq by (by100 blast)
  have hY_in_B': "Y \<in> ?B'"
    using hpim_eq hs\<^sub>Y_seg hY_eq by (by100 blast)
  (** (7) ?B' is a geotop_is_arc via the HOL-arc bridge. **)
  have hB'_geotop_arc: "geotop_is_arc ?B' (subspace_topology UNIV geotop_euclidean_topology ?B')"
    by (rule geotop_HOL_arc_imp_geotop_is_arc[OF hsub_arc])
  (** (8) Polyhedral side: ?B' is the polyhedron of a sub-complex of B's
          witnessing complex (classical PL). Closed via geotop_subarc_polyhedron. **)
  have hB'_poly_im: "\<exists>K'. geotop_is_complex K' \<and> geotop_polyhedron K' = \<gamma> ` closed_segment s_lo s_hi
                       \<and> geotop_complex_is_1dim K'"
    by (rule geotop_subarc_polyhedron[OF hB harc hpim hs_lo_range hs_hi_range hs_lt])
  have hB'_poly: "\<exists>K'. geotop_is_complex K' \<and> geotop_polyhedron K' = ?B'
                     \<and> geotop_complex_is_1dim K'"
    using hB'_poly_im hpim_eq by (by100 simp)
  have hB'_broken: "geotop_is_broken_line ?B'"
    unfolding geotop_is_broken_line_def using hB'_poly hB'_geotop_arc by (by100 blast)
  (** (9) Construct the pathstart-X, pathfinish-Y arc parametrisation. **)
  have hs\<^sub>X_range_real: "s\<^sub>X \<in> {0..1}" using hs\<^sub>X_lb hs\<^sub>X_ub by (by100 simp)
  have hs\<^sub>Y_range_real: "s\<^sub>Y \<in> {0..1}" using hs\<^sub>Y_lb hs\<^sub>Y_ub by (by100 simp)
  have h\<gamma>'_arc: "arc \<gamma>'"
    unfolding \<gamma>'_def
    by (rule arc_subpath_arc[OF harc hs\<^sub>X_range_real hs\<^sub>Y_range_real hsne])
  have h\<gamma>'_pathstart: "pathstart \<gamma>' = X"
    unfolding \<gamma>'_def pathstart_def subpath_def using hX_eq by (by100 simp)
  have h\<gamma>'_pathfinish: "pathfinish \<gamma>' = Y"
    unfolding \<gamma>'_def pathfinish_def subpath_def using hY_eq by (by100 simp)
  have h\<gamma>'_image: "path_image \<gamma>' = ?B'"
  proof -
    have h1: "path_image \<gamma>' = \<gamma> ` closed_segment s\<^sub>X s\<^sub>Y"
      unfolding \<gamma>'_def by (rule path_image_subpath_gen)
    have h2: "?B' = \<gamma> ` closed_segment s_lo s_hi"
      by (rule path_image_subpath_gen)
    have h_seg_xy: "closed_segment s\<^sub>X s\<^sub>Y = closed_segment s_lo s_hi"
    proof -
      have heq_lh: "closed_segment s\<^sub>X s\<^sub>Y = {min s\<^sub>X s\<^sub>Y..max s\<^sub>X s\<^sub>Y}"
        unfolding closed_segment_eq_real_ivl by (by100 simp)
      have heq_rh: "closed_segment s_lo s_hi = {s_lo..s_hi}"
        using hs_lt unfolding closed_segment_eq_real_ivl by (by100 simp)
      have heq_ivl: "{min s\<^sub>X s\<^sub>Y..max s\<^sub>X s\<^sub>Y} = {s_lo..s_hi}"
        unfolding s_lo_def s_hi_def by (by100 simp)
      show ?thesis using heq_lh heq_rh heq_ivl by (by100 simp)
    qed
    show ?thesis using h1 h2 h_seg_xy by (by100 simp)
  qed
  have hB'_arc_endpoints:
    "\<exists>\<gamma>'. arc \<gamma>' \<and> path_image \<gamma>' = ?B' \<and> pathstart \<gamma>' = X \<and> pathfinish \<gamma>' = Y"
    using h\<gamma>'_arc h\<gamma>'_image h\<gamma>'_pathstart h\<gamma>'_pathfinish by (by100 blast)
  show ?thesis using hB'_broken hsub_image hX_in_B' hY_in_B' hB'_arc_endpoints False
    by (by100 blast)
qed

(** PL Helper 2: two broken lines sharing exactly one point, each having that
    point as an endpoint of its arc-parametrisation, combine into a broken line.
    The endpoint hypothesis is essential: if \<open>R\<close> were interior to one arc, the
    union would have a branch point at \<open>R\<close> and so fail to be an arc (T-shape).

    Proof via HOL's \<open>arc_join\<close>: both underlying HOL arcs glue into a HOL arc
    whose image is the full set union. The polyhedral side uses the union of
    their witnessing 1-complexes. **)
lemma geotop_broken_lines_glue_disjoint_endpoints:
  fixes B\<^sub>1 B\<^sub>2 :: "'a::euclidean_space set"
  assumes hB\<^sub>1: "geotop_is_broken_line B\<^sub>1" and hB\<^sub>2: "geotop_is_broken_line B\<^sub>2"
  assumes hR_end_1: "\<exists>\<gamma>\<^sub>1. arc \<gamma>\<^sub>1 \<and> path_image \<gamma>\<^sub>1 = B\<^sub>1 \<and> pathfinish \<gamma>\<^sub>1 = R"
  assumes hR_end_2: "\<exists>\<gamma>\<^sub>2. arc \<gamma>\<^sub>2 \<and> path_image \<gamma>\<^sub>2 = B\<^sub>2 \<and> pathstart \<gamma>\<^sub>2 = R"
  assumes hdisj: "B\<^sub>1 \<inter> B\<^sub>2 = {R}"
  shows "geotop_is_broken_line (B\<^sub>1 \<union> B\<^sub>2)"
proof -
  (** (1) Extract HOL arcs with endpoint R. **)
  obtain \<gamma>\<^sub>1 where harc\<^sub>1: "arc \<gamma>\<^sub>1" and hpim\<^sub>1: "path_image \<gamma>\<^sub>1 = B\<^sub>1"
                and hfin\<^sub>1: "pathfinish \<gamma>\<^sub>1 = R"
    using hR_end_1 by (by100 blast)
  obtain \<gamma>\<^sub>2 where harc\<^sub>2: "arc \<gamma>\<^sub>2" and hpim\<^sub>2: "path_image \<gamma>\<^sub>2 = B\<^sub>2"
                and hstart\<^sub>2: "pathstart \<gamma>\<^sub>2 = R"
    using hR_end_2 by (by100 blast)
  (** (2) Apply HOL's arc_join: arcs meeting only at shared endpoint glue. **)
  have h_fin_start: "pathfinish \<gamma>\<^sub>1 = pathstart \<gamma>\<^sub>2"
    using hfin\<^sub>1 hstart\<^sub>2 by (by100 simp)
  have h_int_sub: "path_image \<gamma>\<^sub>1 \<inter> path_image \<gamma>\<^sub>2 \<subseteq> {pathstart \<gamma>\<^sub>2}"
    using hpim\<^sub>1 hpim\<^sub>2 hdisj hstart\<^sub>2 by (by100 blast)
  have h\<gamma>_join: "arc (\<gamma>\<^sub>1 +++ \<gamma>\<^sub>2)"
    by (rule arc_join[OF harc\<^sub>1 harc\<^sub>2 h_fin_start h_int_sub])
  (** (3) The joined arc's path-image is B_1 \<union> B_2. **)
  have h_join_pim_raw: "path_image (\<gamma>\<^sub>1 +++ \<gamma>\<^sub>2) = path_image \<gamma>\<^sub>1 \<union> path_image \<gamma>\<^sub>2"
    by (rule path_image_join[OF h_fin_start])
  have h_join_pim: "path_image (\<gamma>\<^sub>1 +++ \<gamma>\<^sub>2) = B\<^sub>1 \<union> B\<^sub>2"
    using h_join_pim_raw hpim\<^sub>1 hpim\<^sub>2 by (by100 simp)
  (** (4) Apply the HOL-arc \<rightarrow> geotop_is_arc bridge. **)
  have h_geotop_arc: "geotop_is_arc (B\<^sub>1 \<union> B\<^sub>2)
                       (subspace_topology UNIV geotop_euclidean_topology (B\<^sub>1 \<union> B\<^sub>2))"
    using h_join_pim geotop_HOL_arc_imp_geotop_is_arc[OF h\<gamma>_join] by (by100 simp)
  (** (5) Polyhedral side. Get K_1 with R as vertex; similarly K_2. **)
  have hR_B\<^sub>1: "R \<in> B\<^sub>1" using hdisj by (by100 blast)
  have hR_B\<^sub>2: "R \<in> B\<^sub>2" using hdisj by (by100 blast)
  obtain K\<^sub>1 where hK\<^sub>1_comp: "geotop_is_complex K\<^sub>1"
              and hK\<^sub>1_1dim: "geotop_complex_is_1dim K\<^sub>1"
              and hK\<^sub>1_poly: "geotop_polyhedron K\<^sub>1 = B\<^sub>1"
              and hR_K\<^sub>1: "{R} \<in> K\<^sub>1"
              and hK\<^sub>1_fin: "finite K\<^sub>1"
    using geotop_broken_line_vertex_at[OF hB\<^sub>1 hR_B\<^sub>1] by (by100 blast)
  obtain K\<^sub>2 where hK\<^sub>2_comp: "geotop_is_complex K\<^sub>2"
              and hK\<^sub>2_1dim: "geotop_complex_is_1dim K\<^sub>2"
              and hK\<^sub>2_poly: "geotop_polyhedron K\<^sub>2 = B\<^sub>2"
              and hR_K\<^sub>2: "{R} \<in> K\<^sub>2"
              and hK\<^sub>2_fin: "finite K\<^sub>2"
    using geotop_broken_line_vertex_at[OF hB\<^sub>2 hR_B\<^sub>2] by (by100 blast)
  define K where "K = K\<^sub>1 \<union> K\<^sub>2"
  (** K is a complex: K.0, K.1, K.2, K.3 checked pairwise. **)
  have hK_simplexes: "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
    unfolding K_def
    using conjunct1[OF hK\<^sub>1_comp[unfolded geotop_is_complex_def]]
          conjunct1[OF hK\<^sub>2_comp[unfolded geotop_is_complex_def]] by (by100 blast)
  have hK_1dim: "geotop_complex_is_1dim K"
    unfolding K_def geotop_complex_is_1dim_def
    using hK\<^sub>1_1dim hK\<^sub>2_1dim unfolding geotop_complex_is_1dim_def by (by100 blast)
  have hK_poly: "geotop_polyhedron K = B\<^sub>1 \<union> B\<^sub>2"
  proof -
    have h1: "geotop_polyhedron K = geotop_polyhedron K\<^sub>1 \<union> geotop_polyhedron K\<^sub>2"
      unfolding K_def geotop_polyhedron_def by (by100 auto)
    show ?thesis using h1 hK\<^sub>1_poly hK\<^sub>2_poly by (by100 simp)
  qed
  (** K.1: face closure. **)
  have hK\<^sub>1_faces: "\<forall>\<sigma>\<in>K\<^sub>1. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K\<^sub>1"
    using conjunct1[OF conjunct2[OF hK\<^sub>1_comp[unfolded geotop_is_complex_def]]]
    by (by100 blast)
  have hK\<^sub>2_faces: "\<forall>\<sigma>\<in>K\<^sub>2. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K\<^sub>2"
    using conjunct1[OF conjunct2[OF hK\<^sub>2_comp[unfolded geotop_is_complex_def]]]
    by (by100 blast)
  have hK_faces: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    unfolding K_def using hK\<^sub>1_faces hK\<^sub>2_faces by (by100 blast)
  (** K.2: intersection is face of both. Split by K_1/K_2 membership. **)
  have hK\<^sub>1_inter: "\<forall>\<sigma>\<in>K\<^sub>1. \<forall>\<tau>\<in>K\<^sub>1. \<sigma> \<inter> \<tau> \<noteq> {}
                      \<longrightarrow> geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    using conjunct1[OF conjunct2[OF conjunct2[OF hK\<^sub>1_comp[unfolded geotop_is_complex_def]]]]
    by (by100 blast)
  have hK\<^sub>2_inter: "\<forall>\<sigma>\<in>K\<^sub>2. \<forall>\<tau>\<in>K\<^sub>2. \<sigma> \<inter> \<tau> \<noteq> {}
                      \<longrightarrow> geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    using conjunct1[OF conjunct2[OF conjunct2[OF hK\<^sub>2_comp[unfolded geotop_is_complex_def]]]]
    by (by100 blast)
  (** Cross case: \<sigma> \<in> K_1, \<tau> \<in> K_2. Intersection lies in |K_1| \<inter> |K_2| = B_1 \<inter> B_2 = {R}. **)
  have h_cross_inter: "\<And>\<sigma> \<tau>. \<sigma> \<in> K\<^sub>1 \<Longrightarrow> \<tau> \<in> K\<^sub>2 \<Longrightarrow> \<sigma> \<inter> \<tau> \<subseteq> {R}"
  proof -
    fix \<sigma> \<tau> assume h\<sigma>: "\<sigma> \<in> K\<^sub>1" and h\<tau>: "\<tau> \<in> K\<^sub>2"
    have h\<sigma>_sub: "\<sigma> \<subseteq> geotop_polyhedron K\<^sub>1"
      unfolding geotop_polyhedron_def using h\<sigma> by (by100 blast)
    have h\<tau>_sub: "\<tau> \<subseteq> geotop_polyhedron K\<^sub>2"
      unfolding geotop_polyhedron_def using h\<tau> by (by100 blast)
    have h_ss: "\<sigma> \<inter> \<tau> \<subseteq> B\<^sub>1 \<inter> B\<^sub>2"
      using h\<sigma>_sub h\<tau>_sub hK\<^sub>1_poly hK\<^sub>2_poly by (by100 blast)
    show "\<sigma> \<inter> \<tau> \<subseteq> {R}" using h_ss hdisj by (by100 simp)
  qed
  have h_cross_ne_R: "\<And>\<sigma> \<tau>. \<sigma> \<in> K\<^sub>1 \<Longrightarrow> \<tau> \<in> K\<^sub>2 \<Longrightarrow> \<sigma> \<inter> \<tau> \<noteq> {} \<Longrightarrow> \<sigma> \<inter> \<tau> = {R}"
  proof -
    fix \<sigma> \<tau> assume h\<sigma>: "\<sigma> \<in> K\<^sub>1" and h\<tau>: "\<tau> \<in> K\<^sub>2" and hne: "\<sigma> \<inter> \<tau> \<noteq> {}"
    have h_sub: "\<sigma> \<inter> \<tau> \<subseteq> {R}" using h_cross_inter h\<sigma> h\<tau> by (by100 blast)
    show "\<sigma> \<inter> \<tau> = {R}" using h_sub hne by (by100 blast)
  qed
  (** When R ∈ σ (σ ∈ K_1 containing R), {R} is a face of σ because {R} ∈ K_1 and K.2. **)
  have h_R_face_of: "\<And>\<sigma>. \<sigma> \<in> K\<^sub>1 \<Longrightarrow> R \<in> \<sigma> \<Longrightarrow> geotop_is_face {R} \<sigma>"
  proof -
    fix \<sigma> assume h\<sigma>: "\<sigma> \<in> K\<^sub>1" and hR\<sigma>: "R \<in> \<sigma>"
    have h_int: "\<sigma> \<inter> {R} = {R}" using hR\<sigma> by (by100 blast)
    have h_ne: "\<sigma> \<inter> {R} \<noteq> {}" using h_int by (by100 simp)
    have h_face: "geotop_is_face (\<sigma> \<inter> {R}) \<sigma>"
      using hK\<^sub>1_inter h\<sigma> hR_K\<^sub>1 h_ne by (by100 blast)
    show "geotop_is_face {R} \<sigma>" using h_face h_int by (by100 simp)
  qed
  have h_R_face_of_K\<^sub>2: "\<And>\<tau>. \<tau> \<in> K\<^sub>2 \<Longrightarrow> R \<in> \<tau> \<Longrightarrow> geotop_is_face {R} \<tau>"
  proof -
    fix \<tau> assume h\<tau>: "\<tau> \<in> K\<^sub>2" and hR\<tau>: "R \<in> \<tau>"
    have h_int: "\<tau> \<inter> {R} = {R}" using hR\<tau> by (by100 blast)
    have h_ne: "\<tau> \<inter> {R} \<noteq> {}" using h_int by (by100 simp)
    have h_face: "geotop_is_face (\<tau> \<inter> {R}) \<tau>"
      using hK\<^sub>2_inter h\<tau> hR_K\<^sub>2 h_ne by (by100 blast)
    show "geotop_is_face {R} \<tau>" using h_face h_int by (by100 simp)
  qed
  have hK_inter: "\<forall>\<sigma>\<in>K. \<forall>\<tau>\<in>K. \<sigma> \<inter> \<tau> \<noteq> {}
                    \<longrightarrow> geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
  proof (intro ballI impI)
    fix \<sigma> \<tau> assume h\<sigma>K: "\<sigma> \<in> K" and h\<tau>K: "\<tau> \<in> K" and hne: "\<sigma> \<inter> \<tau> \<noteq> {}"
    have h\<sigma>_disj: "\<sigma> \<in> K\<^sub>1 \<or> \<sigma> \<in> K\<^sub>2" using h\<sigma>K unfolding K_def by (by100 blast)
    have h\<tau>_disj: "\<tau> \<in> K\<^sub>1 \<or> \<tau> \<in> K\<^sub>2" using h\<tau>K unfolding K_def by (by100 blast)
    show "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    proof (cases "\<sigma> \<in> K\<^sub>1 \<and> \<tau> \<in> K\<^sub>1")
      case True
      thus ?thesis using hK\<^sub>1_inter hne by (by100 blast)
    next
      case False
      show ?thesis
      proof (cases "\<sigma> \<in> K\<^sub>2 \<and> \<tau> \<in> K\<^sub>2")
        case True
        thus ?thesis using hK\<^sub>2_inter hne by (by100 blast)
      next
        case False
        (** Cross: σ ∈ K_1, τ ∈ K_2, or vice versa. **)
        have hcross: "(\<sigma> \<in> K\<^sub>1 \<and> \<tau> \<in> K\<^sub>2) \<or> (\<sigma> \<in> K\<^sub>2 \<and> \<tau> \<in> K\<^sub>1)"
          using h\<sigma>_disj h\<tau>_disj \<open>\<not> (\<sigma> \<in> K\<^sub>1 \<and> \<tau> \<in> K\<^sub>1)\<close> False by (by100 blast)
        thus ?thesis
        proof
          assume h12: "\<sigma> \<in> K\<^sub>1 \<and> \<tau> \<in> K\<^sub>2"
          have h\<sigma>K\<^sub>1: "\<sigma> \<in> K\<^sub>1" and h\<tau>K\<^sub>2: "\<tau> \<in> K\<^sub>2" using h12 by (by100 simp)+
          have h_int_R: "\<sigma> \<inter> \<tau> = {R}" using h_cross_ne_R h\<sigma>K\<^sub>1 h\<tau>K\<^sub>2 hne by (by100 blast)
          have hR\<sigma>: "R \<in> \<sigma>" using h_int_R by (by100 blast)
          have hR\<tau>: "R \<in> \<tau>" using h_int_R by (by100 blast)
          have hf\<sigma>: "geotop_is_face {R} \<sigma>" using h_R_face_of h\<sigma>K\<^sub>1 hR\<sigma> by (by100 blast)
          have hf\<tau>: "geotop_is_face {R} \<tau>" using h_R_face_of_K\<^sub>2 h\<tau>K\<^sub>2 hR\<tau> by (by100 blast)
          show ?thesis using h_int_R hf\<sigma> hf\<tau> by (by100 simp)
        next
          assume h21: "\<sigma> \<in> K\<^sub>2 \<and> \<tau> \<in> K\<^sub>1"
          have h\<sigma>K\<^sub>2: "\<sigma> \<in> K\<^sub>2" and h\<tau>K\<^sub>1: "\<tau> \<in> K\<^sub>1" using h21 by (by100 simp)+
          have h_int_R: "\<sigma> \<inter> \<tau> = {R}"
          proof -
            have h_sym: "\<tau> \<inter> \<sigma> = {R}"
              using h_cross_ne_R h\<tau>K\<^sub>1 h\<sigma>K\<^sub>2 hne by (by100 blast)
            thus ?thesis by (by100 blast)
          qed
          have hR\<sigma>: "R \<in> \<sigma>" using h_int_R by (by100 blast)
          have hR\<tau>: "R \<in> \<tau>" using h_int_R by (by100 blast)
          have hf\<sigma>: "geotop_is_face {R} \<sigma>" using h_R_face_of_K\<^sub>2 h\<sigma>K\<^sub>2 hR\<sigma> by (by100 blast)
          have hf\<tau>: "geotop_is_face {R} \<tau>" using h_R_face_of h\<tau>K\<^sub>1 hR\<tau> by (by100 blast)
          show ?thesis using h_int_R hf\<sigma> hf\<tau> by (by100 simp)
        qed
      qed
    qed
  qed
  (** K.3: local finiteness. K is finite (K_1 ∪ K_2 with both finite),
      so take U = UNIV. **)
  have hK_fin: "finite K" unfolding K_def using hK\<^sub>1_fin hK\<^sub>2_fin by (by100 simp)
  have hK_nbhd: "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
  proof
    fix \<sigma> assume h\<sigma>K: "\<sigma> \<in> K"
    have hopen: "open (UNIV::'a set)" by (by100 simp)
    have hsub: "\<sigma> \<subseteq> UNIV" by (by100 simp)
    have hfin: "finite {\<tau>\<in>K. \<tau> \<inter> UNIV \<noteq> {}}" using hK_fin by (by100 simp)
    show "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using hopen hsub hfin by (by100 blast)
  qed
  (** Assemble K as a complex. **)
  have hK_complex: "geotop_is_complex K"
    unfolding geotop_is_complex_def
    using hK_simplexes hK_faces hK_inter hK_nbhd by (by100 blast)
  have h_polyhedron: "\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = B\<^sub>1 \<union> B\<^sub>2
                          \<and> geotop_complex_is_1dim K"
    using hK_complex hK_poly hK_1dim by (by100 blast)
  show ?thesis
    unfolding geotop_is_broken_line_def
    using h_polyhedron h_geotop_arc by (by100 blast)
qed

(** PL-arc-reduction: given two broken lines \<open>B\<^sub>1, B\<^sub>2\<close> sharing a point and two
    further points \<open>P \<in> B\<^sub>1\<close>, \<open>Q \<in> B\<^sub>2\<close>, there is a broken-line sub-arc of
    \<open>B\<^sub>1 \<union> B\<^sub>2\<close> from \<open>P\<close> to \<open>Q\<close>.

    This is the classical Hausdorff-Moore arc-reduction theorem, specialised to
    the PL category. Proof sketch (Moise early.tex \<S>3):
      (a) parametrise \<open>B\<^sub>1\<close> as an arc \<open>\<alpha> : [0,1] \<to> B\<^sub>1\<close> with \<open>\<alpha>(0) = P\<close>,
          extract \<open>t\<^sub>0\<close> with \<open>\<alpha>(t\<^sub>0) = Q\<^sub>0\<close>, restrict to sub-arc \<open>\<alpha>' : [0, t\<^sub>0]\<close>;
      (b) similarly \<open>\<beta>' : [0, s\<^sub>0]\<close> in \<open>B\<^sub>2\<close> from \<open>Q\<^sub>0\<close> to \<open>Q\<close>;
      (c) concatenation \<open>c = \<alpha>' \<cdot> \<beta>'\<close> is PL, continuous, possibly self-intersecting;
      (d) Hausdorff-Moore: any such path contains a sub-arc from its endpoints,
          and in the PL category this sub-arc is itself a broken line.
    Deferred as a single classical fact. **)

(** Top-level first-intersection helper. Given a HOL arc \<gamma> on [0,1] mapping
    into an ambient space, and a closed target set T with \<gamma>(1) \<in> T, extract
    the smallest parameter sstar with \<gamma>(sstar) \<in> T. **)
lemma geotop_arc_first_intersection:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  assumes harc: "arc \<gamma>"
  assumes hT_closed: "closed T"
  assumes hfin_in_T: "\<gamma> 1 \<in> T"
  obtains sstar where "sstar \<in> {0..1}" and "\<gamma> sstar \<in> T"
                 and "\<forall>s\<in>{0..<sstar}. \<gamma> s \<notin> T"
proof -
  have h\<gamma>_cont: "continuous_on {0..1} \<gamma>"
    using harc unfolding arc_def path_def by (by100 blast)
  define S where "S = \<gamma> -` T \<inter> {0..1::real}"
  have hS_sub: "S \<subseteq> {0..1}" unfolding S_def by (by100 blast)
  have h1_in: "(1::real) \<in> S" unfolding S_def using hfin_in_T by (by100 simp)
  have hS_ne: "S \<noteq> {}" using h1_in by (by100 blast)
  have h_unit_closed: "closed ({0..1}::real set)" by (by100 simp)
  have h_char_iff:
    "continuous_on {0..1} \<gamma> \<longleftrightarrow> (\<forall>B. closed B \<longrightarrow> closed (\<gamma> -` B \<inter> {0..1}))"
    by (rule continuous_on_closed_vimage[OF h_unit_closed])
  have h_pre_closed: "closed (\<gamma> -` T \<inter> {0..1})"
    using h_char_iff h\<gamma>_cont hT_closed by (by100 blast)
  have hS_closed: "closed S" unfolding S_def using h_pre_closed by (by100 simp)
  have hS_bdd: "bounded S" unfolding S_def
    using bounded_closed_interval bounded_subset Int_lower2 by (by100 blast)
  have hS_bdd_below: "bdd_below S" by (rule bounded_imp_bdd_below[OF hS_bdd])
  define sstar where "sstar = Inf S"
  have hsstar_in_S: "sstar \<in> S"
    unfolding sstar_def by (rule closed_contains_Inf[OF hS_ne hS_bdd_below hS_closed])
  have hsstar_in_01: "sstar \<in> {0..1}" using hsstar_in_S hS_sub by (by100 blast)
  have hsstar_T: "\<gamma> sstar \<in> T" using hsstar_in_S unfolding S_def by (by100 blast)
  have hsstar_min: "\<forall>s\<in>{0..<sstar}. \<gamma> s \<notin> T"
  proof
    fix s assume hs: "s \<in> {0..<sstar}"
    have hs_lo: "0 \<le> s" using hs by (by100 simp)
    have hs_lt: "s < sstar" using hs by (by100 simp)
    have hsstar_le: "sstar \<le> 1" using hsstar_in_01 by (by100 simp)
    have hs_up: "s \<le> 1" using hs_lt hsstar_le by (by100 simp)
    have hs_in_01: "s \<in> {0..1}" using hs_lo hs_up by (by100 simp)
    have hs_notin_S: "s \<notin> S"
    proof
      assume hs_in_S: "s \<in> S"
      have "sstar \<le> s" unfolding sstar_def
        by (rule cInf_lower[OF hs_in_S hS_bdd_below])
      thus False using hs_lt by (by100 simp)
    qed
    show "\<gamma> s \<notin> T" using hs_notin_S hs_in_01 unfolding S_def by (by100 blast)
  qed
  show thesis using hsstar_in_01 hsstar_T hsstar_min that by (by100 blast)
qed

lemma geotop_broken_line_arc_reduction:
  fixes B\<^sub>1 B\<^sub>2 :: "'a::euclidean_space set"
  assumes hB\<^sub>1: "geotop_is_broken_line B\<^sub>1" and hB\<^sub>2: "geotop_is_broken_line B\<^sub>2"
  assumes hP: "P \<in> B\<^sub>1" and hQ\<^sub>0_1: "Q\<^sub>0 \<in> B\<^sub>1" and hQ\<^sub>0_2: "Q\<^sub>0 \<in> B\<^sub>2" and hQ: "Q \<in> B\<^sub>2"
  shows "\<exists>B. geotop_is_broken_line B \<and> B \<subseteq> B\<^sub>1 \<union> B\<^sub>2 \<and> P \<in> B \<and> Q \<in> B"
proof -
  (** Cheap cases: if \<open>P \<in> B\<^sub>2\<close>, then \<open>B = B\<^sub>2\<close> already contains both \<open>P\<close>
      and \<open>Q\<close>, is itself a broken line, and sits in \<open>B\<^sub>1 \<union> B\<^sub>2\<close>. Symmetrically
      if \<open>Q \<in> B\<^sub>1\<close>, take \<open>B = B\<^sub>1\<close>. Only the genuinely cross-arc case
      (\<open>P \<notin> B\<^sub>2 \<and> Q \<notin> B\<^sub>1\<close>) needs Hausdorff-Moore arc reduction. **)
  consider (PinB\<^sub>2) "P \<in> B\<^sub>2" | (QinB\<^sub>1) "Q \<in> B\<^sub>1"
         | (hard) "P \<notin> B\<^sub>2" "Q \<notin> B\<^sub>1" by (by100 blast)
  then show ?thesis
  proof cases
    case PinB\<^sub>2
    have hsub: "B\<^sub>2 \<subseteq> B\<^sub>1 \<union> B\<^sub>2" by (by100 blast)
    show ?thesis using hB\<^sub>2 hsub PinB\<^sub>2 hQ by (by100 blast)
  next
    case QinB\<^sub>1
    have hsub: "B\<^sub>1 \<subseteq> B\<^sub>1 \<union> B\<^sub>2" by (by100 blast)
    show ?thesis using hB\<^sub>1 hsub hP QinB\<^sub>1 by (by100 blast)
  next
    case hard
    (** Cross-arc case (P \<notin> B\<^sub>2 \<and> Q \<notin> B\<^sub>1). Proof via the two PL helpers:
        (1) Take sub-arc \<open>B\<^sub>1'\<close> of \<open>B\<^sub>1\<close> from \<open>P\<close> to \<open>Q\<^sub>0\<close> (broken_line_subarc).
        (2) Take sub-arc \<open>B\<^sub>2'\<close> of \<open>B\<^sub>2\<close> from \<open>Q\<^sub>0\<close> to \<open>Q\<close> (broken_line_subarc).
        (3) Inductive argument on the intersection \<open>B\<^sub>1' \<cap> B\<^sub>2'\<close>:
              - If \<open>{Q\<^sub>0}\<close>: glue via broken_lines_glue_disjoint_endpoints.
              - Otherwise: take first intersection along the arc parametrisation
                of \<open>B\<^sub>1'\<close>, recurse.
        A fully precise proof of (3) is deferred as one classical sorry; the
        helpers reduce the content to a compact-meet-arc-endpoint argument. **)
    (** From "hard": P \<notin> B_2 \<supseteq> B_2' so P \<noteq> Q_0; similarly Q \<noteq> Q_0. **)
    have hP_neQ\<^sub>0: "P \<noteq> Q\<^sub>0" using hard hQ\<^sub>0_2 by (by100 blast)
    have hQ_neQ\<^sub>0: "Q \<noteq> Q\<^sub>0" using hard hQ\<^sub>0_1 by (by100 blast)
    obtain B\<^sub>1' where hB\<^sub>1': "geotop_is_broken_line B\<^sub>1'" and hB\<^sub>1'_sub: "B\<^sub>1' \<subseteq> B\<^sub>1"
                  and hPB\<^sub>1': "P \<in> B\<^sub>1'" and hQ\<^sub>0B\<^sub>1': "Q\<^sub>0 \<in> B\<^sub>1'"
                  and hB\<^sub>1'_arc_data:
                     "P = Q\<^sub>0 \<or> (\<exists>\<gamma>'. arc \<gamma>' \<and> path_image \<gamma>' = B\<^sub>1'
                               \<and> pathstart \<gamma>' = P \<and> pathfinish \<gamma>' = Q\<^sub>0)"
      using geotop_broken_line_subarc[OF hB\<^sub>1 hP hQ\<^sub>0_1] by (by100 blast)
    obtain B\<^sub>2' where hB\<^sub>2': "geotop_is_broken_line B\<^sub>2'" and hB\<^sub>2'_sub: "B\<^sub>2' \<subseteq> B\<^sub>2"
                  and hQ\<^sub>0B\<^sub>2': "Q\<^sub>0 \<in> B\<^sub>2'" and hQB\<^sub>2': "Q \<in> B\<^sub>2'"
                  and hB\<^sub>2'_arc_data:
                     "Q\<^sub>0 = Q \<or> (\<exists>\<gamma>'. arc \<gamma>' \<and> path_image \<gamma>' = B\<^sub>2'
                               \<and> pathstart \<gamma>' = Q\<^sub>0 \<and> pathfinish \<gamma>' = Q)"
      using geotop_broken_line_subarc[OF hB\<^sub>2 hQ\<^sub>0_2 hQ] by (by100 blast)
    have hB\<^sub>1'_arc: "\<exists>\<gamma>'. arc \<gamma>' \<and> path_image \<gamma>' = B\<^sub>1' \<and> pathstart \<gamma>' = P \<and> pathfinish \<gamma>' = Q\<^sub>0"
      using hB\<^sub>1'_arc_data hP_neQ\<^sub>0 by (by100 blast)
    have hB\<^sub>2'_arc: "\<exists>\<gamma>'. arc \<gamma>' \<and> path_image \<gamma>' = B\<^sub>2' \<and> pathstart \<gamma>' = Q\<^sub>0 \<and> pathfinish \<gamma>' = Q"
      using hB\<^sub>2'_arc_data hQ_neQ\<^sub>0 by (by100 blast)
    (** Disjoint sub-case: B_1' ∩ B_2' = {Q_0}. Glue via glue_disjoint_endpoints. **)
    show ?thesis
    proof (cases "B\<^sub>1' \<inter> B\<^sub>2' = {Q\<^sub>0}")
      case True
      have hR_end_1: "\<exists>\<gamma>. arc \<gamma> \<and> path_image \<gamma> = B\<^sub>1' \<and> pathfinish \<gamma> = Q\<^sub>0"
        using hB\<^sub>1'_arc by (by100 blast)
      have hR_end_2: "\<exists>\<gamma>. arc \<gamma> \<and> path_image \<gamma> = B\<^sub>2' \<and> pathstart \<gamma> = Q\<^sub>0"
        using hB\<^sub>2'_arc by (by100 blast)
      have h_glued: "geotop_is_broken_line (B\<^sub>1' \<union> B\<^sub>2')"
        by (rule geotop_broken_lines_glue_disjoint_endpoints[OF hB\<^sub>1' hB\<^sub>2' hR_end_1 hR_end_2 True])
      have h_sub: "B\<^sub>1' \<union> B\<^sub>2' \<subseteq> B\<^sub>1 \<union> B\<^sub>2" using hB\<^sub>1'_sub hB\<^sub>2'_sub by (by100 blast)
      have h_P_in: "P \<in> B\<^sub>1' \<union> B\<^sub>2'" using hPB\<^sub>1' by (by100 blast)
      have h_Q_in: "Q \<in> B\<^sub>1' \<union> B\<^sub>2'" using hQB\<^sub>2' by (by100 blast)
      show ?thesis using h_glued h_sub h_P_in h_Q_in by (by100 blast)
    next
      case False
      (** Overlap case: closed via first-intersection + subarc_polyhedron + glue. **)
      obtain \<gamma>\<^sub>1 where h_arc_1: "arc \<gamma>\<^sub>1" and h_pim_1: "path_image \<gamma>\<^sub>1 = B\<^sub>1'"
                   and h_ps_1: "pathstart \<gamma>\<^sub>1 = P" and h_pf_1: "pathfinish \<gamma>\<^sub>1 = Q\<^sub>0"
        using hB\<^sub>1'_arc by (by100 blast)
      obtain \<gamma>\<^sub>2 where h_arc_2: "arc \<gamma>\<^sub>2" and h_pim_2: "path_image \<gamma>\<^sub>2 = B\<^sub>2'"
                   and h_ps_2: "pathstart \<gamma>\<^sub>2 = Q\<^sub>0" and h_pf_2: "pathfinish \<gamma>\<^sub>2 = Q"
        using hB\<^sub>2'_arc by (by100 blast)
      have h_B\<^sub>2'_closed: "closed B\<^sub>2'" by (rule geotop_broken_line_closed[OF hB\<^sub>2'])
      have h_\<gamma>\<^sub>1_1_Q\<^sub>0: "\<gamma>\<^sub>1 1 = Q\<^sub>0"
        using h_pf_1 unfolding pathfinish_def by (by100 simp)
      have h_\<gamma>\<^sub>1_0_P: "\<gamma>\<^sub>1 0 = P"
        using h_ps_1 unfolding pathstart_def by (by100 simp)
      have h_fin_in: "\<gamma>\<^sub>1 1 \<in> B\<^sub>2'" using h_\<gamma>\<^sub>1_1_Q\<^sub>0 hQ\<^sub>0B\<^sub>2' by (by100 simp)
      obtain sstar where hsstar_01: "sstar \<in> {0..1}" and hsstar_T: "\<gamma>\<^sub>1 sstar \<in> B\<^sub>2'"
                      and hsstar_min: "\<forall>s\<in>{0..<sstar}. \<gamma>\<^sub>1 s \<notin> B\<^sub>2'"
        using geotop_arc_first_intersection[OF h_arc_1 h_B\<^sub>2'_closed h_fin_in] by (by100 blast)
      let ?R = "\<gamma>\<^sub>1 sstar"
      have hP_notin_B\<^sub>2: "P \<notin> B\<^sub>2" using hard by (by100 blast)
      have hP_notin_B\<^sub>2': "P \<notin> B\<^sub>2'" using hP_notin_B\<^sub>2 hB\<^sub>2'_sub by (by100 blast)
      have hsstar_pos: "0 < sstar"
      proof -
        have h_0_le: "0 \<le> sstar" using hsstar_01 by (by100 simp)
        have h_ne: "sstar \<noteq> 0"
        proof
          assume hs0: "sstar = 0"
          have h_\<gamma>_0_in: "\<gamma>\<^sub>1 0 \<in> B\<^sub>2'" using hsstar_T hs0 by (by100 simp)
          have "P \<in> B\<^sub>2'" using h_\<gamma>_0_in h_\<gamma>\<^sub>1_0_P by (by100 simp)
          thus False using hP_notin_B\<^sub>2' by (by100 blast)
        qed
        show ?thesis using h_0_le h_ne by (by100 linarith)
      qed
      have h_R_B\<^sub>1': "?R \<in> B\<^sub>1'"
      proof -
        have "?R \<in> path_image \<gamma>\<^sub>1" using hsstar_01 unfolding path_image_def by (by100 blast)
        thus ?thesis using h_pim_1 by (by100 simp)
      qed
      have h_R_B\<^sub>2': "?R \<in> B\<^sub>2'" by (rule hsstar_T)
      (** R ≠ Q: R ∈ B_1 \<subseteq> B_1' \<subseteq> B_1, Q \<notin> B_1 from hard. **)
      have hQ_notin_B\<^sub>1: "Q \<notin> B\<^sub>1" using hard by (by100 blast)
      have h_R_B\<^sub>1: "?R \<in> B\<^sub>1" using h_R_B\<^sub>1' hB\<^sub>1'_sub by (by100 blast)
      have h_R_ne_Q: "?R \<noteq> Q"
      proof
        assume heq: "?R = Q"
        have "Q \<in> B\<^sub>1" using h_R_B\<^sub>1 heq by (by100 simp)
        thus False using hQ_notin_B\<^sub>1 by (by100 blast)
      qed
      (** R ∈ B_2' ⊆ path_image γ_2: get s* in [0,1]. **)
      have h_R_pim_2: "?R \<in> path_image \<gamma>\<^sub>2" using h_R_B\<^sub>2' h_pim_2 by (by100 simp)
      have h_R_img: "?R \<in> \<gamma>\<^sub>2 ` {0..1}"
        using h_R_pim_2 unfolding path_image_def by (by100 simp)
      obtain sstar_2 where hsstar_2_01: "sstar_2 \<in> {0..1}" and hsstar_2_eq_sym: "?R = \<gamma>\<^sub>2 sstar_2"
        by (rule imageE[OF h_R_img])
      have hsstar_2_eq: "\<gamma>\<^sub>2 sstar_2 = ?R" using hsstar_2_eq_sym by (by100 simp)
      have h_\<gamma>\<^sub>2_1_Q: "\<gamma>\<^sub>2 1 = Q" using h_pf_2 unfolding pathfinish_def by (by100 simp)
      have h_sstar_2_lt_1: "sstar_2 < 1"
      proof -
        have h_le: "sstar_2 \<le> 1" using hsstar_2_01 by (by100 simp)
        have h_ne1: "sstar_2 \<noteq> 1"
        proof
          assume h1: "sstar_2 = 1"
          have "\<gamma>\<^sub>2 1 = ?R" using hsstar_2_eq h1 by (by100 simp)
          hence "?R = Q" using h_\<gamma>\<^sub>2_1_Q by (by100 simp)
          thus False using h_R_ne_Q by (by100 blast)
        qed
        show ?thesis using h_le h_ne1 by (by100 linarith)
      qed
      (** Construct B_1'' = γ_1([0, sstar]). **)
      have h_0_01: "(0::real) \<in> {0..1}" by (by100 simp)
      obtain K\<^sub>1'' where hK\<^sub>1''_comp: "geotop_is_complex K\<^sub>1''"
                    and hK\<^sub>1''_poly: "geotop_polyhedron K\<^sub>1'' = \<gamma>\<^sub>1 ` closed_segment 0 sstar"
                    and hK\<^sub>1''_1dim: "geotop_complex_is_1dim K\<^sub>1''"
        using geotop_subarc_polyhedron[OF hB\<^sub>1' h_arc_1 h_pim_1 h_0_01 hsstar_01 hsstar_pos]
        by (by100 blast)
      let ?B\<^sub>1'' = "\<gamma>\<^sub>1 ` closed_segment 0 sstar"
      have h_seg_1: "closed_segment 0 sstar = {0..sstar}"
        using hsstar_pos closed_segment_eq_real_ivl by (by100 simp)
      have h_sstar_ne_0: "sstar \<noteq> 0" using hsstar_pos by (by100 simp)
      have h_arc_sub_1: "arc (subpath 0 sstar \<gamma>\<^sub>1)"
        by (rule arc_subpath_arc[OF h_arc_1 h_0_01 hsstar_01 h_sstar_ne_0[symmetric]])
      have h_pim_sub_1: "path_image (subpath 0 sstar \<gamma>\<^sub>1) = ?B\<^sub>1''"
        by (rule path_image_subpath_gen)
      have h_geotop_arc_1'': "geotop_is_arc ?B\<^sub>1'' (subspace_topology UNIV geotop_euclidean_topology ?B\<^sub>1'')"
        using geotop_HOL_arc_imp_geotop_is_arc[OF h_arc_sub_1] h_pim_sub_1 by (by100 simp)
      have h_broken_1'': "geotop_is_broken_line ?B\<^sub>1''"
        unfolding geotop_is_broken_line_def
        using hK\<^sub>1''_comp hK\<^sub>1''_poly hK\<^sub>1''_1dim h_geotop_arc_1'' by (by100 blast)
      (** B_2'' = γ_2([sstar_2, 1]). **)
      have h_1_01: "(1::real) \<in> {0..1}" by (by100 simp)
      obtain K\<^sub>2'' where hK\<^sub>2''_comp: "geotop_is_complex K\<^sub>2''"
                    and hK\<^sub>2''_poly: "geotop_polyhedron K\<^sub>2'' = \<gamma>\<^sub>2 ` closed_segment sstar_2 1"
                    and hK\<^sub>2''_1dim: "geotop_complex_is_1dim K\<^sub>2''"
        using geotop_subarc_polyhedron[OF hB\<^sub>2' h_arc_2 h_pim_2 hsstar_2_01 h_1_01 h_sstar_2_lt_1]
        by (by100 blast)
      let ?B\<^sub>2'' = "\<gamma>\<^sub>2 ` closed_segment sstar_2 1"
      have h_seg_2: "closed_segment sstar_2 1 = {sstar_2..1}"
        using h_sstar_2_lt_1 closed_segment_eq_real_ivl by (by100 simp)
      have h_s_2_ne_1: "sstar_2 \<noteq> 1" using h_sstar_2_lt_1 by (by100 simp)
      have h_arc_sub_2: "arc (subpath sstar_2 1 \<gamma>\<^sub>2)"
        by (rule arc_subpath_arc[OF h_arc_2 hsstar_2_01 h_1_01 h_s_2_ne_1])
      have h_pim_sub_2: "path_image (subpath sstar_2 1 \<gamma>\<^sub>2) = ?B\<^sub>2''"
        by (rule path_image_subpath_gen)
      have h_geotop_arc_2'': "geotop_is_arc ?B\<^sub>2'' (subspace_topology UNIV geotop_euclidean_topology ?B\<^sub>2'')"
        using geotop_HOL_arc_imp_geotop_is_arc[OF h_arc_sub_2] h_pim_sub_2 by (by100 simp)
      have h_broken_2'': "geotop_is_broken_line ?B\<^sub>2''"
        unfolding geotop_is_broken_line_def
        using hK\<^sub>2''_comp hK\<^sub>2''_poly hK\<^sub>2''_1dim h_geotop_arc_2'' by (by100 blast)
      (** B_1'' ∩ B_2'' = {R} via minimality. **)
      have h_B\<^sub>2''_sub_B\<^sub>2': "?B\<^sub>2'' \<subseteq> B\<^sub>2'"
      proof
        fix x assume "x \<in> ?B\<^sub>2''"
        then obtain t where ht_seg: "t \<in> closed_segment sstar_2 1" and hxt: "x = \<gamma>\<^sub>2 t"
          by (by100 blast)
        have ht_ivl: "t \<in> {sstar_2..1}" using ht_seg h_seg_2 by (by100 simp)
        have ht_01: "t \<in> {0..1}" using ht_ivl hsstar_2_01 by (by100 auto)
        have "x \<in> path_image \<gamma>\<^sub>2" using hxt ht_01 unfolding path_image_def by (by100 blast)
        thus "x \<in> B\<^sub>2'" using h_pim_2 by (by100 simp)
      qed
      have h_int_R: "?B\<^sub>1'' \<inter> ?B\<^sub>2'' = {?R}"
      proof
        show "?B\<^sub>1'' \<inter> ?B\<^sub>2'' \<subseteq> {?R}"
        proof
          fix x assume hx: "x \<in> ?B\<^sub>1'' \<inter> ?B\<^sub>2''"
          have hx_1: "x \<in> ?B\<^sub>1''" using hx by (by100 blast)
          have hx_2: "x \<in> ?B\<^sub>2''" using hx by (by100 blast)
          obtain t where ht_seg: "t \<in> closed_segment 0 sstar" and hxt: "x = \<gamma>\<^sub>1 t"
            using hx_1 by (by100 blast)
          have ht_ivl: "t \<in> {0..sstar}" using ht_seg h_seg_1 by (by100 simp)
          have ht_0: "0 \<le> t" using ht_ivl by (by100 simp)
          have ht_sstar: "t \<le> sstar" using ht_ivl by (by100 simp)
          have hx_B\<^sub>2': "x \<in> B\<^sub>2'" using hx_2 h_B\<^sub>2''_sub_B\<^sub>2' by (by100 blast)
          have h_\<gamma>t_B\<^sub>2': "\<gamma>\<^sub>1 t \<in> B\<^sub>2'" using hxt hx_B\<^sub>2' by (by100 simp)
          have h_t_ge: "sstar \<le> t"
          proof (rule ccontr)
            assume "\<not> sstar \<le> t"
            hence h_t_lt: "t < sstar" by (by100 linarith)
            have h_t_in: "t \<in> {0..<sstar}" using ht_0 h_t_lt by (by100 simp)
            have h_notin: "\<gamma>\<^sub>1 t \<notin> B\<^sub>2'" using hsstar_min h_t_in by (by100 blast)
            show False using h_notin h_\<gamma>t_B\<^sub>2' by (by100 simp)
          qed
          have h_t_eq: "t = sstar" using ht_sstar h_t_ge by (by100 linarith)
          have "x = ?R" using hxt h_t_eq by (by100 simp)
          thus "x \<in> {?R}" by (by100 simp)
        qed
        show "{?R} \<subseteq> ?B\<^sub>1'' \<inter> ?B\<^sub>2''"
        proof -
          have hR_1: "?R \<in> ?B\<^sub>1''"
          proof -
            have hsstar_seg: "sstar \<in> closed_segment 0 sstar"
              using h_seg_1 hsstar_pos by (by100 simp)
            show ?thesis using hsstar_seg by (by100 blast)
          qed
          have hR_2: "?R \<in> ?B\<^sub>2''"
          proof -
            have h_s2_le_1: "sstar_2 \<le> 1" using h_sstar_2_lt_1 by (by100 linarith)
            have hsstar_2_ivl: "sstar_2 \<in> {sstar_2..1}" using h_s2_le_1 by (by100 simp)
            have hsstar_2_seg: "sstar_2 \<in> closed_segment sstar_2 1"
              using hsstar_2_ivl h_seg_2 by (by100 simp)
            have "\<gamma>\<^sub>2 sstar_2 \<in> ?B\<^sub>2''" using hsstar_2_seg by (by100 blast)
            thus ?thesis using hsstar_2_eq by (by100 simp)
          qed
          show ?thesis using hR_1 hR_2 by (by100 simp)
        qed
      qed
      (** Arc data for glue. **)
      have h_arc_data_1'': "\<exists>\<gamma>. arc \<gamma> \<and> path_image \<gamma> = ?B\<^sub>1'' \<and> pathfinish \<gamma> = ?R"
      proof -
        have h_pf_sub: "pathfinish (subpath 0 sstar \<gamma>\<^sub>1) = ?R"
          unfolding subpath_def pathfinish_def by (by100 simp)
        show ?thesis using h_arc_sub_1 h_pim_sub_1 h_pf_sub by (by100 blast)
      qed
      have h_arc_data_2'': "\<exists>\<gamma>. arc \<gamma> \<and> path_image \<gamma> = ?B\<^sub>2'' \<and> pathstart \<gamma> = ?R"
      proof -
        have h_ps_sub: "pathstart (subpath sstar_2 1 \<gamma>\<^sub>2) = ?R"
          unfolding subpath_def pathstart_def using hsstar_2_eq by (by100 simp)
        show ?thesis using h_arc_sub_2 h_pim_sub_2 h_ps_sub by (by100 blast)
      qed
      (** Glue. **)
      have h_glued: "geotop_is_broken_line (?B\<^sub>1'' \<union> ?B\<^sub>2'')"
        by (rule geotop_broken_lines_glue_disjoint_endpoints
                 [OF h_broken_1'' h_broken_2'' h_arc_data_1'' h_arc_data_2'' h_int_R])
      (** Containment. **)
      have h_B\<^sub>1''_sub_B\<^sub>1': "?B\<^sub>1'' \<subseteq> B\<^sub>1'"
      proof
        fix x assume "x \<in> ?B\<^sub>1''"
        then obtain t where ht_seg: "t \<in> closed_segment 0 sstar" and hxt: "x = \<gamma>\<^sub>1 t"
          by (by100 blast)
        have ht_ivl: "t \<in> {0..sstar}" using ht_seg h_seg_1 by (by100 simp)
        have ht_01: "t \<in> {0..1}" using ht_ivl hsstar_01 by (by100 auto)
        have "x \<in> path_image \<gamma>\<^sub>1" using hxt ht_01 unfolding path_image_def by (by100 blast)
        thus "x \<in> B\<^sub>1'" using h_pim_1 by (by100 simp)
      qed
      have h_union_sub: "?B\<^sub>1'' \<union> ?B\<^sub>2'' \<subseteq> B\<^sub>1 \<union> B\<^sub>2"
      proof -
        have h1: "?B\<^sub>1'' \<subseteq> B\<^sub>1" using h_B\<^sub>1''_sub_B\<^sub>1' hB\<^sub>1'_sub by (by100 blast)
        have h2: "?B\<^sub>2'' \<subseteq> B\<^sub>2" using h_B\<^sub>2''_sub_B\<^sub>2' hB\<^sub>2'_sub by (by100 blast)
        show ?thesis using h1 h2 by (by100 blast)
      qed
      have h_P_in: "P \<in> ?B\<^sub>1'' \<union> ?B\<^sub>2''"
      proof -
        have h_sstar_ge: "0 \<le> sstar" using hsstar_pos by (by100 linarith)
        have h_0_ivl: "(0::real) \<in> {0..sstar}" using h_sstar_ge by (by100 simp)
        have h_0_seg: "(0::real) \<in> closed_segment 0 sstar"
          using h_0_ivl h_seg_1 by (by100 simp)
        have "\<gamma>\<^sub>1 0 \<in> ?B\<^sub>1''" using h_0_seg by (by100 blast)
        thus ?thesis using h_\<gamma>\<^sub>1_0_P by (by100 simp)
      qed
      have h_Q_in: "Q \<in> ?B\<^sub>1'' \<union> ?B\<^sub>2''"
      proof -
        have h_s2_le_1: "sstar_2 \<le> 1" using h_sstar_2_lt_1 by (by100 linarith)
        have h_1_ivl: "(1::real) \<in> {sstar_2..1}" using h_s2_le_1 by (by100 simp)
        have h_1_seg: "(1::real) \<in> closed_segment sstar_2 1"
          using h_1_ivl h_seg_2 by (by100 simp)
        have "\<gamma>\<^sub>2 1 \<in> ?B\<^sub>2''" using h_1_seg by (by100 blast)
        thus ?thesis using h_\<gamma>\<^sub>2_1_Q by (by100 simp)
      qed
      show ?thesis using h_glued h_union_sub h_P_in h_Q_in by (by100 blast)
    qed
  qed
qed

(** Broken-line concatenation: two broken lines sharing an endpoint combine
    into a single broken line within the ambient set \<open>U\<close>.
    Proved via \<open>geotop_broken_line_arc_reduction\<close> + transitivity of \<open>\<subseteq>\<close>. **)
lemma geotop_broken_line_concat:
  fixes B\<^sub>1 B\<^sub>2 U :: "'a::euclidean_space set"
  assumes hB\<^sub>1: "geotop_is_broken_line B\<^sub>1" and hB\<^sub>1U: "B\<^sub>1 \<subseteq> U"
  assumes hB\<^sub>2: "geotop_is_broken_line B\<^sub>2" and hB\<^sub>2U: "B\<^sub>2 \<subseteq> U"
  assumes hP: "P \<in> B\<^sub>1" and hQ\<^sub>0_1: "Q\<^sub>0 \<in> B\<^sub>1" and hQ\<^sub>0_2: "Q\<^sub>0 \<in> B\<^sub>2" and hQ: "Q \<in> B\<^sub>2"
  assumes hU_open: "open U"
  shows "\<exists>B. geotop_is_broken_line B \<and> B \<subseteq> U \<and> P \<in> B \<and> Q \<in> B"
proof -
  obtain B where hB: "geotop_is_broken_line B" and hBsub: "B \<subseteq> B\<^sub>1 \<union> B\<^sub>2"
              and hPB: "P \<in> B" and hQB: "Q \<in> B"
    using geotop_broken_line_arc_reduction[OF hB\<^sub>1 hB\<^sub>2 hP hQ\<^sub>0_1 hQ\<^sub>0_2 hQ]
    by (by100 blast)
  have hunion_U: "B\<^sub>1 \<union> B\<^sub>2 \<subseteq> U" using hB\<^sub>1U hB\<^sub>2U by (by100 blast)
  have hBU: "B \<subseteq> U" using hBsub hunion_U by (by100 blast)
  show ?thesis using hB hBU hPB hQB by (by100 blast)
qed

theorem Theorem_GT_1_13:
  fixes U :: "'a::euclidean_space set"
  assumes hU_open: "U \<in> geotop_euclidean_topology"
  assumes hU_conn: "top1_connected_on U (subspace_topology UNIV geotop_euclidean_topology U)"
  shows "geotop_broken_line_connected U"
proof -
  (** (1) For any P \<in> U, the set B_P = {Q \<in> U | P is connected to Q by a broken line in
         U} is open (any Q has an open ball in U which is convex, hence broken-line
         connected; any Q' in that ball extends the path). **)
  have h_B_open:
    "\<forall>P\<in>U. (\<exists>BP. BP \<subseteq> U \<and> P \<in> BP \<and> BP \<in> geotop_euclidean_topology \<and>
           (\<forall>Q\<in>BP. \<exists>B. geotop_is_broken_line B \<and> B \<subseteq> U \<and> P \<in> B \<and> Q \<in> B))"
  proof
    fix P assume hP: "P \<in> U"
    have hU_HOL: "open U"
      using hU_open unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    have hball_ex: "\<exists>e>0. ball P e \<subseteq> U"
      using hU_HOL hP open_contains_ball by (by100 blast)
    then obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" and h\<epsilon>sub: "ball P \<epsilon> \<subseteq> U"
      by (by100 blast)
    let ?BP = "ball P \<epsilon>"
    have hBP_open: "open ?BP" by (by100 simp)
    have hBP_topgeo: "?BP \<in> geotop_euclidean_topology"
      using hBP_open unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    have hBP_convex: "convex ?BP" by (by100 simp)
    have hBP_bl: "geotop_broken_line_connected ?BP"
      by (rule geotop_convex_open_broken_line_connected[OF hBP_topgeo hBP_convex])
    have hP_BP: "P \<in> ?BP" using h\<epsilon> by (by100 simp)
    have hQ_bline: "\<forall>Q\<in>?BP. \<exists>B. geotop_is_broken_line B \<and> B \<subseteq> ?BP \<and> P \<in> B \<and> Q \<in> B"
      using hBP_bl hP_BP unfolding geotop_broken_line_connected_def by (by100 blast)
    have hQ_bline_U: "\<forall>Q\<in>?BP. \<exists>B. geotop_is_broken_line B \<and> B \<subseteq> U \<and> P \<in> B \<and> Q \<in> B"
    proof
      fix Q assume hQ: "Q \<in> ?BP"
      obtain B where hB: "geotop_is_broken_line B" and hBBP: "B \<subseteq> ?BP"
                 and hPB: "P \<in> B" and hQB: "Q \<in> B"
        using hQ_bline hQ by (by100 blast)
      have "B \<subseteq> U" using hBBP h\<epsilon>sub by (by100 blast)
      then show "\<exists>B. geotop_is_broken_line B \<and> B \<subseteq> U \<and> P \<in> B \<and> Q \<in> B"
        using hB hPB hQB by (by100 blast)
    qed
    show "\<exists>BP. BP \<subseteq> U \<and> P \<in> BP \<and> BP \<in> geotop_euclidean_topology \<and>
                 (\<forall>Q\<in>BP. \<exists>B. geotop_is_broken_line B \<and> B \<subseteq> U \<and> P \<in> B \<and> Q \<in> B)"
      using h\<epsilon>sub hP_BP hBP_topgeo hQ_bline_U by (by100 blast)
  qed
  (** (2) The complement U - B_P is also open. NOTE: the statement below is weaker than
         the actual content (the empty-set witness satisfies it vacuously). The real
         content is captured by h_B_eq_U. We close with V = {} and use h_B_eq_U directly. **)
  have h_complement_open:
    "\<forall>P\<in>U. (\<exists>V. V \<subseteq> U \<and> V \<in> geotop_euclidean_topology \<and>
              (\<forall>Q\<in>V. \<not> (\<exists>B. geotop_is_broken_line B \<and> B \<subseteq> U \<and> P \<in> B \<and> Q \<in> B)) \<and>
              (V \<union> (U - V) = U))"
  proof
    fix P assume "P \<in> U"
    have "({}::'a set) \<in> geotop_euclidean_topology"
      unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
      by (by100 simp)
    then show "\<exists>V. V \<subseteq> U \<and> V \<in> geotop_euclidean_topology \<and>
                   (\<forall>Q\<in>V. \<not> (\<exists>B. geotop_is_broken_line B \<and> B \<subseteq> U \<and> P \<in> B \<and> Q \<in> B)) \<and>
                   (V \<union> (U - V) = U)"
      by (by100 blast)
  qed
  (** (3) U is connected (hypothesis); hence the partition B_P \<union> (U - B_P) = U with both
         open forces one to be empty. B_P \<ne> \<emptyset> (contains P), so U - B_P = \<emptyset>, i.e. B_P = U.
         Structure:
           (3a) Define \<open>B_P\<close> = broken-line reachable set from \<open>P\<close> in \<open>U\<close>.
           (3b) \<open>B_P\<close> is open: any \<open>Q \<in> B_P\<close> has an open ball \<open>V \<subseteq> U\<close> around \<open>Q\<close>;
                \<open>V\<close> is convex, broken-line connected, so any \<open>Q'\<in>V\<close> is \<open>P\<close>-reachable
                by concatenation (broken-line concat lemma).
           (3c) \<open>U \<setminus> B_P\<close> is open: any \<open>Q \<in> U \<setminus> B_P\<close> has a ball \<open>V \<subseteq> U\<close>;
                if some \<open>Q' \<in> V\<close> were in \<open>B_P\<close>, concatenation gives \<open>P\<close>-reachable \<open>Q\<close>,
                contradiction. So \<open>V \<subseteq> U \<setminus> B_P\<close>.
           (3d) \<open>U\<close> connected + partition into two open sets forces one empty.
           (3e) \<open>P \<in> B_P\<close> (any ball \<open>V \<subseteq> U\<close> around P is broken-line connected so
                has a \<open>Q' \<in> V\<close> with broken-line from \<open>P\<close> to \<open>Q'\<close>; then \<open>Q' \<in> B_P\<close>).
                Actually simpler: \<open>P \<in> B\<close> trivially for any \<open>B\<close> containing \<open>P\<close> —
                witness: a segment \<open>P, Q_0\<close> for some \<open>Q_0 \<in> ball P \<epsilon> \<setminus> {P}\<close>. **)
  (** For each \<open>P \<in> U\<close>, let \<open>B_P = {Q \<in> U. \<exists> broken line P-Q in U}\<close>.
      \<open>B_P\<close> is open (h_B_open). \<open>U \<setminus> B_P\<close> is open: any \<open>Q \<in> U \<setminus> B_P\<close> has an open
      ball \<open>V \<subseteq> U\<close> such that if some \<open>Q' \<in> V\<close> were in \<open>B_P\<close>, concatenation gives
      \<open>Q \<in> B_P\<close>, contradiction. By connectedness of \<open>U\<close>, \<open>B_P \<in> {\<emptyset>, U}\<close>; \<open>P \<in> B_P\<close>,
      so \<open>B_P = U\<close>. **)
  have hU_HOL_open: "open U"
    using hU_open unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have h_B_eq_U:
    "\<forall>P\<in>U. (\<forall>Q\<in>U. \<exists>B. geotop_is_broken_line B \<and> B \<subseteq> U \<and> P \<in> B \<and> Q \<in> B)"
  proof (rule ballI)
    fix P assume hP: "P \<in> U"
    define BP :: "'a set" where
      "BP = {Q. Q \<in> U \<and> (\<exists>B. geotop_is_broken_line B \<and> B \<subseteq> U \<and> P \<in> B \<and> Q \<in> B)}"
    (** (a) \<open>BP\<close> is open in HOL sense. **)
    have hBP_open: "open BP"
    proof (rule openI)
      fix Q assume hQBP: "Q \<in> BP"
      then have hQU: "Q \<in> U" and hQ_reach:
          "\<exists>B\<^sub>1. geotop_is_broken_line B\<^sub>1 \<and> B\<^sub>1 \<subseteq> U \<and> P \<in> B\<^sub>1 \<and> Q \<in> B\<^sub>1"
        unfolding BP_def by (by100 blast)+
      obtain B\<^sub>1 where hB\<^sub>1: "geotop_is_broken_line B\<^sub>1" and hB\<^sub>1U: "B\<^sub>1 \<subseteq> U"
                  and hPB\<^sub>1: "P \<in> B\<^sub>1" and hQB\<^sub>1: "Q \<in> B\<^sub>1"
        using hQ_reach by (by100 blast)
      have hrexQ: "\<exists>e>0. ball Q e \<subseteq> U"
        using hU_HOL_open hQU open_contains_ball by (by100 blast)
      obtain r where hr: "r > 0" and hballsub: "ball Q r \<subseteq> U"
        using hrexQ by (by100 blast)
      have hball_top: "ball Q r \<in> geotop_euclidean_topology"
        unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
        by (by100 simp)
      have hball_conv: "convex (ball Q r)" by (by100 simp)
      have hball_bl: "geotop_broken_line_connected (ball Q r)"
        by (rule geotop_convex_open_broken_line_connected[OF hball_top hball_conv])
      (** Any \<open>Q' \<in> ball Q r\<close> is broken-line reachable from \<open>P\<close> via \<open>B\<^sub>1\<close> then concat
          with segment \<open>Q \<to> Q'\<close> in the ball. **)
      have hQ_ball: "Q \<in> ball Q r" using hr by (by100 simp)
      have hQ'_reach: "\<forall>Q'\<in>ball Q r. Q' \<in> BP"
      proof
        fix Q' assume hQ'_ball: "Q' \<in> ball Q r"
        have hQ'U: "Q' \<in> U" using hQ'_ball hballsub by (by100 blast)
        obtain B\<^sub>2 where hB\<^sub>2: "geotop_is_broken_line B\<^sub>2" and hB\<^sub>2ball: "B\<^sub>2 \<subseteq> ball Q r"
                     and hQB\<^sub>2: "Q \<in> B\<^sub>2" and hQ'B\<^sub>2: "Q' \<in> B\<^sub>2"
          using hball_bl hQ_ball hQ'_ball unfolding geotop_broken_line_connected_def
          by (by100 blast)
        have hB\<^sub>2U: "B\<^sub>2 \<subseteq> U" using hB\<^sub>2ball hballsub by (by100 blast)
        obtain B where hB: "geotop_is_broken_line B" and hBU: "B \<subseteq> U"
                    and hPB: "P \<in> B" and hQ'B: "Q' \<in> B"
          using geotop_broken_line_concat[OF hB\<^sub>1 hB\<^sub>1U hB\<^sub>2 hB\<^sub>2U hPB\<^sub>1 hQB\<^sub>1 hQB\<^sub>2 hQ'B\<^sub>2
                                            hU_HOL_open]
          by (by100 blast)
        show "Q' \<in> BP"
          unfolding BP_def using hQ'U hB hBU hPB hQ'B by (by100 blast)
      qed
      show "\<exists>e>0. ball Q e \<subseteq> BP" using hr hQ'_reach by (by100 blast)
    qed
    (** (b) \<open>U \<setminus> BP\<close> is open: any \<open>Q \<in> U \<setminus> BP\<close> has a ball \<open>V \<subseteq> U\<close> entirely in \<open>U \<setminus> BP\<close>
        (otherwise concat would put \<open>Q \<in> BP\<close>). **)
    have hBPcomp_open: "open (U - BP)"
    proof (rule openI)
      fix Q assume hQdiff: "Q \<in> U - BP"
      then have hQU: "Q \<in> U" and hQ_notBP: "Q \<notin> BP" by (by100 blast)+
      have hrex: "\<exists>e>0. ball Q e \<subseteq> U"
        using hU_HOL_open hQU open_contains_ball by (by100 blast)
      obtain r where hr: "r > 0" and hballsub: "ball Q r \<subseteq> U" using hrex by (by100 blast)
      have hball_top: "ball Q r \<in> geotop_euclidean_topology"
        unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
        by (by100 simp)
      have hball_conv: "convex (ball Q r)" by (by100 simp)
      have hball_bl: "geotop_broken_line_connected (ball Q r)"
        by (rule geotop_convex_open_broken_line_connected[OF hball_top hball_conv])
      have hQ_ball: "Q \<in> ball Q r" using hr by (by100 simp)
      have hballsub_comp: "ball Q r \<subseteq> U - BP"
      proof
        fix Q' assume hQ'_ball: "Q' \<in> ball Q r"
        have hQ'U: "Q' \<in> U" using hQ'_ball hballsub by (by100 blast)
        (** Contradiction: if \<open>Q' \<in> BP\<close>, concat gives \<open>Q \<in> BP\<close>. **)
        have hQ'_notBP: "Q' \<notin> BP"
        proof
          assume hQ'BP: "Q' \<in> BP"
          then obtain B\<^sub>1 where hB\<^sub>1: "geotop_is_broken_line B\<^sub>1" and hB\<^sub>1U: "B\<^sub>1 \<subseteq> U"
                            and hPB\<^sub>1: "P \<in> B\<^sub>1" and hQ'B\<^sub>1: "Q' \<in> B\<^sub>1"
            unfolding BP_def by (by100 blast)
          obtain B\<^sub>2 where hB\<^sub>2: "geotop_is_broken_line B\<^sub>2" and hB\<^sub>2ball: "B\<^sub>2 \<subseteq> ball Q r"
                       and hQ'B\<^sub>2: "Q' \<in> B\<^sub>2" and hQB\<^sub>2: "Q \<in> B\<^sub>2"
            using hball_bl hQ'_ball hQ_ball unfolding geotop_broken_line_connected_def
            by (by100 blast)
          have hB\<^sub>2U: "B\<^sub>2 \<subseteq> U" using hB\<^sub>2ball hballsub by (by100 blast)
          obtain B where hB: "geotop_is_broken_line B" and hBU: "B \<subseteq> U"
                      and hPB: "P \<in> B" and hQB: "Q \<in> B"
            using geotop_broken_line_concat[OF hB\<^sub>1 hB\<^sub>1U hB\<^sub>2 hB\<^sub>2U hPB\<^sub>1 hQ'B\<^sub>1 hQ'B\<^sub>2 hQB\<^sub>2
                                              hU_HOL_open]
            by (by100 blast)
          have "Q \<in> BP" unfolding BP_def using hQU hB hBU hPB hQB by (by100 blast)
          thus False using hQ_notBP by (by100 blast)
        qed
        show "Q' \<in> U - BP" using hQ'U hQ'_notBP by (by100 blast)
      qed
      show "\<exists>e>0. ball Q e \<subseteq> U - BP" using hr hballsub_comp by (by100 blast)
    qed
    (** (c) \<open>P \<in> BP\<close>: tiny segment \<open>P, Q\<^sub>0\<close> in a ball around P. **)
    have hP_BP: "P \<in> BP"
    proof -
      have hrex: "\<exists>e>0. ball P e \<subseteq> U"
        using hU_HOL_open hP open_contains_ball by (by100 blast)
      obtain r where hr: "r > 0" and hballsub: "ball P r \<subseteq> U" using hrex by (by100 blast)
      have hball_top: "ball P r \<in> geotop_euclidean_topology"
        unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
        by (by100 simp)
      have hball_conv: "convex (ball P r)" by (by100 simp)
      have hball_bl: "geotop_broken_line_connected (ball P r)"
        by (rule geotop_convex_open_broken_line_connected[OF hball_top hball_conv])
      have hP_ball: "P \<in> ball P r" using hr by (by100 simp)
      obtain B where hB: "geotop_is_broken_line B" and hBball: "B \<subseteq> ball P r"
                  and hPB: "P \<in> B"
        using hball_bl hP_ball unfolding geotop_broken_line_connected_def by (by100 blast)
      have hBU: "B \<subseteq> U" using hBball hballsub by (by100 blast)
      show "P \<in> BP"
        unfolding BP_def using hP hB hBU hPB by (by100 blast)
    qed
    (** (d) Use connectedness of U to conclude BP = U. **)
    have hU_HOL_conn: "connected U"
      using hU_conn top1_connected_on_geotop_iff_connected by (by100 blast)
    have hBP_sub_U: "BP \<subseteq> U" unfolding BP_def by (by100 blast)
    have hBP_nonempty: "BP \<noteq> {}" using hP_BP by (by100 blast)
    have hBP_eq_U: "BP = U"
    proof (rule ccontr)
      assume "BP \<noteq> U"
      then have hBP_proper: "BP \<subset> U" using hBP_sub_U by (by100 blast)
      have hcomp_nonempty: "U - BP \<noteq> {}" using hBP_proper by (by100 blast)
      (** BP is open in HOL, U - BP is open in HOL; both disjoint; union is U. **)
      have hU_union: "U = BP \<union> (U - BP)" using hBP_sub_U by (by100 blast)
      have hU_disj: "BP \<inter> (U - BP) = {}" by (by100 blast)
      (** By connectedness: one of BP, U - BP is empty. **)
      have hBP_meets_U: "BP \<inter> U \<noteq> {}" using hBP_nonempty hBP_sub_U by (by100 blast)
      have hcomp_meets_U: "(U - BP) \<inter> U \<noteq> {}" using hcomp_nonempty by (by100 blast)
      have hU_sub_union: "U \<subseteq> BP \<union> (U - BP)" using hBP_sub_U by (by100 blast)
      have hinter_empty: "BP \<inter> (U - BP) \<inter> U = {}" by (by100 blast)
      have hU_not_conn: "\<not> connected U"
        unfolding connected_def
        using hBP_open hBPcomp_open hU_sub_union hinter_empty hBP_meets_U hcomp_meets_U
        by (by100 blast)
      show False using hU_not_conn hU_HOL_conn by (by100 blast)
    qed
    (** BP = U means all Q ∈ U are broken-line reachable from P. **)
    have hall_Q: "\<And>Q. Q \<in> U \<Longrightarrow> \<exists>B. geotop_is_broken_line B \<and> B \<subseteq> U \<and> P \<in> B \<and> Q \<in> B"
    proof -
      fix Q assume hQU_l: "Q \<in> U"
      have hQBP: "Q \<in> BP" using hBP_eq_U hQU_l by (by100 blast)
      show "\<exists>B. geotop_is_broken_line B \<and> B \<subseteq> U \<and> P \<in> B \<and> Q \<in> B"
        using hQBP unfolding BP_def by (by100 blast)
    qed
    show "\<forall>Q\<in>U. \<exists>B. geotop_is_broken_line B \<and> B \<subseteq> U \<and> P \<in> B \<and> Q \<in> B"
      using hall_Q by (by100 blast)
  qed
  show ?thesis using h_B_eq_U unfolding geotop_broken_line_connected_def by (by100 blast)
qed

(** from \<S>1 Theorem 14 (geotop.tex:408)
    LATEX VERSION: Let G be a collection of connected sets, with a point P in common. Then
      the union G* is connected. **)
theorem Theorem_GT_1_14:
  assumes "is_topology_on X T"
  assumes "\<forall>g\<in>G. g \<subseteq> X \<and> top1_connected_on g (subspace_topology X T g)"
  assumes "\<forall>g\<in>G. P \<in> g"
  shows "top1_connected_on (\<Union>G) (subspace_topology X T (\<Union>G))"
proof (cases "G = {}")
  case True
  show ?thesis
    by (simp add: True assms(1) subspace_topology_is_topology_on
      top1_connected_on_def)
next
  case False
  have h2: "\<forall>g\<in>G. g \<subseteq> X"
    by (metis assms(2))
  have h3: "\<forall>g\<in>G. top1_connected_on g (subspace_topology X T g)"
    by (metis assms(2))
  have h4: "P \<in> \<Inter>(id ` G)"
    by (metis assms(3) id_apply image_id InterI)
  have h5: "\<Union>G = (\<Union>g\<in>G. id g)"
    by simp
  have h6: "top1_connected_on (\<Union>g\<in>G. id g) (subspace_topology X T (\<Union>g\<in>G. id g))"
    by (rule Theorem_23_3[OF assms(1) False _ _ h4])
       (use h2 h3 in auto)
  show ?thesis
    by (metis h6 h5)
qed

(** from \<S>1 Theorem 15 (geotop.tex:412)
    LATEX VERSION: If M is connected, and M \<subset> L \<subset> \<bar>M\<close>, then L is connected. **)
theorem Theorem_GT_1_15:
  assumes "is_topology_on X T"
  assumes "M \<subseteq> X"
  assumes "M \<subseteq> L" "L \<subseteq> closure_on X T M"
  assumes "top1_connected_on M (subspace_topology X T M)"
  shows "top1_connected_on L (subspace_topology X T L)"
proof -
  have hLX: "L \<subseteq> X"
    using assms(1,2,4) closure_on_subset_carrier by blast
  show ?thesis
    by (metis Theorem_23_4 assms(1,2,3,4,5) hLX)
qed

(** from \<S>1: component C(M,P) (geotop.tex:415)
    LATEX VERSION: The component C(M,P) of M containing P is the union of all connected
      subsets of M that contain P. **)
definition geotop_component_at ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "geotop_component_at X T M P =
    \<Union>{C. C \<subseteq> M \<and> P \<in> C \<and> top1_connected_on C (subspace_topology X T C)}"

(** Bridge: geotop_component_at on UNIV equals HOL connected_component_set. **)
lemma geotop_component_at_UNIV_eq_connected_component_set:
  fixes Y :: "'a::real_normed_vector set" and P :: 'a
  shows "geotop_component_at UNIV geotop_euclidean_topology Y P
         = connected_component_set Y P"
  unfolding geotop_component_at_def connected_component_Union
  using top1_connected_on_geotop_iff_connected by blast

(** Self-membership: P \<in> its own component whenever the singleton is connected. **)
lemma geotop_self_in_component_at:
  assumes hPM: "P \<in> M"
  assumes hsing: "top1_connected_on {P} (subspace_topology X T {P})"
  shows "P \<in> geotop_component_at X T M P"
proof -
  have "{P} \<subseteq> M" using hPM by (by100 simp)
  moreover have "P \<in> {P}" by (by100 simp)
  ultimately show ?thesis
    unfolding geotop_component_at_def using hsing by (by100 blast)
qed

(** from \<S>1 Theorem 16 (geotop.tex:417)
    LATEX VERSION: Every two (different) components of the same set are disjoint. **)
theorem Theorem_GT_1_16:
  assumes hTX: "is_topology_on X T"
  assumes hMX: "M \<subseteq> X"
  assumes hPM: "P \<in> M"
  assumes hQM: "Q \<in> M"
  shows "geotop_component_at X T M P = geotop_component_at X T M Q
       \<or> geotop_component_at X T M P \<inter> geotop_component_at X T M Q = {}"
proof (cases "geotop_component_at X T M P \<inter> geotop_component_at X T M Q = {}")
  case True
  thus ?thesis by simp
next
  case False
  then obtain R where hRP: "R \<in> geotop_component_at X T M P"
                 and hRQ: "R \<in> geotop_component_at X T M Q"
    by blast
  obtain CP where hCP_P: "CP \<subseteq> M \<and> P \<in> CP \<and> top1_connected_on CP (subspace_topology X T CP)"
              and hR_CP: "R \<in> CP"
    using hRP unfolding geotop_component_at_def by blast
  obtain CQ where hCQ_Q: "CQ \<subseteq> M \<and> Q \<in> CQ \<and> top1_connected_on CQ (subspace_topology X T CQ)"
              and hR_CQ: "R \<in> CQ"
    using hRQ unfolding geotop_component_at_def by blast
  have hCP_sub: "CP \<subseteq> X" using hCP_P hMX by fast
  have hCQ_sub: "CQ \<subseteq> X" using hCQ_Q hMX by fast
  have hCP_conn: "top1_connected_on CP (subspace_topology X T CP)" using hCP_P by simp
  have hCQ_conn: "top1_connected_on CQ (subspace_topology X T CQ)" using hCQ_Q by simp
  (** Apply Theorem_GT_1_14 on G = {CP, CQ} with common R. **)
  have hG_sub: "\<forall>g\<in>{CP, CQ}. g \<subseteq> X \<and> top1_connected_on g (subspace_topology X T g)"
    using hCP_sub hCQ_sub hCP_conn hCQ_conn by simp
  have hG_R: "\<forall>g\<in>{CP, CQ}. R \<in> g"
    using hR_CP hR_CQ by simp
  have hUnion_conn: "top1_connected_on (\<Union>{CP, CQ}) (subspace_topology X T (\<Union>{CP, CQ}))"
    by (rule Theorem_GT_1_14[OF hTX hG_sub hG_R])
  have hCPuCQ_eq: "\<Union>{CP, CQ} = CP \<union> CQ" by simp
  have hCPCQ_conn: "top1_connected_on (CP \<union> CQ) (subspace_topology X T (CP \<union> CQ))"
    using hUnion_conn hCPuCQ_eq by simp
  have hCPCQ_sub_M: "CP \<union> CQ \<subseteq> M" using hCP_P hCQ_Q by fast
  have hP_CPCQ: "P \<in> CP \<union> CQ" using hCP_P by fast
  have hQ_CPCQ: "Q \<in> CP \<union> CQ" using hCQ_Q by fast
  have hCPCQ_sub_X: "CP \<union> CQ \<subseteq> X" using hCPCQ_sub_M hMX by fast
  (** Now for any connected C ⊆ M with P ∈ C, apply 1_14 to {C, CP∪CQ} sharing P:
      get C ∪ CP ∪ CQ connected, ⊆ M, contains Q. So C ⊆ component_Q. **)
  have hPQ_sub: "geotop_component_at X T M P \<subseteq> geotop_component_at X T M Q"
  proof (rule subsetI)
    fix x assume hx: "x \<in> geotop_component_at X T M P"
    obtain C where hC_P: "C \<subseteq> M \<and> P \<in> C \<and> top1_connected_on C (subspace_topology X T C)"
                and hxC: "x \<in> C"
      using hx unfolding geotop_component_at_def by blast
    have hCsubX: "C \<subseteq> X" using hC_P hMX by fast
    have hCconn: "top1_connected_on C (subspace_topology X T C)" using hC_P by simp
    have hP_C: "P \<in> C" using hC_P by simp
    (** Apply 1_14 to G = {C, CP∪CQ} with common P. **)
    have hG2_sub: "\<forall>g\<in>{C, CP\<union>CQ}. g \<subseteq> X \<and> top1_connected_on g (subspace_topology X T g)"
      using hCsubX hCconn hCPCQ_sub_X hCPCQ_conn by simp
    have hG2_P: "\<forall>g\<in>{C, CP\<union>CQ}. P \<in> g" using hP_C hP_CPCQ by simp
    have hUn2_conn: "top1_connected_on (\<Union>{C, CP\<union>CQ}) (subspace_topology X T (\<Union>{C, CP\<union>CQ}))"
      by (rule Theorem_GT_1_14[OF hTX hG2_sub hG2_P])
    have hUn2_eq: "\<Union>{C, CP\<union>CQ} = C \<union> CP \<union> CQ" by auto
    have hW_conn: "top1_connected_on (C \<union> CP \<union> CQ) (subspace_topology X T (C \<union> CP \<union> CQ))"
      using hUn2_conn hUn2_eq by simp
    have hW_sub_M: "C \<union> CP \<union> CQ \<subseteq> M" using hC_P hCPCQ_sub_M by fast
    have hQ_W: "Q \<in> C \<union> CP \<union> CQ" using hQ_CPCQ by fast
    have hx_W: "x \<in> C \<union> CP \<union> CQ" using hxC by fast
    have "C \<union> CP \<union> CQ \<in> {D. D \<subseteq> M \<and> Q \<in> D \<and> top1_connected_on D (subspace_topology X T D)}"
      using hW_sub_M hQ_W hW_conn by simp
    thus "x \<in> geotop_component_at X T M Q"
      unfolding geotop_component_at_def using hx_W by blast
  qed
  (** Symmetric direction: component_Q ⊆ component_P. **)
  have hQP_sub: "geotop_component_at X T M Q \<subseteq> geotop_component_at X T M P"
  proof (rule subsetI)
    fix x assume hx: "x \<in> geotop_component_at X T M Q"
    obtain C where hC_Q: "C \<subseteq> M \<and> Q \<in> C \<and> top1_connected_on C (subspace_topology X T C)"
                and hxC: "x \<in> C"
      using hx unfolding geotop_component_at_def by blast
    have hCsubX: "C \<subseteq> X" using hC_Q hMX by fast
    have hCconn: "top1_connected_on C (subspace_topology X T C)" using hC_Q by simp
    have hQ_C: "Q \<in> C" using hC_Q by simp
    have hG2_sub: "\<forall>g\<in>{C, CP\<union>CQ}. g \<subseteq> X \<and> top1_connected_on g (subspace_topology X T g)"
      using hCsubX hCconn hCPCQ_sub_X hCPCQ_conn by simp
    have hG2_Q: "\<forall>g\<in>{C, CP\<union>CQ}. Q \<in> g" using hQ_C hQ_CPCQ by simp
    have hUn2_conn: "top1_connected_on (\<Union>{C, CP\<union>CQ}) (subspace_topology X T (\<Union>{C, CP\<union>CQ}))"
      by (rule Theorem_GT_1_14[OF hTX hG2_sub hG2_Q])
    have hUn2_eq: "\<Union>{C, CP\<union>CQ} = C \<union> CP \<union> CQ" by auto
    have hW_conn: "top1_connected_on (C \<union> CP \<union> CQ) (subspace_topology X T (C \<union> CP \<union> CQ))"
      using hUn2_conn hUn2_eq by simp
    have hW_sub_M: "C \<union> CP \<union> CQ \<subseteq> M" using hC_Q hCPCQ_sub_M by fast
    have hP_W: "P \<in> C \<union> CP \<union> CQ" using hP_CPCQ by fast
    have hx_W: "x \<in> C \<union> CP \<union> CQ" using hxC by fast
    have "C \<union> CP \<union> CQ \<in> {D. D \<subseteq> M \<and> P \<in> D \<and> top1_connected_on D (subspace_topology X T D)}"
      using hW_sub_M hP_W hW_conn by simp
    thus "x \<in> geotop_component_at X T M P"
      unfolding geotop_component_at_def using hx_W by blast
  qed
  have heq: "geotop_component_at X T M P = geotop_component_at X T M Q"
    using hPQ_sub hQP_sub by simp
  thus ?thesis by simp
qed

(** from \<S>1 Theorem 17 (geotop.tex:418)
    LATEX VERSION: If M \<subset> N, then every component of M lies in a component of N. **)
theorem Theorem_GT_1_17:
  assumes "is_topology_on X T" "M \<subseteq> N" "N \<subseteq> X" "P \<in> M"
  shows "\<exists>Q\<in>N. geotop_component_at X T M P \<subseteq> geotop_component_at X T N Q"
proof -
  (** Moise's proof is implicit: take Q = P; M \<subseteq> N gives component_M \<subseteq> component_N. **)
  have hPN: "P \<in> N"
    using assms(2,4) by blast
  have hsub: "geotop_component_at X T M P \<subseteq> geotop_component_at X T N P"
    unfolding geotop_component_at_def
    using assms(2) by blast
  show ?thesis
    using hPN hsub by blast
qed


end
