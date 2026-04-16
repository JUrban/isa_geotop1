theory GeoTop
  imports "Top0.AlgTop" "HOL-Analysis.Cartesian_Euclidean_Space"
begin

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

(** from Introduction: Theorem 1 (geotop.tex:172)
    LATEX VERSION: Every two subdivisions of the same complex have a common subdivision. **)
theorem Theorem_GT_1:
  fixes K L1 L2 :: "'a::real_normed_vector set set"
  assumes "geotop_is_subdivision L1 K"
  assumes "geotop_is_subdivision L2 K"
  shows "\<exists>L. geotop_is_subdivision L L1 \<and> geotop_is_subdivision L L2"
  sorry

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
      then K and L are combinatorially equivalent, written K \<sim>_c L. **)
definition geotop_comb_equiv :: "'a::real_normed_vector set set \<Rightarrow> 'b::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_comb_equiv K L \<longleftrightarrow>
    (\<exists>K' L'. geotop_is_subdivision K' K \<and> geotop_is_subdivision L' L \<and> geotop_isomorphic K' L')"

(** from Introduction: Theorem 2 (geotop.tex:184)
    LATEX VERSION: K \<sim>_c L iff |K| is the image of |L| under a PLH. **)
theorem Theorem_GT_2:
  fixes K :: "'a::real_normed_vector set set" and L :: "'a set set"
  shows "geotop_comb_equiv K L \<longleftrightarrow> (\<exists>f. geotop_PLH L K f \<and> f ` (geotop_polyhedron L) = geotop_polyhedron K)"
  sorry

(** from Introduction: Theorem 3 (geotop.tex:185)
    LATEX VERSION: Combinatorial equivalence is an equivalence relation. **)
theorem Theorem_GT_3:
  shows "equivp (geotop_comb_equiv :: 'a::real_normed_vector set set \<Rightarrow> 'a set set \<Rightarrow> bool)"
  sorry

subsection \<open>Cells, manifolds, dense sets, separability\<close>

(** from Introduction: n-cell (geotop.tex:188)
    LATEX VERSION: An n-cell is a space homeomorphic to an n-simplex. A 1-cell is an arc,
      and a 2-cell is a disk. A combinatorial n-cell is a complex combinatorially equivalent
      to an n-simplex. **)
text \<open>An $n$-cell is a space homeomorphic to an $n$-simplex. We formulate this parametrically:
  the witness simplex lives in the same type as our space, or via a second type variable.
  For the definition to be truly general we use a second parametric type \<open>'b\<close>.\<close>
text \<open>The Euclidean topology on a normed vector space, expressed as a topology in
  Top0's set-of-sets formulation, via the distance function \<open>\<lambda>x y. norm (x - y)\<close>.\<close>
definition geotop_euclidean_topology :: "('a::real_normed_vector) set set" where
  "geotop_euclidean_topology = top1_metric_topology_on (UNIV::'a set) (\<lambda>x y. norm (x - y))"

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

(** from Introduction: Theorem 4 - Invariance of domain (geotop.tex:206)
    LATEX VERSION: Let U be a subset of R^n, such that U is homeomorphic to R^n. Then U is open. **)
theorem Theorem_GT_4_invariance_of_domain:
  fixes U :: "'a::real_normed_vector set"
  assumes "top1_homeomorphism_on U
             (subspace_topology (UNIV::'a set) geotop_euclidean_topology U)
             (UNIV::'a set) geotop_euclidean_topology f"
  shows "U \<in> geotop_euclidean_topology"
  sorry

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
  assumes "is_topology_on X T"
  assumes "\<forall>g\<in>G. g \<subseteq> X \<and> top1_path_connected_on g (subspace_topology X T g)"
  assumes "\<forall>g\<in>G. P \<in> g"
  shows "top1_path_connected_on (\<Union>G) (subspace_topology X T (\<Union>G))"
  sorry

(** from \<S>1 Theorem 2 (geotop.tex:330)
    LATEX VERSION: Pathwise connectivity is preserved by surjective mappings. **)
theorem Theorem_GT_1_2:
  assumes "is_topology_on X TX" "is_topology_on Y TY"
  assumes "top1_continuous_map_on X TX Y TY f"
  assumes "f ` X = Y"
  assumes "top1_path_connected_on X TX"
  shows "top1_path_connected_on Y TY"
  sorry

(** from \<S>1: connected complex (geotop.tex:334)
    LATEX VERSION: A complex K is connected if it is not the union of two disjoint nonempty
      complexes. **)
definition geotop_complex_connected :: "'a::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_complex_connected K \<longleftrightarrow>
    geotop_is_complex K \<and>
    \<not>(\<exists>K1 K2. K1 \<noteq> {} \<and> K2 \<noteq> {} \<and> K1 \<inter> K2 = {} \<and> K = K1 \<union> K2
          \<and> geotop_is_complex K1 \<and> geotop_is_complex K2)"

(** from \<S>1 Theorem 3 (geotop.tex:338)
    LATEX VERSION: Every simplex is pathwise connected. **)
theorem Theorem_GT_1_3:
  fixes \<sigma> :: "'a::real_normed_vector set"
  assumes "geotop_is_simplex \<sigma>"
  shows "top1_path_connected_on \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>)"
  sorry

(** from \<S>1 Theorem 4 (geotop.tex:341)
    LATEX VERSION: Let K be a complex. If K is connected, then |K| is pathwise connected. **)
theorem Theorem_GT_1_4:
  fixes K :: "'a::real_normed_vector set set"
  assumes "geotop_complex_connected K"
  shows "top1_path_connected_on (geotop_polyhedron K)
           (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
  sorry

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
  assumes "is_topology_on X T" "M \<subseteq> X" "H \<subseteq> M" "K \<subseteq> M" "M = H \<union> K"
  shows "geotop_separated X T H K \<longleftrightarrow>
    (H \<in> subspace_topology X T M \<and> K \<in> subspace_topology X T M \<and> H \<inter> K = {})"
  sorry

(** from \<S>1 Theorem 6 (geotop.tex:365)
    LATEX VERSION: A set M \<subset> X is connected iff M is not the union of two nonempty
      separated sets. **)
theorem Theorem_GT_1_6:
  assumes "is_topology_on X T" "M \<subseteq> X"
  shows "top1_connected_on M (subspace_topology X T M) \<longleftrightarrow>
    \<not>(\<exists>H K. H \<noteq> {} \<and> K \<noteq> {} \<and> M = H \<union> K \<and> geotop_separated X T H K)"
  sorry

(** from \<S>1 Theorem 7 (geotop.tex:369)
    LATEX VERSION: For spaces, connectivity is preserved by surjective mappings. **)
theorem Theorem_GT_1_7:
  assumes "is_topology_on X TX" "is_topology_on Y TY"
  assumes "top1_continuous_map_on X TX Y TY f" "f ` X = Y"
  assumes "top1_connected_on X TX"
  shows "top1_connected_on Y TY"
  sorry

(** from \<S>1 Theorem 8 (geotop.tex:373)
    LATEX VERSION: For sets, connectivity is preserved by surjective mappings. **)
theorem Theorem_GT_1_8:
  assumes "is_topology_on X TX" "is_topology_on Y TY"
  assumes "top1_continuous_map_on X TX Y TY f"
  assumes "M \<subseteq> X" "f ` M = N"
  assumes "top1_connected_on M (subspace_topology X TX M)"
  shows "top1_connected_on N (subspace_topology Y TY N)"
  sorry

(** from \<S>1 Theorem 9 (geotop.tex:375)
    LATEX VERSION: Every closed interval in R is connected. **)
theorem Theorem_GT_1_9:
  fixes a b :: real
  assumes "a \<le> b"
  shows "top1_connected_on {t. a \<le> t \<and> t \<le> b}
           (subspace_topology UNIV geotop_euclidean_topology {t. a \<le> t \<and> t \<le> b})"
  sorry

(** from \<S>1 Theorem 10 (geotop.tex:384)
    LATEX VERSION: If H and K are separated, then every connected subset M of H \<union> K lies
      either in H or in K. **)
theorem Theorem_GT_1_10:
  assumes "is_topology_on X T"
  assumes "geotop_separated X T H K"
  assumes "M \<subseteq> H \<union> K"
  assumes "top1_connected_on M (subspace_topology X T M)"
  shows "M \<subseteq> H \<or> M \<subseteq> K"
  sorry

(** from \<S>1 Theorem 11 (geotop.tex:388)
    LATEX VERSION: Every pathwise connected set is connected. **)
theorem Theorem_GT_1_11:
  assumes "is_topology_on X T" "M \<subseteq> X"
  assumes "top1_path_connected_on M (subspace_topology X T M)"
  shows "top1_connected_on M (subspace_topology X T M)"
  sorry

(** from \<S>1 Theorem 12 (geotop.tex:391)
    LATEX VERSION: Let K be a complex. TFAE: (1) K is connected; (2) |K| is pathwise connected;
      (3) |K| is connected. **)
theorem Theorem_GT_1_12:
  fixes K :: "'a::real_normed_vector set set"
  shows "geotop_complex_connected K \<longleftrightarrow>
    top1_path_connected_on (geotop_polyhedron K)
        (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
    and "top1_path_connected_on (geotop_polyhedron K)
           (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) \<longleftrightarrow>
         top1_connected_on (geotop_polyhedron K)
           (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
  sorry

(** from \<S>1: arc (geotop.tex:401)
    LATEX VERSION: An arc is a 1-cell. **)
text \<open>Already defined above as \<open>geotop_is_arc\<close>.\<close>

(** from \<S>1: broken line (geotop.tex:401)
    LATEX VERSION: A broken line is a polyhedral arc. **)
definition geotop_is_broken_line :: "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_broken_line B \<longleftrightarrow>
    (\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = B
       \<and> geotop_is_arc B (subspace_topology UNIV geotop_euclidean_topology B))"

(** from \<S>1 Theorem 13 (geotop.tex:403)
    LATEX VERSION: In R^n, every connected open set U is broken-line-wise connected. **)
definition geotop_broken_line_connected :: "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_broken_line_connected U \<longleftrightarrow>
    (\<forall>P\<in>U. \<forall>Q\<in>U. \<exists>B. geotop_is_broken_line B \<and> B \<subseteq> U \<and> P \<in> B \<and> Q \<in> B)"

theorem Theorem_GT_1_13:
  fixes U :: "'a::real_normed_vector set"
  assumes "U \<in> geotop_euclidean_topology"
  assumes "top1_connected_on U (subspace_topology UNIV geotop_euclidean_topology U)"
  shows "geotop_broken_line_connected U"
  sorry

(** from \<S>1 Theorem 14 (geotop.tex:408)
    LATEX VERSION: Let G be a collection of connected sets, with a point P in common. Then
      the union G* is connected. **)
theorem Theorem_GT_1_14:
  assumes "is_topology_on X T"
  assumes "\<forall>g\<in>G. g \<subseteq> X \<and> top1_connected_on g (subspace_topology X T g)"
  assumes "\<forall>g\<in>G. P \<in> g"
  shows "top1_connected_on (\<Union>G) (subspace_topology X T (\<Union>G))"
  sorry

(** from \<S>1 Theorem 15 (geotop.tex:412)
    LATEX VERSION: If M is connected, and M \<subset> L \<subset> \<bar>M\<close>, then L is connected. **)
theorem Theorem_GT_1_15:
  assumes "is_topology_on X T"
  assumes "M \<subseteq> L" "L \<subseteq> closure_on X T M"
  assumes "top1_connected_on M (subspace_topology X T M)"
  shows "top1_connected_on L (subspace_topology X T L)"
  sorry

(** from \<S>1: component C(M,P) (geotop.tex:415)
    LATEX VERSION: The component C(M,P) of M containing P is the union of all connected
      subsets of M that contain P. **)
definition geotop_component_at ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "geotop_component_at X T M P =
    \<Union>{C. C \<subseteq> M \<and> P \<in> C \<and> top1_connected_on C (subspace_topology X T C)}"

(** from \<S>1 Theorem 16 (geotop.tex:417)
    LATEX VERSION: Every two (different) components of the same set are disjoint. **)
theorem Theorem_GT_1_16:
  assumes "is_topology_on X T" "M \<subseteq> X" "P \<in> M" "Q \<in> M"
  shows "geotop_component_at X T M P = geotop_component_at X T M Q
       \<or> geotop_component_at X T M P \<inter> geotop_component_at X T M Q = {}"
  sorry

(** from \<S>1 Theorem 17 (geotop.tex:418)
    LATEX VERSION: If M \<subset> N, then every component of M lies in a component of N. **)
theorem Theorem_GT_1_17:
  assumes "is_topology_on X T" "M \<subseteq> N" "N \<subseteq> X" "P \<in> M"
  shows "\<exists>Q\<in>N. geotop_component_at X T M P \<subseteq> geotop_component_at X T N Q"
  sorry


section \<open>\<S>2 Separation properties of polygons in $\mathbf{R}^2$\<close>

(** from \<S>2: standard n-ball (geotop.tex:490)
    LATEX VERSION: B^n = {P | P \<in> R^n and d(P_0, P) \<le> 1}, where P_0 is the origin. **)
definition geotop_std_ball :: "'a::real_normed_vector set" where
  "geotop_std_ball = {P. norm P \<le> 1}"

(** from \<S>2: standard n-sphere (geotop.tex:494)
    LATEX VERSION: S^n = {P | P \<in> R^n and d(P_0, P) = 1}. **)
definition geotop_std_sphere :: "'a::real_normed_vector set" where
  "geotop_std_sphere = {P. norm P = 1}"

(** from \<S>2: n-sphere as an abstract space (geotop.tex:500)
    LATEX VERSION: A space (or set) S^n is an n-sphere if S^n is homeomorphic to S^n (standard). **)
definition geotop_is_n_sphere :: "'a::real_normed_vector set \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_is_n_sphere X TX n \<longleftrightarrow>
    is_topology_on X TX \<and>
    (\<exists>f. top1_homeomorphism_on X TX
           (geotop_std_sphere::'a set)
           (subspace_topology UNIV geotop_euclidean_topology geotop_std_sphere) f)"

(** from \<S>2: polygon (geotop.tex:500)
    LATEX VERSION: A polygon is a polyhedral 1-sphere. **)
definition geotop_is_polygon :: "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_polygon J \<longleftrightarrow>
    (\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = J
       \<and> geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1)"

(** from \<S>2: triangulation of a polyhedron (geotop.tex:500)
    LATEX VERSION: For each complex K, K is called a triangulation of |K|. **)
text \<open>A triangulation of a set $M$ is a complex $K$ with $|K| = M$.
  Formalized inline as \<open>geotop_polyhedron K = M\<close>.\<close>

(** from \<S>2 Theorem 1 (geotop.tex:502)
    LATEX VERSION: Let J be a polygon in R^2. Then R^2 - J has exactly two components. **)
theorem Theorem_GT_2_1:
  fixes J :: "(real^2) set"
  assumes "geotop_is_polygon J"
  shows "card {C. \<exists>P. P \<in> (UNIV::(real^2) set) - J \<and>
           C = geotop_component_at UNIV geotop_euclidean_topology ((UNIV::(real^2) set) - J) P} = 2"
  sorry

(** from \<S>2 Theorem 1 - Lemma 1 (geotop.tex:514)
    LATEX VERSION: R^2 - J has at most two components. **)
theorem Lemma_GT_2_1a:
  fixes J :: "(real^2) set"
  assumes "geotop_is_polygon J"
  shows "card {C. \<exists>P. P \<in> (UNIV::(real^2) set) - J \<and>
           C = geotop_component_at UNIV geotop_euclidean_topology ((UNIV::(real^2) set) - J) P} \<le> 2"
  sorry

(** from \<S>2 Theorem 1 - Lemma 2 (geotop.tex:527)
    LATEX VERSION: R^2 - J has at least two components. **)
theorem Lemma_GT_2_1b:
  fixes J :: "(real^2) set"
  assumes "geotop_is_polygon J"
  shows "card {C. \<exists>P. P \<in> (UNIV::(real^2) set) - J \<and>
           C = geotop_component_at UNIV geotop_euclidean_topology ((UNIV::(real^2) set) - J) P} \<ge> 2"
  sorry

(** from \<S>2: interior and exterior of a polygon (geotop.tex:553)
    LATEX VERSION: The bounded component I of R^2 - J is called the interior of J, and the
      unbounded component E is called the exterior. **)
text \<open>A set $A \subseteq \mathbb{R}^2$ is \emph{bounded} if there exists $r > 0$ such that
  $A \subseteq N(\mathbf{0}, r)$. We define interior and exterior of a polygon accordingly.\<close>

definition geotop_bounded_R2 :: "(real^2) set \<Rightarrow> bool" where
  "geotop_bounded_R2 A \<longleftrightarrow> (\<exists>r>0. \<forall>P\<in>A. norm P < r)"

definition geotop_polygon_interior :: "(real^2) set \<Rightarrow> (real^2) set" where
  "geotop_polygon_interior J =
    (SOME I. I \<subseteq> UNIV - J \<and> geotop_bounded_R2 I \<and>
       top1_connected_on I (subspace_topology UNIV geotop_euclidean_topology I) \<and>
       (\<forall>P\<in>I. geotop_component_at UNIV geotop_euclidean_topology
                   ((UNIV::(real^2) set) - J) P = I))"

definition geotop_polygon_exterior :: "(real^2) set \<Rightarrow> (real^2) set" where
  "geotop_polygon_exterior J =
    (SOME E. E \<subseteq> UNIV - J \<and> \<not> geotop_bounded_R2 E \<and>
       top1_connected_on E (subspace_topology UNIV geotop_euclidean_topology E) \<and>
       (\<forall>P\<in>E. geotop_component_at UNIV geotop_euclidean_topology
                   ((UNIV::(real^2) set) - J) P = E))"

(** from \<S>2 Theorem 2 (geotop.tex:555)
    LATEX VERSION: Let I be the interior of the polygon J in R^2. Then \<bar>I\<close> is a finite polyhedron. **)
theorem Theorem_GT_2_2:
  fixes J :: "(real^2) set"
  assumes "geotop_is_polygon J"
  shows "\<exists>K. geotop_is_complex K \<and> finite K \<and>
    geotop_polyhedron K = closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  sorry

(** from \<S>2 Theorem 3 (geotop.tex:579)
    LATEX VERSION: No broken line separates R^2. That is, if B is a broken line in R^2,
      then R^2 - B is connected. **)
theorem Theorem_GT_2_3:
  fixes B :: "(real^2) set"
  assumes "geotop_is_broken_line B"
  shows "top1_connected_on (UNIV - B)
           (subspace_topology UNIV geotop_euclidean_topology (UNIV - B))"
  sorry

(** from \<S>2 Theorem 4 (geotop.tex:593)
    LATEX VERSION: Let X be a topological space and let U be an open set. Then Fr U = \<bar>U\<close> - U. **)
theorem Theorem_GT_2_4:
  assumes "is_topology_on X T"
  assumes "U \<in> T"
  assumes "U \<subseteq> X"
  shows "geotop_frontier X T U = closure_on X T U - U"
  sorry

(** from \<S>2 Theorem 5 (geotop.tex:596)
    LATEX VERSION: Let J be a polygon in R^2, with interior I and exterior E. Then every point
      of J is a limit point both of I and of E. **)
theorem Theorem_GT_2_5:
  fixes J :: "(real^2) set"
  assumes "geotop_is_polygon J"
  shows "\<forall>P\<in>J. is_limit_point_of P (geotop_polygon_interior J) UNIV geotop_euclidean_topology
             \<and> is_limit_point_of P (geotop_polygon_exterior J) UNIV geotop_euclidean_topology"
  sorry

(** from \<S>2 Theorem 6 (geotop.tex:611)
    LATEX VERSION: Let J, I, E be as in Theorem 5. Then J = Fr I = Fr E. **)
theorem Theorem_GT_2_6:
  fixes J :: "(real^2) set"
  assumes "geotop_is_polygon J"
  shows "J = geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
    and "J = geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_exterior J)"
  sorry

(** from \<S>2: \<theta>-graph (geotop.tex:619)
    LATEX VERSION: Let M be the union of three arcs B_1, B_2, B_3 with the same end-points P, Q
      but with disjoint interiors. Then M is called a \<theta>-graph. **)
definition geotop_arc_endpoints :: "'a::real_normed_vector set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_arc_endpoints A E \<longleftrightarrow>
    geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A) \<and>
    card E = 2 \<and> E \<subseteq> A \<and>
    (\<exists>f::real\<Rightarrow>'a. top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
        (subspace_topology UNIV geotop_euclidean_topology {t::real. 0 \<le> t \<and> t \<le> 1}) A
        (subspace_topology UNIV geotop_euclidean_topology A) f
      \<and> E = {f 0, f 1})"

definition geotop_arc_interior :: "'a::real_normed_vector set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "geotop_arc_interior A E = A - E"

definition geotop_is_theta_graph ::
  "'a::real_normed_vector set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_is_theta_graph M B1 B2 B3 E \<longleftrightarrow>
    M = B1 \<union> B2 \<union> B3 \<and>
    geotop_arc_endpoints B1 E \<and> geotop_arc_endpoints B2 E \<and> geotop_arc_endpoints B3 E \<and>
    geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E = {} \<and>
    geotop_arc_interior B1 E \<inter> geotop_arc_interior B3 E = {} \<and>
    geotop_arc_interior B2 E \<inter> geotop_arc_interior B3 E = {}"

text \<open>A polyhedral \<theta>-graph is a \<theta>-graph whose arcs are broken lines.\<close>
definition geotop_is_polyhedral_theta_graph ::
  "'a::real_normed_vector set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_is_polyhedral_theta_graph M B1 B2 B3 E \<longleftrightarrow>
    geotop_is_theta_graph M B1 B2 B3 E \<and>
    geotop_is_broken_line B1 \<and> geotop_is_broken_line B2 \<and> geotop_is_broken_line B3"

(** from \<S>2 Theorem 7 (geotop.tex:621)
    LATEX VERSION: Let M = B_1 \<union> B_2 \<union> B_3 be a polyhedral \<theta>-graph in R^2, with Bd B_i = {P,Q}.
      Then (1) Every component of R^2 - M has a polygon B_i \<union> B_j as its frontier, and
      (2) Exactly one of the sets B_i lies, except for its end-points, in the interior of the
      polygon formed by the other two. **)
theorem Theorem_GT_2_7:
  fixes M B1 B2 B3 E :: "(real^2) set"
  assumes "geotop_is_polyhedral_theta_graph M B1 B2 B3 E"
  shows "\<forall>U. (U \<in> {C. \<exists>P\<in>UNIV - M.
           C = geotop_component_at UNIV geotop_euclidean_topology ((UNIV::(real^2) set) - M) P})
         \<longrightarrow> (\<exists>i j. {i,j} \<subseteq> {B1, B2, B3} \<and> i \<noteq> j \<and>
              geotop_is_polygon (i \<union> j) \<and>
              geotop_frontier UNIV geotop_euclidean_topology U = i \<union> j)"
    and "(\<exists>!k. k \<in> {B1, B2, B3} \<and>
          (\<exists>i j. {i,j} = {B1, B2, B3} - {k} \<and> i \<noteq> j \<and> geotop_is_polygon (i \<union> j) \<and>
            geotop_arc_interior k E \<subseteq> geotop_polygon_interior (i \<union> j)))"
  sorry

(** from \<S>2 Theorem 8 (geotop.tex:651)
    LATEX VERSION: Let B_1, B_2, B_3 be as in Theorem 7, with Int B_2 in the interior I_13 of
      B_1 \<union> B_3. Then
      (1) The components of I_13 - Int B_2 are the interiors I_12 and I_23.
      (2) \<bar>I_13\<close> = \<bar>I_12\<close> \<union> \<bar>I_23\<close>.
      (3) \<bar>I_13\<close> - B_2 = (I_12 \<union> Int B_1) \<union> (I_23 \<union> Int B_3), where the sets on the right are
        connected and separated. **)
theorem Theorem_GT_2_8:
  fixes M B1 B2 B3 E :: "(real^2) set"
  assumes "geotop_is_polyhedral_theta_graph M B1 B2 B3 E"
  assumes "geotop_arc_interior B2 E \<subseteq> geotop_polygon_interior (B1 \<union> B3)"
  defines "I12 \<equiv> geotop_polygon_interior (B1 \<union> B2)"
  defines "I23 \<equiv> geotop_polygon_interior (B2 \<union> B3)"
  defines "I13 \<equiv> geotop_polygon_interior (B1 \<union> B3)"
  shows "{C. \<exists>P\<in>I13 - geotop_arc_interior B2 E.
           C = geotop_component_at UNIV geotop_euclidean_topology (I13 - geotop_arc_interior B2 E) P}
         = {I12, I23}"
    and "closure_on UNIV geotop_euclidean_topology I13 =
         closure_on UNIV geotop_euclidean_topology I12
         \<union> closure_on UNIV geotop_euclidean_topology I23"
    and "closure_on UNIV geotop_euclidean_topology I13 - B2 =
         (I12 \<union> geotop_arc_interior B1 E) \<union> (I23 \<union> geotop_arc_interior B3 E)"
    and "top1_connected_on (I12 \<union> geotop_arc_interior B1 E)
           (subspace_topology UNIV geotop_euclidean_topology (I12 \<union> geotop_arc_interior B1 E))"
    and "top1_connected_on (I23 \<union> geotop_arc_interior B3 E)
           (subspace_topology UNIV geotop_euclidean_topology (I23 \<union> geotop_arc_interior B3 E))"
    and "geotop_separated UNIV geotop_euclidean_topology
           (I12 \<union> geotop_arc_interior B1 E) (I23 \<union> geotop_arc_interior B3 E)"
  sorry


section \<open>\<S>3 The Schönflies theorem for polygons in $\mathbf{R}^2$\<close>

(** from \<S>3 Theorem 1 (geotop.tex:724)
    LATEX VERSION: Let \<sigma>^n = v_0 v_1 ... v_n and \<tau>^n = w_0 w_1 ... w_n be simplexes in R^m.
      Then there is a simplicial homeomorphism f: \<sigma>^n \<leftrightarrow> \<tau>^n, f: v_i \<mapsto> w_i. **)
theorem Theorem_GT_3_1:
  fixes V W :: "'a::real_normed_vector set" and \<sigma> \<tau> :: "'a set"
  assumes "geotop_simplex_vertices \<sigma> V"
  assumes "geotop_simplex_vertices \<tau> W"
  assumes "card V = card W"
  assumes "\<phi> \<in> V \<rightarrow>\<^sub>E W"
  assumes "bij_betw \<phi> V W"
  shows "\<exists>f. top1_homeomorphism_on \<sigma>
              (subspace_topology UNIV geotop_euclidean_topology \<sigma>)
              \<tau>
              (subspace_topology UNIV geotop_euclidean_topology \<tau>) f
          \<and> geotop_simplicial_on \<sigma> f \<tau>
          \<and> (\<forall>v\<in>V. f v = \<phi> v)"
  sorry

(** from \<S>3 Theorem 2 (geotop.tex:735)
    LATEX VERSION: In Theorem 1, if m = n, then there is a homeomorphism g: R^n \<leftrightarrow> R^n such
      that g|\<sigma>^n is a simplicial homeomorphism \<sigma>^n \<leftrightarrow> \<tau>^n. **)
theorem Theorem_GT_3_2:
  fixes V W :: "'a::real_normed_vector set" and \<sigma> \<tau> :: "'a set"
  assumes "geotop_simplex_dim \<sigma> n" and "geotop_simplex_dim \<tau> n"
  assumes "geotop_simplex_vertices \<sigma> V" and "geotop_simplex_vertices \<tau> W"
  assumes "\<phi> \<in> V \<rightarrow>\<^sub>E W" and "bij_betw \<phi> V W"
  shows "\<exists>g. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology g
          \<and> (\<forall>x\<in>\<sigma>. g x \<in> \<tau>) \<and> geotop_simplicial_on \<sigma> g \<tau>"
  sorry

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
  assumes "geotop_is_polygon J"
  assumes "geotop_is_complex K"
  assumes "geotop_polyhedron K =
    closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2} > 1"
  shows "\<exists>\<sigma>\<^sub>2. geotop_free_2_simplex K J \<sigma>\<^sub>2"
  sorry

(** from \<S>3 Theorem 4 (geotop.tex:782)
    LATEX VERSION: Let J be a polygon in R^2. Then there is a homeomorphism h: R^2 \<leftrightarrow> R^2,
      such that h(J) is the frontier of a 2-simplex. **)
theorem Theorem_GT_3_4:
  fixes J :: "(real^2) set"
  assumes "geotop_is_polygon J"
  shows "\<exists>h \<sigma>. top1_homeomorphism_on UNIV geotop_euclidean_topology
                 UNIV geotop_euclidean_topology h
          \<and> geotop_simplex_dim \<sigma> 2
          \<and> h ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
  sorry

(** from \<S>3 Theorem 5 (Schönflies for polygons) (geotop.tex:801)
    LATEX VERSION: Let J and J' be polygons in R^2. Then there is a homeomorphism h: R^2 \<leftrightarrow> R^2,
      J \<leftrightarrow> J'. **)
theorem Theorem_GT_3_5:
  fixes J J' :: "(real^2) set"
  assumes "geotop_is_polygon J" and "geotop_is_polygon J'"
  shows "\<exists>h. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology h
          \<and> h ` J = J'"
  sorry

(** from \<S>3 Theorem 6 (geotop.tex:821)
    LATEX VERSION: Every polygon in R^2 is the frontier of a 2-cell in R^2. **)
theorem Theorem_GT_3_6:
  fixes J :: "(real^2) set"
  assumes "geotop_is_polygon J"
  shows "\<exists>D. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2
        \<and> J = geotop_frontier UNIV geotop_euclidean_topology D"
  sorry

(** from \<S>3 Theorem 7 (geotop.tex:824)
    LATEX VERSION: Let J be a polygon in R^2 with interior I, and let U be an open set
      containing \<bar>I\<close>. Then there is a homeomorphism h: R^2 \<leftrightarrow> R^2 such that
      (1) h(J) is the frontier of a 2-simplex, and (2) h|(R^2 - U) is the identity. **)
theorem Theorem_GT_3_7:
  fixes J U :: "(real^2) set"
  assumes "geotop_is_polygon J"
  assumes "U \<in> geotop_euclidean_topology"
  assumes "closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J) \<subseteq> U"
  shows "\<exists>h \<sigma>. top1_homeomorphism_on UNIV geotop_euclidean_topology
                 UNIV geotop_euclidean_topology h
          \<and> geotop_simplex_dim \<sigma> 2
          \<and> h ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>
          \<and> (\<forall>P\<in>UNIV - U. h P = P)"
  sorry


section \<open>\<S>4 The Jordan curve theorem\<close>

text \<open>The goal of this section: Let J be a topological 1-sphere in R^2. Then R^2 - J is
  the union of two disjoint connected sets I and E, such that J = Fr I = Fr E.\<close>

(** from \<S>4 Theorem 1 (geotop.tex:865)
    LATEX VERSION: Let U be an open set in R^n, and let P, Q \<in> U. If P and Q are in different
      components of U, then U is the union of two disjoint open sets containing P and Q. **)
theorem Theorem_GT_4_1:
  fixes U :: "'a::real_normed_vector set"
  assumes "U \<in> geotop_euclidean_topology"
  assumes "P \<in> U" and "Q \<in> U"
  assumes "geotop_component_at UNIV geotop_euclidean_topology U P \<noteq>
           geotop_component_at UNIV geotop_euclidean_topology U Q"
  shows "\<exists>V W. U = V \<union> W \<and> V \<inter> W = {} \<and>
           V \<in> geotop_euclidean_topology \<and> W \<in> geotop_euclidean_topology \<and>
           P \<in> V \<and> Q \<in> W"
  sorry

(** from \<S>4 Theorem 2 (geotop.tex:869)
    LATEX VERSION: Let I be the interior of a polygon in R^2, and let P, Q, R, S be points of
      Fr I, in cyclic order. Let A be an arc from P to R, lying in \<bar>I\<close>, with A \<inter> Fr I = {P,R}.
      Then I - A is the union of two disjoint open sets U_Q, U_S containing Q and S in
      their frontiers. **)
text \<open>We parametrize "cyclic order" abstractly via the existence of the four distinct
  points on the polygon.\<close>
theorem Theorem_GT_4_2:
  fixes J :: "(real^2) set" and A :: "(real^2) set" and P Q R S :: "real^2"
  assumes "geotop_is_polygon J"
  assumes "P \<in> J" "Q \<in> J" "R \<in> J" "S \<in> J"
  assumes "card {P, Q, R, S} = 4"
  assumes "geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A)"
  assumes "A \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes "A \<inter> J = {P, R}"
  shows "\<exists>U\<^sub>Q U\<^sub>S. geotop_polygon_interior J - A = U\<^sub>Q \<union> U\<^sub>S \<and>
           U\<^sub>Q \<inter> U\<^sub>S = {} \<and>
           U\<^sub>Q \<in> geotop_euclidean_topology \<and> U\<^sub>S \<in> geotop_euclidean_topology \<and>
           Q \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>Q \<and>
           S \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>S"
  sorry

(** from \<S>4 Theorem 3 (geotop.tex:886)
    LATEX VERSION: Let J be a topological 1-sphere in R^2. Then R^2 - J is not connected. **)
theorem Theorem_GT_4_3:
  fixes J :: "(real^2) set"
  assumes "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "\<not> top1_connected_on (UNIV - J)
           (subspace_topology UNIV geotop_euclidean_topology (UNIV - J))"
  sorry

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
  sorry

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

(** from \<S>4: diameter and mesh (geotop.tex:953)
    LATEX VERSION: In a metric space [X,d], the diameter \<delta>M of M is the least upper bound of
      d(P,Q) (P,Q \<in> M). If G is a collection of subsets, the mesh of G is the least upper
      bound of \<delta>g (g \<in> G). **)
definition geotop_diameter :: "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> real" where
  "geotop_diameter d M = (if M = {} then 0 else (SUP P\<in>M. SUP Q\<in>M. d P Q))"

definition geotop_mesh :: "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set set \<Rightarrow> real" where
  "geotop_mesh d G = (if G = {} then 0 else (SUP g\<in>G. geotop_diameter d g))"

(** from \<S>4 Theorem 5 (geotop.tex:976)
    LATEX VERSION: No arc separates R^2. **)
theorem Theorem_GT_4_5:
  fixes A :: "(real^2) set"
  assumes "geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A)"
  shows "top1_connected_on (UNIV - A)
           (subspace_topology UNIV geotop_euclidean_topology (UNIV - A))"
  sorry

(** from \<S>4 Theorem 6 (geotop.tex:996)
    LATEX VERSION: Let J be a 1-sphere in R^2, and let U be a component of R^2 - J. Then J = Fr U. **)
theorem Theorem_GT_4_6:
  fixes J U :: "(real^2) set"
  assumes "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes "\<exists>P\<in>UNIV - J. U = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
  shows "J = geotop_frontier UNIV geotop_euclidean_topology U"
  sorry

(** from \<S>4 Theorem 7 (geotop.tex:1002)
    LATEX VERSION: Let J be a 1-sphere in R^2. Then R^2 - J has only one bounded component. **)
theorem Theorem_GT_4_7:
  fixes J :: "(real^2) set"
  assumes "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "card {C. geotop_bounded_R2 C \<and>
            (\<exists>P\<in>UNIV - J.
               C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)} = 1"
  sorry

(** JORDAN CURVE THEOREM — combining the above
    LATEX VERSION: Let J be a topological 1-sphere in R^2. Then R^2 - J is the union of two
      disjoint connected sets I and E, such that J = Fr I = Fr E. **)
theorem Jordan_curve_theorem:
  fixes J :: "(real^2) set"
  assumes "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "\<exists>I E. UNIV - J = I \<union> E \<and> I \<inter> E = {} \<and>
           top1_connected_on I (subspace_topology UNIV geotop_euclidean_topology I) \<and>
           top1_connected_on E (subspace_topology UNIV geotop_euclidean_topology E) \<and>
           J = geotop_frontier UNIV geotop_euclidean_topology I \<and>
           J = geotop_frontier UNIV geotop_euclidean_topology E"
  sorry

(** from \<S>4 Theorem 8 (geotop.tex:1020)
    LATEX VERSION: Let K be a complex such that M = |K| is a 2-manifold. Then K is a
      combinatorial 2-manifold; i.e., every subcomplex St v is a combinatorial 2-cell. **)
theorem Theorem_GT_4_8:
  fixes K :: "(real^2) set set" and d :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real"
  assumes "geotop_is_complex K"
  assumes "geotop_n_manifold_on (geotop_polyhedron K) d 2"
  shows "\<forall>v\<in>geotop_complex_vertices K. geotop_comb_n_cell (geotop_star K v) 2"
  sorry

(** from \<S>4 Theorem 9 (geotop.tex:1052)
    LATEX VERSION: Let K be a complex such that M = |K| is a 2-manifold with boundary. Then
      K is a combinatorial 2-manifold with boundary, and Bd M is the union of the edges of K
      that lie in only one 2-simplex of K. **)
theorem Theorem_GT_4_9:
  fixes K :: "(real^2) set set" and d :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real"
  assumes "geotop_is_complex K"
  assumes "geotop_n_manifold_with_boundary_on (geotop_polyhedron K) d 2"
  shows "\<forall>v\<in>geotop_complex_vertices K. geotop_comb_n_cell (geotop_star K v) 2"
    and "geotop_manifold_boundary (geotop_polyhedron K) d =
         \<Union>{e\<in>K. geotop_is_edge e \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
  sorry

(** from \<S>4 Theorem 10 (geotop.tex:1058)
    LATEX VERSION: Let M be a 2-manifold with boundary, lying in R^2. If M is closed, then
      Bd M = Fr M. **)
theorem Theorem_GT_4_10:
  fixes M :: "(real^2) set" and d :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real"
  assumes "geotop_n_manifold_with_boundary_on M d 2"
  assumes "closedin_on UNIV geotop_euclidean_topology M"
  shows "geotop_manifold_boundary M d = geotop_frontier UNIV geotop_euclidean_topology M"
  sorry


section \<open>\<S>5 Piecewise linear homeomorphisms\<close>

(** from \<S>5 Theorem 1 (geotop.tex:1118)
    LATEX VERSION: Given K_1 < K. Then f is PL relative to K,L iff f is PL relative to K_1,L. **)
theorem Theorem_GT_5_1:
  fixes K K1 :: "'a::real_normed_vector set set" and L :: "'b::real_normed_vector set set"
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "geotop_is_subdivision K1 K"
  shows "geotop_PL_map K L f \<longleftrightarrow> geotop_PL_map K1 L f"
  sorry

(** from \<S>5 Theorem 2 (geotop.tex:1124)
    LATEX VERSION: Let L_1 be a subdivision of L. f is PL relative to K,L iff f is PL
      relative to K,L_1. **)
theorem Theorem_GT_5_2:
  fixes K :: "'a::real_normed_vector set set" and L L1 :: "'b::real_normed_vector set set"
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "geotop_is_subdivision L1 L"
  shows "geotop_PL_map K L f \<longleftrightarrow> geotop_PL_map K L1 f"
  sorry

(** from \<S>5 Theorem 3 (geotop.tex:1146)
    LATEX VERSION: Let J be a polygon in R^2, let I be its interior, and let K be a
      subcomplex of a triangulation of R^2 such that |K| = \<bar>I\<close>. Then there is a PLH
      f: R^2 \<leftrightarrow> R^2, \<bar>I\<close> \<leftrightarrow> \<sigma>^2, f: J \<leftrightarrow> Bd \<sigma>^2 = Fr \<sigma>^2. Thus K is a combinatorial 2-cell. **)
theorem Theorem_GT_5_3:
  fixes J :: "(real^2) set" and K :: "(real^2) set set"
  assumes "geotop_is_polygon J"
  assumes "geotop_is_complex K"
  assumes "geotop_polyhedron K =
    closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  shows "\<exists>f \<sigma>. geotop_simplex_dim \<sigma> 2 \<and>
          top1_homeomorphism_on UNIV geotop_euclidean_topology
             UNIV geotop_euclidean_topology f \<and>
          f ` geotop_polyhedron K = \<sigma> \<and>
          f ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
    and "geotop_comb_n_cell K 2"
  sorry

(** from \<S>5 Theorem 4 (geotop.tex:1157)
    LATEX VERSION: Let K_1 and K_2 be combinatorial 2-cells and let f be a PLH
      Bd|K_1| \<leftrightarrow> Bd|K_2|. Then f has a PLH extension f': |K_1| \<leftrightarrow> |K_2|. **)
theorem Theorem_GT_5_4:
  fixes K1 K2 :: "'a::real_normed_vector set set"
  fixes f :: "'a \<Rightarrow> 'a" and d :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes "geotop_comb_n_cell K1 2"
  assumes "geotop_comb_n_cell K2 2"
  assumes "geotop_PLH (geotop_comb_boundary K1 2) (geotop_comb_boundary K2 2) f"
  shows "\<exists>f'. geotop_PLH K1 K2 f' \<and>
              (\<forall>x\<in>geotop_polyhedron (geotop_comb_boundary K1 2). f' x = f x)"
  sorry

(** from \<S>5 Theorem 5 (geotop.tex:1174)
    LATEX VERSION: Let K be a complex such that M^2 = |K| is a 2-manifold with boundary.
      Let J be a polygon in |K| which forms a subcomplex of a subdivision. If J lies in a
      set |St v|, then J is the boundary of a combinatorial 2-cell in K. **)
theorem Theorem_GT_5_5:
  fixes K :: "'a::real_normed_vector set set" and J :: "'a set" and v :: "'a"
  fixes d :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes "geotop_is_complex K"
  assumes "geotop_n_manifold_with_boundary_on (geotop_polyhedron K :: 'a set) d 2"
  assumes "geotop_is_polygon J"
  assumes "J \<subseteq> geotop_polyhedron K"
  assumes "v \<in> geotop_complex_vertices K"
  assumes "J \<subseteq> geotop_polyhedron (geotop_star K v)"
  shows "\<exists>K'. K' \<subseteq> K \<and> geotop_comb_n_cell K' 2
          \<and> geotop_polyhedron (geotop_comb_boundary K' 2) = J"
  sorry

(** from \<S>5 Theorem 6 (geotop.tex:1178)
    LATEX VERSION: Let C_1 and C_2 be 2-cells, and let f be a homeomorphism Bd C_1 \<leftrightarrow> Bd C_2.
      Then f has a homeomorphic extension f': C_1 \<leftrightarrow> C_2. **)
theorem Theorem_GT_5_6:
  fixes C1 C2 :: "'a::real_normed_vector set"
  assumes "geotop_is_disk C1 (subspace_topology UNIV geotop_euclidean_topology C1)"
  assumes "geotop_is_disk C2 (subspace_topology UNIV geotop_euclidean_topology C2)"
  assumes "top1_homeomorphism_on
             (geotop_frontier UNIV geotop_euclidean_topology C1)
             (subspace_topology UNIV geotop_euclidean_topology
                (geotop_frontier UNIV geotop_euclidean_topology C1))
             (geotop_frontier UNIV geotop_euclidean_topology C2)
             (subspace_topology UNIV geotop_euclidean_topology
                (geotop_frontier UNIV geotop_euclidean_topology C2))
             f"
  shows "\<exists>f'. top1_homeomorphism_on C1 (subspace_topology UNIV geotop_euclidean_topology C1)
                C2 (subspace_topology UNIV geotop_euclidean_topology C2) f'
          \<and> (\<forall>x\<in>geotop_frontier UNIV geotop_euclidean_topology C1. f' x = f x)"
  sorry

subsection \<open>Joins, barycenters, barycentric subdivision\<close>

(** from Problem Set 5 / \<S>5 additions: join (geotop.tex:1190)
    LATEX VERSION: The join J(A,v) of A and v is the union of all segments vP (P \<in> A).
      More generally, J(A,B) = union of all segments PQ (P \<in> A, Q \<in> B). **)
definition geotop_join_pt :: "'a::real_vector set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "geotop_join_pt A v = (\<Union>P\<in>A. geotop_segment v P)"

definition geotop_join :: "'a::real_vector set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "geotop_join A B = (\<Union>P\<in>A. \<Union>Q\<in>B. geotop_segment P Q)"

(** from Problem Set 5 / \<S>5: barycenter (geotop.tex:1197)
    LATEX VERSION: The barycenter v of \<sigma>^n is the point of \<sigma>^n all of whose barycentric
      coordinates are equal (= 1/(n+1)). **)
definition geotop_barycenter :: "'a::real_vector set \<Rightarrow> 'a" where
  "geotop_barycenter \<sigma> = (SOME v. \<exists>V. geotop_simplex_vertices \<sigma> V \<and>
     v = (\<Sum>w\<in>V. (1 / real (card V)) *\<^sub>R w))"

(** from Problem Set 5 / \<S>5: barycentric subdivision (geotop.tex:1197)
    LATEX VERSION: bK^0 = K^0. bK^{i+1} = bK^i union the set of all joins v\<sigma>^i where v is
      the barycenter of \<sigma>^{i+1} of K, \<sigma>^i \<in> bK^i, \<sigma>^i \<subset> \<sigma>^{i+1}. **)
text \<open>Definition is inductive; we state its existence as a function on complexes.\<close>
definition geotop_barycentric_subdivision ::
  "'a::real_normed_vector set set \<Rightarrow> 'a set set" where
  "geotop_barycentric_subdivision K =
    (SOME bK. geotop_is_subdivision bK K \<and>
       (\<forall>\<sigma>. geotop_simplex_dim \<sigma> 0 \<and> \<sigma> \<in> K \<longrightarrow> \<sigma> \<in> bK))"

(** \<epsilon>-approximation of a mapping (Problem 5.8 and PL approximations \<S>F) (geotop.tex:1201)
    LATEX VERSION: f' is an \<epsilon>-approximation of f if for each P, d(f(P), f'(P)) < \<epsilon>. **)
definition geotop_epsilon_approximation ::
  "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'b set \<Rightarrow> bool" where
  "geotop_epsilon_approximation d f g \<epsilon> X \<longleftrightarrow> (\<forall>P\<in>X. d (f P) (g P) < \<epsilon>)"


section \<open>\<S>6 PL approximations of homeomorphisms\<close>

(** from \<S>6: strongly positive function (geotop.tex:1211)
    LATEX VERSION: Let \<phi>: X \<rightarrow> R^+ be a function (not necessarily continuous). \<phi> is strongly
      positive (written \<phi> >> 0 on X) if \<phi> is bounded away from 0 on every compact set. **)
definition geotop_strongly_positive ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" where
  "geotop_strongly_positive X TX \<phi> \<longleftrightarrow>
    (\<forall>P\<in>X. 0 \<le> \<phi> P) \<and>
    (\<forall>M. M \<subseteq> X \<and> top1_compact_on M (subspace_topology X TX M) \<longrightarrow>
       (\<exists>\<epsilon>>0. \<forall>P\<in>M. \<phi> P \<ge> \<epsilon>))"

(** from \<S>6: \<phi>-approximation (geotop.tex:1217)
    LATEX VERSION: Let \<phi> >> 0 on X, and let f, g be mappings X \<rightarrow> Y. If for each P \<in> X,
      d'(f(P), g(P)) < \<phi>(P), then g is a \<phi>-approximation of f. **)
definition geotop_phi_approximation ::
  "('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_phi_approximation d f g \<phi> X \<longleftrightarrow> (\<forall>P\<in>X. d (f P) (g P) < \<phi> P)"

(** distance between two sets (needed for proof of Theorem 3) (geotop.tex:1342)
    LATEX VERSION: d(A,B) = inf {d(P,Q) | P \<in> A, Q \<in> B}. **)
definition geotop_set_distance ::
  "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> real" where
  "geotop_set_distance d A B = (if A = {} \<or> B = {} then 0 else (INF P\<in>A. INF Q\<in>B. d P Q))"

(** from \<S>6 Theorem 1 (geotop.tex:1219)
    LATEX VERSION: Let vv' be a 1-simplex, let h be a homeomorphism vv' \<leftrightarrow> A \<subset> R^2, with
      v \<mapsto> P, v' \<mapsto> Q, and let \<epsilon> > 0. Then there is a broken line B from P to Q, lying
      in N(A,\<epsilon>). **)
theorem Theorem_GT_6_1:
  fixes e :: "(real^2) set" and A :: "(real^2) set"
  fixes h :: "real^2 \<Rightarrow> real^2" and \<epsilon> :: real
  assumes "geotop_is_edge e"
  assumes "top1_homeomorphism_on e (subspace_topology UNIV geotop_euclidean_topology e)
             A (subspace_topology UNIV geotop_euclidean_topology A) h"
  assumes "\<epsilon> > 0"
  assumes "geotop_simplex_vertices e {v, v'}"
  assumes "P = h v" and "Q = h v'"
  shows "\<exists>B. geotop_is_broken_line B \<and>
          B \<subseteq> geotop_nbhd_set UNIV (\<lambda>x y. norm (x - y)) A \<epsilon>
          \<and> P \<in> B \<and> Q \<in> B"
  sorry

(** from \<S>6 Theorem 2 (geotop.tex:1223)
    LATEX VERSION: Let K^1 be a 1-dimensional complex (not necessarily finite), let h be a
      homeomorphism |K^1| \<rightarrow> R^2, and let \<phi> >> 0 on K^1. Then there is a PLH
      f: |K^1| \<rightarrow> R^2 such that (1) f is a \<phi>-approximation of h, and (2) for each vertex
      v of K^1, h(v) = f(v). **)
theorem Theorem_GT_6_2:
  fixes K1 :: "(real^2) set set" and h :: "real^2 \<Rightarrow> real^2" and \<phi> :: "real^2 \<Rightarrow> real"
  assumes "geotop_is_complex K1"
  assumes "\<forall>\<sigma>\<in>K1. \<exists>i\<le>1. geotop_simplex_dim \<sigma> i"
  assumes "top1_homeomorphism_on (geotop_polyhedron K1)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K1))
             UNIV geotop_euclidean_topology h"
  assumes "geotop_strongly_positive (geotop_polyhedron K1)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K1)) \<phi>"
  shows "\<exists>f. top1_homeomorphism_on (geotop_polyhedron K1)
                (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K1))
                UNIV geotop_euclidean_topology f
          \<and> geotop_PL_map K1 (SOME L. geotop_is_complex L \<and> f ` geotop_polyhedron K1 = geotop_polyhedron L) f
          \<and> geotop_phi_approximation (\<lambda>x y. norm (x - y)) h f \<phi> (geotop_polyhedron K1)
          \<and> (\<forall>v\<in>geotop_complex_vertices K1. h v = f v)"
  sorry

(** from \<S>6 Theorem 3 (geotop.tex:1326)
    LATEX VERSION: Let K be a combinatorial 2-manifold with boundary (not necessarily finite),
      let h be a homeomorphism |K| \<leftrightarrow> M \<subset> R^2, and let \<phi> be a strongly positive function
      |K| \<rightarrow> R. Then there is a PLH f: |K| \<rightarrow> R^2 such that f is a \<phi>-approximation of h. **)
theorem Theorem_GT_6_3:
  fixes K :: "(real^2) set set" and h :: "real^2 \<Rightarrow> real^2" and \<phi> :: "real^2 \<Rightarrow> real"
  fixes M :: "(real^2) set" and d :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real"
  assumes "geotop_is_complex K"
  assumes "geotop_n_manifold_with_boundary_on (geotop_polyhedron K) d 2"
  assumes "top1_homeomorphism_on (geotop_polyhedron K)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))
             M (subspace_topology UNIV geotop_euclidean_topology M) h"
  assumes "geotop_strongly_positive (geotop_polyhedron K)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) \<phi>"
  shows "\<exists>f L. geotop_is_complex L \<and>
          top1_homeomorphism_on (geotop_polyhedron K)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))
             (geotop_polyhedron L)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L)) f
          \<and> geotop_PLH K L f
          \<and> geotop_phi_approximation (\<lambda>x y. norm (x - y)) h f \<phi> (geotop_polyhedron K)"
  sorry

(** from \<S>6 Theorem 4 (geotop.tex:1397)
    LATEX VERSION: Let K_1 be a combinatorial 2-manifold with boundary, let K_2 be a
      combinatorial 2-manifold, let h be a homeomorphism |K_1| \<rightarrow> |K_2|, and let \<phi> >> 0 on K_1.
      Then there is a PLH f: |K_1| \<rightarrow> |K_2| such that f is a \<phi>-approximation of h. **)
theorem Theorem_GT_6_4:
  fixes K1 K2 :: "(real^2) set set"
  fixes h :: "real^2 \<Rightarrow> real^2" and \<phi> :: "real^2 \<Rightarrow> real"
  fixes d1 d2 :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real"
  assumes "geotop_is_complex K1"
  assumes "geotop_is_complex K2"
  assumes "geotop_n_manifold_with_boundary_on (geotop_polyhedron K1) d1 2"
  assumes "geotop_n_manifold_on (geotop_polyhedron K2) d2 2"
  assumes "top1_homeomorphism_on (geotop_polyhedron K1)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K1))
             (geotop_polyhedron K2)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K2)) h"
  assumes "geotop_strongly_positive (geotop_polyhedron K1)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K1)) \<phi>"
  shows "\<exists>f. geotop_PLH K1 K2 f
          \<and> geotop_phi_approximation (\<lambda>x y. norm (x - y)) h f \<phi> (geotop_polyhedron K1)"
  sorry


section \<open>\<S>7 Abstract complexes and PL complexes\<close>

subsection \<open>Abstract complexes\<close>

(** from \<S>7: diagram \<Phi>(K) of a Euclidean complex (geotop.tex:1423)
    LATEX VERSION: The diagram \<Phi>(K) is the set of all sets {v_0,...,v_k} where v_0 v_1 ... v_k \<in> K. **)
definition geotop_diagram :: "'a::real_normed_vector set set \<Rightarrow> 'a set set" where
  "geotop_diagram K = {V. \<exists>\<sigma>\<in>K. geotop_simplex_vertices \<sigma> V}"

(** from \<S>7: abstract complex (geotop.tex:1434)
    LATEX VERSION: A collection \<Phi> is an abstract complex if
      (1) \<Phi> is a collection of nonempty finite sets,
      (2) if \<phi> \<in> \<Phi> and \<phi>' is a nonempty subset of \<phi>, then \<phi>' \<in> \<Phi>,
      (3) every element of \<Phi> intersects only a finite number of elements,
      (4) the union of the elements is countable. **)
definition geotop_is_abstract_complex :: "'a set set \<Rightarrow> bool" where
  "geotop_is_abstract_complex \<Phi> \<longleftrightarrow>
    (\<forall>\<phi>\<in>\<Phi>. finite \<phi> \<and> \<phi> \<noteq> {}) \<and>
    (\<forall>\<phi>\<in>\<Phi>. \<forall>\<phi>'. \<phi>' \<noteq> {} \<and> \<phi>' \<subseteq> \<phi> \<longrightarrow> \<phi>' \<in> \<Phi>) \<and>
    (\<forall>\<phi>\<in>\<Phi>. finite {\<psi>\<in>\<Phi>. \<psi> \<inter> \<phi> \<noteq> {}}) \<and>
    top1_countable (\<Union>\<Phi>)"

(** from \<S>7: finite-dimensional abstract complex (geotop.tex:1434)
    LATEX VERSION: If \<Phi> satisfies (5) There is n such that every element has at most n+1
      elements, then \<Phi> is finite-dimensional, and the least such n is dim \<Phi>. **)
definition geotop_abstract_dim :: "'a set set \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_abstract_dim \<Phi> n \<longleftrightarrow>
    (\<forall>\<phi>\<in>\<Phi>. card \<phi> \<le> n + 1) \<and>
    (\<exists>\<phi>\<in>\<Phi>. card \<phi> = n + 1)"

(** from \<S>7: abstract k-simplex, face (geotop.tex:1434) **)
definition geotop_abstract_simplex :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "geotop_abstract_simplex \<phi> \<Phi> \<longleftrightarrow> \<phi> \<in> \<Phi>"

definition geotop_abstract_simplex_dim :: "'a set \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_abstract_simplex_dim \<phi> k \<longleftrightarrow> card \<phi> = k + 1"

definition geotop_abstract_face :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_abstract_face \<phi>' \<phi> \<longleftrightarrow> \<phi>' \<noteq> {} \<and> \<phi>' \<subseteq> \<phi>"

(** from \<S>7: i-skeleton \<Phi>^i (geotop.tex:1434)
    LATEX VERSION: The i-skeleton \<Phi>^i of \<Phi> is the set of all i-simplexes of \<Phi>
      together with all their faces. **)
definition geotop_abstract_skeleton :: "'a set set \<Rightarrow> nat \<Rightarrow> 'a set set" where
  "geotop_abstract_skeleton \<Phi> i = {\<phi>\<in>\<Phi>. \<exists>k\<le>i. geotop_abstract_simplex_dim \<phi> k}"

(** from \<S>7: isomorphism of abstract complexes (geotop.tex:1436)
    LATEX VERSION: An isomorphism between abstract complexes \<Phi> and \<Psi> is a bijection
      f: \<Phi>^0 \<leftrightarrow> \<Psi>^0 such that \<phi> \<in> \<Phi> iff f(\<phi>) \<in> \<Psi>. **)
definition geotop_abstract_iso :: "'a set set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "geotop_abstract_iso \<Phi> \<Psi> f \<longleftrightarrow>
    bij_betw f (\<Union>\<Phi>) (\<Union>\<Psi>) \<and>
    (\<forall>\<phi>. \<phi> \<subseteq> \<Union>\<Phi> \<and> \<phi> \<noteq> {} \<longrightarrow> (\<phi> \<in> \<Phi> \<longleftrightarrow> f ` \<phi> \<in> \<Psi>))"

(** from \<S>7 Theorem 1 (geotop.tex:1443)
    LATEX VERSION: Let \<Phi> be a finite-dimensional abstract complex with dim \<Phi> \<le> n. Then
      there is a Euclidean complex K in R^{2n+1} such that \<Phi>(K) is isomorphic to \<Phi>. **)
theorem Theorem_GT_7_1:
  fixes \<Phi> :: "'a set set"
  assumes "geotop_is_abstract_complex \<Phi>"
  assumes "geotop_abstract_dim \<Phi> n"
  shows "\<exists>(K::(real^'b::finite) set set) (f::'a \<Rightarrow> real^'b).
           geotop_is_complex K \<and>
           geotop_abstract_iso \<Phi> (geotop_diagram K) f"
  sorry

(** from \<S>7: Euclidean realization (geotop.tex:1473)
    LATEX VERSION: If \<Phi> is an abstract complex and K a Euclidean complex such that \<Phi> and
      \<Phi>(K) are isomorphic, then K is called a Euclidean realization of \<Phi>. **)
definition geotop_euclidean_realization ::
  "'a set set \<Rightarrow> 'b::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_euclidean_realization \<Phi> K \<longleftrightarrow>
    geotop_is_complex K \<and> (\<exists>f. geotop_abstract_iso \<Phi> (geotop_diagram K) f)"

subsection \<open>Coordinate mappings, PL simplexes, PL complexes\<close>

(** from \<S>7: coordinate mapping (geotop.tex:1475)
    LATEX VERSION: Let [X, \<O>] be a topological space, and let h be a homeomorphism of a
      Euclidean simplex into X. h is called a coordinate mapping. **)
definition geotop_coordinate_mapping ::
  "'a::real_normed_vector set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "geotop_coordinate_mapping \<sigma> X TX h \<longleftrightarrow>
    geotop_is_simplex \<sigma> \<and> is_topology_on X TX \<and>
    h ` \<sigma> \<subseteq> X \<and>
    top1_homeomorphism_on \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>)
       (h ` \<sigma>) (subspace_topology X TX (h ` \<sigma>)) h"

(** from \<S>7: equivalence of coordinate mappings (geotop.tex:1510)
    LATEX VERSION: Let g and h be coordinate mappings into X. g \<sim> h if |g| = |h| and
      h^{-1}(g) is a simplicial homeomorphism. **)
definition geotop_coord_equiv ::
  "'a::real_normed_vector set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "geotop_coord_equiv \<sigma>\<^sub>g \<sigma>\<^sub>h g h \<longleftrightarrow>
    g ` \<sigma>\<^sub>g = h ` \<sigma>\<^sub>h \<and>
    (\<exists>\<phi>::'a\<Rightarrow>'a. top1_homeomorphism_on \<sigma>\<^sub>g (subspace_topology UNIV geotop_euclidean_topology \<sigma>\<^sub>g)
                  \<sigma>\<^sub>h (subspace_topology UNIV geotop_euclidean_topology \<sigma>\<^sub>h) \<phi>
         \<and> geotop_simplicial_on \<sigma>\<^sub>g \<phi> \<sigma>\<^sub>h
         \<and> (\<forall>x\<in>\<sigma>\<^sub>g. g x = h (\<phi> x)))"

(** from \<S>7 Theorem 2 (geotop.tex:1520)
    LATEX VERSION: For each [X, \<O>], \<sim> is an equivalence relation on C(X). **)
text \<open>We state this inline as a part of the coordinate equivalence definition; it can be
  formalized as three separate theorems about reflexivity, symmetry, transitivity.\<close>

(** from \<S>7 Theorem 3 (geotop.tex:1523)
    LATEX VERSION: Given g \<sim> h, S \<subset> |g| = |h|. If S forms a face of g, then S forms a face of h. **)
theorem Theorem_GT_7_3:
  fixes \<sigma>\<^sub>g \<sigma>\<^sub>h :: "'a::real_normed_vector set" and g h :: "'a \<Rightarrow> 'b::real_normed_vector"
  fixes S :: "'b set"
  assumes "geotop_coord_equiv \<sigma>\<^sub>g \<sigma>\<^sub>h g h"
  assumes "\<exists>\<tau>. geotop_is_face \<tau> \<sigma>\<^sub>g \<and> S = g ` \<tau>"
  shows "\<exists>\<rho>. geotop_is_face \<rho> \<sigma>\<^sub>h \<and> S = h ` \<rho>"
  sorry

(** from \<S>7 Theorem 4 (geotop.tex:1526)
    LATEX VERSION: Equivalent coordinate mappings induce the same barycentric coordinate
      systems in their common image. **)
text \<open>Stated implicitly: the coordinate-system function depends only on the equivalence class.
  A full Isabelle formalization would introduce a barycentric coordinate function; we omit
  the detail here as it is a consequence of the definitions.\<close>

(** from \<S>7: PL simplex (as equivalence class) (geotop.tex:1547)
    LATEX VERSION: For each h \<in> C(X), [h] = {g | g \<in> C(X) and g \<sim> h}. The [h] are called
      PL simplexes. **)
text \<open>A PL simplex is represented by a pair (domain simplex, coordinate mapping) up to
  equivalence. We use the pair directly in the PL complex definition below.\<close>

definition geotop_PL_simplex_support ::
  "'a::real_normed_vector set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b set" where
  "geotop_PL_simplex_support \<sigma> h = h ` \<sigma>"

definition geotop_PL_simplex_dim ::
  "'a::real_normed_vector set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_PL_simplex_dim \<sigma> h k \<longleftrightarrow> geotop_simplex_dim \<sigma> k"

(** from \<S>7: PL complex in a topological space (geotop.tex:1556)
    LATEX VERSION: A PL complex in [X, \<O>] is a countable collection \<K> of PL simplexes
      satisfying: (K.1) If [h] \<in> \<K>, every face of [h] is in \<K>;
      (K.2) If [g], [h] \<in> \<K> with |[g]| \<inter> |[h]| = S \<noteq> \<emptyset>, there are faces \<tau>_g, \<tau>_h with
        g(\<tau>_g) = h(\<tau>_h) = S and [g|\<tau>_g] = [h|\<tau>_h];
      (K.3) Every |[h]| has a neighborhood intersecting only finitely many |[g]|. **)
text \<open>We represent a PL complex as a set of pairs (domain simplex, coordinate mapping).\<close>
definition geotop_PL_complex ::
  "'b set \<Rightarrow> 'b set set \<Rightarrow> (('a::real_normed_vector set \<times> ('a \<Rightarrow> 'b)) set) \<Rightarrow> bool" where
  "geotop_PL_complex X TX \<K> \<longleftrightarrow>
    is_topology_on X TX \<and>
    top1_countable \<K> \<and>
    (\<forall>(\<sigma>, h)\<in>\<K>. geotop_coordinate_mapping \<sigma> X TX h) \<and>
    (\<forall>(\<sigma>, h)\<in>\<K>. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> (\<tau>, h) \<in> \<K>) \<and>
    (\<forall>(\<sigma>\<^sub>g, g)\<in>\<K>. \<forall>(\<sigma>\<^sub>h, h)\<in>\<K>. g ` \<sigma>\<^sub>g \<inter> h ` \<sigma>\<^sub>h \<noteq> {} \<longrightarrow>
       (\<exists>\<tau>\<^sub>g \<tau>\<^sub>h. geotop_is_face \<tau>\<^sub>g \<sigma>\<^sub>g \<and> geotop_is_face \<tau>\<^sub>h \<sigma>\<^sub>h \<and>
             g ` \<tau>\<^sub>g = h ` \<tau>\<^sub>h \<and> g ` \<tau>\<^sub>g = g ` \<sigma>\<^sub>g \<inter> h ` \<sigma>\<^sub>h \<and>
             geotop_coord_equiv \<tau>\<^sub>g \<tau>\<^sub>h g h)) \<and>
    (\<forall>(\<sigma>, h)\<in>\<K>. \<exists>U\<in>TX. h ` \<sigma> \<subseteq> U \<and>
       finite {(\<sigma>', h')\<in>\<K>. h' ` \<sigma>' \<inter> U \<noteq> {}})"

(** from \<S>7: support of PL complex, i-skeleton, finite-dimensionality (geotop.tex:1563) **)
definition geotop_PL_support ::
  "(('a::real_normed_vector set \<times> ('a \<Rightarrow> 'b)) set) \<Rightarrow> 'b set" where
  "geotop_PL_support \<K> = \<Union>{h ` \<sigma> |\<sigma> h. (\<sigma>, h) \<in> \<K>}"

definition geotop_PL_skeleton ::
  "(('a::real_normed_vector set \<times> ('a \<Rightarrow> 'b)) set) \<Rightarrow> nat \<Rightarrow>
   (('a set \<times> ('a \<Rightarrow> 'b)) set)" where
  "geotop_PL_skeleton \<K> i = {(\<sigma>, h)\<in>\<K>. \<exists>k\<le>i. geotop_simplex_dim \<sigma> k}"

definition geotop_PL_finite_dim ::
  "(('a::real_normed_vector set \<times> ('a \<Rightarrow> 'b)) set) \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_PL_finite_dim \<K> n \<longleftrightarrow>
    (\<forall>(\<sigma>, h)\<in>\<K>. \<exists>k\<le>n. geotop_simplex_dim \<sigma> k) \<and>
    (\<exists>(\<sigma>, h)\<in>\<K>. geotop_simplex_dim \<sigma> n)"

(** from \<S>7 Theorem 5 (geotop.tex:1569)
    LATEX VERSION: Let \<K> be a finite-dimensional PL complex. Then there is a Euclidean
      complex K such that there is a simplicial homeomorphism f: |K| \<leftrightarrow> |\<K>|. **)
theorem Theorem_GT_7_5:
  fixes X :: "'b set" and TX :: "'b set set"
  fixes \<K> :: "(('a::real_normed_vector set) \<times> ('a \<Rightarrow> 'b)) set"
  assumes "geotop_PL_complex X TX \<K>"
  assumes "geotop_PL_finite_dim \<K> n"
  shows "\<exists>(K::'a set set) (f::'a \<Rightarrow> 'b).
           geotop_is_complex K \<and>
           top1_homeomorphism_on (geotop_polyhedron K)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))
             (geotop_PL_support \<K>) (subspace_topology X TX (geotop_PL_support \<K>)) f
         \<and> \<K> = {(\<sigma>, \<lambda>x\<in>\<sigma>. f x) |\<sigma>. \<sigma> \<in> K}"
  sorry

(** from \<S>7 Theorem 6 (geotop.tex:1593)
    LATEX VERSION: Let \<K>_1 and \<K>_2 be PL complexes in the same space [X, \<O>]. Suppose that
      if [g] \<in> \<K>_1, [h] \<in> \<K>_2, and S = |[g]| \<inter> |[h]| \<noteq> \<emptyset>, there are faces \<tau>_g, \<tau>_h with
      g(\<tau>_g) = h(\<tau>_h) = S and [g|\<tau>_g] = [h|\<tau>_h]. Then \<K>_1 \<union> \<K>_2 is a PL complex. **)
theorem Theorem_GT_7_6:
  fixes X :: "'b set" and TX :: "'b set set"
  fixes \<K>\<^sub>1 \<K>\<^sub>2 :: "(('a::real_normed_vector set) \<times> ('a \<Rightarrow> 'b)) set"
  assumes "geotop_PL_complex X TX \<K>\<^sub>1"
  assumes "geotop_PL_complex X TX \<K>\<^sub>2"
  assumes "\<forall>(\<sigma>\<^sub>g, g)\<in>\<K>\<^sub>1. \<forall>(\<sigma>\<^sub>h, h)\<in>\<K>\<^sub>2. g ` \<sigma>\<^sub>g \<inter> h ` \<sigma>\<^sub>h \<noteq> {} \<longrightarrow>
             (\<exists>\<tau>\<^sub>g \<tau>\<^sub>h. geotop_is_face \<tau>\<^sub>g \<sigma>\<^sub>g \<and> geotop_is_face \<tau>\<^sub>h \<sigma>\<^sub>h \<and>
                 g ` \<tau>\<^sub>g = h ` \<tau>\<^sub>h \<and> g ` \<tau>\<^sub>g = g ` \<sigma>\<^sub>g \<inter> h ` \<sigma>\<^sub>h \<and>
                 geotop_coord_equiv \<tau>\<^sub>g \<tau>\<^sub>h g h)"
  shows "geotop_PL_complex X TX (\<K>\<^sub>1 \<union> \<K>\<^sub>2)"
  sorry

(** from \<S>7: PL star (geotop.tex:1596)
    LATEX VERSION: In a PL complex \<K>, for each vertex v, St v is the set of all elements [h]
      of \<K> such that |[h]| contains v, together with all faces. **)
definition geotop_PL_star ::
  "(('a::real_normed_vector set \<times> ('a \<Rightarrow> 'b)) set) \<Rightarrow> 'b \<Rightarrow>
   (('a set \<times> ('a \<Rightarrow> 'b)) set)" where
  "geotop_PL_star \<K> v =
    {(\<tau>, h')\<in>\<K>. \<exists>\<sigma> h. (\<sigma>, h)\<in>\<K> \<and> v \<in> h ` \<sigma> \<and> (geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>)}"


section \<open>\<S>8 The triangulation theorem for 2-manifolds\<close>

(** from \<S>8: unit balls D and D' (geotop.tex:1615)
    LATEX VERSION: D = {P | ||P|| < 1}, D' = {P | ||P|| < 1/2}. **)
definition geotop_std_open_ball :: "real \<Rightarrow> 'a::real_normed_vector set" where
  "geotop_std_open_ball r = {P. norm P < r}"

abbreviation geotop_D :: "'a::real_normed_vector set" where
  "geotop_D \<equiv> geotop_std_open_ball 1"

abbreviation geotop_D' :: "'a::real_normed_vector set" where
  "geotop_D' \<equiv> geotop_std_open_ball (1/2)"

(** from \<S>8 Theorem 1 (geotop.tex:1622)
    LATEX VERSION: Let M be an n-manifold. Then there is a sequence (N_i, N_i') of ordered
      pairs of open sets in M, such that for each i there is a homeomorphism
      h_i: \<bar>N_i\<close> \<leftrightarrow> \<bar>D\<close>, \<bar>N_i'\<close> \<leftrightarrow> \<bar>D'\<close>, and {N_i'} covers M. **)
theorem Theorem_GT_8_1:
  fixes M :: "'a::real_normed_vector set" and d :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes "geotop_n_manifold_on M d n"
  shows "\<exists>(N :: nat \<Rightarrow> 'a set) (N' :: nat \<Rightarrow> 'a set) (h :: nat \<Rightarrow> 'a \<Rightarrow> 'a).
    (\<forall>i. openin_on M (top1_metric_topology_on M d) (N i) \<and>
         openin_on M (top1_metric_topology_on M d) (N' i) \<and>
         top1_homeomorphism_on
           (closure_on M (top1_metric_topology_on M d) (N i))
           (subspace_topology M (top1_metric_topology_on M d)
               (closure_on M (top1_metric_topology_on M d) (N i)))
           (closure_on UNIV geotop_euclidean_topology (geotop_std_open_ball 1))
           (subspace_topology UNIV geotop_euclidean_topology
               (closure_on UNIV geotop_euclidean_topology (geotop_std_open_ball 1)))
           (h i) \<and>
         h i ` closure_on M (top1_metric_topology_on M d) (N' i) =
            closure_on UNIV geotop_euclidean_topology (geotop_std_open_ball (1/2)))
    \<and> M = (\<Union>i. N' i)"
  sorry

(** from \<S>8 Theorem 2 (geotop.tex:1639)
    LATEX VERSION: Let K be a finite complex, and let U be an open set in |K| (relative to the
      subspace topology for |K|). Then there is a complex K_U such that |K_U| = U and every
      simplex \<sigma> of K_U is a (rectilinear) subsimplex of some simplex of K. **)
theorem Theorem_GT_8_2:
  fixes K :: "'a::real_normed_vector set set" and U :: "'a set"
  assumes "geotop_is_complex K"
  assumes "finite K"
  assumes "U \<in> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
  shows "\<exists>KU. geotop_is_complex KU \<and> geotop_polyhedron KU = U \<and>
           (\<forall>\<sigma>\<in>KU. \<exists>\<tau>\<in>K. \<sigma> \<subseteq> \<tau>)"
  sorry

(** from \<S>8 Theorem 3 (T. Radó) (geotop.tex:1674)
    LATEX VERSION: Every 2-manifold is triangulable, i.e., there is a (Euclidean) complex K
      such that M and |K| are homeomorphic; equivalently, there is a PL complex \<K> in M with
      |\<K>| = M. **)
theorem Theorem_GT_8_3_Rado:
  fixes M :: "'a::real_normed_vector set" and d :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes "geotop_n_manifold_on M d 2"
  shows "\<exists>(K :: (real^2) set set) (f :: real^2 \<Rightarrow> 'a).
    geotop_is_complex K \<and>
    top1_homeomorphism_on (geotop_polyhedron K)
        (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))
        M (top1_metric_topology_on M d) f"
  sorry

(** from \<S>8 Theorem 4 (geotop.tex:1826)
    LATEX VERSION: Let K_1 and K_2 be triangulated 2-manifolds, let U be an open set in |K_1|,
      let h be a homeomorphism U \<rightarrow> |K_2|, and let \<phi> be strongly positive on U. Then there is
      a PLH f: U \<rightarrow> |K_2| such that f is a \<phi>-approximation of h and f(U) = h(U). **)
theorem Theorem_GT_8_4:
  fixes K1 K2 :: "(real^2) set set"
  fixes h :: "real^2 \<Rightarrow> real^2" and \<phi> :: "real^2 \<Rightarrow> real"
  fixes d1 d2 :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real"
  fixes U :: "(real^2) set"
  assumes "geotop_is_complex K1"
  assumes "geotop_is_complex K2"
  assumes "geotop_n_manifold_on (geotop_polyhedron K1) d1 2"
  assumes "geotop_n_manifold_on (geotop_polyhedron K2) d2 2"
  assumes "U \<in> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K1)"
  assumes "top1_homeomorphism_on U (subspace_topology UNIV geotop_euclidean_topology U)
             (h ` U) (subspace_topology UNIV geotop_euclidean_topology (h ` U)) h"
  assumes "h ` U \<subseteq> geotop_polyhedron K2"
  assumes "geotop_strongly_positive U
             (subspace_topology UNIV geotop_euclidean_topology U) \<phi>"
  shows "\<exists>f. top1_homeomorphism_on U (subspace_topology UNIV geotop_euclidean_topology U)
               (f ` U) (subspace_topology UNIV geotop_euclidean_topology (f ` U)) f
          \<and> f ` U = h ` U
          \<and> geotop_phi_approximation (\<lambda>x y. norm (x - y)) h f \<phi> U
          \<and> (\<exists>KU. geotop_is_complex KU \<and> geotop_polyhedron KU = U \<and> geotop_PL_map KU K2 f)"
  sorry

(** from \<S>8 Theorem 5 (Hauptvermutung for 2-manifolds) (geotop.tex:1844)
    LATEX VERSION: Let K_1 and K_2 be triangulated 2-manifolds. If there is a homeomorphism
      |K_1| \<leftrightarrow> |K_2|, then there is a PLH |K_1| \<leftrightarrow> |K_2|. Thus, for triangulated 2-manifolds,
      homeomorphism implies combinatorial equivalence. **)
theorem Theorem_GT_8_5_Hauptvermutung_2d:
  fixes K1 K2 :: "(real^2) set set"
  fixes d1 d2 :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real"
  fixes h :: "real^2 \<Rightarrow> real^2"
  assumes "geotop_is_complex K1"
  assumes "geotop_is_complex K2"
  assumes "geotop_n_manifold_on (geotop_polyhedron K1) d1 2"
  assumes "geotop_n_manifold_on (geotop_polyhedron K2) d2 2"
  assumes "top1_homeomorphism_on (geotop_polyhedron K1)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K1))
             (geotop_polyhedron K2)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K2)) h"
  shows "\<exists>f. geotop_PLH K1 K2 f"
    and "geotop_comb_equiv K1 K2"
  sorry

end
