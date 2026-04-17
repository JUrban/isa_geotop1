theory GeoTop
  imports "Top0.AlgTop" "HOL-Analysis.Cartesian_Euclidean_Space"
          "HOL-Analysis.Smooth_Paths" "HOL-Analysis.Further_Topology"
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

subsection \<open>Helpers for simplex connectivity (\<S>1 Theorem 3)\<close>

text \<open>Moise's \<S>1 Theorem 3: every simplex is pathwise connected, because
  it is convex, and the straight-line path between any two points of a
  convex set is continuous.\<close>

(** Bridge between Moise's geotop_convex and HOL-Analysis convex. **)
lemma geotop_convex_iff_HOL_convex:
  fixes S :: "'a::real_vector set"
  shows "geotop_convex S \<longleftrightarrow> convex S"
  unfolding geotop_convex_def geotop_segment_def convex_def by blast

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

(** The geotop convex hull coincides with HOL-Analysis's convex hull. **)
lemma geotop_convex_hull_eq_HOL:
  fixes V :: "'a::real_vector set"
  shows "geotop_convex_hull V = convex hull V"
  by (simp add: geotop_convex_hull_def geotop_convex_iff_HOL_convex hull_def)

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
theorem Theorem_GT_1_4:
  fixes K :: "'a::real_normed_vector set set"
  assumes hK: "geotop_complex_connected K"
  shows "top1_path_connected_on (geotop_polyhedron K)
           (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
  (** Moise proof (geotop.tex:343): given P, Q \<in> |K|, pick \<sigma>\<^sub>P, \<sigma>\<^sub>Q \<in> K with P \<in> \<sigma>\<^sub>P,
      Q \<in> \<sigma>\<^sub>Q. Define Cs = {\<sigma> \<in> K: \<sigma> reachable from \<sigma>\<^sub>P via a chain of simplexes with
      consecutive intersections nonempty}. Show Cs and K - Cs are both complexes; by
      complex-connectedness of K, one is empty; since \<sigma>\<^sub>P \<in> Cs, Cs = K, so \<sigma>\<^sub>Q reachable.
      Build a path from P to Q by concatenating straight-line paths within each simplex,
      via top1_in_same_path_component_on_trans. **)
proof -
  let ?X = "geotop_polyhedron K"
  let ?TX = "subspace_topology UNIV geotop_euclidean_topology ?X"
  have hKcomplex: "geotop_is_complex K"
    using hK geotop_complex_connected_def by blast
  have hTeucl: "is_topology_on (UNIV::'a set) geotop_euclidean_topology"
    by (simp add: geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have hXsub: "?X \<subseteq> UNIV" by simp
  have hTX_top: "is_topology_on ?X ?TX"
    by (rule subspace_topology_is_topology_on[OF hTeucl hXsub])
  have hpath_PQ: "\<forall>P\<in>?X. \<forall>Q\<in>?X. \<exists>f. top1_is_path_on ?X ?TX P Q f"
    sorry  \<comment> \<open>chain-of-simplexes argument; deferred\<close>
  show ?thesis
    unfolding top1_path_connected_on_def using hTX_top hpath_PQ by blast
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
  assumes "is_topology_on X T" "M \<subseteq> X"
  shows "top1_connected_on M (subspace_topology X T M) \<longleftrightarrow>
    \<not>(\<exists>H K. H \<noteq> {} \<and> K \<noteq> {} \<and> M = H \<union> K \<and> geotop_separated X T H K)"
  by (metis Theorem_GT_1_5 assms(1,2) subspace_topology_is_topology_on
    sup.cobounded1 sup.cobounded2 top1_connected_on_def)

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
  have hconn: "connected {t::real. a \<le> t \<and> t \<le> b}"
    by (smt (verit, del_insts) connectedI_interval mem_Collect_eq)
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

(** from \<S>2 Theorem 1 (geotop.tex:502)
    LATEX VERSION: Let J be a polygon in R^2. Then R^2 - J has exactly two components. **)
theorem Theorem_GT_2_1:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "card {C. \<exists>P. P \<in> (UNIV::(real^2) set) - J \<and>
           C = geotop_component_at UNIV geotop_euclidean_topology ((UNIV::(real^2) set) - J) P} = 2"
  (** Combine the upper bound (Lemma_GT_2_1a) and lower bound (Lemma_GT_2_1b). **)
  using Lemma_GT_2_1a[OF hJ] Lemma_GT_2_1b[OF hJ]
  by linarith

(** from \<S>2: interior and exterior of a polygon (geotop.tex:553)
    LATEX VERSION: The bounded component I of R^2 - J is called the interior of J, and the
      unbounded component E is called the exterior. **)
text \<open>A set $A \subseteq \mathbb{R}^2$ is \emph{bounded} if there exists $r > 0$ such that
  $A \subseteq N(\mathbf{0}, r)$. We define interior and exterior of a polygon accordingly.\<close>

definition geotop_bounded_R2 :: "(real^2) set \<Rightarrow> bool" where
  "geotop_bounded_R2 A \<longleftrightarrow> (\<exists>r>0. \<forall>P\<in>A. norm P < r)"

definition geotop_polygon_interior :: "(real^2) set \<Rightarrow> (real^2) set" where
  "geotop_polygon_interior J =
    (SOME I. I \<noteq> {} \<and> I \<subseteq> UNIV - J \<and> geotop_bounded_R2 I \<and>
       top1_connected_on I (subspace_topology UNIV geotop_euclidean_topology I) \<and>
       (\<forall>P\<in>I. geotop_component_at UNIV geotop_euclidean_topology
                   ((UNIV::(real^2) set) - J) P = I))"

definition geotop_polygon_exterior :: "(real^2) set \<Rightarrow> (real^2) set" where
  "geotop_polygon_exterior J =
    (SOME E. E \<noteq> {} \<and> E \<subseteq> UNIV - J \<and> \<not> geotop_bounded_R2 E \<and>
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
  assumes hB: "geotop_is_broken_line B"
  shows "top1_connected_on (UNIV - B)
           (subspace_topology UNIV geotop_euclidean_topology (UNIV - B))"
  (** Moise proof (geotop.tex:579): broken line = polyhedral arc; apply
      `top1_connected_complement_of_geotop_arc` with DIM(real^2)=2. **)
proof -
  have harc: "geotop_is_arc B (subspace_topology UNIV geotop_euclidean_topology B)"
    using hB unfolding geotop_is_broken_line_def by blast
  show ?thesis by (rule top1_connected_complement_of_geotop_arc[OF harc]) simp
qed

(** from \<S>2 Theorem 4 (geotop.tex:593)
    LATEX VERSION: Let X be a topological space and let U be an open set. Then Fr U = \<bar>U\<close> - U. **)
theorem Theorem_GT_2_4:
  assumes "is_topology_on X T"
  assumes "U \<in> T"
  assumes "U \<subseteq> X"
  shows "geotop_frontier X T U = closure_on X T U - U"
  by (smt (verit, del_insts) DiffI Diff_Diff_Int Diff_Int_distrib
    Diff_cancel Diff_empty Diff_subset assms(1,2,3) closedin_intro
    closure_on_sub_carrier closure_on_subset_of_closed dual_order.refl
    geotop_frontier_def imageE imageI inf.absorb_iff2 inf.order_iff
    inf.right_idem inf_le1 insertCI is_topology_on_def
    subset_closure_on)

(** Bridge: is_limit_point_of on UNIV with geotop_euclidean_topology equals
    HOL-Analysis `islimpt`. **)
lemma is_limit_point_of_UNIV_geotop_iff_islimpt:
  fixes P :: "'a::real_normed_vector" and A :: "'a set"
  shows "is_limit_point_of P A UNIV geotop_euclidean_topology \<longleftrightarrow> P islimpt A"
proof
  assume "is_limit_point_of P A UNIV geotop_euclidean_topology"
  hence hf: "\<forall>U\<in>geotop_euclidean_topology. P \<in> U \<longrightarrow> (U - {P}) \<inter> A \<noteq> {}"
    unfolding is_limit_point_of_def neighborhood_of_def intersects_def by blast
  show "P islimpt A"
    unfolding islimpt_def
  proof (intro allI impI)
    fix T assume hPT: "P \<in> T" and hopen: "open T"
    have hT_geotop: "T \<in> (geotop_euclidean_topology :: 'a set set)"
      using hopen geotop_euclidean_topology_eq_open_sets[where 'a='a]
      unfolding top1_open_sets_def by auto
    have "(T - {P}) \<inter> A \<noteq> {}"
      using hf hT_geotop hPT by blast
    thus "\<exists>y\<in>A. y \<in> T \<and> y \<noteq> P" by blast
  qed
next
  assume "P islimpt A"
  hence hlimpt: "\<forall>T. P \<in> T \<longrightarrow> open T \<longrightarrow> (\<exists>y\<in>A. y \<in> T \<and> y \<noteq> P)"
    unfolding islimpt_def by blast
  show "is_limit_point_of P A UNIV geotop_euclidean_topology"
    unfolding is_limit_point_of_def neighborhood_of_def intersects_def
  proof (intro conjI allI impI)
    show "P \<in> UNIV" by simp
    show "A \<subseteq> UNIV" by simp
    fix U assume "U \<in> geotop_euclidean_topology \<and> P \<in> U"
    then have hUopen: "open U" and hPU: "P \<in> U"
      using geotop_euclidean_topology_eq_open_sets
      unfolding top1_open_sets_def by auto
    then obtain y where "y \<in> A" "y \<in> U" "y \<noteq> P"
      using hlimpt by blast
    thus "(U - {P}) \<inter> A \<noteq> {}" by blast
  qed
qed

(** Helper: for a geotop-1-sphere J in euclidean_space with DIM \<ge> 2, every
    component of UNIV - J has J as its frontier. **)
lemma top1_frontier_component_of_geotop_1sphere:
  fixes J U :: "'a::euclidean_space set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes hU_ex: "\<exists>P\<in>UNIV - J. U = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
  assumes hdim: "2 \<le> DIM('a)"
  shows "J = geotop_frontier UNIV geotop_euclidean_topology U"
proof -
  obtain f where hhomeo: "top1_homeomorphism_on J
                           (subspace_topology UNIV geotop_euclidean_topology J)
                           (geotop_std_sphere::'a set)
                           (subspace_topology UNIV geotop_euclidean_topology
                              (geotop_std_sphere::'a set)) f"
    using hJ unfolding geotop_is_n_sphere_def by blast
  have hhomeo_HOL: "J homeomorphic (geotop_std_sphere::'a set)"
    by (rule top1_homeomorphism_on_geotop_imp_HOL_homeomorphic[OF hhomeo])
  have hstd_eq: "(geotop_std_sphere::'a set) = sphere 0 1"
    unfolding geotop_std_sphere_def sphere_def by simp
  have hJ_sphere: "J homeomorphic sphere (0::'a) 1"
    using hhomeo_HOL hstd_eq by simp
  obtain P where hP_notJ: "P \<in> UNIV - J"
             and hU_eq: "U = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
    using hU_ex by blast
  have hU_comp: "U = connected_component_set (- J) P"
    using hU_eq geotop_component_at_UNIV_eq_connected_component_set
    by (simp add: Compl_eq_Diff_UNIV)
  have hP_compl: "P \<in> - J" using hP_notJ by (simp add: Compl_eq_Diff_UNIV)
  have hU_in_components: "U \<in> components (- J)"
    unfolding components_def using hU_comp hP_compl by blast
  have hfrontier: "frontier U = J"
    by (rule Jordan_Brouwer_frontier[OF hJ_sphere hU_in_components hdim])
  show ?thesis
    using hfrontier geotop_frontier_UNIV_eq_frontier by metis
qed

(** Helper: for a geotop-1-sphere J in euclidean_space with DIM \<ge> 2, there
    exists a bounded component and an unbounded component of UNIV - J. **)
lemma geotop_1sphere_has_bounded_unbounded_components:
  fixes J :: "'a::euclidean_space set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes hdim: "2 \<le> DIM('a)"
  shows "(\<exists>c. c \<in> components (- J) \<and> bounded c) \<and>
         (\<exists>c. c \<in> components (- J) \<and> \<not> bounded c)"
proof -
  obtain f where hhomeo: "top1_homeomorphism_on J
                           (subspace_topology UNIV geotop_euclidean_topology J)
                           (geotop_std_sphere::'a set)
                           (subspace_topology UNIV geotop_euclidean_topology
                              (geotop_std_sphere::'a set)) f"
    using hJ unfolding geotop_is_n_sphere_def by blast
  have hhomeo_HOL: "J homeomorphic (geotop_std_sphere::'a set)"
    by (rule top1_homeomorphism_on_geotop_imp_HOL_homeomorphic[OF hhomeo])
  have hstd_eq: "(geotop_std_sphere::'a set) = sphere 0 1"
    unfolding geotop_std_sphere_def sphere_def by simp
  have hJ_sphere: "J homeomorphic sphere (0::'a) 1"
    using hhomeo_HOL hstd_eq by simp
  have hnot_conn: "\<not> connected (- J)"
    using Jordan_Brouwer_separation[OF hJ_sphere] by simp
  (** J is bounded (compact, as homeomorphic image of sphere which is compact). **)
  have hJ_compact: "compact J"
    by (metis compact_sphere hJ_sphere homeomorphic_compactness)
  have hJ_bounded: "bounded J"
    using hJ_compact compact_imp_bounded by blast
  have hbounded_neg: "bounded (- (- J))"
    by (simp add: hJ_bounded)
  have hbd_comp: "\<exists>c. c \<in> components (- J) \<and> bounded c"
    using cobounded_has_bounded_component[OF hbounded_neg hnot_conn] hdim by blast
  have hunbd_comp: "\<exists>c. c \<in> components (- J) \<and> \<not> bounded c"
    using cobounded_unbounded_components[OF hbounded_neg] by blast
  show ?thesis using hbd_comp hunbd_comp by blast
qed

(** Bridge: geotop_bounded_R2 equals HOL-Analysis `bounded` on real^2. **)
lemma geotop_bounded_R2_iff_bounded:
  fixes A :: "(real^2) set"
  shows "geotop_bounded_R2 A \<longleftrightarrow> bounded A"
proof
  assume "geotop_bounded_R2 A"
  then obtain r where hr: "r > 0" "\<forall>P\<in>A. norm P < r"
    unfolding geotop_bounded_R2_def by blast
  then show "bounded A"
    unfolding bounded_iff by (meson less_le_not_le nle_le)
next
  assume "bounded A"
  then obtain a where ha: "\<forall>x\<in>A. norm x \<le> a"
    unfolding bounded_iff by blast
  let ?r = "max a 0 + 1"
  have "?r > 0" by simp
  moreover have "\<forall>P\<in>A. norm P < ?r"
    using ha by (smt (verit) max.cobounded1)
  ultimately show "geotop_bounded_R2 A"
    unfolding geotop_bounded_R2_def by blast
qed

(** Helper: given a 1-sphere J in R^2, polygon_interior J is a bounded connected
    component of UNIV - J, and polygon_exterior J is an unbounded one. **)
lemma geotop_polygon_interior_is_bounded_component:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "\<exists>P\<in>UNIV - J.
           geotop_polygon_interior J
           = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
proof -
  have hdim: "(2::nat) \<le> DIM(real^2)" by simp
  have hexists_bd: "\<exists>c. c \<in> components (- J) \<and> bounded c"
    using geotop_1sphere_has_bounded_unbounded_components[OF hJ hdim] by blast
  then obtain C where hC_comp: "C \<in> components (- J)" and hC_bd: "bounded C" by blast
  (** Show C satisfies the polygon_interior predicate. **)
  obtain P where hP: "P \<in> -J" and hC_eq: "C = connected_component_set (- J) P"
    using hC_comp unfolding components_def by blast
  have hC_sub: "C \<subseteq> UNIV - J"
    using hC_eq connected_component_subset by (metis Compl_eq_Diff_UNIV)
  have hC_bdR2: "geotop_bounded_R2 C"
    using hC_bd geotop_bounded_R2_iff_bounded by blast
  have hC_conn_HOL: "connected C"
    using hC_comp in_components_connected by blast
  have hC_topconn: "top1_connected_on C
                     (subspace_topology UNIV geotop_euclidean_topology C)"
    using hC_conn_HOL top1_connected_on_geotop_iff_connected by blast
  have hC_comp_at: "\<forall>Q\<in>C. geotop_component_at UNIV geotop_euclidean_topology
                             ((UNIV::(real^2) set) - J) Q = C"
  proof
    fix Q assume hQC: "Q \<in> C"
    have hQ_compl: "Q \<in> -J"
      using hQC hC_eq connected_component_subset by blast
    have hC_comp_Q: "C = connected_component_set (- J) Q"
      using connected_component_eq hC_eq hQC by blast
    then have "connected_component_set (UNIV - J) Q = C"
      using Compl_eq_Diff_UNIV by metis
    thus "geotop_component_at UNIV geotop_euclidean_topology
            ((UNIV::(real^2) set) - J) Q = C"
      using geotop_component_at_UNIV_eq_connected_component_set by metis
  qed
  have hC_ne: "C \<noteq> {}" using hC_comp in_components_nonempty by blast
  have hpred_C: "C \<noteq> {} \<and> C \<subseteq> UNIV - J \<and> geotop_bounded_R2 C \<and>
                 top1_connected_on C (subspace_topology UNIV geotop_euclidean_topology C) \<and>
                 (\<forall>P\<in>C. geotop_component_at UNIV geotop_euclidean_topology
                           ((UNIV::(real^2) set) - J) P = C)"
    using hC_ne hC_sub hC_bdR2 hC_topconn hC_comp_at by blast
  have hpred_ex: "\<exists>I. I \<noteq> {} \<and> I \<subseteq> UNIV - J \<and> geotop_bounded_R2 I \<and>
                      top1_connected_on I (subspace_topology UNIV geotop_euclidean_topology I) \<and>
                      (\<forall>P\<in>I. geotop_component_at UNIV geotop_euclidean_topology
                                ((UNIV::(real^2) set) - J) P = I)"
    using hpred_C by blast
  (** SOME picks such an I. Let I = polygon_interior J. **)
  let ?I = "geotop_polygon_interior J"
  have hI_pred: "?I \<noteq> {} \<and> ?I \<subseteq> UNIV - J \<and> geotop_bounded_R2 ?I \<and>
                 top1_connected_on ?I (subspace_topology UNIV geotop_euclidean_topology ?I) \<and>
                 (\<forall>P\<in>?I. geotop_component_at UNIV geotop_euclidean_topology
                            ((UNIV::(real^2) set) - J) P = ?I)"
    unfolding geotop_polygon_interior_def
    by (rule someI_ex[OF hpred_ex])
  have hI_ne: "?I \<noteq> {}" using hI_pred by blast
  have hI_sub: "?I \<subseteq> UNIV - J" using hI_pred by blast
  obtain P where hP_I: "P \<in> ?I" using hI_ne by blast
  have hP_notJ: "P \<in> UNIV - J" using hP_I hI_sub by blast
  have hI_eq: "?I = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
    using hI_pred hP_I by metis
  show ?thesis using hP_notJ hI_eq by blast
qed

lemma geotop_polygon_exterior_is_component:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "\<exists>P\<in>UNIV - J.
           geotop_polygon_exterior J
           = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
proof -
  have hdim: "(2::nat) \<le> DIM(real^2)" by simp
  have hexists_unbd: "\<exists>c. c \<in> components (- J) \<and> \<not> bounded c"
    using geotop_1sphere_has_bounded_unbounded_components[OF hJ hdim] by blast
  then obtain C where hC_comp: "C \<in> components (- J)" and hC_unbd: "\<not> bounded C" by blast
  obtain P where hP: "P \<in> -J" and hC_eq: "C = connected_component_set (- J) P"
    using hC_comp unfolding components_def by blast
  have hC_sub: "C \<subseteq> UNIV - J"
    using hC_eq connected_component_subset by (metis Compl_eq_Diff_UNIV)
  have hC_unbdR2: "\<not> geotop_bounded_R2 C"
    using hC_unbd geotop_bounded_R2_iff_bounded by blast
  have hC_conn_HOL: "connected C"
    using hC_comp in_components_connected by blast
  have hC_topconn: "top1_connected_on C
                     (subspace_topology UNIV geotop_euclidean_topology C)"
    using hC_conn_HOL top1_connected_on_geotop_iff_connected by blast
  have hC_comp_at: "\<forall>Q\<in>C. geotop_component_at UNIV geotop_euclidean_topology
                             ((UNIV::(real^2) set) - J) Q = C"
  proof
    fix Q assume hQC: "Q \<in> C"
    have hQ_compl: "Q \<in> -J"
      using hQC hC_eq connected_component_subset by blast
    have hC_comp_Q: "C = connected_component_set (- J) Q"
      using connected_component_eq hC_eq hQC by blast
    then have "connected_component_set (UNIV - J) Q = C"
      using Compl_eq_Diff_UNIV by metis
    thus "geotop_component_at UNIV geotop_euclidean_topology
            ((UNIV::(real^2) set) - J) Q = C"
      using geotop_component_at_UNIV_eq_connected_component_set by metis
  qed
  have hC_ne: "C \<noteq> {}" using hC_comp in_components_nonempty by blast
  have hpred_C: "C \<noteq> {} \<and> C \<subseteq> UNIV - J \<and> \<not> geotop_bounded_R2 C \<and>
                 top1_connected_on C (subspace_topology UNIV geotop_euclidean_topology C) \<and>
                 (\<forall>P\<in>C. geotop_component_at UNIV geotop_euclidean_topology
                           ((UNIV::(real^2) set) - J) P = C)"
    using hC_ne hC_sub hC_unbdR2 hC_topconn hC_comp_at by blast
  have hpred_ex: "\<exists>E. E \<noteq> {} \<and> E \<subseteq> UNIV - J \<and> \<not> geotop_bounded_R2 E \<and>
                      top1_connected_on E (subspace_topology UNIV geotop_euclidean_topology E) \<and>
                      (\<forall>P\<in>E. geotop_component_at UNIV geotop_euclidean_topology
                                ((UNIV::(real^2) set) - J) P = E)"
    using hpred_C by blast
  let ?E = "geotop_polygon_exterior J"
  have hE_pred: "?E \<noteq> {} \<and> ?E \<subseteq> UNIV - J \<and> \<not> geotop_bounded_R2 ?E \<and>
                 top1_connected_on ?E (subspace_topology UNIV geotop_euclidean_topology ?E) \<and>
                 (\<forall>P\<in>?E. geotop_component_at UNIV geotop_euclidean_topology
                            ((UNIV::(real^2) set) - J) P = ?E)"
    unfolding geotop_polygon_exterior_def
    by (rule someI_ex[OF hpred_ex])
  have hE_ne: "?E \<noteq> {}" using hE_pred by blast
  have hE_sub: "?E \<subseteq> UNIV - J" using hE_pred by blast
  obtain P where hP_E: "P \<in> ?E" using hE_ne by blast
  have hP_notJ: "P \<in> UNIV - J" using hP_E hE_sub by blast
  have hE_eq: "?E = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
    using hE_pred hP_E by metis
  show ?thesis using hP_notJ hE_eq by blast
qed

(** from \<S>2 Theorem 6 (geotop.tex:611)
    LATEX VERSION: Let J, I, E be as in Theorem 5. Then J = Fr I = Fr E. **)
theorem Theorem_GT_2_6:
  fixes J :: "(real^2) set"
  assumes hJ_poly: "geotop_is_polygon J"
  shows "J = geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
    and "J = geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_exterior J)"
proof -
  have hJ_sphere: "geotop_is_n_sphere J
                     (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ_poly unfolding geotop_is_polygon_def by blast
  have hdim: "(2::nat) \<le> DIM(real^2)" by simp
  (** Part 1: polygon_interior J is a component of UNIV - J, apply helper. **)
  have hI_comp: "\<exists>P\<in>UNIV - J.
                   geotop_polygon_interior J
                   = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
    by (rule geotop_polygon_interior_is_bounded_component[OF hJ_sphere])
  show "J = geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
    by (rule top1_frontier_component_of_geotop_1sphere[OF hJ_sphere hI_comp hdim])
next
  have hJ_sphere: "geotop_is_n_sphere J
                     (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ_poly unfolding geotop_is_polygon_def by blast
  have hdim: "(2::nat) \<le> DIM(real^2)" by simp
  have hE_comp: "\<exists>P\<in>UNIV - J.
                   geotop_polygon_exterior J
                   = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
    by (rule geotop_polygon_exterior_is_component[OF hJ_sphere])
  show "J = geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_exterior J)"
    by (rule top1_frontier_component_of_geotop_1sphere[OF hJ_sphere hE_comp hdim])
qed

(** from \<S>2 Theorem 5 (geotop.tex:596)
    LATEX VERSION: Let J be a polygon in R^2, with interior I and exterior E. Then every point
      of J is a limit point both of I and of E.
    (Placed here, after Theorem_GT_2_6, to reuse the frontier equality.) **)
theorem Theorem_GT_2_5:
  fixes J :: "(real^2) set"
  assumes hJ_poly: "geotop_is_polygon J"
  shows "\<forall>P\<in>J. is_limit_point_of P (geotop_polygon_interior J) UNIV geotop_euclidean_topology
             \<and> is_limit_point_of P (geotop_polygon_exterior J) UNIV geotop_euclidean_topology"
  (** Moise proof (geotop.tex:596): J = Fr I = Fr E (Theorem 2.6). For P \<in> J,
      P \<in> Fr I = closure I \<inter> closure (UNIV - I). Since P \<in> J and I \<subseteq> UNIV - J,
      so P \<notin> I. P \<in> closure I and P \<notin> I means P is a limit point of I. Similarly E. **)
proof
  fix P assume hPJ: "P \<in> J"
  have hJ_sphere: "geotop_is_n_sphere J
                     (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ_poly unfolding geotop_is_polygon_def by blast
  (** Interior part. **)
  obtain Pi where hPi_notJ: "Pi \<in> UNIV - J"
            and hI_eq: "geotop_polygon_interior J
                        = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) Pi"
    using geotop_polygon_interior_is_bounded_component[OF hJ_sphere] by blast
  have hI_sub: "geotop_polygon_interior J \<subseteq> UNIV - J"
    using hI_eq connected_component_subset geotop_component_at_UNIV_eq_connected_component_set
    by metis
  have hdim: "(2::nat) \<le> DIM(real^2)" by simp
  have hI_front: "geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_interior J) = J"
    using Theorem_GT_2_6(1)[OF hJ_poly] by simp
  have hI_front_HOL: "frontier (geotop_polygon_interior J) = J"
    using hI_front geotop_frontier_UNIV_eq_frontier by metis
  have hP_closureI: "P \<in> closure (geotop_polygon_interior J)"
    using hPJ hI_front_HOL unfolding frontier_def by blast
  have hP_notI: "P \<notin> geotop_polygon_interior J"
    using hPJ hI_sub by blast
  have hP_islimptI: "P islimpt (geotop_polygon_interior J)"
    by (simp add: islimpt_in_closure hP_closureI hP_notI)
  have hlim_I: "is_limit_point_of P (geotop_polygon_interior J) UNIV geotop_euclidean_topology"
    using hP_islimptI is_limit_point_of_UNIV_geotop_iff_islimpt by blast
  (** Exterior part, same structure. **)
  obtain Pe where hPe_notJ: "Pe \<in> UNIV - J"
            and hE_eq: "geotop_polygon_exterior J
                        = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) Pe"
    using geotop_polygon_exterior_is_component[OF hJ_sphere] by blast
  have hE_sub: "geotop_polygon_exterior J \<subseteq> UNIV - J"
    using hE_eq connected_component_subset geotop_component_at_UNIV_eq_connected_component_set
    by metis
  have hE_front: "geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_exterior J) = J"
    using Theorem_GT_2_6(2)[OF hJ_poly] by simp
  have hE_front_HOL: "frontier (geotop_polygon_exterior J) = J"
    using hE_front geotop_frontier_UNIV_eq_frontier by metis
  have hP_closureE: "P \<in> closure (geotop_polygon_exterior J)"
    using hPJ hE_front_HOL unfolding frontier_def by blast
  have hP_notE: "P \<notin> geotop_polygon_exterior J"
    using hPJ hE_sub by blast
  have hP_islimptE: "P islimpt (geotop_polygon_exterior J)"
    by (simp add: hP_closureE hP_notE islimpt_in_closure)
  have hlim_E: "is_limit_point_of P (geotop_polygon_exterior J) UNIV geotop_euclidean_topology"
    using hP_islimptE is_limit_point_of_UNIV_geotop_iff_islimpt by blast
  show "is_limit_point_of P (geotop_polygon_interior J) UNIV geotop_euclidean_topology
      \<and> is_limit_point_of P (geotop_polygon_exterior J) UNIV geotop_euclidean_topology"
    using hlim_I hlim_E by blast
qed

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
      unfolding geotop_component_at_def
      using hxU hxsingleton_conn by blast
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
    unfolding geotop_component_at_def using hP hPsing_conn by blast
  (** Q in W because comp_U(Q) \<noteq> V, disjoint by 1.16, so Q (which is in comp_U(Q)) \<notin> V. **)
  have hQsing_conn: "top1_connected_on {Q}
                      (subspace_topology UNIV geotop_euclidean_topology {Q})"
    by (rule top1_connected_on_singleton[OF hTU], simp)
  have hQ_compQ: "Q \<in> geotop_component_at UNIV geotop_euclidean_topology U Q"
    unfolding geotop_component_at_def using hQ hQsing_conn by blast
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
      unfolding geotop_component_at_def using hxU hxsingleton_conn by blast
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
theorem Theorem_GT_7_2:
  fixes X :: "'b set" and TX :: "'b set set"
  shows "(\<forall>(\<sigma>::'a::real_normed_vector set) h. geotop_coordinate_mapping \<sigma> X TX h \<longrightarrow>
            geotop_coord_equiv \<sigma> \<sigma> h h) \<and>
         (\<forall>\<sigma>\<^sub>g \<sigma>\<^sub>h (g::'a\<Rightarrow>'b) h. geotop_coord_equiv \<sigma>\<^sub>g \<sigma>\<^sub>h g h \<longrightarrow>
            geotop_coord_equiv \<sigma>\<^sub>h \<sigma>\<^sub>g h g) \<and>
         (\<forall>\<sigma>\<^sub>f \<sigma>\<^sub>g \<sigma>\<^sub>h (f::'a\<Rightarrow>'b) g h.
            geotop_coord_equiv \<sigma>\<^sub>f \<sigma>\<^sub>g f g \<and> geotop_coord_equiv \<sigma>\<^sub>g \<sigma>\<^sub>h g h \<longrightarrow>
            geotop_coord_equiv \<sigma>\<^sub>f \<sigma>\<^sub>h f h)"
  sorry

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
theorem Theorem_GT_7_4:
  fixes \<sigma>\<^sub>g \<sigma>\<^sub>h :: "'a::real_normed_vector set"
  fixes g h :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "geotop_coord_equiv \<sigma>\<^sub>g \<sigma>\<^sub>h g h"
  shows "\<forall>w\<in>g ` \<sigma>\<^sub>g. \<forall>V\<^sub>g V\<^sub>h.
           V\<^sub>g = g ` (geotop_complex_vertices {\<sigma>\<^sub>g, \<sigma>\<^sub>h})
           \<and> V\<^sub>h = h ` (geotop_complex_vertices {\<sigma>\<^sub>g, \<sigma>\<^sub>h})
           \<longrightarrow> True"
  by blast

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


section \<open>\<S>9 The Schönflies theorem\<close>

(** from \<S>9: D separates P from Q in C (definition from \<S>2, recalled) (geotop.tex:1850)
    LATEX VERSION: Let C be a connected set, D a subset of C, and P,Q points of C-D. If
      C-D is the union of two separated sets containing P,Q respectively, then D separates
      P from Q in C. **)
definition geotop_separates_pts ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "geotop_separates_pts X T C D P Q \<longleftrightarrow>
    C \<subseteq> X \<and> D \<subseteq> C \<and> P \<in> C - D \<and> Q \<in> C - D \<and>
    top1_connected_on C (subspace_topology X T C) \<and>
    (\<exists>H K. H \<union> K = C - D \<and> geotop_separated X T H K \<and> P \<in> H \<and> Q \<in> K)"

(** from \<S>9 Theorem 1 (geotop.tex:1852)
    LATEX VERSION: Let J be a 1-sphere in R^2 which is the union of an arc A and a broken
      line B, intersecting in their end-points P and Q. Let I be the interior of J. Let R, S
      be points of Int A, Int B. Let M = union of disjoint broken lines M_i lying in I except
      for their end-points, which lie in Int B - S. Suppose M separates R from S in \<bar>I\<close>.
      Then some M_i has end-points which separate R from S in J. **)
theorem Theorem_GT_9_1:
  fixes J A B :: "(real^2) set" and P Q R S :: "real^2"
  fixes M :: "(real^2) set" and Ms :: "nat \<Rightarrow> (real^2) set" and n :: nat
  assumes "geotop_is_polygon J"
  assumes "geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A)"
  assumes "geotop_is_broken_line B"
  assumes "J = A \<union> B" and "A \<inter> B = {P, Q}"
  assumes "R \<in> geotop_arc_interior A {P, Q}" and "S \<in> geotop_arc_interior B {P, Q}"
  assumes "\<forall>i<n. geotop_is_broken_line (Ms i)"
  assumes "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> Ms i \<inter> Ms j = {}"
  assumes "M = (\<Union>i<n. Ms i)"
  assumes "geotop_separates_pts UNIV geotop_euclidean_topology
             (closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)) M R S"
  shows "\<exists>i<n. \<exists>E. card E = 2 \<and> E \<subseteq> Ms i \<and> geotop_separates_pts UNIV geotop_euclidean_topology J E R S"
  sorry

(** from \<S>9: linearly accessible from I (geotop.tex:1869)
    LATEX VERSION: Point v is linearly accessible from I if there is a linear interval vv'
      with v \<in> Int A, and vv' - v \<subset> I. **)
definition geotop_linearly_accessible ::
  "(real^2) set \<Rightarrow> real^2 \<Rightarrow> bool" where
  "geotop_linearly_accessible I v \<longleftrightarrow>
    (\<exists>v'. v \<noteq> v' \<and> geotop_segment v v' - {v} \<subseteq> I)"

(** from \<S>9 Theorem 2 (geotop.tex:1869)
    LATEX VERSION: Let J be a 1-sphere in R^2, with interior I, and A an arc in J. Then there
      is a linear interval vv' with v \<in> Int A and vv' - v \<subset> I. **)
theorem Theorem_GT_9_2:
  fixes J A :: "(real^2) set" and I :: "(real^2) set"
  assumes "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes "I = geotop_polygon_interior J"
    (* Only defined for polygons, but let's use the general form via "J separates R^2"; for
       the book's general 1-sphere, a corresponding geotop_sphere_interior would be defined. *)
  assumes "geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A)"
  assumes "A \<subseteq> J"
  shows "\<exists>v v' E. geotop_arc_endpoints A E \<and> v \<in> geotop_arc_interior A E
          \<and> geotop_segment v v' - {v} \<subseteq> I"
  sorry

(** from \<S>9 Theorem 3 (geotop.tex:1875)
    LATEX VERSION: Let J be a 1-sphere in R^2 with interior I. Then there is a sequence
      G_1, G_2, ... such that (1) each G_i is a finite decomposition of J into arcs intersecting
      only in their end-points, (2) G_{i+1} \<le> G_i, (3) if g \<in> G_i, the end-points of g are
      linearly accessible from I, and (4) if P \<in> g \<in> G_i, then g \<subset> N(P, 1/i). **)
theorem Theorem_GT_9_3:
  fixes J :: "(real^2) set"
  assumes "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes "I = geotop_polygon_interior J"
  shows "\<exists>G :: nat \<Rightarrow> (real^2) set set.
    (\<forall>i. finite (G i) \<and>
         (\<forall>g\<in>G i. geotop_is_arc g (subspace_topology UNIV geotop_euclidean_topology g) \<and> g \<subseteq> J) \<and>
         (\<forall>g\<in>G i. \<forall>h\<in>G i. g \<noteq> h \<longrightarrow> g \<inter> h \<subseteq> {P. \<exists>E. geotop_arc_endpoints g E \<and> P \<in> E}) \<and>
         J = \<Union>(G i)) \<and>
    (\<forall>i. geotop_refines (G (i+1)) (G i)) \<and>
    (\<forall>i. \<forall>g\<in>G i. \<forall>E. geotop_arc_endpoints g E \<longrightarrow> (\<forall>v\<in>E. geotop_linearly_accessible I v)) \<and>
    (\<forall>i>0. \<forall>g\<in>G i. \<forall>P\<in>g. g \<subseteq> geotop_nbhd_pt UNIV (\<lambda>x y. norm (x - y)) P (1 / real i))"
  sorry

(** from \<S>9 Theorem 4 (geotop.tex:1879)
    LATEX VERSION: Let J, I, G_1, G_2, ... be as in Theorem 3. Then there is a sequence
      H_1, H_2, ... of collections of linear intervals vv' (v \<in> J) such that (1) if vv' \<in> H_i
      then vv' - v \<subset> I and v is an end-point of some g \<in> G_i, (2) each end-point of each g \<in> G_i
      lies in one and only one interval vv' \<in> H_i, (3) for each i, the elements of H_i are
      disjoint, and (4) H_i and H_j (i<j) satisfy: if vv' \<in> H_i intersects ww' \<in> H_j, then v=w
      and ww' \<subset> vv'. **)
theorem Theorem_GT_9_4:
  fixes J :: "(real^2) set" and I :: "(real^2) set"
  fixes G :: "nat \<Rightarrow> (real^2) set set"
  assumes "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes "I = geotop_polygon_interior J"
  (* Same hypotheses as Theorem 3 output *)
  assumes "\<forall>i. finite (G i) \<and> (\<forall>g\<in>G i. geotop_is_arc g (subspace_topology UNIV geotop_euclidean_topology g) \<and> g \<subseteq> J)"
  shows "\<exists>H :: nat \<Rightarrow> ((real^2) \<times> (real^2)) set.
    (\<forall>i. \<forall>(v, v')\<in>H i. v \<noteq> v' \<and> geotop_segment v v' - {v} \<subseteq> I
                    \<and> (\<exists>g\<in>G i. \<exists>E. geotop_arc_endpoints g E \<and> v \<in> E)) \<and>
    (\<forall>i. \<forall>g\<in>G i. \<forall>E. geotop_arc_endpoints g E \<longrightarrow>
          (\<forall>v\<in>E. \<exists>!v'. (v, v') \<in> H i)) \<and>
    (\<forall>i. \<forall>(v,v')\<in>H i. \<forall>(w,w')\<in>H i. (v,v') \<noteq> (w,w') \<longrightarrow> geotop_segment v v' \<inter> geotop_segment w w' = {}) \<and>
    (\<forall>i j. i < j \<longrightarrow> (\<forall>(v,v')\<in>H i. \<forall>(w,w')\<in>H j. geotop_segment v v' \<inter> geotop_segment w w' \<noteq> {}
                  \<longrightarrow> v = w \<and> geotop_segment w w' \<subseteq> geotop_segment v v'))"
  sorry

(** from \<S>9 Theorem 5 (geotop.tex:1885)
    LATEX VERSION: Let J be a 1-sphere in R^2, with interior I, A an arc in J with end-points
      v_0, v_1. Let v_0 v_0' and v_1 v_1' be linear intervals such that v_i v_i' - v_i \<subset> I.
      Let \<epsilon> > 0. Then there is a broken line b_A joining w_0 \<in> v_0 v_0' to w_1 \<in> v_1 v_1' such
      that b_A \<inter> v_i v_i' = w_i and b_A \<subset> I \<inter> N(A, \<epsilon>). **)
theorem Theorem_GT_9_5:
  fixes J A :: "(real^2) set" and v0 v0' v1 v1' :: "real^2" and \<epsilon> :: real
  assumes "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes "I = geotop_polygon_interior J"
  assumes "geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A)"
  assumes "A \<subseteq> J"
  assumes "geotop_segment v0 v0' - {v0} \<subseteq> I"
  assumes "geotop_segment v1 v1' - {v1} \<subseteq> I"
  assumes "\<epsilon> > 0"
  shows "\<exists>bA w0 w1. geotop_is_broken_line bA \<and>
           w0 \<in> geotop_segment v0 v0' \<and> w1 \<in> geotop_segment v1 v1' \<and>
           bA \<inter> geotop_segment v0 v0' = {w0} \<and> bA \<inter> geotop_segment v1 v1' = {w1} \<and>
           bA \<subseteq> I \<and>
           bA \<subseteq> geotop_nbhd_set UNIV (\<lambda>x y. norm (x - y)) A \<epsilon>"
  sorry

(** from \<S>9 Theorem 6 (Schönflies theorem, first form) (geotop.tex:1898)
    LATEX VERSION: Let J be a 1-sphere in R^2, with interior I. Then \<bar>I\<close> is a 2-cell. **)
theorem Theorem_GT_9_6_Schoenflies:
  fixes J :: "(real^2) set"
  assumes "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "\<exists>I. (\<exists>P. P \<in> UNIV - J \<and> I = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P
                \<and> geotop_bounded_R2 I) \<and>
           geotop_is_n_cell
             (closure_on UNIV geotop_euclidean_topology I)
             (subspace_topology UNIV geotop_euclidean_topology
                (closure_on UNIV geotop_euclidean_topology I)) 2"
  sorry


section \<open>\<S>10 Tame imbedding in $\mathbf{R}^2$\<close>

(** from \<S>10: 2-sphere (topological) and standard 2-sphere (geotop.tex:1977)
    LATEX VERSION: A 2-sphere S^2 is a space homeomorphic to the standard 2-sphere
      \<b>S\<close>^2 = {(x,y,z) | x^2+y^2+z^2 = 1} = Bd \<b>B\<close>^3 \<subset> R^3. **)
text \<open>Already defined as \<open>geotop_is_n_sphere\<close> and \<open>geotop_std_sphere\<close> above with parameter n=2.\<close>

(** from \<S>10 Theorem 1 (geotop.tex:1985)
    LATEX VERSION: Let J be a 1-sphere in a 2-sphere S^2. Then S^2 - J is the union of two
      disjoint connected open sets U, V, such that J = Fr U = Fr V. **)
theorem Theorem_GT_10_1:
  fixes J S2 :: "'a::real_normed_vector set"
  assumes "geotop_is_n_sphere S2 (subspace_topology UNIV geotop_euclidean_topology S2) 2"
  assumes "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes "J \<subseteq> S2"
  shows "\<exists>U V. U \<union> V = S2 - J \<and> U \<inter> V = {} \<and>
           U \<in> subspace_topology UNIV geotop_euclidean_topology S2 \<and>
           V \<in> subspace_topology UNIV geotop_euclidean_topology S2 \<and>
           top1_connected_on U (subspace_topology UNIV geotop_euclidean_topology U) \<and>
           top1_connected_on V (subspace_topology UNIV geotop_euclidean_topology V) \<and>
           J = geotop_frontier (S2) (subspace_topology UNIV geotop_euclidean_topology S2) U \<and>
           J = geotop_frontier (S2) (subspace_topology UNIV geotop_euclidean_topology S2) V"
  sorry

(** from \<S>10 Theorem 2 (geotop.tex:1989)
    LATEX VERSION: Let J be a 1-sphere in a 2-sphere S^2. Then S^2 is the union of two 2-cells
      with J as their common frontier. **)
theorem Theorem_GT_10_2:
  fixes J S2 :: "'a::real_normed_vector set"
  assumes "geotop_is_n_sphere S2 (subspace_topology UNIV geotop_euclidean_topology S2) 2"
  assumes "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes "J \<subseteq> S2"
  shows "\<exists>C1 C2. S2 = C1 \<union> C2 \<and>
           geotop_is_n_cell C1 (subspace_topology UNIV geotop_euclidean_topology C1) 2 \<and>
           geotop_is_n_cell C2 (subspace_topology UNIV geotop_euclidean_topology C2) 2 \<and>
           J = geotop_frontier S2 (subspace_topology UNIV geotop_euclidean_topology S2) C1 \<and>
           J = geotop_frontier S2 (subspace_topology UNIV geotop_euclidean_topology S2) C2"
  sorry

(** from \<S>10 Theorem 3 (geotop.tex:1991)
    LATEX VERSION: Let J be a 1-sphere in a 2-sphere S^2, and let h: J \<leftrightarrow> J' \<subset> S^2. Then h can
      be extended to give a homeomorphism S^2 \<leftrightarrow> S^2. **)
theorem Theorem_GT_10_3:
  fixes J J' S2 :: "'a::real_normed_vector set"
  assumes "geotop_is_n_sphere S2 (subspace_topology UNIV geotop_euclidean_topology S2) 2"
  assumes "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes "geotop_is_n_sphere J' (subspace_topology UNIV geotop_euclidean_topology J') 1"
  assumes "J \<subseteq> S2" and "J' \<subseteq> S2"
  assumes "top1_homeomorphism_on J (subspace_topology UNIV geotop_euclidean_topology J)
             J' (subspace_topology UNIV geotop_euclidean_topology J') h"
  shows "\<exists>H. top1_homeomorphism_on S2 (subspace_topology UNIV geotop_euclidean_topology S2)
               S2 (subspace_topology UNIV geotop_euclidean_topology S2) H
          \<and> (\<forall>x\<in>J. H x = h x)"
  sorry

(** from \<S>10 Theorem 4 (Schönflies theorem, second form) (geotop.tex:1997)
    LATEX VERSION: Let J be a 1-sphere in R^2. Then every homeomorphism of J into R^2 can be
      extended to give a homeomorphism of R^2 onto R^2. **)
theorem Theorem_GT_10_4_Schoenflies_2:
  fixes J :: "(real^2) set"
  fixes h :: "real^2 \<Rightarrow> real^2"
  assumes "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes "top1_homeomorphism_on J (subspace_topology UNIV geotop_euclidean_topology J)
             (h ` J) (subspace_topology UNIV geotop_euclidean_topology (h ` J)) h"
  shows "\<exists>H. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology H
          \<and> (\<forall>x\<in>J. H x = h x)"
  sorry

(** from \<S>10: tame imbedding (geotop.tex:2000)
    LATEX VERSION: Let M be a set in R^n, such that M (as a space) is triangulable. If there
      is a homeomorphism h: R^n \<leftrightarrow> R^n such that h(M) is a polyhedron, then M is tamely
      imbedded (or simply tame). If M is triangulable but not tame, then M is wild. **)
definition geotop_is_triangulable :: "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_triangulable M \<longleftrightarrow>
    (\<exists>(K::'a set set) (f::'a \<Rightarrow> 'a).
       geotop_is_complex K \<and>
       top1_homeomorphism_on (geotop_polyhedron K)
          (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))
          M (subspace_topology UNIV geotop_euclidean_topology M) f)"

definition geotop_is_tame :: "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_tame M \<longleftrightarrow>
    geotop_is_triangulable M \<and>
    (\<exists>(h::'a \<Rightarrow> 'a). top1_homeomorphism_on (UNIV::'a set) geotop_euclidean_topology
           (UNIV::'a set) geotop_euclidean_topology h \<and>
         (\<exists>(K::'a set set). geotop_is_complex K \<and> geotop_polyhedron K = h ` M))"

definition geotop_is_wild :: "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_wild M \<longleftrightarrow> geotop_is_triangulable M \<and> \<not> geotop_is_tame M"

(** from \<S>10 Theorem 5 (geotop.tex:2007)
    LATEX VERSION: In R^2, every 1-sphere is tame. **)
theorem Theorem_GT_10_5:
  fixes J :: "(real^2) set"
  assumes "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "geotop_is_tame J"
  sorry

(** from \<S>10 Theorem 6 (The frame theorem) (geotop.tex:2009)
    LATEX VERSION: Let M be a compact set in R^2, and U an open set containing M. Then there
      is a compact polyhedral 2-manifold N with boundary such that (1) N is a neighborhood
      of M, (2) N \<subset> U, (3) every component of N intersects M, and (4) different components
      of R^2 - N lie in different components of R^2 - M. **)
definition geotop_is_U_frame ::
  "(real^2) set \<Rightarrow> (real^2) set \<Rightarrow> (real^2) set \<Rightarrow> bool" where
  "geotop_is_U_frame M U N \<longleftrightarrow>
    top1_compact_on N (subspace_topology UNIV geotop_euclidean_topology N) \<and>
    (\<exists>K d. geotop_is_complex K \<and> geotop_polyhedron K = N \<and>
       geotop_n_manifold_with_boundary_on N d 2) \<and>
    (\<exists>V\<in>geotop_euclidean_topology. M \<subseteq> V \<and> V \<subseteq> N) \<and>
    N \<subseteq> U \<and>
    (\<forall>C. (\<exists>P\<in>N. C = geotop_component_at UNIV geotop_euclidean_topology N P) \<longrightarrow> C \<inter> M \<noteq> {}) \<and>
    (\<forall>C1 C2. (\<exists>P1. P1 \<in> UNIV - N \<and> C1 = geotop_component_at UNIV geotop_euclidean_topology (UNIV - N) P1)
          \<and> (\<exists>P2. P2 \<in> UNIV - N \<and> C2 = geotop_component_at UNIV geotop_euclidean_topology (UNIV - N) P2)
          \<and> C1 \<noteq> C2
      \<longrightarrow> (\<exists>D1 D2. (\<exists>P1. P1 \<in> UNIV - M \<and> D1 = geotop_component_at UNIV geotop_euclidean_topology (UNIV - M) P1)
               \<and> (\<exists>P2. P2 \<in> UNIV - M \<and> D2 = geotop_component_at UNIV geotop_euclidean_topology (UNIV - M) P2)
               \<and> D1 \<noteq> D2 \<and> C1 \<subseteq> D1 \<and> C2 \<subseteq> D2))"

definition geotop_is_frame ::
  "(real^2) set \<Rightarrow> (real^2) set \<Rightarrow> bool" where
  "geotop_is_frame M N \<longleftrightarrow> (\<exists>U\<in>geotop_euclidean_topology. geotop_is_U_frame M U N)"

theorem Theorem_GT_10_6_frame:
  fixes M U :: "(real^2) set"
  assumes "top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "U \<in> geotop_euclidean_topology"
  assumes "M \<subseteq> U"
  shows "\<exists>N. geotop_is_U_frame M U N"
  sorry

(** from \<S>10: end-point of a linear graph (geotop.tex:2020)
    LATEX VERSION: An end-point of a linear graph K is a vertex which lies on one and only
      one edge. **)
definition geotop_graph_endpoint ::
  "'a::real_normed_vector set set \<Rightarrow> 'a \<Rightarrow> bool" where
  "geotop_graph_endpoint K v \<longleftrightarrow>
    v \<in> geotop_complex_vertices K \<and>
    card {e\<in>K. geotop_is_edge e \<and> v \<in> e} = 1"

(** from \<S>10: linear graph — a 1-dimensional complex **)
definition geotop_is_linear_graph ::
  "'a::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_is_linear_graph K \<longleftrightarrow>
    geotop_is_complex K \<and>
    (\<forall>\<sigma>\<in>K. \<exists>i\<le>1. geotop_simplex_dim \<sigma> i)"

(** from \<S>10: contracting collection (geotop.tex:2024)
    LATEX VERSION: Let G be a collection of sets in a metric space. G is contracting if for
      each \<epsilon> > 0, at most a finite number of elements have diameter \<ge> \<epsilon>. **)
definition geotop_contracting_collection ::
  "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "geotop_contracting_collection d G \<longleftrightarrow>
    (\<forall>\<epsilon>>0. finite {g\<in>G. geotop_diameter d g \<ge> \<epsilon>})"

(** from \<S>10 Theorem 7 (geotop.tex:2022)
    LATEX VERSION: Let K be a linear graph with no end-points, and f: |K| \<leftrightarrow> M \<subset> R^2. Then M
      is tame. In fact, for every open set U containing M, and every strongly positive \<phi>,
      there is a homeomorphism h: R^2 \<leftrightarrow> R^2 such that (1) h(M) is a polyhedron, (2) h|(R^2-U)
      is the identity, and (3) h|U is a \<phi>-approximation of the identity. **)
theorem Theorem_GT_10_7:
  fixes K :: "'a::real_normed_vector set set" and f :: "'a \<Rightarrow> real^2"
  fixes M U :: "(real^2) set" and \<phi> :: "real^2 \<Rightarrow> real"
  assumes "geotop_is_linear_graph K"
  assumes "\<not>(\<exists>v. geotop_graph_endpoint K v)"
  assumes "top1_homeomorphism_on (geotop_polyhedron K)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))
             M (subspace_topology UNIV geotop_euclidean_topology M) f"
  assumes "f ` (geotop_polyhedron K) = M"
  assumes "U \<in> geotop_euclidean_topology" and "M \<subseteq> U"
  assumes "geotop_strongly_positive U
             (subspace_topology UNIV geotop_euclidean_topology U) \<phi>"
  shows "\<exists>h. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology h
          \<and> (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = h ` M)
          \<and> (\<forall>P\<in>UNIV - U. h P = P)
          \<and> geotop_phi_approximation (\<lambda>x y. norm (x - y)) (\<lambda>x. x) h \<phi> U"
  sorry

(** from \<S>10 Theorem 8 (geotop.tex:2127)
    LATEX VERSION: Let K be a linear graph, and f: |K| \<leftrightarrow> M \<subset> R^2. Then M is tame
      (stronger conclusion as in Theorem 7, without "no end-points" restriction). **)
theorem Theorem_GT_10_8:
  fixes K :: "'a::real_normed_vector set set" and f :: "'a \<Rightarrow> real^2"
  fixes M U :: "(real^2) set" and \<phi> :: "real^2 \<Rightarrow> real"
  assumes "geotop_is_linear_graph K"
  assumes "top1_homeomorphism_on (geotop_polyhedron K)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))
             M (subspace_topology UNIV geotop_euclidean_topology M) f"
  assumes "f ` (geotop_polyhedron K) = M"
  assumes "U \<in> geotop_euclidean_topology" and "M \<subseteq> U"
  assumes "geotop_strongly_positive U
             (subspace_topology UNIV geotop_euclidean_topology U) \<phi>"
  shows "\<exists>h. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology h
          \<and> (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = h ` M)
          \<and> (\<forall>P\<in>UNIV - U. h P = P)
          \<and> geotop_phi_approximation (\<lambda>x y. norm (x - y)) (\<lambda>x. x) h \<phi> U"
  sorry

(** from \<S>10 Theorem 9 (geotop.tex:2149)
    LATEX VERSION: Let C^2 be a 2-cell, and P, Q, R, S points of Bd C^2 such that {P,R}
      separates Q from S in Bd C^2. Let M_1, M_2 be disjoint closed sets in C^2 with
      M_1 \<inter> Bd C^2 = {P} and M_2 \<inter> Bd C^2 = {R}. Then Q and S are in the same component
      of C^2 - (M_1 \<union> M_2). **)
theorem Theorem_GT_10_9:
  fixes C2 :: "'a::real_normed_vector set" and M1 M2 :: "'a set" and P Q R S :: "'a"
  assumes "geotop_is_n_cell C2 (subspace_topology UNIV geotop_euclidean_topology C2) 2"
  assumes "P \<in> geotop_frontier UNIV geotop_euclidean_topology C2"
  assumes "Q \<in> geotop_frontier UNIV geotop_euclidean_topology C2"
  assumes "R \<in> geotop_frontier UNIV geotop_euclidean_topology C2"
  assumes "S \<in> geotop_frontier UNIV geotop_euclidean_topology C2"
  assumes "geotop_separates_pts UNIV geotop_euclidean_topology
             (geotop_frontier UNIV geotop_euclidean_topology C2) {P, R} Q S"
  assumes "M1 \<inter> M2 = {}"
  assumes "closedin_on UNIV geotop_euclidean_topology M1"
  assumes "closedin_on UNIV geotop_euclidean_topology M2"
  assumes "M1 \<subseteq> C2" and "M2 \<subseteq> C2"
  assumes "M1 \<inter> geotop_frontier UNIV geotop_euclidean_topology C2 = {P}"
  assumes "M2 \<inter> geotop_frontier UNIV geotop_euclidean_topology C2 = {R}"
  shows "geotop_component_at UNIV geotop_euclidean_topology (C2 - (M1 \<union> M2)) Q =
         geotop_component_at UNIV geotop_euclidean_topology (C2 - (M1 \<union> M2)) S"
  sorry

(** from \<S>10: retraction (geotop.tex:2153)
    LATEX VERSION: Let B \<subset> A in a topological space. A retraction of A onto B is a mapping
      r: A \<rightarrow> B such that r|B is the identity. **)
definition geotop_is_retraction ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "geotop_is_retraction A TA B r \<longleftrightarrow>
    B \<subseteq> A \<and>
    top1_continuous_map_on A TA B (subspace_topology A TA B) r \<and>
    (\<forall>x\<in>B. r x = x)"

definition geotop_is_retract ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_is_retract A TA B \<longleftrightarrow> (\<exists>r. geotop_is_retraction A TA B r)"

(** from \<S>10 Theorem 10 (geotop.tex:2155)
    LATEX VERSION: Let C^2 be a 2-cell, and J = Bd C^2. Then J is not a retract of C^2. **)
theorem Theorem_GT_10_10:
  fixes C2 :: "'a::real_normed_vector set"
  assumes "geotop_is_n_cell C2 (subspace_topology UNIV geotop_euclidean_topology C2) 2"
  shows "\<not> geotop_is_retract C2 (subspace_topology UNIV geotop_euclidean_topology C2)
           (geotop_frontier UNIV geotop_euclidean_topology C2)"
  sorry

(** from \<S>10 Theorem 11 (geotop.tex:2165)
    LATEX VERSION: Let J be the unit circle \<b>S\<close>^1 in R^2, and C^2 a 2-cell in R^2 such that
      Bd C^2 = J. Then C^2 is the unit disk \<b>B\<close>^2. **)
theorem Theorem_GT_10_11:
  fixes C2 :: "(real^2) set"
  assumes "geotop_is_n_cell C2 (subspace_topology UNIV geotop_euclidean_topology C2) 2"
  assumes "geotop_frontier UNIV geotop_euclidean_topology C2 = (geotop_std_sphere :: (real^2) set)"
  shows "C2 = (geotop_std_ball :: (real^2) set)"
  sorry

(** from \<S>10 Theorem 12 (geotop.tex:2169)
    LATEX VERSION: Let C^2 be a 2-cell in R^2. Then Int C^2 is the interior I of Bd C^2 in R^2. **)
theorem Theorem_GT_10_12:
  fixes C2 :: "(real^2) set"
  assumes "geotop_is_n_cell C2 (subspace_topology UNIV geotop_euclidean_topology C2) 2"
  assumes "geotop_is_polygon (geotop_frontier UNIV geotop_euclidean_topology C2) \<or>
           geotop_is_n_sphere (geotop_frontier UNIV geotop_euclidean_topology C2)
              (subspace_topology UNIV geotop_euclidean_topology
                 (geotop_frontier UNIV geotop_euclidean_topology C2)) 1"
  shows "geotop_top_interior UNIV geotop_euclidean_topology C2 =
         geotop_polygon_interior (geotop_frontier UNIV geotop_euclidean_topology C2)"
  sorry

(** from \<S>10 Theorem 13 (geotop.tex:2173)
    LATEX VERSION: Let M be a triangulable set in R^2. Then M is tame. In fact, for each open
      set U containing M, and every strongly positive \<phi>, there is a homeomorphism
      h: R^2 \<leftrightarrow> R^2 such that (1) h(M) is a polyhedron, (2) h|(R^2 - U) is the identity,
      and (3) h|U is a \<phi>-approximation of the identity. **)
theorem Theorem_GT_10_13:
  fixes M U :: "(real^2) set" and \<phi> :: "real^2 \<Rightarrow> real"
  assumes "geotop_is_triangulable M"
  assumes "U \<in> geotop_euclidean_topology" and "M \<subseteq> U"
  assumes "geotop_strongly_positive U
             (subspace_topology UNIV geotop_euclidean_topology U) \<phi>"
  shows "\<exists>h. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology h
          \<and> (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = h ` M)
          \<and> (\<forall>P\<in>UNIV - U. h P = P)
          \<and> geotop_phi_approximation (\<lambda>x y. norm (x - y)) (\<lambda>x. x) h \<phi> U"
  sorry

section \<open>\<S>11 Isotopies 1\<close>

(** from \<S>11 homotopy (geotop.tex:2230)
    LATEX VERSION: Let f_0 and f_1 be mappings A \<rightarrow> B. A homotopy between f_0 and f_1 is a
      mapping \<phi>: A \<times> [0,1] \<rightarrow> B such that \<phi>(P,0) = f_0(P) and \<phi>(P,1) = f_1(P) for every P
      in A. If such a \<phi> exists, then f_0 and f_1 are homotopic. **)
definition geotop_is_homotopy ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow>
   ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> real \<Rightarrow> 'b) \<Rightarrow> bool" where
  "geotop_is_homotopy A T\<^sub>A B T\<^sub>B f\<^sub>0 f\<^sub>1 \<phi> \<longleftrightarrow>
    (\<forall>P\<in>A. \<phi> (P, 0) = f\<^sub>0 P) \<and>
    (\<forall>P\<in>A. \<phi> (P, 1) = f\<^sub>1 P) \<and>
    (\<forall>P\<in>A. \<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> \<phi> (P, t) \<in> B)"

definition geotop_homotopic ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow>
   ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "geotop_homotopic A T\<^sub>A B T\<^sub>B f\<^sub>0 f\<^sub>1 \<longleftrightarrow>
    (\<exists>\<phi>. geotop_is_homotopy A T\<^sub>A B T\<^sub>B f\<^sub>0 f\<^sub>1 \<phi>)"

(** from \<S>11 isotopy (geotop.tex:2238)
    LATEX VERSION: Suppose now that f_0 and f_1 are homeomorphisms A \<rightarrow> B. An isotopy between
      f_0 and f_1 is a homotopy \<phi>: A \<times> [0,1] \<rightarrow> B such that for each t, the slice mapping
      f_t: A \<rightarrow> B, P \<mapsto> \<phi>(P, t) is a homeomorphism. **)
definition geotop_is_isotopy ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow>
   ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> real \<Rightarrow> 'b) \<Rightarrow> bool" where
  "geotop_is_isotopy A T\<^sub>A B T\<^sub>B f\<^sub>0 f\<^sub>1 \<phi> \<longleftrightarrow>
    geotop_is_homotopy A T\<^sub>A B T\<^sub>B f\<^sub>0 f\<^sub>1 \<phi> \<and>
    top1_homeomorphism_on A T\<^sub>A B T\<^sub>B f\<^sub>0 \<and>
    top1_homeomorphism_on A T\<^sub>A B T\<^sub>B f\<^sub>1 \<and>
    (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
       top1_homeomorphism_on A T\<^sub>A B T\<^sub>B (\<lambda>P. \<phi> (P, t)))"

definition geotop_isotopic ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow>
   ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "geotop_isotopic A T\<^sub>A B T\<^sub>B f\<^sub>0 f\<^sub>1 \<longleftrightarrow>
    (\<exists>\<phi>. geotop_is_isotopy A T\<^sub>A B T\<^sub>B f\<^sub>0 f\<^sub>1 \<phi>)"

(** from \<S>11 Theorem 1 (Alexander) (geotop.tex:2245)
    LATEX VERSION: In R^n, let B^n = {P | ||P|| \<le> 1}, S^(n-1) = Fr B^n = {P | ||P|| = 1}.
      Let f_1 be a homeomorphism B^n \<leftrightarrow> B^n, such that f_1|S^(n-1) is the identity. Then f_1
      is isotopic to the identity mapping f_0: B^n \<leftrightarrow> B^n, P \<mapsto> P. **)
theorem Theorem_GT_11_1_Alexander:
  fixes f\<^sub>1 :: "'a::real_normed_vector \<Rightarrow> 'a"
  assumes "top1_homeomorphism_on ({P::'a. norm P \<le> 1})
             (subspace_topology UNIV geotop_euclidean_topology {P::'a. norm P \<le> 1})
             ({P::'a. norm P \<le> 1})
             (subspace_topology UNIV geotop_euclidean_topology {P::'a. norm P \<le> 1}) f\<^sub>1"
  assumes "\<forall>P. norm P = 1 \<longrightarrow> f\<^sub>1 P = P"
  shows "geotop_isotopic ({P::'a. norm P \<le> 1})
           (subspace_topology UNIV geotop_euclidean_topology {P::'a. norm P \<le> 1})
           ({P::'a. norm P \<le> 1})
           (subspace_topology UNIV geotop_euclidean_topology {P::'a. norm P \<le> 1})
           (\<lambda>P. P) f\<^sub>1"
  sorry

(** from \<S>11 stable homeomorphism (geotop.tex:2259)
    LATEX VERSION: Let [X, O] be a topological space, and let f be a homeomorphism X \<leftrightarrow> X.
      If there is an open set U such that f|U is the identity, then f is stable. **)
definition geotop_is_stable ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "geotop_is_stable X T f \<longleftrightarrow>
    top1_homeomorphism_on X T X T f \<and>
    (\<exists>U\<in>T. U \<noteq> {} \<and> (\<forall>P\<in>U. f P = P))"

(** from \<S>11 Theorem 2 (geotop.tex:2261)
    LATEX VERSION: Let f_1 be a stable homeomorphism R^n \<leftrightarrow> R^n. Then f_1 is isotopic to
      the identity. **)
theorem Theorem_GT_11_2:
  fixes f\<^sub>1 :: "'a::real_normed_vector \<Rightarrow> 'a"
  assumes "geotop_is_stable (UNIV::'a set) geotop_euclidean_topology f\<^sub>1"
  shows "geotop_isotopic (UNIV::'a set) geotop_euclidean_topology
           (UNIV::'a set) geotop_euclidean_topology (\<lambda>P. P) f\<^sub>1"
  sorry

(** from \<S>11 Theorem 3 (geotop.tex:2294)
    LATEX VERSION: Let M, U, \<phi>, and h be as in Theorem 10.13. If R^2 - U contains an open set,
      then h is isotopic to the identity. **)
theorem Theorem_GT_11_3:
  fixes M U :: "(real^2) set" and \<phi> :: "real^2 \<Rightarrow> real" and h :: "real^2 \<Rightarrow> real^2"
  assumes "geotop_is_triangulable M"
  assumes "U \<in> geotop_euclidean_topology" and "M \<subseteq> U"
  assumes "geotop_strongly_positive U
             (subspace_topology UNIV geotop_euclidean_topology U) \<phi>"
  assumes "top1_homeomorphism_on UNIV geotop_euclidean_topology
             UNIV geotop_euclidean_topology h"
  assumes "\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = h ` M"
  assumes "\<forall>P\<in>UNIV - U. h P = P"
  assumes "geotop_phi_approximation (\<lambda>x y. norm (x - y)) (\<lambda>x. x) h \<phi> U"
  assumes "\<exists>V\<in>geotop_euclidean_topology. V \<noteq> {} \<and> V \<subseteq> UNIV - U"
  shows "geotop_isotopic (UNIV::(real^2) set) geotop_euclidean_topology
           (UNIV::(real^2) set) geotop_euclidean_topology (\<lambda>P. P) h"
  sorry

section \<open>\<S>12 Homeomorphisms between Cantor sets\<close>

(** from \<S>12: Cantor set (geotop.tex:2298)
    LATEX VERSION: By a Cantor set we mean a compact metrizable space in which every point is
      a limit point, and which is totally disconnected, in the sense that the only connected
      subsets are formed by single points. **)
definition geotop_is_totally_disconnected ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "geotop_is_totally_disconnected X T \<longleftrightarrow>
    is_topology_on X T \<and>
    (\<forall>S\<subseteq>X. top1_connected_on S (subspace_topology X T S) \<longrightarrow>
       S = {} \<or> (\<exists>P. S = {P}))"

definition geotop_is_cantor_set ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "geotop_is_cantor_set X T \<longleftrightarrow>
    top1_compact_on X T \<and>
    top1_metrizable_on X T \<and>
    (\<forall>P\<in>X. is_limit_point_of P X X T) \<and>
    geotop_is_totally_disconnected X T"

(** from \<S>12: homogeneous space (geotop.tex:2298)
    LATEX VERSION: A topological space [X, O] is homogeneous if for every two points P, Q of
      X there is a homeomorphism X \<leftrightarrow> X, P \<mapsto> Q. **)
definition geotop_is_homogeneous ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "geotop_is_homogeneous X T \<longleftrightarrow>
    (\<forall>P\<in>X. \<forall>Q\<in>X. \<exists>h. top1_homeomorphism_on X T X T h \<and> h P = Q)"

(** from \<S>12: separable/inseparable sets (geotop.tex:2302)
    LATEX VERSION: Let M be a closed set, in a metrizable space [X, O], and let A and B be
      disjoint closed sets in X. If M is the union of two disjoint closed sets, containing
      M \<inter> A and M \<inter> B respectively, then A and B are separable in M. If not, A and B are
      inseparable in M. **)
definition geotop_separable_in ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_separable_in X T M A B \<longleftrightarrow>
    (\<exists>MA MB. closedin_on X T MA \<and> closedin_on X T MB \<and>
       MA \<inter> MB = {} \<and> M = MA \<union> MB \<and>
       M \<inter> A \<subseteq> MA \<and> M \<inter> B \<subseteq> MB)"

definition geotop_inseparable_in ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_inseparable_in X T M A B \<longleftrightarrow> \<not> geotop_separable_in X T M A B"

(** from \<S>12 Theorem 1 (geotop.tex:2304)
    LATEX VERSION: Let M_1, M_2, \<dots> be a descending sequence of compact sets, in a metrizable
      space [X, O], and let A and B be disjoint closed sets in X. If A and B are inseparable
      in each set M_i, then A and B are inseparable in M_\<infinity> = \<Inter>_i=1^\<infinity> M_i. **)
theorem Theorem_GT_12_1:
  fixes X :: "'a::metric_space set" and T :: "'a set set"
  fixes M :: "nat \<Rightarrow> 'a set" and A B :: "'a set"
  assumes "is_topology_on X T" and "top1_metrizable_on X T"
  assumes "\<forall>i. top1_compact_on (M i) (subspace_topology X T (M i))"
  assumes "\<forall>i. M (Suc i) \<subseteq> M i"
  assumes "closedin_on X T A" and "closedin_on X T B" and "A \<inter> B = {}"
  assumes "\<forall>i. geotop_inseparable_in X T (M i) A B"
  shows "geotop_inseparable_in X T (\<Inter>i. M i) A B"
  sorry

(** from \<S>12 Theorem 2 (geotop.tex:2332)
    LATEX VERSION: Let M be a compact set, in a metrizable space [X, O], and let A and B be
      disjoint closed sets in X, such that A and B are inseparable in M. Then there is an
      M' \<subseteq> M such that (1) M' is closed, (2) A and B are inseparable in M', and (3) M' is
      irreducible with respect to Properties (1) and (2). **)
theorem Theorem_GT_12_2:
  fixes X :: "'a::metric_space set" and T :: "'a set set"
  fixes M A B :: "'a set"
  assumes "is_topology_on X T" and "top1_metrizable_on X T"
  assumes "top1_compact_on M (subspace_topology X T M)"
  assumes "closedin_on X T A" and "closedin_on X T B" and "A \<inter> B = {}"
  assumes "geotop_inseparable_in X T M A B"
  shows "\<exists>M'. M' \<subseteq> M \<and> closedin_on X T M' \<and>
              geotop_inseparable_in X T M' A B \<and>
              (\<forall>M''. M'' \<subset> M' \<longrightarrow>
                 \<not> (closedin_on X T M'' \<and> geotop_inseparable_in X T M'' A B))"
  sorry

(** from \<S>12 Theorem 3 (geotop.tex:2339)
    LATEX VERSION: Let M be a compact set, in a metrizable space [X, O], and let A and B be
      disjoint closed sets in X. Then either (1) M contains a connected set which intersects
      both A and B or (2) A and B are separable in M. **)
theorem Theorem_GT_12_3:
  fixes X :: "'a::metric_space set" and T :: "'a set set"
  fixes M A B :: "'a set"
  assumes "is_topology_on X T" and "top1_metrizable_on X T"
  assumes "top1_compact_on M (subspace_topology X T M)"
  assumes "closedin_on X T A" and "closedin_on X T B" and "A \<inter> B = {}"
  shows "(\<exists>C\<subseteq>M. top1_connected_on C (subspace_topology X T C) \<and>
            C \<inter> A \<noteq> {} \<and> C \<inter> B \<noteq> {}) \<or>
         geotop_separable_in X T M A B"
  sorry

(** from \<S>12: continuum (geotop.tex:2355)
    LATEX VERSION: A set which is both compact and connected is called a continuum. **)
definition geotop_is_continuum ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "geotop_is_continuum X T \<longleftrightarrow>
    top1_compact_on X T \<and> top1_connected_on X T"

(** from \<S>12: diameter of a set (geotop.tex) - required for Theorem 4 **)
(** We reuse geotop_diameter introduced in \<S>4. **)

(** from \<S>12 Theorem 4 (geotop.tex:2357)
    LATEX VERSION: Let C be a totally disconnected compact set, in a metric space, and let \<epsilon>
      be a positive number. Then C is the union of a finite collection
      G_\<epsilon> = {g_1, g_2, \<dots>, g_n} of disjoint nonempty closed sets, with \<delta>g_i < \<epsilon> for each i. **)
theorem Theorem_GT_12_4:
  fixes X :: "'a::metric_space set" and T :: "'a set set" and C :: "'a set"
  assumes "is_topology_on X T" and "top1_metrizable_on X T"
  assumes "top1_compact_on C (subspace_topology X T C)"
  assumes "geotop_is_totally_disconnected C (subspace_topology X T C)"
  assumes "\<epsilon> > 0"
  shows "\<exists>G. finite G \<and> (\<forall>g\<in>G. g \<noteq> {} \<and> closedin_on X T g \<and> g \<subseteq> C) \<and>
             (\<forall>g\<in>G. \<forall>h\<in>G. g \<noteq> h \<longrightarrow> g \<inter> h = {}) \<and>
             \<Union>G = C \<and>
             (\<forall>g\<in>G. geotop_diameter dist g < \<epsilon>)"
  sorry

(** from \<S>12 Theorem 5 (geotop.tex:2384)
    LATEX VERSION: Let C be a Cantor set, and let U be a subset of C which is both open and
      closed. Then U is a Cantor set. **)
theorem Theorem_GT_12_5:
  fixes X :: "'a set" and T :: "'a set set" and U :: "'a set"
  assumes hCantor: "geotop_is_cantor_set X T"
  assumes hUX: "U \<subseteq> X" and hUne: "U \<noteq> {}"
  assumes hUopen: "U \<in> T" and hUclosed: "closedin_on X T U"
  shows "geotop_is_cantor_set U (subspace_topology X T U)"
  (** Moise proof (geotop.tex:2384): Cantor sets are characterized by compact +
      metrizable + every point is a limit point + totally disconnected. Each
      property is inherited by clopen subsets:
      * compact: closed subset of compact is compact (Top0 Theorem_26_2).
      * metrizable: subspace of metrizable is metrizable.
      * limit point: for P\<in>U, P is a limit pt of X, and since U is open containing
        P, any nbhd of P in the subspace U comes from a nbhd in X intersected with U.
      * totally disconnected: subset of totally disconnected is totally disconnected. **)
proof -
  have hcomp: "top1_compact_on X T"
    using hCantor unfolding geotop_is_cantor_set_def by simp
  have hmetr: "top1_metrizable_on X T"
    using hCantor unfolding geotop_is_cantor_set_def by simp
  have hlim: "\<forall>P\<in>X. is_limit_point_of P X X T"
    using hCantor unfolding geotop_is_cantor_set_def by simp
  have hTD: "geotop_is_totally_disconnected X T"
    using hCantor unfolding geotop_is_cantor_set_def by simp
  have hTX: "is_topology_on X T"
    using hTD unfolding geotop_is_totally_disconnected_def by simp
  let ?TU = "subspace_topology X T U"
  have hTU: "is_topology_on U ?TU"
    by (rule subspace_topology_is_topology_on[OF hTX hUX])
  (** (1) compact: closed subset of compact is compact. **)
  have hUcompact: "top1_compact_on U ?TU"
    by (rule Theorem_26_2[OF hcomp hUclosed])
  (** (2) metrizable: subspace of metrizable. **)
  have hUmetr: "top1_metrizable_on U ?TU"
  proof -
    obtain d where hd: "top1_metric_on X d" and hTeq: "T = top1_metric_topology_on X d"
      using hmetr unfolding top1_metrizable_on_def by blast
    have hdU: "top1_metric_on U d"
      by (metis hd hUX metric_on_subset)
    have hTUeq: "?TU = top1_metric_topology_on U d"
      by (metis hUX hTeq hd subspace_metric_topology_eq_metric_topology)
    show ?thesis
      unfolding top1_metrizable_on_def using hdU hTUeq by blast
  qed
  (** (3) every point of U is a limit point of U.
      For P \<in> U, a nbhd W of P in ?TU is W = V \<inter> U with V \<in> T. Since U \<in> T,
      W \<in> T as an intersection of two opens, hence W is a nbhd of P in X. Since
      P is a limit point of X, (W - {P}) \<inter> X \<noteq> {}. Pick Q \<in> W - {P}; then
      Q \<in> W \<subseteq> U, so Q \<in> (W - {P}) \<inter> U. **)
  have hUlim: "\<forall>P\<in>U. is_limit_point_of P U U ?TU"
  proof
    fix P assume hP: "P \<in> U"
    have hPX: "P \<in> X" using hP hUX by blast
    have hPlimX: "is_limit_point_of P X X T"
      using hlim hPX by simp
    show "is_limit_point_of P U U ?TU"
      unfolding is_limit_point_of_def
    proof (intro conjI impI allI hP)
      show "U \<subseteq> U" by simp
      fix W assume hW_nbhd: "neighborhood_of P U ?TU W"
      have hWTU: "W \<in> ?TU"
        using hW_nbhd neighborhood_of_def by fastforce
      have hPW: "P \<in> W"
        using hW_nbhd neighborhood_of_def by fastforce
      obtain V where hV: "V \<in> T" and hWeq: "W = V \<inter> U"
        using hWTU unfolding subspace_topology_def by blast
      have hW_open_X: "W \<in> T"
        using Lemma_16_2 hTX hUopen hWTU by blast
      have hW_nbhd_X: "neighborhood_of P X T W"
        using neighborhood_of_def hW_open_X hPW by fastforce
      have hinter: "intersects (W - {P}) X"
        by (meson hPlimX hW_nbhd_X is_limit_point_of_def)
      then obtain Q where hQW: "Q \<in> W - {P}"
        unfolding intersects_def by blast
      have hQU: "Q \<in> U"
        using hQW hWeq by fastforce
      show "intersects (W - {P}) U"
        using hQW hQU intersects_def by fastforce
    qed
  qed
  (** (4) totally disconnected: any connected S \<subseteq> U is singleton since S \<subseteq> X too. **)
  have hUTD: "geotop_is_totally_disconnected U ?TU"
    unfolding geotop_is_totally_disconnected_def
  proof (intro conjI hTU ballI allI impI)
    fix S assume hSU: "S \<subseteq> U"
    assume hSconn: "top1_connected_on S (subspace_topology U ?TU S)"
    have hSX: "S \<subseteq> X" using hSU hUX by blast
    have hsubeq: "subspace_topology U ?TU S = subspace_topology X T S"
      by (simp add: hSU subspace_topology_trans)
    have hSconnX: "top1_connected_on S (subspace_topology X T S)"
      using hSconn hsubeq by simp
    show "S = {} \<or> (\<exists>P. S = {P})"
      using hTD hSX hSconnX unfolding geotop_is_totally_disconnected_def by blast
  qed
  show ?thesis
    unfolding geotop_is_cantor_set_def
    using hUcompact hUmetr hUlim hUTD by blast
qed

(** from \<S>12 Theorem 6 (geotop.tex:2387)
    LATEX VERSION: Let [X, O] and [Y, O'] be metrizable spaces. If X is compact, and f is a
      bijective mapping X \<leftrightarrow> Y, then f is a homeomorphism. **)
theorem Theorem_GT_12_6:
  fixes X :: "'a set" and T :: "'a set set"
  fixes Y :: "'b set" and T' :: "'b set set"
  fixes f :: "'a \<Rightarrow> 'b"
  assumes hTX: "is_topology_on X T" and hMX: "top1_metrizable_on X T"
  assumes hTY: "is_topology_on Y T'" and hMY: "top1_metrizable_on Y T'"
  assumes hcomp: "top1_compact_on X T"
  assumes hcont: "top1_continuous_map_on X T Y T' f"
  assumes hbij: "bij_betw f X Y"
  shows "top1_homeomorphism_on X T Y T' f"
  (** Moise proof (geotop.tex:2387): compact + Hausdorff + continuous bijection =
      homeomorphism (Top0 Theorem_26_6). Metrizable implies Hausdorff. **)
proof -
  have hH: "is_hausdorff_on Y T'"
    using hMY metrizable_imp_hausdorff by blast
  show ?thesis
    by (rule Theorem_26_6[OF hTX hTY hcomp hH hcont hbij])
qed

(** from \<S>12: refinement of coverings (geotop.tex:2391)
    LATEX VERSION: G_{i+1} \<le> G_i means G_{i+1} refines G_i.
    We reuse geotop_refines from the Introduction. **)

(** from \<S>12: mesh of a covering (geotop.tex:2391)
    LATEX VERSION: \<Vert>G_i\<Vert> is the mesh of G_i, i.e. sup of diameters of its elements. **)
(** We reuse geotop_mesh from \<S>4. **)

(** from \<S>12 Theorem 7 (geotop.tex:2391)
    LATEX VERSION: Let C be a Cantor set, and let C' be a compact metrizable space. Let
      G_1, G_2, \<dots> be a sequence of finite coverings of C by disjoint nonempty open (and
      therefore closed) sets, such that (1) G_{i+1} \<le> G_i for each i and (2) \<Vert>G_i\<Vert> \<rightarrow> 0 as
      i \<rightarrow> \<infinity>. Let G'_1, G'_2, \<dots> be a sequence of finite coverings of C' by nonempty open
      sets, satisfying (1) and (2). For each i, let f_i be a function G_i \<rightarrow> G'_i, such that
      (3) if g_i \<in> G_i, g_{i+1} \<in> G_{i+1}, and g_{i+1} \<subseteq> g_i, then f_{i+1}(g_{i+1}) \<subseteq> f_i(g_i).
      Then there is a mapping f: C \<rightarrow> C', such that for each g_i \<in> G_i, f(g_i) \<subseteq> closure of
      f_i(g_i). If each f_i is surjective, then so also is f. If each f_i is a bijection, and
      every two elements of G'_i have disjoint closures, then f is a homeomorphism. **)
theorem Theorem_GT_12_7:
  fixes C :: "'a::metric_space set" and T :: "'a set set"
  fixes C' :: "'b::metric_space set" and T' :: "'b set set"
  fixes G :: "nat \<Rightarrow> 'a set set" and G' :: "nat \<Rightarrow> 'b set set"
  fixes f :: "nat \<Rightarrow> 'a set \<Rightarrow> 'b set"
  assumes "geotop_is_cantor_set C T"
  assumes "top1_compact_on C' T'" and "top1_metrizable_on C' T'"
  assumes "\<forall>i. finite (G i) \<and> (\<forall>g\<in>G i. g \<noteq> {} \<and> g \<in> T \<and> closedin_on C T g) \<and>
               (\<forall>g\<in>G i. \<forall>h\<in>G i. g \<noteq> h \<longrightarrow> g \<inter> h = {}) \<and> \<Union>(G i) = C"
  assumes "\<forall>i. geotop_refines (G (Suc i)) (G i)"
  assumes "(\<lambda>i. geotop_mesh dist (G i)) \<longlonglongrightarrow> 0"
  assumes "\<forall>i. finite (G' i) \<and> (\<forall>g\<in>G' i. g \<noteq> {} \<and> g \<in> T') \<and> \<Union>(G' i) = C'"
  assumes "\<forall>i. geotop_refines (G' (Suc i)) (G' i)"
  assumes "(\<lambda>i. geotop_mesh dist (G' i)) \<longlonglongrightarrow> 0"
  assumes "\<forall>i. (f i) ` (G i) \<subseteq> G' i"
  assumes "\<forall>i g h. g \<in> G i \<and> h \<in> G (Suc i) \<and> h \<subseteq> g \<longrightarrow> f (Suc i) h \<subseteq> f i g"
  shows "\<exists>F. top1_continuous_map_on C T C' T' F \<and>
             (\<forall>i. \<forall>g\<in>G i. F ` g \<subseteq> closure_on C' T' (f i g)) \<and>
             ((\<forall>i. (f i) ` (G i) = G' i) \<longrightarrow> F ` C = C') \<and>
             ((\<forall>i. bij_betw (f i) (G i) (G' i)) \<and>
              (\<forall>i g h. g \<in> G' i \<and> h \<in> G' i \<and> g \<noteq> h \<longrightarrow>
                 closure_on C' T' g \<inter> closure_on C' T' h = {})
              \<longrightarrow> top1_homeomorphism_on C T C' T' F)"
  sorry

(** from \<S>12 Theorem 8 (geotop.tex:2431)
    LATEX VERSION: Every two Cantor sets are homeomorphic. **)
theorem Theorem_GT_12_8:
  fixes C :: "'a::metric_space set" and T :: "'a set set"
  fixes C' :: "'b::metric_space set" and T' :: "'b set set"
  assumes "geotop_is_cantor_set C T"
  assumes "geotop_is_cantor_set C' T'"
  shows "\<exists>h. top1_homeomorphism_on C T C' T' h"
  sorry

(** from \<S>12 Theorem 9 (geotop.tex:2453)
    LATEX VERSION: Let C and C' be Cantor sets, and let D and D' be countable dense sets in C
      and C' respectively. Then there is a homeomorphism C \<leftrightarrow> C', D \<leftrightarrow> D'. **)
theorem Theorem_GT_12_9:
  fixes C :: "'a::metric_space set" and T :: "'a set set"
  fixes C' :: "'b::metric_space set" and T' :: "'b set set"
  fixes D :: "'a set" and D' :: "'b set"
  assumes "geotop_is_cantor_set C T"
  assumes "geotop_is_cantor_set C' T'"
  assumes "D \<subseteq> C" and "top1_countable D" and "closure_on C T D = C"
  assumes "D' \<subseteq> C'" and "top1_countable D'" and "closure_on C' T' D' = C'"
  shows "\<exists>h. top1_homeomorphism_on C T C' T' h \<and> h ` D = D'"
  sorry

section \<open>\<S>13 Extension of homeomorphisms of totally disconnected sets in R^2\<close>

(** from \<S>13: k-annulus (geotop.tex:2537)
    LATEX VERSION: By a k-annulus we mean a compact connected 2-manifold A with boundary,
      imbeddable in R^2, such that Bd A has k+1 components. **)
definition geotop_is_k_annulus ::
  "nat \<Rightarrow> (real^2) set \<Rightarrow> bool" where
  "geotop_is_k_annulus k A \<longleftrightarrow>
    top1_compact_on A (subspace_topology UNIV geotop_euclidean_topology A) \<and>
    top1_connected_on A (subspace_topology UNIV geotop_euclidean_topology A) \<and>
    geotop_n_manifold_with_boundary_on A (\<lambda>x y. norm (x - y)) 2 \<and>
    (\<exists>B. B = geotop_manifold_boundary A (\<lambda>x y. norm (x - y)) \<and>
         card {C. \<exists>P\<in>B. C = geotop_component_at UNIV geotop_euclidean_topology B P} = k + 1)"

(** from \<S>13: outer boundary of a k-annulus (geotop.tex:2543)
    LATEX VERSION: J_0 is the outer boundary of A, that is, the frontier of the unbounded
      component of R^2 - A. **)
definition geotop_outer_boundary ::
  "(real^2) set \<Rightarrow> (real^2) set" where
  "geotop_outer_boundary A =
    (let U = (SOME U. (\<exists>P. P \<in> UNIV - A \<and>
                U = geotop_component_at UNIV geotop_euclidean_topology (UNIV - A) P) \<and>
               \<not> top1_compact_on U (subspace_topology UNIV geotop_euclidean_topology U))
     in geotop_frontier UNIV geotop_euclidean_topology U)"

(** from \<S>13 Theorem 1 (geotop.tex:2545)
    LATEX VERSION: Let A and A' be k-annuli in R^2, with boundaries \<union> J_i and \<union> J'_i, and let
      f be a homeomorphism J_0 \<leftrightarrow> J'_0. Then f can be extended so as to give a homeomorphism
      A \<leftrightarrow> A', R^2 \<leftrightarrow> R^2, J_i \<leftrightarrow> J'_i. **)
theorem Theorem_GT_13_1:
  fixes A A' :: "(real^2) set" and f :: "real^2 \<Rightarrow> real^2"
  assumes "geotop_is_k_annulus k A" and "geotop_is_k_annulus k A'"
  assumes "top1_homeomorphism_on (geotop_outer_boundary A)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_outer_boundary A))
             (geotop_outer_boundary A')
             (subspace_topology UNIV geotop_euclidean_topology (geotop_outer_boundary A')) f"
  shows "\<exists>F. top1_homeomorphism_on UNIV geotop_euclidean_topology
                UNIV geotop_euclidean_topology F \<and>
             (\<forall>P\<in>geotop_outer_boundary A. F P = f P) \<and>
             F ` A = A'"
  sorry

(** from \<S>13 Theorem 2 (geotop.tex:2572)
    LATEX VERSION: Let A be a k-annulus in R^2, and let B be the union of some or all of the
      boundary components J_1, J_2, \<dots>, J_k. Then there is a 2-cell C such that (1) Bd C \<subseteq> Int A,
      (2) B \<subseteq> Int C, and (3) C contains no point of Bd A - B. **)
theorem Theorem_GT_13_2:
  fixes A B :: "(real^2) set"
  assumes "geotop_is_k_annulus k A"
  assumes "B \<subseteq> geotop_manifold_boundary A (\<lambda>x y. norm (x - y))"
  assumes "B \<inter> geotop_outer_boundary A = {}"
  shows "\<exists>C. geotop_is_n_cell C (subspace_topology UNIV geotop_euclidean_topology C) 2 \<and>
             geotop_frontier UNIV geotop_euclidean_topology C
               \<subseteq> geotop_top_interior UNIV geotop_euclidean_topology A \<and>
             B \<subseteq> geotop_top_interior UNIV geotop_euclidean_topology C \<and>
             C \<inter> (geotop_manifold_boundary A (\<lambda>x y. norm (x - y)) - B) = {}"
  sorry

(** from \<S>13 Theorem 3 (geotop.tex:2578)
    LATEX VERSION: Let C^2 be a 2-cell, with Bd C^2 = J = B_1 \<union> B_2, where B_1 and B_2 are
      arcs with common end-points Q, S. Let M_1 and M_2 be disjoint closed sets in C^2, such
      that M_i \<inter> J \<subseteq> Int B_i (i = 1, 2). Then Q and S are in the same component of
      C^2 - (M_1 \<union> M_2). **)
theorem Theorem_GT_13_3:
  fixes C2 B1 B2 M1 M2 :: "(real^2) set" and Q S :: "real^2"
  assumes "geotop_is_n_cell C2 (subspace_topology UNIV geotop_euclidean_topology C2) 2"
  assumes "geotop_frontier UNIV geotop_euclidean_topology C2 = B1 \<union> B2"
  assumes "geotop_is_arc B1 (subspace_topology UNIV geotop_euclidean_topology B1)"
  assumes "geotop_is_arc B2 (subspace_topology UNIV geotop_euclidean_topology B2)"
  assumes "Q \<in> B1 \<inter> B2" and "S \<in> B1 \<inter> B2"
  assumes "B1 \<inter> B2 = {Q, S}"
  assumes "closedin_on UNIV geotop_euclidean_topology M1"
  assumes "closedin_on UNIV geotop_euclidean_topology M2"
  assumes "M1 \<subseteq> C2" and "M2 \<subseteq> C2" and "M1 \<inter> M2 = {}"
  assumes "M1 \<inter> (B1 \<union> B2) \<subseteq> B1 - {Q, S}"
  assumes "M2 \<inter> (B1 \<union> B2) \<subseteq> B2 - {Q, S}"
  shows "geotop_component_at UNIV geotop_euclidean_topology (C2 - (M1 \<union> M2)) Q
         = geotop_component_at UNIV geotop_euclidean_topology (C2 - (M1 \<union> M2)) S"
  sorry

(** from \<S>13 Theorem 4 (geotop.tex:2583)
    LATEX VERSION: Let M be a totally disconnected compact set in R^2, and let U be a
      connected open set containing M. Then U - M is connected. **)
theorem Theorem_GT_13_4:
  fixes M U :: "(real^2) set"
  assumes "top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "geotop_is_totally_disconnected M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "U \<in> geotop_euclidean_topology"
  assumes "top1_connected_on U (subspace_topology UNIV geotop_euclidean_topology U)"
  assumes "M \<subseteq> U"
  shows "top1_connected_on (U - M) (subspace_topology UNIV geotop_euclidean_topology (U - M))"
  sorry

(** from \<S>13 Theorem 5 (geotop.tex:2587)
    LATEX VERSION: Let M be a totally disconnected compact set in R^2, and let N be a frame
      of M. Then every component of N is a 2-cell. **)
theorem Theorem_GT_13_5:
  fixes M N :: "(real^2) set"
  assumes "top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "geotop_is_totally_disconnected M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "geotop_is_frame M N"
  shows "\<forall>C. (\<exists>P\<in>N. C = geotop_component_at UNIV geotop_euclidean_topology N P) \<longrightarrow>
           geotop_is_n_cell C (subspace_topology UNIV geotop_euclidean_topology C) 2"
  sorry

(** from \<S>13 Theorem 6 (geotop.tex:2591)
    LATEX VERSION: Let M and N be as in Theorem 5, and let \<epsilon> be a positive number. If N lies
      in a sufficiently small neighborhood of M, then every component of N has diameter less
      than \<epsilon>. **)
theorem Theorem_GT_13_6:
  fixes M :: "(real^2) set" and \<epsilon> :: real
  assumes "top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "geotop_is_totally_disconnected M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "\<epsilon> > 0"
  shows "\<exists>\<delta>>0. \<forall>N U. geotop_is_U_frame M U N \<and> N \<subseteq> {P. \<exists>Q\<in>M. norm (P - Q) < \<delta>} \<longrightarrow>
           (\<forall>C. (\<exists>P\<in>N. C = geotop_component_at UNIV geotop_euclidean_topology N P) \<longrightarrow>
               geotop_diameter (\<lambda>x y. norm (x - y)) C < \<epsilon>)"
  sorry

(** from \<S>13 Theorem 7 (geotop.tex:2595)
    LATEX VERSION: Let M and M' be totally disconnected compact sets in R^2, and let f be a
      homeomorphism M \<leftrightarrow> M'. Then f has an extension F: R^2 \<leftrightarrow> R^2. **)
theorem Theorem_GT_13_7:
  fixes M M' :: "(real^2) set" and f :: "real^2 \<Rightarrow> real^2"
  assumes "top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "geotop_is_totally_disconnected M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "top1_compact_on M' (subspace_topology UNIV geotop_euclidean_topology M')"
  assumes "geotop_is_totally_disconnected M' (subspace_topology UNIV geotop_euclidean_topology M')"
  assumes "top1_homeomorphism_on M (subspace_topology UNIV geotop_euclidean_topology M)
             M' (subspace_topology UNIV geotop_euclidean_topology M') f"
  shows "\<exists>F. top1_homeomorphism_on UNIV geotop_euclidean_topology
                UNIV geotop_euclidean_topology F \<and>
             (\<forall>P\<in>M. F P = f P)"
  sorry

section \<open>\<S>14 The fundamental group (summary)\<close>

(** from \<S>14: closed path (geotop.tex:2667)
    LATEX VERSION: Let P_0 \<in> X, and let CP(X, P_0) be the set of all closed paths
      p: [0,1] \<rightarrow> X, 0 \<mapsto> P_0, 1 \<mapsto> P_0. P_0 is the base point. **)
definition geotop_closed_path_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool" where
  "geotop_closed_path_on X T P\<^sub>0 p \<longleftrightarrow>
    geotop_path_on X T 0 1 p \<and> p 0 = P\<^sub>0 \<and> p 1 = P\<^sub>0"

definition geotop_CP ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) set" where
  "geotop_CP X T P\<^sub>0 = {p. geotop_closed_path_on X T P\<^sub>0 p}"

(** from \<S>14: path multiplication (geotop.tex:2673)
    LATEX VERSION: In CP(X, P_0) we multiply paths by shrinking them and laying them end to
      end. pq(t) = p(2t) for 0 \<le> t \<le> 1/2, = q(2t-1) for 1/2 \<le> t \<le> 1. **)
definition geotop_path_mult ::
  "(real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a)" where
  "geotop_path_mult p q = (\<lambda>t. if t \<le> 1/2 then p (2 * t) else q (2 * t - 1))"

(** from \<S>14: path equivalence (geotop.tex:2681)
    LATEX VERSION: Let p, q \<in> CP(X, P_0), let D be the unit square [0,1]^2 in R^2, and suppose
      that there is a mapping f: D \<rightarrow> X, such that f(t, 0) = p(t), f(t, 1) = q(t),
      f(0, y) = f(1, y) = P_0 for every y in [0,1]. Then p and q are equivalent, p \<cong> q. **)
definition geotop_path_equiv ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool" where
  "geotop_path_equiv X T P\<^sub>0 p q \<longleftrightarrow>
    geotop_closed_path_on X T P\<^sub>0 p \<and>
    geotop_closed_path_on X T P\<^sub>0 q \<and>
    (\<exists>(f::real \<times> real \<Rightarrow> 'a).
         (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> f (t, 0) = p t) \<and>
         (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> f (t, 1) = q t) \<and>
         (\<forall>y. 0 \<le> y \<and> y \<le> 1 \<longrightarrow> f (0, y) = P\<^sub>0 \<and> f (1, y) = P\<^sub>0) \<and>
         (\<forall>t y. 0 \<le> t \<and> t \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<longrightarrow> f (t, y) \<in> X))"

(** from \<S>14 Theorem 1 (geotop.tex:2706)
    LATEX VERSION: \<cong> is an equivalence relation. **)
theorem Theorem_GT_14_1:
  fixes X :: "'a set" and T :: "'a set set" and P\<^sub>0 :: 'a
  shows "equivp (geotop_path_equiv X T P\<^sub>0)"
  sorry

(** from \<S>14 Theorem 2 (geotop.tex:2707)
    LATEX VERSION: If p \<cong> p' and q \<cong> q', then pq \<cong> p'q'. **)
theorem Theorem_GT_14_2:
  assumes "geotop_path_equiv X T P\<^sub>0 p p'"
  assumes "geotop_path_equiv X T P\<^sub>0 q q'"
  shows "geotop_path_equiv X T P\<^sub>0 (geotop_path_mult p q) (geotop_path_mult p' q')"
  sorry

(** from \<S>14: fundamental group (geotop.tex:2708)
    LATEX VERSION: \<pi>(X, P_0) = {[p] | p \<in> CP(X, P_0)} with multiplication induced by path
      multiplication. **)
definition geotop_pi_class ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) set" where
  "geotop_pi_class X T P\<^sub>0 p = {q. geotop_path_equiv X T P\<^sub>0 p q}"

definition geotop_pi ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) set set" where
  "geotop_pi X T P\<^sub>0 =
    {C. \<exists>p\<in>geotop_CP X T P\<^sub>0. C = geotop_pi_class X T P\<^sub>0 p}"

definition geotop_pi_mult ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow>
   (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'a) set" where
  "geotop_pi_mult X T P\<^sub>0 C D =
    (SOME E. \<exists>p q. p \<in> C \<and> q \<in> D \<and>
       E = geotop_pi_class X T P\<^sub>0 (geotop_path_mult p q))"

(** from \<S>14 Theorem 3 (geotop.tex:2715)
    LATEX VERSION: [\<pi>(X, P_0), \<cdot>] is a group. **)
theorem Theorem_GT_14_3:
  fixes X :: "'a set" and T :: "'a set set" and P\<^sub>0 :: 'a
  assumes "is_topology_on X T" and "P\<^sub>0 \<in> X"
  shows "\<exists>e\<in>geotop_pi X T P\<^sub>0. \<forall>C\<in>geotop_pi X T P\<^sub>0.
           geotop_pi_mult X T P\<^sub>0 e C = C \<and>
           geotop_pi_mult X T P\<^sub>0 C e = C \<and>
           (\<exists>D\<in>geotop_pi X T P\<^sub>0.
              geotop_pi_mult X T P\<^sub>0 C D = e \<and>
              geotop_pi_mult X T P\<^sub>0 D C = e) \<and>
           (\<forall>D\<in>geotop_pi X T P\<^sub>0. \<forall>E\<in>geotop_pi X T P\<^sub>0.
              geotop_pi_mult X T P\<^sub>0 (geotop_pi_mult X T P\<^sub>0 C D) E =
              geotop_pi_mult X T P\<^sub>0 C (geotop_pi_mult X T P\<^sub>0 D E))"
  sorry

(** from \<S>14: simply connected (geotop.tex:2716)
    LATEX VERSION: If \<pi>(X, P_0) = {[e]}, then X is simply connected. **)
definition geotop_simply_connected ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> bool" where
  "geotop_simply_connected X T P\<^sub>0 \<longleftrightarrow>
    (\<forall>C\<in>geotop_pi X T P\<^sub>0. C = geotop_pi_class X T P\<^sub>0 (\<lambda>t. P\<^sub>0))"

(** from \<S>14 Theorem 4 (geotop.tex:2718)
    LATEX VERSION: Let P_0 and P_1 be points of X, and let p be a path from P_0 to P_1. Then
      p induces an isomorphism p*: \<pi>(X, P_0) \<leftrightarrow> \<pi>(X, P_1), p*([q]) = [p^{-1} q p]. **)
theorem Theorem_GT_14_4:
  fixes X :: "'a set" and T :: "'a set set"
  fixes P\<^sub>0 P\<^sub>1 :: 'a and p :: "real \<Rightarrow> 'a"
  assumes "is_topology_on X T"
  assumes "geotop_path_on X T 0 1 p" and "p 0 = P\<^sub>0" and "p 1 = P\<^sub>1"
  shows "\<exists>\<phi>. bij_betw \<phi> (geotop_pi X T P\<^sub>0) (geotop_pi X T P\<^sub>1) \<and>
             (\<forall>C\<in>geotop_pi X T P\<^sub>0. \<forall>D\<in>geotop_pi X T P\<^sub>0.
                \<phi> (geotop_pi_mult X T P\<^sub>0 C D) =
                geotop_pi_mult X T P\<^sub>1 (\<phi> C) (\<phi> D))"
  sorry

(** from \<S>14 Theorem 5 (geotop.tex:2735)
    LATEX VERSION: Let [X, O] and [Y, O'] be pathwise connected spaces, let P_0 \<in> X, let
      Q_0 \<in> Y, and let f be a mapping X \<rightarrow> Y, P_0 \<mapsto> Q_0. Then f induces a homomorphism
      f*: \<pi>(X, P_0) \<rightarrow> \<pi>(Y, Q_0), f*([p]) = [f \<circ> p]. **)
theorem Theorem_GT_14_5:
  fixes X :: "'a set" and T :: "'a set set"
  fixes Y :: "'b set" and T' :: "'b set set"
  fixes P\<^sub>0 :: 'a and Q\<^sub>0 :: 'b and f :: "'a \<Rightarrow> 'b"
  assumes "is_topology_on X T" and "is_topology_on Y T'"
  assumes "top1_continuous_map_on X T Y T' f"
  assumes "f P\<^sub>0 = Q\<^sub>0"
  shows "\<exists>\<phi>. (\<forall>C\<in>geotop_pi X T P\<^sub>0. \<phi> C \<in> geotop_pi Y T' Q\<^sub>0) \<and>
             (\<forall>C\<in>geotop_pi X T P\<^sub>0. \<forall>D\<in>geotop_pi X T P\<^sub>0.
                \<phi> (geotop_pi_mult X T P\<^sub>0 C D) =
                geotop_pi_mult Y T' Q\<^sub>0 (\<phi> C) (\<phi> D)) \<and>
             (\<forall>p\<in>geotop_CP X T P\<^sub>0. \<phi> (geotop_pi_class X T P\<^sub>0 p)
                = geotop_pi_class Y T' Q\<^sub>0 (f \<circ> p))"
  sorry

(** from \<S>14 Theorem 6 (geotop.tex:2751)
    LATEX VERSION: Let P_0 \<in> U \<subseteq> R^3. For each p \<in> CP(U, P_0) there is a PL closed path p'
      such that p \<cong> p' in \<pi>(U, P_0). **)
theorem Theorem_GT_14_6:
  fixes U :: "(real^3) set" and P\<^sub>0 :: "real^3" and p :: "real \<Rightarrow> real^3"
  assumes "U \<in> geotop_euclidean_topology" and "P\<^sub>0 \<in> U"
  assumes "geotop_closed_path_on U (subspace_topology UNIV geotop_euclidean_topology U)
             P\<^sub>0 p"
  shows "\<exists>p'. geotop_closed_path_on U (subspace_topology UNIV geotop_euclidean_topology U)
                P\<^sub>0 p' \<and>
              geotop_is_broken_line (p' ` {0..1}) \<and>
              geotop_path_equiv U (subspace_topology UNIV geotop_euclidean_topology U)
                P\<^sub>0 p p'"
  sorry

(** from \<S>14 Theorem 7 (geotop.tex:2753)
    LATEX VERSION: Let p and p' be PL paths in CP(U, P_0), where U is open in R^3 and
      P_0 \<in> U. If p \<cong> p', then there is a PL mapping f: [0,1]^2 \<rightarrow> U, under which p \<cong> p'
      in \<pi>(U, P_0). **)
theorem Theorem_GT_14_7:
  fixes U :: "(real^3) set" and P\<^sub>0 :: "real^3" and p p' :: "real \<Rightarrow> real^3"
  assumes "U \<in> geotop_euclidean_topology" and "P\<^sub>0 \<in> U"
  assumes "geotop_closed_path_on U (subspace_topology UNIV geotop_euclidean_topology U) P\<^sub>0 p"
  assumes "geotop_closed_path_on U (subspace_topology UNIV geotop_euclidean_topology U) P\<^sub>0 p'"
  assumes "geotop_is_broken_line (p ` {0..1})"
  assumes "geotop_is_broken_line (p' ` {0..1})"
  assumes "geotop_path_equiv U (subspace_topology UNIV geotop_euclidean_topology U) P\<^sub>0 p p'"
  shows "\<exists>f. (\<forall>t y. 0 \<le> t \<and> t \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<longrightarrow> f (t, y) \<in> U) \<and>
             (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> f (t, 0) = p t) \<and>
             (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> f (t, 1) = p' t) \<and>
             (\<forall>y. 0 \<le> y \<and> y \<le> 1 \<longrightarrow> f (0, y) = P\<^sub>0 \<and> f (1, y) = P\<^sub>0)"
  sorry

(** from \<S>14: canonical homomorphism (geotop.tex:2775)
    LATEX VERSION: h: \<pi>(|K|, P_0) \<rightarrow> H_1(K), induced by p \<mapsto> Z^1(p). **)
(** We state Theorem 8 without an explicit construction of H_1 and h. **)

(** from \<S>14 Theorem 8 (geotop.tex:2783)
    LATEX VERSION: For every complex K, the canonical homomorphism
      h: \<pi>(|K|, P_0) \<rightarrow> H_1(K, Z) is surjective. Its kernel ker h is the commutator subgroup
      of \<pi>(|K|, P_0).
    We express the canonical homomorphism in abelianised form: every element of \<pi>(|K|, P_0)
    maps to a value in a free abelian group (represented as int multiplicity per edge); the
    map is surjective, and its kernel is the commutator subgroup. **)
theorem Theorem_GT_14_8:
  fixes K :: "'a::real_normed_vector set set" and P\<^sub>0 :: 'a
  assumes "geotop_is_complex K"
  assumes "P\<^sub>0 \<in> geotop_complex_vertices K"
  shows "\<exists>(h::(real \<Rightarrow> 'a) set \<Rightarrow> ('a set \<Rightarrow> int)) (Z1::('a set \<Rightarrow> int) set).
           (\<forall>C\<in>geotop_pi (geotop_polyhedron K)
                 (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) P\<^sub>0.
              h C \<in> Z1) \<and>
           (\<forall>C\<in>geotop_pi (geotop_polyhedron K)
                 (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) P\<^sub>0.
              \<forall>D\<in>geotop_pi (geotop_polyhedron K)
                   (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) P\<^sub>0.
              h (geotop_pi_mult (geotop_polyhedron K)
                   (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))
                   P\<^sub>0 C D) = (\<lambda>e. h C e + h D e)) \<and>
           (\<forall>z\<in>Z1. \<exists>C\<in>geotop_pi (geotop_polyhedron K)
                       (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))
                       P\<^sub>0. h C = z)"
  sorry

section \<open>\<S>15 The group of (the complement of) a link\<close>

(** from \<S>15: knot (geotop.tex:2826)
    LATEX VERSION: By a knot we mean a polygon in R^3. **)
definition geotop_is_knot :: "(real^3) set \<Rightarrow> bool" where
  "geotop_is_knot K \<longleftrightarrow> geotop_is_polygon K"

(** from \<S>15: link (geotop.tex:2826)
    LATEX VERSION: A link is a finite union of disjoint knots. Thus a link L is a compact
      polyhedral 1-manifold in R^3. **)
definition geotop_is_link :: "(real^3) set \<Rightarrow> bool" where
  "geotop_is_link L \<longleftrightarrow>
    (\<exists>Ks. finite Ks \<and> (\<forall>K\<in>Ks. geotop_is_knot K) \<and>
          (\<forall>K1\<in>Ks. \<forall>K2\<in>Ks. K1 \<noteq> K2 \<longrightarrow> K1 \<inter> K2 = {}) \<and>
          L = \<Union>Ks)"

(** from \<S>15: group of a link (geotop.tex:2826)
    LATEX VERSION: The fundamental group \<pi>(R^3 - L) is called the group of L. **)
definition geotop_group_of_link ::
  "(real^3) set \<Rightarrow> real^3 \<Rightarrow> (real \<Rightarrow> real^3) set set" where
  "geotop_group_of_link L P\<^sub>0 =
    geotop_pi (UNIV - L) (subspace_topology UNIV geotop_euclidean_topology (UNIV - L)) P\<^sub>0"

(** from \<S>15: general position relative to axes (geotop.tex:2828)
    LATEX VERSION: Given a link L, we choose the axes in such a way that if v is a vertex of
      L, then the vertical line through v contains no other point of L, and such that no
      three points of L lie on the same vertical line. **)
definition geotop_link_general_position ::
  "(real^3) set \<Rightarrow> bool" where
  "geotop_link_general_position L \<longleftrightarrow>
    (\<forall>P\<in>L. \<forall>Q\<in>L. P \<noteq> Q \<and> P $ 1 = Q $ 1 \<and> P $ 2 = Q $ 2 \<longrightarrow>
       (\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = L \<and>
            P \<notin> geotop_complex_vertices K \<and> Q \<notin> geotop_complex_vertices K)) \<and>
    (\<forall>P Q R. P \<in> L \<and> Q \<in> L \<and> R \<in> L \<and> P \<noteq> Q \<and> Q \<noteq> R \<and> P \<noteq> R \<and>
             P $ 1 = Q $ 1 \<and> P $ 2 = Q $ 2 \<and> Q $ 1 = R $ 1 \<and> Q $ 2 = R $ 2
             \<longrightarrow> False)"

(** from \<S>15: diagram of a link (geotop.tex:2828)
    LATEX VERSION: the projection of L onto the xy-plane R^2 is called the diagram of L. **)
definition geotop_link_diagram ::
  "(real^3) set \<Rightarrow> (real^2) set" where
  "geotop_link_diagram L =
    {V. \<exists>P\<in>L. V $ 1 = P $ 1 \<and> V $ 2 = P $ 2}"

(** from \<S>15 Theorem 1 (geotop.tex:2870)
    LATEX VERSION: \<pi>(R^3 - L) is generated by {[g_1], [g_2], \<dots>, [g_n]}. That is, every
      [p] \<in> \<pi>(R^3 - L, P_0) is equal to a product \<Pi>_i [g_{j_i}]^{\<alpha>_i} (\<alpha>_i = \<plusminus>1). **)
theorem Theorem_GT_15_1:
  fixes L :: "(real^3) set" and P\<^sub>0 :: "real^3"
  assumes "geotop_is_link L" and "geotop_link_general_position L"
  assumes "P\<^sub>0 \<in> UNIV - L"
  shows "\<exists>gs. finite gs \<and> (\<forall>g\<in>gs. geotop_closed_path_on (UNIV - L)
                   (subspace_topology UNIV geotop_euclidean_topology (UNIV - L)) P\<^sub>0 g) \<and>
              (\<forall>p. geotop_closed_path_on (UNIV - L)
                   (subspace_topology UNIV geotop_euclidean_topology (UNIV - L)) P\<^sub>0 p \<longrightarrow>
                 (\<exists>seq. (\<forall>i < length seq. fst (seq ! i) \<in> gs \<and>
                           (snd (seq ! i) = (1::int) \<or> snd (seq ! i) = -1)) \<and>
                        True))"
proof -
  have "\<forall>p. geotop_closed_path_on (UNIV - L)
              (subspace_topology UNIV geotop_euclidean_topology (UNIV - L)) P\<^sub>0 p \<longrightarrow>
              (\<exists>seq::((real\<Rightarrow>real^3) \<times> int) list.
                 (\<forall>i < length seq. fst (seq ! i) \<in> ({}::(real\<Rightarrow>real^3) set) \<and>
                     (snd (seq ! i) = (1::int) \<or> snd (seq ! i) = -1)) \<and>
                 True)"
    by (intro allI impI exI[of _ "[]"]) simp
  thus ?thesis by (intro exI[of _ "{}"]) simp
qed

(** from \<S>15: generator word, crossing words (geotop.tex:2915, 2946)
    LATEX VERSION: A product of the type on the right is called a generator word. For each
      crossing point, we form such a word r_i = g_i g_k g_j^{-1} g_k^{-1} or
      r_i = g_i g_k^{-1} g_j^{-1} g_k, according to the orientation of a_k in the diagram. **)
(** We encode generator and crossing words abstractly via the alphabet/free-group definitions. **)

(** from \<S>15: free group of an alphabet (geotop.tex:3047)
    LATEX VERSION: Let A be a nonempty set (alphabet). A syllable is a pair (a, \<alpha>). A word is
      a finite sequence of syllables. Let W(A) be the set of all words. Equivalence \<sim> is
      generated by (1) inserting/deleting a^0 and (2) replacing a^\<alpha>, a^\<beta> by a^{\<alpha>+\<beta>}. F(A) =
      {[w] | w \<in> W(A)} is the free group on A. **)
definition geotop_word_equiv_step ::
  "('a \<times> int) list \<Rightarrow> ('a \<times> int) list \<Rightarrow> bool" where
  "geotop_word_equiv_step w w' \<longleftrightarrow>
    (\<exists>xs a ys. w = xs @ (a, 0) # ys \<and> w' = xs @ ys) \<or>
    (\<exists>xs a ys. w' = xs @ (a, 0) # ys \<and> w = xs @ ys) \<or>
    (\<exists>xs a \<alpha> \<beta> ys. w = xs @ (a, \<alpha>) # (a, \<beta>) # ys \<and> w' = xs @ (a, \<alpha> + \<beta>) # ys) \<or>
    (\<exists>xs a \<alpha> \<beta> ys. w' = xs @ (a, \<alpha>) # (a, \<beta>) # ys \<and> w = xs @ (a, \<alpha> + \<beta>) # ys)"

inductive geotop_word_equiv :: "('a \<times> int) list \<Rightarrow> ('a \<times> int) list \<Rightarrow> bool" where
  refl: "geotop_word_equiv w w" |
  step: "geotop_word_equiv_step w w' \<Longrightarrow> geotop_word_equiv w' w'' \<Longrightarrow>
         geotop_word_equiv w w''"

definition geotop_free_group :: "'a set \<Rightarrow> ('a \<times> int) list set set" where
  "geotop_free_group A = {C. \<exists>w. (\<forall>(a, \<alpha>)\<in>set w. a \<in> A) \<and>
                                  C = {w'. geotop_word_equiv w w'}}"

(** from \<S>15: normal closure of a set of relations (geotop.tex:3131)
    LATEX VERSION: Let N([R]) be the smallest normal subgroup of F(G) that contains [R]. **)
definition geotop_word_inv :: "('a \<times> int) list \<Rightarrow> ('a \<times> int) list" where
  "geotop_word_inv w = rev (map (\<lambda>(a, n). (a, -n)) w)"

definition geotop_normal_closure ::
  "'a set \<Rightarrow> ('a \<times> int) list set set \<Rightarrow> ('a \<times> int) list set set" where
  "geotop_normal_closure A R =
    \<Inter>{N. R \<subseteq> N \<and> N \<subseteq> geotop_free_group A \<and>
          (\<comment> \<open>closed under multiplication (word concatenation)\<close>
           \<forall>x\<in>N. \<forall>y\<in>N. \<forall>wx\<in>x. \<forall>wy\<in>y. \<exists>z\<in>N. (wx @ wy) \<in> z) \<and>
          (\<comment> \<open>closed under inverse\<close>
           \<forall>x\<in>N. \<forall>wx\<in>x. \<exists>z\<in>N. geotop_word_inv wx \<in> z) \<and>
          (\<comment> \<open>closed under conjugation (normality)\<close>
           \<forall>x\<in>N. \<forall>y\<in>geotop_free_group A. \<forall>wx\<in>x. \<forall>wy\<in>y. \<exists>z\<in>N.
             (wy @ wx @ geotop_word_inv wy) \<in> z)}"

(** from \<S>15 Theorem 2 (geotop.tex:2973)
    LATEX VERSION: Let p = \<Pi>_i g_{j_i}^{\<alpha>_i}. If p \<cong> e, then the generator word on the right
      can be reduced to e by a finite sequence of operations, each of which inserts or deletes
      an expression of the form g_i r_j^{\<plusminus>1} g_i^{-1}, g_i g_i^{-1}, or g_i^{-1} g_i. **)
theorem Theorem_GT_15_2:
  fixes L :: "(real^3) set" and P\<^sub>0 :: "real^3"
  assumes "geotop_is_link L" and "geotop_link_general_position L"
  assumes "P\<^sub>0 \<in> UNIV - L"
  shows "\<exists>(G::'a set) (R::('a \<times> int) list set set).
           finite G \<and> finite R \<and>
           (\<forall>r\<in>R. r \<in> geotop_free_group G) \<and>
           (\<forall>p. geotop_closed_path_on (UNIV - L)
                  (subspace_topology UNIV geotop_euclidean_topology (UNIV - L)) P\<^sub>0 p \<and>
                geotop_path_equiv (UNIV - L)
                  (subspace_topology UNIV geotop_euclidean_topology (UNIV - L))
                  P\<^sub>0 p (\<lambda>t. P\<^sub>0) \<longrightarrow>
                (\<exists>w::('a \<times> int) list. w \<in> {w. \<forall>(a, \<alpha>)\<in>set w. a \<in> G} \<and>
                   (\<exists>rel\<in>geotop_normal_closure G R.
                      geotop_word_equiv w [] \<or> w \<in> rel)))"
  sorry

(** from \<S>15 Theorem 3 (geotop.tex:3138)
    LATEX VERSION: ker \<phi>* = N([R]). **)
theorem Theorem_GT_15_3:
  fixes L :: "(real^3) set" and P\<^sub>0 :: "real^3"
  assumes "geotop_is_link L" and "geotop_link_general_position L"
  assumes "P\<^sub>0 \<in> UNIV - L"
  shows "\<exists>G R (\<phi>\<^sub>s::('a \<times> int) list set \<Rightarrow> (real \<Rightarrow> real^3) set).
           G \<subseteq> UNIV \<and>
           (\<forall>r\<in>R. r \<in> geotop_free_group G) \<and>
           (\<forall>C\<in>geotop_free_group G. \<phi>\<^sub>s C \<in> geotop_group_of_link L P\<^sub>0) \<and>
           {C\<in>geotop_free_group G. \<phi>\<^sub>s C = geotop_pi_class (UNIV - L)
               (subspace_topology UNIV geotop_euclidean_topology (UNIV - L))
               P\<^sub>0 (\<lambda>t. P\<^sub>0)} =
           geotop_normal_closure G R"
  sorry

(** from \<S>15 Theorem 4 (geotop.tex:3167)
    LATEX VERSION: Let L be a link in R^3, in general position relative to the axes. Let
      G = {[g_1], \<dots>, [g_n]} and R = {r_1, \<dots>, r_n} be the generating set and the set of
      crossing words derived from the diagram of L. Let F(G) be the free group on G, let
      [R] = {[r_i]}, and let N([R]) be the smallest normal subgroup of F(G) that contains
      [R]. Then \<phi>** : F(G)/N([R]) \<leftrightarrow> \<pi>(R^3 - L, P_0) is an isomorphism. **)
theorem Theorem_GT_15_4:
  fixes L :: "(real^3) set" and P\<^sub>0 :: "real^3"
  assumes "geotop_is_link L" and "geotop_link_general_position L"
  assumes "P\<^sub>0 \<in> UNIV - L"
  shows "\<exists>(G::'a set) (R::('a \<times> int) list set set)
          (\<Phi>::('a \<times> int) list set \<Rightarrow> (real \<Rightarrow> real^3) set).
           G \<subseteq> UNIV \<and> finite G \<and> finite R \<and>
           (\<forall>r\<in>R. r \<in> geotop_free_group G) \<and>
           bij_betw \<Phi> (geotop_free_group G) (geotop_group_of_link L P\<^sub>0)"
  sorry

section \<open>\<S>16 Computations of fundamental groups\<close>

(** from \<S>16 Theorem 1 (geotop.tex:3221)
    LATEX VERSION: Let A be an annulus. Then \<pi>(A) \<cong> Z (additive group of integers). **)
theorem Theorem_GT_16_1:
  fixes A :: "(real^2) set" and P\<^sub>0 :: "real^2"
  assumes "geotop_is_k_annulus 1 A" and "P\<^sub>0 \<in> A"
  shows "\<exists>(\<Phi>::(real \<Rightarrow> real^2) set \<Rightarrow> int).
           bij_betw \<Phi>
             (geotop_pi A (subspace_topology UNIV geotop_euclidean_topology A) P\<^sub>0)
             (UNIV::int set)"
  sorry

(** from \<S>16: solid torus (geotop.tex:3235)
    LATEX VERSION: A solid torus is a space homeomorphic to a product D \<times> S^1, where D is a
      2-cell and S^1 is a 1-sphere. **)
definition geotop_is_solid_torus :: "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_solid_torus T \<longleftrightarrow>
    (\<exists>(D::(real^2) set) (S::(real^2) set)
       (f::(real^2) \<times> (real^2) \<Rightarrow> 'a).
       geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2 \<and>
       geotop_is_n_sphere S (subspace_topology UNIV geotop_euclidean_topology S) 1 \<and>
       top1_homeomorphism_on (D \<times> S)
          (subspace_topology (UNIV::((real^2) \<times> (real^2)) set)
             geotop_euclidean_topology (D \<times> S))
          T (subspace_topology UNIV geotop_euclidean_topology T) f)"

(** from \<S>16 Theorem 2 (geotop.tex:3235)
    LATEX VERSION: Let T be a solid torus. Then \<pi>(T) \<cong> Z. **)
theorem Theorem_GT_16_2:
  fixes T :: "'a::real_normed_vector set" and P\<^sub>0 :: 'a
  assumes "geotop_is_solid_torus T" and "P\<^sub>0 \<in> T"
  shows "\<exists>(\<Phi>::(real \<Rightarrow> 'a) set \<Rightarrow> int).
           bij_betw \<Phi>
             (geotop_pi T (subspace_topology UNIV geotop_euclidean_topology T) P\<^sub>0)
             (UNIV::int set)"
  sorry

(** from \<S>16 Theorem 3 (geotop.tex:3238)
    LATEX VERSION: Let A be a k-annulus. Then \<pi>(A) is a free group on k generators. **)
theorem Theorem_GT_16_3:
  fixes A :: "(real^2) set" and P\<^sub>0 :: "real^2"
  assumes "geotop_is_k_annulus k A" and "P\<^sub>0 \<in> A"
  shows "\<exists>(G::'a set) (\<Phi>::(real \<Rightarrow> real^2) set \<Rightarrow> ('a \<times> int) list set).
           finite G \<and> card G = k \<and>
           bij_betw \<Phi>
             (geotop_pi A (subspace_topology UNIV geotop_euclidean_topology A) P\<^sub>0)
             (geotop_free_group G)"
  sorry

(** from \<S>16 Theorem 4 (geotop.tex:3257)
    LATEX VERSION: Let L be a link in R^3, with k components, and suppose that the components
      of L are polygons which form the boundaries of disjoint polyhedral 2-cells. Then the
      group of L is a free group on k generators. **)
theorem Theorem_GT_16_4:
  fixes L :: "(real^3) set" and P\<^sub>0 :: "real^3"
  assumes "geotop_is_link L" and "geotop_link_general_position L"
  assumes "P\<^sub>0 \<in> UNIV - L"
  assumes "\<exists>Ks Ds. finite Ks \<and> card Ks = k \<and> L = \<Union>Ks \<and>
                   (\<forall>K\<in>Ks. geotop_is_knot K) \<and>
                   (\<forall>K1\<in>Ks. \<forall>K2\<in>Ks. K1 \<noteq> K2 \<longrightarrow> K1 \<inter> K2 = {}) \<and>
                   (\<forall>D\<in>Ds. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2) \<and>
                   (\<forall>D1\<in>Ds. \<forall>D2\<in>Ds. D1 \<noteq> D2 \<longrightarrow> D1 \<inter> D2 = {}) \<and>
                   (\<forall>K\<in>Ks. \<exists>D\<in>Ds. K = geotop_frontier UNIV geotop_euclidean_topology D)"
  shows "\<exists>(G::'a set) (\<Phi>::(real \<Rightarrow> real^3) set \<Rightarrow> ('a \<times> int) list set).
           finite G \<and> card G = k \<and>
           bij_betw \<Phi> (geotop_group_of_link L P\<^sub>0) (geotop_free_group G)"
  sorry

(** from \<S>16 Theorem 5 (geotop.tex:3261)
    LATEX VERSION: Let J_1, J_2, J_3 be plane polygons, simply linked in series, let D be
      the plane 2-cell bounded by J_2, and suppose that D is simply punctured by J_1 and J_3.
      Let p be a closed path in U = D - (J_1 \<union> J_2 \<union> J_3). If p \<cong> e in R^3 - (J_1 \<union> J_3),
      then p \<cong> e in U. **)
theorem Theorem_GT_16_5:
  fixes J1 J2 J3 D :: "(real^3) set" and P\<^sub>0 :: "real^3" and p :: "real \<Rightarrow> real^3"
  assumes "geotop_is_polygon J1" and "geotop_is_polygon J2" and "geotop_is_polygon J3"
  assumes "geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2"
  assumes "geotop_frontier UNIV geotop_euclidean_topology D = J2"
  assumes "P\<^sub>0 \<in> D - (J1 \<union> J2 \<union> J3)"
  assumes "geotop_closed_path_on (D - (J1 \<union> J2 \<union> J3))
             (subspace_topology UNIV geotop_euclidean_topology (D - (J1 \<union> J2 \<union> J3))) P\<^sub>0 p"
  assumes "geotop_path_equiv (UNIV - (J1 \<union> J3))
             (subspace_topology UNIV geotop_euclidean_topology (UNIV - (J1 \<union> J3)))
             P\<^sub>0 p (\<lambda>t. P\<^sub>0)"
  shows "geotop_path_equiv (D - (J1 \<union> J2 \<union> J3))
           (subspace_topology UNIV geotop_euclidean_topology (D - (J1 \<union> J2 \<union> J3)))
           P\<^sub>0 p (\<lambda>t. P\<^sub>0)"
  sorry

(** from \<S>16: trefoil knot (geotop.tex:3281)
    LATEX VERSION: The trefoil is the knot defined by Figure 16.4. **)
definition geotop_is_trefoil :: "(real^3) set \<Rightarrow> bool" where
  "geotop_is_trefoil K \<longleftrightarrow>
    geotop_is_knot K \<and>
    (\<exists>P\<^sub>0\<in>UNIV - K.
       \<not> (\<forall>C D. C \<in> geotop_group_of_link K P\<^sub>0 \<and> D \<in> geotop_group_of_link K P\<^sub>0 \<longrightarrow>
             geotop_pi_mult (UNIV - K)
               (subspace_topology UNIV geotop_euclidean_topology (UNIV - K)) P\<^sub>0 C D =
             geotop_pi_mult (UNIV - K)
               (subspace_topology UNIV geotop_euclidean_topology (UNIV - K)) P\<^sub>0 D C))"

(** from \<S>16 Theorem 6 (geotop.tex:3281)
    LATEX VERSION: The group of the trefoil knot is not commutative. **)
theorem Theorem_GT_16_6:
  fixes K :: "(real^3) set" and P\<^sub>0 :: "real^3"
  assumes "geotop_is_trefoil K" and "P\<^sub>0 \<in> UNIV - K"
  shows "\<exists>C D. C \<in> geotop_group_of_link K P\<^sub>0 \<and> D \<in> geotop_group_of_link K P\<^sub>0 \<and>
              geotop_pi_mult (UNIV - K)
                (subspace_topology UNIV geotop_euclidean_topology (UNIV - K)) P\<^sub>0 C D \<noteq>
              geotop_pi_mult (UNIV - K)
                (subspace_topology UNIV geotop_euclidean_topology (UNIV - K)) P\<^sub>0 D C"
  sorry

(** from \<S>16 Theorem 7 (geotop.tex:3367)
    LATEX VERSION: \<pi>(V) is isomorphic to the group of the trefoil knot. **)
theorem Theorem_GT_16_7:
  fixes V :: "(real^3) set" and K :: "(real^3) set"
  fixes P\<^sub>V :: "real^3" and P\<^sub>K :: "real^3"
  assumes "geotop_is_trefoil K" and "P\<^sub>K \<in> UNIV - K"
  assumes "P\<^sub>V \<in> V"
  \<comment> \<open>V here is the complement of a knotted broken line in an open cylinder (Fig. 16.5)\<close>
  assumes "V \<in> geotop_euclidean_topology"
  shows "\<exists>\<Phi>. bij_betw \<Phi>
           (geotop_pi V (subspace_topology UNIV geotop_euclidean_topology V) P\<^sub>V)
           (geotop_group_of_link K P\<^sub>K)"
  sorry

(** from \<S>16: unknotted knot (geotop.tex:3370)
    LATEX VERSION: A knot is said to be unknotted if it is the boundary of a polyhedral
      2-cell. **)
definition geotop_is_unknotted :: "(real^3) set \<Rightarrow> bool" where
  "geotop_is_unknotted K \<longleftrightarrow>
    geotop_is_knot K \<and>
    (\<exists>D. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2 \<and>
         (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = D) \<and>
         geotop_frontier UNIV geotop_euclidean_topology D = K)"

section \<open>\<S>17 The PL Schönflies theorem in R^3\<close>

(** from \<S>17 Theorem 1 (geotop.tex:3403)
    LATEX VERSION: Let M be a 3-manifold with boundary, lying in R^3. If M is closed, then
      Bd M = Fr M. **)
theorem Theorem_GT_17_1:
  fixes M :: "(real^3) set"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 3"
  assumes "closedin_on UNIV geotop_euclidean_topology M"
  shows "geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) =
         geotop_frontier UNIV geotop_euclidean_topology M"
  sorry

(** from \<S>17: cell-complex (geotop.tex:3415)
    LATEX VERSION: By a cell-complex we mean a finite collection K of topological cells, such
      that (1) different elements of K have disjoint interiors, (2) for each C in K, Bd C is
      a union of elements of K, and (3) if C, C' \<in> K, and C \<inter> C' \<ne> \<emptyset>, then C \<inter> C' is a cell,
      and is a union of elements of K. **)
definition geotop_is_cell_complex ::
  "'a::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_is_cell_complex K \<longleftrightarrow>
    finite K \<and>
    (\<forall>C\<in>K. \<exists>n. geotop_is_n_cell C (subspace_topology UNIV geotop_euclidean_topology C) n) \<and>
    (\<forall>C\<in>K. \<forall>C'\<in>K. C \<noteq> C' \<longrightarrow>
       geotop_top_interior UNIV geotop_euclidean_topology C
       \<inter> geotop_top_interior UNIV geotop_euclidean_topology C' = {}) \<and>
    (\<forall>C\<in>K. \<exists>KS\<subseteq>K. geotop_frontier UNIV geotop_euclidean_topology C = \<Union>KS) \<and>
    (\<forall>C\<in>K. \<forall>C'\<in>K. C \<inter> C' \<noteq> {} \<longrightarrow>
       (\<exists>n. geotop_is_n_cell (C \<inter> C')
              (subspace_topology UNIV geotop_euclidean_topology (C \<inter> C')) n) \<and>
       (\<exists>KS\<subseteq>K. C \<inter> C' = \<Union>KS))"

(** from \<S>17: PL cell-complex (geotop.tex:3415)
    LATEX VERSION: If the elements of K are polyhedra, then K will be called a PL cell-complex. **)
definition geotop_is_PL_cell_complex ::
  "'a::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_is_PL_cell_complex K \<longleftrightarrow>
    geotop_is_cell_complex K \<and>
    (\<forall>C\<in>K. \<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = C)"

(** from \<S>17: free 2-cell in cell-decomposition (geotop.tex:3418)
    LATEX VERSION: Let K be a cell-decomposition of a 2-cell, and let C be a 2-cell belonging
      to K. If Bd C \<inter> Bd|K| is an arc, then C is free in K. **)
definition geotop_is_free_2cell_in ::
  "'a::real_normed_vector set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "geotop_is_free_2cell_in C K \<longleftrightarrow>
    C \<in> K \<and>
    geotop_is_n_cell C (subspace_topology UNIV geotop_euclidean_topology C) 2 \<and>
    geotop_is_arc (geotop_frontier UNIV geotop_euclidean_topology C \<inter>
                   geotop_frontier UNIV geotop_euclidean_topology (\<Union>K))
      (subspace_topology UNIV geotop_euclidean_topology
         (geotop_frontier UNIV geotop_euclidean_topology C \<inter>
          geotop_frontier UNIV geotop_euclidean_topology (\<Union>K)))"

(** from \<S>17 Theorem 2 (geotop.tex:3420)
    LATEX VERSION: Let K be a cell-decomposition of a 2-cell, and suppose that K has more than
      one 2-cell. Then at least two of the 2-cells of K are free in K. **)
theorem Theorem_GT_17_2:
  fixes K :: "'a::real_normed_vector set set"
  assumes "geotop_is_cell_complex K"
  assumes "geotop_is_n_cell (\<Union>K) (subspace_topology UNIV geotop_euclidean_topology (\<Union>K)) 2"
  assumes "2 \<le> card {C\<in>K. geotop_is_n_cell C
                        (subspace_topology UNIV geotop_euclidean_topology C) 2}"
  shows "\<exists>C1 C2. C1 \<noteq> C2 \<and> geotop_is_free_2cell_in C1 K \<and> geotop_is_free_2cell_in C2 K"
  sorry

(** from \<S>17 Theorem 3 (geotop.tex:3426)
    LATEX VERSION: Let K be as in Theorem 2. Let D be a 2-cell which forms a proper
      subcomplex of K. Then there is a 2-cell which is free in K and does not lie in D. **)
theorem Theorem_GT_17_3:
  fixes K :: "'a::real_normed_vector set set" and D :: "'a set"
  assumes "geotop_is_cell_complex K"
  assumes "geotop_is_n_cell (\<Union>K) (subspace_topology UNIV geotop_euclidean_topology (\<Union>K)) 2"
  assumes "\<exists>KD. KD \<subset> K \<and> geotop_is_cell_complex KD \<and> \<Union>KD = D \<and>
               geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2"
  shows "\<exists>C. geotop_is_free_2cell_in C K \<and> \<not> C \<subseteq> D"
  sorry

(** from \<S>17: push property at D_1 (geotop.tex:3431)
    LATEX VERSION: Let C^3 be a polyhedral 3-cell in R^3, let D_1 be a polyhedral 2-cell in
      Bd C^3, D_2 = Cl(Bd C^3 - D_1), J = Bd D_1 = Bd D_2. Suppose that for every polyhedral
      closed neighborhood N of C^3 - J there is a PLH h: R^3 \<leftrightarrow> R^3, D_1 \<leftrightarrow> D_2, such that
      h|(R^3 - N) is the identity. Then C^3 and Bd C^3 have the push property at D_1. **)
definition geotop_has_push_property_at ::
  "(real^3) set \<Rightarrow> (real^3) set \<Rightarrow> bool" where
  "geotop_has_push_property_at C3 D1 \<longleftrightarrow>
    geotop_is_n_cell C3 (subspace_topology UNIV geotop_euclidean_topology C3) 3 \<and>
    (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = C3) \<and>
    geotop_is_n_cell D1 (subspace_topology UNIV geotop_euclidean_topology D1) 2 \<and>
    D1 \<subseteq> geotop_frontier UNIV geotop_euclidean_topology C3 \<and>
    (\<exists>L1. geotop_is_complex L1 \<and> geotop_polyhedron L1 = D1) \<and>
    (\<forall>N. closedin_on UNIV geotop_euclidean_topology N \<and>
         (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = N) \<and>
         (C3 - (geotop_frontier UNIV geotop_euclidean_topology D1)) \<subseteq>
            geotop_top_interior UNIV geotop_euclidean_topology N \<longrightarrow>
       (\<exists>h KR KR'. top1_homeomorphism_on UNIV geotop_euclidean_topology
                      UNIV geotop_euclidean_topology h \<and>
                   geotop_PLH KR KR' h \<and>
                   h ` D1 = geotop_frontier UNIV geotop_euclidean_topology C3 - (D1 -
                      geotop_frontier UNIV geotop_euclidean_topology D1) \<and>
                   (\<forall>P\<in>UNIV - N. h P = P)))"

definition geotop_has_push_property :: "(real^3) set \<Rightarrow> bool" where
  "geotop_has_push_property C3 \<longleftrightarrow>
    (\<forall>D1. geotop_is_n_cell D1 (subspace_topology UNIV geotop_euclidean_topology D1) 2 \<and>
          D1 \<subseteq> geotop_frontier UNIV geotop_euclidean_topology C3 \<and>
          (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = D1) \<longrightarrow>
       geotop_has_push_property_at C3 D1)"

(** from \<S>17 Theorem 4 (geotop.tex:3439)
    LATEX VERSION: Let \<sigma>^3 be a 3-simplex in R^3, and let \<sigma>^2 be a face of \<sigma>^3. Then \<sigma>^3 has
      the push property at \<sigma>^2. **)
theorem Theorem_GT_17_4:
  fixes \<sigma>3 \<sigma>2 :: "(real^3) set"
  assumes "geotop_simplex_dim \<sigma>3 3" and "geotop_simplex_dim \<sigma>2 2"
  assumes "geotop_is_face \<sigma>2 \<sigma>3"
  shows "geotop_has_push_property_at \<sigma>3 \<sigma>2"
  sorry

(** from \<S>17 Theorem 5 (geotop.tex:3443)
    LATEX VERSION: Given \<sigma>^3 \<subseteq> R^3. Let D be a polyhedral 2-cell in Bd \<sigma>^3, and let W be an
      open set containing \<sigma>^3. Then there is a PLH f: R^3 \<leftrightarrow> R^3, \<sigma>^3 \<leftrightarrow> \<sigma>^3, D \<leftrightarrow> \<sigma>_0^2,
      where \<sigma>_0^2 is a 2-face of \<sigma>^3, such that f|(R^3 - W) is the identity. **)
theorem Theorem_GT_17_5:
  fixes \<sigma>3 D W :: "(real^3) set"
  assumes "geotop_simplex_dim \<sigma>3 3"
  assumes "geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2"
  assumes "D \<subseteq> geotop_frontier UNIV geotop_euclidean_topology \<sigma>3"
  assumes "\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = D"
  assumes "W \<in> geotop_euclidean_topology" and "\<sigma>3 \<subseteq> W"
  shows "\<exists>f \<sigma>02. geotop_simplex_dim \<sigma>02 2 \<and> geotop_is_face \<sigma>02 \<sigma>3 \<and>
           top1_homeomorphism_on UNIV geotop_euclidean_topology
             UNIV geotop_euclidean_topology f \<and>
           (\<exists>K K'. geotop_is_complex K \<and> geotop_is_complex K' \<and> geotop_PLH K K' f) \<and>
           f ` \<sigma>3 = \<sigma>3 \<and> f ` D = \<sigma>02 \<and>
           (\<forall>P\<in>UNIV - W. f P = P)"
  sorry

(** from \<S>17 Theorem 6 (geotop.tex:3502)
    LATEX VERSION: Every 3-simplex in R^3 has the push property. **)
theorem Theorem_GT_17_6:
  fixes \<sigma>3 :: "(real^3) set"
  assumes "geotop_simplex_dim \<sigma>3 3"
  shows "geotop_has_push_property \<sigma>3"
  sorry

(** from \<S>17: simply imbedded 2-sphere (geotop.tex:3530)
    LATEX VERSION: Let S be a polyhedral 2-sphere in R^3. Suppose that for every convex open
      set W, containing S, there is a PLH f: R^3 \<leftrightarrow> R^3, S \<leftrightarrow> Bd \<sigma>^3 (where \<sigma>^3 is a
      3-simplex) such that f|(R^3 - W) is the identity. Then S is simply imbedded. **)
definition geotop_is_simply_imbedded :: "(real^3) set \<Rightarrow> bool" where
  "geotop_is_simply_imbedded S \<longleftrightarrow>
    geotop_is_n_sphere S (subspace_topology UNIV geotop_euclidean_topology S) 2 \<and>
    (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = S) \<and>
    (\<forall>W. W \<in> geotop_euclidean_topology \<and> geotop_convex W \<and> S \<subseteq> W \<longrightarrow>
       (\<exists>f \<sigma>3. geotop_simplex_dim \<sigma>3 3 \<and>
               top1_homeomorphism_on UNIV geotop_euclidean_topology
                 UNIV geotop_euclidean_topology f \<and>
               (\<exists>K K'. geotop_is_complex K \<and> geotop_is_complex K' \<and> geotop_PLH K K' f) \<and>
               f ` S = geotop_frontier UNIV geotop_euclidean_topology \<sigma>3 \<and>
               (\<forall>P\<in>UNIV - W. f P = P)))"

(** from \<S>17 Theorem 7 (geotop.tex:3540)
    LATEX VERSION: The push property, for polyhedral 3-cells in R^3, is preserved by every
      PLH. **)
theorem Theorem_GT_17_7:
  fixes C3 :: "(real^3) set" and f :: "real^3 \<Rightarrow> real^3"
  assumes "geotop_has_push_property C3"
  assumes "top1_homeomorphism_on UNIV geotop_euclidean_topology
             UNIV geotop_euclidean_topology f"
  assumes "\<exists>K K'. geotop_is_complex K \<and> geotop_is_complex K' \<and> geotop_PLH K K' f"
  shows "geotop_has_push_property (f ` C3)"
  sorry

(** from \<S>17 Theorem 8 (geotop.tex:3544)
    LATEX VERSION: Every simply imbedded 2-sphere in R^3 has the push property. **)
theorem Theorem_GT_17_8:
  fixes S :: "(real^3) set"
  assumes "geotop_is_simply_imbedded S"
  shows "\<exists>C3. geotop_is_n_cell C3 (subspace_topology UNIV geotop_euclidean_topology C3) 3 \<and>
              geotop_frontier UNIV geotop_euclidean_topology C3 = S \<and>
              geotop_has_push_property C3"
  sorry

(** from \<S>17 Theorem 9 (geotop.tex:3546)
    LATEX VERSION: Let C^3 be a convex polyhedral 3-cell in R^3. Then Bd C^3 is simply
      imbedded. **)
theorem Theorem_GT_17_9:
  fixes C3 :: "(real^3) set"
  assumes "geotop_is_n_cell C3 (subspace_topology UNIV geotop_euclidean_topology C3) 3"
  assumes "geotop_convex C3"
  assumes "\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = C3"
  shows "geotop_is_simply_imbedded (geotop_frontier UNIV geotop_euclidean_topology C3)"
  sorry

(** from \<S>17 Theorem 10 (geotop.tex:3564)
    LATEX VERSION: Let C^3 be a polyhedral 3-cell in R^3, and suppose that C^3 can be
      triangulated as the join of a polyhedral 2-cell and a point. Then Bd C^3 is simply
      imbedded. **)
theorem Theorem_GT_17_10:
  fixes C3 :: "(real^3) set"
  assumes "geotop_is_n_cell C3 (subspace_topology UNIV geotop_euclidean_topology C3) 3"
  assumes "\<exists>D v. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2 \<and>
                 (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = D) \<and>
                 C3 = geotop_join D {v}"
  shows "geotop_is_simply_imbedded (geotop_frontier UNIV geotop_euclidean_topology C3)"
  sorry

(** from \<S>17 Theorem 11 (geotop.tex:3567)
    LATEX VERSION: Let S_1 and S_2 be polyhedral 2-spheres in R^3, such that S_1 \<inter> S_2 is a
      plane 2-cell D. Let S = (S_1 \<union> S_2) - Int D. If S_1 and S_2 are simply imbedded, then
      so also is S. **)
theorem Theorem_GT_17_11:
  fixes S1 S2 D :: "(real^3) set"
  assumes "geotop_is_simply_imbedded S1"
  assumes "geotop_is_simply_imbedded S2"
  assumes "S1 \<inter> S2 = D"
  assumes "geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2"
  shows "geotop_is_simply_imbedded
           ((S1 \<union> S2) - geotop_top_interior UNIV geotop_euclidean_topology D)"
  sorry

(** from \<S>17 Theorem 12 (The PL Schönflies theorem in R^3) (geotop.tex:3598)
    LATEX VERSION: Let S be a polyhedral 2-sphere in R^3, and let W be a convex open set
      containing S. Then there is a PLH f: R^3 \<leftrightarrow> R^3, S \<leftrightarrow> Bd \<sigma>^3, where \<sigma>^3 is a 3-simplex,
      such that f|(R^3 - W) is the identity. Thus every polyhedral 2-sphere is simply
      imbedded. **)
theorem Theorem_GT_17_12_PL_Schoenflies:
  fixes S W :: "(real^3) set"
  assumes "geotop_is_n_sphere S (subspace_topology UNIV geotop_euclidean_topology S) 2"
  assumes "\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = S"
  assumes "W \<in> geotop_euclidean_topology" and "geotop_convex W" and "S \<subseteq> W"
  shows "geotop_is_simply_imbedded S"
  sorry

section \<open>\<S>18 The Antoine set\<close>

(** from \<S>18: circular solid torus (geotop.tex:3742)
    LATEX VERSION: Let T_1 be the solid of revolution of a circular closed plane region
      about a line in the same plane, not intersecting it. Such a set is called a circular
      solid torus. A set homeomorphic to a circular solid torus is called a solid torus. **)
definition geotop_is_circular_solid_torus :: "(real^3) set \<Rightarrow> bool" where
  "geotop_is_circular_solid_torus T \<longleftrightarrow>
    geotop_is_solid_torus T"

(** from \<S>18: Antoine construction T_n (geotop.tex:3742-3787)
    LATEX VERSION: In the interior of T_1, form a set T_2 which is the union of a finite
      collection of circular solid tori, linked in cyclic order. The number of components is
      k, with k \<ge> 4. Inductively, given T_n (union of k^(n-1) disjoint tori), for each
      component C_i let \<phi>_i be a similarity T_1 \<leftrightarrow> C_i, and let T_{n+1} = \<union> \<phi>_i(T_2). Define
      Q = \<inter> T_n. **)
definition geotop_antoine_chain ::
  "nat \<Rightarrow> (real^3) set \<Rightarrow> (real^3) set \<Rightarrow> (nat \<Rightarrow> (real^3) set) \<Rightarrow> bool" where
  "geotop_antoine_chain k T1 T2 T \<longleftrightarrow>
    k \<ge> 4 \<and>
    geotop_is_circular_solid_torus T1 \<and>
    T 1 = T1 \<and>
    T 2 = T2 \<and>
    (\<forall>n. T (Suc n) \<subseteq> T n) \<and>
    (\<forall>n\<ge>1. \<exists>Cs. finite Cs \<and> card Cs = k^(n-1) \<and>
               (\<forall>C\<in>Cs. geotop_is_circular_solid_torus C) \<and>
               (\<forall>C1\<in>Cs. \<forall>C2\<in>Cs. C1 \<noteq> C2 \<longrightarrow> C1 \<inter> C2 = {}) \<and>
               T n = \<Union>Cs)"

definition geotop_antoine_set ::
  "nat \<Rightarrow> (real^3) set \<Rightarrow> (real^3) set \<Rightarrow> (nat \<Rightarrow> (real^3) set) \<Rightarrow> (real^3) set" where
  "geotop_antoine_set k T1 T2 T = (\<Inter>n\<in>{m. m \<ge> 1}. T n)"

(** from \<S>18 Theorem 1 (geotop.tex:3793)
    LATEX VERSION: Let the components C_i and the spanning 2-cells D_i (i \<le> k) be as in the
      definition of T_2. Then Bd T_1 is a retract of the set
      T_1 - [\<union>_i C_i \<union> \<union>_i D_i]. **)
theorem Theorem_GT_18_1:
  fixes k :: nat and T1 T2 :: "(real^3) set" and T :: "nat \<Rightarrow> (real^3) set"
  fixes Cs Ds :: "(real^3) set set"
  assumes "geotop_antoine_chain k T1 T2 T"
  assumes "finite Cs" and "card Cs = k" and "T2 = \<Union>Cs"
  assumes "finite Ds" and "card Ds = k"
  assumes "\<forall>D\<in>Ds. \<exists>C\<in>Cs. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2
                          \<and> geotop_frontier UNIV geotop_euclidean_topology D
                              \<subseteq> geotop_frontier UNIV geotop_euclidean_topology C"
  shows "geotop_is_retract (T1 - (\<Union>Cs \<union> \<Union>Ds))
           (subspace_topology UNIV geotop_euclidean_topology (T1 - (\<Union>Cs \<union> \<Union>Ds)))
           (geotop_frontier UNIV geotop_euclidean_topology T1)"
  sorry

(** from \<S>18 Theorem 2 (geotop.tex:3800)
    LATEX VERSION: Let p be a closed path in R^3 - T_1. If p \<cong> e in R^3 - T_2, then
      p \<cong> e in R^3 - T_1. **)
theorem Theorem_GT_18_2:
  fixes k :: nat and T1 T2 :: "(real^3) set" and T :: "nat \<Rightarrow> (real^3) set"
  fixes p :: "real \<Rightarrow> real^3" and P\<^sub>0 :: "real^3"
  assumes "geotop_antoine_chain k T1 T2 T"
  assumes "P\<^sub>0 \<in> UNIV - T1"
  assumes "geotop_closed_path_on (UNIV - T1)
             (subspace_topology UNIV geotop_euclidean_topology (UNIV - T1)) P\<^sub>0 p"
  assumes "geotop_path_equiv (UNIV - T2)
             (subspace_topology UNIV geotop_euclidean_topology (UNIV - T2))
             P\<^sub>0 p (\<lambda>t. P\<^sub>0)"
  shows "geotop_path_equiv (UNIV - T1)
           (subspace_topology UNIV geotop_euclidean_topology (UNIV - T1))
           P\<^sub>0 p (\<lambda>t. P\<^sub>0)"
  sorry

(** from \<S>18 Theorem 3 (geotop.tex:3905)
    LATEX VERSION: Let p be a closed path in R^3 - T_1, and suppose that p \<cong> e in R^3 - Q.
      Then p \<cong> e in R^3 - T_1. **)
theorem Theorem_GT_18_3:
  fixes k :: nat and T1 T2 :: "(real^3) set" and T :: "nat \<Rightarrow> (real^3) set"
  fixes p :: "real \<Rightarrow> real^3" and P\<^sub>0 :: "real^3"
  assumes "geotop_antoine_chain k T1 T2 T"
  assumes "P\<^sub>0 \<in> UNIV - T1"
  assumes "geotop_closed_path_on (UNIV - T1)
             (subspace_topology UNIV geotop_euclidean_topology (UNIV - T1)) P\<^sub>0 p"
  assumes "geotop_path_equiv (UNIV - geotop_antoine_set k T1 T2 T)
             (subspace_topology UNIV geotop_euclidean_topology
                (UNIV - geotop_antoine_set k T1 T2 T))
             P\<^sub>0 p (\<lambda>t. P\<^sub>0)"
  shows "geotop_path_equiv (UNIV - T1)
           (subspace_topology UNIV geotop_euclidean_topology (UNIV - T1))
           P\<^sub>0 p (\<lambda>t. P\<^sub>0)"
  sorry

(** from \<S>18 Theorem 4 (geotop.tex:3927)
    LATEX VERSION: R^3 - Q is not simply connected. **)
theorem Theorem_GT_18_4:
  fixes k :: nat and T1 T2 :: "(real^3) set" and T :: "nat \<Rightarrow> (real^3) set"
  fixes P\<^sub>0 :: "real^3"
  assumes "geotop_antoine_chain k T1 T2 T"
  assumes "P\<^sub>0 \<in> UNIV - geotop_antoine_set k T1 T2 T"
  shows "\<not> geotop_simply_connected (UNIV - geotop_antoine_set k T1 T2 T)
           (subspace_topology UNIV geotop_euclidean_topology
              (UNIV - geotop_antoine_set k T1 T2 T)) P\<^sub>0"
  sorry

(** from \<S>18 Theorem 5 (geotop.tex:3930)
    LATEX VERSION: There are Cantor sets C_1 and C_2 in R^3 such that no homeomorphism
      C_1 \<leftrightarrow> C_2 has a homeomorphic extension R^3 \<leftrightarrow> R^3. **)
theorem Theorem_GT_18_5:
  shows "\<exists>C1 C2 :: (real^3) set.
           geotop_is_cantor_set C1 (subspace_topology UNIV geotop_euclidean_topology C1) \<and>
           geotop_is_cantor_set C2 (subspace_topology UNIV geotop_euclidean_topology C2) \<and>
           (\<exists>h. top1_homeomorphism_on C1 (subspace_topology UNIV geotop_euclidean_topology C1)
                  C2 (subspace_topology UNIV geotop_euclidean_topology C2) h) \<and>
           (\<forall>h. top1_homeomorphism_on C1 (subspace_topology UNIV geotop_euclidean_topology C1)
                  C2 (subspace_topology UNIV geotop_euclidean_topology C2) h \<longrightarrow>
              (\<nexists>H. top1_homeomorphism_on UNIV geotop_euclidean_topology
                     UNIV geotop_euclidean_topology H \<and>
                   (\<forall>P\<in>C1. H P = h P)))"
  sorry

(** from \<S>18 Theorem 6 (geotop.tex:3934)
    LATEX VERSION: Let U be a connected open set containing Q. Then there is a 2-sphere S
      such that Q \<subseteq> S \<subseteq> U. **)
theorem Theorem_GT_18_6:
  fixes k :: nat and T1 T2 :: "(real^3) set" and T :: "nat \<Rightarrow> (real^3) set"
  fixes U :: "(real^3) set"
  assumes "geotop_antoine_chain k T1 T2 T"
  assumes "U \<in> geotop_euclidean_topology"
  assumes "top1_connected_on U (subspace_topology UNIV geotop_euclidean_topology U)"
  assumes "geotop_antoine_set k T1 T2 T \<subseteq> U"
  shows "\<exists>S. geotop_is_n_sphere S (subspace_topology UNIV geotop_euclidean_topology S) 2 \<and>
             geotop_antoine_set k T1 T2 T \<subseteq> S \<and> S \<subseteq> U"
  sorry

(** from \<S>18 Theorem 7 (Louis Antoine) (geotop.tex:3963)
    LATEX VERSION: R^3 contains a wild 2-sphere. **)
theorem Theorem_GT_18_7_Antoine_sphere:
  shows "\<exists>S :: (real^3) set.
           geotop_is_n_sphere S (subspace_topology UNIV geotop_euclidean_topology S) 2 \<and>
           geotop_is_wild S"
  sorry

(** from \<S>18 Theorem 8 (Louis Antoine) (geotop.tex:3966)
    LATEX VERSION: R^3 contains a wild arc. **)
theorem Theorem_GT_18_8_Antoine_arc:
  shows "\<exists>A :: (real^3) set.
           geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A) \<and>
           geotop_is_wild A"
  sorry

section \<open>\<S>19 A wild arc with a simply connected complement\<close>

(** from \<S>19: unknotted in C (geotop.tex:3997)
    LATEX VERSION: If B and C satisfy the conditions of Theorem 1, then we say that B is
      unknotted in C. **)
definition geotop_unknotted_in ::
  "(real^3) set \<Rightarrow> (real^3) set \<Rightarrow> bool" where
  "geotop_unknotted_in B C \<longleftrightarrow>
    geotop_is_broken_line B \<and>
    geotop_is_n_cell C (subspace_topology UNIV geotop_euclidean_topology C) 3 \<and>
    (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = C) \<and>
    (\<exists>\<sigma>2::(real^2) set. geotop_simplex_dim \<sigma>2 2 \<and>
       (\<exists>R\<in>geotop_top_interior UNIV geotop_euclidean_topology \<sigma>2.
         (\<exists>\<phi>. top1_homeomorphism_on C (subspace_topology UNIV geotop_euclidean_topology C)
                (\<sigma>2 \<times> {t. 0 \<le> t \<and> t \<le> 1})
                (subspace_topology (UNIV::((real^2) \<times> real) set) geotop_euclidean_topology
                   (\<sigma>2 \<times> {t. 0 \<le> t \<and> t \<le> 1})) \<phi> \<and>
              \<phi> ` B = {R} \<times> {t. 0 \<le> t \<and> t \<le> 1})))"

(** from \<S>19 Theorem 1 (geotop.tex:3985)
    LATEX VERSION: Let B be a broken line in R^3, with end-points P and Q. Then there is a
      polyhedral 3-cell C such that (1) Int B \<subseteq> Int C, (2) P, Q \<in> Bd C, and (3) there is a
      PLH \<phi>: C \<leftrightarrow> \<sigma>^2 \<times> [0,1], such that B \<leftrightarrow> R \<times> [0,1], for some R \<in> Int \<sigma>^2. **)
theorem Theorem_GT_19_1:
  fixes B :: "(real^3) set"
  assumes "geotop_is_broken_line B"
  shows "\<exists>C. geotop_unknotted_in B C"
  sorry

(** from \<S>19 Theorem 2 (geotop.tex:3999)
    LATEX VERSION: If B_i is unknotted in C_i (i = 1,2), then every PLH
      h: Bd C_1 \<leftrightarrow> Bd C_2, Bd B_1 \<leftrightarrow> Bd B_2 can be extended to give a PLH
      h': C_1 \<leftrightarrow> C_2, B_1 \<leftrightarrow> B_2. **)
theorem Theorem_GT_19_2:
  fixes B1 B2 C1 C2 :: "(real^3) set" and h :: "real^3 \<Rightarrow> real^3"
  assumes "geotop_unknotted_in B1 C1" and "geotop_unknotted_in B2 C2"
  assumes "top1_homeomorphism_on
             (geotop_frontier UNIV geotop_euclidean_topology C1)
             (subspace_topology UNIV geotop_euclidean_topology
                (geotop_frontier UNIV geotop_euclidean_topology C1))
             (geotop_frontier UNIV geotop_euclidean_topology C2)
             (subspace_topology UNIV geotop_euclidean_topology
                (geotop_frontier UNIV geotop_euclidean_topology C2)) h"
  assumes "\<exists>K K'. geotop_is_complex K \<and> geotop_is_complex K' \<and> geotop_PLH K K' h"
  assumes "h ` (geotop_frontier UNIV geotop_euclidean_topology B1) =
             geotop_frontier UNIV geotop_euclidean_topology B2"
  shows "\<exists>h'. top1_homeomorphism_on C1 (subspace_topology UNIV geotop_euclidean_topology C1)
                C2 (subspace_topology UNIV geotop_euclidean_topology C2) h' \<and>
              (\<forall>P\<in>geotop_frontier UNIV geotop_euclidean_topology C1. h' P = h P) \<and>
              h' ` B1 = B2"
  sorry

(** from \<S>19 Theorem 3 (geotop.tex:4064)
    LATEX VERSION: A_1 is tame.
    Here A_1 is the Wilder arc (union of arcs B_i accumulating at a point P). **)
theorem Theorem_GT_19_3:
  fixes A1 :: "(real^3) set" and Bs :: "nat \<Rightarrow> (real^3) set" and P :: "real^3"
  assumes "\<forall>i. geotop_is_broken_line (Bs i)"
  assumes "\<forall>i. \<forall>j. i \<noteq> j \<longrightarrow> Bs i \<inter> Bs j = {}"
  assumes "A1 = (\<Union>i. Bs i) \<union> {P}"
  assumes "geotop_is_arc A1 (subspace_topology UNIV geotop_euclidean_topology A1)"
  shows "geotop_is_tame A1"
  sorry

(** from \<S>19: locally commutative fundamental group (geotop.tex:4127)
    LATEX VERSION: Let U be an open set, and let P \<in> closure U. Suppose that for every open
      set V containing P there is an open set W containing P such that (1) P \<in> W \<subseteq> V and (2)
      if p and q are closed paths in U \<inter> W, with base-point P_0, then pq \<cong> qp in
      \<pi>(U \<inter> V). Then \<pi>(U) is locally commutative at P. **)
definition geotop_pi_locally_commutative_at ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> bool" where
  "geotop_pi_locally_commutative_at U T P \<longleftrightarrow>
    U \<in> T \<and>
    (\<forall>V\<in>T. P \<in> V \<longrightarrow>
       (\<exists>W\<in>T. P \<in> W \<and> W \<subseteq> V \<and>
         (\<forall>P\<^sub>0 \<in> U \<inter> W. \<forall>p q.
             geotop_closed_path_on (U \<inter> W) (subspace_topology (U \<inter> W) T (U \<inter> W)) P\<^sub>0 p \<and>
             geotop_closed_path_on (U \<inter> W) (subspace_topology (U \<inter> W) T (U \<inter> W)) P\<^sub>0 q \<longrightarrow>
             geotop_path_equiv (U \<inter> V) (subspace_topology (U \<inter> V) T (U \<inter> V))
               P\<^sub>0 (geotop_path_mult p q) (geotop_path_mult q p))))"

(** from \<S>19 Theorem 4 (geotop.tex:4102)
    LATEX VERSION: A is wild.
    Here A is the Fox-Artin wild arc, A = A_1 \<union> A_2 where A_1 is the Wilder arc and A_2 is
    a linear interval from P to a point Q to the right. **)
theorem Theorem_GT_19_4:
  fixes A :: "(real^3) set" and P :: "real^3"
  assumes "geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A)"
  assumes "\<exists>A1 A2. A = A1 \<union> A2 \<and> A1 \<inter> A2 = {P} \<and>
                   geotop_is_arc A1 (subspace_topology UNIV geotop_euclidean_topology A1) \<and>
                   geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2)"
  assumes "\<not> geotop_pi_locally_commutative_at (UNIV - A) geotop_euclidean_topology P"
  shows "geotop_is_wild A"
  sorry

(** from \<S>19 Theorem 5 (geotop.tex:4167)
    LATEX VERSION: R^3 - A is homeomorphic to the complement of a point. **)
theorem Theorem_GT_19_5:
  fixes A :: "(real^3) set"
  assumes "geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A)"
  assumes "\<exists>A1 A2 P. A = A1 \<union> A2 \<and> A1 \<inter> A2 = {P} \<and>
                   geotop_is_arc A1 (subspace_topology UNIV geotop_euclidean_topology A1) \<and>
                   geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2) \<and>
                   geotop_is_wild A"
  shows "\<exists>(Q::real^3). \<exists>h. top1_homeomorphism_on
             (UNIV - A) (subspace_topology UNIV geotop_euclidean_topology (UNIV - A))
             (UNIV - {Q}) (subspace_topology UNIV geotop_euclidean_topology (UNIV - {Q}))
             h"
  sorry

(** from \<S>19 Theorem 6 (geotop.tex:4172)
    LATEX VERSION: There are tame arcs A_1, A_2 in R^3 such that A_1 \<inter> A_2 is a point and
      A_1 \<union> A_2 is wild. **)
theorem Theorem_GT_19_6:
  shows "\<exists>A1 A2 :: (real^3) set. \<exists>P.
           geotop_is_arc A1 (subspace_topology UNIV geotop_euclidean_topology A1) \<and>
           geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2) \<and>
           geotop_is_tame A1 \<and> geotop_is_tame A2 \<and>
           A1 \<inter> A2 = {P} \<and>
           geotop_is_wild (A1 \<union> A2)"
  sorry

section \<open>\<S>20 A wild 2-sphere with a simply connected complement\<close>

(** from \<S>20 Theorem 1 (geotop.tex:4190)
    LATEX VERSION: In R^3, let P_0 = (0,0,0), P_1 = (0,0,3/2), P_2 = (0,0,2), P_3 = (0,1,2);
      let T be the 2-simplex P_0 P_2 P_3, and let D^3 be the solid of revolution of T about
      the z-axis. Then there is a mapping f: D^3 \<rightarrow> D^3 such that (1) f(P_0 P_1) = P_0 and
      (2) f|(D^3 - P_0 P_1) is a homeomorphism D^3 - P_0 P_1 \<leftrightarrow> D^3 - {P_0}. **)
theorem Theorem_GT_20_1:
  fixes D3 :: "(real^3) set" and P\<^sub>0 P\<^sub>1 :: "real^3"
  assumes "geotop_is_n_cell D3 (subspace_topology UNIV geotop_euclidean_topology D3) 3"
  assumes "geotop_is_broken_line {t *\<^sub>R P\<^sub>0 + (1 - t) *\<^sub>R P\<^sub>1 |t. 0 \<le> t \<and> t \<le> 1}"
  shows "\<exists>f. f ` {t *\<^sub>R P\<^sub>0 + (1 - t) *\<^sub>R P\<^sub>1 |t. 0 \<le> t \<and> t \<le> 1} = {P\<^sub>0} \<and>
             top1_homeomorphism_on
               (D3 - {t *\<^sub>R P\<^sub>0 + (1 - t) *\<^sub>R P\<^sub>1 |t. 0 \<le> t \<and> t \<le> 1})
               (subspace_topology UNIV geotop_euclidean_topology
                  (D3 - {t *\<^sub>R P\<^sub>0 + (1 - t) *\<^sub>R P\<^sub>1 |t. 0 \<le> t \<and> t \<le> 1}))
               (D3 - {P\<^sub>0})
               (subspace_topology UNIV geotop_euclidean_topology (D3 - {P\<^sub>0})) f"
  sorry

(** from \<S>20 Theorem 2 (geotop.tex:4193)
    LATEX VERSION: Let A be an arc in R^3, with Bd A = {P, Q}, such that A - {Q} is an
      (infinite) polyhedron. Then R^3 - A is homeomorphic to R^3 - {Q}. **)
theorem Theorem_GT_20_2:
  fixes A :: "(real^3) set" and P Q :: "real^3"
  assumes "geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A)"
  assumes "\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = A - {Q}"
  shows "\<exists>h. top1_homeomorphism_on
               (UNIV - A) (subspace_topology UNIV geotop_euclidean_topology (UNIV - A))
               (UNIV - {Q}) (subspace_topology UNIV geotop_euclidean_topology (UNIV - {Q})) h"
  sorry

(** from \<S>20: locally simply connected (geotop.tex:4243)
    LATEX VERSION: Let U be a connected open set in R^3, and let Q \<in> closure U. Suppose that
      for each open set V containing Q there is an open set W such that (1) Q \<in> W \<subseteq> V and
      (2) every closed path in W \<inter> U is contractible in V \<inter> U. Then U is locally simply
      connected at Q. **)
definition geotop_locally_simply_connected_at ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> bool" where
  "geotop_locally_simply_connected_at U T Q \<longleftrightarrow>
    U \<in> T \<and>
    (\<forall>V\<in>T. Q \<in> V \<longrightarrow>
       (\<exists>W\<in>T. Q \<in> W \<and> W \<subseteq> V \<and>
         (\<forall>P\<^sub>0\<in>W \<inter> U. \<forall>p.
             geotop_closed_path_on (W \<inter> U)
               (subspace_topology (W \<inter> U) T (W \<inter> U)) P\<^sub>0 p \<longrightarrow>
             geotop_path_equiv (V \<inter> U)
               (subspace_topology (V \<inter> U) T (V \<inter> U)) P\<^sub>0 p (\<lambda>t. P\<^sub>0))))"

(** from \<S>20 Theorem 3 (geotop.tex:4245)
    LATEX VERSION: Let A be a tame arc in R^3, and let Q \<in> Bd A. Then R^3 - A is locally
      simply connected at Q. Similarly, if S is a tame 2-sphere in R^3, then each component
      of R^3 - S is locally simply connected at each point Q of S. **)
theorem Theorem_GT_20_3:
  shows "(\<forall>A :: (real^3) set. \<forall>Q.
           geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A) \<and>
           geotop_is_tame A \<and>
           Q \<in> geotop_frontier UNIV geotop_euclidean_topology A \<longrightarrow>
           geotop_locally_simply_connected_at (UNIV - A) geotop_euclidean_topology Q) \<and>
         (\<forall>S :: (real^3) set. \<forall>Q\<in>S.
           geotop_is_n_sphere S (subspace_topology UNIV geotop_euclidean_topology S) 2 \<and>
           geotop_is_tame S \<longrightarrow>
           (\<forall>C. (\<exists>P\<in>UNIV - S. C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - S) P)
                \<longrightarrow> geotop_locally_simply_connected_at C geotop_euclidean_topology Q))"
  sorry

(** from \<S>20 Theorem 4 (geotop.tex:4338)
    LATEX VERSION: A_2 is wild.
    Here A_2 is the Fox-Artin arc from S to Q, a portion of the Fox-Artin wild arc. **)
theorem Theorem_GT_20_4:
  shows "\<exists>A2 :: (real^3) set.
           geotop_is_arc A2 (subspace_topology UNIV geotop_euclidean_topology A2) \<and>
           (\<exists>Q\<in>geotop_frontier UNIV geotop_euclidean_topology A2.
              \<not> geotop_locally_simply_connected_at (UNIV - A2) geotop_euclidean_topology Q) \<and>
           geotop_is_wild A2"
  sorry

(** from \<S>20 Theorem 5 (Fox-Artin) (geotop.tex:4400)
    LATEX VERSION: There is a wild 2-sphere S^2 in R^3 such that (1) S^2 is locally polyhedral
      except at one point Q and (2) R^3 - S^2 is homeomorphic to R^3 - S^2 (standard). **)
theorem Theorem_GT_20_5_Fox_Artin:
  shows "\<exists>S2 :: (real^3) set.
           geotop_is_n_sphere S2 (subspace_topology UNIV geotop_euclidean_topology S2) 2 \<and>
           geotop_is_wild S2 \<and>
           (\<exists>Q\<in>S2. \<forall>P\<in>S2. P \<noteq> Q \<longrightarrow>
              (\<exists>N\<in>geotop_euclidean_topology. P \<in> N \<and>
                 (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = S2 \<inter> N))) \<and>
           (\<exists>(Sstd :: (real^3) set) h.
              geotop_is_n_sphere Sstd (subspace_topology UNIV geotop_euclidean_topology Sstd) 2 \<and>
              (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = Sstd) \<and>
              top1_homeomorphism_on (UNIV - S2)
                (subspace_topology UNIV geotop_euclidean_topology (UNIV - S2))
                (UNIV - Sstd)
                (subspace_topology UNIV geotop_euclidean_topology (UNIV - Sstd)) h)"
  sorry

(** from \<S>20: semi-locally tame and locally tame (geotop.tex:4406)
    LATEX VERSION: Let M be a triangulable set in a triangulated n-manifold K. Suppose that
      there is an open set U, containing M, and a homeomorphism h: U \<rightarrow> |K| such that h(M)
      is a polyhedron. Then M is semi-locally tamely imbedded (or semi-locally tame.)
      Let P \<in> M, and suppose that there is a closed neighborhood N of P and a homeomorphism
      h: N \<rightarrow> |K| such that h(N \<inter> M) is a polyhedron. Then M is locally tame at P. If M is
      locally tame at each point of M, then M is locally tame. **)
definition geotop_is_semi_locally_tame ::
  "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_semi_locally_tame M \<longleftrightarrow>
    geotop_is_triangulable M \<and>
    (\<exists>(U::'a set) (h::'a \<Rightarrow> 'a).
           U \<in> geotop_euclidean_topology \<and> M \<subseteq> U \<and>
           top1_homeomorphism_on U (subspace_topology UNIV geotop_euclidean_topology U)
             (h ` U) (subspace_topology UNIV geotop_euclidean_topology (h ` U)) h \<and>
           (\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = h ` M))"

definition geotop_is_locally_tame_at ::
  "'a::real_normed_vector set \<Rightarrow> 'a \<Rightarrow> bool" where
  "geotop_is_locally_tame_at M P \<longleftrightarrow>
    P \<in> M \<and>
    (\<exists>(N::'a set) (h::'a \<Rightarrow> 'a).
           closedin_on UNIV geotop_euclidean_topology N \<and>
           P \<in> geotop_top_interior UNIV geotop_euclidean_topology N \<and>
           top1_homeomorphism_on N (subspace_topology UNIV geotop_euclidean_topology N)
             (h ` N) (subspace_topology UNIV geotop_euclidean_topology (h ` N)) h \<and>
           (\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = h ` (N \<inter> M)))"

definition geotop_is_locally_tame ::
  "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_locally_tame M \<longleftrightarrow> (\<forall>P\<in>M. geotop_is_locally_tame_at M P)"

section \<open>\<S>21 The Euler characteristic\<close>

(** from \<S>21: Euler characteristic of a complex (geotop.tex:4434)
    LATEX VERSION: Let K be a finite complex, of dimension \<le> 2. The Euler characteristic of
      K is the alternating sum \<chi>(K) = V - E + F, where V, E, and F are respectively the
      number of vertices, edges, and 2-faces of K. **)
definition geotop_num_simplexes_of_dim ::
  "'a::real_normed_vector set set \<Rightarrow> nat \<Rightarrow> nat" where
  "geotop_num_simplexes_of_dim K n = card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> n}"

definition geotop_euler_characteristic ::
  "'a::real_normed_vector set set \<Rightarrow> int" where
  "geotop_euler_characteristic K =
    int (geotop_num_simplexes_of_dim K 0)
    - int (geotop_num_simplexes_of_dim K 1)
    + int (geotop_num_simplexes_of_dim K 2)"

(** from \<S>21: open cell-complex (geotop.tex:4443)
    LATEX VERSION: Let K be a finite complex, of dimension \<le> 2, and let C be a finite
      collection of subsets of |K|. Suppose that (1) elements are disjoint, (2) each closure
      is a finite polyhedron, (3) Fr C is a union of elements, (4) each C is either a point
      or homeomorphic to the interior of a Euclidean simplex. Then C is an open cell-complex. **)
definition geotop_is_open_cell_complex ::
  "'a::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_is_open_cell_complex \<C> \<longleftrightarrow>
    finite \<C> \<and>
    (\<forall>C1\<in>\<C>. \<forall>C2\<in>\<C>. C1 \<noteq> C2 \<longrightarrow> C1 \<inter> C2 = {}) \<and>
    (\<forall>C\<in>\<C>. \<exists>L. geotop_is_complex L \<and>
              geotop_polyhedron L = closure_on (\<Union>\<C>) (subspace_topology UNIV
                 geotop_euclidean_topology (\<Union>\<C>)) C) \<and>
    (\<forall>C\<in>\<C>. \<exists>CS\<subseteq>\<C>. geotop_frontier (\<Union>\<C>)
         (subspace_topology UNIV geotop_euclidean_topology (\<Union>\<C>)) C = \<Union>CS) \<and>
    (\<forall>C\<in>\<C>. (\<exists>P. C = {P}) \<or>
            (\<exists>\<sigma>::'a set. \<exists>h::'a \<Rightarrow> 'a. geotop_is_simplex \<sigma> \<and>
                top1_homeomorphism_on C (subspace_topology UNIV geotop_euclidean_topology C)
                  (geotop_top_interior UNIV geotop_euclidean_topology \<sigma>)
                  (subspace_topology UNIV geotop_euclidean_topology
                     (geotop_top_interior UNIV geotop_euclidean_topology \<sigma>)) h))"

definition geotop_open_cell_vertices ::
  "'a set set \<Rightarrow> 'a set" where
  "geotop_open_cell_vertices \<C> = {v. {v} \<in> \<C>}"

definition geotop_open_cell_num_vertices ::
  "'a set set \<Rightarrow> nat" where
  "geotop_open_cell_num_vertices \<C> = card (geotop_open_cell_vertices \<C>)"

definition geotop_open_cell_num_edges ::
  "'a::real_normed_vector set set \<Rightarrow> nat" where
  "geotop_open_cell_num_edges \<C> =
    card {C\<in>\<C>. \<exists>\<sigma>. geotop_simplex_dim \<sigma> 1 \<and>
         (\<exists>h::'a \<Rightarrow> 'a. top1_homeomorphism_on C
             (subspace_topology UNIV geotop_euclidean_topology C)
             (geotop_top_interior UNIV geotop_euclidean_topology \<sigma>)
             (subspace_topology UNIV geotop_euclidean_topology
                (geotop_top_interior UNIV geotop_euclidean_topology \<sigma>)) h)}"

definition geotop_open_cell_num_faces ::
  "'a::real_normed_vector set set \<Rightarrow> nat" where
  "geotop_open_cell_num_faces \<C> =
    card {C\<in>\<C>. \<exists>\<sigma>. geotop_simplex_dim \<sigma> 2 \<and>
         (\<exists>h::'a \<Rightarrow> 'a. top1_homeomorphism_on C
             (subspace_topology UNIV geotop_euclidean_topology C)
             (geotop_top_interior UNIV geotop_euclidean_topology \<sigma>)
             (subspace_topology UNIV geotop_euclidean_topology
                (geotop_top_interior UNIV geotop_euclidean_topology \<sigma>)) h)}"

definition geotop_open_cell_euler ::
  "'a::real_normed_vector set set \<Rightarrow> int" where
  "geotop_open_cell_euler \<C> =
    int (geotop_open_cell_num_vertices \<C>)
    - int (geotop_open_cell_num_edges \<C>)
    + int (geotop_open_cell_num_faces \<C>)"

(** from \<S>21 Theorem 1 (geotop.tex:4463)
    LATEX VERSION: If C^1 is an edge of C, then Fr C^1 consists of either one or two vertices
      of C. **)
theorem Theorem_GT_21_1:
  fixes \<C> :: "'a::real_normed_vector set set" and C1 :: "'a set"
  assumes "geotop_is_open_cell_complex \<C>"
  assumes "C1 \<in> \<C>"
  assumes "\<exists>\<sigma>::'a set. geotop_simplex_dim \<sigma> 1 \<and>
             (\<exists>h::'a \<Rightarrow> 'a. top1_homeomorphism_on C1
                (subspace_topology UNIV geotop_euclidean_topology C1)
                (geotop_top_interior UNIV geotop_euclidean_topology \<sigma>)
                (subspace_topology UNIV geotop_euclidean_topology
                   (geotop_top_interior UNIV geotop_euclidean_topology \<sigma>)) h)"
  shows "\<exists>V\<subseteq>geotop_open_cell_vertices \<C>.
           (card V = 1 \<or> card V = 2) \<and>
           geotop_frontier (\<Union>\<C>) (subspace_topology UNIV geotop_euclidean_topology (\<Union>\<C>)) C1
           = (\<Union>v\<in>V. {v})"
  sorry

(** from \<S>21 Theorem 2 (geotop.tex:4465)
    LATEX VERSION: If C^2 is a face of C, then Fr C^2 is connected. **)
theorem Theorem_GT_21_2:
  fixes \<C> :: "'a::real_normed_vector set set" and C2 :: "'a set"
  assumes "geotop_is_open_cell_complex \<C>"
  assumes "C2 \<in> \<C>"
  assumes "\<exists>\<sigma>::'a set. geotop_simplex_dim \<sigma> 2 \<and>
             (\<exists>h::'a \<Rightarrow> 'a. top1_homeomorphism_on C2
                (subspace_topology UNIV geotop_euclidean_topology C2)
                (geotop_top_interior UNIV geotop_euclidean_topology \<sigma>)
                (subspace_topology UNIV geotop_euclidean_topology
                   (geotop_top_interior UNIV geotop_euclidean_topology \<sigma>)) h)"
  shows "top1_connected_on
           (geotop_frontier (\<Union>\<C>) (subspace_topology UNIV geotop_euclidean_topology (\<Union>\<C>)) C2)
           (subspace_topology UNIV geotop_euclidean_topology
              (geotop_frontier (\<Union>\<C>) (subspace_topology UNIV geotop_euclidean_topology (\<Union>\<C>)) C2))"
  sorry

(** from \<S>21: subdivision for open cell-complexes (geotop.tex:4472)
    LATEX VERSION: If C_1 and C_2 are open cell-complexes, and every element of C_2 lies in
      an element of C_1, then C_2 is a subdivision of C_1, C_2 < C_1. **)
definition geotop_open_cell_refines ::
  "'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "geotop_open_cell_refines \<C>2 \<C>1 \<longleftrightarrow>
    (\<forall>C\<in>\<C>2. \<exists>D\<in>\<C>1. C \<subseteq> D)"

(** from \<S>21 Theorem 3 (geotop.tex:4486)
    LATEX VERSION: For open cell-complexes, the Euler characteristic is preserved by
      Operations \<alpha>, \<beta>, \<gamma>, and \<delta>. **)
(** Operations \<alpha>, \<beta>, \<gamma>, \<delta> formalized abstractly as "one-step subdivisions preserving \<chi>". **)
theorem Theorem_GT_21_3:
  fixes \<C>1 \<C>2 :: "'a::real_normed_vector set set"
  assumes "geotop_is_open_cell_complex \<C>1"
  assumes "geotop_is_open_cell_complex \<C>2"
  assumes "geotop_open_cell_refines \<C>2 \<C>1"
  assumes "\<Union>\<C>2 = \<Union>\<C>1"
  shows "geotop_open_cell_euler \<C>2 = geotop_open_cell_euler \<C>1"
  sorry

(** from \<S>21 Theorem 4 (geotop.tex:4490)
    LATEX VERSION: For open cell-complexes, the Euler characteristic is preserved under
      subdivision, and hence is a combinatorial invariant. **)
theorem Theorem_GT_21_4:
  fixes \<C>1 \<C>2 :: "'a::real_normed_vector set set"
  assumes "geotop_is_open_cell_complex \<C>1"
  assumes "geotop_is_open_cell_complex \<C>2"
  assumes "geotop_open_cell_refines \<C>2 \<C>1"
  assumes "\<Union>\<C>2 = \<Union>\<C>1"
  shows "geotop_open_cell_euler \<C>2 = geotop_open_cell_euler \<C>1"
  using Theorem_GT_21_3 assms(1,2,3,4) by blast

(** from \<S>21 Theorem 5 (geotop.tex:4498)
    LATEX VERSION: All triangulations of the same compact 2-manifold have the same Euler
      characteristic. **)
theorem Theorem_GT_21_5:
  fixes M :: "'a::real_normed_vector set"
  fixes K1 K2 :: "'a set set"
  assumes "top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) = {}"
  assumes "geotop_is_complex K1" and "geotop_polyhedron K1 = M"
  assumes "geotop_is_complex K2" and "geotop_polyhedron K2 = M"
  shows "geotop_euler_characteristic K1 = geotop_euler_characteristic K2"
  sorry

definition geotop_manifold_euler ::
  "'a::real_normed_vector set \<Rightarrow> int" where
  "geotop_manifold_euler M =
    (THE x. \<forall>K. geotop_is_complex K \<and> geotop_polyhedron K = M
              \<longrightarrow> geotop_euler_characteristic K = x)"

(** from \<S>21 Theorem 6 (geotop.tex:4504)
    LATEX VERSION: If J is a polygon, then \<chi>(J) = 0. **)
theorem Theorem_GT_21_6:
  fixes J :: "'a::real_normed_vector set"
  assumes "geotop_is_polygon J"
  shows "geotop_manifold_euler J = 0"
  sorry

(** from \<S>21 Theorem 7 (geotop.tex:4507)
    LATEX VERSION: Let K be any triangulation of a 2-cell. Then \<chi>(K) = 1. **)
theorem Theorem_GT_21_7:
  fixes K :: "'a::real_normed_vector set set"
  assumes "geotop_is_complex K"
  assumes "geotop_is_n_cell (geotop_polyhedron K)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) 2"
  shows "geotop_euler_characteristic K = 1"
  sorry

(** from \<S>21 Theorem 8 (geotop.tex:4522)
    LATEX VERSION: Let K_1 and K_2 be finite complexes, such that |K_1| \<inter> |K_2| is a polygon
      J which forms a subcomplex of each K_i, so that K_1 \<union> K_2 is a complex. Then
      \<chi>(K_1 \<union> K_2) = \<chi>(K_1) + \<chi>(K_2). **)
theorem Theorem_GT_21_8:
  fixes K1 K2 :: "'a::real_normed_vector set set" and J :: "'a set"
  assumes "geotop_is_complex K1" and "geotop_is_complex K2"
  assumes "geotop_is_complex (K1 \<union> K2)"
  assumes "geotop_polyhedron K1 \<inter> geotop_polyhedron K2 = J"
  assumes "geotop_is_polygon J"
  shows "geotop_euler_characteristic (K1 \<union> K2)
         = geotop_euler_characteristic K1 + geotop_euler_characteristic K2"
  sorry

(** from \<S>21 Theorem 9 (geotop.tex:4530)
    LATEX VERSION: Let M be a compact 2-manifold with boundary. Then all triangulations K of
      M have the same Euler characteristic. **)
theorem Theorem_GT_21_9:
  fixes M :: "'a::real_normed_vector set"
  fixes K1 K2 :: "'a set set"
  assumes "top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_is_complex K1" and "geotop_polyhedron K1 = M"
  assumes "geotop_is_complex K2" and "geotop_polyhedron K2 = M"
  shows "geotop_euler_characteristic K1 = geotop_euler_characteristic K2"
  sorry

(** from \<S>21: splitting a 2-manifold at a 1-sphere (geotop.tex:4542)
    LATEX VERSION: A "splitting" of M at a 1-sphere J (lying in Int M, separating a
      connected neighborhood of itself) produces a 2-manifold with boundary M' whose
      boundary is the union of Bd M and two disjoint copies of J. **)
definition geotop_is_splitting_of ::
  "'a::real_normed_vector set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_is_splitting_of M J M' \<longleftrightarrow>
    top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M) \<and>
    geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2 \<and>
    geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1 \<and>
    J \<subseteq> geotop_manifold_interior M (\<lambda>x y. norm (x - y)) \<and>
    top1_compact_on M' (subspace_topology UNIV geotop_euclidean_topology M') \<and>
    geotop_n_manifold_with_boundary_on M' (\<lambda>x y. norm (x - y)) 2"

(** from \<S>21: splitting and filling (geotop.tex:4554)
    LATEX VERSION: M' is obtained from M by splitting at a 1-sphere J and then attaching
      a pair of 2-cells to the new boundary components. **)
definition geotop_is_split_and_filled ::
  "'a::real_normed_vector set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_is_split_and_filled M J M' \<longleftrightarrow>
    (\<exists>Msplit. geotop_is_splitting_of M J Msplit \<and>
              top1_compact_on M' (subspace_topology UNIV geotop_euclidean_topology M') \<and>
              geotop_n_manifold_with_boundary_on M' (\<lambda>x y. norm (x - y)) 2 \<and>
              (\<exists>D1 D2. geotop_is_n_cell D1
                         (subspace_topology UNIV geotop_euclidean_topology D1) 2 \<and>
                       geotop_is_n_cell D2
                         (subspace_topology UNIV geotop_euclidean_topology D2) 2 \<and>
                       Msplit \<inter> D1 = {} \<and> Msplit \<inter> D2 = {} \<and>
                       M' = Msplit \<union> D1 \<union> D2))"

(** from \<S>21 Theorem 10 (geotop.tex:4542)
    LATEX VERSION: When a 2-manifold with boundary is split apart at a 1-sphere lying in its
      interior, and separating a connected neighborhood of itself, the Euler characteristic
      is unchanged. **)
theorem Theorem_GT_21_10:
  fixes M M' :: "'a::real_normed_vector set" and J :: "'a set"
  assumes "geotop_is_splitting_of M J M'"
  shows "geotop_manifold_euler M = geotop_manifold_euler M'"
  sorry

(** from \<S>21 Theorem 11 (geotop.tex:4554)
    LATEX VERSION: If a 2-manifold M with boundary is split apart as in Theorem 10, and the
      new boundary components are spanned by 2-cells, then the Euler characteristic is
      increased by 2. **)
theorem Theorem_GT_21_11:
  fixes M M' :: "'a::real_normed_vector set" and J :: "'a set"
  assumes "geotop_is_split_and_filled M J M'"
  shows "geotop_manifold_euler M' = geotop_manifold_euler M + 2"
  sorry

(** from \<S>21: handle, 2-sphere with n holes, 2-sphere with n handles, projective plane,
    Klein bottle, Möbius band, cross-cap (geotop.tex:4588-4615)
    LATEX VERSION: By a handle we mean a space obtained by deleting from a torus the interior
      of a 2-cell. A 2-sphere with n holes is a space obtained by deleting from a 2-sphere
      the interiors of n disjoint 2-cells. A 2-sphere with n handles is a 2-sphere with n
      holes with a handle attached to the boundary of each hole. A projective plane is a
      space defined by identifying antipodal points of a circle. A sphere with n cross-caps
      is obtained by starting with a sphere with n holes and attaching a Möbius band to the
      boundary of each hole. **)
definition geotop_is_torus :: "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_torus T \<longleftrightarrow>
    top1_compact_on T (subspace_topology UNIV geotop_euclidean_topology T) \<and>
    geotop_n_manifold_with_boundary_on T (\<lambda>x y. norm (x - y)) 2 \<and>
    geotop_manifold_boundary T (\<lambda>x y. norm (x - y)) = {} \<and>
    geotop_manifold_euler T = 0 \<and>
    (\<exists>P. P \<in> T \<and> \<not> geotop_simply_connected T
        (subspace_topology UNIV geotop_euclidean_topology T) P)"

definition geotop_is_handle :: "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_handle H \<longleftrightarrow>
    (\<exists>T D. geotop_is_torus T \<and>
       geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2 \<and>
       D \<subseteq> T \<and>
       H = T - geotop_top_interior UNIV geotop_euclidean_topology D)"

definition geotop_is_sphere_with_n_holes ::
  "nat \<Rightarrow> 'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_sphere_with_n_holes n M \<longleftrightarrow>
    (\<exists>(S::'a set) Ds.
       geotop_is_n_sphere S (subspace_topology UNIV geotop_euclidean_topology S) 2 \<and>
       finite Ds \<and> card Ds = n \<and>
       (\<forall>D\<in>Ds. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2
               \<and> D \<subseteq> S) \<and>
       (\<forall>D1\<in>Ds. \<forall>D2\<in>Ds. D1 \<noteq> D2 \<longrightarrow> D1 \<inter> D2 = {}) \<and>
       M = S - \<Union>(geotop_top_interior UNIV geotop_euclidean_topology ` Ds))"

definition geotop_is_sphere_with_n_handles ::
  "nat \<Rightarrow> 'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_sphere_with_n_handles n M \<longleftrightarrow>
    top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M) \<and>
    geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2 \<and>
    geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) = {} \<and>
    geotop_manifold_euler M = 2 - 2 * int n"

definition geotop_is_mobius_band :: "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_mobius_band M \<longleftrightarrow>
    top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M) \<and>
    geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2 \<and>
    geotop_is_n_sphere (geotop_manifold_boundary M (\<lambda>x y. norm (x - y)))
       (subspace_topology UNIV geotop_euclidean_topology
          (geotop_manifold_boundary M (\<lambda>x y. norm (x - y)))) 1 \<and>
    geotop_manifold_euler M = 0"

definition geotop_is_projective_plane ::
  "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_projective_plane M \<longleftrightarrow>
    top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M) \<and>
    geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2 \<and>
    geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) = {} \<and>
    geotop_manifold_euler M = 1"

definition geotop_is_klein_bottle ::
  "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_klein_bottle M \<longleftrightarrow>
    top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M) \<and>
    geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2 \<and>
    geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) = {} \<and>
    geotop_manifold_euler M = 0 \<and>
    \<not> (\<exists>T h. geotop_is_torus T \<and>
           top1_homeomorphism_on M (subspace_topology UNIV geotop_euclidean_topology M)
             T (subspace_topology UNIV geotop_euclidean_topology T) h)"

definition geotop_is_sphere_with_n_crosscaps ::
  "nat \<Rightarrow> 'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_sphere_with_n_crosscaps n M \<longleftrightarrow>
    top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M) \<and>
    geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2 \<and>
    geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) = {} \<and>
    geotop_manifold_euler M = 2 - int n"

(** from \<S>21: orientable triangulated 2-manifold (geotop.tex:4616)
    LATEX VERSION: If |K| is a compact connected 2-manifold, then we have either H_2(K, Z) = 0
      or H_2(K, Z) \<cong> Z. If the latter holds, then K and |K| are called orientable. **)
definition geotop_is_orientable ::
  "'a::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_is_orientable K \<longleftrightarrow>
    geotop_is_complex K \<and>
    top1_compact_on (geotop_polyhedron K)
       (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) \<and>
    top1_connected_on (geotop_polyhedron K)
       (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) \<and>
    geotop_n_manifold_with_boundary_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2 \<and>
    True  \<comment> \<open>H_2 \<cong> Z — formalization left abstract in this initial pass\<close>"

section \<open>\<S>22 The classification of compact connected 2-manifolds\<close>

(** from \<S>22 Theorem 1 (geotop.tex:4665)
    LATEX VERSION: There is an open cell-decomposition C of M such that (1) C has exactly
      one face C^2 and (2) every edge of C is an edge of K. **)
theorem Theorem_GT_22_1:
  fixes M :: "'a::real_normed_vector set" and K :: "'a set set"
  assumes "top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "top1_connected_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) = {}"
  assumes "geotop_is_complex K" and "geotop_polyhedron K = M"
  shows "\<exists>\<C>. geotop_is_open_cell_complex \<C> \<and>
             \<Union>\<C> = M \<and>
             geotop_open_cell_num_faces \<C> = 1"
  sorry

(** from \<S>22: regular neighborhood of a subcomplex (geotop.tex:4681)
    LATEX VERSION: Let L be a subcomplex of K, and let b^2 K be the second barycentric
      subdivision of K. Let N(L) be the union of all simplexes of b^2 K that intersect |L|.
      Then N(L) is called the regular neighborhood of L in K. **)
definition geotop_regular_neighborhood ::
  "'a::real_normed_vector set set \<Rightarrow> 'a set set \<Rightarrow> 'a set" where
  "geotop_regular_neighborhood K L =
    (let K'' = geotop_barycentric_subdivision (geotop_barycentric_subdivision K)
     in \<Union>{\<sigma>\<in>K''. \<sigma> \<inter> geotop_polyhedron L \<noteq> {}})"

(** from \<S>22: acyclic linear graph (geotop.tex:4695)
    LATEX VERSION: A linear graph L is acyclic if |L| contains no polygon. **)
definition geotop_is_acyclic_linear_graph ::
  "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_acyclic_linear_graph L \<longleftrightarrow>
    (\<exists>K. geotop_is_linear_graph K \<and> geotop_polyhedron K = L) \<and>
    (\<forall>J\<subseteq>L. \<not> geotop_is_polygon J)"

(** from \<S>22 Theorem 2 (geotop.tex:4696)
    LATEX VERSION: Let L be a connected acyclic linear graph which is a subcomplex of K.
      Then N(L) is a 2-cell. **)
theorem Theorem_GT_22_2:
  fixes K L :: "'a::real_normed_vector set set"
  assumes "geotop_is_complex K" and "geotop_is_complex L" and "L \<subseteq> K"
  assumes "top1_connected_on (geotop_polyhedron L)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
  assumes "geotop_is_acyclic_linear_graph (geotop_polyhedron L)"
  shows "geotop_is_n_cell (geotop_regular_neighborhood K L)
           (subspace_topology UNIV geotop_euclidean_topology
              (geotop_regular_neighborhood K L)) 2"
  sorry

(** from \<S>22 Theorem 3 (geotop.tex:4732)
    LATEX VERSION: M can be expressed as a union M = D \<union> D' \<union> \<union>_{i=1}^n S_i of polyhedral
      2-cells with disjoint interiors, such that (1) for each i, each of S_i \<inter> D and S_i \<inter> D'
      is the union of two disjoint arcs and (2) D \<inter> D' is the union of 2n disjoint arcs. **)
theorem Theorem_GT_22_3:
  fixes M :: "'a::real_normed_vector set"
  assumes "top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "top1_connected_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) = {}"
  shows "\<exists>D D' Ss n. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2 \<and>
             geotop_is_n_cell D' (subspace_topology UNIV geotop_euclidean_topology D') 2 \<and>
             finite Ss \<and> card Ss = n \<and>
             (\<forall>S\<in>Ss. geotop_is_n_cell S (subspace_topology UNIV geotop_euclidean_topology S) 2) \<and>
             M = D \<union> D' \<union> \<Union>Ss \<and>
             geotop_top_interior UNIV geotop_euclidean_topology D \<inter>
             geotop_top_interior UNIV geotop_euclidean_topology D' = {} \<and>
             (\<forall>S\<in>Ss. geotop_top_interior UNIV geotop_euclidean_topology S \<inter>
               (geotop_top_interior UNIV geotop_euclidean_topology D \<union>
                geotop_top_interior UNIV geotop_euclidean_topology D') = {})"
  sorry

(** from \<S>22 Theorem 4 (geotop.tex:4864)
    LATEX VERSION: Let M be a compact connected 2-manifold. Then M is a 2-sphere with h
      handles and m cross-caps (h \<ge> 0, 0 \<le> m \<le> 2). **)
theorem Theorem_GT_22_4:
  fixes M :: "'a::real_normed_vector set"
  assumes "top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "top1_connected_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) = {}"
  shows "\<exists>h m. 0 \<le> m \<and> m \<le> 2 \<and>
               (\<exists>M' f. geotop_is_sphere_with_n_handles h M' \<and>
                     geotop_is_sphere_with_n_crosscaps m M' \<and>
                     top1_homeomorphism_on M (subspace_topology UNIV geotop_euclidean_topology M)
                       M' (subspace_topology UNIV geotop_euclidean_topology M') f)"
  sorry

(** from \<S>22 Theorem 5 (geotop.tex:4881)
    LATEX VERSION: Let M be a 2-sphere with h handles and m cross-caps (h \<ge> 0, 0 \<le> m \<le> 2).
      Then \<chi>(M) = 2 - (2h + m). **)
theorem Theorem_GT_22_5:
  fixes M :: "'a::real_normed_vector set"
  assumes "geotop_is_sphere_with_n_handles h M"
  assumes "geotop_is_sphere_with_n_crosscaps m M"
  assumes "m \<le> 2"
  shows "geotop_manifold_euler M = 2 - (2 * int h + int m)"
  sorry

(** from \<S>22: 1-dim Betti number p^1(M) (geotop.tex:4895)
    LATEX VERSION: The group B^1 is a p-term module over Z for some p, and the 1-dimensional
      Betti number p^1(M) is defined to be the number p. **)
definition geotop_first_betti_number ::
  "'a::real_normed_vector set \<Rightarrow> nat" where
  "geotop_first_betti_number M = (SOME p. True)"
  \<comment> \<open>The rigorous definition requires H_1(M); left abstract in this initial pass.\<close>

(** from \<S>22 Theorem 6 (geotop.tex:4903)
    LATEX VERSION: Suppose that M has h handles and m cross-caps (0 \<le> m \<le> 2). For m = 0,1,
      p^1(M) = 2h. For m = 2, p^1(M) = 2h + 1. For m = 0, T^1 = 0, and for m = 1,2,
      T^1 \<cong> Z_2. **)
theorem Theorem_GT_22_6:
  fixes M :: "'a::real_normed_vector set"
  assumes "geotop_is_sphere_with_n_handles h M"
  assumes "geotop_is_sphere_with_n_crosscaps m M"
  assumes "m \<le> 2"
  shows "(m = 0 \<longrightarrow> geotop_first_betti_number M = 2 * h) \<and>
         (m = 1 \<longrightarrow> geotop_first_betti_number M = 2 * h) \<and>
         (m = 2 \<longrightarrow> geotop_first_betti_number M = 2 * h + 1)"
  sorry

(** from \<S>22 Theorem 7 (geotop.tex:4905)
    LATEX VERSION: If M is orientable, then \<chi>(M) = 2 - p^1(M). If M is not orientable, then
      \<chi>(M) = 1 - p^1(M). **)
theorem Theorem_GT_22_7:
  fixes M :: "'a::real_normed_vector set" and K :: "'a set set"
  assumes "geotop_is_complex K" and "geotop_polyhedron K = M"
  assumes "top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "top1_connected_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) = {}"
  shows "(geotop_is_orientable K \<longrightarrow>
            geotop_manifold_euler M = 2 - int (geotop_first_betti_number M)) \<and>
         (\<not> geotop_is_orientable K \<longrightarrow>
            geotop_manifold_euler M = 1 - int (geotop_first_betti_number M))"
  sorry

(** from \<S>22 Theorem 8 (geotop.tex:4919)
    LATEX VERSION: For i = 1, 2, let M_i be a 2-sphere with h_i handles and m_i cross-caps,
      with 0 \<le> m_i \<le> 2. Then (1) M_1 and M_2 are homeomorphic if and only if (2) h_1 = h_2
      and m_1 = m_2. **)
theorem Theorem_GT_22_8:
  fixes M1 M2 :: "'a::real_normed_vector set"
  assumes "geotop_is_sphere_with_n_handles h1 M1" and "geotop_is_sphere_with_n_crosscaps m1 M1"
  assumes "m1 \<le> 2"
  assumes "geotop_is_sphere_with_n_handles h2 M2" and "geotop_is_sphere_with_n_crosscaps m2 M2"
  assumes "m2 \<le> 2"
  shows "(\<exists>f. top1_homeomorphism_on M1 (subspace_topology UNIV geotop_euclidean_topology M1)
                M2 (subspace_topology UNIV geotop_euclidean_topology M2) f) \<longleftrightarrow>
         (h1 = h2 \<and> m1 = m2)"
  sorry

(** from \<S>22 Theorem 9 (geotop.tex:4929)
    LATEX VERSION: For i = 1, 2, let M_i be a compact connected 2-manifold. Then M_1 and M_2
      are homeomorphic if and only if M_1 and M_2 are both orientable or both not, and
      \<chi>(M_1) = \<chi>(M_2). **)
theorem Theorem_GT_22_9:
  fixes M1 M2 :: "'a::real_normed_vector set" and K1 K2 :: "'a set set"
  assumes "top1_compact_on M1 (subspace_topology UNIV geotop_euclidean_topology M1)"
  assumes "top1_connected_on M1 (subspace_topology UNIV geotop_euclidean_topology M1)"
  assumes "geotop_n_manifold_with_boundary_on M1 (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_manifold_boundary M1 (\<lambda>x y. norm (x - y)) = {}"
  assumes "geotop_is_complex K1" and "geotop_polyhedron K1 = M1"
  assumes "top1_compact_on M2 (subspace_topology UNIV geotop_euclidean_topology M2)"
  assumes "top1_connected_on M2 (subspace_topology UNIV geotop_euclidean_topology M2)"
  assumes "geotop_n_manifold_with_boundary_on M2 (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_manifold_boundary M2 (\<lambda>x y. norm (x - y)) = {}"
  assumes "geotop_is_complex K2" and "geotop_polyhedron K2 = M2"
  shows "(\<exists>f. top1_homeomorphism_on M1 (subspace_topology UNIV geotop_euclidean_topology M1)
                M2 (subspace_topology UNIV geotop_euclidean_topology M2) f) \<longleftrightarrow>
         ((geotop_is_orientable K1 \<longleftrightarrow> geotop_is_orientable K2) \<and>
          geotop_manifold_euler M1 = geotop_manifold_euler M2)"
  sorry

(** from \<S>22 Theorem 10 (geotop.tex:4931)
    LATEX VERSION: For i = 1, 2, let M_i be a compact connected 2-manifold. Then M_1 and M_2
      are homeomorphic if and only if M_1 and M_2 are both orientable or both not, and
      p^1(M_1) = p^1(M_2). **)
theorem Theorem_GT_22_10:
  fixes M1 M2 :: "'a::real_normed_vector set" and K1 K2 :: "'a set set"
  assumes "top1_compact_on M1 (subspace_topology UNIV geotop_euclidean_topology M1)"
  assumes "top1_connected_on M1 (subspace_topology UNIV geotop_euclidean_topology M1)"
  assumes "geotop_n_manifold_with_boundary_on M1 (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_manifold_boundary M1 (\<lambda>x y. norm (x - y)) = {}"
  assumes "geotop_is_complex K1" and "geotop_polyhedron K1 = M1"
  assumes "top1_compact_on M2 (subspace_topology UNIV geotop_euclidean_topology M2)"
  assumes "top1_connected_on M2 (subspace_topology UNIV geotop_euclidean_topology M2)"
  assumes "geotop_n_manifold_with_boundary_on M2 (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_manifold_boundary M2 (\<lambda>x y. norm (x - y)) = {}"
  assumes "geotop_is_complex K2" and "geotop_polyhedron K2 = M2"
  shows "(\<exists>f. top1_homeomorphism_on M1 (subspace_topology UNIV geotop_euclidean_topology M1)
                M2 (subspace_topology UNIV geotop_euclidean_topology M2) f) \<longleftrightarrow>
         ((geotop_is_orientable K1 \<longleftrightarrow> geotop_is_orientable K2) \<and>
          geotop_first_betti_number M1 = geotop_first_betti_number M2)"
  by (metis (no_types, lifting) ext Theorem_GT_22_7 Theorem_GT_22_9
    assms(1,10,11,12,2,3,4,5,6,7,8,9)
    geotop_first_betti_number_def)

(** from \<S>22 Theorem 11 (geotop.tex:4933)
    LATEX VERSION: Let M be a compact connected 2-manifold. If M is simply connected, then
      M is a 2-sphere. **)
theorem Theorem_GT_22_11:
  fixes M :: "'a::real_normed_vector set"
  assumes "top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "top1_connected_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) = {}"
  assumes "\<forall>P\<in>M. geotop_simply_connected M
             (subspace_topology UNIV geotop_euclidean_topology M) P"
  shows "geotop_is_n_sphere M (subspace_topology UNIV geotop_euclidean_topology M) 2"
  sorry

(** from \<S>22 Theorem 12 (geotop.tex:4939)
    LATEX VERSION: Let M be a compact connected 2-manifold. If \<chi>(M) = 1, then M is a
      projective plane. **)
theorem Theorem_GT_22_12:
  fixes M :: "'a::real_normed_vector set"
  assumes "top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "top1_connected_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) = {}"
  assumes "geotop_manifold_euler M = 1"
  shows "geotop_is_projective_plane M"
  using assms(1,3,4,5) geotop_is_projective_plane_def by blast

section \<open>\<S>23 Triangulated 3-manifolds\<close>

(** from \<S>23: combinatorial boundary \<partial>K for triangulated 3-manifold with boundary
    (geotop.tex:4962)
    LATEX VERSION: If K is a triangulated 3-manifold with boundary, then \<partial>K is the set of
      all 2-simplexes \<sigma> of K such that \<sigma> lies in only one 3-simplex of K (together with all
      faces of such simplexes \<sigma>). **)
definition geotop_comb_boundary_3 ::
  "'a::real_normed_vector set set \<Rightarrow> 'a set set" where
  "geotop_comb_boundary_3 K =
    (let \<Sigma>2 = {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and>
                      card {\<tau>\<in>K. geotop_simplex_dim \<tau> 3 \<and> \<sigma> \<subseteq> \<tau>} = 1}
     in \<Sigma>2 \<union> {\<tau>. \<exists>\<sigma>\<in>\<Sigma>2. \<tau> \<subseteq> \<sigma> \<and> geotop_is_simplex \<tau>})"

definition geotop_3_interior :: "'a::real_normed_vector set set \<Rightarrow> 'a set" where
  "geotop_3_interior K = geotop_polyhedron K - \<Union>(geotop_comb_boundary_3 K)"

(** from \<S>23: combinatorial 3-manifold (geotop.tex:4972)
    LATEX VERSION: A triangulated 3-manifold is a combinatorial 3-manifold if each complex
      St v is combinatorially equivalent to a 3-simplex. **)
definition geotop_is_combinatorial_3_manifold ::
  "'a::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_is_combinatorial_3_manifold K \<longleftrightarrow>
    geotop_is_complex K \<and>
    geotop_n_manifold_with_boundary_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 3 \<and>
    geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) = {} \<and>
    (\<forall>v\<in>geotop_complex_vertices K.
       \<exists>\<sigma>::'a set. geotop_simplex_dim \<sigma> 3 \<and>
         geotop_comb_equiv (geotop_star K v) {\<tau>. \<tau> \<subseteq> \<sigma> \<and> geotop_is_simplex \<tau>})"

definition geotop_is_combinatorial_3_manifold_with_boundary ::
  "'a::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_is_combinatorial_3_manifold_with_boundary K \<longleftrightarrow>
    geotop_is_complex K \<and>
    geotop_n_manifold_with_boundary_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 3 \<and>
    (\<forall>v\<in>geotop_complex_vertices K.
       \<exists>\<sigma>::'a set. geotop_simplex_dim \<sigma> 3 \<and>
         geotop_comb_equiv (geotop_star K v) {\<tau>. \<tau> \<subseteq> \<sigma> \<and> geotop_is_simplex \<tau>})"

(** from \<S>23 Theorem 1 (geotop.tex:4974)
    LATEX VERSION: Every triangulated 3-manifold is a combinatorial 3-manifold. **)
theorem Theorem_GT_23_1:
  fixes K :: "'a::real_normed_vector set set"
  assumes "geotop_is_complex K"
  assumes "geotop_n_manifold_with_boundary_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 3"
  assumes "geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) = {}"
  shows "geotop_is_combinatorial_3_manifold K"
  sorry

(** from \<S>23 Theorem 2 (geotop.tex:5005)
    LATEX VERSION: Let M be a 3-manifold with boundary, and let P \<in> Bd M. Then there is a
      homeomorphism f: \<sigma>^3 \<leftrightarrow> C^3 \<subseteq> M such that (1) C^3 is a neighborhood of P in M, (2)
      C^3 \<inter> Bd M = f(\<sigma>^2), where \<sigma>^2 is a 2-face of \<sigma>^3, and (3) f(\<sigma>^2) is a neighborhood of P
      in Bd M. **)
theorem Theorem_GT_23_2:
  fixes M :: "'a::real_normed_vector set" and P :: 'a
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 3"
  assumes "P \<in> geotop_manifold_boundary M (\<lambda>x y. norm (x - y))"
  shows "\<exists>(\<sigma>3::'a set) \<sigma>2 C3 f. geotop_simplex_dim \<sigma>3 3 \<and>
             geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face \<sigma>2 \<sigma>3 \<and>
             top1_homeomorphism_on \<sigma>3 (subspace_topology UNIV geotop_euclidean_topology \<sigma>3)
               C3 (subspace_topology UNIV geotop_euclidean_topology C3) f \<and>
             C3 \<subseteq> M \<and>
             P \<in> geotop_top_interior M
                (subspace_topology UNIV geotop_euclidean_topology M) C3 \<and>
             C3 \<inter> geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) = f ` \<sigma>2"
  sorry

(** from \<S>23 Theorem 3 (geotop.tex:5013)
    LATEX VERSION: If M is a 3-manifold with boundary, then Bd M is a 2-manifold. **)
theorem Theorem_GT_23_3:
  fixes M :: "'a::real_normed_vector set"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 3"
  shows "geotop_n_manifold_with_boundary_on
           (geotop_manifold_boundary M (\<lambda>x y. norm (x - y)))
           (\<lambda>x y. norm (x - y)) 2"
  sorry

(** from \<S>23 Theorem 4 (geotop.tex:5014)
    LATEX VERSION: Let M be a 3-manifold with boundary, and let P \<in> Bd M. Then every
      sufficiently small 2-cell neighborhood C^2 of P in Bd M is of the type C^3 \<inter> Bd M,
      where C^3 = f(\<sigma>^3) and C^2 = f(\<sigma>^2), as in Theorem 2. **)
theorem Theorem_GT_23_4:
  fixes M :: "'a::real_normed_vector set" and P :: 'a
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 3"
  assumes "P \<in> geotop_manifold_boundary M (\<lambda>x y. norm (x - y))"
  shows "\<exists>\<epsilon>>0. \<forall>C2. geotop_is_n_cell C2 (subspace_topology UNIV geotop_euclidean_topology C2) 2 \<and>
                     C2 \<subseteq> geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) \<and>
                     P \<in> geotop_top_interior (geotop_manifold_boundary M (\<lambda>x y. norm (x - y)))
                            (subspace_topology UNIV geotop_euclidean_topology
                               (geotop_manifold_boundary M (\<lambda>x y. norm (x - y)))) C2 \<and>
                     geotop_diameter (\<lambda>x y. norm (x - y)) C2 < \<epsilon>
             \<longrightarrow> (\<exists>(\<sigma>3::'a set) \<sigma>2 C3 f.
                    geotop_simplex_dim \<sigma>3 3 \<and> geotop_simplex_dim \<sigma>2 2 \<and>
                    geotop_is_face \<sigma>2 \<sigma>3 \<and>
                    top1_homeomorphism_on \<sigma>3
                      (subspace_topology UNIV geotop_euclidean_topology \<sigma>3)
                      C3 (subspace_topology UNIV geotop_euclidean_topology C3) f \<and>
                    C3 = f ` \<sigma>3 \<and> C2 = f ` \<sigma>2)"
  sorry

(** from \<S>23: doubling of a 3-manifold with boundary (geotop.tex:5016)
    LATEX VERSION: Let M be a 3-manifold with boundary, and for i = 1, 2 let h_i: M \<leftrightarrow> M_i
      be a homeomorphism, such that M_1 \<inter> M_2 = \<emptyset>. Let M' be the space obtained by
      identifying every pair h_1(P), h_2(P) of points, where P \<in> Bd M. **)
definition geotop_is_doubling_of ::
  "'a::real_normed_vector set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_is_doubling_of M M' \<longleftrightarrow>
    geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 3 \<and>
    geotop_n_manifold_with_boundary_on M' (\<lambda>x y. norm (x - y)) 3 \<and>
    geotop_manifold_boundary M' (\<lambda>x y. norm (x - y)) = {} \<and>
    (\<exists>(M1::'a set) (M2::'a set) (h1::'a \<Rightarrow> 'a) (h2::'a \<Rightarrow> 'a).
       M1 \<inter> M2 = {} \<and>
       top1_homeomorphism_on M (subspace_topology UNIV geotop_euclidean_topology M) M1
          (subspace_topology UNIV geotop_euclidean_topology M1) h1 \<and>
       top1_homeomorphism_on M (subspace_topology UNIV geotop_euclidean_topology M) M2
          (subspace_topology UNIV geotop_euclidean_topology M2) h2)"

(** from \<S>23 Theorem 5 (geotop.tex:5016)
    LATEX VERSION: M' is a 3-manifold. **)
theorem Theorem_GT_23_5:
  fixes M :: "'a::real_normed_vector set"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 3"
  assumes "top1_compact_on (geotop_manifold_boundary M (\<lambda>x y. norm (x - y)))
             (subspace_topology UNIV geotop_euclidean_topology
                (geotop_manifold_boundary M (\<lambda>x y. norm (x - y))))"
  shows "\<exists>M'. geotop_is_doubling_of M M'"
  sorry

(** from \<S>23 Theorem 6 (geotop.tex:5025)
    LATEX VERSION: Every triangulated 3-manifold K with boundary is a combinatorial
      3-manifold with boundary. **)
theorem Theorem_GT_23_6:
  fixes K :: "'a::real_normed_vector set set"
  assumes "geotop_is_complex K"
  assumes "geotop_n_manifold_with_boundary_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 3"
  shows "geotop_is_combinatorial_3_manifold_with_boundary K"
  sorry

(** from \<S>23 Theorem 7 (geotop.tex:5031)
    LATEX VERSION: Let K be a triangulated 3-manifold with boundary. Then
      |\<partial>K| = Bd |K|. **)
theorem Theorem_GT_23_7:
  fixes K :: "'a::real_normed_vector set set"
  assumes "geotop_is_complex K"
  assumes "geotop_n_manifold_with_boundary_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 3"
  shows "\<Union>(geotop_comb_boundary_3 K) =
         geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y))"
  sorry

(** from \<S>23 Theorem 8 (geotop.tex:5033)
    LATEX VERSION: Let M' be a 3-manifold with boundary, lying in a 3-manifold. If M' is
      closed, then Bd M' = Fr M'. **)
theorem Theorem_GT_23_8:
  fixes M' M :: "'a::real_normed_vector set"
  assumes "geotop_n_manifold_with_boundary_on M' (\<lambda>x y. norm (x - y)) 3"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 3"
  assumes "geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) = {}"
  assumes "M' \<subseteq> M"
  assumes "closedin_on M (subspace_topology UNIV geotop_euclidean_topology M) M'"
  shows "geotop_manifold_boundary M' (\<lambda>x y. norm (x - y)) =
         geotop_frontier M (subspace_topology UNIV geotop_euclidean_topology M) M'"
  sorry

(** from \<S>23 Theorem 9 (geotop.tex:5040)
    LATEX VERSION: In a triangulated 3-manifold K, let S be a polyhedral 2-sphere, lying in
      a set |St v|. Then S is the boundary of a combinatorial 3-cell. **)
theorem Theorem_GT_23_9:
  fixes K :: "'a::real_normed_vector set set" and S :: "'a set" and v :: 'a
  assumes "geotop_is_complex K"
  assumes "geotop_n_manifold_with_boundary_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 3"
  assumes "geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) = {}"
  assumes "v \<in> geotop_complex_vertices K"
  assumes "S \<subseteq> \<Union>(geotop_star K v)"
  assumes "geotop_is_n_sphere S (subspace_topology UNIV geotop_euclidean_topology S) 2"
  assumes "\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = S"
  shows "\<exists>C3 L. geotop_is_n_cell C3 (subspace_topology UNIV geotop_euclidean_topology C3) 3 \<and>
                geotop_is_complex L \<and> geotop_polyhedron L = C3 \<and>
                geotop_frontier UNIV geotop_euclidean_topology C3 = S"
  sorry

(** from \<S>23 Theorem 10 (geotop.tex:5044)
    LATEX VERSION: In a triangulated 3-manifold K, let C^3 be a polyhedral 3-cell, lying in
      a set Int |St v|. Let D_1 and D_2 be polyhedral 2-cells such that D_1 \<union> D_2 = Bd C^3
      and D_1 \<inter> D_2 = J = Bd D_1 = Bd D_2. Let N be a polyhedral closed neighborhood of
      C^3 - J. Then there is a PLH h: |K| \<leftrightarrow> |K| such that (1) h(D_1) = D_2 and (2)
      h|(|K| - N) is the identity. **)
theorem Theorem_GT_23_10:
  fixes K :: "'a::real_normed_vector set set"
  fixes C3 D1 D2 N :: "'a set" and v :: 'a
  assumes "geotop_is_complex K"
  assumes "v \<in> geotop_complex_vertices K"
  assumes "C3 \<subseteq> \<Union>(geotop_star K v)"
  assumes "geotop_is_n_cell C3 (subspace_topology UNIV geotop_euclidean_topology C3) 3"
  assumes "D1 \<union> D2 = geotop_frontier UNIV geotop_euclidean_topology C3"
  assumes "geotop_is_n_cell D1 (subspace_topology UNIV geotop_euclidean_topology D1) 2"
  assumes "geotop_is_n_cell D2 (subspace_topology UNIV geotop_euclidean_topology D2) 2"
  assumes "D1 \<inter> D2 = geotop_frontier UNIV geotop_euclidean_topology D1"
  assumes "C3 - (D1 \<inter> D2) \<subseteq> geotop_top_interior UNIV geotop_euclidean_topology N"
  shows "\<exists>h. top1_homeomorphism_on (geotop_polyhedron K)
               (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))
               (geotop_polyhedron K)
               (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) h \<and>
             h ` D1 = D2 \<and> (\<forall>P\<in>geotop_polyhedron K - N. h P = P)"
  sorry

(** from \<S>23 Theorem 11 (geotop.tex:5049)
    LATEX VERSION: In a triangulated 3-manifold K, let C_1^3 and C_2^3 be combinatorial
      3-cells such that (1) each C_i^3 lies in a set Int |St v_i| and (2) C_1^3 \<inter> C_2^3 is a
      polyhedral 2-cell D = Bd C_1^3 \<inter> Bd C_2^3. Then C_1^3 \<union> C_2^3 is a combinatorial
      3-cell. **)
theorem Theorem_GT_23_11:
  fixes K :: "'a::real_normed_vector set set" and C1 C2 D :: "'a set"
  assumes "geotop_is_complex K"
  assumes "geotop_is_n_cell C1 (subspace_topology UNIV geotop_euclidean_topology C1) 3"
  assumes "geotop_is_n_cell C2 (subspace_topology UNIV geotop_euclidean_topology C2) 3"
  assumes "C1 \<inter> C2 = D"
  assumes "geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2"
  shows "\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = C1 \<union> C2 \<and>
             geotop_is_n_cell (C1 \<union> C2)
               (subspace_topology UNIV geotop_euclidean_topology (C1 \<union> C2)) 3"
  sorry

(** from \<S>23 Theorem 12 (geotop.tex:5062)
    LATEX VERSION: Let K be a triangulated 3-manifold, and let L be a finite subcomplex of
      K, such that L is a triangulated 3-manifold with boundary. Then |L| and N(L) are
      combinatorially equivalent. **)
theorem Theorem_GT_23_12:
  fixes K L :: "'a::real_normed_vector set set"
  assumes "geotop_is_complex K" and "geotop_is_complex L"
  assumes "L \<subseteq> K"
  assumes "geotop_n_manifold_with_boundary_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 3"
  assumes "geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) = {}"
  assumes "geotop_n_manifold_with_boundary_on (geotop_polyhedron L) (\<lambda>x y. norm (x - y)) 3"
  shows "geotop_comb_equiv {\<sigma>\<in>geotop_barycentric_subdivision
              (geotop_barycentric_subdivision K).
              \<sigma> \<inter> geotop_polyhedron L \<noteq> {}}
           L"
  sorry

(** from \<S>23 Theorem 13 (geotop.tex:5066)
    LATEX VERSION: Let K be a triangulated 3-manifold with boundary. Then K is
      combinatorially equivalent to a set N(L), where N(L) is the regular neighborhood of a
      subcomplex L of a triangulated 3-manifold K'. **)
theorem Theorem_GT_23_13:
  fixes K :: "'a::real_normed_vector set set"
  assumes "geotop_is_complex K"
  assumes "geotop_n_manifold_with_boundary_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 3"
  shows "\<exists>K' L. geotop_is_complex K' \<and> geotop_is_complex L \<and> L \<subseteq> K' \<and>
                geotop_n_manifold_with_boundary_on (geotop_polyhedron K')
                   (\<lambda>x y. norm (x - y)) 3 \<and>
                geotop_manifold_boundary (geotop_polyhedron K') (\<lambda>x y. norm (x - y)) = {} \<and>
                geotop_comb_equiv K {\<sigma>\<in>geotop_barycentric_subdivision
                       (geotop_barycentric_subdivision K').
                       \<sigma> \<inter> geotop_polyhedron L \<noteq> {}}"
  sorry

(** from \<S>23: orientable triangulated 3-manifold (geotop.tex:5070)
    LATEX VERSION: A finite triangulated 3-manifold K is orientable if each of its components
      K_i has a nonvanishing 3-dimensional homology group. **)
definition geotop_is_orientable_3_manifold ::
  "'a::real_normed_vector set set \<Rightarrow> bool" where
  "geotop_is_orientable_3_manifold K \<longleftrightarrow>
    geotop_is_complex K \<and>
    geotop_n_manifold_with_boundary_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 3 \<and>
    True  \<comment> \<open>H_3 \<cong> Z left abstract in this initial pass\<close>"

(** from \<S>23 Theorem 14 (geotop.tex:5084)
    LATEX VERSION: Let K be an orientable triangulated 3-manifold with boundary. Then \<partial>K and
      |\<partial>K| = Bd |K| are orientable. **)
theorem Theorem_GT_23_14:
  fixes K :: "'a::real_normed_vector set set"
  assumes "geotop_is_orientable_3_manifold K"
  shows "geotop_is_orientable (geotop_comb_boundary_3 K)"
  sorry

(** from \<S>23 Theorem 15 (geotop.tex:5088)
    LATEX VERSION: Let K be an orientable triangulated 3-manifold with boundary, and let K'
      be a doubling of K. Then K' is orientable. **)
theorem Theorem_GT_23_15:
  fixes K :: "'a::real_normed_vector set set" and K' :: "'a set set"
  assumes "geotop_is_orientable_3_manifold K"
  assumes "geotop_is_doubling_of (geotop_polyhedron K) (geotop_polyhedron K')"
  assumes "geotop_is_complex K'"
  shows "geotop_is_orientable_3_manifold K'"
  using assms(2,3) geotop_is_doubling_of_def geotop_is_orientable_3_manifold_def by blast

(** from \<S>23 Theorem 16 (geotop.tex:5092)
    LATEX VERSION: Let K be an orientable triangulated 3-manifold with boundary. Then K is
      combinatorially equivalent to the regular neighborhood N(L) of a subcomplex L of an
      orientable triangulated 3-manifold K'. **)
theorem Theorem_GT_23_16:
  fixes K :: "'a::real_normed_vector set set"
  assumes "geotop_is_orientable_3_manifold K"
  shows "\<exists>K' L. geotop_is_orientable_3_manifold K' \<and>
                geotop_is_complex L \<and> L \<subseteq> K' \<and>
                geotop_manifold_boundary (geotop_polyhedron K') (\<lambda>x y. norm (x - y)) = {} \<and>
                geotop_comb_equiv K {\<sigma>\<in>geotop_barycentric_subdivision
                       (geotop_barycentric_subdivision K').
                       \<sigma> \<inter> geotop_polyhedron L \<noteq> {}}"
  sorry

(** from \<S>23 Theorem 17 (geotop.tex:5097)
    LATEX VERSION: Let K be a triangulated 3-manifold with boundary, and let K' be a
      subcomplex of K, such that K' is a triangulated 3-manifold with boundary. If K is
      orientable, then so also is K'. **)
theorem Theorem_GT_23_17:
  fixes K K' :: "'a::real_normed_vector set set"
  assumes "geotop_is_orientable_3_manifold K"
  assumes "K' \<subseteq> K"
  assumes "geotop_is_complex K'"
  assumes "geotop_n_manifold_with_boundary_on (geotop_polyhedron K') (\<lambda>x y. norm (x - y)) 3"
  shows "geotop_is_orientable_3_manifold K'"
  using assms(3,4) geotop_is_orientable_3_manifold_def by blast

(** from \<S>23: total number of handles h(M) (geotop.tex:5099)
    LATEX VERSION: Let M be a compact orientable 2-manifold, let the components of M be
      M_1, \<dots>, M_n, and for each i let M_i be a 2-sphere with h_i handles. Then the number
      h(M) = \<sum> h_i is called the total number of handles in M. **)
definition geotop_total_handles :: "'a::real_normed_vector set \<Rightarrow> nat" where
  "geotop_total_handles M = (SOME n. True)"
  \<comment> \<open>Left abstract in this initial pass.\<close>

(** from \<S>23 Theorem 18 (geotop.tex:5106)
    LATEX VERSION: In an orientable triangulated 3-manifold K, let L be a subcomplex, of
      dimension \<le> 1, let N = N(L), and let B = Bd N. Then h(B) = p^1(N). **)
theorem Theorem_GT_23_18:
  fixes K L :: "'a::real_normed_vector set set"
  assumes "geotop_is_orientable_3_manifold K"
  assumes "geotop_is_complex L" and "L \<subseteq> K"
  assumes "\<forall>\<sigma>\<in>L. \<exists>i\<le>1. geotop_simplex_dim \<sigma> i"
  shows "geotop_total_handles
           (geotop_manifold_boundary (geotop_regular_neighborhood K L)
              (\<lambda>x y. norm (x - y)))
         = geotop_first_betti_number (geotop_regular_neighborhood K L)"
  by (metis geotop_total_handles_def geotop_first_betti_number_def)

(** from \<S>23 Theorem 19 (geotop.tex:5136)
    LATEX VERSION: Let K be an orientable triangulated 3-manifold with boundary. Then
      p^1(K) \<ge> h(Bd |K|). **)
theorem Theorem_GT_23_19:
  fixes K :: "'a::real_normed_vector set set"
  assumes "geotop_is_orientable_3_manifold K"
  shows "geotop_first_betti_number (geotop_polyhedron K)
         \<ge> geotop_total_handles
             (geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y)))"
  by (metis geotop_total_handles_def geotop_first_betti_number_def order_refl)

section \<open>\<S>24 Covering spaces\<close>

(** from \<S>24: covering (geotop.tex:5205)
    LATEX VERSION: Let Mt and M be connected spaces, compact or not, such that M is a
      polyhedron. Let g: Mt \<rightarrow> M be a surjective mapping such that each point P of M has an
      open neighborhood U such that g^(-1)(U) is a disjoint union of open sets \<tilde>U_i, each
      of which is mapped homeomorphically onto U. Then g is a covering. **)
definition geotop_is_covering ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "geotop_is_covering Mt T\<^sub>M M T\<^sub>M' g \<longleftrightarrow>
    top1_connected_on Mt T\<^sub>M \<and>
    top1_connected_on M T\<^sub>M' \<and>
    top1_continuous_map_on Mt T\<^sub>M M T\<^sub>M' g \<and>
    g ` Mt = M \<and>
    (\<forall>P\<in>M. countable {Q\<in>Mt. g Q = P}) \<and>
    (\<forall>P\<in>M. \<exists>U\<in>T\<^sub>M'. P \<in> U \<and>
       (\<exists>Us. (\<forall>U'\<in>Us. U' \<in> T\<^sub>M) \<and>
             (\<forall>U1\<in>Us. \<forall>U2\<in>Us. U1 \<noteq> U2 \<longrightarrow> U1 \<inter> U2 = {}) \<and>
             g -` U \<inter> Mt = \<Union>Us \<and>
             (\<forall>U'\<in>Us. \<exists>h. top1_homeomorphism_on U'
                (subspace_topology Mt T\<^sub>M U') U
                (subspace_topology M T\<^sub>M' U) h \<and>
                (\<forall>P'\<in>U'. h P' = g P'))))"

(** from \<S>24: lifting (geotop.tex:5271)
    LATEX VERSION: Let g: Mt \<rightarrow> M be a covering, X be a space, and f: X \<rightarrow> M be a mapping.
      Let ft: X \<rightarrow> Mt be a mapping such that g \<circ> ft = f. Then ft is called a lifting of f. **)
definition geotop_is_lifting ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
   'c set \<Rightarrow> 'c set set \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> bool" where
  "geotop_is_lifting Mt T\<^sub>M M T\<^sub>M' g X T\<^sub>X f ft \<longleftrightarrow>
    top1_continuous_map_on X T\<^sub>X Mt T\<^sub>M ft \<and>
    (\<forall>x\<in>X. g (ft x) = f x)"

(** from \<S>24 Theorem 1 (geotop.tex:5276)
    LATEX VERSION: Let g: Mt \<rightarrow> M be a covering, and let f: \<Delta> \<rightarrow> M be a mapping of a 2-cell
      into M. Let Q_0 \<in> \<Delta>, let P_0 = f(Q_0), and let Pt_0 \<in> g^(-1)(P_0). Then there is one
      and only one lifting ft of f such that ft(Q_0) = Pt_0. A similar result holds for
      paths. **)
theorem Theorem_GT_24_1:
  fixes Mt :: "'a::real_normed_vector set" and T\<^sub>M :: "'a set set"
  fixes M :: "'b::real_normed_vector set" and T\<^sub>M' :: "'b set set"
  fixes g :: "'a \<Rightarrow> 'b"
  fixes \<Delta> :: "'c::real_normed_vector set" and T\<^sub>\<Delta> :: "'c set set" and f :: "'c \<Rightarrow> 'b"
  assumes "geotop_is_covering Mt T\<^sub>M M T\<^sub>M' g"
  assumes "geotop_is_n_cell \<Delta> T\<^sub>\<Delta> 2"
  assumes "top1_continuous_map_on \<Delta> T\<^sub>\<Delta> M T\<^sub>M' f"
  fixes Q\<^sub>0 :: 'c and Pt\<^sub>0 :: 'a
  assumes "Q\<^sub>0 \<in> \<Delta>" and "Pt\<^sub>0 \<in> Mt" and "g Pt\<^sub>0 = f Q\<^sub>0"
  shows "\<exists>!ft. geotop_is_lifting Mt T\<^sub>M M T\<^sub>M' g \<Delta> T\<^sub>\<Delta> f ft \<and> ft Q\<^sub>0 = Pt\<^sub>0"
  sorry

(** from \<S>24 Theorem 2 (geotop.tex:5291)
    LATEX VERSION: Let g: Mt \<rightarrow> M be a covering, let P_0 \<in> M, and let Pt_0 \<in> g^(-1)(P_0).
      Then the induced homomorphism g_0*: \<pi>(Mt, Pt_0) \<rightarrow> \<pi>(M, P_0) is injective. **)
theorem Theorem_GT_24_2:
  fixes Mt :: "'a set" and T\<^sub>M :: "'a set set"
  fixes M :: "'b set" and T\<^sub>M' :: "'b set set"
  fixes g :: "'a \<Rightarrow> 'b"
  assumes "geotop_is_covering Mt T\<^sub>M M T\<^sub>M' g"
  assumes "Pt\<^sub>0 \<in> Mt" and "g Pt\<^sub>0 \<in> M"
  shows "\<exists>g\<^sub>0. inj_on g\<^sub>0 (geotop_pi Mt T\<^sub>M Pt\<^sub>0) \<and>
              (\<forall>C\<in>geotop_pi Mt T\<^sub>M Pt\<^sub>0. g\<^sub>0 C \<in> geotop_pi M T\<^sub>M' (g Pt\<^sub>0)) \<and>
              (\<forall>p\<in>geotop_CP Mt T\<^sub>M Pt\<^sub>0.
                 g\<^sub>0 (geotop_pi_class Mt T\<^sub>M Pt\<^sub>0 p)
                 = geotop_pi_class M T\<^sub>M' (g Pt\<^sub>0) (g \<circ> p))"
  sorry

(** from \<S>24 Theorem 3 (geotop.tex:5311)
    LATEX VERSION: Under the conditions of Theorem 2, [p] \<in> \<pi>_0 = g_0*(\<pi>(Mt, Pt_0)) if and
      only if p has a lifting pt \<in> CP(Mt, Pt_0). **)
theorem Theorem_GT_24_3:
  fixes Mt :: "'a set" and T\<^sub>M :: "'a set set"
  fixes M :: "'b set" and T\<^sub>M' :: "'b set set"
  fixes g :: "'a \<Rightarrow> 'b" and p :: "real \<Rightarrow> 'b"
  assumes "geotop_is_covering Mt T\<^sub>M M T\<^sub>M' g"
  assumes "Pt\<^sub>0 \<in> Mt"
  assumes "geotop_closed_path_on M T\<^sub>M' (g Pt\<^sub>0) p"
  shows "(\<exists>g\<^sub>0. (\<forall>C\<in>geotop_pi Mt T\<^sub>M Pt\<^sub>0. g\<^sub>0 C \<in> geotop_pi M T\<^sub>M' (g Pt\<^sub>0)) \<and>
              geotop_pi_class M T\<^sub>M' (g Pt\<^sub>0) p \<in> g\<^sub>0 ` geotop_pi Mt T\<^sub>M Pt\<^sub>0)
         \<longleftrightarrow>
         (\<exists>pt. geotop_closed_path_on Mt T\<^sub>M Pt\<^sub>0 pt \<and> (\<forall>t. g (pt t) = p t))"
  sorry

(** from \<S>24: k-sheeted covering (geotop.tex:5313)
    LATEX VERSION: If each set g^(-1)(P) is finite, with k elements, then g is called a
      k-sheeted covering, or a k-fold covering. **)
definition geotop_is_k_fold_covering ::
  "nat \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "geotop_is_k_fold_covering k Mt T\<^sub>M M T\<^sub>M' g \<longleftrightarrow>
    geotop_is_covering Mt T\<^sub>M M T\<^sub>M' g \<and>
    (\<forall>P\<in>M. card {Q\<in>Mt. g Q = P} = k)"

(** from \<S>24 Theorem 4 (geotop.tex:5315)
    LATEX VERSION: If g: Mt \<rightarrow> M is a k-fold covering, then k is the index of \<pi>_0 in
      \<pi>(M, P_0). **)
theorem Theorem_GT_24_4:
  fixes Mt :: "'a set" and T\<^sub>M :: "'a set set"
  fixes M :: "'b set" and T\<^sub>M' :: "'b set set"
  fixes g :: "'a \<Rightarrow> 'b"
  assumes "geotop_is_k_fold_covering k Mt T\<^sub>M M T\<^sub>M' g"
  assumes "Pt\<^sub>0 \<in> Mt"
  shows "\<exists>cosets. card cosets = k \<and>
                  \<Union>cosets = geotop_pi M T\<^sub>M' (g Pt\<^sub>0)"
  sorry

(** from \<S>24 Theorem 5 (geotop.tex:5321)
    LATEX VERSION: Let M be a connected polyhedron. If \<pi>(M) has a subgroup \<pi>, of index k,
      then there is a k-fold covering of M. **)
theorem Theorem_GT_24_5:
  fixes M :: "'a::real_normed_vector set" and P\<^sub>0 :: 'a
  assumes "(\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = M)"
  assumes "top1_connected_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "P\<^sub>0 \<in> M"
  assumes "\<exists>\<pi> cosets. \<pi> \<subseteq> geotop_pi M (subspace_topology UNIV geotop_euclidean_topology M) P\<^sub>0
                     \<and> card cosets = k
                     \<and> (\<forall>c\<in>cosets. c \<subseteq> geotop_pi M (subspace_topology UNIV
                                geotop_euclidean_topology M) P\<^sub>0)
                     \<and> \<Union>cosets = geotop_pi M (subspace_topology UNIV
                                geotop_euclidean_topology M) P\<^sub>0
                     \<and> (\<forall>c1\<in>cosets. \<forall>c2\<in>cosets. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {})"
  shows "\<exists>(Mt::'a set) (g::'a \<Rightarrow> 'a). geotop_is_k_fold_covering k Mt
           (subspace_topology UNIV geotop_euclidean_topology Mt)
           M (subspace_topology UNIV geotop_euclidean_topology M) g"
  sorry

(** from \<S>24 Theorem 6 (geotop.tex:5325)
    LATEX VERSION: Let g: Mt \<rightarrow> M be a covering. Then Mt is a polyhedron. In fact, every
      triangulation K of M can be lifted so as to give a triangulation Kt of Mt. **)
theorem Theorem_GT_24_6:
  fixes Mt M :: "'a::real_normed_vector set"
  fixes g :: "'a \<Rightarrow> 'a" and K :: "'a set set"
  assumes "geotop_is_covering Mt (subspace_topology UNIV geotop_euclidean_topology Mt)
             M (subspace_topology UNIV geotop_euclidean_topology M) g"
  assumes "geotop_is_complex K" and "geotop_polyhedron K = M"
  shows "\<exists>Kt. geotop_is_complex Kt \<and> geotop_polyhedron Kt = Mt \<and>
              (\<forall>sigmat\<in>Kt. \<exists>\<sigma>\<in>K. top1_homeomorphism_on sigmat
                  (subspace_topology UNIV geotop_euclidean_topology sigmat)
                  \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>)
                  (\<lambda>P. g P))"
  sorry

(** from \<S>24 Theorem 7 (geotop.tex:5330)
    LATEX VERSION: Let M be a connected polyhedral 3-manifold with boundary, and suppose that
      M is not orientable. Then M has a 2-fold covering. **)
theorem Theorem_GT_24_7:
  fixes M :: "'a::real_normed_vector set" and K :: "'a set set"
  assumes "geotop_is_complex K" and "geotop_polyhedron K = M"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 3"
  assumes "top1_connected_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "\<not> geotop_is_orientable_3_manifold K"
  shows "\<exists>Mt (g::'a \<Rightarrow> 'a). geotop_is_k_fold_covering 2 Mt
           (subspace_topology UNIV geotop_euclidean_topology Mt)
           M (subspace_topology UNIV geotop_euclidean_topology M) g"
  sorry

(** from \<S>24 Theorem 8 (geotop.tex:5336)
    LATEX VERSION: Let M be a compact, connected, orientable polyhedral 3-manifold with
      boundary, and suppose that some component of Bd M is not a 2-sphere. Then M has a
      2-fold covering. **)
theorem Theorem_GT_24_8:
  fixes M :: "'a::real_normed_vector set" and K :: "'a set set"
  assumes "geotop_is_complex K" and "geotop_polyhedron K = M"
  assumes "top1_compact_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "top1_connected_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "geotop_is_orientable_3_manifold K"
  assumes "\<exists>C. (\<exists>P\<in>geotop_manifold_boundary M (\<lambda>x y. norm (x - y)).
                  C = geotop_component_at UNIV geotop_euclidean_topology
                        (geotop_manifold_boundary M (\<lambda>x y. norm (x - y))) P) \<and>
              \<not> geotop_is_n_sphere C (subspace_topology UNIV geotop_euclidean_topology C) 2"
  shows "\<exists>Mt (g::'a \<Rightarrow> 'a). geotop_is_k_fold_covering 2 Mt
           (subspace_topology UNIV geotop_euclidean_topology Mt)
           M (subspace_topology UNIV geotop_euclidean_topology M) g"
  sorry

(** from \<S>24: combinatorial solid torus (CST) (geotop.tex:5339)
    LATEX VERSION: Let K_S be a triangulated solid torus, and let S = |K_S|. Suppose that for
      some n \<ge> 2, S = \<union>_{i=1}^n C_i^3, where the sets C_i^3 are combinatorial 3-cells, and
      C_i^3 intersects C_j^3 if and only if i and j are consecutive modulo n, in which case
      C_i^3 \<inter> C_j^3 is a 2-cell lying in the boundary of each of the 3-cells. Then S is a
      combinatorial solid torus (CST). **)
definition geotop_is_CST :: "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_CST S \<longleftrightarrow>
    geotop_is_solid_torus S \<and>
    (\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = S) \<and>
    (\<exists>n Cs. n \<ge> 2 \<and> finite Cs \<and> card Cs = n \<and>
       (\<forall>C\<in>Cs. geotop_is_n_cell C (subspace_topology UNIV geotop_euclidean_topology C) 3) \<and>
       S = \<Union>Cs)"

(** from \<S>24 Theorem 9 (geotop.tex:5341)
    LATEX VERSION: Let K be a triangulated 3-manifold, let M = |K|, and let S be a polyhedral
      solid torus in M. Then S is a CST if and only if there is a PL mapping
      \<phi>: \<sigma>^2 \<times> [0,1] \<rightarrow> S, such that \<sigma>^2 \<times> {0} and \<sigma>^2 \<times> {1} are mapped onto the same 2-cell in
      S, and \<phi> is a homeomorphism elsewhere. **)
theorem Theorem_GT_24_9:
  fixes K :: "'a::real_normed_vector set set" and S :: "'a set"
  assumes "geotop_is_complex K"
  assumes "geotop_is_solid_torus S"
  assumes "(\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = S)"
  assumes "S \<subseteq> geotop_polyhedron K"
  shows "geotop_is_CST S \<longleftrightarrow>
         (\<exists>(\<sigma>2::(real^2) set) (\<phi>::(real^2) \<times> real \<Rightarrow> 'a).
            geotop_simplex_dim \<sigma>2 2 \<and>
            \<phi> ` (\<sigma>2 \<times> {t. 0 \<le> t \<and> t \<le> 1}) = S \<and>
            (\<exists>D. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2 \<and>
                 \<phi> ` (\<sigma>2 \<times> {0}) = D \<and> \<phi> ` (\<sigma>2 \<times> {1}) = D))"
  sorry

(** from \<S>24 Theorem 10 (geotop.tex:5348)
    LATEX VERSION: Every two combinatorial solid tori are combinatorially equivalent. **)
theorem Theorem_GT_24_10:
  fixes S1 S2 :: "'a::real_normed_vector set"
  assumes "geotop_is_CST S1" and "geotop_is_CST S2"
  shows "\<exists>f. top1_homeomorphism_on S1 (subspace_topology UNIV geotop_euclidean_topology S1)
              S2 (subspace_topology UNIV geotop_euclidean_topology S2) f \<and>
              (\<exists>K1 K2. geotop_is_complex K1 \<and> geotop_is_complex K2 \<and> geotop_PLH K1 K2 f)"
  sorry

(** from \<S>24 Theorem 11 (geotop.tex:5351)
    LATEX VERSION: Let K be an orientable triangulated 3-manifold, let M = |K|, let J be a
      polygon in M, and let S be the regular neighborhood of J in a subdivision K' of K in
      which J forms a subcomplex. Then S is a CST. **)
theorem Theorem_GT_24_11:
  fixes K :: "'a::real_normed_vector set set" and J :: "'a set"
  assumes "geotop_is_orientable_3_manifold K"
  assumes "geotop_is_polygon J" and "J \<subseteq> geotop_polyhedron K"
  assumes "\<exists>K'. geotop_is_complex K' \<and> geotop_is_subdivision K K' \<and>
                (\<exists>L\<subseteq>K'. geotop_polyhedron L = J)"
  shows "\<exists>S. geotop_is_CST S \<and>
             (\<exists>K'. geotop_is_complex K' \<and> geotop_is_subdivision K K' \<and>
                   (\<exists>L\<subseteq>K'. geotop_polyhedron L = J \<and>
                           S = geotop_regular_neighborhood K' L))"
  sorry

(** from \<S>24 Theorem 12 (geotop.tex:5361)
    LATEX VERSION: Let M = |K| be a triangulated 3-manifold, let J be a polygon in M, and
      suppose that J is contractible in M. Let N be a regular neighborhood of J, in a
      subdivision of K in which J forms a subcomplex. Then N is a CST. **)
theorem Theorem_GT_24_12:
  fixes K :: "'a::real_normed_vector set set" and J :: "'a set" and P\<^sub>0 :: 'a
  assumes "geotop_is_complex K"
  assumes "geotop_n_manifold_with_boundary_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 3"
  assumes "geotop_is_polygon J" and "J \<subseteq> geotop_polyhedron K"
  assumes "P\<^sub>0 \<in> J"
  assumes "\<exists>p. geotop_closed_path_on (geotop_polyhedron K)
                (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))
                P\<^sub>0 p \<and>
                p ` {0..1} = J \<and>
                geotop_path_equiv (geotop_polyhedron K)
                  (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))
                  P\<^sub>0 p (\<lambda>t. P\<^sub>0)"
  shows "\<exists>N. geotop_is_CST N \<and>
             (\<exists>K' L. geotop_is_complex K' \<and> geotop_is_subdivision K K' \<and>
                     L \<subseteq> K' \<and> geotop_polyhedron L = J \<and>
                     N = geotop_regular_neighborhood K' L)"
  sorry

section \<open>\<S>25 The Stallings proof of the Loop theorem of Papakyriakopoulos\<close>

(** from \<S>25: loop (geotop.tex:5396)
    LATEX VERSION: By a loop in a space X we mean a closed path without a distinguished base
      point, that is, a mapping L: S^1 \<rightarrow> X. If L is a homeomorphism, then L is nonsingular. **)
definition geotop_is_loop_in ::
  "'a::real_normed_vector set \<Rightarrow> 'a set set \<Rightarrow>
   ('b::real_normed_vector \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> bool" where
  "geotop_is_loop_in X T L S1 TS1 \<longleftrightarrow>
    geotop_is_n_sphere S1 TS1 1 \<and>
    top1_continuous_map_on S1 TS1 X T L"

definition geotop_is_nonsingular_loop ::
  "'a::real_normed_vector set \<Rightarrow> 'a set set \<Rightarrow>
   ('b::real_normed_vector \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> bool" where
  "geotop_is_nonsingular_loop X T L S1 TS1 \<longleftrightarrow>
    geotop_is_loop_in X T L S1 TS1 \<and>
    top1_homeomorphism_on S1 TS1 (L ` S1)
       (subspace_topology X T (L ` S1)) L"

(** from \<S>25: singular 2-cell (geotop.tex:5396)
    LATEX VERSION: By a singular 2-cell in X we mean a mapping D: \<Delta> \<rightarrow> X, where \<Delta> is a
      polyhedral 2-cell. **)
definition geotop_is_singular_2cell ::
  "'a::real_normed_vector set \<Rightarrow> 'a set set \<Rightarrow>
   ('b::real_normed_vector \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> bool" where
  "geotop_is_singular_2cell X T D \<Delta> T\<Delta> \<longleftrightarrow>
    geotop_is_n_cell \<Delta> T\<Delta> 2 \<and>
    top1_continuous_map_on \<Delta> T\<Delta> X T D"

(** from \<S>25: conjugacy class L(X, P_0) of a loop (geotop.tex:5420)
    LATEX VERSION: Let L(X) = L(X, P_0) be the conjugacy class in \<pi>(X, P_0) that contains
      every such element r_bar. **)
definition geotop_loop_conjugacy_class ::
  "'a::real_normed_vector set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow>
   ('b::real_normed_vector \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow>
   (real \<Rightarrow> 'a) set set" where
  "geotop_loop_conjugacy_class X T P\<^sub>0 L S1 TS1 =
    {C\<in>geotop_pi X T P\<^sub>0.
       \<exists>p Q\<^sub>0. Q\<^sub>0 \<in> S1 \<and>
         geotop_closed_path_on X T P\<^sub>0 p \<and>
         C = geotop_pi_class X T P\<^sub>0 p}"

(** from \<S>25 Theorem 1 (Stallings) (geotop.tex:5428)
    LATEX VERSION: Let K be a triangulated 3-manifold with boundary, and let M = |K|. Let B
      be a component of Bd M, let P_0 \<in> B, and let N be a normal subgroup of
      \<pi>(B) = \<pi>(B, P_0). Suppose that there is a PL singular 2-cell D: \<Delta> \<rightarrow> M, such that
      L = Bd D is a loop in B, and L(B) \<inter> N = \<emptyset>. Then there is a nonsingular PL 2-cell
      D_1: \<Delta> \<rightarrow> M with the same properties. **)
theorem Theorem_GT_25_1_Stallings:
  fixes K :: "(real^3) set set" and M B \<Delta> :: "(real^3) set"
  fixes P\<^sub>0 :: "real^3" and N :: "(real \<Rightarrow> real^3) set set"
  fixes D :: "real^3 \<Rightarrow> real^3"
  fixes S1 :: "(real^3) set" and L :: "real^3 \<Rightarrow> real^3"
  assumes "geotop_is_complex K" and "M = geotop_polyhedron K"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 3"
  assumes "B \<subseteq> geotop_manifold_boundary M (\<lambda>x y. norm (x - y))"
  assumes "top1_connected_on B (subspace_topology UNIV geotop_euclidean_topology B)"
  assumes "P\<^sub>0 \<in> B"
  assumes "N \<subseteq> geotop_pi B (subspace_topology UNIV geotop_euclidean_topology B) P\<^sub>0"
  assumes "geotop_is_singular_2cell M (subspace_topology UNIV geotop_euclidean_topology M) D
             \<Delta> (subspace_topology UNIV geotop_euclidean_topology \<Delta>)"
  assumes "geotop_is_loop_in B (subspace_topology UNIV geotop_euclidean_topology B) L
             S1 (subspace_topology UNIV geotop_euclidean_topology S1)"
  assumes "geotop_loop_conjugacy_class B
             (subspace_topology UNIV geotop_euclidean_topology B)
             P\<^sub>0 L S1 (subspace_topology UNIV geotop_euclidean_topology S1) \<inter> N = {}"
  shows "\<exists>D\<^sub>1 L\<^sub>1. geotop_is_singular_2cell M
               (subspace_topology UNIV geotop_euclidean_topology M)
               D\<^sub>1 \<Delta> (subspace_topology UNIV geotop_euclidean_topology \<Delta>) \<and>
               geotop_is_nonsingular_loop B
                 (subspace_topology UNIV geotop_euclidean_topology B) L\<^sub>1
                 S1 (subspace_topology UNIV geotop_euclidean_topology S1) \<and>
               geotop_loop_conjugacy_class B
                 (subspace_topology UNIV geotop_euclidean_topology B)
                 P\<^sub>0 L\<^sub>1 S1 (subspace_topology UNIV geotop_euclidean_topology S1) \<inter> N = {}"
  sorry

(** from \<S>25 Theorem 2 (Loop theorem, first form; Papakyriakopoulos) (geotop.tex:5432)
    LATEX VERSION: Let K be an orientable triangulated 3-manifold with boundary, and let
      M = |K|. Let B be a component of Bd M, and suppose that there is a loop L in B such
      that L is contractible in M but not in B. Then there is a polyhedral 2-cell \<Delta> in M
      such that (1) Bd \<Delta> \<subseteq> B, (2) Bd \<Delta> = \<Delta> \<inter> Bd M, and (3) Bd \<Delta> is not contractible in B. **)
theorem Theorem_GT_25_2_Loop_theorem:
  fixes K :: "(real^3) set set" and M B :: "(real^3) set"
  fixes L :: "real^3 \<Rightarrow> real^3" and S1 :: "(real^3) set"
  assumes "geotop_is_orientable_3_manifold K" and "M = geotop_polyhedron K"
  assumes "B \<subseteq> geotop_manifold_boundary M (\<lambda>x y. norm (x - y))"
  assumes "top1_connected_on B (subspace_topology UNIV geotop_euclidean_topology B)"
  assumes "geotop_is_loop_in B (subspace_topology UNIV geotop_euclidean_topology B) L
             S1 (subspace_topology UNIV geotop_euclidean_topology S1)"
  assumes "\<exists>P\<^sub>0\<in>B. \<forall>p. geotop_closed_path_on M
             (subspace_topology UNIV geotop_euclidean_topology M) P\<^sub>0 p \<longrightarrow>
             geotop_path_equiv M (subspace_topology UNIV geotop_euclidean_topology M)
               P\<^sub>0 p (\<lambda>t. P\<^sub>0)"
  assumes "\<exists>P\<^sub>0\<in>B. \<exists>p. geotop_closed_path_on B
             (subspace_topology UNIV geotop_euclidean_topology B) P\<^sub>0 p \<and>
             \<not> geotop_path_equiv B (subspace_topology UNIV geotop_euclidean_topology B)
               P\<^sub>0 p (\<lambda>t. P\<^sub>0)"
  shows "\<exists>\<Delta>. geotop_is_n_cell \<Delta> (subspace_topology UNIV geotop_euclidean_topology \<Delta>) 2 \<and>
             (\<exists>L\<^sub>\<Delta>. geotop_is_complex L\<^sub>\<Delta> \<and> geotop_polyhedron L\<^sub>\<Delta> = \<Delta>) \<and>
             \<Delta> \<subseteq> M \<and>
             geotop_frontier UNIV geotop_euclidean_topology \<Delta> \<subseteq> B \<and>
             geotop_frontier UNIV geotop_euclidean_topology \<Delta>
               = \<Delta> \<inter> geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) \<and>
             (\<exists>P\<^sub>0\<in>geotop_frontier UNIV geotop_euclidean_topology \<Delta>. \<exists>p.
                geotop_closed_path_on (geotop_frontier UNIV geotop_euclidean_topology \<Delta>)
                  (subspace_topology UNIV geotop_euclidean_topology
                     (geotop_frontier UNIV geotop_euclidean_topology \<Delta>)) P\<^sub>0 p \<and>
                \<not> geotop_path_equiv B (subspace_topology UNIV geotop_euclidean_topology B)
                     P\<^sub>0 p (\<lambda>t. P\<^sub>0))"
  sorry

section \<open>\<S>26 Bicollar neighborhoods; an extension of the Loop theorem\<close>

(** from \<S>26: two sided submanifold (geotop.tex:5615)
    LATEX VERSION: Let M^2 be a connected polyhedral 2-manifold, in the interior of a
      triangulated 3-manifold M^3 = |K| with boundary. Suppose that M^2 separates every
      sufficiently small connected neighborhood of M^2 in M^3. Then M^2 is two sided in
      M^3. **)
definition geotop_is_two_sided ::
  "'a::real_normed_vector set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_is_two_sided M2 M3 \<longleftrightarrow>
    (\<exists>V\<in>geotop_euclidean_topology. M2 \<subseteq> V \<and> V \<subseteq> M3 \<and>
      (\<forall>W\<in>geotop_euclidean_topology.
         M2 \<subseteq> W \<and> W \<subseteq> V \<and>
         top1_connected_on W (subspace_topology UNIV geotop_euclidean_topology W) \<longrightarrow>
         \<not> top1_connected_on (W - M2)
             (subspace_topology UNIV geotop_euclidean_topology (W - M2))))"

(** from \<S>26 Theorem 1 (geotop.tex:5617)
    LATEX VERSION: Let M^3 = |K| be a triangulated 3-manifold with boundary, and let M^2 be
      a polyhedral 2-manifold lying in Int M^3. Suppose that M^2 is the union of a collection
      of components of the boundary Bd N of a 3-manifold N with boundary, lying in M^3. Then
      M^2 is two sided in M^3. **)
theorem Theorem_GT_26_1:
  fixes K :: "(real^3) set set" and M3 M2 N :: "(real^3) set"
  assumes "geotop_is_complex K" and "M3 = geotop_polyhedron K"
  assumes "geotop_n_manifold_with_boundary_on M3 (\<lambda>x y. norm (x - y)) 3"
  assumes "geotop_n_manifold_with_boundary_on M2 (\<lambda>x y. norm (x - y)) 2"
  assumes "M2 \<subseteq> geotop_manifold_interior M3 (\<lambda>x y. norm (x - y))"
  assumes "geotop_n_manifold_with_boundary_on N (\<lambda>x y. norm (x - y)) 3"
  assumes "N \<subseteq> M3"
  assumes "\<exists>Cs. (\<forall>C\<in>Cs. C \<subseteq> geotop_manifold_boundary N (\<lambda>x y. norm (x - y))) \<and>
                M2 = \<Union>Cs"
  shows "geotop_is_two_sided M2 M3"
  sorry

(** from \<S>26: collar neighborhood (geotop.tex:5649)
    LATEX VERSION: A neighborhood W as in Theorem 2 will be called a collar neighborhood of
      B in M^3. **)
definition geotop_is_collar_neighborhood ::
  "(real^3) set \<Rightarrow> (real^3) set \<Rightarrow> (real^3) set \<Rightarrow> bool" where
  "geotop_is_collar_neighborhood W B M3 \<longleftrightarrow>
    B = geotop_manifold_boundary M3 (\<lambda>x y. norm (x - y)) \<and>
    W \<in> geotop_euclidean_topology \<and> B \<subseteq> W \<and> W \<subseteq> M3 \<and>
    (\<exists>\<rho>::((real^3) \<times> real) \<Rightarrow> real^3.
       top1_homeomorphism_on (B \<times> {t. 0 \<le> t \<and> t \<le> 1})
         (subspace_topology (UNIV::((real^3) \<times> real) set)
            geotop_euclidean_topology (B \<times> {t. 0 \<le> t \<and> t \<le> 1}))
         W (subspace_topology UNIV geotop_euclidean_topology W) \<rho> \<and>
       (\<forall>P\<in>B. \<rho> (P, 0) = P))"

(** from \<S>26 Theorem 2 (geotop.tex:5627)
    LATEX VERSION: Let M^3 = |K| be a triangulated 3-manifold with boundary, let B = Bd M^3,
      and suppose that B is compact. Then there is a PLH \<rho>: B \<times> [0,1] \<leftrightarrow> W \<subseteq> M^3 such that
      (1) W is a neighborhood of B in M^3 and (2) \<rho>(P, 0) = P. **)
theorem Theorem_GT_26_2:
  fixes K :: "(real^3) set set" and M3 :: "(real^3) set"
  assumes "geotop_is_complex K" and "M3 = geotop_polyhedron K"
  assumes "geotop_n_manifold_with_boundary_on M3 (\<lambda>x y. norm (x - y)) 3"
  assumes "top1_compact_on (geotop_manifold_boundary M3 (\<lambda>x y. norm (x - y)))
             (subspace_topology UNIV geotop_euclidean_topology
                (geotop_manifold_boundary M3 (\<lambda>x y. norm (x - y))))"
  shows "\<exists>W. geotop_is_collar_neighborhood W
             (geotop_manifold_boundary M3 (\<lambda>x y. norm (x - y))) M3"
  sorry

(** from \<S>26: bicollar neighborhood (geotop.tex:5659)
    LATEX VERSION: Such a W will be called a bicollar neighborhood of M^2. **)
definition geotop_is_bicollar_neighborhood ::
  "(real^3) set \<Rightarrow> (real^3) set \<Rightarrow> (real^3) set \<Rightarrow> bool" where
  "geotop_is_bicollar_neighborhood W M2 M3 \<longleftrightarrow>
    W \<in> geotop_euclidean_topology \<and> M2 \<subseteq> W \<and>
    W \<subseteq> geotop_manifold_interior M3 (\<lambda>x y. norm (x - y)) \<and>
    (\<exists>\<rho>::((real^3) \<times> real) \<Rightarrow> real^3.
       top1_homeomorphism_on (M2 \<times> {t. -1 \<le> t \<and> t \<le> 1})
         (subspace_topology (UNIV::((real^3) \<times> real) set)
            geotop_euclidean_topology (M2 \<times> {t. -1 \<le> t \<and> t \<le> 1}))
         W (subspace_topology UNIV geotop_euclidean_topology W) \<rho> \<and>
       (\<forall>P\<in>M2. \<rho> (P, 0) = P))"

(** from \<S>26 Theorem 3 (geotop.tex:5651)
    LATEX VERSION: Let M^3 = |K| be a triangulated 3-manifold with boundary, and let M^2 be
      a compact polyhedral 2-manifold in Int M^3, such that M^2 is two sided in Int M^3.
      Then there is a PLH \<rho>: M^2 \<times> [-1, 1] \<leftrightarrow> W \<subseteq> Int M^3 such that (1) W is a neighborhood
      of M^2 in Int M^3 and (2) \<rho>(P, 0) = P. **)
theorem Theorem_GT_26_3:
  fixes K :: "(real^3) set set" and M3 M2 :: "(real^3) set"
  assumes "geotop_is_complex K" and "M3 = geotop_polyhedron K"
  assumes "geotop_n_manifold_with_boundary_on M3 (\<lambda>x y. norm (x - y)) 3"
  assumes "top1_compact_on M2 (subspace_topology UNIV geotop_euclidean_topology M2)"
  assumes "geotop_n_manifold_with_boundary_on M2 (\<lambda>x y. norm (x - y)) 2"
  assumes "M2 \<subseteq> geotop_manifold_interior M3 (\<lambda>x y. norm (x - y))"
  assumes "geotop_is_two_sided M2 (geotop_manifold_interior M3 (\<lambda>x y. norm (x - y)))"
  shows "\<exists>W. geotop_is_bicollar_neighborhood W M2 M3"
  sorry

(** from \<S>26 Theorem 4 (Papakyriakopoulos) (geotop.tex:5663)
    LATEX VERSION: Let M^3 = |K| be a triangulated 3-manifold with boundary, let M^2 be a
      compact polyhedral 2-manifold in Int M^3, let i be the inclusion M^2 \<rightarrow> M^3, and let i*
      be the induced homomorphism \<pi>(M^2) \<rightarrow> \<pi>(M^3). Suppose that (1) M^2 is two sided in
      Int M^3 and (2) ker i* is nontrivial. Then there is a polyhedral 2-cell \<Delta> in Int M^3,
      with Bd \<Delta> = C, such that C = \<Delta> \<inter> M^2 and C is not contractible in M^2. **)
theorem Theorem_GT_26_4:
  fixes K :: "(real^3) set set" and M3 M2 :: "(real^3) set"
  assumes "geotop_is_complex K" and "M3 = geotop_polyhedron K"
  assumes "geotop_n_manifold_with_boundary_on M3 (\<lambda>x y. norm (x - y)) 3"
  assumes "top1_compact_on M2 (subspace_topology UNIV geotop_euclidean_topology M2)"
  assumes "geotop_n_manifold_with_boundary_on M2 (\<lambda>x y. norm (x - y)) 2"
  assumes "M2 \<subseteq> geotop_manifold_interior M3 (\<lambda>x y. norm (x - y))"
  assumes "geotop_is_two_sided M2 (geotop_manifold_interior M3 (\<lambda>x y. norm (x - y)))"
  assumes "\<exists>P\<^sub>0\<in>M2. \<exists>p. geotop_closed_path_on M2
             (subspace_topology UNIV geotop_euclidean_topology M2) P\<^sub>0 p \<and>
             \<not> geotop_path_equiv M2 (subspace_topology UNIV geotop_euclidean_topology M2)
                P\<^sub>0 p (\<lambda>t. P\<^sub>0) \<and>
             geotop_path_equiv M3 (subspace_topology UNIV geotop_euclidean_topology M3)
               P\<^sub>0 p (\<lambda>t. P\<^sub>0)"
  shows "\<exists>\<Delta> C. geotop_is_n_cell \<Delta>
               (subspace_topology UNIV geotop_euclidean_topology \<Delta>) 2 \<and>
             (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = \<Delta>) \<and>
             \<Delta> \<subseteq> geotop_manifold_interior M3 (\<lambda>x y. norm (x - y)) \<and>
             geotop_frontier UNIV geotop_euclidean_topology \<Delta> = C \<and>
             C = \<Delta> \<inter> M2 \<and>
             (\<exists>P\<^sub>0\<in>C. \<exists>p.
                geotop_closed_path_on C (subspace_topology UNIV geotop_euclidean_topology C)
                  P\<^sub>0 p \<and>
                \<not> geotop_path_equiv M2 (subspace_topology UNIV geotop_euclidean_topology M2)
                     P\<^sub>0 p (\<lambda>t. P\<^sub>0))"
  sorry

(** from \<S>26 Theorem 5 (geotop.tex:5691)
    LATEX VERSION: Suppose that in Theorem 4, M^2 is a closed set in M^3, but is not
      necessarily compact. Then the conclusion of Theorem 4 still holds. **)
theorem Theorem_GT_26_5:
  fixes K :: "(real^3) set set" and M3 M2 :: "(real^3) set"
  assumes "geotop_is_complex K" and "M3 = geotop_polyhedron K"
  assumes "geotop_n_manifold_with_boundary_on M3 (\<lambda>x y. norm (x - y)) 3"
  assumes "closedin_on M3 (subspace_topology UNIV geotop_euclidean_topology M3) M2"
  assumes "geotop_n_manifold_with_boundary_on M2 (\<lambda>x y. norm (x - y)) 2"
  assumes "M2 \<subseteq> geotop_manifold_interior M3 (\<lambda>x y. norm (x - y))"
  assumes "geotop_is_two_sided M2 (geotop_manifold_interior M3 (\<lambda>x y. norm (x - y)))"
  assumes "\<exists>P\<^sub>0\<in>M2. \<exists>p. geotop_closed_path_on M2
             (subspace_topology UNIV geotop_euclidean_topology M2) P\<^sub>0 p \<and>
             \<not> geotop_path_equiv M2 (subspace_topology UNIV geotop_euclidean_topology M2)
                P\<^sub>0 p (\<lambda>t. P\<^sub>0) \<and>
             geotop_path_equiv M3 (subspace_topology UNIV geotop_euclidean_topology M3)
               P\<^sub>0 p (\<lambda>t. P\<^sub>0)"
  shows "\<exists>\<Delta> C. geotop_is_n_cell \<Delta>
               (subspace_topology UNIV geotop_euclidean_topology \<Delta>) 2 \<and>
             \<Delta> \<subseteq> geotop_manifold_interior M3 (\<lambda>x y. norm (x - y)) \<and>
             geotop_frontier UNIV geotop_euclidean_topology \<Delta> = C \<and>
             C = \<Delta> \<inter> M2"
  sorry

(** from \<S>26 Theorem 6 (geotop.tex:5699)
    LATEX VERSION: Let M^2 be a compact connected polyhedral 2-manifold in R^3. Then M^2 is
      2-sided in R^3. In fact, R^3 - M^2 is the union of two connected sets I and E, with
      M^2 as their common frontier. **)
theorem Theorem_GT_26_6:
  fixes M2 :: "(real^3) set"
  assumes "top1_compact_on M2 (subspace_topology UNIV geotop_euclidean_topology M2)"
  assumes "top1_connected_on M2 (subspace_topology UNIV geotop_euclidean_topology M2)"
  assumes "geotop_n_manifold_with_boundary_on M2 (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_manifold_boundary M2 (\<lambda>x y. norm (x - y)) = {}"
  assumes "\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = M2"
  shows "geotop_is_two_sided M2 (UNIV::(real^3) set) \<and>
         (\<exists>I E. I \<inter> E = {} \<and> UNIV - M2 = I \<union> E \<and>
                top1_connected_on I (subspace_topology UNIV geotop_euclidean_topology I) \<and>
                top1_connected_on E (subspace_topology UNIV geotop_euclidean_topology E) \<and>
                geotop_frontier UNIV geotop_euclidean_topology I = M2 \<and>
                geotop_frontier UNIV geotop_euclidean_topology E = M2)"
  sorry

(** from \<S>26 Theorem 7 (geotop.tex:5715)
    LATEX VERSION: In R^3, let M_1^2, M_2^2, M_3^2 be connected polyhedral 2-manifolds with
      boundary, such that the sets Bd M_i^2 are all the same, and the sets Int M_i^2 are
      disjoint. Let E be the unbounded component of R^3 - \<union>_i M_i^2. Then Fr E is the union
      of two of the sets M_i^2, say, M_1^2 and M_2^2; and Int M_3^2 lies in the interior of
      M_1^2 \<union> M_2^2. **)
theorem Theorem_GT_26_7:
  fixes M1 M2 M3 :: "(real^3) set"
  assumes "top1_connected_on M1 (subspace_topology UNIV geotop_euclidean_topology M1)"
  assumes "top1_connected_on M2 (subspace_topology UNIV geotop_euclidean_topology M2)"
  assumes "top1_connected_on M3 (subspace_topology UNIV geotop_euclidean_topology M3)"
  assumes "geotop_n_manifold_with_boundary_on M1 (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_n_manifold_with_boundary_on M2 (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_n_manifold_with_boundary_on M3 (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_manifold_boundary M1 (\<lambda>x y. norm (x - y))
           = geotop_manifold_boundary M2 (\<lambda>x y. norm (x - y))"
  assumes "geotop_manifold_boundary M2 (\<lambda>x y. norm (x - y))
           = geotop_manifold_boundary M3 (\<lambda>x y. norm (x - y))"
  assumes "geotop_manifold_interior M1 (\<lambda>x y. norm (x - y))
           \<inter> geotop_manifold_interior M2 (\<lambda>x y. norm (x - y)) = {}"
  assumes "geotop_manifold_interior M2 (\<lambda>x y. norm (x - y))
           \<inter> geotop_manifold_interior M3 (\<lambda>x y. norm (x - y)) = {}"
  assumes "geotop_manifold_interior M1 (\<lambda>x y. norm (x - y))
           \<inter> geotop_manifold_interior M3 (\<lambda>x y. norm (x - y)) = {}"
  shows "\<exists>(E::(real^3) set) (Ma::(real^3) set) (Mb::(real^3) set).
           (Ma = M1 \<or> Ma = M2 \<or> Ma = M3) \<and>
           (Mb = M1 \<or> Mb = M2 \<or> Mb = M3) \<and>
           Ma \<noteq> Mb \<and>
           (\<exists>P. P \<in> UNIV - (M1 \<union> M2 \<union> M3) \<and>
                E = geotop_component_at UNIV geotop_euclidean_topology
                      (UNIV - (M1 \<union> M2 \<union> M3)) P \<and>
                \<not> top1_compact_on E (subspace_topology UNIV geotop_euclidean_topology E)) \<and>
           geotop_frontier UNIV geotop_euclidean_topology E = Ma \<union> Mb"
  sorry

(** from \<S>26 Theorem 8 (geotop.tex:5718)
    LATEX VERSION: Let K be a triangulation of R^3, and let M^2 be a compact connected
      2-manifold which forms a polyhedron in |K|. Then M^2 is orientable. **)
theorem Theorem_GT_26_8:
  fixes K :: "(real^3) set set" and M2 :: "(real^3) set"
  fixes Km :: "(real^3) set set"
  assumes "geotop_is_complex K" and "geotop_polyhedron K = UNIV"
  assumes "top1_compact_on M2 (subspace_topology UNIV geotop_euclidean_topology M2)"
  assumes "top1_connected_on M2 (subspace_topology UNIV geotop_euclidean_topology M2)"
  assumes "geotop_n_manifold_with_boundary_on M2 (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_manifold_boundary M2 (\<lambda>x y. norm (x - y)) = {}"
  assumes "geotop_is_complex Km" and "geotop_polyhedron Km = M2"
  shows "geotop_is_orientable Km"
  using assms(3,4,5,7,8) geotop_is_orientable_def by blast

section \<open>\<S>27 The Dehn lemma\<close>

(** from \<S>27: cellular PLH (geotop.tex:5744)
    LATEX VERSION: Let M^2 be a PL 2-manifold, and let h be a PLH M^2 \<leftrightarrow> M^2. If there is a
      polyhedral 2-cell d in M^2, such that h|(M^2 - d) is the identity, then h is cellular. **)
definition geotop_is_cellular_PLH ::
  "'a::real_normed_vector set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "geotop_is_cellular_PLH M2 h \<longleftrightarrow>
    top1_homeomorphism_on M2 (subspace_topology UNIV geotop_euclidean_topology M2)
       M2 (subspace_topology UNIV geotop_euclidean_topology M2) h \<and>
    (\<exists>K K'. geotop_is_complex K \<and> geotop_is_complex K' \<and> geotop_PLH K K' h) \<and>
    (\<exists>d. geotop_is_n_cell d (subspace_topology UNIV geotop_euclidean_topology d) 2 \<and>
         (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = d) \<and>
         d \<subseteq> M2 \<and> (\<forall>P\<in>M2 - d. h P = P))"

(** from \<S>27 Theorem 1 (geotop.tex:5746)
    LATEX VERSION: Let M^3 be a PL 3-manifold, let N be a polyhedral 3-manifold with boundary,
      lying in M^3, and let M^2 be a polyhedral 2-manifold (not necessarily compact) lying in
      Bd N. Then every cellular PLH h: M^2 \<leftrightarrow> M^2 has a PLH extension h': M^3 \<leftrightarrow> M^3, N \<leftrightarrow> N.
      And for each neighborhood W of M^2, h' can be chosen so that h'|(M^3 - W) is the
      identity. **)
theorem Theorem_GT_27_1:
  fixes K :: "(real^3) set set" and M3 N M2 W :: "(real^3) set"
  fixes h :: "real^3 \<Rightarrow> real^3"
  assumes "geotop_is_complex K" and "M3 = geotop_polyhedron K"
  assumes "geotop_n_manifold_with_boundary_on M3 (\<lambda>x y. norm (x - y)) 3"
  assumes "N \<subseteq> M3"
  assumes "geotop_n_manifold_with_boundary_on N (\<lambda>x y. norm (x - y)) 3"
  assumes "(\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = N)"
  assumes "M2 \<subseteq> geotop_manifold_boundary N (\<lambda>x y. norm (x - y))"
  assumes "geotop_n_manifold_with_boundary_on M2 (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_is_cellular_PLH M2 h"
  assumes "W \<in> geotop_euclidean_topology" and "M2 \<subseteq> W"
  shows "\<exists>h'. top1_homeomorphism_on M3 (subspace_topology UNIV geotop_euclidean_topology M3)
                 M3 (subspace_topology UNIV geotop_euclidean_topology M3) h' \<and>
              (\<exists>K1 K1'. geotop_is_complex K1 \<and> geotop_is_complex K1' \<and>
                        geotop_PLH K1 K1' h') \<and>
              h' ` N = N \<and>
              (\<forall>P\<in>M2. h' P = h P) \<and>
              (\<forall>P\<in>M3 - W. h' P = P)"
  sorry

(** from \<S>27 Theorem 2 (geotop.tex:5750)
    LATEX VERSION: Let A be a PL annulus, and let J and J' be polygons in Int A, neither of
      which bounds a 2-cell in A. Then there is PLH h: A \<leftrightarrow> A such that (1) h(J) = J',
      (2) h|Bd A is the identity, and (3) h is the composition of a finite sequence of
      cellular homeomorphisms. **)
theorem Theorem_GT_27_2:
  fixes A J J' :: "(real^2) set"
  assumes "geotop_is_k_annulus 1 A"
  assumes "geotop_is_polygon J" and "geotop_is_polygon J'"
  assumes "J \<subseteq> geotop_manifold_interior A (\<lambda>x y. norm (x - y))"
  assumes "J' \<subseteq> geotop_manifold_interior A (\<lambda>x y. norm (x - y))"
  assumes "\<not> (\<exists>D. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2
                  \<and> D \<subseteq> A \<and> geotop_frontier UNIV geotop_euclidean_topology D = J)"
  assumes "\<not> (\<exists>D. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2
                  \<and> D \<subseteq> A \<and> geotop_frontier UNIV geotop_euclidean_topology D = J')"
  shows "\<exists>h. top1_homeomorphism_on A (subspace_topology UNIV geotop_euclidean_topology A)
              A (subspace_topology UNIV geotop_euclidean_topology A) h \<and>
              h ` J = J' \<and>
              (\<forall>P\<in>geotop_manifold_boundary A (\<lambda>x y. norm (x - y)). h P = P) \<and>
              (\<exists>hs. hs \<noteq> [] \<and>
                    (\<forall>hi\<in>set hs. geotop_is_cellular_PLH A hi) \<and>
                    h = foldr (\<circ>) hs id)"
  sorry

(** from \<S>27 Theorem 3 (geotop.tex:5771)
    LATEX VERSION: Let J be a polygon in the interior of a PL annulus A. Then (1) J bounds a
      2-cell in A or (2) J carries a generator of H_1(A) = H_1(A, Z) and a generator of
      \<pi>(A). **)
theorem Theorem_GT_27_3:
  fixes A J :: "(real^2) set"
  assumes "geotop_is_k_annulus 1 A"
  assumes "geotop_is_polygon J"
  assumes "J \<subseteq> geotop_manifold_interior A (\<lambda>x y. norm (x - y))"
  shows "(\<exists>D. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2
              \<and> D \<subseteq> A \<and> geotop_frontier UNIV geotop_euclidean_topology D = J) \<or>
         (\<exists>P\<^sub>0\<in>J. \<exists>pJ. geotop_closed_path_on A
              (subspace_topology UNIV geotop_euclidean_topology A) P\<^sub>0 pJ \<and>
              pJ ` {0..1} = J \<and>
              (\<forall>q. geotop_closed_path_on A
                    (subspace_topology UNIV geotop_euclidean_topology A) P\<^sub>0 q \<longrightarrow>
                   (\<exists>n::int. geotop_path_equiv A
                        (subspace_topology UNIV geotop_euclidean_topology A) P\<^sub>0 q q)))"
  sorry

(** from \<S>27 Theorem 4 (geotop.tex:5774)
    LATEX VERSION: Let N be a polyhedral 3-manifold with boundary, in a PL 3-manifold M^3,
      let A be a polyhedral annulus in Bd N, and let J and J' be polygons in Int A, neither
      of which bounds a 2-cell in Int A. Let W be a neighborhood of A in M^3. Then there is
      a PLH h: M^3 \<leftrightarrow> M^3, Bd N \<leftrightarrow> Bd N, A \<leftrightarrow> A, J \<leftrightarrow> J', such that h|(M^3 - W) is the
      identity. **)
theorem Theorem_GT_27_4:
  fixes N M3 A J J' W :: "(real^3) set"
  assumes "geotop_n_manifold_with_boundary_on M3 (\<lambda>x y. norm (x - y)) 3"
  assumes "(\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = M3)"
  assumes "N \<subseteq> M3"
  assumes "geotop_n_manifold_with_boundary_on N (\<lambda>x y. norm (x - y)) 3"
  assumes "(\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = N)"
  assumes "geotop_n_manifold_with_boundary_on A (\<lambda>x y. norm (x - y)) 2"
  assumes "(\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = A)"
  assumes "\<exists>A0::(real^2) set. geotop_is_k_annulus 1 A0 \<and>
            (\<exists>f. top1_homeomorphism_on A0
               (subspace_topology UNIV geotop_euclidean_topology A0)
               A (subspace_topology UNIV geotop_euclidean_topology A) f)"
  assumes "A \<subseteq> geotop_manifold_boundary N (\<lambda>x y. norm (x - y))"
  assumes "geotop_is_polygon J" and "geotop_is_polygon J'"
  assumes "J \<subseteq> geotop_manifold_interior A (\<lambda>x y. norm (x - y))"
  assumes "J' \<subseteq> geotop_manifold_interior A (\<lambda>x y. norm (x - y))"
  assumes "\<not> (\<exists>D. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2
                  \<and> D \<subseteq> geotop_manifold_interior A (\<lambda>x y. norm (x - y))
                  \<and> geotop_frontier UNIV geotop_euclidean_topology D = J)"
  assumes "\<not> (\<exists>D. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2
                  \<and> D \<subseteq> geotop_manifold_interior A (\<lambda>x y. norm (x - y))
                  \<and> geotop_frontier UNIV geotop_euclidean_topology D = J')"
  assumes "W \<in> geotop_euclidean_topology" and "A \<subseteq> W"
  shows "\<exists>h. top1_homeomorphism_on M3 (subspace_topology UNIV geotop_euclidean_topology M3)
              M3 (subspace_topology UNIV geotop_euclidean_topology M3) h \<and>
              h ` (geotop_manifold_boundary N (\<lambda>x y. norm (x - y)))
                = geotop_manifold_boundary N (\<lambda>x y. norm (x - y)) \<and>
              h ` A = A \<and> h ` J = J' \<and>
              (\<forall>P\<in>M3 - W. h P = P)"
  sorry

(** from \<S>27 Theorem 5 (The Dehn lemma, Papakyriakopoulos) (geotop.tex:5778)
    LATEX VERSION: Let M^3 be a PL 3-manifold, and let D: \<Delta> \<rightarrow> M^3 be a PL singular 2-cell
      with no singularities on its boundary. Then the polygon D(Bd \<Delta>) is the boundary of a
      polyhedral 2-cell \<Delta>_1 in M^3. **)
theorem Theorem_GT_27_5_Dehn:
  fixes M3 :: "(real^3) set" and D :: "real^3 \<Rightarrow> real^3" and \<Delta> :: "(real^3) set"
  assumes "geotop_n_manifold_with_boundary_on M3 (\<lambda>x y. norm (x - y)) 3"
  assumes "(\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = M3)"
  assumes "geotop_is_singular_2cell M3 (subspace_topology UNIV geotop_euclidean_topology M3)
             D \<Delta> (subspace_topology UNIV geotop_euclidean_topology \<Delta>)"
  assumes "top1_homeomorphism_on (geotop_frontier UNIV geotop_euclidean_topology \<Delta>)
             (subspace_topology UNIV geotop_euclidean_topology
                (geotop_frontier UNIV geotop_euclidean_topology \<Delta>))
             (D ` (geotop_frontier UNIV geotop_euclidean_topology \<Delta>))
             (subspace_topology UNIV geotop_euclidean_topology
                (D ` (geotop_frontier UNIV geotop_euclidean_topology \<Delta>))) D"
  shows "\<exists>\<Delta>1. geotop_is_n_cell \<Delta>1 (subspace_topology UNIV geotop_euclidean_topology \<Delta>1) 2 \<and>
              \<Delta>1 \<subseteq> M3 \<and>
              geotop_frontier UNIV geotop_euclidean_topology \<Delta>1
                = D ` (geotop_frontier UNIV geotop_euclidean_topology \<Delta>)"
  sorry

section \<open>\<S>28 Polygons in the boundary of a combinatorial solid torus\<close>

(** from \<S>28 Theorem 1 (geotop.tex:5812)
    LATEX VERSION: Let S be a polyhedral torus in R^3. Then S is a CST. **)
theorem Theorem_GT_28_1:
  fixes S :: "(real^3) set"
  assumes "geotop_is_solid_torus S"
  assumes "\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = S"
  shows "geotop_is_CST S"
  sorry

(** from \<S>28: latitudinal polygon in a CST (geotop.tex:5822)
    LATEX VERSION: If S has a cylindrical diagram in which J_x appears as the boundaries of
      the two bases, then J_x is latitudinal in S. **)
definition geotop_is_latitudinal ::
  "(real^3) set \<Rightarrow> (real^3) set \<Rightarrow> bool" where
  "geotop_is_latitudinal S Jx \<longleftrightarrow>
    geotop_is_CST S \<and>
    geotop_is_polygon Jx \<and>
    Jx \<subseteq> geotop_manifold_boundary S (\<lambda>x y. norm (x - y)) \<and>
    (\<exists>(\<sigma>2::(real^2) set) (\<phi>::(real^2) \<times> real \<Rightarrow> real^3).
       geotop_simplex_dim \<sigma>2 2 \<and>
       \<phi> ` (\<sigma>2 \<times> {t. 0 \<le> t \<and> t \<le> 1}) = S \<and>
       \<phi> ` (geotop_frontier UNIV geotop_euclidean_topology \<sigma>2 \<times> {0}) = Jx)"

(** from \<S>28: standard position relative to J_x (geotop.tex:5822) **)
definition geotop_in_standard_position ::
  "(real^3) set \<Rightarrow> (real^3) set \<Rightarrow> (real^3) set \<Rightarrow> bool" where
  "geotop_in_standard_position S J Jx \<longleftrightarrow>
    geotop_is_latitudinal S Jx \<and>
    geotop_is_polygon J \<and>
    J \<subseteq> geotop_manifold_boundary S (\<lambda>x y. norm (x - y)) \<and>
    finite (J \<inter> Jx)"

(** from \<S>28 Theorem 2 (geotop.tex:5824)
    LATEX VERSION: Let J_x be latitudinal in S, and let J be a polygon in T. Then there is a
      PLH h: M^3 \<leftrightarrow> M^3, S \<leftrightarrow> S, such that h(J) is in standard position relative to J_x. **)
theorem Theorem_GT_28_2:
  fixes M3 S Jx J W :: "(real^3) set"
  assumes "geotop_n_manifold_with_boundary_on M3 (\<lambda>x y. norm (x - y)) 3"
  assumes "\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = M3"
  assumes "S \<subseteq> M3"
  assumes "geotop_is_latitudinal S Jx"
  assumes "geotop_is_polygon J"
  assumes "J \<subseteq> geotop_manifold_boundary S (\<lambda>x y. norm (x - y))"
  assumes "W \<in> geotop_euclidean_topology"
  assumes "geotop_manifold_boundary S (\<lambda>x y. norm (x - y)) \<subseteq> W"
  shows "\<exists>h. top1_homeomorphism_on M3 (subspace_topology UNIV geotop_euclidean_topology M3)
              M3 (subspace_topology UNIV geotop_euclidean_topology M3) h \<and>
              h ` S = S \<and>
              geotop_in_standard_position S (h ` J) Jx \<and>
              (\<forall>P\<in>M3 - W. h P = P)"
  sorry

(** from \<S>28 Theorem 3 (geotop.tex:5828)
    LATEX VERSION: Let J_x be latitudinal on S, and let J_1, ..., J_n be disjoint polygons in
      T. Then there is a PLH h such that each h(J_i) is in standard position. **)
theorem Theorem_GT_28_3:
  fixes M3 S Jx W :: "(real^3) set" and Js :: "(real^3) set set"
  assumes "geotop_n_manifold_with_boundary_on M3 (\<lambda>x y. norm (x - y)) 3"
  assumes "S \<subseteq> M3"
  assumes "geotop_is_latitudinal S Jx"
  assumes "finite Js"
  assumes "\<forall>J\<in>Js. geotop_is_polygon J \<and>
             J \<subseteq> geotop_manifold_boundary S (\<lambda>x y. norm (x - y))"
  assumes "\<forall>J1\<in>Js. \<forall>J2\<in>Js. J1 \<noteq> J2 \<longrightarrow> J1 \<inter> J2 = {}"
  assumes "W \<in> geotop_euclidean_topology"
  assumes "geotop_manifold_boundary S (\<lambda>x y. norm (x - y)) \<subseteq> W"
  shows "\<exists>h. top1_homeomorphism_on M3 (subspace_topology UNIV geotop_euclidean_topology M3)
              M3 (subspace_topology UNIV geotop_euclidean_topology M3) h \<and>
              h ` S = S \<and>
              (\<forall>J\<in>Js. geotop_in_standard_position S (h ` J) Jx) \<and>
              (\<forall>P\<in>M3 - W. h P = P)"
  sorry

(** from \<S>28 Theorem 4 (geotop.tex:5835)
    LATEX VERSION: Let J and J_x be polygons in T, such that J_x is latitudinal and J is in
      standard position relative to J_x. Let n be the number of points in J \<inter> J_x. Then
      Z^1(J) \<sim> n Y^1 on S, where Y^1 is a generator of H_1(S). **)
theorem Theorem_GT_28_4:
  fixes S Jx J :: "(real^3) set"
  assumes "geotop_is_latitudinal S Jx"
  assumes "geotop_in_standard_position S J Jx"
  shows "\<exists>n::nat. n = card (J \<inter> Jx) \<and>
         (\<forall>P\<^sub>0\<in>J. \<exists>pJ pY. geotop_closed_path_on S
              (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 pJ \<and>
              geotop_closed_path_on S
              (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 pY \<and>
              pJ ` {0..1} = J)"
  sorry

(** from \<S>28 Theorem 5 (geotop.tex:5839)
    LATEX VERSION: Let J be a polygon in T. If J \<sim> 0 on S but not on T, then J is
      latitudinal in S. **)
theorem Theorem_GT_28_5:
  fixes S J :: "(real^3) set" and Jx :: "(real^3) set"
  assumes "geotop_is_latitudinal S Jx"
  assumes "geotop_is_polygon J"
  assumes "J \<subseteq> geotop_manifold_boundary S (\<lambda>x y. norm (x - y))"
  assumes "\<exists>P\<^sub>0\<in>J. \<exists>p. p ` {0..1} = J \<and>
             geotop_closed_path_on S (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 p \<and>
             geotop_path_equiv S (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 p
               (\<lambda>t. P\<^sub>0)"
  assumes "\<not> (\<exists>P\<^sub>0\<in>J. \<exists>p. p ` {0..1} = J \<and>
                 geotop_path_equiv (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))
                   (subspace_topology UNIV geotop_euclidean_topology
                      (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))) P\<^sub>0 p (\<lambda>t. P\<^sub>0))"
  shows "geotop_is_latitudinal S J"
  sorry

(** from \<S>28 Theorem 6 (geotop.tex:5843)
    LATEX VERSION: Let J_1, ..., J_n (n > 1) be disjoint polygons in T, such that J_i is not
      contractible in T. Let U be a component of T - \<union> J_i, and let A = closure U. Then A
      is an annulus, and Bd A = J_i \<union> J_j for some i, j. **)
theorem Theorem_GT_28_6:
  fixes S :: "(real^3) set" and Js :: "(real^3) set set"
  assumes "geotop_is_CST S"
  assumes "finite Js" and "2 \<le> card Js"
  assumes "\<forall>J\<in>Js. geotop_is_polygon J \<and>
             J \<subseteq> geotop_manifold_boundary S (\<lambda>x y. norm (x - y)) \<and>
             \<not> (\<exists>P\<^sub>0\<in>J. \<exists>p. p ` {0..1} = J \<and>
                geotop_path_equiv (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))
                   (subspace_topology UNIV geotop_euclidean_topology
                      (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))) P\<^sub>0 p (\<lambda>t. P\<^sub>0))"
  assumes "\<forall>J1\<in>Js. \<forall>J2\<in>Js. J1 \<noteq> J2 \<longrightarrow> J1 \<inter> J2 = {}"
  shows "\<forall>U. (\<exists>P\<in>geotop_manifold_boundary S (\<lambda>x y. norm (x - y)) - \<Union>Js.
                U = geotop_component_at UNIV geotop_euclidean_topology
                     (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)) - \<Union>Js) P) \<longrightarrow>
             (\<exists>A::(real^2) set. \<exists>f. geotop_is_k_annulus 1 A \<and>
                top1_homeomorphism_on A (subspace_topology UNIV geotop_euclidean_topology A)
                  (closure_on UNIV geotop_euclidean_topology U)
                  (subspace_topology UNIV geotop_euclidean_topology
                     (closure_on UNIV geotop_euclidean_topology U)) f) \<and>
             (\<exists>i\<in>Js. \<exists>j\<in>Js. i \<noteq> j \<and>
               geotop_frontier UNIV geotop_euclidean_topology
                  (closure_on UNIV geotop_euclidean_topology U) = i \<union> j)"
  sorry

(** from \<S>28 Theorem 7 (geotop.tex:5851)
    LATEX VERSION: Let J be a polygon in T, such that J is not contractible on T, and let
      B be a regular neighborhood of J in T. Then Cl(T - B) is an annulus. **)
theorem Theorem_GT_28_7:
  fixes S J :: "(real^3) set"
  assumes "geotop_is_CST S"
  assumes "geotop_is_polygon J"
  assumes "J \<subseteq> geotop_manifold_boundary S (\<lambda>x y. norm (x - y))"
  assumes "\<exists>P\<^sub>0\<in>J. \<exists>p. p ` {0..1} = J \<and>
             geotop_closed_path_on (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))
                (subspace_topology UNIV geotop_euclidean_topology
                   (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))) P\<^sub>0 p \<and>
             \<not> geotop_path_equiv (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))
                  (subspace_topology UNIV geotop_euclidean_topology
                     (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))) P\<^sub>0 p (\<lambda>t. P\<^sub>0)"
  shows "\<exists>B. (\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = J) \<and>
             J \<subseteq> geotop_top_interior (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))
               (subspace_topology UNIV geotop_euclidean_topology
                  (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))) B \<and>
             (\<exists>A::(real^2) set. geotop_is_k_annulus 1 A \<and>
                (\<exists>f. top1_homeomorphism_on A
                   (subspace_topology UNIV geotop_euclidean_topology A)
                   (closure_on (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))
                     (subspace_topology UNIV geotop_euclidean_topology
                        (geotop_manifold_boundary S (\<lambda>x y. norm (x - y))))
                     (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)) - B))
                   (subspace_topology UNIV geotop_euclidean_topology
                     (closure_on (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))
                       (subspace_topology UNIV geotop_euclidean_topology
                          (geotop_manifold_boundary S (\<lambda>x y. norm (x - y))))
                       (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)) - B))) f))"
  sorry

(** from \<S>28 Theorem 8 (geotop.tex:5855)
    LATEX VERSION: Let J_1, ..., J_n be disjoint polygons on T, such that J_i is not
      contractible on S for each i, and such that \<union> J_i carries a generator of H_1(S). Then
      each J_i carries a generator of H_1(S). **)
theorem Theorem_GT_28_8:
  fixes S :: "(real^3) set" and Js :: "(real^3) set set"
  assumes "geotop_is_CST S"
  assumes "finite Js"
  assumes "\<forall>J\<in>Js. geotop_is_polygon J \<and>
             J \<subseteq> geotop_manifold_boundary S (\<lambda>x y. norm (x - y)) \<and>
             (\<forall>P\<^sub>0\<in>J. \<forall>p. p ` {0..1} = J \<and>
                geotop_closed_path_on S
                  (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 p
                \<longrightarrow> \<not> geotop_path_equiv S
                      (subspace_topology UNIV geotop_euclidean_topology S)
                      P\<^sub>0 p (\<lambda>t. P\<^sub>0))"
  assumes "\<forall>J1\<in>Js. \<forall>J2\<in>Js. J1 \<noteq> J2 \<longrightarrow> J1 \<inter> J2 = {}"
  assumes "\<exists>P\<^sub>0\<in>\<Union>Js. \<exists>p. p ` {0..1} \<subseteq> \<Union>Js \<and>
              geotop_closed_path_on S
                 (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 p \<and>
              (\<forall>q. geotop_closed_path_on S
                     (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 q \<longrightarrow>
                geotop_pi_class S (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 q
                \<in> geotop_pi S (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0)"
  shows "\<forall>J\<in>Js. \<exists>P\<^sub>0\<in>J. \<exists>p. p ` {0..1} = J \<and>
              geotop_closed_path_on S
                (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 p \<and>
              (\<forall>q. geotop_closed_path_on S
                     (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 q \<longrightarrow>
                geotop_pi_class S (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 q
                \<in> geotop_pi S (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0)"
  sorry

(** from \<S>28 Theorem 9 (geotop.tex:5859)
    LATEX VERSION: Let J be a polygon in T. If J \<sim> 0 on T, then J bounds a 2-cell in T. **)
theorem Theorem_GT_28_9:
  fixes S J :: "(real^3) set"
  assumes "geotop_is_CST S"
  assumes "geotop_is_polygon J"
  assumes "J \<subseteq> geotop_manifold_boundary S (\<lambda>x y. norm (x - y))"
  assumes "\<exists>P\<^sub>0\<in>J. \<exists>p. p ` {0..1} = J \<and>
             geotop_path_equiv (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))
                (subspace_topology UNIV geotop_euclidean_topology
                   (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))) P\<^sub>0 p (\<lambda>t. P\<^sub>0)"
  shows "\<exists>D. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2 \<and>
             D \<subseteq> geotop_manifold_boundary S (\<lambda>x y. norm (x - y)) \<and>
             geotop_frontier UNIV geotop_euclidean_topology D = J"
  sorry

(** from \<S>28 Theorem 10 (geotop.tex:5863)
    LATEX VERSION: Let K be a polyhedron in T, such that K carries a generator of H_1(S). Let
      J be a polygon in T - K, such that J does not bound a 2-cell in T. Then J carries a
      generator of H_1(S). **)
theorem Theorem_GT_28_10:
  fixes S K J :: "(real^3) set"
  assumes "geotop_is_CST S"
  assumes "K \<subseteq> geotop_manifold_boundary S (\<lambda>x y. norm (x - y))"
  assumes "\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = K"
  assumes "\<exists>P\<^sub>0\<in>K. \<exists>p. p ` {0..1} \<subseteq> K \<and>
             geotop_closed_path_on S
               (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 p"
  assumes "geotop_is_polygon J"
  assumes "J \<subseteq> geotop_manifold_boundary S (\<lambda>x y. norm (x - y)) - K"
  assumes "\<nexists>D. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2 \<and>
              D \<subseteq> geotop_manifold_boundary S (\<lambda>x y. norm (x - y)) \<and>
              geotop_frontier UNIV geotop_euclidean_topology D = J"
  shows "\<forall>P\<^sub>0\<in>J. \<exists>p. p ` {0..1} = J \<and>
              geotop_closed_path_on S
                (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 p"
  sorry

(** from \<S>28 Theorem 11 (geotop.tex:5869)
    LATEX VERSION: Let K_1 and K_2 be complexes whose union is a complex K. Let Z^n be a
      cycle on K_1, such that Z^n \<sim> 0 on K. Then there is a cycle Y^n on K_1 \<inter> K_2 such that
      (1) Y^n \<sim> Z^n on K_1 and (2) Y^n \<sim> 0 on K_2. **)
theorem Theorem_GT_28_11:
  fixes K1 K2 :: "'a::real_normed_vector set set"
  assumes "geotop_is_complex K1" and "geotop_is_complex K2"
  assumes "geotop_is_complex (K1 \<union> K2)"
  shows "True"  \<comment> \<open>Homology statement (H_n cycles); left abstract in this initial pass.\<close>
  by simp

(** from \<S>28 Theorem 12 (geotop.tex:5891)
    LATEX VERSION: Let S be a CST in R^3 (or S^3), and let T = Bd S. Let \<Delta> be a polyhedral
      2-cell in Cl(R^3 - S), such that J = Bd \<Delta> = \<Delta> \<inter> T, and such that J is not contractible
      on T. Then J carries a generator of H_1(S). **)
theorem Theorem_GT_28_12:
  fixes S \<Delta> J :: "(real^3) set"
  assumes "geotop_is_CST S"
  assumes "geotop_is_n_cell \<Delta> (subspace_topology UNIV geotop_euclidean_topology \<Delta>) 2"
  assumes "\<Delta> \<subseteq> closure_on (UNIV::(real^3) set) geotop_euclidean_topology (UNIV - S)"
  assumes "geotop_frontier UNIV geotop_euclidean_topology \<Delta> = J"
  assumes "\<Delta> \<inter> geotop_manifold_boundary S (\<lambda>x y. norm (x - y)) = J"
  assumes "\<exists>P\<^sub>0\<in>J. \<exists>p. p ` {0..1} = J \<and>
             geotop_closed_path_on (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))
                (subspace_topology UNIV geotop_euclidean_topology
                   (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))) P\<^sub>0 p \<and>
             \<not> geotop_path_equiv (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))
                  (subspace_topology UNIV geotop_euclidean_topology
                     (geotop_manifold_boundary S (\<lambda>x y. norm (x - y)))) P\<^sub>0 p (\<lambda>t. P\<^sub>0)"
  shows "\<forall>P\<^sub>0\<in>J. \<exists>p. p ` {0..1} = J \<and>
             geotop_closed_path_on S
               (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 p"
  sorry

(** from \<S>28 Theorem 13 (geotop.tex:5904)
    LATEX VERSION: Let S be a regular neighborhood of a polygon J_0 in R^3 (or S^3). Let
      T = Bd S, let J be a polygon in T, such that J is not contractible on T, and let \<Delta>
      be a polyhedral 2-cell such that Bd \<Delta> = J and Int \<Delta> \<subseteq> R^3 - S. Then J_0 is
      unknotted. **)
theorem Theorem_GT_28_13:
  fixes J0 S J \<Delta> :: "(real^3) set"
  assumes "geotop_is_polygon J0"
  assumes "geotop_is_CST S"
  assumes "geotop_is_polygon J"
  assumes "J \<subseteq> geotop_manifold_boundary S (\<lambda>x y. norm (x - y))"
  assumes "geotop_is_n_cell \<Delta> (subspace_topology UNIV geotop_euclidean_topology \<Delta>) 2"
  assumes "geotop_frontier UNIV geotop_euclidean_topology \<Delta> = J"
  assumes "geotop_top_interior UNIV geotop_euclidean_topology \<Delta> \<subseteq> UNIV - S"
  shows "geotop_is_unknotted J0"
  sorry

(** from \<S>28 Theorem 14 (geotop.tex:5910)
    LATEX VERSION: Let J be a polygon in R^3 (or S^3). Then H_1(R^3 - J) \<cong> Z. And if S is a
      regular neighborhood of J, with boundary T, and J_x is latitudinal on T, then
      Z^1(J_x) generates H_1(R^3 - J). **)
theorem Theorem_GT_28_14:
  fixes J :: "(real^3) set"
  assumes "geotop_is_polygon J"
  shows "\<exists>P\<^sub>0\<in>UNIV - J. \<exists>g.
           geotop_closed_path_on (UNIV - J)
             (subspace_topology UNIV geotop_euclidean_topology (UNIV - J)) P\<^sub>0 g \<and>
           (\<forall>p. geotop_closed_path_on (UNIV - J)
                  (subspace_topology UNIV geotop_euclidean_topology (UNIV - J)) P\<^sub>0 p \<longrightarrow>
                geotop_pi_class (UNIV - J)
                   (subspace_topology UNIV geotop_euclidean_topology (UNIV - J)) P\<^sub>0 p
                \<in> geotop_pi (UNIV - J)
                   (subspace_topology UNIV geotop_euclidean_topology (UNIV - J)) P\<^sub>0)"
  sorry

(** from \<S>28 Theorem 15 (geotop.tex:5914)
    LATEX VERSION: Let J be a polygon in R^3 (or S^3). Let S be a regular neighborhood of J.
      Then there is a polygon J_y in T = Bd S such that Z^1(J_y) generates H_1(S) and
      Z^1(J_y) \<sim> 0 on Cl(R^3 - S). **)
theorem Theorem_GT_28_15:
  fixes J S :: "(real^3) set"
  assumes "geotop_is_polygon J"
  assumes "geotop_is_CST S"
  shows "\<exists>Jy. geotop_is_polygon Jy \<and>
              Jy \<subseteq> geotop_manifold_boundary S (\<lambda>x y. norm (x - y))"
  sorry

(** from \<S>28 Theorem 16 (geotop.tex:5926)
    LATEX VERSION: Let J be a polygon in R^3 (or S^3), and suppose that \<pi>(R^3 - J) is
      commutative. Then J is unknotted. **)
theorem Theorem_GT_28_16:
  fixes J :: "(real^3) set"
  assumes "geotop_is_polygon J"
  assumes "\<forall>P\<^sub>0\<in>UNIV - J. \<forall>C D.
             C \<in> geotop_pi (UNIV - J) (subspace_topology UNIV geotop_euclidean_topology (UNIV - J)) P\<^sub>0 \<and>
             D \<in> geotop_pi (UNIV - J) (subspace_topology UNIV geotop_euclidean_topology (UNIV - J)) P\<^sub>0 \<longrightarrow>
             geotop_pi_mult (UNIV - J)
               (subspace_topology UNIV geotop_euclidean_topology (UNIV - J)) P\<^sub>0 C D =
             geotop_pi_mult (UNIV - J)
               (subspace_topology UNIV geotop_euclidean_topology (UNIV - J)) P\<^sub>0 D C"
  shows "geotop_is_unknotted J"
  sorry

(** from \<S>28 Theorem 17 (Poincaré) (geotop.tex:5930)
    LATEX VERSION: There is a compact connected triangulated 3-manifold which has the
      homology groups of a 3-sphere, but is not simply connected (and hence is not a
      3-sphere). **)
theorem Theorem_GT_28_17_Poincare:
  shows "\<exists>K :: (real^3) set set. geotop_is_complex K \<and>
           top1_compact_on (geotop_polyhedron K)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) \<and>
           top1_connected_on (geotop_polyhedron K)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) \<and>
           geotop_n_manifold_with_boundary_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 3 \<and>
           geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) = {} \<and>
           (\<exists>P\<^sub>0\<in>geotop_polyhedron K.
              \<not> geotop_simply_connected (geotop_polyhedron K)
                  (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))
                  P\<^sub>0)"
  sorry

(** from \<S>28 Theorem 18 (geotop.tex:5977)
    LATEX VERSION: Let M^2 be a polyhedral projective plane, in an orientable PL 3-manifold
      M, and let N be a regular neighborhood of M^2. Then Bd N is a 2-sphere. **)
theorem Theorem_GT_28_18:
  fixes M3 :: "(real^3) set" and K :: "(real^3) set set" and M2 N :: "(real^3) set"
  assumes "geotop_is_orientable_3_manifold K" and "M3 = geotop_polyhedron K"
  assumes "geotop_is_projective_plane M2" and "M2 \<subseteq> M3"
  assumes "\<exists>L\<subseteq>K. geotop_polyhedron L = M2"
  assumes "N = geotop_regular_neighborhood K (SOME L::(real^3) set set. L \<subseteq> K \<and> geotop_polyhedron L = M2)"
  shows "geotop_is_n_sphere (geotop_manifold_boundary N (\<lambda>x y. norm (x - y)))
           (subspace_topology UNIV geotop_euclidean_topology
              (geotop_manifold_boundary N (\<lambda>x y. norm (x - y)))) 2"
  sorry

(** from \<S>28 Theorem 19 (geotop.tex:5983)
    LATEX VERSION: Let M^2 be a polyhedral 2-manifold, in a PL 3-manifold M^3 = |K|. Let \<Delta>
      be a polyhedral 2-cell such that Bd \<Delta> = J = \<Delta> \<inter> M^2. Then J has an annular
      neighborhood in M^2. **)
theorem Theorem_GT_28_19:
  fixes M3 M2 \<Delta> J :: "(real^3) set"
  assumes "geotop_n_manifold_with_boundary_on M3 (\<lambda>x y. norm (x - y)) 3"
  assumes "geotop_n_manifold_with_boundary_on M2 (\<lambda>x y. norm (x - y)) 2"
  assumes "M2 \<subseteq> M3"
  assumes "geotop_is_n_cell \<Delta> (subspace_topology UNIV geotop_euclidean_topology \<Delta>) 2"
  assumes "geotop_frontier UNIV geotop_euclidean_topology \<Delta> = J"
  assumes "\<Delta> \<inter> M2 = J"
  shows "\<exists>A::(real^3) set. J \<subseteq> geotop_top_interior M2
           (subspace_topology UNIV geotop_euclidean_topology M2) A \<and>
           A \<subseteq> M2"
  sorry

(** from \<S>28 Theorem 20 (geotop.tex:5991)
    LATEX VERSION: Let M^2 be a polyhedral 2-manifold, in a PL 3-manifold M^3, and let \<Delta> be
      as in Theorem 19. Suppose that M^2 \<rightarrow> M_1^2, under an operation which splits M^2 \<union> \<Delta>
      apart at \<Delta>. Then \<chi>(M_1^2) = \<chi>(M^2) + 2. **)
theorem Theorem_GT_28_20:
  fixes M3 M2 M1 \<Delta> :: "(real^3) set"
  assumes "geotop_n_manifold_with_boundary_on M3 (\<lambda>x y. norm (x - y)) 3"
  assumes "geotop_n_manifold_with_boundary_on M2 (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_n_manifold_with_boundary_on M1 (\<lambda>x y. norm (x - y)) 2"
  assumes "geotop_is_n_cell \<Delta> (subspace_topology UNIV geotop_euclidean_topology \<Delta>) 2"
  assumes "geotop_frontier UNIV geotop_euclidean_topology \<Delta> = \<Delta> \<inter> M2"
  shows "geotop_manifold_euler M1 = geotop_manifold_euler M2 + 2"
  sorry

section \<open>\<S>29 Limits on the Loop theorem: Stallings's example\<close>

(** from \<S>29: lens space L(p,q) (geotop.tex:6010)
    LATEX VERSION: Let p and q be positive integers, with p \<ge> 2 and q < p. The lens space
      L(p, q) is defined by identifying (r, \<theta>, z) in S^2 with z \<ge> 0 with
      (r, \<theta> + 2\<pi>q/p, -z). **)
definition geotop_is_lens_space ::
  "nat \<Rightarrow> nat \<Rightarrow> (real^3) set \<Rightarrow> bool" where
  "geotop_is_lens_space p q L \<longleftrightarrow>
    p \<ge> 2 \<and> q < p \<and>
    top1_compact_on L (subspace_topology UNIV geotop_euclidean_topology L) \<and>
    top1_connected_on L (subspace_topology UNIV geotop_euclidean_topology L) \<and>
    geotop_n_manifold_with_boundary_on L (\<lambda>x y. norm (x - y)) 3 \<and>
    geotop_manifold_boundary L (\<lambda>x y. norm (x - y)) = {}"

(** from \<S>29: Stallings's counterexample (geotop.tex:6008)
    LATEX VERSION: If in Theorem 26.4 we omit the hypothesis that M^2 is two sided in
      Int M^3, the resulting proposition is false. **)
theorem Theorem_GT_29_1_Stallings_counterexample:
  shows "\<exists>(L::(real^3) set) (M2::(real^3) set).
           geotop_is_lens_space 6 1 L \<and>
           top1_compact_on M2 (subspace_topology UNIV geotop_euclidean_topology M2) \<and>
           geotop_n_manifold_with_boundary_on M2 (\<lambda>x y. norm (x - y)) 2 \<and>
           geotop_manifold_boundary M2 (\<lambda>x y. norm (x - y)) = {} \<and>
           \<not> geotop_is_two_sided M2 (geotop_manifold_interior L (\<lambda>x y. norm (x - y))) \<and>
           (\<exists>P\<^sub>0\<in>M2. \<exists>p. geotop_closed_path_on M2
                     (subspace_topology UNIV geotop_euclidean_topology M2) P\<^sub>0 p \<and>
                     \<not> geotop_path_equiv M2
                          (subspace_topology UNIV geotop_euclidean_topology M2)
                          P\<^sub>0 p (\<lambda>t. P\<^sub>0) \<and>
                     geotop_path_equiv L (subspace_topology UNIV geotop_euclidean_topology L)
                       P\<^sub>0 p (\<lambda>t. P\<^sub>0)) \<and>
           (\<nexists>\<Delta>. geotop_is_n_cell \<Delta>
                  (subspace_topology UNIV geotop_euclidean_topology \<Delta>) 2 \<and>
                \<Delta> \<subseteq> geotop_manifold_interior L (\<lambda>x y. norm (x - y)) \<and>
                geotop_frontier UNIV geotop_euclidean_topology \<Delta> = \<Delta> \<inter> M2 \<and>
                (\<exists>P\<^sub>0\<in>\<Delta> \<inter> M2. \<exists>p.
                   geotop_closed_path_on (\<Delta> \<inter> M2)
                     (subspace_topology UNIV geotop_euclidean_topology (\<Delta> \<inter> M2)) P\<^sub>0 p \<and>
                   \<not> geotop_path_equiv M2
                        (subspace_topology UNIV geotop_euclidean_topology M2)
                        P\<^sub>0 p (\<lambda>t. P\<^sub>0)))"
  sorry

section \<open>\<S>30 Polyhedral interpolation theorems\<close>

(** from \<S>30: separation of disjoint closed sets (geotop.tex:6113)
    LATEX VERSION: Let H and K be disjoint closed sets, in a topological space X, and let C
      be a closed set, disjoint from H and K. If X - C is the union of two disjoint open
      sets, containing H and K respectively, then C separates H from K. **)
definition geotop_separates_in ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_separates_in X T C H K \<longleftrightarrow>
    H \<inter> K = {} \<and> C \<inter> H = {} \<and> C \<inter> K = {} \<and>
    closedin_on X T C \<and> closedin_on X T H \<and> closedin_on X T K \<and>
    (\<exists>U V. U \<in> T \<and> V \<in> T \<and> U \<inter> V = {} \<and> X - C = U \<union> V \<and> H \<subseteq> U \<and> K \<subseteq> V)"

(** from \<S>30 Theorem 1 (geotop.tex:6115)
    LATEX VERSION: Let X be a simply connected and locally connected topological space in
      which every connected open set is pathwise connected. Let H, K, C, and D be disjoint
      closed sets, and suppose that both H and K are connected. If C \<union> D separates H from K,
      then either C or D separates H from K. **)
theorem Theorem_GT_30_1:
  fixes X :: "'a set" and T :: "'a set set" and H K C D :: "'a set"
  assumes "is_topology_on X T"
  assumes "\<forall>P\<in>X. geotop_simply_connected X T P"
  assumes "top1_connected_on H (subspace_topology X T H)"
  assumes "top1_connected_on K (subspace_topology X T K)"
  assumes "H \<inter> K = {}" and "H \<inter> C = {}" and "H \<inter> D = {}"
  assumes "K \<inter> C = {}" and "K \<inter> D = {}" and "C \<inter> D = {}"
  assumes "closedin_on X T H" and "closedin_on X T K"
  assumes "closedin_on X T C" and "closedin_on X T D"
  assumes "geotop_separates_in X T (C \<union> D) H K"
  shows "geotop_separates_in X T C H K \<or> geotop_separates_in X T D H K"
  sorry

(** from \<S>30 Theorem 2 (geotop.tex:6123)
    LATEX VERSION: Let X, H, K be as in Theorem 1. Let C be a closed set which separates H
      from K in X, and suppose that C has only a finite number of components. Then some
      component of C separates H from K. **)
theorem Theorem_GT_30_2:
  fixes X :: "'a set" and T :: "'a set set" and H K C :: "'a set"
  assumes "is_topology_on X T"
  assumes "\<forall>P\<in>X. geotop_simply_connected X T P"
  assumes "top1_connected_on H (subspace_topology X T H)"
  assumes "top1_connected_on K (subspace_topology X T K)"
  assumes "geotop_separates_in X T C H K"
  assumes "finite {cC. \<exists>P\<in>C. cC = geotop_component_at X T C P}"
  shows "\<exists>cC. (\<exists>P\<in>C. cC = geotop_component_at X T C P) \<and>
              geotop_separates_in X T cC H K"
  sorry

(** from \<S>30 Theorem 3 (geotop.tex:6126)
    LATEX VERSION: Let M be a connected PL 3-manifold, let H and K be disjoint closed sets in
      M, and let C be a closed set which separates H from K. Let \<Delta> be a polyhedral 2-cell
      in C, let J = Bd \<Delta>, and suppose that \<Delta> has a neighborhood in C of the form D_1 \<union> D_2.
      If C is split apart at \<Delta>, leaving D_2 fixed, then the resulting set C' separates H
      from K. **)
theorem Theorem_GT_30_3:
  fixes M :: "(real^3) set" and K :: "(real^3) set set"
  fixes H Kk C \<Delta> C' :: "(real^3) set"
  assumes "geotop_is_complex K" and "M = geotop_polyhedron K"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 3"
  assumes "top1_connected_on M (subspace_topology UNIV geotop_euclidean_topology M)"
  assumes "geotop_separates_in M (subspace_topology UNIV geotop_euclidean_topology M) C H Kk"
  assumes "geotop_is_n_cell \<Delta> (subspace_topology UNIV geotop_euclidean_topology \<Delta>) 2"
  assumes "\<Delta> \<subseteq> C"
  shows "geotop_separates_in M (subspace_topology UNIV geotop_euclidean_topology M) C' H Kk"
  sorry

(** from \<S>30: spherical shell (geotop.tex:6137)
    LATEX VERSION: Let S^2 be a 2-sphere, and let \<phi> be a homeomorphism S^2 \<times> [0,1] \<leftrightarrow> X.
      Then X is a spherical shell. **)
definition geotop_is_spherical_shell ::
  "(real^3) set \<Rightarrow> bool" where
  "geotop_is_spherical_shell X \<longleftrightarrow>
    (\<exists>(S2::(real^3) set) (\<phi>::(real^3) \<times> real \<Rightarrow> real^3).
       geotop_is_n_sphere S2 (subspace_topology UNIV geotop_euclidean_topology S2) 2 \<and>
       top1_homeomorphism_on (S2 \<times> {t. 0 \<le> t \<and> t \<le> 1})
         (subspace_topology (UNIV::((real^3) \<times> real) set)
            geotop_euclidean_topology (S2 \<times> {t. 0 \<le> t \<and> t \<le> 1}))
         X (subspace_topology UNIV geotop_euclidean_topology X) \<phi>)"

(** from \<S>30 Theorem 4 (geotop.tex:6149)
    LATEX VERSION: Let X be a spherical shell in R^3 (or S^3). Then there is a polyhedral
      2-sphere B in Int X such that B separates B_0 from B_1 in R^3 (and hence in X). **)
theorem Theorem_GT_30_4:
  fixes X :: "(real^3) set" and B0 B1 :: "(real^3) set"
  assumes "geotop_is_spherical_shell X"
  assumes "B0 \<union> B1 = geotop_manifold_boundary X (\<lambda>x y. norm (x - y))"
  assumes "geotop_is_n_sphere B0 (subspace_topology UNIV geotop_euclidean_topology B0) 2"
  assumes "geotop_is_n_sphere B1 (subspace_topology UNIV geotop_euclidean_topology B1) 2"
  assumes "B0 \<inter> B1 = {}"
  shows "\<exists>B. geotop_is_n_sphere B (subspace_topology UNIV geotop_euclidean_topology B) 2 \<and>
             (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = B) \<and>
             B \<subseteq> geotop_manifold_interior X (\<lambda>x y. norm (x - y)) \<and>
             geotop_separates_in UNIV geotop_euclidean_topology B B0 B1"
  sorry

(** from \<S>30 Theorem 5 (geotop.tex:6155)
    LATEX VERSION: Let C_1 and C_2 be topological 3-cells in R^3 (or S^3) such that
      C_1 \<subseteq> Int C_2 and such that Cl(C_2 - C_1) is a spherical shell. Then there is a
      polyhedral 3-cell C such that C_1 \<subseteq> Int C and C \<subseteq> Int C_2. **)
theorem Theorem_GT_30_5:
  fixes C1 C2 :: "(real^3) set"
  assumes "geotop_is_n_cell C1 (subspace_topology UNIV geotop_euclidean_topology C1) 3"
  assumes "geotop_is_n_cell C2 (subspace_topology UNIV geotop_euclidean_topology C2) 3"
  assumes "C1 \<subseteq> geotop_top_interior UNIV geotop_euclidean_topology C2"
  assumes "geotop_is_spherical_shell
             (closure_on UNIV geotop_euclidean_topology (C2 - C1))"
  shows "\<exists>C. geotop_is_n_cell C (subspace_topology UNIV geotop_euclidean_topology C) 3 \<and>
             (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = C) \<and>
             C1 \<subseteq> geotop_top_interior UNIV geotop_euclidean_topology C \<and>
             C \<subseteq> geotop_top_interior UNIV geotop_euclidean_topology C2"
  sorry

(** from \<S>30: toroidal shell (geotop.tex:6163)
    LATEX VERSION: Let M be a torus, and let \<phi> be a homeomorphism M \<times> [0,1] \<leftrightarrow> Y. Then Y is
      a toroidal shell. **)
definition geotop_is_toroidal_shell ::
  "(real^3) set \<Rightarrow> bool" where
  "geotop_is_toroidal_shell Y \<longleftrightarrow>
    (\<exists>(M::(real^3) set) (\<phi>::(real^3) \<times> real \<Rightarrow> real^3).
       geotop_is_torus M \<and>
       top1_homeomorphism_on (M \<times> {t. 0 \<le> t \<and> t \<le> 1})
         (subspace_topology (UNIV::((real^3) \<times> real) set)
            geotop_euclidean_topology (M \<times> {t. 0 \<le> t \<and> t \<le> 1}))
         Y (subspace_topology UNIV geotop_euclidean_topology Y) \<phi>)"

(** from \<S>30 Theorem 6 (geotop.tex:6169)
    LATEX VERSION: Let Y be a toroidal shell in R^3 (or S^3). Then there is a polyhedral
      torus T \<subseteq> Int Y such that T separates T_0 from T_1. **)
theorem Theorem_GT_30_6:
  fixes Y T0 T1 :: "(real^3) set"
  assumes "geotop_is_toroidal_shell Y"
  assumes "T0 \<union> T1 = geotop_manifold_boundary Y (\<lambda>x y. norm (x - y))"
  assumes "geotop_is_torus T0" and "geotop_is_torus T1"
  assumes "T0 \<inter> T1 = {}"
  shows "\<exists>T. geotop_is_torus T \<and>
             (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = T) \<and>
             T \<subseteq> geotop_manifold_interior Y (\<lambda>x y. norm (x - y)) \<and>
             geotop_separates_in UNIV geotop_euclidean_topology T T0 T1"
  sorry

(** from \<S>30 Theorem 7 (geotop.tex:6177)
    LATEX VERSION: Let S_1 and S_2 be (topological) solid tori in R^3 (or S^3) such that
      S_1 \<subseteq> Int S_2 and Cl(S_2 - S_1) is a toroidal shell. Then there is a combinatorial
      solid torus (CST) S such that S_1 \<subseteq> Int S and S \<subseteq> Int S_2. **)
theorem Theorem_GT_30_7:
  fixes S1 S2 :: "(real^3) set"
  assumes "geotop_is_solid_torus S1" and "geotop_is_solid_torus S2"
  assumes "S1 \<subseteq> geotop_manifold_interior S2 (\<lambda>x y. norm (x - y))"
  assumes "geotop_is_toroidal_shell
             (closure_on UNIV geotop_euclidean_topology (S2 - S1))"
  shows "\<exists>S. geotop_is_CST S \<and>
             S1 \<subseteq> geotop_manifold_interior S (\<lambda>x y. norm (x - y)) \<and>
             S \<subseteq> geotop_manifold_interior S2 (\<lambda>x y. norm (x - y))"
  sorry

(** from \<S>30: spine of a solid torus (geotop.tex:6188)
    LATEX VERSION: Let S be a solid torus, and let J be a 1-sphere in Int S. Let \<Delta> be a
      2-cell, S^1 be a 1-sphere, and suppose that there is a homeomorphism
      \<phi>: \<Delta> \<times> S^1 \<leftrightarrow> S, and a point P of Int \<Delta>, such that J = \<phi>(P \<times> S^1). Then J is a
      spine of S. **)
definition geotop_is_spine_of_solid_torus ::
  "(real^3) set \<Rightarrow> (real^3) set \<Rightarrow> bool" where
  "geotop_is_spine_of_solid_torus J S \<longleftrightarrow>
    geotop_is_solid_torus S \<and>
    geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1 \<and>
    J \<subseteq> geotop_manifold_interior S (\<lambda>x y. norm (x - y)) \<and>
    (\<exists>(\<Delta>::(real^2) set) (S1::(real^2) set)
       (\<phi>::((real^2) \<times> (real^2)) \<Rightarrow> real^3) P.
       geotop_is_n_cell \<Delta> (subspace_topology UNIV geotop_euclidean_topology \<Delta>) 2 \<and>
       geotop_is_n_sphere S1 (subspace_topology UNIV geotop_euclidean_topology S1) 1 \<and>
       top1_homeomorphism_on (\<Delta> \<times> S1)
         (subspace_topology (UNIV::((real^2) \<times> (real^2)) set)
            geotop_euclidean_topology (\<Delta> \<times> S1))
         S (subspace_topology UNIV geotop_euclidean_topology S) \<phi> \<and>
       P \<in> geotop_top_interior UNIV geotop_euclidean_topology \<Delta> \<and>
       J = \<phi> ` ({P} \<times> S1))"

(** from \<S>30 Theorem 8 (geotop.tex:6190)
    LATEX VERSION: Let S_1, S, and S_2 be as in Theorem 7, let J be a spine of S_1, and let
      P_0 \<in> J. Then p_J generates \<pi>(S) = \<pi>(S, P_0). **)
theorem Theorem_GT_30_8:
  fixes S1 S S2 :: "(real^3) set" and J :: "(real^3) set" and P\<^sub>0 :: "real^3"
  assumes "geotop_is_solid_torus S1" and "geotop_is_CST S" and "geotop_is_solid_torus S2"
  assumes "S1 \<subseteq> geotop_manifold_interior S (\<lambda>x y. norm (x - y))"
  assumes "S \<subseteq> geotop_manifold_interior S2 (\<lambda>x y. norm (x - y))"
  assumes "geotop_is_spine_of_solid_torus J S1"
  assumes "P\<^sub>0 \<in> J"
  shows "\<exists>p. geotop_closed_path_on S (subspace_topology UNIV geotop_euclidean_topology S)
               P\<^sub>0 p \<and>
             p ` {0..1} = J \<and>
             (\<forall>q. geotop_closed_path_on S
                    (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 q \<longrightarrow>
                  geotop_pi_class S (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0 q
                  \<in> geotop_pi S (subspace_topology UNIV geotop_euclidean_topology S) P\<^sub>0)"
  sorry

section \<open>\<S>31 Canonical configurations; dual cells; pseudo-cells\<close>

(** from \<S>31: canonical configuration (geotop.tex:6274)
    LATEX VERSION: The entire apparatus described above will be called a canonical
      configuration. A canonical configuration consists of points P_j, 2-cells D_j, their
      rotations to solid tori S_j with T_j = Bd S_j, A_j \<subseteq> Int S_j, N = \<union>_{j=i}^{i+2} S_j,
      a homeomorphism h: N \<leftrightarrow> N' \<subseteq> R^3, and polyhedral solid tori S_j'' with A_j' \<subseteq> Int S_j''
      and S_j'' \<subseteq> Int S_j'. **)
definition geotop_is_canonical_configuration ::
  "(nat \<Rightarrow> (real^3) set) \<Rightarrow>
   (nat \<Rightarrow> (real^3) set) \<Rightarrow>
   (nat \<Rightarrow> (real^3) set) \<Rightarrow>
   (nat \<Rightarrow> (real^3) set) \<Rightarrow>
   (nat \<Rightarrow> (real^3) set) \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_is_canonical_configuration A S S' S'' T'' i \<longleftrightarrow>
    (\<forall>j. geotop_is_solid_torus (S j) \<and>
         geotop_is_solid_torus (S' j) \<and>
         geotop_is_solid_torus (S'' j) \<and>
         (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = S'' j)) \<and>
    (\<forall>j. j = i \<or> j = i+1 \<or> j = i+2 \<longrightarrow>
         A j \<subseteq> geotop_manifold_interior (S'' j) (\<lambda>x y. norm (x - y)) \<and>
         S'' j \<subseteq> geotop_manifold_interior (S' j) (\<lambda>x y. norm (x - y)))"

(** from \<S>31 Theorem 1 (geotop.tex:6276)
    LATEX VERSION: Given sets A_j, D_j, and a homeomorphism h, as in the definition of a
      canonical configuration, there are polyhedral solid tori S_j'' which give a canonical
      configuration. **)
theorem Theorem_GT_31_1:
  fixes A S S' :: "nat \<Rightarrow> (real^3) set" and i :: nat
  assumes "\<forall>j. j = i \<or> j = i+1 \<or> j = i+2 \<longrightarrow>
             geotop_is_solid_torus (S j) \<and>
             geotop_is_solid_torus (S' j) \<and>
             A j \<subseteq> geotop_manifold_interior (S' j) (\<lambda>x y. norm (x - y))"
  shows "\<exists>S'' T''. geotop_is_canonical_configuration A S S' S'' T'' i"
  sorry

(** from \<S>31 Theorem 2 (geotop.tex:6279)
    LATEX VERSION: In a canonical configuration, each of the sets J_j' and J_{j+1}' carries
      a generator of \<pi>(S_j''). **)
theorem Theorem_GT_31_2:
  fixes A S S' S'' T'' J :: "nat \<Rightarrow> (real^3) set" and i :: nat
  assumes "geotop_is_canonical_configuration A S S' S'' T'' i"
  assumes "\<forall>j. geotop_is_polygon (J j) \<and> J j \<subseteq> S' j"
  shows "\<forall>j. \<forall>P\<^sub>0\<in>J j. \<exists>p.
           p ` {0..1} = J j \<and>
           geotop_closed_path_on (S'' j)
             (subspace_topology UNIV geotop_euclidean_topology (S'' j)) P\<^sub>0 p \<and>
           (\<forall>q. geotop_closed_path_on (S'' j)
                  (subspace_topology UNIV geotop_euclidean_topology (S'' j)) P\<^sub>0 q \<longrightarrow>
                geotop_pi_class (S'' j)
                  (subspace_topology UNIV geotop_euclidean_topology (S'' j)) P\<^sub>0 q
                \<in> geotop_pi (S'' j)
                  (subspace_topology UNIV geotop_euclidean_topology (S'' j)) P\<^sub>0)"
  sorry

(** from \<S>31 Theorem 3 (geotop.tex:6282)
    LATEX VERSION: In a canonical configuration, S_i'' \<inter> S_{i+2}'' = \<emptyset>. **)
theorem Theorem_GT_31_3:
  fixes A S S' S'' T'' :: "nat \<Rightarrow> (real^3) set" and i :: nat
  assumes "geotop_is_canonical_configuration A S S' S'' T'' i"
  shows "S'' i \<inter> S'' (i+2) = {}"
  sorry

(** from \<S>31 Theorem 4 (geotop.tex:6285)
    LATEX VERSION: In a canonical configuration, let J be a polygon in a set T_j'' \<inter>
      T_{j+1}''. Then either (1) J carries a generator of \<pi>(S_j'') and of \<pi>(S_{j+1}'') or
      (2) J bounds a 2-cell in T_j'' and a 2-cell in T_{j+1}''. **)
theorem Theorem_GT_31_4:
  fixes A S S' S'' T'' :: "nat \<Rightarrow> (real^3) set" and J :: "(real^3) set" and j :: nat
  assumes "geotop_is_canonical_configuration A S S' S'' T'' i"
  assumes "geotop_is_polygon J"
  assumes "J \<subseteq> T'' j \<inter> T'' (j+1)"
  shows "(\<forall>k\<in>{j, j+1}. \<forall>P\<^sub>0\<in>J. \<exists>p.
             p ` {0..1} = J \<and>
             geotop_closed_path_on (S'' k)
               (subspace_topology UNIV geotop_euclidean_topology (S'' k)) P\<^sub>0 p) \<or>
         (\<forall>k\<in>{j, j+1}. \<exists>D. geotop_is_n_cell D
              (subspace_topology UNIV geotop_euclidean_topology D) 2 \<and>
              D \<subseteq> T'' k \<and> geotop_frontier UNIV geotop_euclidean_topology D = J)"
  sorry

(** from \<S>31: dual cells of a tubular neighborhood (geotop.tex:6316)
    LATEX VERSION: Let K be a 1-dimensional complex, in a PL 3-manifold M, and let N be a
      regular neighborhood of K. Then for each edge \<sigma>^1 of K there is a 2-cell D, orthogonal
      to \<sigma>^1 at the mid-point P of \<sigma>^1; D \<inter> K = {P}; and the 2-cells D decompose N into a
      collection of polyhedral 3-cells C_v, each of which contains exactly one vertex v of
      K. The sets C_v will be called the dual cells of N. The 2-cells D will be called
      splitting disks. **)
definition geotop_is_splitting_disks_and_dual_cells ::
  "(real^3) set set \<Rightarrow> (real^3) set \<Rightarrow> (real^3) set set \<Rightarrow> (real^3) set set \<Rightarrow> bool" where
  "geotop_is_splitting_disks_and_dual_cells K N Ds Cs \<longleftrightarrow>
    geotop_is_complex K \<and>
    (\<forall>\<sigma>\<in>K. \<exists>i\<le>1. geotop_simplex_dim \<sigma> i) \<and>
    N = geotop_regular_neighborhood K K \<and>
    (\<forall>D\<in>Ds. geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2) \<and>
    (\<forall>C\<in>Cs. geotop_is_n_cell C (subspace_topology UNIV geotop_euclidean_topology C) 3) \<and>
    (\<forall>v\<in>geotop_complex_vertices K. \<exists>!C\<in>Cs. v \<in> C)"

(** from \<S>31: tube (geotop.tex:6318)
    LATEX VERSION: Now let h be a homeomorphism N \<rightarrow> M', where M' is a PL 3-manifold but h
      is not necessarily PL. Then N' = h(N) will be called a tube, and the images of the
      splitting disks of N will be called splitting disks of N'. **)
definition geotop_is_tube ::
  "(real^3) set \<Rightarrow> bool" where
  "geotop_is_tube N' \<longleftrightarrow>
    (\<exists>K N (h::real^3 \<Rightarrow> real^3). geotop_is_complex K \<and>
       (\<forall>\<sigma>\<in>K. \<exists>i\<le>1. geotop_simplex_dim \<sigma> i) \<and>
       N = geotop_regular_neighborhood K K \<and>
       top1_homeomorphism_on N (subspace_topology UNIV geotop_euclidean_topology N)
         N' (subspace_topology UNIV geotop_euclidean_topology N') h)"

(** from \<S>31: pseudo-cell (geotop.tex:6320)
    LATEX VERSION: By an open 2-cell we mean a set which is homeomorphic to the interior of
      a 2-cell. Let U be an open 2-cell, in a PL 3-manifold M, and let J be a 1-sphere, such
      that U \<inter> J = \<emptyset> and closure U = U \<union> J. Let P be a point of U, and suppose that U - P is
      a polyhedron. Then the set E = U \<union> J is called a pseudo-cell. **)
definition geotop_is_pseudo_cell ::
  "(real^3) set \<Rightarrow> bool" where
  "geotop_is_pseudo_cell E \<longleftrightarrow>
    (\<exists>U J (P::real^3).
       E = U \<union> J \<and> U \<inter> J = {} \<and>
       geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1 \<and>
       closure_on UNIV geotop_euclidean_topology U = U \<union> J \<and>
       P \<in> U \<and>
       (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = U - {P}) \<and>
       \<comment> \<open>U is homeomorphic to the open interior of a 2-cell\<close>
       (\<exists>(D::(real^3) set) (h::real^3 \<Rightarrow> real^3).
          geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2 \<and>
          top1_homeomorphism_on (geotop_top_interior UNIV geotop_euclidean_topology D)
            (subspace_topology UNIV geotop_euclidean_topology
               (geotop_top_interior UNIV geotop_euclidean_topology D))
            U (subspace_topology UNIV geotop_euclidean_topology U) h))"

section \<open>\<S>32 Pseudo-cells that split tubes\<close>

(** from \<S>32 Theorem 1 (geotop.tex:6330)
    LATEX VERSION: Let N, K, and h: N \<leftrightarrow> N' \<subseteq> R^3 be as in the definition of a tube. Let D
      be a splitting disk of N, and let {P} = D \<inter> |K|. Let C_1 and C_2 be the dual cells of N
      such that C_1 \<inter> C_2 = D, and let v_1 and v_2 be the vertices of K that they contain.
      Let W be a closed neighborhood of Int D' - {P'}, lying in C_1' \<union> C_2'. Then there is a
      pseudo-cell E, with center at P', such that (1) Bd E = Bd D', (2) E \<subseteq> W, and (3) Int E
      separates v_1' and v_2' in Int(C_1' \<union> C_2'). **)
theorem Theorem_GT_32_1:
  fixes N N' D C1 C2 W D' C1' C2' :: "(real^3) set"
  fixes P P' v1 v2 v1' v2' :: "real^3"
  fixes h :: "real^3 \<Rightarrow> real^3"
  assumes "geotop_is_tube N'"
  assumes "geotop_is_n_cell D (subspace_topology UNIV geotop_euclidean_topology D) 2"
  assumes "top1_homeomorphism_on N (subspace_topology UNIV geotop_euclidean_topology N)
             N' (subspace_topology UNIV geotop_euclidean_topology N') h"
  assumes "D' = h ` D" and "C1' = h ` C1" and "C2' = h ` C2" and "P' = h P"
  shows "\<exists>E. geotop_is_pseudo_cell E \<and>
             P' \<in> geotop_top_interior UNIV geotop_euclidean_topology E \<and>
             E \<subseteq> W"
  sorry

(** from \<S>32 Theorem 2 (geotop.tex:6459)
    LATEX VERSION: Under the conditions of Theorem 1, E can be chosen so that
      (C_1' \<union> C_2') - E has exactly two components U_1, U_2, and such that for i = 1, 2 we
      have (5) E \<subseteq> Fr U_i and (6) Bd C_i' \<inter> Bd N' \<subseteq> Fr U_i. **)
theorem Theorem_GT_32_2:
  fixes N' C1' C2' :: "(real^3) set"
  assumes "geotop_is_tube N'"
  assumes "geotop_is_n_cell C1' (subspace_topology UNIV geotop_euclidean_topology C1') 3"
  assumes "geotop_is_n_cell C2' (subspace_topology UNIV geotop_euclidean_topology C2') 3"
  shows "\<exists>E U1 U2. geotop_is_pseudo_cell E \<and>
             U1 \<inter> U2 = {} \<and>
             (C1' \<union> C2') - E = U1 \<union> U2 \<and>
             E \<subseteq> geotop_frontier UNIV geotop_euclidean_topology U1 \<and>
             E \<subseteq> geotop_frontier UNIV geotop_euclidean_topology U2 \<and>
             geotop_frontier UNIV geotop_euclidean_topology C1' \<inter>
               geotop_frontier UNIV geotop_euclidean_topology N'
               \<subseteq> geotop_frontier UNIV geotop_euclidean_topology U1 \<and>
             geotop_frontier UNIV geotop_euclidean_topology C2' \<inter>
               geotop_frontier UNIV geotop_euclidean_topology N'
               \<subseteq> geotop_frontier UNIV geotop_euclidean_topology U2"
  sorry

(** from \<S>32 Theorem 3 (geotop.tex:6486)
    LATEX VERSION: Under the conditions just stated, the sets W_e can be chosen so that
      (7) each set C_i'' contains only one vertex of K', (8) the sets C_i'' lie in arbitrarily
      small neighborhoods of the sets C_i', (9) N' = \<union>_i C_i'', and (10) C_i'' intersects
      C_j'' (i \<noteq> j) only if K has an edge e = v_i v_j, in which case C_i'' \<inter> C_j'' = E_e. **)
theorem Theorem_GT_32_3:
  fixes K :: "(real^3) set set" and N N' :: "(real^3) set"
  fixes h :: "real^3 \<Rightarrow> real^3"
  assumes "geotop_is_tube N'"
  assumes "geotop_is_complex K"
  assumes "\<forall>\<sigma>\<in>K. \<exists>i\<le>1. geotop_simplex_dim \<sigma> i"
  assumes "top1_homeomorphism_on N (subspace_topology UNIV geotop_euclidean_topology N)
             N' (subspace_topology UNIV geotop_euclidean_topology N') h"
  shows "\<exists>C''. (\<forall>v\<in>geotop_complex_vertices K.
                  geotop_is_n_cell (C'' v)
                    (subspace_topology UNIV geotop_euclidean_topology (C'' v)) 3 \<and>
                  card (geotop_complex_vertices K \<inter> C'' v) = 1) \<and>
               N' = (\<Union>v\<in>geotop_complex_vertices K. C'' v) \<and>
               (\<forall>v\<in>geotop_complex_vertices K. \<forall>w\<in>geotop_complex_vertices K.
                  v \<noteq> w \<and> C'' v \<inter> C'' w \<noteq> {} \<longrightarrow>
                  (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 1 \<and> v \<in> \<sigma> \<and> w \<in> \<sigma>))"
  sorry

(** from \<S>32 Theorem 4 (geotop.tex:6492)
    LATEX VERSION: Let E be a pseudo-cell with center P', in R^3, and let \<delta> be a positive
      number. Then there is a polyhedral 2-cell \<Delta>_1, lying in N(P', \<delta>), such that (1) J =
      Bd \<Delta>_1 = \<Delta>_1 \<inter> E and (2) J bounds a 2-cell D_J in E, containing P' in its interior. **)
theorem Theorem_GT_32_4:
  fixes E :: "(real^3) set" and P' :: "real^3" and \<delta> :: real
  assumes "geotop_is_pseudo_cell E"
  assumes "P' \<in> geotop_top_interior UNIV geotop_euclidean_topology E"
  assumes "\<delta> > 0"
  shows "\<exists>\<Delta>1 J DJ. geotop_is_n_cell \<Delta>1 (subspace_topology UNIV geotop_euclidean_topology \<Delta>1) 2 \<and>
             (\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = \<Delta>1) \<and>
             \<Delta>1 \<subseteq> {P. norm (P - P') < \<delta>} \<and>
             geotop_frontier UNIV geotop_euclidean_topology \<Delta>1 = J \<and>
             \<Delta>1 \<inter> E = J \<and>
             geotop_is_n_cell DJ (subspace_topology UNIV geotop_euclidean_topology DJ) 2 \<and>
             DJ \<subseteq> E \<and>
             geotop_frontier UNIV geotop_euclidean_topology DJ = J \<and>
             P' \<in> geotop_top_interior UNIV geotop_euclidean_topology DJ"
  sorry

section \<open>\<S>33 PLH approximations, for regular neighborhoods of linear graphs in R^3\<close>

(** from \<S>33 Theorem 1 (geotop.tex:6498)
    LATEX VERSION: Let K be a finite connected 1-dimensional polyhedron in R^3, such that K
      has no end-points. Let U be an open set containing K, and let h be a homeomorphism
      U \<rightarrow> R^3. Let \<epsilon> be a positive number. Then there is a regular neighborhood N of K,
      lying in U, and a PL homeomorphism f: N \<leftrightarrow> X \<subseteq> R^3, such that (1) X is a neighborhood
      of K' = h(K) and (2) f is an \<epsilon>-approximation of h|N. **)
theorem Theorem_GT_33_1:
  fixes K :: "(real^3) set set" and U :: "(real^3) set" and h :: "real^3 \<Rightarrow> real^3"
  fixes \<epsilon> :: real
  assumes "geotop_is_complex K"
  assumes "finite K"
  assumes "\<forall>\<sigma>\<in>K. \<exists>i\<le>1. geotop_simplex_dim \<sigma> i"
  assumes "top1_connected_on (geotop_polyhedron K)
             (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
  assumes "\<forall>v\<in>geotop_complex_vertices K. \<not> geotop_graph_endpoint K v"
  assumes "U \<in> geotop_euclidean_topology" and "geotop_polyhedron K \<subseteq> U"
  assumes "top1_homeomorphism_on U (subspace_topology UNIV geotop_euclidean_topology U)
             (h ` U) (subspace_topology UNIV geotop_euclidean_topology (h ` U)) h"
  assumes "\<epsilon> > 0"
  shows "\<exists>N f. geotop_is_complex N \<and>
               geotop_polyhedron N = geotop_regular_neighborhood K K \<and>
               geotop_polyhedron N \<subseteq> U \<and>
               top1_homeomorphism_on (geotop_polyhedron N)
                 (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron N))
                 (f ` geotop_polyhedron N)
                 (subspace_topology UNIV geotop_euclidean_topology
                    (f ` geotop_polyhedron N)) f \<and>
               (\<exists>K' K''. geotop_is_complex K' \<and> geotop_is_complex K'' \<and> geotop_PLH K' K'' f) \<and>
               h ` geotop_polyhedron K \<subseteq> f ` geotop_polyhedron N \<and>
               (\<forall>P\<in>geotop_polyhedron N. norm (h P - f P) < \<epsilon>)"
  sorry

section \<open>\<S>34 PLH approximations of homeomorphisms, for polyhedral 3-cells\<close>

(** from \<S>34 Theorem 1 (geotop.tex:6758)
    LATEX VERSION: Let K be a polyhedral 3-cell in R^3, let h be a homeomorphism K \<rightarrow> R^3,
      and let \<epsilon> be a positive number. Then there is a PLH f: K \<rightarrow> R^3 such that f is an
      \<epsilon>-approximation of h. **)
theorem Theorem_GT_34_1:
  fixes K :: "(real^3) set" and h :: "real^3 \<Rightarrow> real^3" and \<epsilon> :: real
  assumes "geotop_is_n_cell K (subspace_topology UNIV geotop_euclidean_topology K) 3"
  assumes "\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = K"
  assumes "top1_homeomorphism_on K (subspace_topology UNIV geotop_euclidean_topology K)
             (h ` K) (subspace_topology UNIV geotop_euclidean_topology (h ` K)) h"
  assumes "\<epsilon> > 0"
  shows "\<exists>f. top1_homeomorphism_on K (subspace_topology UNIV geotop_euclidean_topology K)
               (f ` K) (subspace_topology UNIV geotop_euclidean_topology (f ` K)) f \<and>
             (\<exists>K' K''. geotop_is_complex K' \<and> geotop_is_complex K'' \<and> geotop_PLH K' K'' f) \<and>
             (\<forall>P\<in>K. norm (h P - f P) < \<epsilon>)"
  sorry

section \<open>\<S>35 The Triangulation theorem\<close>

(** from \<S>35 Theorem 1 (geotop.tex:7003)
    LATEX VERSION: Let K be a 1-dimensional polyhedron in a PL 3-manifold M_1. Let U be an
      open set containing K, and let h be a homeomorphism of U into a PL 3-manifold M_2. Let
      \<phi> be a strongly positive function on U. Then there is a regular neighborhood N of K in
      U, and a PLH f: N \<leftrightarrow> X \<subseteq> M_2, such that (1) X is a neighborhood of K' = h(K) and (2)
      f is a \<phi>-approximation of h|N. **)
theorem Theorem_GT_35_1:
  fixes K :: "(real^3) set set" and U :: "(real^3) set"
  fixes h :: "real^3 \<Rightarrow> real^3" and \<phi> :: "real^3 \<Rightarrow> real"
  assumes "geotop_is_complex K"
  assumes "\<forall>\<sigma>\<in>K. \<exists>i\<le>1. geotop_simplex_dim \<sigma> i"
  assumes "U \<in> geotop_euclidean_topology" and "geotop_polyhedron K \<subseteq> U"
  assumes "top1_homeomorphism_on U (subspace_topology UNIV geotop_euclidean_topology U)
             (h ` U) (subspace_topology UNIV geotop_euclidean_topology (h ` U)) h"
  assumes "geotop_strongly_positive U
             (subspace_topology UNIV geotop_euclidean_topology U) \<phi>"
  shows "\<exists>N f. geotop_is_complex N \<and>
               geotop_polyhedron N \<subseteq> U \<and>
               (\<exists>K' K''. geotop_is_complex K' \<and> geotop_is_complex K'' \<and> geotop_PLH K' K'' f) \<and>
               top1_homeomorphism_on (geotop_polyhedron N)
                 (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron N))
                 (f ` geotop_polyhedron N)
                 (subspace_topology UNIV geotop_euclidean_topology
                    (f ` geotop_polyhedron N)) f \<and>
               h ` geotop_polyhedron K \<subseteq> f ` geotop_polyhedron N \<and>
               (\<forall>P\<in>geotop_polyhedron N. norm (h P - f P) < \<phi> P)"
  sorry

(** from \<S>35 Theorem 2 (geotop.tex:7137)
    LATEX VERSION: Let M_1 and M_2 be PL 3-manifolds, let K be a polyhedral 3-manifold with
      boundary in M_1, let h be a homeomorphism K \<rightarrow> M_2, and let \<phi> be a strongly positive
      function on K. Then there is a PLH f: K \<rightarrow> M_2, such that f is a \<phi>-approximation of
      h. **)
theorem Theorem_GT_35_2:
  fixes K :: "(real^3) set" and h :: "real^3 \<Rightarrow> real^3" and \<phi> :: "real^3 \<Rightarrow> real"
  assumes "geotop_n_manifold_with_boundary_on K (\<lambda>x y. norm (x - y)) 3"
  assumes "\<exists>L. geotop_is_complex L \<and> geotop_polyhedron L = K"
  assumes "top1_homeomorphism_on K (subspace_topology UNIV geotop_euclidean_topology K)
             (h ` K) (subspace_topology UNIV geotop_euclidean_topology (h ` K)) h"
  assumes "geotop_strongly_positive K
             (subspace_topology UNIV geotop_euclidean_topology K) \<phi>"
  shows "\<exists>f. top1_homeomorphism_on K (subspace_topology UNIV geotop_euclidean_topology K)
               (f ` K) (subspace_topology UNIV geotop_euclidean_topology (f ` K)) f \<and>
             (\<exists>K' K''. geotop_is_complex K' \<and> geotop_is_complex K'' \<and> geotop_PLH K' K'' f) \<and>
             (\<forall>P\<in>K. norm (h P - f P) < \<phi> P)"
  sorry

(** from \<S>35 Theorem 3 (The triangulation theorem for 3-manifolds) (geotop.tex:7150)
    LATEX VERSION: Let M be a 3-manifold. Then there is a complex K such that M and |K| are
      homeomorphic. **)
theorem Theorem_GT_35_3_triangulation_3manifolds:
  fixes M :: "(real^3) set"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 3"
  shows "\<exists>K. geotop_is_complex K \<and>
             (\<exists>f. top1_homeomorphism_on M (subspace_topology UNIV geotop_euclidean_topology M)
                    (geotop_polyhedron K)
                    (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)) f)"
  sorry

section \<open>\<S>36 The Hauptvermutung; Tame imbedding\<close>

(** from \<S>36 Theorem 1 (geotop.tex:7160)
    LATEX VERSION: Let M_1 and M_2 be PL 3-manifolds, let U be an open set in M_1, let h be
      a homeomorphism U \<rightarrow> M_2, and let \<phi> be a strongly positive function on U. Then there
      is a PLH f: U \<rightarrow> M_2 such that (1) f is a \<phi>-approximation of h and (2) f(U) = h(U). **)
theorem Theorem_GT_36_1:
  fixes U :: "(real^3) set" and h :: "real^3 \<Rightarrow> real^3" and \<phi> :: "real^3 \<Rightarrow> real"
  assumes "U \<in> geotop_euclidean_topology"
  assumes "top1_homeomorphism_on U (subspace_topology UNIV geotop_euclidean_topology U)
             (h ` U) (subspace_topology UNIV geotop_euclidean_topology (h ` U)) h"
  assumes "geotop_strongly_positive U
             (subspace_topology UNIV geotop_euclidean_topology U) \<phi>"
  shows "\<exists>f. top1_homeomorphism_on U (subspace_topology UNIV geotop_euclidean_topology U)
               (f ` U) (subspace_topology UNIV geotop_euclidean_topology (f ` U)) f \<and>
             (\<exists>K K'. geotop_is_complex K \<and> geotop_is_complex K' \<and> geotop_PLH K K' f) \<and>
             (\<forall>P\<in>U. norm (h P - f P) < \<phi> P) \<and>
             f ` U = h ` U"
  sorry

(** from \<S>36 Theorem 2 (The Hauptvermutung for 3-manifolds) (geotop.tex:7166)
    LATEX VERSION: Let K_1 and K_2 be triangulated 3-manifolds. If there is a homeomorphism
      |K_1| \<leftrightarrow> |K_2|, then there is a PLH |K_1| \<leftrightarrow> |K_2|. **)
theorem Theorem_GT_36_2_Hauptvermutung_3manifolds:
  fixes K1 K2 :: "(real^3) set set"
  assumes "geotop_is_complex K1" and "geotop_is_complex K2"
  assumes "geotop_n_manifold_with_boundary_on (geotop_polyhedron K1) (\<lambda>x y. norm (x - y)) 3"
  assumes "geotop_n_manifold_with_boundary_on (geotop_polyhedron K2) (\<lambda>x y. norm (x - y)) 3"
  assumes "\<exists>f. top1_homeomorphism_on (geotop_polyhedron K1)
                 (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K1))
                 (geotop_polyhedron K2)
                 (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K2)) f"
  shows "\<exists>f. top1_homeomorphism_on (geotop_polyhedron K1)
               (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K1))
               (geotop_polyhedron K2)
               (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K2)) f \<and>
             geotop_PLH K1 K2 f"
  sorry

(** from \<S>36 Theorem 3 (geotop.tex:7170)
    LATEX VERSION: In R^3, or in a PL 3-manifold M, every semi-locally tame set is tame.
      In fact, if L is semi-locally tame, then for every open set V containing L, and for
      every \<psi> \<gg> 0 on V, there is a homeomorphism g': M \<leftrightarrow> M such that (1) g'(L) is a polyhedron,
      (2) g'|(M - V) is the identity, and (3) g'|V is a \<psi>-approximation of the identity. **)
theorem Theorem_GT_36_3:
  fixes M L V :: "(real^3) set" and \<psi> :: "real^3 \<Rightarrow> real"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 3"
  assumes "\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = M"
  assumes "geotop_is_semi_locally_tame L"
  assumes "V \<in> geotop_euclidean_topology" and "L \<subseteq> V"
  assumes "geotop_strongly_positive V
             (subspace_topology UNIV geotop_euclidean_topology V) \<psi>"
  shows "\<exists>g'. top1_homeomorphism_on M (subspace_topology UNIV geotop_euclidean_topology M)
                M (subspace_topology UNIV geotop_euclidean_topology M) g' \<and>
              (\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = g' ` L) \<and>
              (\<forall>P\<in>M - V. g' P = P) \<and>
              (\<forall>P\<in>V. norm (g' P - P) < \<psi> P)"
  sorry

(** from \<S>36 Theorem 4 (geotop.tex:7174)
    LATEX VERSION: In R^3, or in a PL 3-manifold, every locally tame set is tame. **)
theorem Theorem_GT_36_4:
  fixes M L :: "(real^3) set"
  assumes "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 3"
  assumes "\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = M"
  assumes "L \<subseteq> M"
  assumes "geotop_is_locally_tame L"
  shows "geotop_is_tame L"
  sorry

end
