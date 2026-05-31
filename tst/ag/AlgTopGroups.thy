theory AlgTopGroups
  imports "K5.K5_nonplanar"
begin


\<comment> \<open>Method by5000: like by100 but with 5000ms timeout for hard proof steps.\<close>
method_setup by5000 =
  \<open>
    Method.text_closure >> (fn text => fn ctxt => fn facts =>
      let
        val limit = Time.fromMilliseconds 5000
        fun timed_seq name lim seq =
          Seq.make (fn () =>
            (case
               (Timeout.apply lim (fn () => Seq.pull seq) ()
                 handle Timeout.TIMEOUT _ =>
                   error (name ^ ": timeout after " ^
                     string_of_int (Time.toMilliseconds lim) ^ " ms"))
             of
               NONE => NONE
             | SOME (st, seq') => SOME (st, timed_seq name lim seq')))
        fun method_evaluate_rt text' ctxt' facts' =
          NO_CONTEXT_TACTIC ctxt' (Method.evaluate_runtime text' ctxt' facts')
        fun tac st = timed_seq "by5000" limit (method_evaluate_rt text ctxt facts st)
      in
        SIMPLE_METHOD tac facts
      end)
  \<close>

lemma map_tl_pair: "tl (map (\<lambda>(s,b). (f s, b)) ws) = map (\<lambda>(s,b). (f s, b)) (tl ws)"
  by (cases ws) (by100 simp)+

lemma tl_take_drop_eq: assumes "j > 0"
  shows "tl (take j ws) @ drop (Suc j) ws = take (j-1) (tl ws) @ drop j (tl ws)"
  using assms by (cases ws; cases j) (by100 simp)+

lemma tl_take_map_pair: "tl (take j (map (\<lambda>(s,b). (f s, b)) ws))
    = map (\<lambda>(s,b). (f s, b)) (take (j - 1) (tl ws))"
proof -
  have "take j (map (\<lambda>(s,b). (f s, b)) ws) = map (\<lambda>(s,b). (f s, b)) (take j ws)"
    by (rule take_map)
  hence "tl (take j (map (\<lambda>(s,b). (f s, b)) ws)) = tl (map (\<lambda>(s,b). (f s, b)) (take j ws))"
    by (by100 simp)
  also have "\<dots> = map (\<lambda>(s,b). (f s, b)) (tl (take j ws))"
    by (rule map_tl_pair)
  also have "tl (take j ws) = take (j - 1) (tl ws)"
  proof (cases ws)
    case Nil thus ?thesis by (by100 simp)
  next
    case (Cons a ws')
    thus ?thesis by (cases j) (by100 simp)+
  qed
  finally show ?thesis by (by100 simp)
qed

lemma tl_take_drop_map_pair:
  assumes "j > 0"
  shows "tl (take j (map (\<lambda>(s,b). (f s, b)) ws)) @ drop (Suc j) (map (\<lambda>(s,b). (f s, b)) ws)
       = map (\<lambda>(s,b). (f s, b)) (take (j - 1) (tl ws) @ drop j (tl ws))"
proof -
  have h1: "tl (take j (map (\<lambda>(s,b). (f s, b)) ws)) = map (\<lambda>(s,b). (f s, b)) (take (j - 1) (tl ws))"
    by (rule tl_take_map_pair)
  have "drop (Suc j) (map (\<lambda>(s,b). (f s, b)) ws) = map (\<lambda>(s,b). (f s, b)) (drop (Suc j) ws)"
    by (rule drop_map)
  also have "drop (Suc j) ws = drop j (tl ws)"
    by (cases ws) (by100 simp)+
  finally have h2: "drop (Suc j) (map (\<lambda>(s,b). (f s, b)) ws) = map (\<lambda>(s,b). (f s, b)) (drop j (tl ws))"
    by (by100 simp)
  have "tl (take j (map (\<lambda>(s,b). (f s, b)) ws)) @ drop (Suc j) (map (\<lambda>(s,b). (f s, b)) ws)
      = map (\<lambda>(s,b). (f s, b)) (take (j - 1) (tl ws)) @ map (\<lambda>(s,b). (f s, b)) (drop j (tl ws))"
    using h1 h2 by (by100 simp)
  also have "\<dots> = map (\<lambda>(s,b). (f s, b)) (take (j - 1) (tl ws) @ drop j (tl ws))"
    by (by100 simp)
  finally show ?thesis .
qed

text \<open>Helper: fst-set of flipped/reversed word = fst-set of original.\<close>
lemma fst_set_flip_rev: "fst ` set (map (\<lambda>(s,b). (s, \<not>b)) (rev ws)) = fst ` set ws"
proof -
  have "set (map (\<lambda>(s,b). (s, \<not>b)) (rev ws)) = (\<lambda>(s,b). (s, \<not>b)) ` set (rev ws)"
    by (by100 simp)
  also have "set (rev ws) = set ws" by (by100 simp)
  finally have h1: "set (map (\<lambda>(s,b). (s, \<not>b)) (rev ws)) = (\<lambda>(s,b). (s, \<not>b)) ` set ws" .
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> fst ` set (map (\<lambda>(s,b). (s, \<not>b)) (rev ws))"
    then obtain p where "p \<in> set (map (\<lambda>(s,b). (s, \<not>b)) (rev ws))" "fst p = x" by (by100 blast)
    hence "p \<in> (\<lambda>(s,b). (s, \<not>b)) ` set ws" using h1 by (by100 blast)
    then obtain s b where "(s, b) \<in> set ws" "p = (s, \<not>b)" by (by100 auto)
    hence "x = s" using \<open>fst p = x\<close> by (by100 simp)
    thus "x \<in> fst ` set ws" using \<open>(s,b) \<in> set ws\<close> by (by100 force)
  next
    fix x assume "x \<in> fst ` set ws"
    then obtain s b where "(s, b) \<in> set ws" "x = s" by (by100 force)
    hence "(s, \<not>b) \<in> (\<lambda>(s,b). (s, \<not>b)) ` set ws" by (by100 force)
    hence "(s, \<not>b) \<in> set (map (\<lambda>(s,b). (s, \<not>b)) (rev ws))" using h1 by (by100 blast)
    thus "x \<in> fst ` set (map (\<lambda>(s,b). (s, \<not>b)) (rev ws))" using \<open>x = s\<close> by (by100 force)
  qed
qed

text \<open>Helper: mapped word membership transfer through flip\_rev.\<close>
lemma mapped_word_fst_flip_rev:
  assumes "\<forall>i<length (map (\<lambda>(s,b). (f s, b)) ws). fst (map (\<lambda>(s,b). (f s, b)) ws ! i) \<in> H"
  shows "\<forall>i<length (map (\<lambda>(s,b). (f s, b)) (map (\<lambda>(s,b). (s, \<not>b)) (rev ws))).
    fst (map (\<lambda>(s,b). (f s, b)) (map (\<lambda>(s,b). (s, \<not>b)) (rev ws)) ! i) \<in> H"
proof (intro allI impI)
  fix i assume hi: "i < length (map (\<lambda>(s,b). (f s, b)) (map (\<lambda>(s,b). (s, \<not>b)) (rev ws)))"
  hence hi': "i < length ws" by (by100 simp)
  \<comment> \<open>Use fst\_set\_flip\_rev: fst-set is preserved by flip+rev.\<close>
  define mws where "mws = map (\<lambda>(s,b). (f s, b)) ws"
  define ys where "ys = map (\<lambda>(x,b). (x, \<not>b)) (rev mws)"
  have hflip: "map (\<lambda>(s,b). (f s, b)) (map (\<lambda>(s,b). (s, \<not>b)) (rev ws))
      = map (\<lambda>(s,b). (s, \<not>b)) (map (\<lambda>(s,b). (f s, b)) (rev ws))"
    by (induction ws) (by100 auto)+
  have hrev: "map (\<lambda>(s,b). (f s, b)) (rev ws) = rev mws"
    unfolding mws_def by (induction ws) (by100 simp)+
  have hys_eq: "map (\<lambda>(s,b). (f s, b)) (map (\<lambda>(s,b). (s, \<not>b)) (rev ws)) = ys"
    unfolding ys_def using hflip hrev by (by100 simp)
  have "fst (ys ! i) \<in> fst ` set ys"
  proof -
    have "i < length ys" using hi hys_eq by (by100 simp)
    hence "ys ! i \<in> set ys" using nth_mem by (by100 blast)
    thus ?thesis by (by100 force)
  qed
  also have "fst ` set ys = fst ` set mws"
    unfolding ys_def by (rule fst_set_flip_rev)
  finally have "fst (ys ! i) \<in> fst ` set mws" .
  hence "fst (ys ! i) \<in> H"
  proof -
    assume "fst (ys ! i) \<in> fst ` set mws"
    then obtain p where "p \<in> set mws" "fst p = fst (ys ! i)" by (by100 force)
    then obtain k where "k < length mws" "mws ! k = p" using in_set_conv_nth by (by100 metis)
    have "fst (mws ! k) \<in> H" using assms \<open>k < length mws\<close> unfolding mws_def by (by100 blast)
    thus ?thesis using \<open>mws ! k = p\<close> \<open>fst p = fst (ys ! i)\<close> by (by100 simp)
  qed
  thus "fst (map (\<lambda>(s,b). (f s, b)) (map (\<lambda>(s,b). (s, \<not>b)) (rev ws)) ! i) \<in> H"
    using hys_eq hi by (by100 simp)
qed

text \<open>Helper: map that applies f to fst of pairs commutes with rev and flip.\<close>
lemma map_pair_fst_rev: "map (\<lambda>(s,b). (f s, b)) (rev ws) = rev (map (\<lambda>(s,b). (f s, b)) ws)"
  by (induction ws) (by100 simp)+

lemma map_pair_fst_flip: "map (\<lambda>(s,b). (f s, b)) (map (\<lambda>(s,b). (s, \<not>b)) ws)
    = map (\<lambda>(s,b). (s, \<not>b)) (map (\<lambda>(s,b). (f s, b)) ws)"
  by (induction ws) (by100 auto)+

lemma map_pair_fst_flip_rev: "map (\<lambda>(s,b). (f s, b)) (map (\<lambda>(s,b). (s, \<not>b)) (rev ws))
    = map (\<lambda>(x,b). (x, \<not>b)) (rev (map (\<lambda>(s,b). (f s, b)) ws))"
proof -
  have "map (\<lambda>(s,b). (f s, b)) (map (\<lambda>(s,b). (s, \<not>b)) (rev ws))
      = map (\<lambda>(s,b). (s, \<not>b)) (map (\<lambda>(s,b). (f s, b)) (rev ws))"
    by (rule map_pair_fst_flip)
  also have "map (\<lambda>(s,b). (f s, b)) (rev ws) = rev (map (\<lambda>(s,b). (f s, b)) ws)"
    by (rule map_pair_fst_rev)
  finally show ?thesis .
qed

lemma map_pair_fst_append: "map (\<lambda>(s,b). (f s, b)) (ws1 @ ws2)
    = map (\<lambda>(s,b). (f s, b)) ws1 @ map (\<lambda>(s,b). (f s, b)) ws2"
  by (by100 simp)

text \<open>Theorems 58.7, 63.1(b), 65.1, 65.2 and supporting lemmas (SCC\_pi1\_iso\_Z,
  K4\_final\_contradiction, K4\_nonadjacent\_edges\_different\_components) are in
  AlgIsoFixedBase.thy and AlgIsoFixed.thy (imported above).\<close>


\<comment> \<open>Lemma 64.1 boundary structure: for theta space A\<union>B\<union>C on S2, each component
   of S2-theta is separated from the opposite arc by its bounding SCC.
   Specifically: if U is a theta component, A\<union>B is SCC, and E is a connected set
   with E \<inter> (A\<union>B) = {} containing a point of U and a point of C-{a,b},
   then False (U and C-{a,b} are in different S2-(A\<union>B) components).
   This is the key fact for K33/K5 non-planarity.\<close>
\<comment> \<open>For a theta space with 3 components U,V,W and 3 SCCs (A\<union>B, B\<union>C, A\<union>C):
   each SCC separates S2 into 2 parts. The 3 components + C-{a,b} go to 2 sides.
   One theta component is alone on one side (its boundary = that SCC).
   Result: for each vertex e in U\<union>V\<union>W, some arc from e reaches a vertex
   on the "wrong side" of that SCC, giving a contradiction.

   This helper: given that each of 3 arcs eh1,eh2,eh3 avoids one SCC
   and reaches a vertex on the opposite theta arc, show e can't be in any component.\<close>
lemma theta_space_vertex_exclusion:
  assumes hS2: "is_topology_on_strict top1_S2 top1_S2_topology"
      and hA_sub: "A \<subseteq> top1_S2" and hB_sub: "B \<subseteq> top1_S2" and hC_sub: "C \<subseteq> top1_S2"
      and hA_arc: "top1_is_arc_on A (subspace_topology top1_S2 top1_S2_topology A)"
      and hB_arc: "top1_is_arc_on B (subspace_topology top1_S2 top1_S2_topology B)"
      and hC_arc: "top1_is_arc_on C (subspace_topology top1_S2 top1_S2_topology C)"
      and hab: "a \<noteq> b" and hAB: "A \<inter> B = {a, b}" and hBC: "B \<inter> C = {a, b}" and hAC: "A \<inter> C = {a, b}"
      and hA_ep: "top1_arc_endpoints_on A (subspace_topology top1_S2 top1_S2_topology A) = {a, b}"
      and hB_ep: "top1_arc_endpoints_on B (subspace_topology top1_S2 top1_S2_topology B) = {a, b}"
      and hC_ep: "top1_arc_endpoints_on C (subspace_topology top1_S2 top1_S2_topology C) = {a, b}"
      \<comment> \<open>3 theta components.\<close>
      and hU: "U \<noteq> {}" "U \<in> top1_S2_topology" "U \<subseteq> top1_S2 - (A \<union> B \<union> C)"
          "top1_connected_on U (subspace_topology top1_S2 top1_S2_topology U)"
      and hV: "V \<noteq> {}" "V \<in> top1_S2_topology" "V \<subseteq> top1_S2 - (A \<union> B \<union> C)"
          "top1_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
      and hW: "W \<noteq> {}" "W \<in> top1_S2_topology" "W \<subseteq> top1_S2 - (A \<union> B \<union> C)"
          "top1_connected_on W (subspace_topology top1_S2 top1_S2_topology W)"
      and hUVW: "U \<inter> V = {}" "V \<inter> W = {}" "U \<inter> W = {}" "U \<union> V \<union> W = top1_S2 - (A \<union> B \<union> C)"
      \<comment> \<open>Point e in some component, with 3 arcs to vertices on opposite arcs.\<close>
      and he: "e \<in> U \<union> V \<union> W"
      and hE1_sub: "E1 \<subseteq> top1_S2" and hE1_conn: "top1_connected_on E1 (subspace_topology top1_S2 top1_S2_topology E1)"
      and hE1_disj: "E1 \<inter> (B \<union> C) = {}" and hE1_e: "e \<in> E1" and hE1_h: "E1 \<inter> (A - {a, b}) \<noteq> {}"
      and hE2_sub: "E2 \<subseteq> top1_S2" and hE2_conn: "top1_connected_on E2 (subspace_topology top1_S2 top1_S2_topology E2)"
      and hE2_disj: "E2 \<inter> (A \<union> C) = {}" and hE2_e: "e \<in> E2" and hE2_h: "E2 \<inter> (B - {a, b}) \<noteq> {}"
      and hE3_sub: "E3 \<subseteq> top1_S2" and hE3_conn: "top1_connected_on E3 (subspace_topology top1_S2 top1_S2_topology E3)"
      and hE3_disj: "E3 \<inter> (A \<union> B) = {}" and hE3_e: "e \<in> E3" and hE3_h: "E3 \<inter> (C - {a, b}) \<noteq> {}"
  shows False
proof -
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using hS2 unfolding is_topology_on_strict_def by (by100 blast)
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
  \<comment> \<open>Each pair of arcs forms an SCC.\<close>
  have hAB_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology (A \<union> B)"
    by (rule arcs_form_simple_closed_curve[OF hS2 hS2_haus hA_arc hA_sub hB_arc hB_sub hAB hab hA_ep hB_ep])
  have hBC_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology (B \<union> C)"
    by (rule arcs_form_simple_closed_curve[OF hS2 hS2_haus hB_arc hB_sub hC_arc hC_sub hBC hab hB_ep hC_ep])
  have hAC_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology (A \<union> C)"
    by (rule arcs_form_simple_closed_curve[OF hS2 hS2_haus hA_arc hA_sub hC_arc hC_sub hAC hab hA_ep hC_ep])
  \<comment> \<open>Each SCC separates S2. So S2-SCC is disconnected.
     For each SCC J, each theta component \<subseteq> one side (connected \<subseteq> S2-J \<subseteq> S2-theta \<subseteq> S2-J).
     The "lone" component on one side is a full S2-J component.\<close>
  \<comment> \<open>E3 \<subseteq> S2-(A\<union>B). e \<in> E3, e \<in> U\<union>V\<union>W. E3 connected.
     C-{a,b} \<subseteq> S2-(A\<union>B). E3 \<inter> (C-{a,b}) \<noteq> {}.
     If e's theta component is separated from C-{a,b} in S2-(A\<union>B): contradiction (E3 bridges).
     Similarly for E1 with B\<union>C and E2 with A\<union>C.
     By pigeonhole: one of the 3 SCCs separates e's component from the arc's vertex.\<close>
  \<comment> \<open>For each SCC J: S2-J has 2 components. e's theta component X \<subseteq> one side.
     The opposite arc interior (A/B/C - {a,b}) \<subseteq> one side.
     If X and opposite arc on DIFFERENT sides: E\_i bridges \<Rightarrow> contradiction.
     If X and opposite arc on SAME side for ALL 3 SCCs:
     For each SCC, the "other side" contains at most 2 of {U,V,W}-{X}.
     By pigeonhole among 3 SCCs over 2 elements: some Y is "alone" for 2 SCCs.
     cl(Y) = Y\<union>J1 = Y\<union>J2 \<Rightarrow> J1=J2 \<Rightarrow> A=C or similar \<Rightarrow> A \<subseteq> {a,b} \<Rightarrow> contradiction (arc).\<close>
  \<comment> \<open>Step 1: For SCC A\<union>B, get 2 components and place pieces.\<close>
  have hAB_cl: "closedin_on top1_S2 top1_S2_topology (A \<union> B)"
    by (rule closedin_on_Un[OF hTopS2 arc_in_S2_closed[OF hA_sub hA_arc] arc_in_S2_closed[OF hB_sub hB_arc]])
  have hAB_card: "card (A \<inter> B) = 2" using hAB hab by (by100 simp)
  obtain P1 Q1 where hPQ1: "P1 \<noteq> {}" "Q1 \<noteq> {}" "P1 \<inter> Q1 = {}"
      "P1 \<union> Q1 = top1_S2 - (A \<union> B)"
      "top1_connected_on P1 (subspace_topology top1_S2 top1_S2_topology P1)"
      "top1_connected_on Q1 (subspace_topology top1_S2 top1_S2_topology Q1)"
    using Theorem_63_5_two_closed_connected[OF hS2 arc_in_S2_closed[OF hA_sub hA_arc]
        arc_in_S2_closed[OF hB_sub hB_arc]
        arc_connected[OF hA_arc] arc_connected[OF hB_arc] hAB_card
        Theorem_63_2_arc_no_separation[OF hS2 hA_sub hA_arc]
        Theorem_63_2_arc_no_separation[OF hS2 hB_sub hB_arc]]
    by (metis (no_types))
  \<comment> \<open>Make open.\<close>
  have hAB_open: "top1_S2 - (A \<union> B) \<in> top1_S2_topology"
    using hAB_cl unfolding closedin_on_def by (by100 blast)
  have hAB_not_conn: "\<not> top1_connected_on (top1_S2 - (A \<union> B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B)))"
    using Theorem_61_3_JordanSeparation_S2[OF hS2 hAB_scc] unfolding top1_separates_on_def by (by100 simp)
  have hPQ1_open: "P1 \<in> top1_S2_topology \<and> Q1 \<in> top1_S2_topology"
    using S2_two_component_open[OF hAB_open _ hPQ1(1,2,3,4,5,6) hAB_not_conn] by (by100 blast)
  \<comment> \<open>Each theta component + C-{a,b} in P1 or Q1.\<close>
  \<comment> \<open>E3 connected \<subseteq> S2-(A\<union>B). If e's component X and C-{a,b} in different P1/Q1:
     E3 \<inter> X \<noteq> {} and E3 \<inter> (C-{a,b}) \<noteq> {}. E3 connected \<subseteq> P1\<union>Q1.
     X \<subseteq> Pi, C-{a,b} \<subseteq> Qj with i\<noteq>j. E3 meets Pi and Qj. By Lemma\_23\_2: impossible.\<close>
  have hE3_sub_AB: "E3 \<subseteq> top1_S2 - (A \<union> B)"
    using hE3_sub hE3_disj by (by100 blast)
  \<comment> \<open>Determine e's component X.\<close>
  from he obtain X where hX: "X \<in> {U, V, W}" "e \<in> X" by (by100 blast)
  have hX_sub: "X \<subseteq> top1_S2 - (A \<union> B \<union> C)" using hX(1) hU(3) hV(3) hW(3) by (by100 blast)
  have hX_conn: "top1_connected_on X (subspace_topology top1_S2 top1_S2_topology X)"
    using hX(1) hU(4) hV(4) hW(4) by (by100 blast)
  have hX_ne: "X \<noteq> {}" using hX(2) by (by100 blast)
  have hX_open: "X \<in> top1_S2_topology" using hX(1) hU(2) hV(2) hW(2) by (by100 blast)
  \<comment> \<open>X \<subseteq> P1 or Q1.\<close>
  have hX_sub_AB: "X \<subseteq> top1_S2 - (A \<union> B)" using hX_sub by (by100 blast)
  have hX_in_PQ1: "X \<subseteq> P1 \<or> X \<subseteq> Q1"
  proof -
    have hTAB: "is_topology_on (top1_S2-(A\<union>B)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B)))"
      by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
    have hP1_op: "P1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B))"
      using hPQ1_open hPQ1(4) unfolding subspace_topology_def by (by100 blast)
    have hQ1_op: "Q1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B))"
      using hPQ1_open hPQ1(4) unfolding subspace_topology_def by (by100 blast)
    have hSep1: "top1_is_separation_on (top1_S2-(A\<union>B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B))) P1 Q1"
      unfolding top1_is_separation_on_def using hP1_op hQ1_op hPQ1(1,2,3,4) by (by100 blast)
    have hX_conn_AB: "top1_connected_on X (subspace_topology (top1_S2-(A\<union>B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B))) X)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology X =
          subspace_topology (top1_S2-(A\<union>B)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B))) X"
        using subspace_topology_trans[of X "top1_S2-(A\<union>B)"] hX_sub_AB by (by100 simp)
      thus ?thesis using hX_conn by (by100 simp)
    qed
    from Lemma_23_2[OF hTAB hSep1 hX_sub_AB hX_conn_AB] show ?thesis by (by100 blast)
  qed
  \<comment> \<open>C-{a,b} \<subseteq> P1 or Q1.\<close>
  have hC_sub_AB: "C - {a, b} \<subseteq> top1_S2 - (A \<union> B)"
    using hC_sub hAC hBC by (by100 blast)
  have hC_conn_loc: "top1_connected_on (C - {a, b}) (subspace_topology top1_S2 top1_S2_topology (C - {a, b}))"
    by (rule arc_minus_endpoints_connected[OF hS2 hS2_haus hC_sub hC_arc hC_ep hab])
  have hC_ne_loc: "C - {a, b} \<noteq> {}"
  proof
    assume "C - {a, b} = {}"
    have "a \<in> closure_on top1_S2 top1_S2_topology (C - {a,b})"
      using arc_endpoint_in_closure_of_interior[OF hS2 hS2_haus hC_sub hC_arc hC_ep hab] by (by100 blast)
    hence "a \<in> closure_on top1_S2 top1_S2_topology {}" using \<open>C - {a,b} = {}\<close> by (by100 simp)
    thus False using top1_closure_on_empty[OF hTopS2] by (by100 simp)
  qed
  have hC_in_PQ1: "C - {a, b} \<subseteq> P1 \<or> C - {a, b} \<subseteq> Q1"
  proof -
    have hTAB: "is_topology_on (top1_S2-(A\<union>B)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B)))"
      by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
    have hP1_op: "P1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B))"
      using hPQ1_open hPQ1(4) unfolding subspace_topology_def by (by100 blast)
    have hQ1_op: "Q1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B))"
      using hPQ1_open hPQ1(4) unfolding subspace_topology_def by (by100 blast)
    have hSep1: "top1_is_separation_on (top1_S2-(A\<union>B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B))) P1 Q1"
      unfolding top1_is_separation_on_def using hP1_op hQ1_op hPQ1(1,2,3,4) by (by100 blast)
    have hC_conn_AB: "top1_connected_on (C-{a,b}) (subspace_topology (top1_S2-(A\<union>B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B))) (C-{a,b}))"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology (C-{a,b}) =
          subspace_topology (top1_S2-(A\<union>B)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B))) (C-{a,b})"
        using subspace_topology_trans[of "C-{a,b}" "top1_S2-(A\<union>B)"] hC_sub_AB by (by100 simp)
      thus ?thesis using hC_conn_loc by (by100 simp)
    qed
    from Lemma_23_2[OF hTAB hSep1 hC_sub_AB hC_conn_AB] show ?thesis by (by100 blast)
  qed
  \<comment> \<open>If X and C-{a,b} in DIFFERENT sides: E3 bridges \<Rightarrow> contradiction.\<close>
  \<comment> \<open>If X and C-{a,b} in SAME side: need to check other 2 SCCs similarly.
     By pigeonhole, one theta component is "lone" for 2 SCCs \<Rightarrow>
     cl(Y)=Y\<union>J1=Y\<union>J2 \<Rightarrow> J1=J2 \<Rightarrow> two arcs equal \<Rightarrow> arc = {a,b} \<Rightarrow> False.\<close>
  \<comment> \<open>Case 1: X and C-{a,b} on different sides of A\<union>B.\<close>
  { assume hdiff: "(X \<subseteq> P1 \<and> C - {a,b} \<subseteq> Q1) \<or> (X \<subseteq> Q1 \<and> C - {a,b} \<subseteq> P1)"
    \<comment> \<open>E3 connected \<subseteq> S2-(A\<union>B) = P1\<union>Q1. E3\<inter>X \<noteq> {} (e \<in> X \<inter> E3).
       E3\<inter>(C-{a,b}) \<noteq> {} (hE3\_h). X in one side, C-{a,b} in other.
       E3 must be in one side (Lemma\_23\_2). But meets both. Contradiction.\<close>
    have "False"
    proof -
      \<comment> \<open>E3 \<subseteq> S2-(A\<union>B) = P1\<union>Q1. E3 connected. Apply Lemma\_23\_2.\<close>
      have hTAB: "is_topology_on (top1_S2-(A\<union>B)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B)))"
        by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
      have hP1_op: "P1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B))"
        using hPQ1_open hPQ1(4) unfolding subspace_topology_def by (by100 blast)
      have hQ1_op: "Q1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B))"
        using hPQ1_open hPQ1(4) unfolding subspace_topology_def by (by100 blast)
      have hSep1: "top1_is_separation_on (top1_S2-(A\<union>B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B))) P1 Q1"
        unfolding top1_is_separation_on_def using hP1_op hQ1_op hPQ1(1,2,3,4) by (by100 blast)
      have hE3_conn_AB: "top1_connected_on E3 (subspace_topology (top1_S2-(A\<union>B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B))) E3)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology E3 =
            subspace_topology (top1_S2-(A\<union>B)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>B))) E3"
          using subspace_topology_trans[of E3 "top1_S2-(A\<union>B)"] hE3_sub_AB by (by100 simp)
        thus ?thesis using hE3_conn by (by100 simp)
      qed
      from Lemma_23_2_disjoint[OF hTAB hSep1 hE3_sub_AB hE3_conn_AB]
      have hE3_disj_PQ: "E3 \<inter> Q1 = {} \<or> E3 \<inter> P1 = {}" .
      from hdiff show False
      proof (elim disjE conjE)
        assume hXP: "X \<subseteq> P1" and hCQ: "C - {a,b} \<subseteq> Q1"
        have "E3 \<inter> P1 \<noteq> {}" using hE3_e hX(2) hXP by (by100 blast)
        have "E3 \<inter> Q1 \<noteq> {}" using hE3_h hCQ by (by100 blast)
        thus False using hE3_disj_PQ \<open>E3 \<inter> P1 \<noteq> {}\<close> by (by100 blast)
      next
        assume hXQ: "X \<subseteq> Q1" and hCP: "C - {a,b} \<subseteq> P1"
        have "E3 \<inter> Q1 \<noteq> {}" using hE3_e hX(2) hXQ by (by100 blast)
        have "E3 \<inter> P1 \<noteq> {}" using hE3_h hCP by (by100 blast)
        thus False using hE3_disj_PQ \<open>E3 \<inter> Q1 \<noteq> {}\<close> by (by100 blast)
      qed
    qed
  } note case_AB = this
  \<comment> \<open>Now use the case 1 result: if X and C on different sides of A\<union>B, done.
     Otherwise: X and C on same side. Do the same for B\<union>C (with E1) and A\<union>C (with E2).
     If any SCC separates X from the opposite arc: done (same E-bridges argument).
     If ALL 3 SCCs have X on same side as the opposite arc:
     pigeonhole \<Rightarrow> one of {U,V,W}-{X} is alone for 2 SCCs \<Rightarrow> J1=J2 \<Rightarrow> False.\<close>
  \<comment> \<open>If X and C on different sides of A\<union>B: E3 bridges, done (proved above).
     If same side: repeat with B\<union>C (E1) and A\<union>C (E2).
     By symmetry, if any SCC separates X from the opposite arc: same E-bridges proof.
     If ALL same side: pigeonhole \<Rightarrow> 2 SCCs have same "lone" component \<Rightarrow>
     J1 = J2 \<Rightarrow> arc \<subseteq> {a,b} \<Rightarrow> contradiction.\<close>
  \<comment> \<open>Define a function: for each SCC, whether X is separated from opposite arc.\<close>
  \<comment> \<open>For SCC A\<union>B: X vs C. For SCC B\<union>C: X vs A. For SCC A\<union>C: X vs B.\<close>
  \<comment> \<open>If any SCC separates: use the E-bridges proof (case 1 pattern) with the right E.\<close>
  \<comment> \<open>Setup for B\<union>C and A\<union>C follows the same pattern as A\<union>B above.\<close>
  have hE1_sub_BC: "E1 \<subseteq> top1_S2 - (B \<union> C)" using hE1_sub hE1_disj by (by100 blast)
  have hE2_sub_AC: "E2 \<subseteq> top1_S2 - (A \<union> C)" using hE2_sub hE2_disj by (by100 blast)
  have hX_sub_BC: "X \<subseteq> top1_S2 - (B \<union> C)" using hX_sub by (by100 blast)
  have hX_sub_AC: "X \<subseteq> top1_S2 - (A \<union> C)" using hX_sub by (by100 blast)
  have hA_sub_BC: "A - {a, b} \<subseteq> top1_S2 - (B \<union> C)" using hA_sub hAB hAC by (by100 blast)
  have hB_sub_AC: "B - {a, b} \<subseteq> top1_S2 - (A \<union> C)" using hB_sub hAB hBC by (by100 blast)
  \<comment> \<open>Get 2-component decompositions for B\<union>C and A\<union>C.\<close>
  have hBC_card: "card (B \<inter> C) = 2" using hBC hab by (by100 simp)
  obtain P2 Q2 where hPQ2: "P2 \<noteq> {}" "Q2 \<noteq> {}" "P2 \<inter> Q2 = {}" "P2 \<union> Q2 = top1_S2 - (B \<union> C)"
      "top1_connected_on P2 (subspace_topology top1_S2 top1_S2_topology P2)"
      "top1_connected_on Q2 (subspace_topology top1_S2 top1_S2_topology Q2)"
    using Theorem_63_5_two_closed_connected[OF hS2 arc_in_S2_closed[OF hB_sub hB_arc]
        arc_in_S2_closed[OF hC_sub hC_arc] arc_connected[OF hB_arc] arc_connected[OF hC_arc]
        hBC_card Theorem_63_2_arc_no_separation[OF hS2 hB_sub hB_arc]
        Theorem_63_2_arc_no_separation[OF hS2 hC_sub hC_arc]]
    by (metis (no_types))
  have hAC_card: "card (A \<inter> C) = 2" using hAC hab by (by100 simp)
  obtain P3 Q3 where hPQ3: "P3 \<noteq> {}" "Q3 \<noteq> {}" "P3 \<inter> Q3 = {}" "P3 \<union> Q3 = top1_S2 - (A \<union> C)"
      "top1_connected_on P3 (subspace_topology top1_S2 top1_S2_topology P3)"
      "top1_connected_on Q3 (subspace_topology top1_S2 top1_S2_topology Q3)"
    using Theorem_63_5_two_closed_connected[OF hS2 arc_in_S2_closed[OF hA_sub hA_arc]
        arc_in_S2_closed[OF hC_sub hC_arc] arc_connected[OF hA_arc] arc_connected[OF hC_arc]
        hAC_card Theorem_63_2_arc_no_separation[OF hS2 hA_sub hA_arc]
        Theorem_63_2_arc_no_separation[OF hS2 hC_sub hC_arc]]
    by (metis (no_types))
  \<comment> \<open>For each SCC: X and opposite arc on same or different side.
     If different: E-bridges argument gives False.\<close>
  \<comment> \<open>If ALL same: pigeonhole.\<close>
  \<comment> \<open>X and A-{a,b} placement in {P2,Q2}.\<close>
  have hBC_cl: "closedin_on top1_S2 top1_S2_topology (B \<union> C)"
    by (rule closedin_on_Un[OF hTopS2 arc_in_S2_closed[OF hB_sub hB_arc] arc_in_S2_closed[OF hC_sub hC_arc]])
  have hBC_open: "top1_S2 - (B \<union> C) \<in> top1_S2_topology"
    using hBC_cl unfolding closedin_on_def by (by100 blast)
  have hBC_not_conn: "\<not> top1_connected_on (top1_S2 - (B \<union> C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (B \<union> C)))"
    using Theorem_61_3_JordanSeparation_S2[OF hS2 hBC_scc] unfolding top1_separates_on_def by (by100 simp)
  have hPQ2_open: "P2 \<in> top1_S2_topology \<and> Q2 \<in> top1_S2_topology"
    using S2_two_component_open[OF hBC_open _ hPQ2(1,2,3,4,5,6) hBC_not_conn] by (by100 blast)
  have hTBC: "is_topology_on (top1_S2-(B\<union>C)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(B\<union>C)))"
    by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
  have hP2_op: "P2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(B\<union>C))"
    using hPQ2_open hPQ2(4) unfolding subspace_topology_def by (by100 blast)
  have hQ2_op: "Q2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(B\<union>C))"
    using hPQ2_open hPQ2(4) unfolding subspace_topology_def by (by100 blast)
  have hSep2: "top1_is_separation_on (top1_S2-(B\<union>C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2-(B\<union>C))) P2 Q2"
    unfolding top1_is_separation_on_def using hP2_op hQ2_op hPQ2(1,2,3,4) by (by100 blast)
  have hX_in_PQ2: "X \<subseteq> P2 \<or> X \<subseteq> Q2"
  proof -
    have hX_conn_BC: "top1_connected_on X (subspace_topology (top1_S2-(B\<union>C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2-(B\<union>C))) X)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology X =
          subspace_topology (top1_S2-(B\<union>C)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(B\<union>C))) X"
        using subspace_topology_trans[of X "top1_S2-(B\<union>C)"] hX_sub_BC by (by100 simp)
      thus ?thesis using hX_conn by (by100 simp)
    qed
    from Lemma_23_2[OF hTBC hSep2 hX_sub_BC hX_conn_BC] show ?thesis by (by100 blast)
  qed
  have hA_ne_loc: "A - {a, b} \<noteq> {}"
  proof
    assume "A - {a, b} = {}"
    have "a \<in> closure_on top1_S2 top1_S2_topology (A - {a,b})"
      using arc_endpoint_in_closure_of_interior[OF hS2 hS2_haus hA_sub hA_arc hA_ep hab] by (by100 blast)
    hence "a \<in> closure_on top1_S2 top1_S2_topology {}" using \<open>A - {a,b} = {}\<close> by (by100 simp)
    thus False using top1_closure_on_empty[OF hTopS2] by (by100 simp)
  qed
  have hA_conn_loc: "top1_connected_on (A - {a,b}) (subspace_topology top1_S2 top1_S2_topology (A - {a,b}))"
    by (rule arc_minus_endpoints_connected[OF hS2 hS2_haus hA_sub hA_arc hA_ep hab])
  have hA_in_PQ2: "A - {a, b} \<subseteq> P2 \<or> A - {a, b} \<subseteq> Q2"
  proof -
    have hA_conn_BC: "top1_connected_on (A-{a,b}) (subspace_topology (top1_S2-(B\<union>C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2-(B\<union>C))) (A-{a,b}))"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology (A-{a,b}) =
          subspace_topology (top1_S2-(B\<union>C)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(B\<union>C))) (A-{a,b})"
        using subspace_topology_trans[of "A-{a,b}" "top1_S2-(B\<union>C)"] hA_sub_BC by (by100 simp)
      thus ?thesis using hA_conn_loc by (by100 simp)
    qed
    from Lemma_23_2[OF hTBC hSep2 hA_sub_BC hA_conn_BC] show ?thesis by (by100 blast)
  qed
  \<comment> \<open>X and B-{a,b} placement in {P3,Q3}.\<close>
  have hAC_cl: "closedin_on top1_S2 top1_S2_topology (A \<union> C)"
    by (rule closedin_on_Un[OF hTopS2 arc_in_S2_closed[OF hA_sub hA_arc] arc_in_S2_closed[OF hC_sub hC_arc]])
  have hAC_open: "top1_S2 - (A \<union> C) \<in> top1_S2_topology"
    using hAC_cl unfolding closedin_on_def by (by100 blast)
  have hAC_not_conn: "\<not> top1_connected_on (top1_S2 - (A \<union> C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> C)))"
    using Theorem_61_3_JordanSeparation_S2[OF hS2 hAC_scc] unfolding top1_separates_on_def by (by100 simp)
  have hPQ3_open: "P3 \<in> top1_S2_topology \<and> Q3 \<in> top1_S2_topology"
    using S2_two_component_open[OF hAC_open _ hPQ3(1,2,3,4,5,6) hAC_not_conn] by (by100 blast)
  have hTAC: "is_topology_on (top1_S2-(A\<union>C)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>C)))"
    by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
  have hP3_op: "P3 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>C))"
    using hPQ3_open hPQ3(4) unfolding subspace_topology_def by (by100 blast)
  have hQ3_op: "Q3 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>C))"
    using hPQ3_open hPQ3(4) unfolding subspace_topology_def by (by100 blast)
  have hSep3: "top1_is_separation_on (top1_S2-(A\<union>C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>C))) P3 Q3"
    unfolding top1_is_separation_on_def using hP3_op hQ3_op hPQ3(1,2,3,4) by (by100 blast)
  have hX_in_PQ3: "X \<subseteq> P3 \<or> X \<subseteq> Q3"
  proof -
    have hX_conn_AC: "top1_connected_on X (subspace_topology (top1_S2-(A\<union>C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>C))) X)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology X =
          subspace_topology (top1_S2-(A\<union>C)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>C))) X"
        using subspace_topology_trans[of X "top1_S2-(A\<union>C)"] hX_sub_AC by (by100 simp)
      thus ?thesis using hX_conn by (by100 simp)
    qed
    from Lemma_23_2[OF hTAC hSep3 hX_sub_AC hX_conn_AC] show ?thesis by (by100 blast)
  qed
  have hB_ne_loc: "B - {a, b} \<noteq> {}"
  proof
    assume "B - {a, b} = {}"
    have "a \<in> closure_on top1_S2 top1_S2_topology (B - {a,b})"
      using arc_endpoint_in_closure_of_interior[OF hS2 hS2_haus hB_sub hB_arc hB_ep hab] by (by100 blast)
    hence "a \<in> closure_on top1_S2 top1_S2_topology {}" using \<open>B - {a,b} = {}\<close> by (by100 simp)
    thus False using top1_closure_on_empty[OF hTopS2] by (by100 simp)
  qed
  have hB_conn_loc: "top1_connected_on (B - {a,b}) (subspace_topology top1_S2 top1_S2_topology (B - {a,b}))"
    by (rule arc_minus_endpoints_connected[OF hS2 hS2_haus hB_sub hB_arc hB_ep hab])
  have hB_in_PQ3: "B - {a, b} \<subseteq> P3 \<or> B - {a, b} \<subseteq> Q3"
  proof -
    have hB_conn_AC: "top1_connected_on (B-{a,b}) (subspace_topology (top1_S2-(A\<union>C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>C))) (B-{a,b}))"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology (B-{a,b}) =
          subspace_topology (top1_S2-(A\<union>C)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>C))) (B-{a,b})"
        using subspace_topology_trans[of "B-{a,b}" "top1_S2-(A\<union>C)"] hB_sub_AC by (by100 simp)
      thus ?thesis using hB_conn_loc by (by100 simp)
    qed
    from Lemma_23_2[OF hTAC hSep3 hB_sub_AC hB_conn_AC] show ?thesis by (by100 blast)
  qed
  \<comment> \<open>If ANY SCC separates X from opposite arc: E-bridges gives False.\<close>
  \<comment> \<open>Check SCC B\<union>C with E1.\<close>
  { assume hdiff2: "(X \<subseteq> P2 \<and> A - {a,b} \<subseteq> Q2) \<or> (X \<subseteq> Q2 \<and> A - {a,b} \<subseteq> P2)"
    have hE1_sub_BC_2: "E1 \<subseteq> top1_S2 - (B \<union> C)" using hE1_sub hE1_disj by (by100 blast)
    have hE1_conn_BC: "top1_connected_on E1 (subspace_topology (top1_S2-(B\<union>C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2-(B\<union>C))) E1)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology E1 =
          subspace_topology (top1_S2-(B\<union>C)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(B\<union>C))) E1"
        using subspace_topology_trans[of E1 "top1_S2-(B\<union>C)"] hE1_sub_BC_2 by (by100 simp)
      thus ?thesis using hE1_conn by (by100 simp)
    qed
    have hE1_disj_PQ: "E1 \<inter> Q2 = {} \<or> E1 \<inter> P2 = {}"
      using Lemma_23_2_disjoint[OF hTBC hSep2 hE1_sub_BC_2 hE1_conn_BC] by (by100 blast)
    from hdiff2 have ?thesis
    proof (elim disjE conjE)
      assume hXP: "X \<subseteq> P2" and hAQ: "A - {a,b} \<subseteq> Q2"
      have "E1 \<inter> P2 \<noteq> {}" using hE1_e hX(2) hXP by (by100 blast)
      have "E1 \<inter> Q2 \<noteq> {}" using hE1_h hAQ by (by100 blast)
      thus False using hE1_disj_PQ \<open>E1 \<inter> P2 \<noteq> {}\<close> by (by100 blast)
    next
      assume hXQ: "X \<subseteq> Q2" and hAP: "A - {a,b} \<subseteq> P2"
      have "E1 \<inter> Q2 \<noteq> {}" using hE1_e hX(2) hXQ by (by100 blast)
      have "E1 \<inter> P2 \<noteq> {}" using hE1_h hAP by (by100 blast)
      thus False using hE1_disj_PQ \<open>E1 \<inter> Q2 \<noteq> {}\<close> by (by100 blast)
    qed
  } note case_BC = this
  { assume hdiff3: "(X \<subseteq> P3 \<and> B - {a,b} \<subseteq> Q3) \<or> (X \<subseteq> Q3 \<and> B - {a,b} \<subseteq> P3)"
    have hE2_sub_AC_2: "E2 \<subseteq> top1_S2 - (A \<union> C)" using hE2_sub hE2_disj by (by100 blast)
    have hE2_conn_AC: "top1_connected_on E2 (subspace_topology (top1_S2-(A\<union>C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>C))) E2)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology E2 =
          subspace_topology (top1_S2-(A\<union>C)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(A\<union>C))) E2"
        using subspace_topology_trans[of E2 "top1_S2-(A\<union>C)"] hE2_sub_AC_2 by (by100 simp)
      thus ?thesis using hE2_conn by (by100 simp)
    qed
    have hE2_disj_PQ: "E2 \<inter> Q3 = {} \<or> E2 \<inter> P3 = {}"
      using Lemma_23_2_disjoint[OF hTAC hSep3 hE2_sub_AC_2 hE2_conn_AC] by (by100 blast)
    from hdiff3 have ?thesis
    proof (elim disjE conjE)
      assume hXP: "X \<subseteq> P3" and hBQ: "B - {a,b} \<subseteq> Q3"
      have "E2 \<inter> P3 \<noteq> {}" using hE2_e hX(2) hXP by (by100 blast)
      have "E2 \<inter> Q3 \<noteq> {}" using hE2_h hBQ by (by100 blast)
      thus False using hE2_disj_PQ \<open>E2 \<inter> P3 \<noteq> {}\<close> by (by100 blast)
    next
      assume hXQ: "X \<subseteq> Q3" and hBP: "B - {a,b} \<subseteq> P3"
      have "E2 \<inter> Q3 \<noteq> {}" using hE2_e hX(2) hXQ by (by100 blast)
      have "E2 \<inter> P3 \<noteq> {}" using hE2_h hBP by (by100 blast)
      thus False using hE2_disj_PQ \<open>E2 \<inter> Q3 \<noteq> {}\<close> by (by100 blast)
    qed
  } note case_AC = this
  \<comment> \<open>If all same side: pigeonhole contradiction (not formalized).\<close>
  show False
  proof (cases "(X \<subseteq> P1 \<and> C-{a,b} \<subseteq> Q1) \<or> (X \<subseteq> Q1 \<and> C-{a,b} \<subseteq> P1)")
    case True thus False by (rule case_AB)
  next
    case AB_same: False
    show False
    proof (cases "(X \<subseteq> P2 \<and> A-{a,b} \<subseteq> Q2) \<or> (X \<subseteq> Q2 \<and> A-{a,b} \<subseteq> P2)")
      case True thus False by (rule case_BC)
    next
      case BC_same: False
      show False
      proof (cases "(X \<subseteq> P3 \<and> B-{a,b} \<subseteq> Q3) \<or> (X \<subseteq> Q3 \<and> B-{a,b} \<subseteq> P3)")
        case True thus False by (rule case_AC)
      next
        case AC_same: False
        \<comment> \<open>ALL 3 SCCs have X on same side as opposite arc.
           From each "same" fact: X and opposite arc on same side \<Rightarrow>
           "Q-side" of that SCC contains only theta components from {Y,Z} (not X).
           Q-side \<noteq> {} \<Rightarrow> at least one of {Y,Z} is on Q-side.
           3 SCCs each choose \<ge>1 from {Y,Z}. SCCBMC + closure gives J\_k1 = J\_k2.\<close>
        \<comment> \<open>Step 1: Determine which side X is on for each SCC.\<close>
        \<comment> \<open>For AB: from AB\_same + hX\_in\_PQ1 + hC\_in\_PQ1, X and C on same side.\<close>
        have hXC_sameP1: "(X \<subseteq> P1 \<and> C-{a,b} \<subseteq> P1) \<or> (X \<subseteq> Q1 \<and> C-{a,b} \<subseteq> Q1)"
          using hX_in_PQ1 hC_in_PQ1 AB_same by blast
        have hXA_sameP2: "(X \<subseteq> P2 \<and> A-{a,b} \<subseteq> P2) \<or> (X \<subseteq> Q2 \<and> A-{a,b} \<subseteq> Q2)"
          using hX_in_PQ2 hA_in_PQ2 BC_same by blast
        have hXB_sameP3: "(X \<subseteq> P3 \<and> B-{a,b} \<subseteq> P3) \<or> (X \<subseteq> Q3 \<and> B-{a,b} \<subseteq> Q3)"
          using hX_in_PQ3 hB_in_PQ3 AC_same by blast
        \<comment> \<open>Step 2: The Q-side (opposite from X) for each SCC contains \<subseteq> {Y,Z}.\<close>
        obtain Y Z where hYZ: "{X, Y, Z} = {U, V, W}" "Y \<noteq> X" "Z \<noteq> X" "Y \<noteq> Z"
            "Y \<in> {U, V, W}" "Z \<in> {U, V, W}"
        proof -
          have hUV_ne: "U \<noteq> V" using hUVW(1) hU(1) by blast
          have hVW_ne: "V \<noteq> W" using hUVW(2) hV(1) by blast
          have hUW_ne: "U \<noteq> W" using hUVW(3) hU(1) by blast
          from hX(1) consider "X = U" | "X = V" | "X = W" by blast
          thus ?thesis
          proof cases
            assume h: "X = U"
            show ?thesis
              apply (rule that[of V W])
              using h hUV_ne hUW_ne hVW_ne by (by100 simp) (by100 blast)+
          next
            assume h: "X = V"
            show ?thesis
              apply (rule that[of U W])
              using h hUV_ne hVW_ne hUW_ne by (by100 simp) (by100 blast)+
          next
            assume h: "X = W"
            show ?thesis
              apply (rule that[of U V])
              using h hUW_ne hVW_ne hUV_ne by (by100 simp) (by100 blast)+
          qed
        qed
        have hY_sub: "Y \<subseteq> top1_S2 - (A \<union> B \<union> C)" using hYZ(5) hU(3) hV(3) hW(3) by (by100 blast)
        have hZ_sub: "Z \<subseteq> top1_S2 - (A \<union> B \<union> C)" using hYZ(6) hU(3) hV(3) hW(3) by (by100 blast)
        have hY_conn: "top1_connected_on Y (subspace_topology top1_S2 top1_S2_topology Y)"
          using hYZ(5) hU(4) hV(4) hW(4) by (by100 blast)
        have hZ_conn: "top1_connected_on Z (subspace_topology top1_S2 top1_S2_topology Z)"
          using hYZ(6) hU(4) hV(4) hW(4) by (by100 blast)
        have hY_ne: "Y \<noteq> {}" using hYZ(5) hU(1) hV(1) hW(1) by (by100 blast)
        have hZ_ne: "Z \<noteq> {}" using hYZ(6) hU(1) hV(1) hW(1) by (by100 blast)
        \<comment> \<open>Y and Z are in the same membership sets as some U/V/W.
           For each SCC, the Q-side = union of theta components in Q.
           Since X is on P-side, Q-side \<subseteq> Y \<union> Z.\<close>
        \<comment> \<open>Step 3: For each SCC, the Q-side has closure including the SCC.
           By SCCBMC: closure(Q\_k) = Q\_k \<union> SCC\_k.
           Two SCCs with same Q-side \<Rightarrow> same closure \<Rightarrow> SCCs equal \<Rightarrow> contradiction.\<close>
        \<comment> \<open>Key: for each SCC, the Q-side \<subseteq> Y \<union> Z (no X, no opposite arc interior).
           Q-side \<noteq> {} since SCC separates S2. So Q-side contains \<ge>1 theta component.
           3 Q-sides, each a non-empty subset of \{Y,Z\}. By pigeonhole: 2 equal.
           Their closures give SCC\_k1 = SCC\_k2 \<Rightarrow> two arcs equal \<Rightarrow> contradiction.\<close>
        \<comment> \<open>For each SCC, the Q-side (opposite from X) = some non-empty subset of \{Y,Z\}.
           closure(Q-side) = Q-side \<union> SCC (from SCCBMC + Q open in S2).
           If 2 SCCs have equal Q-sides: their closures give SCC1 = SCC2 \<Rightarrow> False.
           If all 3 different (\{Y\},\{Z\},\{Y,Z\}): containment gives SCC1 \<subseteq> SCC3 \<Rightarrow> False.\<close>
        \<comment> \<open>Key helper: for an open component Q of S2-SCC, closure(Q) = Q \<union> SCC.\<close>
        have closure_eq: "\<And>SCC Q R.
          top1_simple_closed_curve_on top1_S2 top1_S2_topology SCC \<Longrightarrow>
          Q \<in> top1_S2_topology \<Longrightarrow> R \<in> top1_S2_topology \<Longrightarrow>
          Q \<noteq> {} \<Longrightarrow> R \<noteq> {} \<Longrightarrow> Q \<inter> R = {} \<Longrightarrow> Q \<union> R = top1_S2 - SCC \<Longrightarrow>
          top1_connected_on Q (subspace_topology top1_S2 top1_S2_topology Q) \<Longrightarrow>
          top1_connected_on R (subspace_topology top1_S2 top1_S2_topology R) \<Longrightarrow>
          closure_on top1_S2 top1_S2_topology Q = Q \<union> SCC"
        proof -
          fix SCC Q R
          assume hSCC: "top1_simple_closed_curve_on top1_S2 top1_S2_topology SCC"
            and hQop: "Q \<in> top1_S2_topology" and hRop: "R \<in> top1_S2_topology"
            and hQne: "Q \<noteq> {}" and hRne: "R \<noteq> {}" and hQR: "Q \<inter> R = {}"
            and hQR_un: "Q \<union> R = top1_S2 - SCC"
            and hQc: "top1_connected_on Q (subspace_topology top1_S2 top1_S2_topology Q)"
            and hRc: "top1_connected_on R (subspace_topology top1_S2 top1_S2_topology R)"
          \<comment> \<open>(\<supseteq>): Q \<subseteq> closure(Q) and SCC \<subseteq> closure(Q).\<close>
          have hQ_sub_cl: "Q \<subseteq> closure_on top1_S2 top1_S2_topology Q"
            by (rule subset_closure_on)
          have hSCC_sub_cl: "SCC \<subseteq> closure_on top1_S2 top1_S2_topology Q"
          proof
            fix x assume hx: "x \<in> SCC"
            show "x \<in> closure_on top1_S2 top1_S2_topology Q"
              unfolding closure_on_def
            proof (rule InterI, clarsimp)
              fix C assume hCcl: "closedin_on top1_S2 top1_S2_topology C" and hQC: "Q \<subseteq> C"
              \<comment> \<open>S2 - C is open and \<subseteq> S2 - Q = R \<union> SCC. If x \<notin> C: x \<in> S2-C, open.\<close>
              show "x \<in> C"
              proof (rule ccontr)
                assume "x \<notin> C"
                have hV: "top1_S2 - C \<in> top1_S2_topology"
                  using hCcl unfolding closedin_on_def by (by100 blast)
                have hxV: "x \<in> top1_S2 - C"
                  using \<open>x \<notin> C\<close> hx hSCC
                  unfolding top1_simple_closed_curve_on_def top1_continuous_map_on_def
                  by (by100 blast)
                from simple_closed_curve_boundary_meets_component[OF hS2 hSCC hQc hRc hQR hQR_un
                    hQne hRne hQop hRop hx hV hxV]
                have "(top1_S2 - C) \<inter> Q \<noteq> {}" .
                thus False using hQC by (by100 blast)
              qed
            qed
          qed
          \<comment> \<open>(\<subseteq>): closure(Q) \<subseteq> Q \<union> SCC. Because Q \<union> SCC = S2 - R is closed.\<close>
          have hQSCC_closed: "closedin_on top1_S2 top1_S2_topology (Q \<union> SCC)"
          proof -
            have "top1_S2 - (Q \<union> SCC) = R"
            proof -
              have "Q \<union> SCC \<union> R = top1_S2"
                using hQR_un hSCC
                unfolding top1_simple_closed_curve_on_def top1_continuous_map_on_def
                by (by100 blast)
              thus ?thesis using hQR hQR_un by (by100 blast)
            qed
            moreover have "Q \<union> SCC \<subseteq> top1_S2"
            proof -
              have "Q \<subseteq> top1_S2"
                by (rule is_topology_on_strict_opens_sub[OF hS2 hQop])
              moreover have "SCC \<subseteq> top1_S2"
                using hSCC unfolding top1_simple_closed_curve_on_def top1_continuous_map_on_def
                by (by100 blast)
              ultimately show ?thesis by (by100 blast)
            qed
            ultimately show ?thesis unfolding closedin_on_def using hRop by (by100 blast)
          qed
          have hQ_sub_QSCC: "Q \<subseteq> Q \<union> SCC" by (by100 blast)
          have hcl_sub: "closure_on top1_S2 top1_S2_topology Q \<subseteq> Q \<union> SCC"
            unfolding closure_on_def using hQSCC_closed hQ_sub_QSCC by (by100 blast)
          show "closure_on top1_S2 top1_S2_topology Q = Q \<union> SCC"
            using hQ_sub_cl hSCC_sub_cl hcl_sub by (by100 blast)
        qed
        \<comment> \<open>Distinct SCCs.\<close>
        have hA_ne_int: "A - {a, b} \<noteq> {}"
        proof
          assume "A - {a, b} = {}"
          from arc_endpoint_in_closure_of_interior[OF hS2 hS2_haus hA_sub hA_arc hA_ep hab]
          have "a \<in> closure_on top1_S2 top1_S2_topology (A - {a,b})" by (by100 blast)
          thus False using \<open>A - {a, b} = {}\<close> top1_closure_on_empty[OF hTopS2] by (by100 simp)
        qed
        have hB_ne_int: "B - {a, b} \<noteq> {}"
        proof
          assume "B - {a, b} = {}"
          from arc_endpoint_in_closure_of_interior[OF hS2 hS2_haus hB_sub hB_arc hB_ep hab]
          have "a \<in> closure_on top1_S2 top1_S2_topology (B - {a,b})" by (by100 blast)
          thus False using \<open>B - {a, b} = {}\<close> top1_closure_on_empty[OF hTopS2] by (by100 simp)
        qed
        have hC_ne_int: "C - {a, b} \<noteq> {}"
        proof
          assume "C - {a, b} = {}"
          from arc_endpoint_in_closure_of_interior[OF hS2 hS2_haus hC_sub hC_arc hC_ep hab]
          have "a \<in> closure_on top1_S2 top1_S2_topology (C - {a,b})" by (by100 blast)
          thus False using \<open>C - {a, b} = {}\<close> top1_closure_on_empty[OF hTopS2] by (by100 simp)
        qed
        have hSCCs_ne: "A \<union> B \<noteq> B \<union> C" "B \<union> C \<noteq> A \<union> C" "A \<union> B \<noteq> A \<union> C"
        proof -
          { assume h: "A \<union> B = B \<union> C"
            hence "A - B = C - B" by (by100 blast)
            hence "A - {a, b} = C - {a, b}" using hAB hBC by (by100 blast)
            hence "A - {a, b} \<subseteq> C" by (by100 blast)
            hence "(A - {a, b}) \<inter> C \<noteq> {}" using hA_ne_int by (by100 blast)
            hence False using hAC by (by100 blast) }
          thus "A \<union> B \<noteq> B \<union> C" by blast
          { assume h: "B \<union> C = A \<union> C"
            hence "B - C = A - C" by (by100 blast)
            hence "B - {a, b} = A - {a, b}" using hBC hAC by (by100 blast)
            hence "B - {a, b} \<subseteq> A" by (by100 blast)
            hence "(B - {a, b}) \<inter> A \<noteq> {}" using hB_ne_int by (by100 blast)
            hence False using hAB by (by100 blast) }
          thus "B \<union> C \<noteq> A \<union> C" by blast
          { assume h: "A \<union> B = A \<union> C"
            hence "B - A = C - A" by (by100 blast)
            hence "B - {a, b} = C - {a, b}" using hAB hAC by (by100 blast)
            hence "B - {a, b} \<subseteq> C" by (by100 blast)
            hence "(B - {a, b}) \<inter> C \<noteq> {}" using hB_ne_int by (by100 blast)
            hence False using hBC by (by100 blast) }
          thus "A \<union> B \<noteq> A \<union> C" by blast
        qed
        \<comment> \<open>Y \<inter> Z = {} (theta components pairwise disjoint).\<close>
        have hYZ_disj: "Y \<inter> Z = {}"
        proof -
          from hYZ(5) consider "Y = U" | "Y = V" | "Y = W" by (by100 blast)
          thus ?thesis proof cases
            assume "Y = U"
            from hYZ(6) hYZ(4)[unfolded this] consider "Z = V" | "Z = W" by (by100 blast)
            thus ?thesis proof cases
              assume "Z = V" thus ?thesis using hUVW(1) \<open>Y = U\<close> by (by100 blast)
            next assume "Z = W" thus ?thesis using hUVW(3) \<open>Y = U\<close> by (by100 blast)
            qed
          next
            assume "Y = V"
            from hYZ(6) hYZ(4)[unfolded this] consider "Z = U" | "Z = W" by (by100 blast)
            thus ?thesis proof cases
              assume "Z = U" thus ?thesis using hUVW(1) \<open>Y = V\<close> by (by100 blast)
            next assume "Z = W" thus ?thesis using hUVW(2) \<open>Y = V\<close> by (by100 blast)
            qed
          next
            assume "Y = W"
            from hYZ(6) hYZ(4)[unfolded this] consider "Z = U" | "Z = V" by (by100 blast)
            thus ?thesis proof cases
              assume "Z = U" thus ?thesis using hUVW(3) \<open>Y = W\<close> by (by100 blast)
            next assume "Z = V" thus ?thesis using hUVW(2) \<open>Y = W\<close> by (by100 blast)
            qed
          qed
        qed
        have hYZ_disj_arcs: "(Y \<union> Z) \<inter> (A \<union> B \<union> C) = {}"
          using hY_sub hZ_sub by (by100 blast)
        have hXYZ_eq: "X \<union> Y \<union> Z = U \<union> V \<union> W"
        proof -
          have "\<Union>{X, Y, Z} = \<Union>{U, V, W}" using hYZ(1) by (by100 simp)
          thus ?thesis by (simp add: Un_assoc)
        qed
        \<comment> \<open>Helper: SCC subset impossible.\<close>
        have no_sub: "\<not>(A\<union>B \<subseteq> B\<union>C)" "\<not>(B\<union>C \<subseteq> A\<union>B)" "\<not>(A\<union>B \<subseteq> A\<union>C)"
            "\<not>(A\<union>C \<subseteq> A\<union>B)" "\<not>(B\<union>C \<subseteq> A\<union>C)" "\<not>(A\<union>C \<subseteq> B\<union>C)"
        proof -
          { assume "A\<union>B \<subseteq> B\<union>C"
            hence "A-{a,b} \<subseteq> C" using hAB hBC by (by100 blast)
            hence "(A-{a,b})\<inter>C \<noteq> {}" using hA_ne_int by (by100 blast)
            hence False using hAC by (by100 blast) }
          thus "\<not>(A\<union>B \<subseteq> B\<union>C)" by blast
          { assume "B\<union>C \<subseteq> A\<union>B"
            hence "C-{a,b} \<subseteq> A" using hBC hAB by (by100 blast)
            hence "(C-{a,b})\<inter>A \<noteq> {}" using hC_ne_int by (by100 blast)
            hence False using hAC by (by100 blast) }
          thus "\<not>(B\<union>C \<subseteq> A\<union>B)" by blast
          { assume "A\<union>B \<subseteq> A\<union>C"
            hence "B-{a,b} \<subseteq> C" using hAB hAC by (by100 blast)
            hence "(B-{a,b})\<inter>C \<noteq> {}" using hB_ne_int by (by100 blast)
            hence False using hBC by (by100 blast) }
          thus "\<not>(A\<union>B \<subseteq> A\<union>C)" by blast
          { assume "A\<union>C \<subseteq> A\<union>B"
            hence "C-{a,b} \<subseteq> B" using hAC hAB by (by100 blast)
            hence "(C-{a,b})\<inter>B \<noteq> {}" using hC_ne_int by (by100 blast)
            hence False using hBC by (by100 blast) }
          thus "\<not>(A\<union>C \<subseteq> A\<union>B)" by blast
          { assume "B\<union>C \<subseteq> A\<union>C"
            hence "B-{a,b} \<subseteq> A" using hBC hAC by (by100 blast)
            hence "(B-{a,b})\<inter>A \<noteq> {}" using hB_ne_int by (by100 blast)
            hence False using hAB by (by100 blast) }
          thus "\<not>(B\<union>C \<subseteq> A\<union>C)" by blast
          { assume "A\<union>C \<subseteq> B\<union>C"
            hence "A-{a,b} \<subseteq> B" using hAC hBC by (by100 blast)
            hence "(A-{a,b})\<inter>B \<noteq> {}" using hA_ne_int by (by100 blast)
            hence False using hAB by (by100 blast) }
          thus "\<not>(A\<union>C \<subseteq> B\<union>C)" by blast
        qed
        \<comment> \<open>For each SCC, the Q-side contains Y or Z. Use case analysis.
           Key: from hXC\_sameP1, either both in P1 or both in Q1. The OTHER component
           (not containing X) is the Q-side. It lies in Y\<union>Z and contains at least one of Y,Z.
           For ANY pair of SCCs: closure containment gives SCC\_i \<subseteq> SCC\_j. Contradiction.\<close>
        \<comment> \<open>Approach: case-split on which side Y is on for A\<union>B and B\<union>C. In all cases: contradiction.\<close>
        \<comment> \<open>Proof: for ANY 2 SCCs, the Q-sides (opposite from X) give SCC containment.
           Q-side of A\<union>B: the component not containing X. Q-side \<subseteq> Y\<union>Z.
           closure(Q-side) = Q-side \<union> SCC. So SCC \<subseteq> closure(Q-side).
           If Q-side\_1 \<subseteq> Q-side\_2: SCC\_1 \<subseteq> closure(Q-side\_1) \<subseteq> closure(Q-side\_2)
           = Q-side\_2 \<union> SCC\_2 \<subseteq> (Y\<union>Z) \<union> SCC\_2. Since SCC\_1 \<inter> (Y\<union>Z) = {}:
           SCC\_1 \<subseteq> SCC\_2. Contradiction (no\_sub).\<close>
        \<comment> \<open>The 3 Q-sides are connected non-empty subsets of Y\<union>Z with Y\<inter>Z=\{\}.
           So each Q-side \<subseteq> Y or \<subseteq> Z (connected + Y\<inter>Z=\{\}).
           3 choices from \{Y,Z\}: pigeonhole gives 2 on same side.
           Then their Q-sides are equal (both = Y or both = Z).
           Equal Q-sides + closure\_eq \<Rightarrow> SCC\_1 = SCC\_2. Contradiction.\<close>
        \<comment> \<open>To avoid by100 timeouts: use a compact combined argument.\<close>
        \<comment> \<open>Core claim: \<exists>i\<noteq>j. SCC\_i \<subseteq> SCC\_j. This contradicts no\_sub.\<close>
        \<comment> \<open>Helpers for connected subsets of disjoint open unions.\<close>
        have conn_sub: "\<And>P Q S. P \<in> top1_S2_topology \<Longrightarrow> Q \<in> top1_S2_topology \<Longrightarrow>
            P \<inter> Q = {} \<Longrightarrow> S \<subseteq> P \<union> Q \<Longrightarrow> S \<noteq> {} \<Longrightarrow>
            top1_connected_on S (subspace_topology top1_S2 top1_S2_topology S) \<Longrightarrow> S \<subseteq> P \<or> S \<subseteq> Q"
        proof -
          fix P Q S assume hPop: "P \<in> top1_S2_topology" and hQop: "Q \<in> top1_S2_topology"
            and hPQ: "P \<inter> Q = {}" and hS: "S \<subseteq> P \<union> Q" and hSne: "S \<noteq> {}"
            and hSc: "top1_connected_on S (subspace_topology top1_S2 top1_S2_topology S)"
          show "S \<subseteq> P \<or> S \<subseteq> Q"
          proof (rule ccontr)
            assume "\<not> (S \<subseteq> P \<or> S \<subseteq> Q)"
            hence "S\<inter>P \<noteq> {}" "S\<inter>Q \<noteq> {}" using hS hSne by (by100 blast)+
            moreover have "(S\<inter>P) \<inter> (S\<inter>Q) = {}" using hPQ by (by100 blast)
            moreover have "(S\<inter>P) \<union> (S\<inter>Q) = S" using hS by (by100 blast)
            moreover have "S\<inter>P \<in> subspace_topology top1_S2 top1_S2_topology S"
              using hPop unfolding subspace_topology_def by (by100 blast)
            moreover have "S\<inter>Q \<in> subspace_topology top1_S2 top1_S2_topology S"
              using hQop unfolding subspace_topology_def by (by100 blast)
            ultimately have "\<not> top1_connected_on S (subspace_topology top1_S2 top1_S2_topology S)"
              unfolding top1_connected_on_def by (by100 blast)
            thus False using hSc by (by100 blast)
          qed
        qed
        \<comment> \<open>Y and Z placement in each P/Q decomposition.\<close>
        have hYop: "Y \<in> top1_S2_topology" using hYZ(5) hU(2) hV(2) hW(2) by (by100 blast)
        have hZop: "Z \<in> top1_S2_topology" using hYZ(6) hU(2) hV(2) hW(2) by (by100 blast)
        have hY_PQ1: "Y \<subseteq> P1 \<or> Y \<subseteq> Q1"
          using conn_sub[OF _ _ hPQ1(3) _ hY_ne hY_conn] hPQ1_open hY_sub hPQ1(4) by (by100 blast)
        have hZ_PQ1: "Z \<subseteq> P1 \<or> Z \<subseteq> Q1"
          using conn_sub[OF _ _ hPQ1(3) _ hZ_ne hZ_conn] hPQ1_open hZ_sub hPQ1(4) by (by100 blast)
        have hY_PQ2: "Y \<subseteq> P2 \<or> Y \<subseteq> Q2"
          using conn_sub[OF _ _ hPQ2(3) _ hY_ne hY_conn] hPQ2_open hY_sub hPQ2(4) by (by100 blast)
        have hZ_PQ2: "Z \<subseteq> P2 \<or> Z \<subseteq> Q2"
          using conn_sub[OF _ _ hPQ2(3) _ hZ_ne hZ_conn] hPQ2_open hZ_sub hPQ2(4) by (by100 blast)
        have hY_PQ3: "Y \<subseteq> P3 \<or> Y \<subseteq> Q3"
          using conn_sub[OF _ _ hPQ3(3) _ hY_ne hY_conn] hPQ3_open hY_sub hPQ3(4) by (by100 blast)
        have hZ_PQ3: "Z \<subseteq> P3 \<or> Z \<subseteq> Q3"
          using conn_sub[OF _ _ hPQ3(3) _ hZ_ne hZ_conn] hPQ3_open hZ_sub hPQ3(4) by (by100 blast)
        \<comment> \<open>For each SCC, X and opposite arc on same side \<Rightarrow> Q-side is a connected component \<subseteq> Y\<union>Z.
           The Q-side IS either Y or Z (not Y\<union>Z, since it's connected and Y\<inter>Z={}).
           By pigeonhole: 2 of 3 SCCs have Q-side = same theta component.
           Then closure gives SCC1 = SCC2. Contradiction.\<close>
        \<comment> \<open>Helper: connected \<subseteq> Y\<union>Z \<Rightarrow> \<subseteq> Y or \<subseteq> Z.\<close>
        have hYop: "Y \<in> top1_S2_topology" using hYZ(5) hU(2) hV(2) hW(2) by (by100 blast)
        have hZop: "Z \<in> top1_S2_topology" using hYZ(6) hU(2) hV(2) hW(2) by (by100 blast)
        have csYZ: "\<And>S. S \<subseteq> Y\<union>Z \<Longrightarrow> S \<noteq> {} \<Longrightarrow>
            top1_connected_on S (subspace_topology top1_S2 top1_S2_topology S) \<Longrightarrow> S \<subseteq> Y \<or> S \<subseteq> Z"
          by (rule conn_sub[OF hYop hZop hYZ_disj])
        \<comment> \<open>For each SCC, get Q-side \<subseteq> Y or Z. Approach: case-split on same-side,
           show other side \<subseteq> Y\<union>Z (everything except X and arc\_int is in Y\<union>Z),
           then apply csYZ.\<close>
        \<comment> \<open>Decomp: S2-(A\<union>B) \<subseteq> X\<union>Y\<union>Z\<union>(C-{a,b}).\<close>
        have dAB: "top1_S2-(A\<union>B) \<subseteq> X\<union>Y\<union>Z\<union>(C-{a,b})"
        proof
          fix x assume "x \<in> top1_S2-(A\<union>B)"
          hence "x \<in> top1_S2" "x \<notin> A" "x \<notin> B" by (by100 blast)+
          thus "x \<in> X\<union>Y\<union>Z\<union>(C-{a,b})"
            using hUVW(4) hXYZ_eq hAC hBC by (cases "x \<in> C") (by100 blast)+
        qed
        have dBC: "top1_S2-(B\<union>C) \<subseteq> X\<union>Y\<union>Z\<union>(A-{a,b})"
        proof
          fix x assume "x \<in> top1_S2-(B\<union>C)"
          hence "x \<in> top1_S2" "x \<notin> B" "x \<notin> C" by (by100 blast)+
          thus "x \<in> X\<union>Y\<union>Z\<union>(A-{a,b})"
            using hUVW(4) hXYZ_eq hAB hAC by (cases "x \<in> A") (by100 blast)+
        qed
        have dAC: "top1_S2-(A\<union>C) \<subseteq> X\<union>Y\<union>Z\<union>(B-{a,b})"
        proof
          fix x assume "x \<in> top1_S2-(A\<union>C)"
          hence "x \<in> top1_S2" "x \<notin> A" "x \<notin> C" by (by100 blast)+
          thus "x \<in> X\<union>Y\<union>Z\<union>(B-{a,b})"
            using hUVW(4) hXYZ_eq hAB hBC by (cases "x \<in> B") (by100 blast)+
        qed
        \<comment> \<open>For SCC A\<union>B: get Opp1 \<in> {P1,Q1} with Opp1 \<subseteq> Y or Z.\<close>
        obtain Opp1 where hO1: "Opp1 \<in> {P1,Q1}" "Opp1 \<subseteq> Y \<or> Opp1 \<subseteq> Z"
        proof -
          from hXC_sameP1 consider
            (a) "X \<subseteq> P1" "C-{a,b} \<subseteq> P1" | (b) "X \<subseteq> Q1" "C-{a,b} \<subseteq> Q1" by (by100 blast)
          thus ?thesis
          proof cases
            case a
            have "Q1 \<subseteq> Y\<union>Z" using hPQ1(4) dAB a hPQ1(3) by (by100 blast)
            hence "Q1 \<subseteq> Y \<or> Q1 \<subseteq> Z" by (rule csYZ[OF _ hPQ1(2) hPQ1(6)])
            thus ?thesis using that by (by100 blast)
          next
            case b
            have "P1 \<subseteq> Y\<union>Z" using hPQ1(4) dAB b hPQ1(3) by (by100 blast)
            hence "P1 \<subseteq> Y \<or> P1 \<subseteq> Z" by (rule csYZ[OF _ hPQ1(1) hPQ1(5)])
            thus ?thesis using that by (by100 blast)
          qed
        qed
        obtain Opp2 where hO2: "Opp2 \<in> {P2,Q2}" "Opp2 \<subseteq> Y \<or> Opp2 \<subseteq> Z"
        proof -
          from hXA_sameP2 consider
            (a) "X \<subseteq> P2" "A-{a,b} \<subseteq> P2" | (b) "X \<subseteq> Q2" "A-{a,b} \<subseteq> Q2" by (by100 blast)
          thus ?thesis
          proof cases
            case a
            have "Q2 \<subseteq> Y\<union>Z" using hPQ2(4) dBC a hPQ2(3) by (by100 blast)
            hence "Q2 \<subseteq> Y \<or> Q2 \<subseteq> Z" by (rule csYZ[OF _ hPQ2(2) hPQ2(6)])
            thus ?thesis using that by (by100 blast)
          next
            case b
            have "P2 \<subseteq> Y\<union>Z" using hPQ2(4) dBC b hPQ2(3) by (by100 blast)
            hence "P2 \<subseteq> Y \<or> P2 \<subseteq> Z" by (rule csYZ[OF _ hPQ2(1) hPQ2(5)])
            thus ?thesis using that by (by100 blast)
          qed
        qed
        obtain Opp3 where hO3: "Opp3 \<in> {P3,Q3}" "Opp3 \<subseteq> Y \<or> Opp3 \<subseteq> Z"
        proof -
          from hXB_sameP3 consider
            (a) "X \<subseteq> P3" "B-{a,b} \<subseteq> P3" | (b) "X \<subseteq> Q3" "B-{a,b} \<subseteq> Q3" by (by100 blast)
          thus ?thesis
          proof cases
            case a
            have "Q3 \<subseteq> Y\<union>Z" using hPQ3(4) dAC a hPQ3(3) by (by100 blast)
            hence "Q3 \<subseteq> Y \<or> Q3 \<subseteq> Z" by (rule csYZ[OF _ hPQ3(2) hPQ3(6)])
            thus ?thesis using that by (by100 blast)
          next
            case b
            have "P3 \<subseteq> Y\<union>Z" using hPQ3(4) dAC b hPQ3(3) by (by100 blast)
            hence "P3 \<subseteq> Y \<or> P3 \<subseteq> Z" by (rule csYZ[OF _ hPQ3(1) hPQ3(5)])
            thus ?thesis using that by (by100 blast)
          qed
        qed
        \<comment> \<open>Opp \<in> {P,Q}, Opp \<subseteq> Y, Y \<subseteq> P or Q, P\<inter>Q={} \<Rightarrow> Opp = Y.\<close>
        \<comment> \<open>Helper: O \<in> {P,Q}, O \<subseteq> T, T \<subseteq> P or Q, P\<inter>Q={}, T\<noteq>{} \<Rightarrow> O = T.\<close>
        \<comment> \<open>Opp \<in> {P,Q}, Opp \<subseteq> T, T \<subseteq> P or Q, P\<inter>Q={}, T\<noteq>{} \<Rightarrow> T \<subseteq> Opp (hence Opp = T).\<close>
        have o1Y: "Opp1 \<subseteq> Y \<Longrightarrow> Opp1 = Y"
        proof -
          assume h: "Opp1 \<subseteq> Y"
          from hO1(1) consider "Opp1 = P1" | "Opp1 = Q1" by (by100 blast)
          thus "Opp1 = Y" proof cases
            assume hOP: "Opp1 = P1" from hY_PQ1 show ?thesis
            proof assume "Y \<subseteq> P1" thus ?thesis using h hOP by (by100 blast)
            next assume "Y \<subseteq> Q1"
              hence "P1 \<subseteq> Q1" using h hOP by (by100 blast)
              hence "P1 = {}" using hPQ1(3) by (by100 blast)
              thus ?thesis using hPQ1(1) by (by100 blast)
            qed
          next
            assume hOQ: "Opp1 = Q1" from hY_PQ1 show ?thesis
            proof assume "Y \<subseteq> Q1" thus ?thesis using h hOQ by (by100 blast)
            next assume "Y \<subseteq> P1"
              hence "Q1 \<subseteq> P1" using h hOQ by (by100 blast)
              hence "Q1 = {}" using hPQ1(3) by (by100 blast)
              thus ?thesis using hPQ1(2) by (by100 blast)
            qed
          qed
        qed
        have o1Z: "Opp1 \<subseteq> Z \<Longrightarrow> Opp1 = Z"
        proof -
          assume h: "Opp1 \<subseteq> Z"
          from hO1(1) consider "Opp1 = P1" | "Opp1 = Q1" by (by100 blast)
          thus "Opp1 = Z" proof cases
            assume "Opp1 = P1" from hZ_PQ1 show ?thesis
            proof assume "Z \<subseteq> P1" thus ?thesis using h \<open>Opp1=P1\<close> by (by100 blast)
            next assume "Z \<subseteq> Q1"
              hence "P1 \<subseteq> Q1" using h \<open>Opp1=P1\<close> by (by100 blast)
              hence "P1 = {}" using hPQ1(3) by (by100 blast)
              thus ?thesis using hPQ1(1) by (by100 blast)
            qed
          next
            assume "Opp1 = Q1" from hZ_PQ1 show ?thesis
            proof assume "Z \<subseteq> Q1" thus ?thesis using h \<open>Opp1=Q1\<close> by (by100 blast)
            next assume "Z \<subseteq> P1" hence "Q1 \<subseteq> P1" using h \<open>Opp1=Q1\<close> by (by100 blast)
              hence "Q1 = {}" using hPQ1(3) by (by100 blast)
              thus ?thesis using hPQ1(2) by (by100 blast)
            qed
          qed
        qed
        have o2Y: "Opp2 \<subseteq> Y \<Longrightarrow> Opp2 = Y"
        proof -
          assume h: "Opp2 \<subseteq> Y"
          from hO2(1) consider "Opp2=P2"|"Opp2=Q2" by (by100 blast)
          thus ?thesis proof cases
            assume "Opp2=P2" from hY_PQ2 show ?thesis
            proof assume "Y\<subseteq>P2" thus ?thesis using h \<open>Opp2=P2\<close> by (by100 blast)
            next assume "Y\<subseteq>Q2"
              hence "P2 \<subseteq> Q2" using h \<open>Opp2=P2\<close> by (by100 blast)
              hence "P2 = {}" using hPQ2(3) by (by100 blast)
              thus ?thesis using hPQ2(1) by (by100 blast) qed
          next
            assume "Opp2=Q2" from hY_PQ2 show ?thesis
            proof assume "Y\<subseteq>Q2" thus ?thesis using h \<open>Opp2=Q2\<close> by (by100 blast)
            next assume "Y\<subseteq>P2"
              hence "Q2 \<subseteq> P2" using h \<open>Opp2=Q2\<close> by (by100 blast)
              hence "Q2 = {}" using hPQ2(3) by (by100 blast)
              thus ?thesis using hPQ2(2) by (by100 blast) qed
          qed
        qed
        have o2Z: "Opp2 \<subseteq> Z \<Longrightarrow> Opp2 = Z"
        proof -
          assume h: "Opp2 \<subseteq> Z"
          from hO2(1) consider "Opp2=P2"|"Opp2=Q2" by (by100 blast)
          thus ?thesis proof cases
            assume "Opp2=P2" from hZ_PQ2 show ?thesis
            proof assume "Z\<subseteq>P2" thus ?thesis using h \<open>Opp2=P2\<close> by (by100 blast)
            next assume "Z\<subseteq>Q2"
              hence "P2 \<subseteq> Q2" using h \<open>Opp2=P2\<close> by (by100 blast)
              hence "P2 = {}" using hPQ2(3) by (by100 blast)
              thus ?thesis using hPQ2(1) by (by100 blast) qed
          next
            assume "Opp2=Q2" from hZ_PQ2 show ?thesis
            proof assume "Z\<subseteq>Q2" thus ?thesis using h \<open>Opp2=Q2\<close> by (by100 blast)
            next assume "Z\<subseteq>P2"
              hence "Q2 \<subseteq> P2" using h \<open>Opp2=Q2\<close> by (by100 blast)
              hence "Q2 = {}" using hPQ2(3) by (by100 blast)
              thus ?thesis using hPQ2(2) by (by100 blast) qed
          qed
        qed
        have o3Y: "Opp3 \<subseteq> Y \<Longrightarrow> Opp3 = Y"
        proof -
          assume h: "Opp3 \<subseteq> Y"
          from hO3(1) consider "Opp3=P3"|"Opp3=Q3" by (by100 blast)
          thus ?thesis proof cases
            assume "Opp3=P3" from hY_PQ3 show ?thesis
            proof assume "Y\<subseteq>P3" thus ?thesis using h \<open>Opp3=P3\<close> by (by100 blast)
            next assume "Y\<subseteq>Q3"
              hence "P3 \<subseteq> Q3" using h \<open>Opp3=P3\<close> by (by100 blast)
              hence "P3 = {}" using hPQ3(3) by (by100 blast)
              thus ?thesis using hPQ3(1) by (by100 blast) qed
          next
            assume "Opp3=Q3" from hY_PQ3 show ?thesis
            proof assume "Y\<subseteq>Q3" thus ?thesis using h \<open>Opp3=Q3\<close> by (by100 blast)
            next assume "Y\<subseteq>P3"
              hence "Q3 \<subseteq> P3" using h \<open>Opp3=Q3\<close> by (by100 blast)
              hence "Q3 = {}" using hPQ3(3) by (by100 blast)
              thus ?thesis using hPQ3(2) by (by100 blast) qed
          qed
        qed
        have o3Z: "Opp3 \<subseteq> Z \<Longrightarrow> Opp3 = Z"
        proof -
          assume h: "Opp3 \<subseteq> Z"
          from hO3(1) consider "Opp3=P3"|"Opp3=Q3" by (by100 blast)
          thus ?thesis proof cases
            assume "Opp3=P3" from hZ_PQ3 show ?thesis
            proof assume "Z\<subseteq>P3" thus ?thesis using h \<open>Opp3=P3\<close> by (by100 blast)
            next assume "Z\<subseteq>Q3"
              hence "P3 \<subseteq> Q3" using h \<open>Opp3=P3\<close> by (by100 blast)
              hence "P3 = {}" using hPQ3(3) by (by100 blast)
              thus ?thesis using hPQ3(1) by (by100 blast) qed
          next
            assume "Opp3=Q3" from hZ_PQ3 show ?thesis
            proof assume "Z\<subseteq>Q3" thus ?thesis using h \<open>Opp3=Q3\<close> by (by100 blast)
            next assume "Z\<subseteq>P3"
              hence "Q3 \<subseteq> P3" using h \<open>Opp3=Q3\<close> by (by100 blast)
              hence "Q3 = {}" using hPQ3(3) by (by100 blast)
              thus ?thesis using hPQ3(2) by (by100 blast) qed
          qed
        qed
        \<comment> \<open>Closure of each Opp.\<close>
        have one: "Opp1 \<noteq> {}" using hO1(2) o1Y o1Z hY_ne hZ_ne by (by100 blast)
        have cl1: "closure_on top1_S2 top1_S2_topology Opp1 = Opp1 \<union> (A\<union>B)"
        proof -
          from hO1(1) consider (p) "Opp1 = P1" | (q) "Opp1 = Q1" by (by100 blast)
          thus ?thesis
          proof cases
            case p
            have h4: "Opp1 \<in> top1_S2_topology" using p hPQ1_open by (by100 blast)
            have h3: "Q1 \<in> top1_S2_topology" using hPQ1_open by (by100 blast)
            have h1: "Opp1 \<inter> Q1 = {}" using p hPQ1(3) by (by100 blast)
            have h2: "Opp1 \<union> Q1 = top1_S2-(A\<union>B)" using p hPQ1(4) by (by100 blast)
            have h6: "top1_connected_on Opp1 (subspace_topology top1_S2 top1_S2_topology Opp1)"
              using p hPQ1(5) by (by100 blast)
            show ?thesis by (rule closure_eq[OF hAB_scc h4 h3 one hPQ1(2) h1 h2 h6 hPQ1(6)])
          next
            case q
            have h4: "Opp1 \<in> top1_S2_topology" using q hPQ1_open by (by100 blast)
            have h3: "P1 \<in> top1_S2_topology" using hPQ1_open by (by100 blast)
            have h1: "Opp1 \<inter> P1 = {}" using q hPQ1(3) by (by100 blast)
            have h2: "Opp1 \<union> P1 = top1_S2-(A\<union>B)" using q hPQ1(4) by (by100 blast)
            have h6: "top1_connected_on Opp1 (subspace_topology top1_S2 top1_S2_topology Opp1)"
              using q hPQ1(6) by (by100 blast)
            show ?thesis by (rule closure_eq[OF hAB_scc h4 h3 one hPQ1(1) h1 h2 h6 hPQ1(5)])
          qed
        qed
        have two: "Opp2 \<noteq> {}" using hO2(2) o2Y o2Z hY_ne hZ_ne by (by100 blast)
        have cl2: "closure_on top1_S2 top1_S2_topology Opp2 = Opp2 \<union> (B\<union>C)"
        proof -
          from hO2(1) consider (p) "Opp2 = P2" | (q) "Opp2 = Q2" by (by100 blast)
          thus ?thesis
          proof cases
            case p
            have h4: "Opp2 \<in> top1_S2_topology" using p hPQ2_open by (by100 blast)
            have h3: "Q2 \<in> top1_S2_topology" using hPQ2_open by (by100 blast)
            have h1: "Opp2 \<inter> Q2 = {}" using p hPQ2(3) by (by100 blast)
            have h2: "Opp2 \<union> Q2 = top1_S2-(B\<union>C)" using p hPQ2(4) by (by100 blast)
            have h6: "top1_connected_on Opp2 (subspace_topology top1_S2 top1_S2_topology Opp2)"
              using p hPQ2(5) by (by100 blast)
            show ?thesis by (rule closure_eq[OF hBC_scc h4 h3 two hPQ2(2) h1 h2 h6 hPQ2(6)])
          next
            case q
            have h4: "Opp2 \<in> top1_S2_topology" using q hPQ2_open by (by100 blast)
            have h3: "P2 \<in> top1_S2_topology" using hPQ2_open by (by100 blast)
            have h1: "Opp2 \<inter> P2 = {}" using q hPQ2(3) by (by100 blast)
            have h2: "Opp2 \<union> P2 = top1_S2-(B\<union>C)" using q hPQ2(4) by (by100 blast)
            have h6: "top1_connected_on Opp2 (subspace_topology top1_S2 top1_S2_topology Opp2)"
              using q hPQ2(6) by (by100 blast)
            show ?thesis by (rule closure_eq[OF hBC_scc h4 h3 two hPQ2(1) h1 h2 h6 hPQ2(5)])
          qed
        qed
        have three: "Opp3 \<noteq> {}" using hO3(2) o3Y o3Z hY_ne hZ_ne by (by100 blast)
        have cl3: "closure_on top1_S2 top1_S2_topology Opp3 = Opp3 \<union> (A\<union>C)"
        proof -
          from hO3(1) consider (p) "Opp3 = P3" | (q) "Opp3 = Q3" by (by100 blast)
          thus ?thesis
          proof cases
            case p
            have h4: "Opp3 \<in> top1_S2_topology" using p hPQ3_open by (by100 blast)
            have h3: "Q3 \<in> top1_S2_topology" using hPQ3_open by (by100 blast)
            have h1: "Opp3 \<inter> Q3 = {}" using p hPQ3(3) by (by100 blast)
            have h2: "Opp3 \<union> Q3 = top1_S2-(A\<union>C)" using p hPQ3(4) by (by100 blast)
            have h6: "top1_connected_on Opp3 (subspace_topology top1_S2 top1_S2_topology Opp3)"
              using p hPQ3(5) by (by100 blast)
            show ?thesis by (rule closure_eq[OF hAC_scc h4 h3 three hPQ3(2) h1 h2 h6 hPQ3(6)])
          next
            case q
            have h4: "Opp3 \<in> top1_S2_topology" using q hPQ3_open by (by100 blast)
            have h3: "P3 \<in> top1_S2_topology" using hPQ3_open by (by100 blast)
            have h1: "Opp3 \<inter> P3 = {}" using q hPQ3(3) by (by100 blast)
            have h2: "Opp3 \<union> P3 = top1_S2-(A\<union>C)" using q hPQ3(4) by (by100 blast)
            have h6: "top1_connected_on Opp3 (subspace_topology top1_S2 top1_S2_topology Opp3)"
              using q hPQ3(6) by (by100 blast)
            show ?thesis by (rule closure_eq[OF hAC_scc h4 h3 three hPQ3(1) h1 h2 h6 hPQ3(5)])
          qed
        qed
        \<comment> \<open>Pigeonhole: Opp1,Opp2,Opp3 each = Y or Z. 3 from {Y,Z}: 2 match.\<close>
        have darcs: "(Y\<union>Z) \<inter> (A\<union>B\<union>C) = {}" using hY_sub hZ_sub by (by100 blast)
        from hO1(2) show False
        proof (elim disjE)
          assume "Opp1 \<subseteq> Y" hence e1: "Opp1 = Y" by (rule o1Y)
          from hO2(2) show False
          proof (elim disjE)
            assume "Opp2 \<subseteq> Y" hence "Opp2 = Y" by (rule o2Y)
            hence "Y\<union>(A\<union>B) = Y\<union>(B\<union>C)" using cl1 cl2 e1 by (by100 simp)
            hence "A\<union>B = B\<union>C" using darcs by (by100 blast)
            thus False using hSCCs_ne(1) by (by100 blast)
          next
            assume "Opp2 \<subseteq> Z" hence e2: "Opp2 = Z" by (rule o2Z)
            from hO3(2) show False
            proof (elim disjE)
              assume "Opp3 \<subseteq> Y" hence "Opp3 = Y" by (rule o3Y)
              hence "Y\<union>(A\<union>B) = Y\<union>(A\<union>C)" using cl1 cl3 e1 by (by100 simp)
              hence "A\<union>B = A\<union>C" using darcs by (by100 blast)
              thus False using hSCCs_ne(3) by (by100 blast)
            next
              assume "Opp3 \<subseteq> Z" hence "Opp3 = Z" by (rule o3Z)
              hence "Z\<union>(B\<union>C) = Z\<union>(A\<union>C)" using cl2 cl3 e2 by (by100 simp)
              hence "B\<union>C = A\<union>C" using darcs by (by100 blast)
              thus False using hSCCs_ne(2) by (by100 blast)
            qed
          qed
        next
          assume "Opp1 \<subseteq> Z" hence e1: "Opp1 = Z" by (rule o1Z)
          from hO2(2) show False
          proof (elim disjE)
            assume "Opp2 \<subseteq> Z" hence "Opp2 = Z" by (rule o2Z)
            hence "Z\<union>(A\<union>B) = Z\<union>(B\<union>C)" using cl1 cl2 e1 by (by100 simp)
            hence "A\<union>B = B\<union>C" using darcs by (by100 blast)
            thus False using hSCCs_ne(1) by (by100 blast)
          next
            assume "Opp2 \<subseteq> Y" hence e2: "Opp2 = Y" by (rule o2Y)
            from hO3(2) show False
            proof (elim disjE)
              assume "Opp3 \<subseteq> Z" hence "Opp3 = Z" by (rule o3Z)
              hence "Z\<union>(A\<union>B) = Z\<union>(A\<union>C)" using cl1 cl3 e1 by (by100 simp)
              hence "A\<union>B = A\<union>C" using darcs by (by100 blast)
              thus False using hSCCs_ne(3) by (by100 blast)
            next
              assume "Opp3 \<subseteq> Y" hence "Opp3 = Y" by (rule o3Y)
              hence "Y\<union>(B\<union>C) = Y\<union>(A\<union>C)" using cl2 cl3 e2 by (by100 simp)
              hence "B\<union>C = A\<union>C" using darcs by (by100 blast)
              thus False using hSCCs_ne(2) by (by100 blast)
            qed
          qed
        qed
      qed
    qed
  qed
qed

text \<open>Theorem 64.2: The utilities graph K33 cannot be imbedded in the plane.\<close>

text \<open>Theorem 64.2 and 64.4 (K\_3\_3 and K\_5 not planar) are consequences
  of the theta space lemma. Their formal statements require specifying all
  edge-vertex incidence and intersection conditions. We state simplified versions.\<close>

theorem Theorem_64_2_K33_not_planar:
  \<comment> \<open>The utilities graph K33 cannot be imbedded in the plane (or S2).
     Vertices: g, w, e (utilities) and h1, h2, h3 (houses).
     9 arcs: each utility connected to each house.\<close>
  fixes g w e h1 h2 h3 :: "real \<times> real \<times> real"
    and gh1 gh2 gh3 wh1 wh2 wh3 eh1 eh2 eh3 :: "(real \<times> real \<times> real) set"
  assumes hS2: "is_topology_on_strict top1_S2 top1_S2_topology"
      and hcard: "card {g, w, e, h1, h2, h3} = (6::nat)"
      and hsub: "{g, w, e, h1, h2, h3} \<subseteq> top1_S2"
      \<comment> \<open>All 9 arcs are subsets of S2 and are arcs.\<close>
      and "gh1 \<subseteq> top1_S2" "gh2 \<subseteq> top1_S2" "gh3 \<subseteq> top1_S2"
      and "wh1 \<subseteq> top1_S2" "wh2 \<subseteq> top1_S2" "wh3 \<subseteq> top1_S2"
      and "eh1 \<subseteq> top1_S2" "eh2 \<subseteq> top1_S2" "eh3 \<subseteq> top1_S2"
      and "top1_is_arc_on gh1 (subspace_topology top1_S2 top1_S2_topology gh1)"
      and "top1_is_arc_on gh2 (subspace_topology top1_S2 top1_S2_topology gh2)"
      and "top1_is_arc_on gh3 (subspace_topology top1_S2 top1_S2_topology gh3)"
      and "top1_is_arc_on wh1 (subspace_topology top1_S2 top1_S2_topology wh1)"
      and "top1_is_arc_on wh2 (subspace_topology top1_S2 top1_S2_topology wh2)"
      and "top1_is_arc_on wh3 (subspace_topology top1_S2 top1_S2_topology wh3)"
      and "top1_is_arc_on eh1 (subspace_topology top1_S2 top1_S2_topology eh1)"
      and "top1_is_arc_on eh2 (subspace_topology top1_S2 top1_S2_topology eh2)"
      and "top1_is_arc_on eh3 (subspace_topology top1_S2 top1_S2_topology eh3)"
      \<comment> \<open>Endpoints.\<close>
      and "top1_arc_endpoints_on gh1 (subspace_topology top1_S2 top1_S2_topology gh1) = {g, h1}"
      and "top1_arc_endpoints_on gh2 (subspace_topology top1_S2 top1_S2_topology gh2) = {g, h2}"
      and "top1_arc_endpoints_on gh3 (subspace_topology top1_S2 top1_S2_topology gh3) = {g, h3}"
      and "top1_arc_endpoints_on wh1 (subspace_topology top1_S2 top1_S2_topology wh1) = {w, h1}"
      and "top1_arc_endpoints_on wh2 (subspace_topology top1_S2 top1_S2_topology wh2) = {w, h2}"
      and "top1_arc_endpoints_on wh3 (subspace_topology top1_S2 top1_S2_topology wh3) = {w, h3}"
      and "top1_arc_endpoints_on eh1 (subspace_topology top1_S2 top1_S2_topology eh1) = {e, h1}"
      and "top1_arc_endpoints_on eh2 (subspace_topology top1_S2 top1_S2_topology eh2) = {e, h2}"
      and "top1_arc_endpoints_on eh3 (subspace_topology top1_S2 top1_S2_topology eh3) = {e, h3}"
      \<comment> \<open>Planarity: arcs only intersect at shared vertices.\<close>
      and "gh1 \<inter> gh2 = {g}" "gh1 \<inter> gh3 = {g}" "gh2 \<inter> gh3 = {g}"
      and "wh1 \<inter> wh2 = {w}" "wh1 \<inter> wh3 = {w}" "wh2 \<inter> wh3 = {w}"
      and "eh1 \<inter> eh2 = {e}" "eh1 \<inter> eh3 = {e}" "eh2 \<inter> eh3 = {e}"
      and "gh1 \<inter> wh1 = {h1}" "gh2 \<inter> wh2 = {h2}" "gh3 \<inter> wh3 = {h3}"
      and "gh1 \<inter> wh2 = {}" "gh1 \<inter> wh3 = {}" "gh2 \<inter> wh1 = {}"
      and "gh2 \<inter> wh3 = {}" "gh3 \<inter> wh1 = {}" "gh3 \<inter> wh2 = {}"
      and "gh1 \<inter> eh1 = {h1}" "gh2 \<inter> eh2 = {h2}" "gh3 \<inter> eh3 = {h3}"
      and "gh1 \<inter> eh2 = {}" "gh1 \<inter> eh3 = {}" "gh2 \<inter> eh1 = {}"
      and "gh2 \<inter> eh3 = {}" "gh3 \<inter> eh1 = {}" "gh3 \<inter> eh2 = {}"
      and "wh1 \<inter> eh1 = {h1}" "wh2 \<inter> eh2 = {h2}" "wh3 \<inter> eh3 = {h3}"
      and "wh1 \<inter> eh2 = {}" "wh1 \<inter> eh3 = {}" "wh2 \<inter> eh1 = {}"
      and "wh2 \<inter> eh3 = {}" "wh3 \<inter> eh1 = {}" "wh3 \<inter> eh2 = {}"
  shows False
proof -
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using hS2 unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>Form theta space: 3 arcs A = gh1\<union>wh1, B = gh2\<union>wh2, C = gh3\<union>wh3, all from g to w.\<close>
  \<comment> \<open>Each is an arc via arcs\_concatenation\_is\_arc.\<close>
  define A where "A = gh1 \<union> wh1"
  define B where "B = gh2 \<union> wh2"
  define CC where "CC = gh3 \<union> wh3"
  \<comment> \<open>Step 1: A, B, CC are arcs with endpoints {g, w}.\<close>
  have hh1_gh1: "h1 \<in> top1_arc_endpoints_on gh1 (subspace_topology top1_S2 top1_S2_topology gh1)"
    using assms(22) by (by100 blast)
  have hh1_wh1: "h1 \<in> top1_arc_endpoints_on wh1 (subspace_topology top1_S2 top1_S2_topology wh1)"
    using assms(25) by (by100 blast)
  have hh2_gh2: "h2 \<in> top1_arc_endpoints_on gh2 (subspace_topology top1_S2 top1_S2_topology gh2)"
    using assms(23) by (by100 blast)
  have hh2_wh2: "h2 \<in> top1_arc_endpoints_on wh2 (subspace_topology top1_S2 top1_S2_topology wh2)"
    using assms(26) by (by100 blast)
  have hh3_gh3: "h3 \<in> top1_arc_endpoints_on gh3 (subspace_topology top1_S2 top1_S2_topology gh3)"
    using assms(24) by (by100 blast)
  have hh3_wh3: "h3 \<in> top1_arc_endpoints_on wh3 (subspace_topology top1_S2 top1_S2_topology wh3)"
    using assms(27) by (by100 blast)
  have hA_arc: "top1_is_arc_on A (subspace_topology top1_S2 top1_S2_topology A)"
    unfolding A_def
    by (rule arcs_concatenation_is_arc[OF hS2 hS2_haus assms(13,4,16,7) assms(40) hh1_gh1 hh1_wh1])
  have hB_arc: "top1_is_arc_on B (subspace_topology top1_S2 top1_S2_topology B)"
    unfolding B_def
    by (rule arcs_concatenation_is_arc[OF hS2 hS2_haus assms(14,5,17,8) assms(41) hh2_gh2 hh2_wh2])
  have hCC_arc: "top1_is_arc_on CC (subspace_topology top1_S2 top1_S2_topology CC)"
    unfolding CC_def
    by (rule arcs_concatenation_is_arc[OF hS2 hS2_haus assms(15,6,18,9) assms(42) hh3_gh3 hh3_wh3])
  have hA_sub: "A \<subseteq> top1_S2" unfolding A_def using assms(4,7) by (by100 blast)
  have hB_sub: "B \<subseteq> top1_S2" unfolding B_def using assms(5,8) by (by100 blast)
  have hCC_sub: "CC \<subseteq> top1_S2" unfolding CC_def using assms(6,9) by (by100 blast)
  have hg_ne_h1: "g \<noteq> h1" using hcard by (auto simp: card_insert_if split: if_splits)
  have hh1_ne_w: "h1 \<noteq> w" using hcard by (auto simp: card_insert_if split: if_splits)
  have hg_ne_h2: "g \<noteq> h2" using hcard by (auto simp: card_insert_if split: if_splits)
  have hh2_ne_w: "h2 \<noteq> w" using hcard by (auto simp: card_insert_if split: if_splits)
  have hg_ne_h3: "g \<noteq> h3" using hcard by (auto simp: card_insert_if split: if_splits)
  have hh3_ne_w: "h3 \<noteq> w" using hcard by (auto simp: card_insert_if split: if_splits)
  have hep_wh1_swap: "top1_arc_endpoints_on wh1 (subspace_topology top1_S2 top1_S2_topology wh1) = {h1, w}"
    using assms(25) by (by100 blast)
  have hep_wh2_swap: "top1_arc_endpoints_on wh2 (subspace_topology top1_S2 top1_S2_topology wh2) = {h2, w}"
    using assms(26) by (by100 blast)
  have hep_wh3_swap: "top1_arc_endpoints_on wh3 (subspace_topology top1_S2 top1_S2_topology wh3) = {h3, w}"
    using assms(27) by (by100 blast)
  have hA_ep: "top1_arc_endpoints_on A (subspace_topology top1_S2 top1_S2_topology A) = {g, w}"
    unfolding A_def
    by (rule arc_concat_endpoints[OF hS2 hS2_haus assms(13,4,16,7) assms(40)
        hh1_gh1 hh1_wh1 assms(22) hep_wh1_swap hg_ne_h1 hh1_ne_w])
  have hB_ep: "top1_arc_endpoints_on B (subspace_topology top1_S2 top1_S2_topology B) = {g, w}"
    unfolding B_def
    by (rule arc_concat_endpoints[OF hS2 hS2_haus assms(14,5,17,8) assms(41)
        hh2_gh2 hh2_wh2 assms(23) hep_wh2_swap hg_ne_h2 hh2_ne_w])
  have hCC_ep: "top1_arc_endpoints_on CC (subspace_topology top1_S2 top1_S2_topology CC) = {g, w}"
    unfolding CC_def
    by (rule arc_concat_endpoints[OF hS2 hS2_haus assms(15,6,18,9) assms(42)
        hh3_gh3 hh3_wh3 assms(24) hep_wh3_swap hg_ne_h3 hh3_ne_w])
  have hg_ne_w: "g \<noteq> w" using hcard by (auto simp: card_insert_if split: if_splits)
  \<comment> \<open>Intersections: A \<inter> B = {g,w}, B \<inter> CC = {g,w}, A \<inter> CC = {g,w}.\<close>
  have hAB: "A \<inter> B = {g, w}"
  proof -
    have "gh1 \<inter> gh2 = {g}" by (rule assms(31))
    moreover have "gh1 \<inter> wh2 = {}" by (rule assms(43))
    moreover have "wh1 \<inter> gh2 = {}" using assms(45) by (by100 blast)
    moreover have "wh1 \<inter> wh2 = {w}" by (rule assms(34))
    ultimately show ?thesis unfolding A_def B_def by (by100 blast)
  qed
  have hBCC: "B \<inter> CC = {g, w}"
  proof -
    have "gh2 \<inter> gh3 = {g}" by (rule assms(33))
    moreover have "gh2 \<inter> wh3 = {}" by (rule assms(46))
    moreover have "wh2 \<inter> gh3 = {}" using assms(48) by (by100 blast)
    moreover have "wh2 \<inter> wh3 = {w}" by (rule assms(36))
    ultimately show ?thesis unfolding B_def CC_def by (by100 blast)
  qed
  have hACC: "A \<inter> CC = {g, w}"
  proof -
    have "gh1 \<inter> gh3 = {g}" by (rule assms(32))
    moreover have "gh1 \<inter> wh3 = {}" by (rule assms(44))
    moreover have "wh1 \<inter> gh3 = {}" using assms(47) by (by100 blast)
    moreover have "wh1 \<inter> wh3 = {w}" by (rule assms(35))
    ultimately show ?thesis unfolding A_def CC_def by (by100 blast)
  qed
  \<comment> \<open>Step 2: Apply Lemma\_64\_1 \<Rightarrow> 3 components U, V, W.\<close>
  obtain U V W where hUVW: "U \<noteq> {}" "V \<noteq> {}" "W \<noteq> {}"
      "U \<inter> V = {}" "V \<inter> W = {}" "U \<inter> W = {}"
      "U \<union> V \<union> W = top1_S2 - (A \<union> B \<union> CC)"
      "top1_connected_on U (subspace_topology top1_S2 top1_S2_topology U)"
      "top1_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
      "top1_connected_on W (subspace_topology top1_S2 top1_S2_topology W)"
      "U \<in> top1_S2_topology" "V \<in> top1_S2_topology" "W \<in> top1_S2_topology"
    using Lemma_64_1_theta_space_three_components[OF hS2 hA_sub hB_sub hCC_sub
        hA_arc hB_arc hCC_arc hg_ne_w hAB hBCC hACC hA_ep hB_ep hCC_ep]
    by (metis (no_types))
  \<comment> \<open>Step 3: e \<notin> theta (= A\<union>B\<union>CC).\<close>
  have he_not_theta: "e \<notin> A \<union> B \<union> CC"
  proof -
    have he_ne: "e \<noteq> g" "e \<noteq> w" "e \<noteq> h1" "e \<noteq> h2" "e \<noteq> h3"
      using hcard by (auto simp: card_insert_if split: if_splits)
    have he_in_eh1: "e \<in> eh1" using assms(28) unfolding top1_arc_endpoints_on_def by (by100 blast)
    \<comment> \<open>e \<notin> gh1: if e \<in> gh1 then e \<in> gh1\<inter>eh1={h1}, so e=h1, contradiction.\<close>
    have "e \<notin> gh1"
    proof assume "e \<in> gh1" hence "e \<in> gh1 \<inter> eh1" using he_in_eh1 by (by100 blast)
      hence "e = h1" using assms(49) by (by100 blast)
      thus False using he_ne(3) by (by100 blast) qed
    moreover have "e \<notin> wh1"
    proof assume "e \<in> wh1" hence "e \<in> wh1 \<inter> eh1" using he_in_eh1 by (by100 blast)
      hence "e = h1" using assms(58) by (by100 blast)
      thus False using he_ne(3) by (by100 blast) qed
    moreover have "e \<notin> gh2"
    proof assume "e \<in> gh2"
      have "e \<in> eh2" using assms(29) unfolding top1_arc_endpoints_on_def by (by100 blast)
      hence "e \<in> gh2 \<inter> eh2" using \<open>e \<in> gh2\<close> by (by100 blast)
      hence "e = h2" using assms(50) by (by100 blast)
      thus False using he_ne(4) by (by100 blast) qed
    moreover have "e \<notin> wh2"
    proof assume "e \<in> wh2"
      have "e \<in> eh2" using assms(29) unfolding top1_arc_endpoints_on_def by (by100 blast)
      hence "e \<in> wh2 \<inter> eh2" using \<open>e \<in> wh2\<close> by (by100 blast)
      hence "e = h2" using assms(59) by (by100 blast)
      thus False using he_ne(4) by (by100 blast) qed
    moreover have "e \<notin> gh3"
    proof assume "e \<in> gh3"
      have "e \<in> eh3" using assms(30) unfolding top1_arc_endpoints_on_def by (by100 blast)
      hence "e \<in> gh3 \<inter> eh3" using \<open>e \<in> gh3\<close> by (by100 blast)
      hence "e = h3" using assms(51) by (by100 blast)
      thus False using he_ne(5) by (by100 blast) qed
    moreover have "e \<notin> wh3"
    proof assume "e \<in> wh3"
      have "e \<in> eh3" using assms(30) unfolding top1_arc_endpoints_on_def by (by100 blast)
      hence "e \<in> wh3 \<inter> eh3" using \<open>e \<in> wh3\<close> by (by100 blast)
      hence "e = h3" using assms(60) by (by100 blast)
      thus False using he_ne(5) by (by100 blast) qed
    ultimately show ?thesis unfolding A_def B_def CC_def by (by100 blast)
  qed
  hence "e \<in> U \<union> V \<union> W" using hUVW(7) hsub by (by100 blast)
  \<comment> \<open>Step 4: e can't be in any component (each closure misses some h\_i).\<close>
  \<comment> \<open>If e \<in> U: eh3 connected from e to h3. eh3 \<subseteq> closure(U) = U \<union> (boundary of U).
     Boundary of U \<subseteq> A\<union>B (from theta structure). h3 \<notin> A\<union>B. Contradiction.\<close>
  \<comment> \<open>Key: eh3 \<inter> (A\<union>B) = {}, eh3 \<inter> CC = {h3}. So eh3-{h3} \<subseteq> S2-theta.
     If e \<in> U: eh3-{h3} connected in S2-theta with e \<in> U, so eh3-{h3} \<subseteq> U.
     h3 \<in> closure(eh3-{h3}) \<subseteq> closure(U). But closure(U) \<subseteq> U\<union>A\<union>B (SCCBMC).
     h3 \<notin> U (U\<inter>theta={}), h3 \<notin> A\<union>B. Contradiction.\<close>
  \<comment> \<open>Planarity facts for vertex e.\<close>
  have heh3_A: "eh3 \<inter> A = {}"
  proof -
    have "eh3 \<inter> gh1 = {}" using assms(53) by (by100 blast)
    moreover have "eh3 \<inter> wh1 = {}" using assms(62) by (by100 blast)
    ultimately show ?thesis unfolding A_def by (by100 blast)
  qed
  have heh3_B: "eh3 \<inter> B = {}"
  proof -
    have "eh3 \<inter> gh2 = {}" using assms(55) by (by100 blast)
    moreover have "eh3 \<inter> wh2 = {}" using assms(64) by (by100 blast)
    ultimately show ?thesis unfolding B_def by (by100 blast)
  qed
  have heh1_B: "eh1 \<inter> B = {}"
  proof -
    have "eh1 \<inter> gh2 = {}" using assms(54) by (by100 blast)
    moreover have "eh1 \<inter> wh2 = {}" using assms(63) by (by100 blast)
    ultimately show ?thesis unfolding B_def by (by100 blast)
  qed
  have heh1_CC: "eh1 \<inter> CC = {}"
  proof -
    have "eh1 \<inter> gh3 = {}" using assms(56) by (by100 blast)
    moreover have "eh1 \<inter> wh3 = {}" using assms(65) by (by100 blast)
    ultimately show ?thesis unfolding CC_def by (by100 blast)
  qed
  have heh2_A: "eh2 \<inter> A = {}"
  proof -
    have "eh2 \<inter> gh1 = {}" using assms(52) by (by100 blast)
    moreover have "eh2 \<inter> wh1 = {}" using assms(61) by (by100 blast)
    ultimately show ?thesis unfolding A_def by (by100 blast)
  qed
  have heh2_CC: "eh2 \<inter> CC = {}"
  proof -
    have "eh2 \<inter> gh3 = {}" using assms(57) by (by100 blast)
    moreover have "eh2 \<inter> wh3 = {}" using assms(66) by (by100 blast)
    ultimately show ?thesis unfolding CC_def by (by100 blast)
  qed
  \<comment> \<open>eh3 \<inter> theta = {h3}.\<close>
  have heh3_CC: "eh3 \<inter> CC = {h3}"
  proof -
    have "eh3 \<inter> gh3 = {h3}" using assms(51) by (by100 blast)
    moreover have "eh3 \<inter> wh3 = {h3}" using assms(60) by (by100 blast)
    ultimately show ?thesis unfolding CC_def by (by100 blast)
  qed
  have heh3_theta: "eh3 \<inter> (A \<union> B \<union> CC) = {h3}"
    using heh3_A heh3_B heh3_CC by (by100 blast)
  \<comment> \<open>Similarly for eh1 and eh2.\<close>
  have heh1_theta: "eh1 \<inter> (A \<union> B \<union> CC) = {h1}"
  proof -
    have "eh1 \<inter> A = {h1}"
    proof -
      have "eh1 \<inter> gh1 = {h1}" using assms(49) by (by100 blast)
      moreover have "eh1 \<inter> wh1 = {h1}" using assms(58) by (by100 blast)
      ultimately show ?thesis unfolding A_def by (by100 blast)
    qed
    thus ?thesis using heh1_B heh1_CC by (by100 blast)
  qed
  have heh2_theta: "eh2 \<inter> (A \<union> B \<union> CC) = {h2}"
  proof -
    have "eh2 \<inter> B = {h2}"
    proof -
      have "eh2 \<inter> gh2 = {h2}" using assms(50) by (by100 blast)
      moreover have "eh2 \<inter> wh2 = {h2}" using assms(59) by (by100 blast)
      ultimately show ?thesis unfolding B_def by (by100 blast)
    qed
    thus ?thesis using heh2_A heh2_CC by (by100 blast)
  qed
  \<comment> \<open>h\_i vertex distinctness.\<close>
  have he_ne: "e \<noteq> g" "e \<noteq> w" "e \<noteq> h1" "e \<noteq> h2" "e \<noteq> h3"
    using hcard by (auto simp: card_insert_if split: if_splits)
  have hh_ne: "h1 \<noteq> g" "h1 \<noteq> w" "h2 \<noteq> g" "h2 \<noteq> w" "h3 \<noteq> g" "h3 \<noteq> w"
    using hcard by (auto simp: card_insert_if split: if_splits)
  have hh_ne2: "h1 \<noteq> h2" "h1 \<noteq> h3" "h2 \<noteq> h3"
    using hcard by (auto simp: card_insert_if split: if_splits)
  \<comment> \<open>h3 \<notin> A\<union>B: h3 \<in> CC but h3 \<noteq> g, h3 \<noteq> w, and CC \<inter> (A\<union>B) = {g,w}.\<close>
  have hh3_not_AB: "h3 \<notin> A \<union> B"
  proof -
    have "A \<inter> CC = {g, w}" by (rule hACC)
    moreover have "B \<inter> CC = {g, w}" by (rule hBCC)
    ultimately have "(A \<union> B) \<inter> CC = {g, w}" by (by100 blast)
    moreover have "h3 \<in> CC"
      using assms(24) unfolding top1_arc_endpoints_on_def CC_def by (by100 blast)
    ultimately show ?thesis using hh_ne(5,6) by (by100 blast)
  qed
  have hh1_not_BCC: "h1 \<notin> B \<union> CC"
  proof -
    have "(B \<union> CC) \<inter> A = {g, w}"
      using hAB hACC by (by100 blast)
    moreover have "h1 \<in> A"
      using assms(22) unfolding top1_arc_endpoints_on_def A_def by (by100 blast)
    ultimately show ?thesis using hh_ne(1,2) by (by100 blast)
  qed
  have hh2_not_ACC: "h2 \<notin> A \<union> CC"
  proof -
    have "(A \<union> CC) \<inter> B = {g, w}"
      using hAB hBCC by (by100 blast)
    moreover have "h2 \<in> B"
      using assms(23) unfolding top1_arc_endpoints_on_def B_def by (by100 blast)
    ultimately show ?thesis using hh_ne(3,4) by (by100 blast)
  qed
  \<comment> \<open>Apply theta\_space\_vertex\_exclusion: 3 arcs eh1,eh2,eh3 each avoids one SCC
     and reaches a vertex on the opposite theta arc.\<close>
  have he_in_eh1: "e \<in> eh1" using assms(28) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have he_in_eh2: "e \<in> eh2" using assms(29) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have he_in_eh3: "e \<in> eh3" using assms(30) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hh1_in_A: "h1 \<in> A - {g, w}" using assms(22) hh_ne(1,2) unfolding top1_arc_endpoints_on_def A_def by (by100 blast)
  have hh2_in_B: "h2 \<in> B - {g, w}" using assms(23) hh_ne(3,4) unfolding top1_arc_endpoints_on_def B_def by (by100 blast)
  have hh3_in_CC: "h3 \<in> CC - {g, w}" using assms(24) hh_ne(5,6) unfolding top1_arc_endpoints_on_def CC_def by (by100 blast)
  have "eh1 \<inter> (B \<union> CC) = {}" using heh1_B heh1_CC by (by100 blast)
  have "eh2 \<inter> (A \<union> CC) = {}" using heh2_A heh2_CC by (by100 blast)
  have "eh3 \<inter> (A \<union> B) = {}" using heh3_A heh3_B by (by100 blast)
  \<comment> \<open>Apply theta\_space\_vertex\_exclusion with E1=eh1, E2=eh2, E3=eh3.\<close>
  have hh1_in_eh1: "h1 \<in> eh1" using assms(28) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hh2_in_eh2: "h2 \<in> eh2" using assms(29) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have hh3_in_eh3: "h3 \<in> eh3" using assms(30) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have heh1_meets_A: "eh1 \<inter> (A - {g, w}) \<noteq> {}"
    using hh1_in_eh1 hh1_in_A by (by100 blast)
  have heh2_meets_B: "eh2 \<inter> (B - {g, w}) \<noteq> {}"
    using hh2_in_eh2 hh2_in_B by (by100 blast)
  have heh3_meets_CC: "eh3 \<inter> (CC - {g, w}) \<noteq> {}"
    using hh3_in_eh3 hh3_in_CC by (by100 blast)
  have heh1_conn: "top1_connected_on eh1 (subspace_topology top1_S2 top1_S2_topology eh1)"
    by (rule arc_connected[OF assms(19)])
  have heh2_conn: "top1_connected_on eh2 (subspace_topology top1_S2 top1_S2_topology eh2)"
    by (rule arc_connected[OF assms(20)])
  have heh3_conn: "top1_connected_on eh3 (subspace_topology top1_S2 top1_S2_topology eh3)"
    by (rule arc_connected[OF assms(21)])
  have hU_sub: "U \<subseteq> top1_S2 - (A \<union> B \<union> CC)"
    using hUVW(7) hUVW(4,6) by (by100 blast)
  have hV_sub: "V \<subseteq> top1_S2 - (A \<union> B \<union> CC)"
    using hUVW(7) hUVW(4,5) by (by100 blast)
  have hW_sub: "W \<subseteq> top1_S2 - (A \<union> B \<union> CC)"
    using hUVW(7) hUVW(5,6) by (by100 blast)
  show False
    by (rule theta_space_vertex_exclusion[OF hS2 hA_sub hB_sub hCC_sub
        hA_arc hB_arc hCC_arc hg_ne_w hAB hBCC hACC hA_ep hB_ep hCC_ep
        hUVW(1) hUVW(11) hU_sub hUVW(8)
        hUVW(2) hUVW(12) hV_sub hUVW(9)
        hUVW(3) hUVW(13) hW_sub hUVW(10)
        hUVW(4,5,6,7)
        \<open>e \<in> U \<union> V \<union> W\<close>
        assms(10) heh1_conn \<open>eh1 \<inter> (B \<union> CC) = {}\<close> he_in_eh1 heh1_meets_A
        assms(11) heh2_conn \<open>eh2 \<inter> (A \<union> CC) = {}\<close> he_in_eh2 heh2_meets_B
        assms(12) heh3_conn \<open>eh3 \<inter> (A \<union> B) = {}\<close> he_in_eh3 heh3_meets_CC])
qed

text \<open>Theorem 64.4 (K5 non-planarity) is fully proved in the K5 session
  (K5\_nonplanar.Theorem\_64\_4\_K5\_not\_planar, 0 sorry, certified).
  Now imported via the K5 session dependency.\<close>


text \<open>In an abelian group, the product of a word can be decomposed by counting
  net occurrences of each generator. This gives a "net count" homomorphism.\<close>
lemma abelian_word_net_count:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and x :: 'g
  assumes hG: "top1_is_abelian_group_on G mul e invg"
      and hx: "x \<in> G"
      and hws: "\<forall>i<length ws. ws!i \<in> G"
  shows "foldr mul (x # ws) e = mul x (foldr mul ws e)"
  by (by100 simp)

text \<open>Key fact: in an abelian group, foldr mul commutes with permutations.
  More specifically: mul a (mul b c) = mul b (mul a c) for a, b, c \<in> G.\<close>
lemma abelian_mul_left_commute:
  assumes "top1_is_abelian_group_on G mul e invg"
      and "a \<in> G" and "b \<in> G" and "c \<in> G"
  shows "mul a (mul b c) = mul b (mul a c)"
proof -
  have hG: "top1_is_group_on G mul e invg"
    using assms(1) unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hcomm: "mul a b = mul b a"
    using assms unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hassoc1: "mul (mul a b) c = mul a (mul b c)"
    using hG assms(2,3,4) unfolding top1_is_group_on_def by (by100 blast)
  have hassoc2: "mul (mul b a) c = mul b (mul a c)"
    using hG assms(2,3,4) unfolding top1_is_group_on_def by (by100 blast)
  have "mul a (mul b c) = mul (mul a b) c" using hassoc1 by (by100 simp)
  also have "\<dots> = mul (mul b a) c" using hcomm by (by100 simp)
  also have "\<dots> = mul b (mul a c)" using hassoc2 by (by100 simp)
  finally show ?thesis .
qed

text \<open>Key lemma: in an abelian group, an element can be extracted from any position
  in a foldr mul product to the front. This is the building block for permutation
  invariance of products in abelian groups.\<close>
lemma abelian_foldr_mul_extract:
  assumes hG: "top1_is_abelian_group_on G mul e invg"
      and hxs: "\<forall>i<length xs. xs ! i \<in> G"
      and ha: "a \<in> G"
      and hys: "\<forall>i<length ys. ys ! i \<in> G"
  shows "foldr mul (xs @ [a] @ ys) e = mul a (foldr mul (xs @ ys) e)"
  using hxs
proof (induction xs)
  case Nil
  show ?case by (by100 simp)
next
  case (Cons b xs')
  have hb: "b \<in> G" using Cons.prems by (by100 force)
  have hxs': "\<forall>i<length xs'. xs' ! i \<in> G" using Cons.prems by (by100 force)
  have hG_grp: "top1_is_group_on G mul e invg"
    using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hIH: "foldr mul (xs' @ [a] @ ys) e = mul a (foldr mul (xs' @ ys) e)"
    by (rule Cons.IH[OF hxs'])
  have hxsys: "\<forall>i<length (xs' @ ys). (xs' @ ys) ! i \<in> G"
  proof (intro allI impI)
    fix i assume hi: "i < length (xs' @ ys)"
    show "(xs' @ ys) ! i \<in> G"
    proof (cases "i < length xs'")
      case True thus ?thesis using hxs' nth_append[of xs' ys i] by (by100 simp)
    next
      case False thus ?thesis using hys hi nth_append[of xs' ys i] by (by100 force)
    qed
  qed
  have hfoldr_rest: "foldr mul (xs' @ ys) e \<in> G"
    by (rule foldr_mul_closed[OF hG_grp hxsys])
  have "foldr mul ((b # xs') @ [a] @ ys) e = mul b (foldr mul (xs' @ [a] @ ys) e)"
    by (by100 simp)
  also have "\<dots> = mul b (mul a (foldr mul (xs' @ ys) e))" using hIH by (by100 simp)
  also have "\<dots> = mul a (mul b (foldr mul (xs' @ ys) e))"
    by (rule abelian_mul_left_commute[OF hG hb ha hfoldr_rest])
  also have "\<dots> = mul a (foldr mul ((b # xs') @ ys) e)" by (by100 simp)
  finally show ?case .
qed

text \<open>Removing an inverse pair from a foldr product.\<close>
lemma abelian_foldr_mul_cancel_pair:
  assumes hG: "top1_is_abelian_group_on G mul e invg"
      and hxs: "\<forall>i<length xs. xs ! i \<in> G" and ha: "a \<in> G"
      and hys: "\<forall>i<length ys. ys ! i \<in> G"
      and hzs: "\<forall>i<length zs. zs ! i \<in> G"
  shows "foldr mul (xs @ [a] @ ys @ [invg a] @ zs) e = foldr mul (xs @ ys @ zs) e"
proof -
  have hG_grp: "top1_is_group_on G mul e invg"
    using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hinva: "invg a \<in> G"
    using hG_grp ha unfolding top1_is_group_on_def by (by100 blast)
  have hyszs1: "\<forall>i<length (ys @ [invg a] @ zs). (ys @ [invg a] @ zs) ! i \<in> G"
  proof (intro allI impI)
    fix i assume hi: "i < length (ys @ [invg a] @ zs)"
    show "(ys @ [invg a] @ zs) ! i \<in> G"
    proof (cases "i < length ys")
      case True
      hence "(ys @ [invg a] @ zs) ! i = ys ! i"
        apply (simp only: nth_append if_True) done
      thus ?thesis using hys True by (by100 simp)
    next
      case False
      hence hge: "i \<ge> length ys" by (by100 simp)
      show ?thesis
      proof (cases "i = length ys")
        case True
        hence "(ys @ [invg a] @ zs) ! i = invg a"
          apply (simp only: nth_append if_False) using True by (by100 simp)
        thus ?thesis using hinva by (by100 simp)
      next
        case False
        hence "i > length ys" using hge by (by100 simp)
        hence "i - length ys - 1 < length zs" using hi by (by100 simp)
        thus ?thesis using hzs \<open>i > length ys\<close> hi
          apply (simp only: nth_append if_False)
          by (by100 force)
      qed
    qed
  qed
  have hxsys: "\<forall>i<length (xs @ ys). (xs @ ys) ! i \<in> G"
  proof (intro allI impI)
    fix i assume hi: "i < length (xs @ ys)"
    show "(xs @ ys) ! i \<in> G"
    proof (cases "i < length xs")
      case True
      hence "(xs @ ys) ! i = xs ! i"
        apply (simp only: nth_append if_True) done
      thus ?thesis using hxs True by (by100 simp)
    next
      case False
      hence "\<not> i < length xs" by (by100 simp)
      hence "(xs @ ys) ! i = ys ! (i - length xs)"
        apply (simp only: nth_append if_False) done
      moreover have "i - length xs < length ys" using hi False by (by100 simp)
      ultimately show ?thesis using hys by (by100 simp)
    qed
  qed
  have hxsyszs: "\<forall>i<length (xs @ ys @ zs). (xs @ ys @ zs) ! i \<in> G"
  proof (intro allI impI)
    fix i assume hi: "i < length (xs @ ys @ zs)"
    show "(xs @ ys @ zs) ! i \<in> G"
    proof (cases "i < length xs")
      case True
      hence "(xs @ ys @ zs) ! i = xs ! i"
        apply (simp only: nth_append if_True) done
      thus ?thesis using hxs True by (by100 simp)
    next
      case False
      hence "(xs @ ys @ zs) ! i = (ys @ zs) ! (i - length xs)"
        apply (simp only: nth_append if_False) done
      moreover have "i - length xs < length (ys @ zs)" using hi False by (by100 simp)
      ultimately show ?thesis using hys hzs False hi
        apply (simp only: nth_append if_True if_False)
        apply (by100 force)
        done
    qed
  qed
  \<comment> \<open>Step 1: extract a.\<close>
  have h1: "foldr mul (xs @ [a] @ (ys @ [invg a] @ zs)) e
      = mul a (foldr mul (xs @ (ys @ [invg a] @ zs)) e)"
    apply (rule abelian_foldr_mul_extract)
    apply (rule hG) apply (rule hxs) apply (rule ha) apply (rule hyszs1)
    done
  \<comment> \<open>Step 2: extract invg(a).\<close>
  have h2: "foldr mul ((xs @ ys) @ [invg a] @ zs) e
      = mul (invg a) (foldr mul ((xs @ ys) @ zs) e)"
    apply (rule abelian_foldr_mul_extract)
    apply (rule hG) apply (rule hxsys) apply (rule hinva) apply (rule hzs)
    done
  \<comment> \<open>Step 3: cancel.\<close>
  have hprod: "foldr mul (xs @ ys @ zs) e \<in> G"
    by (rule foldr_mul_closed[OF hG_grp hxsyszs])
  have "mul a (mul (invg a) (foldr mul (xs @ ys @ zs) e)) = foldr mul (xs @ ys @ zs) e"
  proof -
    have "mul a (mul (invg a) (foldr mul (xs @ ys @ zs) e))
        = mul (mul a (invg a)) (foldr mul (xs @ ys @ zs) e)"
      using group_assoc[OF hG_grp ha hinva hprod] by (by100 simp)
    also have "mul a (invg a) = e"
      using hG_grp ha unfolding top1_is_group_on_def by (by100 blast)
    also have "mul e (foldr mul (xs @ ys @ zs) e) = foldr mul (xs @ ys @ zs) e"
      using hG_grp hprod unfolding top1_is_group_on_def by (by100 blast)
    finally show ?thesis .
  qed
  \<comment> \<open>Combine.\<close>
  show ?thesis using h1 h2 \<open>mul a (mul (invg a) (foldr mul (xs @ ys @ zs) e)) = foldr mul (xs @ ys @ zs) e\<close>
    by (by100 simp)
qed


text \<open>Corollary: in abelian group, foldr mul of xs @ [a] @ ys = mul a (foldr mul (xs @ ys) e).
  Applied to filter: foldr mul xs e = foldr mul (filter P xs @ filter (Not \<circ> P) xs) e
  = mul (foldr mul (filter P xs) e) (foldr mul (filter (Not \<circ> P) xs) e).\<close>
lemma abelian_foldr_mul_split_filter:
  assumes hG: "top1_is_abelian_group_on G mul e invg"
      and hxs: "\<forall>i<length xs. xs ! i \<in> G"
  shows "foldr mul xs e = mul (foldr mul (filter P xs) e) (foldr mul (filter (\<lambda>x. \<not> P x) xs) e)"
  using hxs
proof (induction xs)
  case Nil
  have "mul e e = e"
    using hG unfolding top1_is_abelian_group_on_def top1_is_group_on_def by (by100 blast)
  thus ?case by (by100 simp)
next
  case (Cons a xs)
  have ha: "a \<in> G" using Cons(2) by (by100 force)
  have hxs': "\<forall>i<length xs. xs ! i \<in> G" using Cons(2) by (by100 force)
  have hG_grp: "top1_is_group_on G mul e invg"
    using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hIH: "foldr mul xs e = mul (foldr mul (filter P xs) e) (foldr mul (filter (\<lambda>x. \<not> P x) xs) e)"
    using Cons(1) hxs' by (by100 blast)
  have hfP_G: "\<forall>i<length (filter P xs). (filter P xs) ! i \<in> G"
  proof (intro allI impI)
    fix i assume "i < length (filter P xs)"
    hence "filter P xs ! i \<in> set (filter P xs)" using nth_mem by (by100 blast)
    hence "filter P xs ! i \<in> set xs" by (by100 auto)
    then obtain k where hk: "k < length xs" "xs ! k = filter P xs ! i"
      using in_set_conv_nth by (by100 metis)
    have "xs ! k \<in> G" using hxs' hk(1) by (by100 blast)
    thus "(filter P xs) ! i \<in> G" using hk(2) by (by100 simp)
  qed
  have hfP: "foldr mul (filter P xs) e \<in> G"
    by (rule foldr_mul_closed[OF hG_grp hfP_G])
  have hfNP_G: "\<forall>i<length (filter (\<lambda>x. \<not> P x) xs). (filter (\<lambda>x. \<not> P x) xs) ! i \<in> G"
  proof (intro allI impI)
    fix i assume "i < length (filter (\<lambda>x. \<not> P x) xs)"
    hence "filter (\<lambda>x. \<not> P x) xs ! i \<in> set (filter (\<lambda>x. \<not> P x) xs)" using nth_mem by (by100 blast)
    hence "filter (\<lambda>x. \<not> P x) xs ! i \<in> set xs" by (by100 auto)
    then obtain k where hk: "k < length xs" "xs ! k = filter (\<lambda>x. \<not> P x) xs ! i"
      using in_set_conv_nth by (by100 metis)
    have "xs ! k \<in> G" using hxs' hk(1) by (by100 blast)
    thus "(filter (\<lambda>x. \<not> P x) xs) ! i \<in> G" using hk(2) by (by100 simp)
  qed
  have hfNP: "foldr mul (filter (\<lambda>x. \<not> P x) xs) e \<in> G"
    by (rule foldr_mul_closed[OF hG_grp hfNP_G])
  show ?case
  proof (cases "P a")
    case True
    have "foldr mul (a # xs) e = mul a (foldr mul xs e)" by (by100 simp)
    also have "\<dots> = mul a (mul (foldr mul (filter P xs) e) (foldr mul (filter (\<lambda>x. \<not> P x) xs) e))"
      using hIH by (by100 simp)
    also have "\<dots> = mul (mul a (foldr mul (filter P xs) e)) (foldr mul (filter (\<lambda>x. \<not> P x) xs) e)"
    proof -
      have "mul a (mul (foldr mul (filter P xs) e) (foldr mul (filter (\<lambda>x. \<not> P x) xs) e))
          = mul (mul a (foldr mul (filter P xs) e)) (foldr mul (filter (\<lambda>x. \<not> P x) xs) e)"
        using group_assoc[OF hG_grp ha hfP hfNP] by (by100 simp)
      thus ?thesis by (by100 simp)
    qed
    also have "mul a (foldr mul (filter P xs) e) = foldr mul (filter P (a # xs)) e"
      using True by (by100 simp)
    also have "filter (\<lambda>x. \<not> P x) xs = filter (\<lambda>x. \<not> P x) (a # xs)"
      using True by (by100 simp)
    finally show ?thesis by (by100 simp)
  next
    case False
    have "foldr mul (a # xs) e = mul a (foldr mul xs e)" by (by100 simp)
    also have "\<dots> = mul a (mul (foldr mul (filter P xs) e) (foldr mul (filter (\<lambda>x. \<not> P x) xs) e))"
      using hIH by (by100 simp)
    also have "\<dots> = mul (foldr mul (filter P xs) e) (mul a (foldr mul (filter (\<lambda>x. \<not> P x) xs) e))"
      by (rule abelian_mul_left_commute[OF hG ha hfP hfNP])
    also have "mul a (foldr mul (filter (\<lambda>x. \<not> P x) xs) e) = foldr mul (filter (\<lambda>x. \<not> P x) (a # xs)) e"
      using False by (by100 simp)
    also have "filter P xs = filter P (a # xs)"
      using False by (by100 simp)
    finally show ?thesis by (by100 simp)
  qed
qed


subsection \<open>Reviewer-requested algebra infrastructure lemmas\<close>

text \<open>Reflexivity: any group is isomorphic to itself (via the identity).\<close>
lemma group_iso_on_refl:
  assumes "top1_is_group_on G mul e invg"
  shows "top1_groups_isomorphic_on G mul G mul"
  unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def top1_group_hom_on_def
  apply (rule exI[of _ id])
  using assms unfolding top1_is_group_on_def
  apply (by100 auto)
  done

text \<open>Composition of group isomorphisms.\<close>
lemma group_iso_on_compose:
  assumes "top1_group_iso_on G mulG H mulH f"
      and "top1_group_iso_on H mulH K mulK g"
      and "top1_is_group_on G mulG eG invgG"
      and "top1_is_group_on H mulH eH invgH"
      and "top1_is_group_on K mulK eK invgK"
  shows "top1_group_iso_on G mulG K mulK (g \<circ> f)"
proof -
  have hf_hom: "top1_group_hom_on G mulG H mulH f" and hf_bij: "bij_betw f G H"
    using assms(1) unfolding top1_group_iso_on_def by (by100 blast)+
  have hg_hom: "top1_group_hom_on H mulH K mulK g" and hg_bij: "bij_betw g H K"
    using assms(2) unfolding top1_group_iso_on_def by (by100 blast)+
  have hgf_hom: "top1_group_hom_on G mulG K mulK (g \<circ> f)"
    unfolding top1_group_hom_on_def comp_def
  proof (intro conjI ballI)
    fix x assume "x \<in> G"
    hence "f x \<in> H" using hf_hom unfolding top1_group_hom_on_def by (by100 blast)
    thus "g (f x) \<in> K" using hg_hom unfolding top1_group_hom_on_def by (by100 blast)
  next
    fix x y assume "x \<in> G" "y \<in> G"
    have "f (mulG x y) = mulH (f x) (f y)"
      using hf_hom \<open>x \<in> G\<close> \<open>y \<in> G\<close> unfolding top1_group_hom_on_def by (by100 blast)
    moreover have "f x \<in> H" "f y \<in> H"
      using hf_hom \<open>x \<in> G\<close> \<open>y \<in> G\<close> unfolding top1_group_hom_on_def by (by100 blast)+
    moreover have "g (mulH (f x) (f y)) = mulK (g (f x)) (g (f y))"
      using hg_hom \<open>f x \<in> H\<close> \<open>f y \<in> H\<close> unfolding top1_group_hom_on_def by (by100 blast)
    ultimately show "g (f (mulG x y)) = mulK (g (f x)) (g (f y))" by (by100 simp)
  qed
  have hgf_bij: "bij_betw (g \<circ> f) G K"
    by (rule bij_betw_trans[OF hf_bij hg_bij])
  show ?thesis unfolding top1_group_iso_on_def using hgf_hom hgf_bij by (by100 blast)
qed

text \<open>Isomorphism maps normal subgroups to normal subgroups.\<close>
lemma group_iso_on_image_normal_subgroup:
  assumes "top1_group_iso_on G mulG H mulH f"
      and "top1_is_group_on G mulG eG invgG"
      and "top1_is_group_on H mulH eH invgH"
      and "top1_normal_subgroup_on G mulG eG invgG N"
  shows "top1_normal_subgroup_on H mulH eH invgH (f ` N)"
proof -
  have hf_hom: "top1_group_hom_on G mulG H mulH f" and hf_bij: "bij_betw f G H"
    using assms(1) unfolding top1_group_iso_on_def by (by100 blast)+
  have hN_sub: "N \<subseteq> G" and hN_grp: "top1_is_group_on N mulG eG invgG"
    and hN_conj: "\<forall>g\<in>G. \<forall>n\<in>N. mulG (mulG g n) (invgG g) \<in> N"
    using assms(4) unfolding top1_normal_subgroup_on_def by (by100 blast)+
  \<comment> \<open>f(N) \<subseteq> H: image of subset.\<close>
  have hfN_sub: "f ` N \<subseteq> H"
    using hf_hom hN_sub unfolding top1_group_hom_on_def by (by100 blast)
  \<comment> \<open>f(N) is a group under mulH (image of group under iso).\<close>
  have hfN_grp: "top1_is_group_on (f ` N) mulH eH invgH"
  proof -
    have hf_mul: "\<And>x y. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> f (mulG x y) = mulH (f x) (f y)"
      using hf_hom unfolding top1_group_hom_on_def by (by100 blast)
    have hf_in: "\<And>x. x \<in> G \<Longrightarrow> f x \<in> H"
      using hf_hom unfolding top1_group_hom_on_def by (by100 blast)
    have hH_lid: "\<And>x. x \<in> H \<Longrightarrow> mulH eH x = x" using assms(3) unfolding top1_is_group_on_def by (by100 blast)
    have hH_rid: "\<And>x. x \<in> H \<Longrightarrow> mulH x eH = x" using assms(3) unfolding top1_is_group_on_def by (by100 blast)
    have hH_linv: "\<And>x. x \<in> H \<Longrightarrow> mulH (invgH x) x = eH" using assms(3) unfolding top1_is_group_on_def by (by100 blast)
    have hH_assoc: "\<And>x y z. x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> z \<in> H \<Longrightarrow> mulH (mulH x y) z = mulH x (mulH y z)"
      using assms(3) unfolding top1_is_group_on_def by (by100 blast)
    have hH_inv_in: "\<And>x. x \<in> H \<Longrightarrow> invgH x \<in> H" using assms(3) unfolding top1_is_group_on_def by (by100 blast)
    \<comment> \<open>eH = f(eG) \<in> f(N).\<close>
    have heG_N: "eG \<in> N" using hN_grp unfolding top1_is_group_on_def by (by100 blast)
    have heG_G: "eG \<in> G" using assms(2) unfolding top1_is_group_on_def by (by100 blast)
    have "f eG = eH"
    proof -
      have "mulH (f eG) (f eG) = f (mulG eG eG)" using hf_mul[OF heG_G heG_G] by (by100 simp)
      also have "mulG eG eG = eG" using assms(2) unfolding top1_is_group_on_def by (by100 blast)
      finally have "mulH (f eG) (f eG) = f eG" .
      have hfe: "f eG \<in> H" using hf_in[OF heG_G] .
      have "invgH (f eG) \<in> H" using assms(3) hfe unfolding top1_is_group_on_def by (by100 blast)
      have hinvfe: "invgH (f eG) \<in> H" using hH_inv_in[OF hfe] .
      have "f eG = mulH eH (f eG)" using hH_lid[OF hfe] by (by100 simp)
      also have "\<dots> = mulH (mulH (invgH (f eG)) (f eG)) (f eG)"
        using hH_linv[OF hfe] by (by100 simp)
      also have "\<dots> = mulH (invgH (f eG)) (mulH (f eG) (f eG))"
        using hH_assoc[OF hinvfe hfe hfe] by (by100 simp)
      also have "\<dots> = mulH (invgH (f eG)) (f eG)" using \<open>mulH (f eG) (f eG) = f eG\<close> by (by100 simp)
      also have "\<dots> = eH" using hH_linv[OF hfe] .
      finally show ?thesis .
    qed
    hence "eH \<in> f ` N" using heG_N by (by100 force)
    \<comment> \<open>Closure under mulH: f(n1)\<cdot>f(n2) = f(n1\<cdot>n2) \<in> f(N).\<close>
    have hfN_mul: "\<forall>x\<in>f ` N. \<forall>y\<in>f ` N. mulH x y \<in> f ` N"
    proof (intro ballI)
      fix fx fy assume "fx \<in> f ` N" "fy \<in> f ` N"
      then obtain n1 n2 where hn: "n1 \<in> N" "f n1 = fx" "n2 \<in> N" "f n2 = fy" by (by100 blast)
      have "mulG n1 n2 \<in> N" using hN_grp hn(1,3) unfolding top1_is_group_on_def by (by100 blast)
      moreover have "f (mulG n1 n2) = mulH fx fy"
        using hf_mul[OF _ _] hN_sub hn by (by100 blast)
      ultimately show "mulH fx fy \<in> f ` N" by (by100 force)
    qed
    \<comment> \<open>Closure under invgH: invgH(f(n)) = f(invgG(n)) \<in> f(N).\<close>
    have hfN_inv: "\<forall>x\<in>f ` N. invgH x \<in> f ` N"
    proof (intro ballI)
      fix fx assume "fx \<in> f ` N"
      then obtain n where hn: "n \<in> N" "f n = fx" by (by100 blast)
      have hn_G: "n \<in> G" using hN_sub hn(1) by (by100 blast)
      have "invgG n \<in> N" using hN_grp hn(1) unfolding top1_is_group_on_def by (by100 blast)
      moreover have "f (invgG n) = invgH fx"
      proof -
        have hinvn_G: "invgG n \<in> G" using assms(2) hn_G unfolding top1_is_group_on_def by (by100 blast)
        have "mulH fx (f (invgG n)) = f (mulG n (invgG n))" using hf_mul[OF hn_G hinvn_G] hn(2) by (by100 simp)
        also have "mulG n (invgG n) = eG" using assms(2) hn_G unfolding top1_is_group_on_def by (by100 blast)
        finally have "mulH fx (f (invgG n)) = eH" using \<open>f eG = eH\<close> by (by100 simp)
        \<comment> \<open>fx \<cdot> f(invgG n) = eH implies f(invgG n) = invgH(fx).\<close>
        have hfx_H: "fx \<in> H" using hfN_sub \<open>fx \<in> f ` N\<close> by (by100 blast)
        have hfinvn_H: "f (invgG n) \<in> H" using hf_in[OF hinvn_G] .
        have "invgH fx \<in> H" using assms(3) hfx_H unfolding top1_is_group_on_def by (by100 blast)
        have "f (invgG n) = mulH eH (f (invgG n))" using hH_lid[OF hfinvn_H] by (by100 simp)
        also have "\<dots> = mulH (mulH (invgH fx) fx) (f (invgG n))"
          using hH_linv[OF hfx_H] by (by100 simp)
        also have "\<dots> = mulH (invgH fx) (mulH fx (f (invgG n)))"
          using hH_assoc[OF \<open>invgH fx \<in> H\<close> hfx_H hfinvn_H] by (by100 simp)
        also have "\<dots> = mulH (invgH fx) eH" using \<open>mulH fx (f (invgG n)) = eH\<close> by (by100 simp)
        also have "\<dots> = invgH fx" using hH_rid[OF \<open>invgH fx \<in> H\<close>] by (by100 simp)
        finally show ?thesis .
      qed
      ultimately show "invgH fx \<in> f ` N" by (by100 force)
    qed
    \<comment> \<open>Associativity, identity, inverse in f(N) inherited from H.\<close>
    have "\<forall>x\<in>f ` N. \<forall>y\<in>f ` N. \<forall>z\<in>f ` N. mulH (mulH x y) z = mulH x (mulH y z)"
      using hfN_sub hH_assoc by (by100 blast)
    moreover have "\<forall>x\<in>f ` N. mulH eH x = x \<and> mulH x eH = x"
      using hfN_sub hH_lid hH_rid by (by100 blast)
    moreover have "\<forall>x\<in>f ` N. mulH (invgH x) x = eH \<and> mulH x (invgH x) = eH"
      using hfN_sub assms(3) unfolding top1_is_group_on_def by (by100 blast)
    ultimately show ?thesis unfolding top1_is_group_on_def
      using \<open>eH \<in> f ` N\<close> hfN_mul hfN_inv by (by100 blast)
  qed
  \<comment> \<open>Conjugation-closed: for h \<in> H, fn \<in> f(N): h\<cdot>fn\<cdot>h\<inverse> \<in> f(N).\<close>
  have hfN_conj: "\<forall>h\<in>H. \<forall>fn\<in>f ` N. mulH (mulH h fn) (invgH h) \<in> f ` N"
  proof (intro ballI)
    fix h fn assume hh: "h \<in> H" and hfn: "fn \<in> f ` N"
    \<comment> \<open>h = f(g) for some g (f surjective). fn = f(n) for some n \<in> N.\<close>
    obtain g where hg: "g \<in> G" "f g = h" using hf_bij hh unfolding bij_betw_def by (by100 blast)
    obtain n where hn: "n \<in> N" "f n = fn" using hfn by (by100 blast)
    \<comment> \<open>mulG(mulG g n)(invgG g) \<in> N by normality.\<close>
    have "mulG (mulG g n) (invgG g) \<in> N"
      using hN_conj hg(1) hn(1) by (by100 blast)
    \<comment> \<open>f maps this to mulH(mulH h fn)(invgH h) by homomorphism.\<close>
    hence "f (mulG (mulG g n) (invgG g)) \<in> f ` N" by (by100 blast)
    moreover have "f (mulG (mulG g n) (invgG g)) = mulH (mulH h fn) (invgH h)"
    proof -
      have hf_mul: "\<And>x y. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> f (mulG x y) = mulH (f x) (f y)"
        using hf_hom unfolding top1_group_hom_on_def by (by100 blast)
      have hn_G: "n \<in> G" using hN_sub hn(1) by (by100 blast)
      have hinvg_G: "invgG g \<in> G" using assms(2) hg(1) unfolding top1_is_group_on_def by (by100 blast)
      have hgn_G: "mulG g n \<in> G" using assms(2) hg(1) hn_G unfolding top1_is_group_on_def by (by100 blast)
      have "f (mulG (mulG g n) (invgG g)) = mulH (f (mulG g n)) (f (invgG g))"
        using hf_mul[OF hgn_G hinvg_G] .
      also have "f (mulG g n) = mulH (f g) (f n)" using hf_mul[OF hg(1) hn_G] .
      also have "f g = h" by (rule hg(2))
      also have "f n = fn" by (rule hn(2))
      finally have h1: "f (mulG (mulG g n) (invgG g)) = mulH (mulH h fn) (f (invgG g))" .
      \<comment> \<open>f(invgG g) = invgH(f g) = invgH(h): iso preserves inverse.\<close>
      have "mulH (f g) (f (invgG g)) = f (mulG g (invgG g))"
        using hf_mul[OF hg(1) hinvg_G] by (by100 simp)
      also have "mulG g (invgG g) = eG" using assms(2) hg(1) unfolding top1_is_group_on_def by (by100 blast)
      also have "f eG = eH"
      proof -
        have "eG \<in> G" using assms(2) unfolding top1_is_group_on_def by (by100 blast)
        have "mulH (f eG) (f eG) = f (mulG eG eG)" using hf_mul[OF \<open>eG \<in> G\<close> \<open>eG \<in> G\<close>] by (by100 simp)
        also have "mulG eG eG = eG" using assms(2) unfolding top1_is_group_on_def by (by100 blast)
        finally have "mulH (f eG) (f eG) = f eG" .
        have "f eG \<in> H" using hf_hom \<open>eG \<in> G\<close> unfolding top1_group_hom_on_def by (by100 blast)
        \<comment> \<open>Idempotent in group = identity.\<close>
        have "mulH eH (f eG) = f eG" using assms(3) \<open>f eG \<in> H\<close> unfolding top1_is_group_on_def by (by100 blast)
        have "mulH (invgH (f eG)) (f eG) = eH" using assms(3) \<open>f eG \<in> H\<close> unfolding top1_is_group_on_def by (by100 blast)
        have "invgH (f eG) \<in> H" using assms(3) \<open>f eG \<in> H\<close> unfolding top1_is_group_on_def by (by100 blast)
        have "f eG = mulH (mulH (invgH (f eG)) (f eG)) (f eG)"
          using \<open>mulH (invgH (f eG)) (f eG) = eH\<close> \<open>mulH eH (f eG) = f eG\<close> by (by100 simp)
        also have "\<dots> = mulH (invgH (f eG)) (mulH (f eG) (f eG))"
          using assms(3) \<open>invgH (f eG) \<in> H\<close> \<open>f eG \<in> H\<close> unfolding top1_is_group_on_def by (by100 blast)
        also have "\<dots> = mulH (invgH (f eG)) (f eG)"
          using \<open>mulH (f eG) (f eG) = f eG\<close> by (by100 simp)
        also have "\<dots> = eH" using \<open>mulH (invgH (f eG)) (f eG) = eH\<close> .
        finally show ?thesis .
      qed
      finally have "mulH h (f (invgG g)) = eH" using hg(2) by (by100 simp)
      \<comment> \<open>So f(invgG g) = invgH(h).\<close>
      have hfg_H: "h \<in> H" by (rule hh)
      have hfinvg_H: "f (invgG g) \<in> H" using hf_hom hinvg_G unfolding top1_group_hom_on_def by (by100 blast)
      have "invgH h \<in> H" using assms(3) hh unfolding top1_is_group_on_def by (by100 blast)
      have "mulH h (invgH h) = eH" using assms(3) hh unfolding top1_is_group_on_def by (by100 blast)
      \<comment> \<open>From mulH h x = eH and mulH h (invgH h) = eH, deduce x = invgH h.\<close>
      have hH_lid: "\<And>x. x \<in> H \<Longrightarrow> mulH eH x = x" using assms(3) unfolding top1_is_group_on_def by (by100 blast)
      have hH_rid: "\<And>x. x \<in> H \<Longrightarrow> mulH x eH = x" using assms(3) unfolding top1_is_group_on_def by (by100 blast)
      have hH_linv: "\<And>x. x \<in> H \<Longrightarrow> mulH (invgH x) x = eH" using assms(3) unfolding top1_is_group_on_def by (by100 blast)
      have hH_assoc: "\<And>x y z. x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> z \<in> H \<Longrightarrow> mulH (mulH x y) z = mulH x (mulH y z)"
        using assms(3) unfolding top1_is_group_on_def by (by100 blast)
      have "f (invgG g) = mulH eH (f (invgG g))" using hH_lid[OF hfinvg_H] by (by100 simp)
      also have "\<dots> = mulH (mulH (invgH h) h) (f (invgG g))"
        using hH_linv[OF hh] by (by100 simp)
      also have "\<dots> = mulH (invgH h) (mulH h (f (invgG g)))"
        using hH_assoc[OF \<open>invgH h \<in> H\<close> hh hfinvg_H] by (by100 simp)
      also have "\<dots> = mulH (invgH h) eH"
        using \<open>mulH h (f (invgG g)) = eH\<close> by (by100 simp)
      also have "\<dots> = invgH h" using hH_rid[OF \<open>invgH h \<in> H\<close>] by (by100 simp)
      finally have "f (invgG g) = invgH h" .
      show ?thesis using h1 \<open>f (invgG g) = invgH h\<close> by (by100 simp)
    qed
    ultimately show "mulH (mulH h fn) (invgH h) \<in> f ` N" by (by100 simp)
  qed
  show ?thesis unfolding top1_normal_subgroup_on_def
    using hfN_sub hfN_grp hfN_conj by (by100 blast)
qed

text \<open>Normal closure is the least normal subgroup containing a set.\<close>
lemma normal_closure_least:
  assumes "top1_is_group_on G mul e invg"
      and "top1_normal_subgroup_on G mul e invg N"
      and "S \<subseteq> N"
  shows "top1_normal_subgroup_generated_on G mul e invg S \<subseteq> N"
  unfolding top1_normal_subgroup_generated_on_def
  using assms(2,3) by (by100 blast)

text \<open>Quotient group universal property: a homomorphism whose kernel contains N
  factors uniquely through G/N.\<close>
lemma quotient_group_universal_property:
  assumes "top1_is_group_on G mul e invg"
      and "top1_normal_subgroup_on G mul e invg N"
      and "top1_is_group_on H mulH eH invgH"
      and "top1_group_hom_on G mul H mulH f"
      and "N \<subseteq> top1_group_kernel_on G eH f"
  shows "\<exists>fbar. top1_group_hom_on (top1_quotient_group_carrier_on G mul N)
      (top1_quotient_group_mul_on mul) H mulH fbar
    \<and> (\<forall>g\<in>G. fbar (top1_group_coset_on G mul N g) = f g)"
proof -
  let ?coset = "\<lambda>g. top1_group_coset_on G mul N g"
  let ?Q = "top1_quotient_group_carrier_on G mul N"
  let ?mulQ = "top1_quotient_group_mul_on mul"
  \<comment> \<open>Define fbar: for coset C, pick representative g and return f(g).\<close>
  define fbar where "fbar = (\<lambda>C. f (SOME g. g \<in> G \<and> C = ?coset g))"
  \<comment> \<open>Well-defined: if ?coset g = ?coset h then f g = f h.\<close>
  have hwd: "\<forall>g\<in>G. \<forall>h\<in>G. ?coset g = ?coset h \<longrightarrow> f g = f h"
  proof (intro ballI impI)
    fix g h assume hg: "g \<in> G" and hh: "h \<in> G" and heq: "?coset g = ?coset h"
    have "mul (invg g) h \<in> N"
      using normal_coset_eq[OF assms(1,2) hg hh] heq by (by100 blast)
    hence "mul (invg g) h \<in> top1_group_kernel_on G eH f" using assms(5) by (by100 blast)
    hence "f (mul (invg g) h) = eH" unfolding top1_group_kernel_on_def by (by100 blast)
    moreover have hinvgG: "invg g \<in> G"
      using assms(1) hg unfolding top1_is_group_on_def by (by100 blast)
    moreover have "f (mul (invg g) h) = mulH (f (invg g)) (f h)"
      using assms(4) hinvgG hh unfolding top1_group_hom_on_def by (by100 blast)
    ultimately have "mulH (f (invg g)) (f h) = eH" by (by100 simp)
    \<comment> \<open>f(invg g) is the H-inverse of f(g): f(g\<cdot>invg(g))=f(e)=eH, so f(invg g) = invgH(f(g)).\<close>
    have hfg_H: "f g \<in> H" using assms(4) hg unfolding top1_group_hom_on_def by (by100 blast)
    have hfh_H: "f h \<in> H" using assms(4) hh unfolding top1_group_hom_on_def by (by100 blast)
    have hfinvg_H: "f (invg g) \<in> H" using assms(4) hinvgG unfolding top1_group_hom_on_def by (by100 blast)
    have hf_mul: "\<And>x y. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> f (mul x y) = mulH (f x) (f y)"
      using assms(4) unfolding top1_group_hom_on_def by (by100 blast)
    have "mulH (f g) (f (invg g)) = f (mul g (invg g))"
      using hf_mul[OF hg hinvgG] by (by100 simp)
    also have "mul g (invg g) = e" using assms(1) hg unfolding top1_is_group_on_def by (by100 blast)
    also have "f e = eH"
    proof -
      have he_G: "e \<in> G" using assms(1) unfolding top1_is_group_on_def by (by100 blast)
      have "mulH (f e) (f e) = f (mul e e)" using hf_mul[OF he_G he_G] by (by100 simp)
      also have "mul e e = e" using assms(1) unfolding top1_is_group_on_def by (by100 blast)
      finally have "mulH (f e) (f e) = f e" .
      have hfe_H: "f e \<in> H" using assms(4) he_G unfolding top1_group_hom_on_def by (by100 blast)
      \<comment> \<open>Idempotent in group = identity: a\<cdot>a=a implies a=e.\<close>
      have "mulH eH (f e) = f e" using assms(3) hfe_H unfolding top1_is_group_on_def by (by100 blast)
      have "mulH (invgH (f e)) (f e) = eH" using assms(3) hfe_H unfolding top1_is_group_on_def by (by100 blast)
      have "f e = mulH eH (f e)" using \<open>mulH eH (f e) = f e\<close> by (by100 simp)
      also have "\<dots> = mulH (mulH (invgH (f e)) (f e)) (f e)"
        using \<open>mulH (invgH (f e)) (f e) = eH\<close> by (by100 simp)
      also have "\<dots> = mulH (invgH (f e)) (mulH (f e) (f e))"
      proof -
        have "invgH (f e) \<in> H" using assms(3) hfe_H unfolding top1_is_group_on_def by (by100 blast)
        thus ?thesis using assms(3) \<open>invgH (f e) \<in> H\<close> hfe_H unfolding top1_is_group_on_def by (by100 blast)
      qed
      also have "\<dots> = mulH (invgH (f e)) (f e)" using \<open>mulH (f e) (f e) = f e\<close> by (by100 simp)
      also have "\<dots> = eH" using \<open>mulH (invgH (f e)) (f e) = eH\<close> .
      finally show "f e = eH" .
    qed
    finally have "mulH (f g) (f (invg g)) = eH" .
    \<comment> \<open>From mulH(f(invg g))(f h) = eH and mulH(f g)(f(invg g)) = eH:
       f(invg g) = invgH(f g), so f h = f g.\<close>
    show "f g = f h"
    proof -
      \<comment> \<open>From mulH(f g)(f(invg g)) = eH: f(invg g) = invgH(f g).\<close>
      have hH_id: "\<And>x. x \<in> H \<Longrightarrow> mulH eH x = x"
        using assms(3) unfolding top1_is_group_on_def by (by100 blast)
      have hH_assoc: "\<And>x y z. x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> z \<in> H \<Longrightarrow> mulH (mulH x y) z = mulH x (mulH y z)"
        using assms(3) unfolding top1_is_group_on_def by (by100 blast)
      have hH_rid: "\<And>x. x \<in> H \<Longrightarrow> mulH x eH = x"
        using assms(3) unfolding top1_is_group_on_def by (by100 blast)
      have "f h = mulH eH (f h)" using hH_id[OF hfh_H] by (by100 simp)
      also have "\<dots> = mulH (mulH (f g) (f (invg g))) (f h)"
        using \<open>mulH (f g) (f (invg g)) = eH\<close> by (by100 simp)
      also have "\<dots> = mulH (f g) (mulH (f (invg g)) (f h))"
        using hH_assoc[OF hfg_H hfinvg_H hfh_H] by (by100 simp)
      also have "\<dots> = mulH (f g) eH"
        using \<open>mulH (f (invg g)) (f h) = eH\<close> by (by100 simp)
      also have "\<dots> = f g" using hH_rid[OF hfg_H] by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
  qed
  have hfbar_eq: "\<forall>g\<in>G. fbar (?coset g) = f g"
  proof (intro ballI)
    fix g assume hg: "g \<in> G"
    \<comment> \<open>fbar(coset g) = f(SOME g'. g' \<in> G \<and> coset g = coset g').\<close>
    let ?rep = "SOME g'. g' \<in> G \<and> ?coset g = ?coset g'"
    have "?rep \<in> G \<and> ?coset g = ?coset ?rep"
    proof (rule someI[of "\<lambda>g'. g' \<in> G \<and> ?coset g = ?coset g'"])
      show "g \<in> G \<and> ?coset g = ?coset g" using hg by (by100 blast)
    qed
    hence hrep_G: "?rep \<in> G" and hrep_eq: "?coset g = ?coset ?rep" by (by100 blast)+
    show "fbar (?coset g) = f g"
      unfolding fbar_def using hwd hrep_G hg hrep_eq by (by100 blast)
  qed
  have hfbar_hom: "top1_group_hom_on ?Q ?mulQ H mulH fbar"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    \<comment> \<open>fbar maps Q into H.\<close>
    fix C assume "C \<in> ?Q"
    then obtain g where hg: "g \<in> G" "C = ?coset g"
      unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    have "fbar C = fbar (?coset g)" using hg(2) by (by100 simp)
    also have "\<dots> = f g" using hfbar_eq hg(1) by (by100 blast)
    finally have "fbar C = f g" .
    moreover have "f g \<in> H" using assms(4) hg(1) unfolding top1_group_hom_on_def by (by100 blast)
    ultimately show "fbar C \<in> H" by (by100 simp)
  next
    \<comment> \<open>fbar(C1 \<cdot> C2) = mulH(fbar C1)(fbar C2).\<close>
    fix C1 C2 assume hC1: "C1 \<in> ?Q" and hC2: "C2 \<in> ?Q"
    obtain g1 where hg1: "g1 \<in> G" "C1 = ?coset g1"
      using hC1 unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    obtain g2 where hg2: "g2 \<in> G" "C2 = ?coset g2"
      using hC2 unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    have "?mulQ C1 C2 = ?coset (mul g1 g2)"
      using normal_coset_mul_eq[OF assms(1,2) hg1(1) hg2(1)] hg1(2) hg2(2) by (by100 simp)
    hence "fbar (?mulQ C1 C2) = f (mul g1 g2)"
    proof -
      have "mul g1 g2 \<in> G" using assms(1) hg1(1) hg2(1) unfolding top1_is_group_on_def by (by100 blast)
      have "fbar (?coset (mul g1 g2)) = f (mul g1 g2)" using hfbar_eq \<open>mul g1 g2 \<in> G\<close> by (by100 blast)
      thus ?thesis using \<open>?mulQ C1 C2 = ?coset (mul g1 g2)\<close> by (by100 simp)
    qed
    also have "\<dots> = mulH (f g1) (f g2)"
      using assms(4) hg1(1) hg2(1) unfolding top1_group_hom_on_def by (by100 blast)
    also have "\<dots> = mulH (fbar C1) (fbar C2)"
      using hfbar_eq hg1 hg2 by (by100 simp)
    finally show "fbar (?mulQ C1 C2) = mulH (fbar C1) (fbar C2)" .
  qed
  show ?thesis using hfbar_hom hfbar_eq by (by100 blast)
qed


text \<open>Word product of elements from G stays in G.\<close>
lemma word_product_in_group:
  assumes "top1_is_group_on G mul e invg"
      and "\<forall>i<length ws. fst (ws ! i) \<in> G"
  shows "top1_group_word_product mul e invg ws \<in> G"
  using assms(2)
proof (induct ws)
  case Nil thus ?case using assms(1) unfolding top1_is_group_on_def by (by100 simp)
next
  case (Cons a ws)
  obtain x b where ha: "a = (x, b)" by (cases a) (by100 blast)
  have hx: "x \<in> G" using Cons(2) ha by (by100 force)
  have hws': "\<forall>i<length ws. fst (ws ! i) \<in> G" using Cons(2) by (by100 force)
  have hIH: "top1_group_word_product mul e invg ws \<in> G" by (rule Cons(1)[OF hws'])
  show ?case
  proof (cases b)
    case True
    have "top1_group_word_product mul e invg (a # ws) = mul x (top1_group_word_product mul e invg ws)"
      using ha True by (by100 simp)
    moreover have "mul x (top1_group_word_product mul e invg ws) \<in> G"
      using assms(1) hx hIH unfolding top1_is_group_on_def by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  next
    case False
    have "top1_group_word_product mul e invg (a # ws) = mul (invg x) (top1_group_word_product mul e invg ws)"
      using ha False by (by100 simp)
    moreover have "invg x \<in> G" using assms(1) hx unfolding top1_is_group_on_def by (by100 blast)
    moreover have "mul (invg x) (top1_group_word_product mul e invg ws) \<in> G"
      using assms(1) calculation(2) hIH unfolding top1_is_group_on_def by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
qed

text \<open>Homomorphism distributes over word product.\<close>
lemma hom_word_product:
  assumes hG: "top1_is_group_on G mul e invg"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hhom: "top1_group_hom_on G mul H mulH f"
      and hws: "\<forall>i<length ws. fst (ws ! i) \<in> G"
  shows "f (top1_group_word_product mul e invg ws)
       = top1_group_word_product mulH eH invgH (map (\<lambda>(x,b). (f x, b)) ws)"
  using hws
proof (induction ws)
  case Nil thus ?case using hom_preserves_id[OF hG hH hhom] by (by100 simp)
next
  case (Cons a ws')
  obtain x b where ha: "a = (x, b)" by (cases a) (by100 blast)
  have hx: "x \<in> G" using Cons.prems ha by (by100 force)
  have hws'G: "\<forall>i<length ws'. fst (ws' ! i) \<in> G" using Cons.prems by (by100 force)
  have hIH: "f (top1_group_word_product mul e invg ws')
       = top1_group_word_product mulH eH invgH (map (\<lambda>(x,b). (f x, b)) ws')"
    by (rule Cons.IH[OF hws'G])
  have hprod_G: "top1_group_word_product mul e invg ws' \<in> G"
    by (rule word_product_in_group[OF hG hws'G])
  show ?case
  proof (cases b)
    case True
    have "f (top1_group_word_product mul e invg (a # ws'))
        = f (mul x (top1_group_word_product mul e invg ws'))" using ha True by (by100 simp)
    also have "\<dots> = mulH (f x) (f (top1_group_word_product mul e invg ws'))"
      using hhom hx hprod_G unfolding top1_group_hom_on_def by (by100 blast)
    also have "\<dots> = mulH (f x) (top1_group_word_product mulH eH invgH (map (\<lambda>(x,b). (f x, b)) ws'))"
      using hIH by (by100 simp)
    also have "\<dots> = top1_group_word_product mulH eH invgH (map (\<lambda>(x,b). (f x, b)) (a # ws'))"
      using ha True by (by100 simp)
    finally show ?thesis .
  next
    case False
    have hinvx: "invg x \<in> G" using hG hx unfolding top1_is_group_on_def by (by100 blast)
    have step1: "f (top1_group_word_product mul e invg (a # ws'))
        = f (mul (invg x) (top1_group_word_product mul e invg ws'))" using ha False by (by100 simp)
    have step2: "f (mul (invg x) (top1_group_word_product mul e invg ws'))
        = mulH (f (invg x)) (f (top1_group_word_product mul e invg ws'))"
      using hhom hinvx hprod_G unfolding top1_group_hom_on_def by (by100 blast)
    have step3: "f (invg x) = invgH (f x)" by (rule hom_preserves_inv[OF hG hH hhom hx])
    have step4: "top1_group_word_product mulH eH invgH (map (\<lambda>(x,b). (f x, b)) (a # ws'))
        = mulH (invgH (f x)) (top1_group_word_product mulH eH invgH (map (\<lambda>(x,b). (f x, b)) ws'))"
      using ha False by (by100 simp)
    show ?thesis using step1 step2 step3 step4 hIH by (by100 simp)
  qed
qed

text \<open>Reducedness transfers through maps where equality implies equality.\<close>
lemma reduced_word_transfer:
  assumes htrans: "\<And>s t. s \<in> S \<Longrightarrow> t \<in> S \<Longrightarrow> g s = g t \<Longrightarrow> h s = h t"
      and hin: "\<forall>i<length ws. fst (ws!i) \<in> S"
      and hred: "top1_is_reduced_word (map (\<lambda>(s,b). (h s, b)) ws)"
  shows "top1_is_reduced_word (map (\<lambda>(s,b). (g s, b)) ws)"
  using hin hred
proof (induction ws rule: induct_list012)
  case 1 thus ?case by (by100 simp)
next
  case (2 a) thus ?case by (by100 simp)
next
  case (3 a b ws')
  obtain sa ba sb bb where ha: "a = (sa, ba)" and hb: "b = (sb, bb)"
    by (cases a, cases b) (by100 blast)+
  have hsa: "sa \<in> S" using 3(3) ha by (by100 force)
  have hsb: "sb \<in> S" using 3(3) hb by (by100 force)
  from 3(4) ha hb have hpair: "h sa \<noteq> h sb \<or> ba = bb"
    and hrest: "top1_is_reduced_word (map (\<lambda>(s, b). (h s, b)) (b # ws'))"
    by (by100 simp)+
  have "g sa \<noteq> g sb \<or> ba = bb"
  proof (cases "ba = bb")
    case True thus ?thesis by (by100 blast)
  next
    case False
    hence "h sa \<noteq> h sb" using hpair by (by100 blast)
    hence "g sa \<noteq> g sb"
    proof (rule contrapos_nn)
      assume "g sa = g sb" thus "h sa = h sb" by (rule htrans[OF hsa hsb])
    qed
    thus ?thesis by (by100 blast)
  qed
  have hin_rest: "\<forall>i<length (b # ws'). fst ((b # ws') ! i) \<in> S"
    using 3(3) by (by100 force)
  moreover have "top1_is_reduced_word (map (\<lambda>(s, b). (g s, b)) (b # ws'))"
    by (rule 3(2)[OF hin_rest hrest])
  ultimately show ?case using ha hb
    using \<open>g sa \<noteq> g sb \<or> ba = bb\<close> by (by100 force)
qed

text \<open>Free groups are invariant under group isomorphism: if G is free on S and G \<cong> H,
  then H is free on the image of S.\<close>
lemma free_group_invariant_under_iso:
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
      and "top1_group_iso_on G mul H mulH f"
      and "top1_is_group_on H mulH eH invgH"
  shows "\<exists>\<iota>'. top1_is_free_group_full_on H mulH eH invgH \<iota>' S
    \<and> (\<forall>s\<in>S. \<iota>' s = f (\<iota> s))"
proof -
  \<comment> \<open>Define \<iota>' = f \<circ> \<iota>.\<close>
  define \<iota>' where "\<iota>' s = f (\<iota> s)" for s
  \<comment> \<open>Extract free group properties of G.\<close>
  have hG: "top1_is_group_on G mul e invg"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have h\<iota>_in: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have h\<iota>_inj: "inj_on \<iota> S"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hG_gen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hG_red: "\<And>ws. ws \<noteq> [] \<Longrightarrow>
      top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<Longrightarrow>
      (\<forall>i<length ws. fst (ws!i) \<in> S) \<Longrightarrow>
      top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<noteq> e"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  \<comment> \<open>Extract isomorphism properties.\<close>
  have hf_hom: "top1_group_hom_on G mul H mulH f"
    using assms(2) unfolding top1_group_iso_on_def by (by100 blast)
  have hf_bij: "bij_betw f G H"
    using assms(2) unfolding top1_group_iso_on_def by (by100 blast)
  \<comment> \<open>Part 1: \<iota>' maps S into H.\<close>
  have h1: "\<forall>s\<in>S. \<iota>' s \<in> H"
    unfolding \<iota>'_def using h\<iota>_in hf_bij unfolding bij_betw_def by (by100 blast)
  \<comment> \<open>Part 2: \<iota>' is injective on S (f is injective, \<iota> is injective).\<close>
  have h2: "inj_on \<iota>' S"
    unfolding \<iota>'_def
  proof (rule inj_onI)
    fix x y assume hx: "x \<in> S" and hy: "y \<in> S" and hfeq: "f (\<iota> x) = f (\<iota> y)"
    have "inj_on f G" using hf_bij unfolding bij_betw_def by (by100 blast)
    hence "\<iota> x = \<iota> y" using hfeq h\<iota>_in hx hy unfolding inj_on_def by (by100 blast)
    thus "x = y" using h\<iota>_inj hx hy unfolding inj_on_def by (by100 blast)
  qed
  \<comment> \<open>Part 3: \<iota>'(S) generates H.\<close>
  have h3: "H = top1_subgroup_generated_on H mulH eH invgH (\<iota>' ` S)"
  proof -
    \<comment> \<open>Proof: \<iota>'(S) = f(\<iota>(S)). Since f is surjective and \<iota>(S) generates G,
       f(\<iota>(S)) generates H. Direct argument via subgroup_generated.\<close>
    have h\<iota>'_img: "\<iota>' ` S = f ` (\<iota> ` S)" unfolding \<iota>'_def image_image by (by100 blast)
    have hf_surj: "f ` G = H" using hf_bij unfolding bij_betw_def by (by100 blast)
    have h\<iota>S_sub: "\<iota> ` S \<subseteq> G" using h\<iota>_in by (by100 blast)
    \<comment> \<open>H \<subseteq> \<langle>\<iota>'(S)\<rangle>: every h \<in> H is f(g) for some g \<in> G = \<langle>\<iota>(S)\<rangle>.
       g in every subgroup containing \<iota>(S) \<Rightarrow> f(g) in every subgroup containing f(\<iota>(S)).\<close>
    \<comment> \<open>Inline proof: f surjective + \<iota>(S) generates G \<Rightarrow> f(\<iota>(S)) generates H.\<close>
    have h\<iota>'_sub_H: "\<iota>' ` S \<subseteq> H" using h1 by (by100 blast)
    have hK_sub: "top1_subgroup_generated_on H mulH eH invgH (\<iota>' ` S) \<subseteq> H"
      by (rule subgroup_generated_subset[OF assms(3) h\<iota>'_sub_H])
    show ?thesis
    proof (rule set_eqI, rule iffI)
      fix h assume hh: "h \<in> H"
      obtain g where hg: "g \<in> G" "f g = h" using hh hf_surj by (by100 blast)
      have "f g \<in> top1_subgroup_generated_on H mulH eH invgH (\<iota>' ` S)"
        unfolding top1_subgroup_generated_on_def
      proof (rule InterI, clarify)
        fix K assume hK_cond: "\<iota>' ` S \<subseteq> K" and hK_sub2: "K \<subseteq> H"
            and hK_grp: "top1_is_group_on K mulH eH invgH"
        \<comment> \<open>Preimage f\<inverse>(K) is a subgroup of G containing \<iota>(S).\<close>
        let ?preK = "{g \<in> G. f g \<in> K}"
        have hpreK_grp: "top1_is_group_on ?preK mul e invg"
        proof -
          have hf_e: "f e = eH" by (rule hom_preserves_id[OF hG assms(3) hf_hom])
          have heG: "e \<in> G" using hG unfolding top1_is_group_on_def by (by100 blast)
          have h_e: "e \<in> ?preK" using heG hf_e hK_grp unfolding top1_is_group_on_def by (by100 blast)
          have h_mul: "\<forall>x\<in>?preK. \<forall>y\<in>?preK. mul x y \<in> ?preK"
          proof (intro ballI)
            fix x y assume hx: "x \<in> ?preK" and hy: "y \<in> ?preK"
            have "mul x y \<in> G" using hG hx hy unfolding top1_is_group_on_def by (by100 blast)
            moreover have "f (mul x y) = mulH (f x) (f y)"
              using hf_hom hx hy unfolding top1_group_hom_on_def by (by100 blast)
            moreover have "mulH (f x) (f y) \<in> K"
              using hK_grp hx hy unfolding top1_is_group_on_def by (by100 blast)
            ultimately have "mul x y \<in> G" "f (mul x y) \<in> K" by (by100 simp)+
            thus "mul x y \<in> ?preK" by (by100 blast)
          qed
          have h_inv: "\<forall>x\<in>?preK. invg x \<in> ?preK"
          proof (intro ballI)
            fix x assume hx: "x \<in> ?preK"
            have hxG: "x \<in> G" using hx by (by100 blast)
            have "invg x \<in> G" using hG hxG unfolding top1_is_group_on_def by (by100 blast)
            moreover have "f (invg x) = invgH (f x)"
              by (rule hom_preserves_inv[OF hG assms(3) hf_hom hxG])
            moreover have "invgH (f x) \<in> K"
              using hK_grp hx unfolding top1_is_group_on_def by (by100 blast)
            ultimately have "invg x \<in> G" "f (invg x) \<in> K" by (by100 simp)+
            thus "invg x \<in> ?preK" by (by100 blast)
          qed
          have h_assoc: "\<forall>x\<in>?preK. \<forall>y\<in>?preK. \<forall>z\<in>?preK. mul (mul x y) z = mul x (mul y z)"
            using hG unfolding top1_is_group_on_def by (by100 blast)
          have h_id: "\<forall>x\<in>?preK. mul e x = x \<and> mul x e = x"
            using hG unfolding top1_is_group_on_def by (by100 blast)
          have h_invax: "\<forall>x\<in>?preK. mul (invg x) x = e \<and> mul x (invg x) = e"
            using hG unfolding top1_is_group_on_def by (by100 blast)
          show ?thesis unfolding top1_is_group_on_def
            using h_e h_mul h_inv h_assoc h_id h_invax by (by100 blast)
        qed
        have h\<iota>S_preK: "\<iota> ` S \<subseteq> ?preK"
          using h\<iota>S_sub hK_cond unfolding \<iota>'_def by (by100 blast)
        have hpreK_sub: "?preK \<subseteq> G" by (by100 blast)
        have "top1_subgroup_generated_on G mul e invg (\<iota> ` S) \<subseteq> ?preK"
          by (rule subgroup_generated_minimal[OF h\<iota>S_preK hpreK_sub hpreK_grp])
        hence "g \<in> ?preK" using hg(1) hG_gen by (by100 blast)
        thus "f g \<in> K" by (by100 blast)
      qed
      thus "h \<in> top1_subgroup_generated_on H mulH eH invgH (\<iota>' ` S)"
        using hg(2) by (by100 simp)
    next
      fix h assume "h \<in> top1_subgroup_generated_on H mulH eH invgH (\<iota>' ` S)"
      thus "h \<in> H" using hK_sub by (by100 blast)
    qed
  qed
  \<comment> \<open>Part 4: No nontrivial reduced word in \<iota>'(S) evaluates to eH.\<close>
  have h4: "\<And>ws. ws \<noteq> [] \<Longrightarrow>
      top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>' s, b)) ws) \<Longrightarrow>
      (\<forall>i<length ws. fst (ws!i) \<in> S) \<Longrightarrow>
      top1_group_word_product mulH eH invgH (map (\<lambda>(s, b). (\<iota>' s, b)) ws) \<noteq> eH"
  proof -
    fix ws assume hne: "ws \<noteq> []"
      and hred: "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota>' s, b)) ws)"
      and hin: "\<forall>i<length ws. fst (ws!i) \<in> S"
    \<comment> \<open>Reducedness of \<iota>'(ws) implies reducedness of \<iota>(ws) since f\<circ>\<iota> is injective.\<close>
    have hred_G: "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws)"
    proof (rule reduced_word_transfer[OF _ hin hred])
      fix s t assume "s \<in> S" "t \<in> S" "\<iota> s = \<iota> t"
      thus "\<iota>' s = \<iota>' t" unfolding \<iota>'_def by (by100 simp)
    qed
    \<comment> \<open>Product in H = f(product in G) by homomorphism.\<close>
    have hf_e: "f e = eH" by (rule hom_preserves_id[OF hG assms(3) hf_hom])
    have hprod: "top1_group_word_product mulH eH invgH (map (\<lambda>(s, b). (\<iota>' s, b)) ws)
        = f (top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota> s, b)) ws))"
    proof -
      \<comment> \<open>The mapped words are equal: map (ι'×id) ws = map (f×id) (map (ι×id) ws).\<close>
      have hmap_eq: "map (\<lambda>(s, b). (\<iota>' s, b)) ws = map (\<lambda>(x, b). (f x, b)) (map (\<lambda>(s, b). (\<iota> s, b)) ws)"
      proof (rule nth_equalityI)
        show "length (map (\<lambda>(s, b). (\<iota>' s, b)) ws) = length (map (\<lambda>(x, b). (f x, b)) (map (\<lambda>(s, b). (\<iota> s, b)) ws))"
          by (by100 simp)
      next
        fix i assume "i < length (map (\<lambda>(s, b). (\<iota>' s, b)) ws)"
        hence hi: "i < length ws" by (by100 simp)
        obtain si bi where hwi: "ws ! i = (si, bi)" by (cases "ws ! i") (by100 blast)
        show "(map (\<lambda>(s, b). (\<iota>' s, b)) ws) ! i = (map (\<lambda>(x, b). (f x, b)) (map (\<lambda>(s, b). (\<iota> s, b)) ws)) ! i"
          using hi hwi unfolding \<iota>'_def by (by100 simp)
      qed
      have hws_G: "\<forall>i<length (map (\<lambda>(s, b). (\<iota> s, b)) ws). fst ((map (\<lambda>(s, b). (\<iota> s, b)) ws) ! i) \<in> G"
      proof (intro allI impI)
        fix i assume hi: "i < length (map (\<lambda>(s, b). (\<iota> s, b)) ws)"
        obtain si bi where hwi: "ws ! i = (si, bi)" by (cases "ws ! i") (by100 blast)
        have "si \<in> S" using hin hi hwi by (by100 force)
        thus "fst ((map (\<lambda>(s, b). (\<iota> s, b)) ws) ! i) \<in> G" using h\<iota>_in hi hwi by (by100 simp)
      qed
      show ?thesis unfolding hmap_eq
        by (rule hom_word_product[OF hG assms(3) hf_hom hws_G, symmetric])
    qed
    \<comment> \<open>If product = eH, then f(product in G) = eH, so product in G = e (f injective).\<close>
    show "top1_group_word_product mulH eH invgH (map (\<lambda>(s, b). (\<iota>' s, b)) ws) \<noteq> eH"
    proof
      assume heq: "top1_group_word_product mulH eH invgH (map (\<lambda>(s, b). (\<iota>' s, b)) ws) = eH"
      have "f (top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota> s, b)) ws)) = eH"
        using heq hprod by (by100 simp)
      moreover have "f e = eH" by (rule hf_e)
      ultimately have "top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota> s, b)) ws) = e"
      proof -
        assume h1: "f (top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota> s, b)) ws)) = eH"
           and h2: "f e = eH"
        have "f (top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota> s, b)) ws)) = f e"
          using h1 h2 by (by100 simp)
        moreover have "inj_on f G" using hf_bij unfolding bij_betw_def by (by100 blast)
        moreover have "top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<in> G"
        proof (rule word_product_in_group[OF hG])
          show "\<forall>i<length (map (\<lambda>(s, b). (\<iota> s, b)) ws). fst (map (\<lambda>(s, b). (\<iota> s, b)) ws ! i) \<in> G"
          proof (intro allI impI)
            fix i assume hi: "i < length (map (\<lambda>(s, b). (\<iota> s, b)) ws)"
            obtain si bi where hwi: "ws ! i = (si, bi)" by (cases "ws ! i") (by100 blast)
            have hsi: "si \<in> S" using hin hi hwi by (by100 force)
            show "fst (map (\<lambda>(s, b). (\<iota> s, b)) ws ! i) \<in> G"
              using hi hwi h\<iota>_in hsi by (by100 simp)
          qed
        qed
        moreover have "e \<in> G" using hG unfolding top1_is_group_on_def by (by100 blast)
        ultimately show ?thesis unfolding inj_on_def by (by100 blast)
      qed
      thus False using hG_red[OF hne hred_G hin] by (by100 blast)
    qed
  qed
  \<comment> \<open>Combine into free group definition.\<close>
  have "top1_is_free_group_full_on H mulH eH invgH \<iota>' S"
    unfolding top1_is_free_group_full_on_def
    using assms(3) h1 h2 h3 h4 by (by100 blast)
  moreover have "\<forall>s\<in>S. \<iota>' s = f (\<iota> s)" unfolding \<iota>'_def by (by100 blast)
  ultimately show ?thesis by (by100 blast)
qed


section \<open>\<S>69 Free Groups\<close>

text \<open>Helper: surjective homomorphism preserves "generated by" property.
  If G = \<langle>S\<rangle> and \<phi>: G \<twoheadrightarrow> H is a surjective homomorphism, then H = \<langle>\<phi>(S)\<rangle>.\<close>
lemma surj_hom_generated:
  assumes hG_grp: "top1_is_group_on G mulG eG invgG"
      and hH_grp: "top1_is_group_on H mulH eH invgH"
      and hhom: "top1_group_hom_on G mulG H mulH \<phi>"
      and hsurj: "\<phi> ` G = H"
      and hS_sub: "S \<subseteq> G"
      and hG_gen: "G = top1_subgroup_generated_on G mulG eG invgG S"
  shows "H = top1_subgroup_generated_on H mulH eH invgH (\<phi> ` S)"
proof -
  have hphiS_sub_H: "\<phi> ` S \<subseteq> H"
  proof (intro image_subsetI)
    fix s assume "s \<in> S"
    hence "s \<in> G" using hS_sub by (by100 blast)
    thus "\<phi> s \<in> H" using hhom unfolding top1_group_hom_on_def by (by100 blast)
  qed
  have hK_sub_H: "top1_subgroup_generated_on H mulH eH invgH (\<phi> ` S) \<subseteq> H"
    by (rule subgroup_generated_subset[OF hH_grp hphiS_sub_H])
  show ?thesis
  proof (rule set_eqI, rule iffI)
  fix h assume hh: "h \<in> H"
  \<comment> \<open>H \<subseteq> \<langle>\<phi>(S)\<rangle>.\<close>
  let ?K = "top1_subgroup_generated_on H mulH eH invgH (\<phi> ` S)"
  \<comment> \<open>g \<in> G = \<langle>S\<rangle> means g is in every subgroup containing S.\<close>
  obtain g where hg: "g \<in> G" and hphi_g: "\<phi> g = h"
    using hh hsurj by (by100 blast)
  have "g \<in> G" by (rule hg)
  \<comment> \<open>g \<in> \<langle>S\<rangle> = G, so g is in the intersection of all subgroups containing S.
     We need \<phi>(g) \<in> ?K. By definition, ?K is the intersection of all subgroups
     of H containing \<phi>(S). It suffices to show \<phi>(g) \<in> every subgroup of H
     containing \<phi>(S).\<close>
  have "\<phi> g \<in> ?K"
    unfolding top1_subgroup_generated_on_def
  proof (rule InterI, clarify)
    fix K assume hK_cond: "\<phi> ` S \<subseteq> K" and hK_sub: "K \<subseteq> H"
        and hK_grp: "top1_is_group_on K mulH eH invgH"
    \<comment> \<open>The preimage \<phi>\<inverse>(K) is a subgroup of G containing S.\<close>
    let ?preK = "{g \<in> G. \<phi> g \<in> K}"
    have hpreK_grp: "top1_is_group_on ?preK mulG eG invgG"
    proof -
      \<comment> \<open>Identity: eG \<in> G and \<phi>(eG) = eH \<in> K.\<close>
      have heG: "eG \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      have hphi_eG: "\<phi> eG = eH" by (rule hom_preserves_id[OF hG_grp hH_grp hhom])
      have h1: "eG \<in> ?preK" using heG hphi_eG hK_grp unfolding top1_is_group_on_def by (by100 blast)
      \<comment> \<open>Closure.\<close>
      have h2: "\<forall>x\<in>?preK. \<forall>y\<in>?preK. mulG x y \<in> ?preK"
      proof (intro ballI)
        fix x y assume hx: "x \<in> ?preK" and hy: "y \<in> ?preK"
        have hxG: "x \<in> G" using hx by (by100 blast)
        have hyG: "y \<in> G" using hy by (by100 blast)
        have hmulG: "mulG x y \<in> G" using hG_grp hxG hyG unfolding top1_is_group_on_def by (by100 blast)
        have "\<phi> (mulG x y) = mulH (\<phi> x) (\<phi> y)" using hhom hxG hyG unfolding top1_group_hom_on_def by (by100 blast)
        also have "mulH (\<phi> x) (\<phi> y) \<in> K" using hK_grp hx hy unfolding top1_is_group_on_def by (by100 blast)
        finally have "\<phi> (mulG x y) \<in> K" .
        thus "mulG x y \<in> ?preK" using hmulG by (by100 blast)
      qed
      \<comment> \<open>Inverse.\<close>
      have h3: "\<forall>x\<in>?preK. invgG x \<in> ?preK"
      proof (intro ballI)
        fix x assume hx: "x \<in> ?preK"
        have hxG: "x \<in> G" using hx by (by100 blast)
        have hinvG: "invgG x \<in> G" using hG_grp hxG unfolding top1_is_group_on_def by (by100 blast)
        have "\<phi> (invgG x) = invgH (\<phi> x)" by (rule hom_preserves_inv[OF hG_grp hH_grp hhom hxG])
        also have "invgH (\<phi> x) \<in> K" using hK_grp hx unfolding top1_is_group_on_def by (by100 blast)
        finally have "\<phi> (invgG x) \<in> K" .
        thus "invgG x \<in> ?preK" using hinvG by (by100 blast)
      qed
      \<comment> \<open>Group axioms (associativity, identity, inverse) follow from G.\<close>
      have h4: "\<forall>x\<in>?preK. \<forall>y\<in>?preK. \<forall>z\<in>?preK. mulG (mulG x y) z = mulG x (mulG y z)"
        using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      have h5: "\<forall>x\<in>?preK. mulG eG x = x \<and> mulG x eG = x"
        using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      have h6: "\<forall>x\<in>?preK. mulG (invgG x) x = eG \<and> mulG x (invgG x) = eG"
        using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      show ?thesis unfolding top1_is_group_on_def using h1 h2 h3 h4 h5 h6 by (by100 blast)
    qed
    have hS_preK: "S \<subseteq> ?preK" using hS_sub hK_cond by (by100 blast)
    have hpreK_subG: "?preK \<subseteq> G" by (by100 blast)
    have "top1_subgroup_generated_on G mulG eG invgG S \<subseteq> ?preK"
      by (rule subgroup_generated_minimal[OF hS_preK hpreK_subG hpreK_grp])
    hence "g \<in> ?preK" using hg hG_gen by (by100 blast)
    thus "\<phi> g \<in> K" by (by100 blast)
  qed
  thus "h \<in> ?K" using hphi_g by (by100 simp)
next
  fix h assume "h \<in> top1_subgroup_generated_on H mulH eH invgH (\<phi> ` S)"
  thus "h \<in> H"
    using hK_sub_H by (by100 blast)
  qed
qed

text \<open>Universal property of free groups: for any group H and function \<phi>: S \<rightarrow> H,
  there exists a unique homomorphism \<psi>: G \<rightarrow> H extending \<phi>.
  This follows from the free group axioms: G = \<langle>\<iota>(S)\<rangle> (generation) and
  no nontrivial reduced word is identity (freeness). Together, they ensure
  that any function on generators extends uniquely to a homomorphism.\<close>
text \<open>Uniqueness: any two homomorphisms G \<rightarrow> H agreeing on \<iota>(S) agree on all of G.
  Proof: {g \<in> G. \<psi>1(g) = \<psi>2(g)} is a subgroup containing \<iota>(S), hence = G.\<close>
lemma free_group_hom_unique:
  assumes hG: "top1_is_group_on G mul e invg"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hgen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
      and hS: "\<forall>s\<in>S. \<iota> s \<in> G"
      and h1: "top1_group_hom_on G mul H mulH \<psi>1"
      and h2: "top1_group_hom_on G mul H mulH \<psi>2"
      and hagree: "\<forall>s\<in>S. \<psi>1 (\<iota> s) = \<psi>2 (\<iota> s)"
  shows "\<forall>g\<in>G. \<psi>1 g = \<psi>2 g"
proof -
  \<comment> \<open>The agreement set A = {g \<in> G. \<psi>1(g) = \<psi>2(g)} is a subgroup containing \<iota>(S).\<close>
  let ?A = "{g \<in> G. \<psi>1 g = \<psi>2 g}"
  have hA_grp: "top1_is_group_on ?A mul e invg"
  proof -
    \<comment> \<open>Identity: \<psi>1(e) = eH = \<psi>2(e).\<close>
    have he_A: "e \<in> ?A"
    proof -
      have "e \<in> G" using hG unfolding top1_is_group_on_def by (by100 blast)
      moreover have "\<psi>1 e = eH" by (rule hom_preserves_id[OF hG hH h1])
      moreover have "\<psi>2 e = eH" by (rule hom_preserves_id[OF hG hH h2])
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Closure: if \<psi>1(g1) = \<psi>2(g1) and \<psi>1(g2) = \<psi>2(g2), then
       \<psi>1(g1\<cdot>g2) = \<psi>1(g1)\<cdot>\<psi>1(g2) = \<psi>2(g1)\<cdot>\<psi>2(g2) = \<psi>2(g1\<cdot>g2).\<close>
    have hclos: "\<forall>x\<in>?A. \<forall>y\<in>?A. mul x y \<in> ?A"
    proof (intro ballI)
      fix x y assume hx: "x \<in> ?A" and hy: "y \<in> ?A"
      have hxG: "x \<in> G" and hyG: "y \<in> G" using hx hy by (by100 blast)+
      have hmul: "mul x y \<in> G" using hG hxG hyG unfolding top1_is_group_on_def by (by100 blast)
      have "\<psi>1 (mul x y) = mulH (\<psi>1 x) (\<psi>1 y)"
        using h1 hxG hyG unfolding top1_group_hom_on_def by (by100 blast)
      also have "\<dots> = mulH (\<psi>2 x) (\<psi>2 y)"
      proof -
        have "\<psi>1 x = \<psi>2 x" using hx by (by100 blast)
        moreover have "\<psi>1 y = \<psi>2 y" using hy by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      also have "\<dots> = \<psi>2 (mul x y)"
        using h2 hxG hyG unfolding top1_group_hom_on_def by (by100 simp)
      finally show "mul x y \<in> ?A" using hmul by (by100 blast)
    qed
    \<comment> \<open>Inverse: if \<psi>1(g) = \<psi>2(g), then \<psi>1(g^{-1}) = \<psi>1(g)^{-1} = \<psi>2(g)^{-1} = \<psi>2(g^{-1}).\<close>
    have hinv: "\<forall>x\<in>?A. invg x \<in> ?A"
    proof (intro ballI)
      fix x assume hx: "x \<in> ?A"
      have hxG: "x \<in> G" using hx by (by100 blast)
      have hinvG: "invg x \<in> G" using hG hxG unfolding top1_is_group_on_def by (by100 blast)
      have "\<psi>1 (invg x) = invgH (\<psi>1 x)" by (rule hom_preserves_inv[OF hG hH h1 hxG])
      also have "\<dots> = invgH (\<psi>2 x)"
      proof -
        have "\<psi>1 x = \<psi>2 x" using hx by (by100 blast)
        thus ?thesis by (by100 simp)
      qed
      also have "\<dots> = \<psi>2 (invg x)" using hom_preserves_inv[OF hG hH h2 hxG] by (by100 simp)
      finally show "invg x \<in> ?A" using hinvG by (by100 blast)
    qed
    \<comment> \<open>Group axioms from G.\<close>
    have hassoc: "\<forall>x\<in>?A. \<forall>y\<in>?A. \<forall>z\<in>?A. mul (mul x y) z = mul x (mul y z)"
      using hG unfolding top1_is_group_on_def by (by100 blast)
    have hid: "\<forall>x\<in>?A. mul e x = x \<and> mul x e = x"
      using hG unfolding top1_is_group_on_def by (by100 blast)
    have hinvax: "\<forall>x\<in>?A. mul (invg x) x = e \<and> mul x (invg x) = e"
      using hG unfolding top1_is_group_on_def by (by100 blast)
    show ?thesis unfolding top1_is_group_on_def
      using he_A hclos hinv hassoc hid hinvax by (by100 blast)
  qed
  \<comment> \<open>\<iota>(S) \<subseteq> A.\<close>
  have hS_A: "\<iota> ` S \<subseteq> ?A" using hS hagree by (by100 blast)
  \<comment> \<open>A \<subseteq> G.\<close>
  have hA_G: "?A \<subseteq> G" by (by100 blast)
  \<comment> \<open>G = \<langle>\<iota>(S)\<rangle> \<subseteq> A (since A is a subgroup containing \<iota>(S)).\<close>
  have "top1_subgroup_generated_on G mul e invg (\<iota> ` S) \<subseteq> ?A"
    by (rule subgroup_generated_minimal[OF hS_A hA_G hA_grp])
  hence "G \<subseteq> ?A" using hgen by (by100 simp)
  thus ?thesis by (by100 blast)
qed


text \<open>Word product distributes over list append.\<close>
lemma word_product_append:
  assumes hG: "top1_is_group_on G mul e invg"
      and hxs: "\<forall>i<length xs. fst (xs ! i) \<in> G"
      and hys: "\<forall>i<length ys. fst (ys ! i) \<in> G"
  shows "top1_group_word_product mul e invg (xs @ ys)
       = mul (top1_group_word_product mul e invg xs) (top1_group_word_product mul e invg ys)"
  using hxs
proof (induct xs)
  case Nil
  have "top1_group_word_product mul e invg ys \<in> G"
    by (rule word_product_in_group[OF hG hys])
  thus ?case using hG unfolding top1_is_group_on_def by (by100 simp)
next
  case (Cons a xs)
  obtain x b where ha: "a = (x, b)" by (cases a) (by100 blast)
  have hx_G: "x \<in> G" using Cons(2) ha by (by100 force)
  have hxs': "\<forall>i<length xs. fst (xs ! i) \<in> G"
    using Cons(2) by (by100 force)
  have hIH: "top1_group_word_product mul e invg (xs @ ys) =
      mul (top1_group_word_product mul e invg xs) (top1_group_word_product mul e invg ys)"
    by (rule Cons(1)[OF hxs'])
  have hwp_xs_G: "top1_group_word_product mul e invg xs \<in> G"
    by (rule word_product_in_group[OF hG hxs'])
  have hwp_ys_G: "top1_group_word_product mul e invg ys \<in> G"
    by (rule word_product_in_group[OF hG hys])
  have hassoc: "\<And>a b c. a \<in> G \<Longrightarrow> b \<in> G \<Longrightarrow> c \<in> G \<Longrightarrow>
      mul (mul a b) c = mul a (mul b c)"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  show ?case
  proof (cases b)
    case True
    have "top1_group_word_product mul e invg ((a # xs) @ ys)
        = mul x (top1_group_word_product mul e invg (xs @ ys))"
      using ha True by (by100 simp)
    also have "\<dots> = mul x (mul (top1_group_word_product mul e invg xs)
        (top1_group_word_product mul e invg ys))" using hIH by (by100 simp)
    also have "\<dots> = mul (mul x (top1_group_word_product mul e invg xs))
        (top1_group_word_product mul e invg ys)"
      using hassoc[OF hx_G hwp_xs_G hwp_ys_G] by (by100 simp)
    finally show ?thesis using ha True by (by100 simp)
  next
    case False
    have hinvx_G: "invg x \<in> G" using hG hx_G unfolding top1_is_group_on_def by (by100 blast)
    have "top1_group_word_product mul e invg ((a # xs) @ ys)
        = mul (invg x) (top1_group_word_product mul e invg (xs @ ys))"
      using ha False by (by100 simp)
    also have "\<dots> = mul (invg x) (mul (top1_group_word_product mul e invg xs)
        (top1_group_word_product mul e invg ys))" using hIH by (by100 simp)
    also have "\<dots> = mul (mul (invg x) (top1_group_word_product mul e invg xs))
        (top1_group_word_product mul e invg ys)"
      using hassoc[OF hinvx_G hwp_xs_G hwp_ys_G] by (by100 simp)
    finally show ?thesis using ha False by (by100 simp)
  qed
qed

text \<open>Removing a cancellable pair from a word preserves group\_word\_product in any group.\<close>
lemma word_cancel_preserves_eval:
  assumes hG: "top1_is_group_on G mul e invg"
      and hi: "i + 1 < length ws"
      and hfst: "fst (ws ! i) = fst (ws ! (i+1))"
      and hsnd: "snd (ws ! i) \<noteq> snd (ws ! (i+1))"
      and hws_G: "\<forall>j<length ws. fst (ws ! j) \<in> G"
  shows "top1_group_word_product mul e invg ws
       = top1_group_word_product mul e invg (take i ws @ drop (i+2) ws)"
proof -
  let ?pre = "take i ws"
  let ?suf = "drop (i+2) ws"
  let ?pair = "[ws ! i, ws ! (i+1)]"
  \<comment> \<open>ws = pre @ pair @ suf\<close>
  have hws_split: "ws = ?pre @ ?pair @ ?suf"
  proof -
    have hi1: "i < length ws" using hi by (by100 simp)
    have hi2: "i + 1 < length ws" using hi by (by100 simp)
    have "ws = take (i+2) ws @ drop (i+2) ws" by (by100 simp)
    moreover have "take (i+2) ws = take i ws @ [ws!i, ws!(i+1)]"
    proof -
      have hsi: "Suc i < length ws" using hi by (by100 simp)
      have "take (Suc (Suc i)) ws = take (Suc i) ws @ [ws ! (Suc i)]"
        by (rule take_Suc_conv_app_nth) (rule hsi)
      moreover have "take (Suc i) ws = take i ws @ [ws ! i]"
        by (rule take_Suc_conv_app_nth) (rule hi1)
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>The pair evaluates to e: x \<cdot> x\<inverse> = e or x\<inverse> \<cdot> x = e.\<close>
  obtain x where hx: "fst (ws ! i) = x" by (by100 blast)
  have hx_G: "x \<in> G" using hws_G hi hx by (by100 force)
  have hpair_e: "top1_group_word_product mul e invg ?pair = e"
  proof -
    obtain b1 b2 where hb1: "ws ! i = (x, b1)" and hb2: "ws ! (i+1) = (x, b2)"
      using hx hfst by (cases "ws ! i", cases "ws ! (i+1)") (by100 auto)
    have "b1 \<noteq> b2" using hsnd hb1 hb2 by (by100 simp)
    show ?thesis
    proof (cases b1)
      case True
      hence "b2 = False" using \<open>b1 \<noteq> b2\<close> by (by100 simp)
      hence "?pair = [(x, True), (x, False)]" using hb1 hb2 True by (by100 simp)
      thus ?thesis using hG hx_G unfolding top1_is_group_on_def by (by100 simp)
    next
      case False
      hence "b2 = True" using \<open>b1 \<noteq> b2\<close> by (by100 simp)
      hence "?pair = [(x, False), (x, True)]" using hb1 hb2 False by (by100 simp)
      thus ?thesis using hG hx_G unfolding top1_is_group_on_def by (by100 simp)
    qed
  qed
  \<comment> \<open>pre elements in G\<close>
  have hpre_G: "\<forall>j<length ?pre. fst (?pre ! j) \<in> G"
    using hws_G by (by100 force)
  have hpair_G: "\<forall>j<length ?pair. fst (?pair ! j) \<in> G"
  proof (intro allI impI)
    fix j assume "j < length ?pair"
    hence "j = 0 \<or> j = 1" by (by100 auto)
    thus "fst (?pair ! j) \<in> G"
      using hx_G hx hfst hws_G hi by (by100 auto)
  qed
  have hsuf_G: "\<forall>j<length ?suf. fst (?suf ! j) \<in> G"
    using hws_G by (by100 force)
  have hpairsuf_G: "\<forall>j<length (?pair @ ?suf). fst ((?pair @ ?suf) ! j) \<in> G"
  proof (intro allI impI)
    fix j assume hj: "j < length (?pair @ ?suf)"
    show "fst ((?pair @ ?suf) ! j) \<in> G"
    proof (cases "j < length ?pair")
      case True thus ?thesis using hpair_G nth_append[of ?pair ?suf j] by (by100 simp)
    next
      case False
      hence hjm: "j - length ?pair < length ?suf" using hj by (by100 simp)
      have hjlen: "j - length ?pair < length ?suf" by (rule hjm)
      have hnth: "fst (?suf ! (j - length ?pair)) \<in> G"
        using hsuf_G hjm by (by100 blast)
      have "(?pair @ ?suf) ! j = ?suf ! (j - length ?pair)"
        using False by (by100 simp)
      hence "fst ((?pair @ ?suf) ! j) = fst (?suf ! (j - length ?pair))" by (by100 simp)
      thus ?thesis using hnth by (by100 simp)
    qed
  qed
  \<comment> \<open>Split and simplify\<close>
  have "top1_group_word_product mul e invg ws
      = top1_group_word_product mul e invg (?pre @ ?pair @ ?suf)"
    using hws_split by (by100 simp)
  also have "\<dots> = mul (top1_group_word_product mul e invg ?pre)
      (top1_group_word_product mul e invg (?pair @ ?suf))"
    by (rule word_product_append[OF hG hpre_G hpairsuf_G])
  also have "top1_group_word_product mul e invg (?pair @ ?suf)
      = mul (top1_group_word_product mul e invg ?pair)
            (top1_group_word_product mul e invg ?suf)"
    by (rule word_product_append[OF hG hpair_G hsuf_G])
  also have "mul (top1_group_word_product mul e invg ?pair)
            (top1_group_word_product mul e invg ?suf) =
      mul e (top1_group_word_product mul e invg ?suf)"
    using hpair_e by (by100 simp)
  also have "\<dots> = top1_group_word_product mul e invg ?suf"
    using hG word_product_in_group[OF hG hsuf_G] unfolding top1_is_group_on_def by (by100 blast)
  finally have "top1_group_word_product mul e invg ws =
      mul (top1_group_word_product mul e invg ?pre) (top1_group_word_product mul e invg ?suf)" .
  also have "\<dots> = top1_group_word_product mul e invg (?pre @ ?suf)"
    by (rule word_product_append[OF hG hpre_G hsuf_G, symmetric])
  finally show ?thesis .
qed

text \<open>A non-reduced word has an adjacent cancellable pair.\<close>
lemma not_reduced_has_cancel:
  "\<not> top1_is_reduced_word xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow>
   \<exists>i. i + 1 < length xs \<and> fst (xs ! i) = fst (xs ! (i+1)) \<and> snd (xs ! i) \<noteq> snd (xs ! (i+1))"
proof (induct xs rule: top1_is_reduced_word.induct)
  case 1 thus ?case by (by100 simp)
next
  case (2 x) thus ?case by (by100 simp)
next
  case (3 x b y c ws)
  \<comment> \<open>is\_reduced\_word ((x,b)#(y,c)#ws) = ((x\<noteq>y \<or> b=c) \<and> is\_reduced\_word ((y,c)#ws))\<close>
  show ?case
  proof (cases "x = y \<and> b \<noteq> c")
    case True
    hence "fst (((x,b) # (y,c) # ws) ! 0) = fst (((x,b) # (y,c) # ws) ! 1)"
      by (by100 simp)
    moreover have "snd (((x,b) # (y,c) # ws) ! 0) \<noteq> snd (((x,b) # (y,c) # ws) ! 1)"
      using True by (by100 simp)
    moreover have "0 + 1 < length ((x,b) # (y,c) # ws)" by (by100 simp)
    ultimately show ?thesis
      apply (rule_tac x=0 in exI) by (by100 simp)
  next
    case False
    hence "x \<noteq> y \<or> b = c" by (by100 blast)
    hence "\<not> top1_is_reduced_word ((y,c) # ws)"
      using 3(2) by (by100 simp)
    from 3(1)[OF this]
    obtain j where hj: "j + 1 < length ((y,c) # ws)"
        and hfj: "fst (((y,c)#ws) ! j) = fst (((y,c)#ws) ! (j+1))"
        and hsj: "snd (((y,c)#ws) ! j) \<noteq> snd (((y,c)#ws) ! (j+1))"
      by (by100 blast)
    have "(j+1) + 1 < length ((x,b) # (y,c) # ws)" using hj by (by100 simp)
    moreover have "fst (((x,b)#(y,c)#ws) ! (j+1)) = fst (((x,b)#(y,c)#ws) ! ((j+1)+1))"
      using hfj by force
    moreover have "snd (((x,b)#(y,c)#ws) ! (j+1)) \<noteq> snd (((x,b)#(y,c)#ws) ! ((j+1)+1))"
      using hsj by force
    ultimately show ?thesis by (by100 blast)
  qed
qed

text \<open>Group inverse is anti-homomorphism: invg(a\<cdot>b) = invg(b)\<cdot>invg(a).\<close>
lemma group_inv_product:
  assumes hG: "top1_is_group_on G mul e invg" and ha: "a \<in> G" and hb: "b \<in> G"
  shows "invg (mul a b) = mul (invg b) (invg a)"
proof -
  have hab: "mul a b \<in> G" using hG ha hb unfolding top1_is_group_on_def by (by100 blast)
  have hia: "invg a \<in> G" using hG ha unfolding top1_is_group_on_def by (by100 blast)
  have hib: "invg b \<in> G" using hG hb unfolding top1_is_group_on_def by (by100 blast)
  have hiab: "invg (mul a b) \<in> G" using hG hab unfolding top1_is_group_on_def by (by100 blast)
  have hprod: "mul (invg b) (invg a) \<in> G" using hG hib hia unfolding top1_is_group_on_def by (by100 blast)
  \<comment> \<open>Compute (invg b \<cdot> invg a) \<cdot> (a \<cdot> b) step by step using right-to-left cancellation.\<close>
  have hassoc: "\<And>x y z. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> z \<in> G \<Longrightarrow> mul (mul x y) z = mul x (mul y z)"
    using hG unfolding top1_is_group_on_def by (by100 blast)
  have "mul (mul (invg b) (invg a)) (mul a b)
      = mul (invg b) (mul (invg a) (mul a b))"
    by (rule hassoc[OF hib hia hab])
  also have "mul (invg a) (mul a b) = mul (mul (invg a) a) b"
    by (rule hassoc[OF hia ha hb, symmetric])
  finally have "mul (mul (invg b) (invg a)) (mul a b)
      = mul (invg b) (mul (mul (invg a) a) b)"
    using hassoc[OF hib hia hab] hassoc[OF hia ha hb] by (by100 simp)
  also have "mul (invg a) a = e" using hG ha unfolding top1_is_group_on_def by (by100 blast)
  hence "mul (invg b) (mul (mul (invg a) a) b) = mul (invg b) (mul e b)"
    by (by100 simp)
  also have "mul e b = b" using hG hb unfolding top1_is_group_on_def by (by100 blast)
  hence "mul (invg b) (mul e b) = mul (invg b) b" by (by100 simp)
  also have "mul (invg b) b = e" using hG hb unfolding top1_is_group_on_def by (by100 blast)
  finally have h_left: "mul (mul (invg b) (invg a)) (mul a b) = e" by (by100 simp)
  \<comment> \<open>Left inverse uniqueness: if x\<cdot>y = e in a group, then x = invg(y).\<close>
  have "mul (mul (invg b) (invg a)) (mul a b) = e" by (rule h_left)
  moreover have "mul (invg (mul a b)) (mul a b) = e"
    using hG hab unfolding top1_is_group_on_def by (by100 blast)
  \<comment> \<open>Both equal e after right-multiplying by (mul a b). Right-cancel to get equality.\<close>
  ultimately have "mul (mul (mul (invg b) (invg a)) (mul a b)) (invg (mul a b))
      = mul (mul (invg (mul a b)) (mul a b)) (invg (mul a b))" by (by100 simp)
  hence "mul (invg b) (invg a) = invg (mul a b)"
  proof -
    \<comment> \<open>LHS: x \<cdot> (a\<cdot>b) \<cdot> (a\<cdot>b)^{-1} = x \<cdot> e = x.\<close>
    have hcancel_ab: "mul (mul a b) (invg (mul a b)) = e"
      using hG hab unfolding top1_is_group_on_def by (by100 blast)
    have hassoc1: "mul (mul (mul (invg b) (invg a)) (mul a b)) (invg (mul a b))
        = mul (mul (invg b) (invg a)) (mul (mul a b) (invg (mul a b)))"
      by (rule hassoc[OF hprod hab hiab])
    have hLHS: "mul (mul (mul (invg b) (invg a)) (mul a b)) (invg (mul a b))
        = mul (invg b) (invg a)"
      using hassoc1 hcancel_ab hG hprod unfolding top1_is_group_on_def by (by100 simp)
    \<comment> \<open>RHS: similarly invg(a\<cdot>b).\<close>
    have hassoc2: "mul (mul (invg (mul a b)) (mul a b)) (invg (mul a b))
        = mul (invg (mul a b)) (mul (mul a b) (invg (mul a b)))"
      by (rule hassoc[OF hiab hab hiab])
    have hRHS: "mul (mul (invg (mul a b)) (mul a b)) (invg (mul a b))
        = invg (mul a b)"
      using hassoc2 hcancel_ab hG hiab unfolding top1_is_group_on_def by (by100 simp)
    from h_left \<open>mul (invg (mul a b)) (mul a b) = e\<close>
    have "mul (mul (invg b) (invg a)) (mul a b) = mul (invg (mul a b)) (mul a b)"
      by (by100 simp)
    hence "mul (mul (mul (invg b) (invg a)) (mul a b)) (invg (mul a b))
        = mul (mul (invg (mul a b)) (mul a b)) (invg (mul a b))" by (by100 simp)
    thus ?thesis using hLHS hRHS by (by100 simp)
  qed
  thus ?thesis by (by100 simp)
qed

text \<open>Word product of sign-reversed word = group inverse of word product.\<close>
lemma word_product_rev_inv:
  assumes hG: "top1_is_group_on G mul e invg"
      and hws: "\<forall>i<length ws. fst (ws ! i) \<in> G"
  shows "top1_group_word_product mul e invg (map (\<lambda>(x,b). (x, \<not>b)) (rev ws))
       = invg (top1_group_word_product mul e invg ws)"
  using hws
proof (induct ws)
  case Nil
  have "invg e = e"
  proof -
    have he: "e \<in> G" using hG unfolding top1_is_group_on_def by (by100 blast)
    have "mul (invg e) e = e" using hG he unfolding top1_is_group_on_def by (by100 blast)
    have "invg e \<in> G" using hG he unfolding top1_is_group_on_def by (by100 blast)
    have "mul (invg e) e = invg e"
      using hG \<open>invg e \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
    thus ?thesis using \<open>mul (invg e) e = e\<close> by (by100 simp)
  qed
  thus ?case by (by100 simp)
next
  case (Cons a ws)
  obtain x b where ha: "a = (x, b)" by (cases a) (by100 blast)
  have hx: "x \<in> G" using Cons(2) ha by (by100 force)
  have hws': "\<forall>i<length ws. fst (ws ! i) \<in> G" using Cons(2) by (by100 force)
  have hIH: "top1_group_word_product mul e invg (map (\<lambda>(x,b). (x, \<not>b)) (rev ws))
      = invg (top1_group_word_product mul e invg ws)" by (rule Cons(1)[OF hws'])
  \<comment> \<open>rev(a#ws) = rev ws @ [a], so map(\<not>b)(rev(a#ws)) = map(\<not>b)(rev ws) @ [(x,\<not>b)].\<close>
  let ?revws = "map (\<lambda>(x,b). (x, \<not>b)) (rev ws)"
  let ?last = "[(x, \<not>b)]"
  have hrev_eq: "map (\<lambda>(x,b). (x, \<not>b)) (rev (a # ws)) = ?revws @ ?last"
    using ha by (by100 simp)
  \<comment> \<open>Elements of reversed word in G.\<close>
  have hrevws_G: "\<forall>i<length ?revws. fst (?revws ! i) \<in> G"
  proof (intro allI impI)
    fix i assume "i < length ?revws"
    hence "i < length ws" by (by100 simp)
    hence hi: "i < length ws" .
    \<comment> \<open>rev ws ! i = ws ! (length ws - 1 - i).\<close>
    have hrev_idx: "rev ws ! i = ws ! (length ws - 1 - i)" using rev_nth hi by (by100 simp)
    have hk: "length ws - 1 - i < length ws" using hi by (by100 simp)
    obtain xk bk where hxk: "ws ! (length ws - 1 - i) = (xk, bk)"
      by (cases "ws ! (length ws - 1 - i)") (by100 blast)
    have "fst (ws ! (length ws - 1 - i)) \<in> G" using hws' hk by (by100 blast)
    hence "xk \<in> G" using hxk by (by100 simp)
    have "?revws ! i = (\<lambda>(x,b). (x, \<not>b)) (rev ws ! i)" using hi by (by100 simp)
    also have "\<dots> = (\<lambda>(x,b). (x, \<not>b)) (xk, bk)" using hrev_idx hxk by (by100 simp)
    also have "\<dots> = (xk, \<not>bk)" by (by100 simp)
    finally have "fst (?revws ! i) = xk" by (by100 simp)
    thus "fst (?revws ! i) \<in> G" using \<open>xk \<in> G\<close> by (by100 simp)
  qed
  have hlast_G: "\<forall>i<length ?last. fst (?last ! i) \<in> G" using hx by (by100 simp)
  \<comment> \<open>Use word\_product\_append.\<close>
  have "top1_group_word_product mul e invg (map (\<lambda>(x,b). (x, \<not>b)) (rev (a # ws)))
      = top1_group_word_product mul e invg (?revws @ ?last)" using hrev_eq by (by100 simp)
  also have "\<dots> = mul (top1_group_word_product mul e invg ?revws)
      (top1_group_word_product mul e invg ?last)"
    by (rule word_product_append[OF hG hrevws_G hlast_G])
  also have "\<dots> = mul (invg (top1_group_word_product mul e invg ws))
      (top1_group_word_product mul e invg ?last)" using hIH by (by100 simp)
  finally have hstep: "top1_group_word_product mul e invg (map (\<lambda>(x,b). (x, \<not>b)) (rev (a # ws)))
      = mul (invg (top1_group_word_product mul e invg ws))
            (top1_group_word_product mul e invg ?last)" .
  \<comment> \<open>Compute: wp([(x,\<not>b)]) = x or invg(x) depending on \<not>b.\<close>
  have hwp_ws: "top1_group_word_product mul e invg ws \<in> G"
    by (rule word_product_in_group[OF hG hws'])
  show ?case
  proof (cases b)
    case True
    \<comment> \<open>a = (x, True), so wp(a#ws) = mul x (wp ws). invg(wp(a#ws)) = invg(mul x (wp ws))
       = mul (invg(wp ws)) (invg x) by group\_inv\_product.\<close>
    have "top1_group_word_product mul e invg (a # ws) = mul x (top1_group_word_product mul e invg ws)"
      using ha True by (by100 simp)
    hence hinv_goal: "invg (top1_group_word_product mul e invg (a # ws))
        = invg (mul x (top1_group_word_product mul e invg ws))" by (by100 simp)
    have "invg (mul x (top1_group_word_product mul e invg ws))
        = mul (invg (top1_group_word_product mul e invg ws)) (invg x)"
      by (rule group_inv_product[OF hG hx hwp_ws])
    hence hinv_expand: "invg (top1_group_word_product mul e invg (a # ws))
        = mul (invg (top1_group_word_product mul e invg ws)) (invg x)"
      using hinv_goal by (by100 simp)
    \<comment> \<open>And wp([(x,False)]) = mul (invg x) e = invg x.\<close>
    have "top1_group_word_product mul e invg ?last = mul (invg x) e"
      using True by (by100 simp)
    also have "\<dots> = invg x"
    proof -
      have "invg x \<in> G" using hG hx unfolding top1_is_group_on_def by (by100 blast)
      thus ?thesis using hG unfolding top1_is_group_on_def by (by100 blast)
    qed
    finally have hwp_last: "top1_group_word_product mul e invg ?last = invg x" .
    show ?thesis using hstep hinv_expand hwp_last by (by100 simp)
  next
    case False
    \<comment> \<open>a = (x, False), so wp(a#ws) = mul (invg x) (wp ws).
       invg(wp(a#ws)) = mul (invg(wp ws)) (invg(invg x)) = mul (invg(wp ws)) x.\<close>
    have "top1_group_word_product mul e invg (a # ws) = mul (invg x) (top1_group_word_product mul e invg ws)"
      using ha False by (by100 simp)
    have hinvx: "invg x \<in> G" using hG hx unfolding top1_is_group_on_def by (by100 blast)
    have "invg (mul (invg x) (top1_group_word_product mul e invg ws))
        = mul (invg (top1_group_word_product mul e invg ws)) (invg (invg x))"
      by (rule group_inv_product[OF hG hinvx hwp_ws])
    \<comment> \<open>invg(invg x) = x.\<close>
    have "invg (invg x) = x"
    proof -
      have "mul x (invg x) = e" using hG hx unfolding top1_is_group_on_def by (by100 blast)
      have "mul (invg (invg x)) (invg x) = e"
        using hG hinvx unfolding top1_is_group_on_def by (by100 blast)
      hence "invg (invg x) = x"
      proof -
        have hiix: "invg (invg x) \<in> G" using hG hinvx unfolding top1_is_group_on_def by (by100 blast)
        have "mul (invg (invg x)) (invg x) = mul x (invg x)"
          using \<open>mul (invg (invg x)) (invg x) = e\<close> \<open>mul x (invg x) = e\<close> by (by100 simp)
        hence "mul (mul (invg (invg x)) (invg x)) x = mul (mul x (invg x)) x" by (by100 simp)
        hence "invg (invg x) = x"
          using hG hx hinvx hiix unfolding top1_is_group_on_def by (by100 metis)
        thus ?thesis .
      qed
      thus ?thesis .
    qed
    have hinv_expand: "invg (top1_group_word_product mul e invg (a # ws))
        = mul (invg (top1_group_word_product mul e invg ws)) x"
      using \<open>top1_group_word_product mul e invg (a # ws) = mul (invg x) (top1_group_word_product mul e invg ws)\<close>
            \<open>invg (mul (invg x) (top1_group_word_product mul e invg ws)) = mul (invg (top1_group_word_product mul e invg ws)) (invg (invg x))\<close>
            \<open>invg (invg x) = x\<close> by (by100 simp)
    have "top1_group_word_product mul e invg ?last = mul x e"
      using False by (by100 simp)
    also have "\<dots> = x" using hG hx unfolding top1_is_group_on_def by (by100 blast)
    finally have hwp_last: "top1_group_word_product mul e invg ?last = x" .
    show ?thesis using hstep hinv_expand hwp_last by (by100 simp)
  qed
qed

text \<open>Key lemma: in a free group, if a word over generators evaluates to e,
  then the same word with generators replaced evaluates to eH in any group H.\<close>
lemma free_group_word_kernel:
  assumes hG: "top1_is_free_group_full_on G mul e invg \<iota> S"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hphi_H: "\<forall>s\<in>S. \<phi> s \<in> H"
      and hws: "\<forall>i<length ws. fst (ws ! i) \<in> S"
      and heval: "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ws) = e"
  shows "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ws) = eH"
proof -
  have hG_grp: "top1_is_group_on G mul e invg"
    using hG unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hG_inj: "inj_on \<iota> S"
    using hG unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hG_in: "\<forall>s\<in>S. \<iota> s \<in> G"
    using hG unfolding top1_is_free_group_full_on_def by (by100 blast)
  \<comment> \<open>The free group axiom: non-empty reduced word \<noteq> e.\<close>
  have hfree_ax: "\<And>ws'. ws' \<noteq> [] \<Longrightarrow>
      top1_is_reduced_word (map (\<lambda>(s,b). (\<iota> s, b)) ws') \<Longrightarrow>
      (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<Longrightarrow>
      top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ws') \<noteq> e"
    using hG unfolding top1_is_free_group_full_on_def by (by100 blast)
  \<comment> \<open>Non-reduced word has a cancellable pair.\<close>
  have hnonred_cancel: "\<And>ws'. ws' \<noteq> [] \<Longrightarrow>
      \<not> top1_is_reduced_word (map (\<lambda>(s,b). (\<iota> s, b)) ws') \<Longrightarrow>
      (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<Longrightarrow>
      \<exists>i. i + 1 < length ws' \<and> fst (ws' ! i) = fst (ws' ! (i+1))
        \<and> snd (ws' ! i) \<noteq> snd (ws' ! (i+1))"
  proof (goal_cases)
    case (1 ws')
    have hne: "ws' \<noteq> []" and hnr: "\<not> top1_is_reduced_word (map (\<lambda>(s,b). (\<iota> s, b)) ws')"
        and hS: "\<forall>i<length ws'. fst (ws' ! i) \<in> S"
      using 1 by (by100 blast)+
    \<comment> \<open>The mapped word has an adjacent cancellable pair. Extract it and
       use injectivity of \<iota> to get a cancellable pair in ws'.\<close>
    let ?mws = "map (\<lambda>(s,b). (\<iota> s, b)) ws'"
    \<comment> \<open>Non-reduced means: \<exists>i. fst(?mws!i) = fst(?mws!(i+1)) \<and> snd(?mws!i) \<noteq> snd(?mws!(i+1)).\<close>
    have "\<exists>i. i + 1 < length ?mws \<and> fst (?mws ! i) = fst (?mws ! (i+1))
        \<and> snd (?mws ! i) \<noteq> snd (?mws ! (i+1))"
    proof -
      \<comment> \<open>General fact by strong induction on length.\<close>
      have gen: "\<And>xs :: ('g \<times> bool) list. xs \<noteq> [] \<Longrightarrow> \<not> top1_is_reduced_word xs \<Longrightarrow>
          \<exists>i. i + 1 < length xs \<and> fst (xs ! i) = fst (xs ! (i+1)) \<and> snd (xs ! i) \<noteq> snd (xs ! (i+1))"
        using not_reduced_has_cancel by (by100 blast)
      have "?mws \<noteq> []" using hne by (by100 simp)
      thus ?thesis using gen[OF \<open>?mws \<noteq> []\<close> hnr] by (by100 blast)
    qed
    then obtain j where hj: "j + 1 < length ?mws"
        and hfj: "fst (?mws ! j) = fst (?mws ! (j+1))"
        and hsj: "snd (?mws ! j) \<noteq> snd (?mws ! (j+1))" by (by100 blast)
    have hjw: "j + 1 < length ws'" using hj by (by100 simp)
    \<comment> \<open>Map nth: ?mws ! j = (\<iota>(fst(ws'!j)), snd(ws'!j)).\<close>
    obtain s1 b1 where hw1: "ws' ! j = (s1, b1)" by (cases "ws'!j") (by100 blast)
    obtain s2 b2 where hw2: "ws' ! (j+1) = (s2, b2)" by (cases "ws'!(j+1)") (by100 blast)
    have hj1: "j < length ws'" using hjw by (by100 simp)
    have hj2: "j+1 < length ws'" using hjw by (by100 simp)
    have hmj: "?mws ! j = (\<iota> s1, b1)" using hw1 hj1 by simp
    have hmj1: "?mws ! (j+1) = (\<iota> s2, b2)" using hw2 hj2 by simp
    \<comment> \<open>\<iota>(s1) = \<iota>(s2) and b1 \<noteq> b2.\<close>
    have "\<iota> s1 = \<iota> s2" using hfj hmj hmj1 by (by100 simp)
    moreover have "s1 \<in> S" using hS hj1 hw1 by (by100 force)
    moreover have "s2 \<in> S" using hS hj2 hw2 by (by100 force)
    ultimately have "s1 = s2" using hG_inj unfolding inj_on_def by (by100 blast)
    hence "fst (ws' ! j) = fst (ws' ! (j+1))" using hw1 hw2 by (by100 simp)
    moreover have "snd (ws' ! j) \<noteq> snd (ws' ! (j+1))"
      using hsj hmj hmj1 hw1 hw2 by (by100 simp)
    ultimately show "\<exists>i. i + 1 < length ws' \<and> fst (ws' ! i) = fst (ws' ! (i+1))
        \<and> snd (ws' ! i) \<noteq> snd (ws' ! (i+1))"
      using hjw by (by100 blast)
  qed
  \<comment> \<open>Strong induction on length ws.\<close>
  show ?thesis using hws heval
  proof (induct "length ws" arbitrary: ws rule: less_induct)
    case (less ws)
    show ?case
    proof (cases "ws = []")
      case True thus ?thesis by (by100 simp)
    next
      case False
      \<comment> \<open>If the mapped word is reduced, contradiction with free group axiom.\<close>
      show ?thesis
      proof (cases "top1_is_reduced_word (map (\<lambda>(s,b). (\<iota> s, b)) ws)")
        case True
        hence "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ws) \<noteq> e"
          by (rule hfree_ax[OF False _ less(2)])
        thus ?thesis using less(3) by (by100 blast)
      next
        case not_reduced: False
        \<comment> \<open>Find cancellable pair.\<close>
        obtain i where hi: "i + 1 < length ws"
            and hfst_i: "fst (ws ! i) = fst (ws ! (i+1))"
            and hsnd_i: "snd (ws ! i) \<noteq> snd (ws ! (i+1))"
          using hnonred_cancel[OF \<open>ws \<noteq> []\<close> not_reduced less(2)] by (by100 blast)
        let ?ws' = "take i ws @ drop (i+2) ws"
        \<comment> \<open>Mapped words: cancellation at position i.\<close>
        \<comment> \<open>Elements in G/H for mapped words — not directly needed, skip.\<close>
        \<comment> \<open>Apply word\_cancel to G-word.\<close>
        \<comment> \<open>Key: map commutes with take/drop, and cancellable pair transfers.\<close>
        have hmap_split: "\<And>f. map f (take i ws @ drop (i+2) ws)
            = take i (map f ws) @ drop (i+2) (map f ws)"
          by (simp add: take_map drop_map)
        have hi1: "i < length ws" using hi by (by100 simp)
        have hi2: "i+1 < length ws" using hi by (by100 simp)
        obtain s1 b1 where hw_i: "ws ! i = (s1, b1)" by (cases "ws!i") (by100 blast)
        obtain s2 b2 where hw_i1: "ws ! (i+1) = (s2, b2)" by (cases "ws!(i+1)") (by100 blast)
        have hs_eq: "s1 = s2" using hfst_i hw_i hw_i1 by (by100 simp)
        have hb_neq: "b1 \<noteq> b2" using hsnd_i hw_i hw_i1 by (by100 simp)
        have hnth_i: "map (\<lambda>(s,b). (\<iota> s, b)) ws ! i = (\<iota> s1, b1)"
          using hi1 hw_i by (by100 simp)
        have hnth_i1: "map (\<lambda>(s,b). (\<iota> s, b)) ws ! (i+1) = (\<iota> s2, b2)"
          using hi2 hw_i1 by (by100 simp)
        have hG_fst: "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! i) = fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! (i+1))"
          using hnth_i hnth_i1 hs_eq by (by100 simp)
        have hG_snd: "snd (map (\<lambda>(s,b). (\<iota> s, b)) ws ! i) \<noteq> snd (map (\<lambda>(s,b). (\<iota> s, b)) ws ! (i+1))"
          using hnth_i hnth_i1 hb_neq by (by100 simp)
        have hG_len: "i + 1 < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)" using hi by (by100 simp)
        have hG_in_mapped: "\<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws).
            fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
        proof (intro allI impI)
          fix j assume hj: "j < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
          hence hjw: "j < length ws" by (by100 simp)
          obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
          have "sj \<in> S" using less(2) hjw hwj by (by100 force)
          hence "\<iota> sj \<in> G" using hG_in by (by100 blast)
          moreover have "map (\<lambda>(s,b). (\<iota> s, b)) ws ! j = (\<iota> sj, bj)" using hjw hwj by simp
          ultimately show "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G" by (by100 simp)
        qed
        have hcancel_G: "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ws)
            = top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ?ws')"
          using word_cancel_preserves_eval[OF hG_grp hG_len hG_fst hG_snd hG_in_mapped]
                hmap_split[of "\<lambda>(s,b). (\<iota> s, b)"] by (by100 simp)
        hence heval': "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ?ws') = e"
          using less(3) by (by100 simp)
        \<comment> \<open>ws' is shorter.\<close>
        have hlen: "length ?ws' < length ws" using hi by (by100 simp)
        have hws'_S: "\<forall>j<length ?ws'. fst (?ws' ! j) \<in> S"
        proof (intro allI impI)
          fix j assume hj: "j < length ?ws'"
          have "?ws' ! j \<in> set ?ws'" using nth_mem hj by (by100 blast)
          hence "?ws' ! j \<in> set (take i ws) \<or> ?ws' ! j \<in> set (drop (i+2) ws)"
            using Un_iff set_append by (by100 fast)
          hence "?ws' ! j \<in> set ws"
          proof
            assume "?ws' ! j \<in> set (take i ws)" thus ?thesis using in_set_takeD by (by100 fast)
          next
            assume "?ws' ! j \<in> set (drop (i+2) ws)" thus ?thesis using in_set_dropD by (by100 fast)
          qed
          then obtain k where hk: "k < length ws" and hwk: "ws ! k = ?ws' ! j"
            using in_set_conv_nth by (by100 metis)
          thus "fst (?ws' ! j) \<in> S" using less(2) hwk by (by100 force)
        qed
        \<comment> \<open>By IH: H-evaluation of ws' equals eH.\<close>
        have hIH: "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ?ws') = eH"
          by (rule less(1)[OF hlen hws'_S heval'])
        \<comment> \<open>word\_cancel on H-word: H-evaluation of ws = H-evaluation of ws'.\<close>
        have hH_in_mapped: "\<forall>j<length (map (\<lambda>(s,b). (\<phi> s, b)) ws).
            fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H"
        proof (intro allI impI)
          fix j assume hj: "j < length (map (\<lambda>(s,b). (\<phi> s, b)) ws)"
          hence hjw: "j < length ws" by (by100 simp)
          obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
          have "sj \<in> S" using less(2) hjw hwj by (by100 force)
          hence "\<phi> sj \<in> H" using hphi_H by (by100 blast)
          moreover have "map (\<lambda>(s,b). (\<phi> s, b)) ws ! j = (\<phi> sj, bj)" using hjw hwj by simp
          ultimately show "fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H" by (by100 simp)
        qed
        have hH_fst: "fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! i) = fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! (i+1))"
          using hw_i hw_i1 hs_eq hi1 hi2 by simp
        have hH_snd: "snd (map (\<lambda>(s,b). (\<phi> s, b)) ws ! i) \<noteq> snd (map (\<lambda>(s,b). (\<phi> s, b)) ws ! (i+1))"
          using hw_i hw_i1 hb_neq hi1 hi2 by simp
        have hH_len: "i + 1 < length (map (\<lambda>(s,b). (\<phi> s, b)) ws)" using hi by (by100 simp)
        have hcancel_H: "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ws)
            = top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ?ws')"
          using word_cancel_preserves_eval[OF hH hH_len hH_fst hH_snd hH_in_mapped]
                hmap_split[of "\<lambda>(s,b). (\<phi> s, b)"] by (by100 simp)
        thus ?thesis using hIH by (by100 simp)
      qed
    qed
  qed
qed

text \<open>Helper: in an abelian group, swapping two adjacent elements in a word preserves
  the word product. Uses abelian\_mul\_left\_commute + word\_product\_append.\<close>
lemma abelian_word_product_swap:
  assumes hG: "top1_is_abelian_group_on G mul e invg"
      and hpre: "\<forall>i<length pre. fst (pre ! i) \<in> G"
      and ha: "fst a \<in> G" and hb: "fst b \<in> G"
      and hpost: "\<forall>i<length post. fst (post ! i) \<in> G"
  shows "top1_group_word_product mul e invg (pre @ [a, b] @ post)
       = top1_group_word_product mul e invg (pre @ [b, a] @ post)"
proof -
  have hG_grp: "top1_is_group_on G mul e invg"
    using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
  obtain xa ba where ha_eq: "a = (xa, ba)" by (cases a) (by100 blast)
  obtain xb bb where hb_eq: "b = (xb, bb)" by (cases b) (by100 blast)
  let ?ga = "if ba then xa else invg xa"
  let ?gb = "if bb then xb else invg xb"
  have hxa: "xa \<in> G" using ha ha_eq by (by100 simp)
  have hxb: "xb \<in> G" using hb hb_eq by (by100 simp)
  have hinvxa: "invg xa \<in> G" using hxa hG_grp unfolding top1_is_group_on_def by (by100 blast)
  have hinvxb: "invg xb \<in> G" using hxb hG_grp unfolding top1_is_group_on_def by (by100 blast)
  have hga: "?ga \<in> G" using hxa hinvxa by (by100 simp)
  have hgb: "?gb \<in> G" using hxb hinvxb by (by100 simp)
  have hwp_post: "top1_group_word_product mul e invg post \<in> G"
    by (rule word_product_in_group[OF hG_grp hpost])
  \<comment> \<open>Key: mul ?ga (mul ?gb c) = mul ?gb (mul ?ga c) by abelian\_mul\_left\_commute.\<close>
  have hswap: "mul ?ga (mul ?gb (top1_group_word_product mul e invg post))
             = mul ?gb (mul ?ga (top1_group_word_product mul e invg post))"
    by (rule abelian_mul_left_commute[OF hG hga hgb hwp_post])
  \<comment> \<open>word\_product [a,b] @ post = ?ga \<cdot> ?gb \<cdot> wp(post).\<close>
  have hlhs: "top1_group_word_product mul e invg ([a, b] @ post)
       = mul ?ga (mul ?gb (top1_group_word_product mul e invg post))"
    using ha_eq hb_eq by (by100 simp)
  have hrhs: "top1_group_word_product mul e invg ([b, a] @ post)
       = mul ?gb (mul ?ga (top1_group_word_product mul e invg post))"
    using ha_eq hb_eq by (by100 simp)
  \<comment> \<open>Connect via word\_product\_append on pre.\<close>
  have hab_G: "\<forall>i<length ([a, b] @ post). fst (([a, b] @ post) ! i) \<in> G"
  proof (intro allI impI)
    fix i assume hi: "i < length ([a, b] @ post)"
    show "fst (([a, b] @ post) ! i) \<in> G"
    proof (cases "i < 2")
      case True
      hence "i = 0 \<or> i = Suc 0" by (by100 auto)
      thus ?thesis using ha hb ha_eq hb_eq by (by100 auto)
    next
      case False
      hence "\<not> i < length [a, b]" by (by100 simp)
      hence "(([a, b] @ post) ! i) = post ! (i - length [a, b])"
        apply (simp only: nth_append if_False)
        done
      moreover have "i - length [a, b] < length post" using hi False by (by100 simp)
      ultimately show ?thesis using hpost by (by100 force)
    qed
  qed
  have hba_G: "\<forall>i<length ([b, a] @ post). fst (([b, a] @ post) ! i) \<in> G"
  proof (intro allI impI)
    fix i assume hi: "i < length ([b, a] @ post)"
    show "fst (([b, a] @ post) ! i) \<in> G"
    proof (cases "i < 2")
      case True
      hence "i = 0 \<or> i = Suc 0" by (by100 auto)
      thus ?thesis using ha hb ha_eq hb_eq by (by100 auto)
    next
      case False
      hence "\<not> i < length [b, a]" by (by100 simp)
      hence "(([b, a] @ post) ! i) = post ! (i - length [b, a])"
        apply (simp only: nth_append if_False)
        done
      moreover have "i - length [b, a] < length post" using hi False by (by100 simp)
      ultimately show ?thesis using hpost by (by100 force)
    qed
  qed
  have "top1_group_word_product mul e invg (pre @ [a, b] @ post)
      = mul (top1_group_word_product mul e invg pre)
            (top1_group_word_product mul e invg ([a, b] @ post))"
    by (rule word_product_append[OF hG_grp hpre hab_G])
  also have "\<dots> = mul (top1_group_word_product mul e invg pre)
            (top1_group_word_product mul e invg ([b, a] @ post))"
    using hlhs hrhs hswap by (by100 simp)
  also have "\<dots> = top1_group_word_product mul e invg (pre @ [b, a] @ post)"
    by (rule word_product_append[OF hG_grp hpre hba_G, symmetric])
  finally show ?thesis .
qed

text \<open>Connection: word\_product = foldr mul on gen-mapped list.\<close>
lemma word_product_as_foldr:
  "top1_group_word_product mul e invg ws
   = foldr mul (map (\<lambda>(x,b). if b then x else invg x) ws) e"
proof (induction ws)
  case Nil thus ?case by (by100 fastforce)
next
  case (Cons a ws)
  obtain x b where ha: "a = (x, b)" by (cases a) (by100 blast)
  show ?case using Cons ha by (cases b) (by100 simp)+
qed

text \<open>Helper: foldr mul of n copies of x equals group\_pow.\<close>
lemma foldr_mul_replicate:
  assumes "top1_is_group_on G mul e invg" and "x \<in> G"
  shows "foldr mul (replicate n x) e = top1_group_pow mul e x n"
proof (induction n)
  case 0 thus ?case by (by100 simp)
next
  case (Suc n) thus ?case by (by100 simp)
qed

text \<open>Helper: filter for a specific element gives replicate, so foldr mul = group\_pow.\<close>
lemma filter_eq_replicate: "filter (\<lambda>x. x = a) xs = replicate (length (filter (\<lambda>x. x = a) xs)) a"
  by (induction xs) (by100 simp)+

lemma abelian_foldr_mul_filter_eq:
  assumes "top1_is_group_on G mul e invg" and "a \<in> G"
  shows "foldr mul (filter (\<lambda>x. x = a) xs) e = top1_group_pow mul e a (length (filter (\<lambda>x. x = a) xs))"
proof -
  let ?n = "length (filter (\<lambda>x. x = a) xs)"
  have "filter (\<lambda>x. x = a) xs = replicate ?n a" by (rule filter_eq_replicate)
  hence "foldr mul (filter (\<lambda>x. x = a) xs) e = foldr mul (replicate ?n a) e" by (by100 simp)
  also have "\<dots> = top1_group_pow mul e a ?n" by (rule foldr_mul_replicate[OF assms])
  finally show ?thesis .
qed

text \<open>Helper: In abelian group, move element at position i to position 0 preserving
  the word product. Uses abelian\_foldr\_mul\_extract on the gen-mapped list.\<close>
lemma abelian_word_product_move_front:
  assumes hG: "top1_is_abelian_group_on G mul e invg"
      and hws: "\<forall>j<length ws. fst (ws ! j) \<in> G"
      and hi: "i < length ws"
  shows "top1_group_word_product mul e invg ws
       = top1_group_word_product mul e invg (ws ! i # take i ws @ drop (Suc i) ws)"
proof -
  have hG_grp: "top1_is_group_on G mul e invg"
    using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
  let ?gen = "\<lambda>(x::('a::type),b::bool). if b then x else invg x"
  let ?gs = "map ?gen ws"
  \<comment> \<open>All gen-mapped elements are in G.\<close>
  have hgs: "\<forall>j<length ?gs. ?gs ! j \<in> G"
  proof (intro allI impI)
    fix j assume hj: "j < length ?gs"
    hence hj': "j < length ws" by (by100 simp)
    obtain xj bj where hwj: "ws ! j = (xj, bj)" by (cases "ws ! j") (by100 blast)
    have "xj \<in> G" using hws hj' hwj by (by100 force)
    hence "invg xj \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
    have "?gs ! j = ?gen (ws ! j)" using hj' by (by100 simp)
    thus "?gs ! j \<in> G" using hwj \<open>xj \<in> G\<close> \<open>invg xj \<in> G\<close> by (by100 simp)
  qed
  \<comment> \<open>Decompose: map gen ws = take i (map gen ws) @ [gen(ws!i)] @ drop (Suc i) (map gen ws).\<close>
  have hdecomp: "?gs = take i ?gs @ [?gen (ws ! i)] @ drop (Suc i) ?gs"
  proof -
    have hi_gs: "i < length ?gs" using hi by (by100 simp)
    have "?gs = take i ?gs @ ?gs ! i # drop (Suc i) ?gs"
      using hi_gs by (rule id_take_nth_drop)
    moreover have "?gs ! i = ?gen (ws ! i)" using hi by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  have htake_gs: "\<forall>j<length (take i ?gs). (take i ?gs) ! j \<in> G"
    using hgs by (by100 fastforce)
  have hdrop_gs: "\<forall>j<length (drop (Suc i) ?gs). (drop (Suc i) ?gs) ! j \<in> G"
    using hgs hi by (by100 fastforce)
  have hgi: "?gen (ws ! i) \<in> G" using hgs hi by (by100 fastforce)
  \<comment> \<open>By abelian\_foldr\_mul\_extract:\<close>
  have "foldr mul ?gs e = foldr mul (take i ?gs @ [?gen (ws ! i)] @ drop (Suc i) ?gs) e"
    using hdecomp by (by100 simp)
  also have "\<dots> = mul (?gen (ws ! i)) (foldr mul (take i ?gs @ drop (Suc i) ?gs) e)"
    by (rule abelian_foldr_mul_extract[OF hG htake_gs hgi hdrop_gs])
  finally have hfoldr: "foldr mul ?gs e = mul (?gen (ws ! i)) (foldr mul (take i ?gs @ drop (Suc i) ?gs) e)" .
  \<comment> \<open>Convert back: LHS = word\_product(ws), RHS = word\_product(ws!i # rest).\<close>
  \<comment> \<open>LHS: word\_product ws = foldr mul ?gs e = mul(gen(ws!i), foldr ...) = mul(gen(ws!i), word\_product(rest)).\<close>
  have hlhs: "top1_group_word_product mul e invg ws
    = mul (?gen (ws ! i)) (top1_group_word_product mul e invg (take i ws @ drop (Suc i) ws))"
  proof -
    have "top1_group_word_product mul e invg ws = foldr mul ?gs e"
      by (rule word_product_as_foldr)
    also have "\<dots> = mul (?gen (ws ! i)) (foldr mul (take i ?gs @ drop (Suc i) ?gs) e)"
      by (rule hfoldr)
    finally have h1: "top1_group_word_product mul e invg ws
        = mul (?gen (ws ! i)) (foldr mul (take i ?gs @ drop (Suc i) ?gs) e)" .
    have "take i ?gs = map ?gen (take i ws)" by (rule take_map)
    moreover have "drop (Suc i) ?gs = map ?gen (drop (Suc i) ws)" by (rule drop_map)
    ultimately have "take i ?gs @ drop (Suc i) ?gs = map ?gen (take i ws) @ map ?gen (drop (Suc i) ws)"
      by (by100 simp)
    hence htd: "take i ?gs @ drop (Suc i) ?gs = map ?gen (take i ws @ drop (Suc i) ws)"
      by (by100 simp)
    hence "foldr mul (take i ?gs @ drop (Suc i) ?gs) e
         = top1_group_word_product mul e invg (take i ws @ drop (Suc i) ws)"
      using word_product_as_foldr[of mul e invg "take i ws @ drop (Suc i) ws"] by (by100 simp)
    thus ?thesis using h1 by (by100 simp)
  qed
  \<comment> \<open>RHS: word\_product(ws!i # rest) = mul(gen(ws!i), word\_product(rest)).\<close>
  have hrhs: "top1_group_word_product mul e invg (ws ! i # take i ws @ drop (Suc i) ws)
    = mul (?gen (ws ! i)) (top1_group_word_product mul e invg (take i ws @ drop (Suc i) ws))"
  proof -
    obtain xi bi where hwi: "ws ! i = (xi, bi)" by (cases "ws ! i") (by100 blast)
    show ?thesis using hwi by (cases bi) (by100 simp)+
  qed
  show ?thesis using hlhs hrhs by (by100 simp)
qed

text \<open>Word-level cancel pair by direct argument.\<close>
lemma word_product_cancel_matching_pair:
  assumes hG: "top1_is_abelian_group_on G mul e invg"
      and hws: "\<forall>i<length ws. fst (ws ! i) \<in> G"
      and h0: "ws ! 0 = (s, b)" and hj0: "j > 0" and hj: "j < length ws"
      and hwj: "ws ! j = (s, \<not>b)"
  shows "top1_group_word_product mul e invg ws
       = top1_group_word_product mul e invg (tl (take j ws) @ drop (Suc j) ws)"
proof -
  have hG_grp: "top1_is_group_on G mul e invg"
    using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
  \<comment> \<open>Decompose ws = a # rest where a = (s,b).\<close>
  obtain a rest where hws_eq: "ws = a # rest" and ha: "a = (s, b)"
    using hj hj0 h0 by (cases ws) (by100 auto)
  have hrest_G: "\<forall>i<length rest. fst (rest ! i) \<in> G"
    using hws hws_eq by (by100 force)
  have hj': "j - 1 < length rest" using hj hws_eq hj0 by (by100 simp)
  have hwj': "rest ! (j - 1) = (s, \<not>b)" using hwj hws_eq hj0 by (by100 simp)
  \<comment> \<open>Move rest!(j-1) to front of rest.\<close>
  have hmove: "top1_group_word_product mul e invg rest
      = top1_group_word_product mul e invg (rest ! (j-1) # take (j-1) rest @ drop (Suc (j-1)) rest)"
    apply (rule abelian_word_product_move_front)
    apply (rule hG) apply (rule hrest_G) apply (rule hj') done
  hence hmove': "top1_group_word_product mul e invg rest
      = top1_group_word_product mul e invg (rest ! (j-1) # take (j-1) rest @ drop j rest)"
    using hj0 by (by100 simp)
  \<comment> \<open>ws = (s,b) # rest. word\_product ws = gen(s,b) \<cdot> word\_product(rest).\<close>
  have hs_G: "s \<in> G" using hws h0 hj hj0 by (by100 force)
  \<comment> \<open>After moving: rest starts with (s,\<not>b).
     word\_product(ws) = gen(s,b) \<cdot> gen(s,\<not>b) \<cdot> word\_product(rest').
     gen(s,b) \<cdot> gen(s,\<not>b) = e. So word\_product(ws) = word\_product(rest').\<close>
  \<comment> \<open>rest' = take(j-1) rest @ drop j rest = tl(take j ws) @ drop(Suc j) ws.\<close>
  have hrest'_eq: "take (j-1) rest @ drop j rest = tl (take j ws) @ drop (Suc j) ws"
  proof -
    have "take j (a # rest) = a # take (j - 1) rest" using hj0
      by (cases j) (by100 simp)+
    hence "tl (take j ws) = take (j - 1) rest" using hws_eq hj0
      by (cases j) (by100 simp)+
    moreover have "drop (Suc j) ws = drop j rest" using hws_eq by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>word\_product(ws) = word\_product((s,b) # rest)
     = gen(s,b) \<cdot> word\_product(rest)
     = gen(s,b) \<cdot> gen(s,\<not>b) \<cdot> word\_product(rest')
     = e \<cdot> word\_product(rest') = word\_product(rest') = word\_product(w').\<close>
  have hwp_cons: "top1_group_word_product mul e invg ws
      = top1_group_word_product mul e invg ((s, b) # rest)"
    using hws_eq ha by (by100 simp)
  define w' where "w' = tl (take j ws) @ drop (Suc j) ws"
  have hwp_rest: "top1_group_word_product mul e invg ((s, b) # rest)
      = (if b then mul s else mul (invg s)) (top1_group_word_product mul e invg rest)"
    by (cases b) (by100 simp)+
  have hwp_moved: "top1_group_word_product mul e invg ((s, \<not>b) # take (j-1) rest @ drop j rest)
      = (if \<not>b then mul s else mul (invg s)) (top1_group_word_product mul e invg (take (j-1) rest @ drop j rest))"
    by (cases b) (by100 simp)+
  have hwp_w': "top1_group_word_product mul e invg (take (j-1) rest @ drop j rest)
      = top1_group_word_product mul e invg w'"
    using hrest'_eq unfolding w'_def by (by100 simp)
  have hprod_w': "top1_group_word_product mul e invg w' \<in> G"
  proof -
    have hw'_G: "\<forall>i<length w'. fst (w' ! i) \<in> G"
    proof (intro allI impI)
      fix i assume hi: "i < length w'"
      have "w' ! i \<in> set w'" using hi nth_mem by (by100 blast)
      have "set w' \<subseteq> set (tl (take j ws)) \<union> set (drop (Suc j) ws)"
        unfolding w'_def by (by100 auto)
      hence "w' ! i \<in> set (tl (take j ws)) \<or> w' ! i \<in> set (drop (Suc j) ws)"
        using \<open>w' ! i \<in> set w'\<close> by (by100 blast)
      hence "w' ! i \<in> set ws"
      proof
        assume "w' ! i \<in> set (tl (take j ws))"
        moreover have "set (tl (take j ws)) \<subseteq> set (take j ws)"
          by (cases "take j ws") (by100 auto)+
        moreover have "set (take j ws) \<subseteq> set ws" by (rule set_take_subset)
        ultimately show "w' ! i \<in> set ws" by (by100 blast)
      next
        assume "w' ! i \<in> set (drop (Suc j) ws)"
        moreover have "set (drop (Suc j) ws) \<subseteq> set ws" by (rule set_drop_subset)
        ultimately show "w' ! i \<in> set ws" by (by100 blast)
      qed
      then obtain k where hk: "k < length ws" "ws ! k = w' ! i"
        using in_set_conv_nth by (by100 metis)
      have "fst (ws ! k) \<in> G" using hws hk(1) by (by100 blast)
      thus "fst (w' ! i) \<in> G" using hk(2) by (by100 simp)
    qed
    show ?thesis
      apply (rule word_product_in_group)
      apply (rule hG_grp)
      apply (rule hw'_G)
      done
  qed
  have hinvs: "invg s \<in> G" using hG_grp hs_G unfolding top1_is_group_on_def by (by100 blast)
  have "top1_group_word_product mul e invg ws
      = (if b then mul s else mul (invg s))
        ((if \<not>b then mul s else mul (invg s)) (top1_group_word_product mul e invg w'))"
  proof -
    have "top1_group_word_product mul e invg ws
        = (if b then mul s else mul (invg s)) (top1_group_word_product mul e invg rest)"
      using hwp_cons hwp_rest by (by100 simp)
    also have "(if b then mul s else mul (invg s)) (top1_group_word_product mul e invg rest)
        = (if b then mul s else mul (invg s))
          ((if \<not>b then mul s else mul (invg s)) (top1_group_word_product mul e invg w'))"
    proof -
      have "top1_group_word_product mul e invg rest
          = top1_group_word_product mul e invg ((s, \<not>b) # take (j-1) rest @ drop j rest)"
        using hmove' hwj' by (by100 simp)
      also have "\<dots> = (if \<not>b then mul s else mul (invg s))
          (top1_group_word_product mul e invg (take (j-1) rest @ drop j rest))"
        by (rule hwp_moved)
      also have "top1_group_word_product mul e invg (take (j-1) rest @ drop j rest)
          = top1_group_word_product mul e invg w'"
        by (rule hwp_w')
      finally have "top1_group_word_product mul e invg rest
          = (if \<not>b then mul s else mul (invg s)) (top1_group_word_product mul e invg w')" by (by100 simp)
      thus ?thesis by (by100 simp)
    qed
    finally show ?thesis .
  qed
  also have "\<dots> = top1_group_word_product mul e invg w'"
  proof (cases b)
    case True
    have "mul s (mul (invg s) (top1_group_word_product mul e invg w'))
        = mul (mul s (invg s)) (top1_group_word_product mul e invg w')"
      using group_assoc[OF hG_grp hs_G hinvs hprod_w'] by (by100 simp)
    also have "mul s (invg s) = e"
      using hG_grp hs_G unfolding top1_is_group_on_def by (by100 blast)
    also have "mul e (top1_group_word_product mul e invg w') = top1_group_word_product mul e invg w'"
      using hG_grp hprod_w' unfolding top1_is_group_on_def by (by100 blast)
    finally show ?thesis using True by (by100 simp)
  next
    case False
    have "mul (invg s) (mul s (top1_group_word_product mul e invg w'))
        = mul (mul (invg s) s) (top1_group_word_product mul e invg w')"
      using group_assoc[OF hG_grp hinvs hs_G hprod_w'] by (by100 simp)
    also have "mul (invg s) s = e"
      using hG_grp hs_G unfolding top1_is_group_on_def by (by100 blast)
    also have "mul e (top1_group_word_product mul e invg w') = top1_group_word_product mul e invg w'"
      using hG_grp hprod_w' unfolding top1_is_group_on_def by (by100 blast)
    finally show ?thesis using False by (by100 simp)
  qed
  finally show ?thesis unfolding w'_def .
qed

text \<open>Helper: in an abelian group, if every generator in w has equal True/False counts,
  then the word product is the identity. Proof by strong induction: find a cancellable
  pair, bring them adjacent using abelian\_word\_product\_move\_front, cancel, apply IH.\<close>
lemma abelian_word_product_zero_net_coeff:
  fixes w :: "('s \<times> bool) list"
  assumes hH: "top1_is_abelian_group_on H mulH eH invgH"
      and hphi: "\<forall>s \<in> fst ` set w. \<phi> s \<in> H"
      and hzero: "\<forall>s. length (filter (\<lambda>(t,b). t = s \<and> b) w)
                    = length (filter (\<lambda>(t,b). t = s \<and> \<not>b) w)"
  shows "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) w) = eH"
  using hphi hzero
proof (induction "length w" arbitrary: w rule: less_induct)
  case (less w)
  show ?case
  proof (cases "w = []")
    case True thus ?thesis by (by100 simp)
  next
    case False
    \<comment> \<open>w is nonempty. Take the first element (s0, b0).
       Since net coeff of s0 = 0, there exists j > 0 with w!j = (s0, \<not>b0).
       Move w!j to position 1, cancel the pair, apply IH.\<close>
    obtain s0 b0 where hfirst: "w ! 0 = (s0, b0)" by (cases "w ! 0") (by100 blast)
    have hw_ne: "w \<noteq> []" using False by (by100 simp)
    have h0_len: "0 < length w" using hw_ne by (by100 simp)
    have "(s0, b0) \<in> set w" using hfirst nth_mem[OF h0_len] by (by100 simp)
    hence hs0_in: "s0 \<in> fst ` set w" by (by100 force)
    \<comment> \<open>Net coeff of s0 = 0 means equal True/False counts.
       Since (s0,b0) appears, (s0,\<not>b0) must also appear.\<close>
    have "\<exists>j. j < length w \<and> j > 0 \<and> w ! j = (s0, \<not>b0)"
    proof -
      \<comment> \<open>(s0, b0) \<in> set w means count\_True or count\_False > 0.
         Equal counts means the OTHER polarity also has count > 0.
         So (s0, \<not>b0) \<in> set w. Find j with w!j = (s0,\<not>b0).
         If j=0 then w!0=(s0,\<not>b0)=(s0,b0) so b0=\<not>b0, contradiction. Hence j>0.\<close>
      have "(s0, b0) \<in> set (filter (\<lambda>(t,b). t = s0 \<and> b = b0) w)"
        using \<open>(s0, b0) \<in> set w\<close> by (by100 simp)
      hence "filter (\<lambda>(t,b). t = s0 \<and> b = b0) w \<noteq> []" by (by100 force)
      hence hcount_pos: "length (filter (\<lambda>(t,b). t = s0 \<and> b = b0) w) > 0" by (by100 simp)
      have hcount_eq: "length (filter (\<lambda>(t,b). t = s0 \<and> b) w)
                     = length (filter (\<lambda>(t,b). t = s0 \<and> \<not>b) w)"
        using less(3) by (by100 blast)
      have hcount_neg: "length (filter (\<lambda>(t,b). t = s0 \<and> b = (\<not>b0)) w) > 0"
        using hcount_pos hcount_eq by (cases b0) (by100 simp)+
      hence "filter (\<lambda>(t,b). t = s0 \<and> b = (\<not>b0)) w \<noteq> []" by (by100 simp)
      then obtain p ps where "filter (\<lambda>(t,b). t = s0 \<and> b = (\<not>b0)) w = p # ps"
        using list.exhaust by (by100 blast)
      hence "p \<in> set (filter (\<lambda>(t,b). t = s0 \<and> b = (\<not>b0)) w)" by (by100 simp)
      hence hp: "p \<in> set w" and "(\<lambda>(t,b). t = s0 \<and> b = (\<not>b0)) p" by (by100 auto)+
      then obtain tp bp where "p = (tp, bp)" and "tp = s0" and "bp = (\<not>b0)"
        by (cases p) (by100 auto)
      hence "(s0, \<not>b0) \<in> set w" using hp by (by100 simp)
      then obtain j where hj: "j < length w" and hwj: "w ! j = (s0, \<not>b0)"
        using in_set_conv_nth by (by100 metis)
      have "j \<noteq> 0"
      proof
        assume "j = 0"
        hence "w ! 0 = (s0, \<not>b0)" using hwj by (by100 simp)
        hence "(s0, b0) = (s0, \<not>b0)" using hfirst by (by100 simp)
        thus False by (by100 simp)
      qed
      thus ?thesis using hj hwj by (by100 blast)
    qed
    then obtain j where hj: "j < length w" and hj0: "j > 0" and hwj: "w ! j = (s0, \<not>b0)"
      by (by100 blast)
    \<comment> \<open>Move w!j to position 1 using abelian swap.\<close>
    let ?w' = "take (j - 1) (tl w) @ drop j (tl w)"
    \<comment> \<open>After moving w!j next to w!0 and cancelling: length decreases by 2, IH applies.\<close>
    have hlen: "length ?w' < length w" using hj by (by100 fastforce)
    have hzero': "\<forall>s. length (filter (\<lambda>(t,b). t = s \<and> b) ?w')
                     = length (filter (\<lambda>(t,b). t = s \<and> \<not>b) ?w')"
    proof (intro allI)
      fix s
      \<comment> \<open>Decompose w into w!0 # middle @ [w!j] @ tail where middle @ tail = ?w'.\<close>
      obtain jn where hjn: "j = Suc jn" using hj0 by (cases j) (by100 auto)+
      have htlw_decomp: "tl w = take jn (tl w) @ [(tl w) ! jn] @ drop (Suc jn) (tl w)"
      proof -
        have "jn < length (tl w)" using hj hjn by (by100 simp)
        thus ?thesis using id_take_nth_drop[of jn "tl w"] by (by100 simp)
      qed
      have htlj: "(tl w) ! jn = (s0, \<not>b0)"
      proof (cases w)
        case Nil thus ?thesis using hj by (by100 simp)
      next
        case (Cons a rest)
        have "w ! j = rest ! jn" using Cons hjn by (by100 simp)
        hence "rest ! jn = (s0, \<not>b0)" using hwj by (by100 simp)
        thus ?thesis using Cons by (by100 simp)
      qed
      \<comment> \<open>?w' = take jn (tl w) @ drop (Suc jn) (tl w) = take jn (tl w) @ drop j (tl w).\<close>
      have hw'_eq: "?w' = take jn (tl w) @ drop (Suc jn) (tl w)"
        using hjn by (by100 simp)
      \<comment> \<open>For any P: filter P (tl w) = filter P ?w' inserted with P-filtered w!j.
         length(filter P (tl w)) = length(filter P ?w') + (if P(w!j) then 1 else 0).\<close>
      have "\<And>P. length (filter P (tl w)) = length (filter P ?w') + (if P (s0, \<not>b0) then 1 else 0)"
      proof -
        fix P :: "('s \<times> bool) \<Rightarrow> bool"
        have "filter P (tl w) = filter P (take jn (tl w) @ [(tl w) ! jn] @ drop (Suc jn) (tl w))"
          using htlw_decomp by (by100 simp)
        also have "\<dots> = filter P (take jn (tl w)) @ filter P [(tl w) ! jn] @ filter P (drop (Suc jn) (tl w))"
          by (by100 simp)
        finally have hlen_decomp: "length (filter P (tl w))
            = length (filter P (take jn (tl w))) + length (filter P [(tl w) ! jn])
              + length (filter P (drop (Suc jn) (tl w)))" by (by100 simp)
        have "length (filter P (take jn (tl w))) + length (filter P (drop (Suc jn) (tl w)))
            = length (filter P ?w')" using hw'_eq by (by100 simp)
        have "length (filter P [(tl w) ! jn]) = (if P (s0, \<not>b0) then 1 else 0)"
          using htlj by (by100 simp)
        thus "length (filter P (tl w)) = length (filter P ?w') + (if P (s0, \<not>b0) then 1 else 0)"
          using hlen_decomp \<open>length (filter P (take jn (tl w))) + length (filter P (drop (Suc jn) (tl w)))
              = length (filter P ?w')\<close>
          by (by100 linarith)
      qed
      hence hcount_tl: "\<And>P. length (filter P w) = (if P (s0, b0) then 1 else 0)
          + length (filter P ?w') + (if P (s0, \<not>b0) then 1 else 0)"
        using \<open>w \<noteq> []\<close> hfirst by (cases w) (by5000 simp)+
      have "length (filter (\<lambda>(t,b). t = s \<and> b) w) = length (filter (\<lambda>(t,b). t = s \<and> \<not>b) w)"
        using less(3) by (by100 blast)
      have htrue_w: "length (filter (\<lambda>(t,b). t = s \<and> b) w)
          = (if s0 = s \<and> b0 then 1 else 0) + length (filter (\<lambda>(t,b). t = s \<and> b) ?w')
            + (if s0 = s \<and> \<not>b0 then 1 else 0)"
        using hcount_tl[of "\<lambda>(t,b). t = s \<and> b"] by (by100 simp)
      have hfalse_w: "length (filter (\<lambda>(t,b). t = s \<and> \<not>b) w)
          = (if s0 = s \<and> \<not>b0 then 1 else 0) + length (filter (\<lambda>(t,b). t = s \<and> \<not>b) ?w')
            + (if s0 = s \<and> b0 then 1 else 0)"
        using hcount_tl[of "\<lambda>(t,b). t = s \<and> \<not>b"] by (by100 simp)
      thus "length (filter (\<lambda>(t,b). t = s \<and> b) ?w') = length (filter (\<lambda>(t,b). t = s \<and> \<not>b) ?w')"
        using \<open>length (filter (\<lambda>(t,b). t = s \<and> b) w) = length (filter (\<lambda>(t,b). t = s \<and> \<not>b) w)\<close>
              htrue_w hfalse_w by (by100 linarith)
    qed
    have hset_sub: "set ?w' \<subseteq> set w"
    proof (rule subsetI)
      fix x assume "x \<in> set ?w'"
      have "set ?w' \<subseteq> set (take (j-1) (tl w)) \<union> set (drop j (tl w))" by (by100 auto)
      moreover have "set (take (j-1) (tl w)) \<subseteq> set (tl w)" by (rule set_take_subset)
      moreover have "set (drop j (tl w)) \<subseteq> set (tl w)" by (rule set_drop_subset)
      moreover have "set (tl w) \<subseteq> set w"
        by (cases w) (by100 auto)+
      ultimately show "x \<in> set w" using \<open>x \<in> set ?w'\<close> by (by100 blast)
    qed
    have hphi': "\<forall>s \<in> fst ` set ?w'. \<phi> s \<in> H"
      using less(2) hset_sub by (by100 blast)
    have "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ?w') = eH"
      using less(1)[OF hlen hphi' hzero'] by (by100 blast)
    \<comment> \<open>Now show eval\_H(w) = eval\_H(?w') using foldr mul + abelian\_foldr\_mul\_extract.\<close>
    \<comment> \<open>The approach: via word\_product\_as\_foldr, work at the foldr mul level.
       Extract genH(w!0) and genH(w!j) from the product — they cancel (inverse pair).
       The remaining product = eval\_H(?w').\<close>
    \<comment> \<open>Apply word\_product\_cancel\_matching\_pair on the \<phi>-mapped word.\<close>
    let ?mw = "map (\<lambda>(s,b). (\<phi> s, b)) w"
    have hmw_G: "\<forall>i<length ?mw. fst (?mw ! i) \<in> H"
    proof (intro allI impI)
      fix i assume "i < length ?mw"
      hence hi: "i < length w" by (by100 simp)
      obtain si bi where hwi: "w ! i = (si, bi)" by (cases "w ! i") (by100 blast)
      have "si \<in> fst ` set w" using hi hwi nth_mem by (by100 force)
      hence "\<phi> si \<in> H" using less(2) by (by100 blast)
      thus "fst (?mw ! i) \<in> H" using hi hwi by (by100 simp)
    qed
    have hmw_0: "?mw ! 0 = (\<phi> s0, b0)" using h0_len hfirst by (by100 simp)
    have hmw_j: "?mw ! j = (\<phi> s0, \<not>b0)" using hj hwj by (by100 simp)
    have hmw_jlen: "j < length ?mw" using hj by (by100 simp)
    have "top1_group_word_product mulH eH invgH ?mw
        = top1_group_word_product mulH eH invgH (tl (take j ?mw) @ drop (Suc j) ?mw)"
      apply (rule word_product_cancel_matching_pair[where s="\<phi> s0" and b=b0])
      apply (rule hH)
      apply (rule hmw_G)
      apply (rule hmw_0)
      apply (rule hj0)
      apply (rule hmw_jlen)
      apply (rule hmw_j)
      done
    \<comment> \<open>And tl(take j ?mw) @ drop(Suc j) ?mw = map \<phi> ?w'.\<close>
    moreover have "tl (take j ?mw) @ drop (Suc j) ?mw = map (\<lambda>(s,b). (\<phi> s, b)) ?w'"
      by (rule tl_take_drop_map_pair[OF hj0])
    ultimately have "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) w)
        = top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ?w')"
      by (by100 simp)
    thus ?thesis using \<open>top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ?w') = eH\<close>
      by (by100 simp)
  qed
qed

text \<open>Helper: every element of the generated subgroup has a word representation.\<close>
lemma subgroup_generated_word_rep:
  assumes hG: "top1_is_group_on G mul e invg"
      and hS: "X \<subseteq> G"
      and hg: "g \<in> top1_subgroup_generated_on G mul e invg X"
  shows "\<exists>ws. (\<forall>i<length ws. fst (ws ! i) \<in> X) \<and> g = top1_group_word_product mul e invg ws"
proof -
  let ?W = "{g. \<exists>ws. (\<forall>i<length ws. fst (ws ! i) \<in> X) \<and> g = top1_group_word_product mul e invg ws}"
  have hW_sub: "?W \<subseteq> G"
  proof (rule subsetI)
    fix g assume "g \<in> ?W"
    then obtain ws where hws: "\<forall>i<length ws. fst (ws!i) \<in> X"
        and hg: "g = top1_group_word_product mul e invg ws" by (by100 blast)
    have "\<forall>i<length ws. fst (ws!i) \<in> G" using hws hS by (by100 blast)
    thus "g \<in> G" using hg word_product_in_group[OF hG] by (by100 blast)
  qed
  have hX_sub: "X \<subseteq> ?W"
  proof (rule subsetI)
    fix x assume hx: "x \<in> X"
    have "x \<in> G" using hx hS by (by100 blast)
    hence "x = top1_group_word_product mul e invg [(x, True)]"
      using hG unfolding top1_is_group_on_def by (by100 simp)
    moreover have "\<forall>i<length [(x, True)]. fst ([(x, True)] ! i) \<in> X"
      using hx by (by100 auto)
    ultimately show "x \<in> ?W" by (by100 blast)
  qed
  have hW_grp: "top1_is_group_on ?W mul e invg"
  proof -
    have he: "e \<in> ?W"
    proof -
      let ?ws = "[]::('a \<times> bool) list"
      have "(\<forall>i<length ?ws. fst (?ws ! i) \<in> X) \<and> e = top1_group_word_product mul e invg ?ws"
        by (by100 simp)
      thus ?thesis by (by100 blast)
    qed
    have hmul: "\<forall>a\<in>?W. \<forall>b\<in>?W. mul a b \<in> ?W"
    proof (intro ballI)
      fix a b assume "a \<in> ?W" "b \<in> ?W"
      then obtain ws1 ws2 where hw1: "\<forall>i<length ws1. fst(ws1!i) \<in> X"
          and ha: "a = top1_group_word_product mul e invg ws1"
          and hw2: "\<forall>i<length ws2. fst(ws2!i) \<in> X"
          and hb: "b = top1_group_word_product mul e invg ws2" by (by100 blast)
      have hw1G: "\<forall>i<length ws1. fst(ws1!i) \<in> G" using hw1 hS by (by100 blast)
      have hw2G: "\<forall>i<length ws2. fst(ws2!i) \<in> G" using hw2 hS by (by100 blast)
      have "mul a b = top1_group_word_product mul e invg (ws1 @ ws2)"
        using ha hb word_product_append[OF hG hw1G hw2G] by (by100 simp)
      moreover have "\<forall>i<length (ws1 @ ws2). fst((ws1 @ ws2)!i) \<in> X"
      proof (intro allI impI)
        fix i assume hi: "i < length (ws1 @ ws2)"
        show "fst ((ws1 @ ws2) ! i) \<in> X"
        proof (cases "i < length ws1")
          case True
          hence "\<not> i < length ws1 = False" by (by100 simp)
          have "(ws1 @ ws2) ! i = ws1 ! i"
            apply (simp only: nth_append)
            using True by (by100 simp)
          thus ?thesis using hw1 True by (by100 simp)
        next
          case False
          hence "\<not> i < length ws1" by (by100 simp)
          hence "(ws1 @ ws2) ! i = ws2 ! (i - length ws1)"
            apply (simp only: nth_append if_False)
            done
          moreover have "i - length ws1 < length ws2" using hi False by (by100 simp)
          ultimately show ?thesis using hw2 by (by100 force)
        qed
      qed
      ultimately show "mul a b \<in> ?W" by (by100 blast)
    qed
    have hinv: "\<forall>a\<in>?W. invg a \<in> ?W"
    proof (intro ballI)
      fix a assume "a \<in> ?W"
      then obtain ws where hws: "\<forall>i<length ws. fst(ws!i) \<in> X"
          and ha: "a = top1_group_word_product mul e invg ws" by (by100 auto)
      have hwsG: "\<forall>i<length ws. fst(ws!i) \<in> G" using hws hS by (by100 blast)
      let ?ws' = "map (\<lambda>(x,b). (x, \<not>b)) (rev ws)"
      have "invg a = top1_group_word_product mul e invg ?ws'"
        using ha word_product_rev_inv[OF hG hwsG] by (by100 simp)
      moreover have "\<forall>i<length ?ws'. fst(?ws'!i) \<in> X"
      proof (intro allI impI)
        fix i assume hi: "i < length ?ws'"
        hence hi2: "i < length ws" using hi by (by100 simp)
        have hidx: "length ws - 1 - i < length ws" using hi2 by (by100 simp)
        have "?ws'!i = (\<lambda>(x,b). (x, \<not>b)) (rev ws ! i)" using hi2 by (by100 simp)
        have "rev ws ! i = ws ! (length ws - 1 - i)" using rev_nth hi2 by (by100 simp)
        obtain xk bk where hwk: "ws ! (length ws - 1 - i) = (xk, bk)"
          by (cases "ws ! (length ws - 1 - i)") (by100 blast)
        have "fst (?ws' ! i) = xk"
          using \<open>?ws' ! i = (\<lambda>(x,b). (x, \<not>b)) (rev ws ! i)\<close>
                \<open>rev ws ! i = ws ! (length ws - 1 - i)\<close> hwk by (by100 simp)
        moreover have "fst (ws ! (length ws - 1 - i)) = xk" using hwk by (by100 simp)
        ultimately have "fst (?ws' ! i) = fst (ws ! (length ws - 1 - i))" by (by100 simp)
        thus "fst (?ws' ! i) \<in> X" using hws hidx by (by100 simp)
      qed
      ultimately show "invg a \<in> ?W" by (by100 blast)
    qed
    have hG_assoc: "\<forall>x\<in>G. \<forall>y\<in>G. \<forall>z\<in>G. mul (mul x y) z = mul x (mul y z)"
      using hG unfolding top1_is_group_on_def by (by100 blast)
    have hG_id: "\<forall>x\<in>G. mul e x = x \<and> mul x e = x"
      using hG unfolding top1_is_group_on_def by (by100 blast)
    have hG_inv: "\<forall>x\<in>G. mul (invg x) x = e \<and> mul x (invg x) = e"
      using hG unfolding top1_is_group_on_def by (by100 blast)
    have hassoc: "\<forall>x\<in>?W. \<forall>y\<in>?W. \<forall>z\<in>?W. mul (mul x y) z = mul x (mul y z)"
      using hW_sub hG_assoc by (by5000 blast)
    have hid: "\<forall>x\<in>?W. mul e x = x \<and> mul x e = x"
      using hW_sub hG_id by (by100 blast)
    have hinverse: "\<forall>x\<in>?W. mul (invg x) x = e \<and> mul x (invg x) = e"
      using hW_sub hG_inv by (by100 blast)
    have hmul_closed: "\<forall>x\<in>?W. \<forall>y\<in>?W. mul x y \<in> ?W" using hmul by (by100 blast)
    have hinv_closed: "\<forall>x\<in>?W. invg x \<in> ?W" using hinv by (by100 blast)
    show ?thesis unfolding top1_is_group_on_def
      using he hmul_closed hinv_closed hassoc hid hinverse by (by100 blast)
  qed
  have "top1_subgroup_generated_on G mul e invg X \<subseteq> ?W"
    by (rule subgroup_generated_minimal[OF hX_sub hW_sub hW_grp])
  thus ?thesis using hg by (by100 blast)
qed

text \<open>Abelian permutation invariance for distinct lists: two distinct lists with the
  same set produce the same foldr mul product in an abelian group.\<close>
lemma abelian_foldr_perm_distinct:
  assumes hG: "top1_is_abelian_group_on G mul e invg"
      and hxs: "set xs \<subseteq> G" and hys: "set ys \<subseteq> G"
      and hdx: "distinct xs" and hdy: "distinct ys"
      and hset: "set xs = set ys"
  shows "foldr mul xs e = foldr mul ys e"
  using assms(2-6)
proof (induction xs arbitrary: ys)
  case Nil thus ?case by (by100 simp)
next
  case (Cons a rest)
  have ha_G: "a \<in> G" using Cons(2) by (by100 simp)
  have hrest_G: "set rest \<subseteq> G" using Cons(2) by (by100 simp)
  have hdrest: "distinct rest" using Cons(4) by (by100 simp)
  have ha_ys: "a \<in> set ys"
  proof -
    have "a \<in> set (a # rest)" by (by100 simp)
    thus ?thesis using Cons(6) by (by5000 blast)
  qed
  then obtain j where hj: "j < length ys" and hyj: "ys ! j = a"
    using in_set_conv_nth by (by100 metis)
  have ha_not_rest: "a \<notin> set rest" using Cons(4) by (by100 simp)
  \<comment> \<open>Decompose ys at position j: ys = take j ys @ [a] @ drop (Suc j) ys.\<close>
  let ?ys' = "take j ys @ drop (Suc j) ys"
  have hys_decomp: "ys = take j ys @ [a] @ drop (Suc j) ys"
    using id_take_nth_drop[OF hj] hyj by (by100 simp)
  \<comment> \<open>By abelian\_foldr\_mul\_extract, foldr mul ys e = mul a (foldr mul ?ys' e).\<close>
  have htake_G: "\<forall>i<length (take j ys). (take j ys) ! i \<in> G"
  proof (intro allI impI)
    fix i assume hi: "i < length (take j ys)"
    have "take j ys ! i \<in> set (take j ys)" using hi nth_mem by (by100 blast)
    moreover have "set (take j ys) \<subseteq> set ys" by (rule set_take_subset)
    ultimately show "(take j ys) ! i \<in> G" using Cons(3) by (by100 blast)
  qed
  have hdrop_G: "\<forall>i<length (drop (Suc j) ys). (drop (Suc j) ys) ! i \<in> G"
  proof (intro allI impI)
    fix i assume hi: "i < length (drop (Suc j) ys)"
    have "drop (Suc j) ys ! i \<in> set (drop (Suc j) ys)" using hi nth_mem by (by100 blast)
    moreover have "set (drop (Suc j) ys) \<subseteq> set ys" by (rule set_drop_subset)
    ultimately show "(drop (Suc j) ys) ! i \<in> G" using Cons(3) by (by100 blast)
  qed
  have "foldr mul ys e = foldr mul (take j ys @ [a] @ drop (Suc j) ys) e"
    using hys_decomp by (by100 simp)
  also have "\<dots> = mul a (foldr mul ?ys' e)"
    by (rule abelian_foldr_mul_extract[OF hG htake_G ha_G hdrop_G])
  finally have hys_eq: "foldr mul ys e = mul a (foldr mul ?ys' e)" .
  \<comment> \<open>xs side: foldr mul (a # rest) e = mul a (foldr mul rest e).\<close>
  have hxs_eq: "foldr mul (a # rest) e = mul a (foldr mul rest e)" by (by100 simp)
  \<comment> \<open>set rest = set ?ys' and distinct ?ys', all in G.\<close>
  have hys'_set: "set ?ys' = set ys - {a}"
  proof -
    have hdecomp: "set ys = set (take j ys @ [a] @ drop (Suc j) ys)"
      using hys_decomp by (by100 simp)
    hence "set ys = set (take j ys) \<union> {a} \<union> set (drop (Suc j) ys)" by (by5000 simp)
    moreover have "a \<notin> set (take j ys)"
    proof -
      from Cons(5) hys_decomp have "distinct (take j ys @ [a] @ drop (Suc j) ys)"
        by (by100 simp)
      thus ?thesis by (by5000 simp)
    qed
    moreover have "a \<notin> set (drop (Suc j) ys)"
    proof -
      from Cons(5) hys_decomp have "distinct (take j ys @ [a] @ drop (Suc j) ys)"
        by (by100 simp)
      thus ?thesis by (by5000 simp)
    qed
    moreover have "set ?ys' = set (take j ys) \<union> set (drop (Suc j) ys)" by (by5000 simp)
    ultimately show ?thesis by (by5000 blast)
  qed
  have hset_eq: "set rest = set ?ys'"
  proof -
    have "set (a # rest) = set ys" using Cons(6) .
    hence "insert a (set rest) = set ys" by (by100 simp)
    thus ?thesis using ha_not_rest hys'_set by (by5000 auto)
  qed
  have hdy': "distinct ?ys'"
  proof -
    from Cons(5) hys_decomp have "distinct (take j ys @ [a] @ drop (Suc j) ys)"
      by (by100 simp)
    hence "distinct (take j ys)" and "distinct (drop (Suc j) ys)"
        and "set (take j ys) \<inter> set (drop (Suc j) ys) = {}"
      by (by5000 simp)+
    thus ?thesis by (by5000 simp)
  qed
  have hys'_G: "set ?ys' \<subseteq> G"
    using hset_eq hrest_G by (by100 simp)
  \<comment> \<open>By IH: foldr mul rest e = foldr mul ?ys' e.\<close>
  have "foldr mul rest e = foldr mul ?ys' e"
    by (rule Cons(1)[OF hrest_G hys'_G hdrest hdy' hset_eq])
  \<comment> \<open>Combine: mul a (foldr mul rest e) = mul a (foldr mul ?ys' e).\<close>
  thus ?case using hxs_eq hys_eq by (by100 simp)
qed

text \<open>Foldr of group elements stays in G.\<close>
lemma foldr_mul_in_group:
  assumes "top1_is_group_on G mul e invg" and "set xs \<subseteq> G"
  shows "foldr mul xs e \<in> G"
  using assms(2)
proof (induction xs)
  case Nil
  have "e \<in> G" using assms(1) unfolding top1_is_group_on_def by (by100 blast)
  thus ?case by (by100 simp)
next
  case (Cons a xs)
  have "a \<in> G" using Cons(2) by (by100 simp)
  have "foldr mul xs e \<in> G" using Cons(1) Cons(2) by (by100 simp)
  have "mul a (foldr mul xs e) \<in> G"
  proof -
    have "\<forall>x\<in>G. \<forall>y\<in>G. mul x y \<in> G"
      using assms(1) unfolding top1_is_group_on_def by (by100 blast)
    thus ?thesis using \<open>a \<in> G\<close> \<open>foldr mul xs e \<in> G\<close> by (by100 blast)
  qed
  thus ?case by (by100 simp)
qed

text \<open>Group power stays in G.\<close>
lemma group_pow_in_group':
  assumes "top1_is_group_on G mul e invg" and "x \<in> G"
  shows "top1_group_pow mul e x n \<in> G"
  using assms
proof (induction n)
  case 0
  have "e \<in> G" using assms(1) unfolding top1_is_group_on_def by (by100 blast)
  thus ?case by (by100 simp)
next
  case (Suc n)
  have hmul: "\<forall>x\<in>G. \<forall>y\<in>G. mul x y \<in> G"
    using assms(1) unfolding top1_is_group_on_def by (by100 blast)
  have "top1_group_pow mul e x n \<in> G" using Suc .
  hence hpow_n: "top1_group_pow mul e x n \<in> G" .
  thus ?case using hmul assms(2) by (by100 simp)
qed

text \<open>Corollary: foldr mul (map f xs) e = foldr mul (map f ys) e when f maps into G,
  both xs/ys are distinct, and set xs = set ys. Map f may not be injective.\<close>
lemma abelian_foldr_map_perm_distinct:
  assumes hG: "top1_is_abelian_group_on G mul e invg"
      and hf: "\<forall>x \<in> set xs. f x \<in> G"
      and hdx: "distinct xs" and hdy: "distinct ys"
      and hset: "set xs = set ys"
  shows "foldr mul (map f xs) e = foldr mul (map f ys) e"
  using hf hdx hdy hset
proof (induction xs arbitrary: ys)
  case Nil
  \<comment> \<open>Nil(2) = hf, Nil(3) = hdx, Nil(4) = hdy, Nil(5) = hset.\<close>
  hence "set ys = {}" by (by100 simp)
  hence "ys = []" using Nil(4) by (by5000 simp)
  thus ?case by (by100 simp)
next
  case (Cons a rest)
  \<comment> \<open>Cons(2) = hf, Cons(3) = hdx, Cons(4) = hdy, Cons(5) = hset.\<close>
  have ha_G: "f a \<in> G" using Cons(2) by (by100 simp)
  have hrest_f: "\<forall>x \<in> set rest. f x \<in> G" using Cons(2) by (by100 auto)
  have hdy_ys: "distinct ys" using Cons(4) .
  have ha_ys: "a \<in> set ys"
  proof -
    have "a \<in> set (a # rest)" by (by100 simp)
    thus ?thesis using Cons(5) by (by5000 blast)
  qed
  then obtain j where hj: "j < length ys" and hyj: "ys ! j = a"
    using in_set_conv_nth by (by100 metis)
  let ?ys' = "take j ys @ drop (Suc j) ys"
  have hys_decomp: "ys = take j ys @ [a] @ drop (Suc j) ys"
    using id_take_nth_drop[OF hj] hyj by (by100 simp)
  have ha_not_rest: "a \<notin> set rest" using Cons(3) by (by5000 simp)
  have hys'_set: "set ?ys' = set ys - {a}"
  proof -
    have hd_ys: "distinct ys" using hdy_ys .
    from hdy_ys hys_decomp have "distinct (take j ys @ [a] @ drop (Suc j) ys)" by (by100 simp)
    hence "a \<notin> set (take j ys)" and "a \<notin> set (drop (Suc j) ys)" by (by5000 simp)+
    moreover have "set ?ys' = set (take j ys) \<union> set (drop (Suc j) ys)" by (by5000 simp)
    moreover have "set ys = set (take j ys) \<union> {a} \<union> set (drop (Suc j) ys)"
    proof -
      have "set ys = set (take j ys @ [a] @ drop (Suc j) ys)" using hys_decomp by (by100 simp)
      thus ?thesis by (by5000 simp)
    qed
    ultimately show ?thesis by (by5000 blast)
  qed
  have hset_eq: "set rest = set ?ys'"
  proof -
    have "insert a (set rest) = set ys" using Cons(5) by (by100 simp)
    thus ?thesis using ha_not_rest hys'_set by (by5000 auto)
  qed
  have hdy': "distinct ?ys'"
  proof -
    from hdy_ys hys_decomp have "distinct (take j ys @ [a] @ drop (Suc j) ys)" by (by100 simp)
    hence "distinct (take j ys)" "distinct (drop (Suc j) ys)"
        "set (take j ys) \<inter> set (drop (Suc j) ys) = {}"
      by (by5000 simp)+
    thus ?thesis by (by5000 simp)
  qed
  \<comment> \<open>foldr mul (map f ys) e = mul (f a) (foldr mul (map f ?ys') e) by extract.\<close>
  have hfoldr_ys: "foldr mul (map f ys) e = mul (f a) (foldr mul (map f ?ys') e)"
  proof -
    have "map f ys = map f (take j ys) @ [f a] @ map f (drop (Suc j) ys)"
    proof -
      have "map f ys = map f (take j ys @ [a] @ drop (Suc j) ys)" using hys_decomp by (by100 simp)
      thus ?thesis by (by100 simp)
    qed
    hence "foldr mul (map f ys) e
        = foldr mul (map f (take j ys) @ [f a] @ map f (drop (Suc j) ys)) e"
      by (by100 simp)
    also have "\<dots> = mul (f a) (foldr mul (map f (take j ys) @ map f (drop (Suc j) ys)) e)"
    proof -
      have hf_ys: "\<forall>x \<in> set ys. f x \<in> G"
        using Cons(2) Cons(5) by (by5000 blast)
      have hmf_take: "\<forall>i<length (map f (take j ys)). map f (take j ys) ! i \<in> G"
      proof (intro allI impI)
        fix i assume hi: "i < length (map f (take j ys))"
        hence "i < length (take j ys)" by (by100 simp)
        hence "take j ys ! i \<in> set (take j ys)" using nth_mem by (by100 blast)
        hence "take j ys ! i \<in> set ys" using set_take_subset[of j ys] by (by100 blast)
        hence "f (take j ys ! i) \<in> G" using hf_ys by (by100 blast)
        thus "map f (take j ys) ! i \<in> G" using \<open>i < length (take j ys)\<close> by (by100 simp)
      qed
      moreover have hmf_drop: "\<forall>i<length (map f (drop (Suc j) ys)). map f (drop (Suc j) ys) ! i \<in> G"
      proof (intro allI impI)
        fix i assume hi: "i < length (map f (drop (Suc j) ys))"
        hence "i < length (drop (Suc j) ys)" by (by100 simp)
        hence "drop (Suc j) ys ! i \<in> set (drop (Suc j) ys)" using nth_mem by (by100 blast)
        hence "drop (Suc j) ys ! i \<in> set ys" using set_drop_subset[of "Suc j" ys] by (by100 blast)
        hence "f (drop (Suc j) ys ! i) \<in> G" using hf_ys by (by100 blast)
        thus "map f (drop (Suc j) ys) ! i \<in> G" using \<open>i < length (drop (Suc j) ys)\<close> by (by100 simp)
      qed
      ultimately show ?thesis by (rule abelian_foldr_mul_extract[OF hG _ ha_G])
    qed
    also have "map f (take j ys) @ map f (drop (Suc j) ys) = map f ?ys'" by (by100 simp)
    finally show ?thesis .
  qed
  have hfoldr_xs: "foldr mul (map f (a # rest)) e = mul (f a) (foldr mul (map f rest) e)"
    by (by100 simp)
  have hdrest: "distinct rest" using Cons(3) by (by5000 simp)
  have hIH: "foldr mul (map f rest) e = foldr mul (map f ?ys') e"
    by (rule Cons(1)[OF hrest_f hdrest hdy' hset_eq])
  show ?case using hfoldr_xs hfoldr_ys hIH by (by100 simp)
qed

text \<open>Split one element type from foldr product: pow(v, count) \<cdot> rest.\<close>
lemma abelian_foldr_split_one_element:
  assumes hG: "top1_is_abelian_group_on G mul e invg"
      and hgs: "set gs \<subseteq> G" and hv: "v \<in> G"
  shows "foldr mul gs e
       = mul (top1_group_pow mul e v (length (filter (\<lambda>x. x = v) gs)))
             (foldr mul (filter (\<lambda>x. x \<noteq> v) gs) e)"
proof -
  have hG_grp: "top1_is_group_on G mul e invg"
    using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hgs': "\<forall>i<length gs. gs ! i \<in> G"
  proof (intro allI impI)
    fix i assume "i < length gs"
    hence "gs ! i \<in> set gs" using nth_mem by (by100 blast)
    thus "gs ! i \<in> G" using hgs by (by100 blast)
  qed
  have hsplit: "foldr mul gs e
      = mul (foldr mul (filter (\<lambda>x. x = v) gs) e) (foldr mul (filter (\<lambda>x. x \<noteq> v) gs) e)"
    by (rule abelian_foldr_mul_split_filter[OF hG hgs', of "\<lambda>x. x = v"])
  have hpow: "foldr mul (filter (\<lambda>x. x = v) gs) e
      = top1_group_pow mul e v (length (filter (\<lambda>x. x = v) gs))"
    by (rule abelian_foldr_mul_filter_eq[OF hG_grp hv])
  show ?thesis using hsplit hpow by (by100 simp)
qed

text \<open>In an abelian group, if one element in a list is replaced by mul(a, element),
  the foldr product is multiplied by a.\<close>
lemma abelian_foldr_replace_one:
  assumes hG: "top1_is_abelian_group_on G mul e invg"
      and hxs: "set xs \<subseteq> G" and hys: "set ys \<subseteq> G"
      and ha: "a \<in> G"
      and hlen: "length xs = length ys"
      and hj: "j < length xs"
      and hat_j: "xs ! j = mul a (ys ! j)"
      and hothers: "\<forall>i<length xs. i \<noteq> j \<longrightarrow> xs ! i = ys ! i"
  shows "foldr mul xs e = mul a (foldr mul ys e)"
proof -
  have hG_grp: "top1_is_group_on G mul e invg"
    using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
  \<comment> \<open>Decompose xs at position j: xs = take j xs @ [xs!j] @ drop (Suc j) xs.\<close>
  have hxs_decomp: "xs = take j xs @ [xs ! j] @ drop (Suc j) xs"
    using id_take_nth_drop[OF hj] by (by100 simp)
  have hys_decomp: "ys = take j ys @ [ys ! j] @ drop (Suc j) ys"
    using id_take_nth_drop[OF hj[unfolded hlen]] hlen by (by100 simp)
  \<comment> \<open>By abelian\_foldr\_mul\_extract on xs:\<close>
  have htake_xs_G: "\<forall>i<length (take j xs). (take j xs) ! i \<in> G"
  proof (intro allI impI)
    fix i assume "i < length (take j xs)"
    have "(take j xs) ! i \<in> set (take j xs)" using nth_mem \<open>i < length (take j xs)\<close> by (by100 blast)
    hence "(take j xs) ! i \<in> set xs" using set_take_subset[of j xs] by (by100 blast)
    thus "(take j xs) ! i \<in> G" using hxs by (by100 blast)
  qed
  have hdrop_xs_G: "\<forall>i<length (drop (Suc j) xs). (drop (Suc j) xs) ! i \<in> G"
  proof (intro allI impI)
    fix i assume "i < length (drop (Suc j) xs)"
    have "(drop (Suc j) xs) ! i \<in> set (drop (Suc j) xs)"
      using nth_mem \<open>i < length (drop (Suc j) xs)\<close> by (by100 blast)
    hence "(drop (Suc j) xs) ! i \<in> set xs" using set_drop_subset[of "Suc j" xs] by (by100 blast)
    thus "(drop (Suc j) xs) ! i \<in> G" using hxs by (by100 blast)
  qed
  have hxs_j_G: "xs ! j \<in> G"
  proof -
    have "xs ! j \<in> set xs" using hj nth_mem by (by100 blast)
    thus ?thesis using hxs by (by100 blast)
  qed
  have hj_ys: "j < length ys" using hj hlen by (by100 simp)
  have hys_j_G: "ys ! j \<in> G"
  proof -
    have "ys ! j \<in> set ys" using hj_ys nth_mem by (by100 blast)
    thus ?thesis using hys by (by100 blast)
  qed
  have hfoldr_xs: "foldr mul xs e = mul (xs ! j) (foldr mul (take j xs @ drop (Suc j) xs) e)"
    using hxs_decomp abelian_foldr_mul_extract[OF hG htake_xs_G hxs_j_G hdrop_xs_G] by (by100 simp)
  \<comment> \<open>Similarly for ys:\<close>
  have htake_ys_G: "\<forall>i<length (take j ys). (take j ys) ! i \<in> G"
  proof (intro allI impI)
    fix i assume "i < length (take j ys)"
    have "(take j ys) ! i \<in> set (take j ys)" using nth_mem \<open>i < length (take j ys)\<close> by (by100 blast)
    hence "(take j ys) ! i \<in> set ys" using set_take_subset[of j ys] by (by100 blast)
    thus "(take j ys) ! i \<in> G" using hys by (by100 blast)
  qed
  have hdrop_ys_G: "\<forall>i<length (drop (Suc j) ys). (drop (Suc j) ys) ! i \<in> G"
  proof (intro allI impI)
    fix i assume "i < length (drop (Suc j) ys)"
    have "(drop (Suc j) ys) ! i \<in> set (drop (Suc j) ys)"
      using nth_mem \<open>i < length (drop (Suc j) ys)\<close> by (by100 blast)
    hence "(drop (Suc j) ys) ! i \<in> set ys" using set_drop_subset[of "Suc j" ys] by (by100 blast)
    thus "(drop (Suc j) ys) ! i \<in> G" using hys by (by100 blast)
  qed
  have hfoldr_ys: "foldr mul ys e = mul (ys ! j) (foldr mul (take j ys @ drop (Suc j) ys) e)"
    using hys_decomp abelian_foldr_mul_extract[OF hG htake_ys_G hys_j_G hdrop_ys_G] by (by100 simp)
  \<comment> \<open>The take/drop parts are equal (elements agree at all positions \<noteq> j).\<close>
  have htake_eq: "take j xs = take j ys"
  proof (rule nth_equalityI)
    show "length (take j xs) = length (take j ys)" using hlen by (by100 simp)
    fix i assume "i < length (take j xs)"
    hence hi: "i < j" by (by5000 simp)
    hence "i < length xs" and "i \<noteq> j" using hj by (by100 simp)+
    hence "xs ! i = ys ! i" using hothers by (by100 blast)
    thus "take j xs ! i = take j ys ! i" using hi hj hj_ys by (by5000 simp)
  qed
  have hdrop_eq: "drop (Suc j) xs = drop (Suc j) ys"
  proof (rule nth_equalityI)
    show "length (drop (Suc j) xs) = length (drop (Suc j) ys)" using hlen by (by100 simp)
    fix i assume "i < length (drop (Suc j) xs)"
    hence hi: "i + Suc j < length xs" by (by100 simp)
    hence "i + Suc j \<noteq> j" by (by100 simp)
    have hisj: "i + Suc j < length xs" using hi .
    have hisj_ne: "i + Suc j \<noteq> j" by (by100 simp)
    have "xs ! (i + Suc j) = ys ! (i + Suc j)" using hothers hisj hisj_ne by (by100 blast)
    moreover have "drop (Suc j) xs ! i = xs ! (i + Suc j)" using hi by (simp add: add.commute)
    moreover have "drop (Suc j) ys ! i = ys ! (i + Suc j)" using hi hlen by (simp add: add.commute)
    ultimately show "drop (Suc j) xs ! i = drop (Suc j) ys ! i" by (by100 simp)
  qed
  \<comment> \<open>Combine: xs!j = mul a (ys!j), so foldr xs = mul (mul a (ys!j)) rest = mul a (mul (ys!j) rest).\<close>
  have hassoc: "mul (xs ! j) (foldr mul (take j xs @ drop (Suc j) xs) e)
      = mul a (mul (ys ! j) (foldr mul (take j ys @ drop (Suc j) ys) e))"
  proof -
    have "mul (xs ! j) (foldr mul (take j xs @ drop (Suc j) xs) e)
        = mul (mul a (ys ! j)) (foldr mul (take j ys @ drop (Suc j) ys) e)"
      using hat_j htake_eq hdrop_eq by (by100 simp)
    also have "\<dots> = mul a (mul (ys ! j) (foldr mul (take j ys @ drop (Suc j) ys) e))"
    proof -
      have hrest_G: "foldr mul (take j ys @ drop (Suc j) ys) e \<in> G"
      proof -
        have "set (take j ys @ drop (Suc j) ys) \<subseteq> set ys"
          using set_take_subset[of j ys] set_drop_subset[of "Suc j" ys] by (by100 auto)
        hence "set (take j ys @ drop (Suc j) ys) \<subseteq> G" using hys by (by100 blast)
        thus ?thesis by (rule foldr_mul_in_group[OF hG_grp])
      qed
      show ?thesis using hG_grp ha hys_j_G hrest_G
        unfolding top1_is_group_on_def by (by5000 blast)
    qed
    finally show ?thesis .
  qed
  show ?thesis using hfoldr_xs hassoc hfoldr_ys by (by100 simp)
qed

text \<open>In an abelian group, foldr of a list decomposes into per-element powers,
  collected by remdups. Proved by induction on the list.\<close>
lemma abelian_foldr_remdups_pow:
  assumes hG: "top1_is_abelian_group_on G mul e invg"
      and hgs: "set gs \<subseteq> G"
  shows "foldr mul gs e
       = foldr mul (map (\<lambda>v. top1_group_pow mul e v (length (filter (\<lambda>x. x = v) gs))) (remdups gs)) e"
  using hgs
proof (induction gs)
  case Nil show ?case by (by100 simp)
next
  case (Cons a rest)
  have ha_G: "a \<in> G" using Cons(2) by (by100 simp)
  have hrest_G: "set rest \<subseteq> G" using Cons(2) by (by100 auto)
  let ?powfn = "\<lambda>v. top1_group_pow mul e v (length (filter (\<lambda>x. x = v) (a # rest)))"
  let ?powfn_r = "\<lambda>v. top1_group_pow mul e v (length (filter (\<lambda>x. x = v) rest))"
  have hIH: "foldr mul rest e = foldr mul (map ?powfn_r (remdups rest)) e"
    using Cons(1)[OF hrest_G] .
  show ?case
  proof (cases "a \<in> set rest")
    case False
    \<comment> \<open>a not in rest: remdups(a#rest) = a # remdups rest.\<close>
    have hremdups: "remdups (a # rest) = a # remdups rest"
      using False by (by100 simp)
    \<comment> \<open>count(a, a#rest) = 1 since a \<notin> rest, count(v, a#rest) = count(v, rest) for v \<noteq> a.\<close>
    have hcount_a: "length (filter (\<lambda>x. x = a) (a # rest)) = Suc 0"
    proof -
      have "filter (\<lambda>x. x = a) rest = []"
        using False filter_empty_conv by (by5000 fast)
      thus ?thesis by (by100 simp)
    qed
    have hcount_other: "\<forall>v \<in> set (remdups rest). v \<noteq> a \<longrightarrow>
        length (filter (\<lambda>x. x = v) (a # rest)) = length (filter (\<lambda>x. x = v) rest)"
      by (by5000 auto)
    \<comment> \<open>pow(a, 1) = mul(a, e) which we need = a. Use right identity.\<close>
    have hpow1: "top1_group_pow mul e a (Suc 0) = mul a e"
      by (by100 simp)
    have hG_grp: "top1_is_group_on G mul e invg"
      using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
    have hrid: "mul a e = a"
      using hG_grp ha_G unfolding top1_is_group_on_def by (by100 blast)
    \<comment> \<open>Map is: ?powfn a = pow(a, 1) = a; ?powfn v = ?powfn\_r v for v \<noteq> a.\<close>
    \<comment> \<open>powfn v = powfn\_r v for v \<in> remdups rest (since v \<noteq> a, count unchanged).\<close>
    have hpowfn_eq: "\<forall>v \<in> set (remdups rest). ?powfn v = ?powfn_r v"
    proof (intro ballI)
      fix v assume "v \<in> set (remdups rest)"
      hence "v \<noteq> a" using False by (by5000 auto)
      hence "filter (\<lambda>x. x = v) (a # rest) = filter (\<lambda>x. x = v) rest"
        by (by100 simp)
      thus "?powfn v = ?powfn_r v" by (by100 simp)
    qed
    have hmap_eq: "map ?powfn (remdups (a # rest)) = a # map ?powfn_r (remdups rest)"
    proof -
      have "map ?powfn (remdups (a # rest)) = map ?powfn (a # remdups rest)"
        using hremdups by (by100 simp)
      also have "\<dots> = ?powfn a # map ?powfn (remdups rest)" by (by100 simp)
      also have "?powfn a = a" using hcount_a hpow1 hrid by (by100 simp)
      also have "map ?powfn (remdups rest) = map ?powfn_r (remdups rest)"
        using hpowfn_eq by (by5000 auto)
      finally show ?thesis by (by100 simp)
    qed
    \<comment> \<open>LHS = mul(a, foldr mul rest e) = mul(a, foldr mul (map powfn\_r (remdups rest)) e) by IH.
       RHS = foldr mul (a # map powfn\_r (remdups rest)) e = mul(a, foldr mul (map ...) e).\<close>
    show ?thesis
    proof -
      have "foldr mul (a # rest) e = mul a (foldr mul rest e)" by (by100 simp)
      also have "\<dots> = mul a (foldr mul (map ?powfn_r (remdups rest)) e)" using hIH by (by100 simp)
      also have "\<dots> = foldr mul (a # map ?powfn_r (remdups rest)) e" by (by100 simp)
      also have "a # map ?powfn_r (remdups rest) = map ?powfn (remdups (a # rest))"
        using hmap_eq by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
  next
    case True
    \<comment> \<open>a in rest: remdups(a#rest) = remdups rest.
       count(a, a#rest) = 1 + count(a, rest), others unchanged.
       Need: mul(a, foldr mul (map powfn\_r (remdups rest)) e)
            = foldr mul (map powfn (remdups rest)) e
       where powfn is powfn\_r except at a: pow(a, count+1) = mul(a, pow(a, count)).\<close>
    have hremdups_eq: "remdups (a # rest) = remdups rest"
      using True by (by100 simp)
    \<comment> \<open>LHS: foldr mul (a # rest) e = mul a (foldr mul (map powfn\_r (remdups rest)) e).\<close>
    have hLHS: "foldr mul (a # rest) e = mul a (foldr mul (map ?powfn_r (remdups rest)) e)"
      using hIH by (by100 simp)
    \<comment> \<open>RHS: foldr mul (map powfn (remdups (a#rest))) e = foldr mul (map powfn (remdups rest)) e.\<close>
    \<comment> \<open>Key: powfn v = powfn\_r v for v \<noteq> a, and powfn a = mul(a, powfn\_r a).\<close>
    have hpowfn_a: "?powfn a = mul a (?powfn_r a)"
      by (by5000 simp)
    have hpowfn_other: "\<forall>v \<in> set (remdups rest). v \<noteq> a \<longrightarrow> ?powfn v = ?powfn_r v"
      by (by5000 auto)
    \<comment> \<open>map powfn (remdups rest) = (at position of a, replace powfn\_r a with mul(a, powfn\_r a)).
       By abelian extract: foldr mul (map powfn (remdups rest)) e
       = mul a (foldr mul (map powfn\_r (remdups rest)) e).\<close>
    have ha_in_rem: "a \<in> set (remdups rest)" using True by (by100 simp)
    then obtain j where hj: "j < length (remdups rest)" and hremj: "remdups rest ! j = a"
      using in_set_conv_nth by (by100 metis)
    \<comment> \<open>Decompose: remdups rest = take j (remdups rest) @ [a] @ drop (Suc j) (remdups rest).\<close>
    \<comment> \<open>Then map powfn (remdups rest) = (take part, with powfn\_r) @ [mul(a, powfn\_r a)] @ (drop part, with powfn\_r).
       And map powfn\_r (remdups rest) = (take part, with powfn\_r) @ [powfn\_r a] @ (drop part, with powfn\_r).
       By abelian extract: the extra factor a can be extracted.\<close>
    \<comment> \<open>Simpler approach: use abelian\_foldr\_split\_one\_element on map powfn (remdups rest)
       to split by a. Then relate.\<close>
    have hRHS: "foldr mul (map ?powfn (remdups rest)) e
        = mul a (foldr mul (map ?powfn_r (remdups rest)) e)"
    proof -
      \<comment> \<open>Apply abelian\_foldr\_replace\_one: map powfn (remdups rest) differs from
         map powfn\_r (remdups rest) exactly at position j (where a sits):
         powfn a = mul(a, powfn\_r a), all others equal.\<close>
      have hG_grp_loc: "top1_is_group_on G mul e invg"
        using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
      have hset_powfn: "set (map ?powfn (remdups rest)) \<subseteq> G"
      proof (rule subsetI)
        fix y assume "y \<in> set (map ?powfn (remdups rest))"
        then obtain v where "v \<in> set (remdups rest)" and hy: "y = ?powfn v" by (by100 auto)
        hence "v \<in> set rest" by (by100 simp)
        hence "v \<in> G" using hrest_G by (by100 blast)
        thus "y \<in> G" using hy group_pow_in_group'[OF hG_grp_loc \<open>v \<in> G\<close>] by (by100 simp)
      qed
      have hset_powfn_r: "set (map ?powfn_r (remdups rest)) \<subseteq> G"
      proof (rule subsetI)
        fix y assume "y \<in> set (map ?powfn_r (remdups rest))"
        then obtain v where "v \<in> set (remdups rest)" and hy: "y = ?powfn_r v" by (by100 auto)
        hence "v \<in> set rest" by (by100 simp)
        hence "v \<in> G" using hrest_G by (by100 blast)
        thus "y \<in> G" using hy group_pow_in_group'[OF hG_grp_loc \<open>v \<in> G\<close>] by (by100 simp)
      qed
      have hlen_maps: "length (map ?powfn (remdups rest)) = length (map ?powfn_r (remdups rest))"
        by (by100 simp)
      have hj_map: "j < length (map ?powfn (remdups rest))" using hj by (by100 simp)
      have hat_j: "map ?powfn (remdups rest) ! j = mul a (map ?powfn_r (remdups rest) ! j)"
      proof -
        have "map ?powfn (remdups rest) ! j = ?powfn (remdups rest ! j)"
          using hj by (by100 simp)
        also have "remdups rest ! j = a" using hremj .
        also have "?powfn a = mul a (?powfn_r a)" using hpowfn_a .
        also have "?powfn_r a = map ?powfn_r (remdups rest) ! j"
          using hj hremj by (by100 simp)
        finally show ?thesis by (by100 simp)
      qed
      have hothers_j: "\<forall>i<length (map ?powfn (remdups rest)). i \<noteq> j \<longrightarrow>
          map ?powfn (remdups rest) ! i = map ?powfn_r (remdups rest) ! i"
      proof (intro allI impI)
        fix i assume "i < length (map ?powfn (remdups rest))" and "i \<noteq> j"
        hence hi: "i < length (remdups rest)" by (by100 simp)
        have hv: "remdups rest ! i \<noteq> a"
        proof -
          have "remdups rest ! i \<noteq> remdups rest ! j"
          proof -
            have "distinct (remdups rest)" by (by100 simp)
            from nth_eq_iff_index_eq[OF this hi hj]
            show ?thesis using \<open>i \<noteq> j\<close> by (by100 simp)
          qed
          thus ?thesis using hremj by (by100 simp)
        qed
        have "remdups rest ! i \<in> set (remdups rest)" using hi nth_mem by (by100 blast)
        hence "?powfn (remdups rest ! i) = ?powfn_r (remdups rest ! i)"
          using hpowfn_other hv by (by100 blast)
        thus "map ?powfn (remdups rest) ! i = map ?powfn_r (remdups rest) ! i"
          using hi by (by100 simp)
      qed
      show ?thesis
        by (rule abelian_foldr_replace_one[OF hG hset_powfn hset_powfn_r ha_G hlen_maps hj_map hat_j hothers_j])
    qed
    have "foldr mul (a # rest) e
        = foldr mul (map ?powfn (remdups (a # rest))) e"
    proof -
      have "foldr mul (a # rest) e = mul a (foldr mul (map ?powfn_r (remdups rest)) e)"
        using hLHS .
      also have "\<dots> = foldr mul (map ?powfn (remdups rest)) e"
        using hRHS by (by100 simp)
      also have "\<dots> = foldr mul (map ?powfn (remdups (a # rest))) e"
        using hremdups_eq by (by100 simp)
      finally show ?thesis .
    qed
    thus ?thesis .
  qed
qed

text \<open>For any ordering of a 2-element set in an abelian group, the foldr product
  equals mul(f a, f b) (order doesn't matter).\<close>
lemma abelian_foldr_two_element:
  assumes hG: "top1_is_abelian_group_on G mul e invg"
      and hfa: "f a \<in> G" and hfb: "f b \<in> G" and hab: "a \<noteq> b"
      and hxs: "set xs = {a, b}" and hdx: "distinct xs"
  shows "foldr mul (map f xs) e = mul (f a) (f b)"
proof -
  have hG_grp: "top1_is_group_on G mul e invg"
    using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hlen: "length xs = 2"
  proof -
    have "card {a, b} = 2" using hab by (by100 simp)
    hence "card (set xs) = 2" using hxs by (by100 simp)
    moreover have "length xs = card (set xs)" using hdx by (rule distinct_card[symmetric])
    ultimately show ?thesis by (by100 simp)
  qed
  then obtain x0 x1 where hxs_eq: "xs = [x0, x1]"
  proof -
    from hlen obtain x0 rest where "xs = x0 # rest" and "length rest = 1"
      by (cases xs) (by100 simp)+
    from \<open>length rest = 1\<close> obtain x1 where "rest = [x1]"
      by (cases rest) (by100 simp)+
    thus ?thesis using that \<open>xs = x0 # rest\<close> by (by100 simp)
  qed
  have hset01: "{x0, x1} = {a, b}" using hxs hxs_eq by (by100 simp)
  have hne01: "x0 \<noteq> x1" using hdx hxs_eq by (by100 simp)
  have hfoldr: "foldr mul (map f xs) e = mul (f x0) (mul (f x1) e)"
    using hxs_eq by (by100 simp)
  have "f x1 \<in> G"
  proof -
    have "x1 \<in> {a, b}" using hset01 by (by100 blast)
    thus ?thesis using hfa hfb by (by100 blast)
  qed
  have hrid: "mul (f x1) e = f x1"
    using hG_grp \<open>f x1 \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
  have hfoldr2: "foldr mul (map f xs) e = mul (f x0) (f x1)"
    using hfoldr hrid by (by100 simp)
  have hx0_ab: "x0 \<in> {a, b}" and hx1_ab: "x1 \<in> {a, b}"
    using hset01 by (by100 auto)+
  have "(x0 = a \<and> x1 = b) \<or> (x0 = b \<and> x1 = a)"
  proof (cases "x0 = a")
    case True hence "x1 = b" using hne01 hx1_ab by (by100 blast)
    thus ?thesis using True by (by100 blast)
  next
    case False hence "x0 = b" using hx0_ab by (by100 blast)
    hence "x1 = a" using hne01 hx1_ab by (by100 blast)
    thus ?thesis using \<open>x0 = b\<close> by (by100 blast)
  qed
  thus ?thesis
  proof
    assume "x0 = a \<and> x1 = b"
    thus ?thesis using hfoldr2 by (by100 simp)
  next
    assume "x0 = b \<and> x1 = a"
    hence "foldr mul (map f xs) e = mul (f b) (f a)" using hfoldr2 by (by100 simp)
    moreover have "mul (f b) (f a) = mul (f a) (f b)"
      using hG hfa hfb unfolding top1_is_abelian_group_on_def by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
qed

text \<open>Two filters agree if predicates agree pointwise on set.\<close>
lemma filter_pred_eq:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> P x = Q x"
  shows "filter P xs = filter Q xs"
  using assms by (induction xs) (by100 simp)+

text \<open>Canonical product over a 2-element support {s1, s2} equals mul(term s1, term s2).\<close>
lemma canonical_product_two_eq:
  assumes hG: "top1_is_abelian_group_on G mul e invg"
      and hfa: "f a \<in> G" and hfb: "f b \<in> G" and hab: "a \<noteq> b"
  shows "foldr mul (map f (SOME xs. set xs = {a, b} \<and> distinct xs)) e = mul (f a) (f b)"
proof -
  have "\<exists>xs. set xs = {a, b} \<and> distinct xs"
  proof -
    have "set [a, b] = {a, b}" by (by100 simp)
    moreover have "distinct [a, b]" using hab by (by100 simp)
    ultimately show ?thesis by (by100 blast)
  qed
  hence hspec: "set (SOME xs. set xs = {a, b} \<and> distinct xs) = {a, b}
      \<and> distinct (SOME xs. set xs = {a, b} \<and> distinct xs)"
    by (rule someI_ex)
  show ?thesis
    by (rule abelian_foldr_two_element[OF hG hfa hfb hab])
       (use hspec in \<open>by100 blast\<close>)+
qed

text \<open>remdups commutes with map when the function is injective.\<close>
lemma remdups_map_inj_on:
  assumes "inj_on f (set xs)"
  shows "remdups (map f xs) = map f (remdups xs)"
  using assms
proof (induction xs)
  case Nil show ?case by (by100 simp)
next
  case (Cons a rest)
  have hIH: "remdups (map f rest) = map f (remdups rest)"
    using Cons(1) Cons(2) by (by5000 auto)
  have "f a \<in> set (map f rest) \<longleftrightarrow> a \<in> set rest"
  proof
    assume "f a \<in> set (map f rest)"
    then obtain a' where "a' \<in> set rest" "f a' = f a" by (by100 auto)
    have "a' \<in> set (a # rest)" using \<open>a' \<in> set rest\<close> by (by100 simp)
    moreover have "a \<in> set (a # rest)" by (by100 simp)
    ultimately have "a' = a"
      using Cons(2) \<open>f a' = f a\<close> unfolding inj_on_def by (by100 blast)
    thus "a \<in> set rest" using \<open>a' \<in> set rest\<close> by (by100 simp)
  next
    assume "a \<in> set rest" thus "f a \<in> set (map f rest)" by (by100 force)
  qed
  thus ?case using hIH by (by100 simp)
qed

text \<open>For single-polarity pairs, map fst (remdups w) = remdups (map fst w).\<close>
lemma remdups_fst_single_pol:
  assumes "\<forall>s b. (s, b) \<in> set w \<longrightarrow> (s, \<not>b) \<notin> set w"
  shows "map fst (remdups w) = remdups (map fst w)"
  using assms
proof (induction w)
  case Nil show ?case by (by100 simp)
next
  case (Cons a rest)
  obtain s b where ha: "a = (s, b)" by (cases a) (by100 blast)
  have huni_rest: "\<forall>s b. (s, b) \<in> set rest \<longrightarrow> (s, \<not>b) \<notin> set rest"
    using Cons(2) by (by100 auto)
  have hIH: "map fst (remdups rest) = remdups (map fst rest)"
    using Cons(1)[OF huni_rest] .
  \<comment> \<open>Key: a \<in> set rest \<longleftrightarrow> fst a \<in> set (map fst rest), because single polarity means
     if (s, b') \<in> set rest with fst = s = fst a, then b' = b (since \<not>b not in set).\<close>
  have "a \<in> set rest \<longleftrightarrow> fst a \<in> set (map fst rest)"
  proof
    assume "a \<in> set rest" thus "fst a \<in> set (map fst rest)" by (by100 force)
  next
    assume "fst a \<in> set (map fst rest)"
    then obtain b' where "(s, b') \<in> set rest" using ha by (by100 force)
    have "b' = b"
    proof (rule ccontr)
      assume "b' \<noteq> b"
      hence "b' = (\<not>b)" by (by100 auto)
      hence "(s, \<not>b) \<in> set rest" using \<open>(s, b') \<in> set rest\<close> by (by100 simp)
      hence "(s, \<not>b) \<in> set (a # rest)" by (by100 simp)
      moreover have "(s, b) \<in> set (a # rest)" using ha by (by100 simp)
      ultimately show False using Cons(2) by (by5000 blast)
    qed
    thus "a \<in> set rest" using \<open>(s, b') \<in> set rest\<close> ha by (by100 simp)
  qed
  thus ?case using ha hIH by (by100 simp)
qed

text \<open>In a free abelian group, if a nonempty word has no matching pairs,
  the word product \<noteq> e. Follows the book: decompose into per-generator
  powers, apply direct sum / independence condition.\<close>
lemma no_matching_pair_word_ne_e:
  fixes w :: "('s \<times> bool) list"
  assumes hfree: "top1_is_free_abelian_group_full_on G mul e invg \<iota> S"
      and hall: "\<forall>s \<in> fst ` set w. s \<in> S"
      and hne: "w \<noteq> []"
      and huni: "\<forall>s b. (s, b) \<in> set w \<longrightarrow> (s, \<not>b) \<notin> set w"
  shows "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) w) \<noteq> e"
proof -
  have hG_abel: "top1_is_abelian_group_on G mul e invg"
    using hfree unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  have hG_grp: "top1_is_group_on G mul e invg"
    using hG_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
  have h\<iota>_in: "\<forall>s\<in>S. \<iota> s \<in> G"
    using hfree unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  \<comment> \<open>Step 1: Convert word\_product to foldr form.\<close>
  let ?gen = "\<lambda>(s::'s,b::bool). if b then \<iota> s else invg (\<iota> s)"
  let ?gs = "map ?gen w"
  have heval_foldr: "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) w) = foldr mul ?gs e"
  proof -
    have "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) w)
        = foldr mul (map (\<lambda>(x,b). if b then x else invg x) (map (\<lambda>(s,b). (\<iota> s, b)) w)) e"
      by (rule word_product_as_foldr)
    also have "map (\<lambda>(x,b). if b then x else invg x) (map (\<lambda>(s,b). (\<iota> s, b)) w) = ?gs"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>(x,b). if b then x else invg x) (map (\<lambda>(s,b). (\<iota> s, b)) w)) = length ?gs"
        by (by100 simp)
      fix i assume "i < length (map (\<lambda>(x,b). if b then x else invg x) (map (\<lambda>(s,b). (\<iota> s, b)) w))"
      hence hi: "i < length w" by (by100 simp)
      obtain si bi where hwi: "w ! i = (si, bi)" by (cases "w ! i") (by100 blast)
      show "map (\<lambda>(x,b). if b then x else invg x) (map (\<lambda>(s,b). (\<iota> s, b)) w) ! i = ?gs ! i"
        using hi hwi by (by100 simp)
    qed
    finally show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Step 2: Define coefficient function c.\<close>
  define c :: "'s \<Rightarrow> int" where
    "c s = (let bs = filter (\<lambda>(t,b). t = s) w
             in if bs = [] then 0
                else if snd (hd bs) then int (length bs)
                else - int (length bs))" for s
  \<comment> \<open>Step 3: Support is finite, nonempty, contained in S.\<close>
  have hsupp_sub: "{s \<in> S. c s \<noteq> 0} \<subseteq> fst ` set w"
  proof (rule subsetI)
    fix s assume "s \<in> {s \<in> S. c s \<noteq> 0}"
    hence "c s \<noteq> 0" by (by100 blast)
    hence hne_filter: "filter (\<lambda>(t,b). t = s) w \<noteq> []" unfolding c_def by (by5000 auto)
    then obtain p ps where "filter (\<lambda>(t,b). t = s) w = p # ps" using list.exhaust by (by100 blast)
    hence "p \<in> set (filter (\<lambda>(t,b). t = s) w)" by (by100 simp)
    hence "p \<in> set w \<and> fst p = s" by (by5000 auto)
    thus "s \<in> fst ` set w" by (by100 force)
  qed
  have hfin: "finite {s \<in> S. c s \<noteq> 0}"
  proof -
    have "finite (fst ` set w)" by (by100 simp)
    from finite_subset[OF hsupp_sub this] show ?thesis .
  qed
  have hnonzero: "\<exists>s\<in>S. c s \<noteq> 0"
  proof -
    obtain s0 b0 where hw0: "w ! 0 = (s0, b0)" by (cases "w ! 0") (by100 blast)
    have "0 < length w" using hne by (by100 simp)
    hence hs0_w: "(s0, b0) \<in> set w" using hw0 nth_mem by (by100 force)
    have hs0_S: "s0 \<in> S" using hs0_w hall by (by100 force)
    have hfilter_ne: "filter (\<lambda>(t,b). t = s0) w \<noteq> []"
    proof -
      have "(s0, b0) \<in> set (filter (\<lambda>(t,b). t = s0) w)"
        using hs0_w by (by5000 auto)
      thus ?thesis by (by100 force)
    qed
    have "c s0 \<noteq> 0"
    proof -
      define bs where "bs = filter (\<lambda>(t,b). t = s0) w"
      have "bs \<noteq> []" using hfilter_ne unfolding bs_def .
      hence "length bs > 0" by (by100 simp)
      hence "int (length bs) > 0" by (by100 simp)
      show ?thesis
      proof (cases "snd (hd bs)")
        case True thus ?thesis using \<open>int (length bs) > 0\<close>
          unfolding c_def bs_def[symmetric] using \<open>bs \<noteq> []\<close> by (by5000 auto)
      next
        case False thus ?thesis using \<open>int (length bs) > 0\<close>
          unfolding c_def bs_def[symmetric] using \<open>bs \<noteq> []\<close> by (by5000 auto)
      qed
    qed
    thus ?thesis using hs0_S by (by100 blast)
  qed
  \<comment> \<open>Step 4: Independence: canonical\_product(c) \<noteq> e.\<close>
  let ?term = "\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
                   else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))"
  let ?supp_list = "SOME xs :: 's list. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs"
  have hcanonical_ne: "foldr mul (map ?term ?supp_list) e \<noteq> e"
  proof -
    have hindep: "\<forall>c :: 's \<Rightarrow> int.
        finite {s\<in>S. c s \<noteq> 0} \<longrightarrow> (\<exists>s\<in>S. c s \<noteq> 0) \<longrightarrow>
        foldr mul (map (\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
                            else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s)))
          (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs)) e \<noteq> e"
      using hfree unfolding top1_is_free_abelian_group_full_on_def by (by5000 blast)
    from hindep[rule_format, OF hfin hnonzero] show ?thesis .
  qed
  \<comment> \<open>Step 5: word\_product = canonical\_product. The word product (after foldr conversion)
     decomposes into per-generator powers via abelian\_foldr\_split\_one\_element / remdups\_pow.
     These per-generator powers match the term function applied to the support.
     The ordering is reconciled via abelian\_foldr\_perm\_distinct.\<close>
  \<comment> \<open>Prove the conclusion directly: word\_product \<noteq> e.\<close>
  show ?thesis
  proof -
    \<comment> \<open>Step 5: word\_product = canonical\_product.\<close>
    \<comment> \<open>Step 5a: By abelian\_foldr\_remdups\_pow, collapse repeated elements.\<close>
    have hgs_G: "set ?gs \<subseteq> G"
    proof (rule subsetI)
      fix y assume "y \<in> set ?gs"
      then obtain s b where "(s, b) \<in> set w" and hy: "y = ?gen (s, b)" by (by5000 auto)
      have "s \<in> S" using \<open>(s, b) \<in> set w\<close> hall by (by100 force)
      hence "\<iota> s \<in> G" using h\<iota>_in by (by100 blast)
      hence "invg (\<iota> s) \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      thus "y \<in> G" using hy \<open>\<iota> s \<in> G\<close> \<open>invg (\<iota> s) \<in> G\<close> by (by100 auto)
    qed
    let ?pow_gs = "\<lambda>v. top1_group_pow mul e v (length (filter (\<lambda>x. x = v) ?gs))"
    have hcollapse: "foldr mul ?gs e = foldr mul (map ?pow_gs (remdups ?gs)) e"
      by (rule abelian_foldr_remdups_pow[OF hG_abel hgs_G])
    \<comment> \<open>Step 5b: Show collapsed product = canonical product.
       Both sides enumerate per-generator powers.
       pow\_gs(gen(s, b\_s)) = term(s) for each generator s.
       The ordering differs but abelian group products are order-independent.
       Use abelian\_foldr\_perm\_distinct on the value lists.\<close>
    \<comment> \<open>Show: the set of gen values in ?gs corresponds bijectively to the support.
       Each gen value maps to the same power as the corresponding term.\<close>
    have hsupp_spec: "set ?supp_list = {s \<in> S. c s \<noteq> 0} \<and> distinct ?supp_list"
    proof -
      have "\<exists>xs::'s list. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs"
        using finite_distinct_list[OF hfin] .
      thus ?thesis by (rule someI_ex)
    qed
    \<comment> \<open>For now, the remaining correspondence argument:\<close>
    \<comment> \<open>Step 5c: Use abelian\_foldr\_map\_perm\_distinct to match orderings.\<close>
    \<comment> \<open>Both remdups (map fst w) and ?supp\_list enumerate the support distinctly.\<close>
    have hgens_dist: "distinct (remdups (map fst w))" by (by100 simp)
    have hsupp_dist: "distinct ?supp_list" using hsupp_spec by (by100 blast)
    have hsupp_set: "set ?supp_list = {s \<in> S. c s \<noteq> 0}" using hsupp_spec by (by100 blast)
    \<comment> \<open>The support = fst ` set w \<inter> S = fst ` set w (since hall says all fst in S).\<close>
    have hgens_set: "set (remdups (map fst w)) = fst ` set w" by (by100 simp)
    \<comment> \<open>Show: fst ` set w = {s \<in> S. c s \<noteq> 0}.\<close>
    have hsets_gen_supp: "fst ` set w = {s \<in> S. c s \<noteq> 0}"
    proof
      show "fst ` set w \<subseteq> {s \<in> S. c s \<noteq> 0}"
      proof (rule subsetI)
        fix s assume "s \<in> fst ` set w"
        hence "s \<in> S" using hall by (by100 blast)
        moreover have "c s \<noteq> 0"
        proof -
          from \<open>s \<in> fst ` set w\<close> obtain b where "(s, b) \<in> set w" by (by100 force)
          hence "(s, b) \<in> set (filter (\<lambda>(t,b). t = s) w)" by (by5000 auto)
          hence hne_filter: "filter (\<lambda>(t,b). t = s) w \<noteq> []" by (by100 force)
          define bs where "bs = filter (\<lambda>(t,b). t = s) w"
          have "bs \<noteq> []" using hne_filter unfolding bs_def .
          hence "length bs > 0" by (by100 simp)
          thus ?thesis
          proof (cases "snd (hd bs)")
            case True thus ?thesis using \<open>length bs > 0\<close> \<open>bs \<noteq> []\<close>
              unfolding c_def bs_def[symmetric] by (by5000 auto)
          next
            case False thus ?thesis using \<open>length bs > 0\<close> \<open>bs \<noteq> []\<close>
              unfolding c_def bs_def[symmetric] by (by5000 auto)
          qed
        qed
        ultimately show "s \<in> {s \<in> S. c s \<noteq> 0}" by (by100 blast)
      qed
    next
      show "{s \<in> S. c s \<noteq> 0} \<subseteq> fst ` set w" using hsupp_sub .
    qed
    hence hgens_eq_supp: "set (remdups (map fst w)) = set ?supp_list"
      using hgens_set hsupp_set by (by100 simp)
    \<comment> \<open>Show: ?term maps generators in the support into G.\<close>
    have hterm_G: "\<forall>s \<in> set (remdups (map fst w)). ?term s \<in> G"
    proof (intro ballI)
      fix s assume "s \<in> set (remdups (map fst w))"
      hence "s \<in> fst ` set w" by (by100 simp)
      hence "s \<in> S" using hall by (by100 blast)
      hence "\<iota> s \<in> G" using h\<iota>_in by (by100 blast)
      hence "invg (\<iota> s) \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      show "?term s \<in> G"
        using group_pow_in_group'[OF hG_grp \<open>\<iota> s \<in> G\<close>]
              group_pow_in_group'[OF hG_grp \<open>invg (\<iota> s) \<in> G\<close>]
        by (by100 auto)
    qed
    \<comment> \<open>Apply abelian\_foldr\_map\_perm\_distinct.\<close>
    have "foldr mul (map ?term (remdups (map fst w))) e = foldr mul (map ?term ?supp_list) e"
      by (rule abelian_foldr_map_perm_distinct[OF hG_abel hterm_G hgens_dist hsupp_dist hgens_eq_supp])
    \<comment> \<open>Show: foldr mul (map ?pow\_gs (remdups ?gs)) e = foldr mul (map ?term (remdups (map fst w))) e.
       This requires: pow\_gs(gen(s, b\_s)) = term(s) for each s.\<close>
    \<comment> \<open>Key: map ?pow\_gs (remdups ?gs) = map ?term (remdups (map fst w)) as lists.
       Both enumerate per-generator powers in first-occurrence order.
       Since ?gen is injective on generators (single-polarity), the remdups orderings match.\<close>
    \<comment> \<open>Show the foldr products match. Both compute per-generator powers.
       pow\_gs(gen(s,b)) = pow(gen(s,b), count) = term(s) for each generator s.
       Use abelian\_foldr\_map\_perm\_distinct on gen/term correspondence.\<close>
    have "foldr mul (map ?pow_gs (remdups ?gs)) e
        = foldr mul (map ?term (remdups (map fst w))) e"
    proof -
      \<comment> \<open>Prove the LIST equality: map pow\_gs (remdups gs) = map term (remdups (map fst w)).
         Chain: remdups(map gen w) = map gen (remdups w) [gen injective],
         then map pow\_gs (map gen (remdups w)) = map (term \<circ> fst) (remdups w)
         = map term (remdups (map fst w)) [single polarity: fst of remdups = remdups of fst].\<close>
      \<comment> \<open>(1) gen is injective on set w.\<close>
      have h\<iota>_inj: "inj_on \<iota> S"
        using hfree unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
      have hgen_inj: "inj_on ?gen (set w)"
      proof (rule inj_onI)
        fix p1 p2 assume hp1: "p1 \<in> set w" and hp2: "p2 \<in> set w"
            and heq: "?gen p1 = ?gen p2"
        obtain s1 b1 where h1: "p1 = (s1, b1)" by (cases p1) (by100 blast)
        obtain s2 b2 where h2: "p2 = (s2, b2)" by (cases p2) (by100 blast)
        have hs1: "s1 \<in> S" using hp1 h1 hall by (by100 force)
        have hs2: "s2 \<in> S" using hp2 h2 hall by (by100 force)
        \<comment> \<open>If s1 = s2: by huni, b1 = b2.\<close>
        \<comment> \<open>If s1 \<noteq> s2: gen values differ (by \<iota> injective + invg injective).\<close>
        have "s1 = s2"
        proof (rule ccontr)
          assume hne: "s1 \<noteq> s2"
          have "\<iota> s1 \<noteq> \<iota> s2" using h\<iota>_inj hs1 hs2 hne unfolding inj_on_def by (by100 blast)
          \<comment> \<open>Case analysis on b1, b2.\<close>
          show False
          proof (cases b1)
            case True note hb1 = this
            show ?thesis
            proof (cases b2)
              case True \<comment> \<open>Both True: \<iota> s1 = \<iota> s2, contradicts \<iota> injective.\<close>
              thus ?thesis using heq h1 h2 hb1 \<open>\<iota> s1 \<noteq> \<iota> s2\<close> by (by100 simp)
            next
              case False \<comment> \<open>s1 True, s2 False: \<iota> s1 = invg(\<iota> s2). Then mul(\<iota> s1, \<iota> s2) = e.\<close>
              hence h_eq: "\<iota> s1 = invg (\<iota> s2)" using heq h1 h2 hb1 by (by100 simp)
              \<comment> \<open>mul(\<iota> s1, \<iota> s2) = e. Define c' with c'(s1) = 1, c'(s2) = 1.
                 canonical\_product(c') = mul(\<iota> s1, \<iota> s2) = e, contradicting independence.\<close>
              have "mul (\<iota> s1) (\<iota> s2) = e"
              proof -
                have "mul (invg (\<iota> s2)) (\<iota> s2) = e"
                  using hG_grp h\<iota>_in hs2 unfolding top1_is_group_on_def by (by100 blast)
                thus ?thesis using h_eq by (by100 simp)
              qed
              \<comment> \<open>This contradicts independence with c(s1) = 1, c(s2) = 1.\<close>
              define c' :: "'s \<Rightarrow> int" where "c' = (\<lambda>s. if s = s1 then 1 else if s = s2 then 1 else 0)"
              have "finite {s \<in> S. c' s \<noteq> 0}"
              proof -
                have "{s \<in> S. c' s \<noteq> 0} \<subseteq> {s1, s2}" unfolding c'_def by (by5000 auto)
                thus ?thesis by (rule finite_subset) (by100 simp)
              qed
              moreover have "\<exists>s\<in>S. c' s \<noteq> 0"
                using hs1 unfolding c'_def by (by100 auto)
              \<comment> \<open>Show canonical\_product(c') = mul(\<iota> s1, \<iota> s2) = e.\<close>
              moreover have "foldr mul (map (\<lambda>s. if c' s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c' s))
                  else top1_group_pow mul e (invg (\<iota> s)) (nat (- c' s)))
                  (SOME xs. set xs = {s \<in> S. c' s \<noteq> 0} \<and> distinct xs)) e = e"
              proof -
                let ?t = "\<lambda>s. if c' s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c' s))
                             else top1_group_pow mul e (invg (\<iota> s)) (nat (- c' s))"
                \<comment> \<open>Support = {s1, s2}.\<close>
                have hsupp: "{s \<in> S. c' s \<noteq> 0} = {s1, s2}"
                  using hs1 hs2 hne unfolding c'_def by (by5000 auto)
                \<comment> \<open>SOME xs with set = {s1,s2} and distinct: exists.\<close>
                have "\<exists>xs::'s list. set xs = {s1, s2} \<and> distinct xs"
                proof -
                  have "set [s1, s2] = {s1, s2}" by (by100 simp)
                  moreover have "distinct [s1, s2]" using hne by (by100 simp)
                  ultimately show ?thesis by (by100 blast)
                qed
                hence hspec: "set (SOME xs::'s list. set xs = {s1, s2} \<and> distinct xs) = {s1, s2}
                    \<and> distinct (SOME xs::'s list. set xs = {s1, s2} \<and> distinct xs)"
                  by (rule someI_ex)
                let ?xs = "SOME xs::'s list. set xs = {s1, s2} \<and> distinct xs"
                \<comment> \<open>t(s1) = pow(\<iota> s1, 1) = \<iota> s1, t(s2) = pow(\<iota> s2, 1) = \<iota> s2.\<close>
                have ht1: "?t s1 = \<iota> s1" unfolding c'_def
                  using hG_grp h\<iota>_in hs1 unfolding top1_is_group_on_def by (by5000 auto)
                have ht2: "?t s2 = \<iota> s2" unfolding c'_def
                  using hne hG_grp h\<iota>_in hs2 unfolding top1_is_group_on_def by (by5000 auto)
                \<comment> \<open>The product of [\<iota> s1, \<iota> s2] = mul(\<iota> s1, \<iota> s2) regardless of order (abelian).\<close>
                have ht1_G: "?t s1 \<in> G" using ht1 h\<iota>_in hs1 by (by100 simp)
                have ht2_G: "?t s2 \<in> G" using ht2 h\<iota>_in hs2 by (by100 simp)
                have "foldr mul (map ?t (SOME xs. set xs = {s1, s2} \<and> distinct xs)) e
                    = mul (?t s1) (?t s2)"
                  by (rule canonical_product_two_eq[OF hG_abel ht1_G ht2_G hne])
                hence "foldr mul (map ?t (SOME xs. set xs = {s1, s2} \<and> distinct xs)) e
                    = mul (\<iota> s1) (\<iota> s2)" using ht1 ht2 by (by100 simp)
                hence "foldr mul (map ?t (SOME xs. set xs = {s1, s2} \<and> distinct xs)) e = e"
                  using \<open>mul (\<iota> s1) (\<iota> s2) = e\<close> by (by100 simp)
                \<comment> \<open>Rewrite {s1,s2} to {s \<in> S. c' s \<noteq> 0} using hsupp.\<close>
                thus ?thesis using hsupp by (by5000 simp)
              qed
              ultimately have False
                using hfree unfolding top1_is_free_abelian_group_full_on_def by (by5000 blast)
              thus ?thesis ..
            qed
          next
            case False note hb1 = this
            show ?thesis
            proof (cases b2)
              case True \<comment> \<open>s1 False, s2 True: invg(\<iota> s1) = \<iota> s2.\<close>
              hence h_eq2: "invg (\<iota> s1) = \<iota> s2" using heq h1 h2 hb1 by (by100 simp)
              have "mul (\<iota> s1) (\<iota> s2) = e"
              proof -
                have "mul (\<iota> s1) (invg (\<iota> s1)) = e"
                  using hG_grp h\<iota>_in hs1 unfolding top1_is_group_on_def by (by100 blast)
                thus ?thesis using h_eq2 by (by100 simp)
              qed
              \<comment> \<open>Same independence contradiction as above.\<close>
              define c'' :: "'s \<Rightarrow> int" where "c'' = (\<lambda>s. if s = s1 then 1 else if s = s2 then 1 else 0)"
              have "finite {s \<in> S. c'' s \<noteq> 0}"
              proof -
                have "{s \<in> S. c'' s \<noteq> 0} \<subseteq> {s1, s2}" unfolding c''_def by (by5000 auto)
                thus ?thesis by (rule finite_subset) (by100 simp)
              qed
              moreover have "\<exists>s\<in>S. c'' s \<noteq> 0"
                using hs1 unfolding c''_def by (by100 auto)
              moreover have "foldr mul (map (\<lambda>s. if c'' s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c'' s))
                  else top1_group_pow mul e (invg (\<iota> s)) (nat (- c'' s)))
                  (SOME xs. set xs = {s \<in> S. c'' s \<noteq> 0} \<and> distinct xs)) e = e"
              proof -
                let ?f'' = "\<lambda>s. if c'' s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c'' s))
                               else top1_group_pow mul e (invg (\<iota> s)) (nat (- c'' s))"
                have hsupp'': "{s \<in> S. c'' s \<noteq> 0} = {s1, s2}"
                  using hs1 hs2 hne unfolding c''_def by (by5000 auto)
                have hf1: "?f'' s1 = \<iota> s1"
                  unfolding c''_def using hG_grp h\<iota>_in hs1
                  unfolding top1_is_group_on_def by (by5000 auto)
                have hf2: "?f'' s2 = \<iota> s2"
                  unfolding c''_def using hne hG_grp h\<iota>_in hs2
                  unfolding top1_is_group_on_def by (by5000 auto)
                have hf1_G: "?f'' s1 \<in> G" using hf1 h\<iota>_in hs1 by (by100 simp)
                have hf2_G: "?f'' s2 \<in> G" using hf2 h\<iota>_in hs2 by (by100 simp)
                have "foldr mul (map ?f'' (SOME xs. set xs = {s1, s2} \<and> distinct xs)) e
                    = mul (?f'' s1) (?f'' s2)"
                  by (rule canonical_product_two_eq[OF hG_abel hf1_G hf2_G hne])
                hence "foldr mul (map ?f'' (SOME xs. set xs = {s1, s2} \<and> distinct xs)) e
                    = mul (\<iota> s1) (\<iota> s2)" using hf1 hf2 by (by100 simp)
                thus ?thesis using \<open>mul (\<iota> s1) (\<iota> s2) = e\<close> hsupp'' by (by5000 simp)
              qed
              ultimately have False
                using hfree unfolding top1_is_free_abelian_group_full_on_def by (by5000 blast)
              thus ?thesis ..
            next
              case False \<comment> \<open>Both False: invg(\<iota> s1) = invg(\<iota> s2), so \<iota> s1 = \<iota> s2.\<close>
              hence "invg (\<iota> s1) = invg (\<iota> s2)" using heq h1 h2 hb1 by (by100 simp)
              hence "\<iota> s1 = \<iota> s2"
              proof -
                assume h: "invg (\<iota> s1) = invg (\<iota> s2)"
                have h1: "\<iota> s1 \<in> G" using h\<iota>_in hs1 by (by100 blast)
                have h2: "\<iota> s2 \<in> G" using h\<iota>_in hs2 by (by100 blast)
                \<comment> \<open>mul(invg(\<iota> s1), \<iota> s1) = e, and invg(\<iota> s1) = invg(\<iota> s2),
                   so mul(invg(\<iota> s2), \<iota> s1) = e, hence \<iota> s1 = \<iota> s2 by left cancel.\<close>
                have "mul (invg (\<iota> s2)) (\<iota> s1) = e"
                proof -
                  have "mul (invg (\<iota> s1)) (\<iota> s1) = e"
                    using hG_grp h1 unfolding top1_is_group_on_def by (by100 blast)
                  thus ?thesis using h by (by100 simp)
                qed
                moreover have "mul (invg (\<iota> s2)) (\<iota> s2) = e"
                  using hG_grp h2 unfolding top1_is_group_on_def by (by100 blast)
                ultimately have "mul (invg (\<iota> s2)) (\<iota> s1) = mul (invg (\<iota> s2)) (\<iota> s2)"
                  by (by100 simp)
                \<comment> \<open>Left-cancel invg(\<iota> s2): mul(c, a) = mul(c, b) \<Longrightarrow> a = b.\<close>
                have hinvg2: "invg (\<iota> s2) \<in> G"
                  using hG_grp h2 unfolding top1_is_group_on_def by (by100 blast)
                have "mul e (\<iota> s1) = mul e (\<iota> s2)"
                proof -
                  have hassoc: "\<forall>x\<in>G. \<forall>y\<in>G. \<forall>z\<in>G. mul (mul x y) z = mul x (mul y z)"
                    using hG_grp unfolding top1_is_group_on_def by (by100 blast)
                  have "mul (invg (invg (\<iota> s2))) (mul (invg (\<iota> s2)) (\<iota> s1))
                      = mul (invg (invg (\<iota> s2))) (mul (invg (\<iota> s2)) (\<iota> s2))"
                    using \<open>mul (invg (\<iota> s2)) (\<iota> s1) = mul (invg (\<iota> s2)) (\<iota> s2)\<close> by (by100 simp)
                  moreover have "invg (invg (\<iota> s2)) \<in> G"
                    using hG_grp hinvg2 unfolding top1_is_group_on_def by (by100 blast)
                  \<comment> \<open>mul(e, \<iota> s1) = \<iota> s1 and mul(e, \<iota> s2) = \<iota> s2.\<close>
                  ultimately show ?thesis
                    using hG_grp h1 h2 hinvg2 \<open>invg (invg (\<iota> s2)) \<in> G\<close>
                    unfolding top1_is_group_on_def by (by5000 metis)
                qed
                moreover have "mul e (\<iota> s1) = \<iota> s1"
                  using hG_grp h1 unfolding top1_is_group_on_def by (by100 blast)
                moreover have "mul e (\<iota> s2) = \<iota> s2"
                  using hG_grp h2 unfolding top1_is_group_on_def by (by100 blast)
                ultimately show "\<iota> s1 = \<iota> s2" by (by100 simp)
              qed
              thus ?thesis using \<open>\<iota> s1 \<noteq> \<iota> s2\<close> by (by100 blast)
            qed
          qed
        qed
        hence "b1 = b2"
        proof -
          have "(s1, b1) \<in> set w" using hp1 h1 by (by100 simp)
          have "(s2, b2) \<in> set w" using hp2 h2 by (by100 simp)
          hence "(s1, b2) \<in> set w" using \<open>s1 = s2\<close> by (by100 simp)
          show ?thesis
          proof (rule ccontr)
            assume "b1 \<noteq> b2"
            hence "b2 = (\<not>b1)" by (by100 auto)
            hence "(s1, \<not>b1) \<in> set w" using \<open>(s1, b2) \<in> set w\<close> by (by100 simp)
            thus False using huni \<open>(s1, b1) \<in> set w\<close> by (by100 blast)
          qed
        qed
        show "p1 = p2" using h1 h2 \<open>s1 = s2\<close> \<open>b1 = b2\<close> by (by100 simp)
      qed
      \<comment> \<open>(2) remdups (map gen w) = map gen (remdups w).\<close>
      have hrm: "remdups (map ?gen w) = map ?gen (remdups w)"
        by (rule remdups_map_inj_on[OF hgen_inj])
      \<comment> \<open>(3) pow\_gs(gen(s,b)) = term(s) for (s,b) \<in> set w.\<close>
      have hpt: "\<And>s b. (s,b) \<in> set w \<Longrightarrow> ?pow_gs (?gen (s,b)) = ?term s"
      proof -
        fix s b assume hsb: "(s, b) \<in> set w"
        \<comment> \<open>Step 1: length(filter (= gen(s,b)) (map gen w)) = length(filter (fst = s) w).
           Because gen is injective on set w: gen(t,c) = gen(s,b) iff (t,c) = (s,b) iff t = s.\<close>
        have hcount_eq: "length (filter (\<lambda>x. x = ?gen (s,b)) ?gs) = length (filter (\<lambda>(t,c). t = s) w)"
        proof -
          \<comment> \<open>By filter\_map: filter (= v) (map f xs) = map f (filter ((= v) \<circ> f) xs).\<close>
          have h1: "filter (\<lambda>x. x = ?gen (s,b)) (map ?gen w)
              = map ?gen (filter ((\<lambda>x. x = ?gen (s,b)) \<circ> ?gen) w)"
            by (rule filter_map)
          \<comment> \<open>Show: ((\<lambda>x. x = gen(s,b)) \<circ> gen) p = (fst p = s) for all p \<in> set w.
             Then the filters are equal by filter\_cong.\<close>
          \<comment> \<open>The two filter predicates agree on set w (gen inj + single polarity).
             Hence the filters produce the same result.\<close>
          have h2: "filter ((\<lambda>x. x = ?gen (s,b)) \<circ> ?gen) w = filter (\<lambda>(t,c). t = s) w"
          proof (rule filter_pred_eq)
            fix p assume hp: "p \<in> set w"
            obtain t c where hp': "p = (t, c)" by (cases p) (by100 blast)
            \<comment> \<open>LHS: gen(t,c) = gen(s,b). RHS: t = s.\<close>
            have "(?gen (t,c) = ?gen (s,b)) = (t = s)"
            proof
              assume "?gen (t,c) = ?gen (s,b)"
              hence "(t,c) = (s,b)" using hgen_inj hp hsb hp'
                unfolding inj_on_def by (by100 blast)
              thus "t = s" by (by100 simp)
            next
              assume "t = s"
              have "(s,c) \<in> set w" using hp hp' \<open>t = s\<close> by (by100 simp)
              have "c = b"
              proof (rule ccontr)
                assume "c \<noteq> b" hence "c = (\<not>b)" by (by100 auto)
                hence "(s, \<not>b) \<in> set w" using \<open>(s,c) \<in> set w\<close> by (by100 simp)
                thus False using huni hsb by (by100 blast)
              qed
              thus "?gen (t,c) = ?gen (s,b)" using \<open>t = s\<close> by (by100 simp)
            qed
            \<comment> \<open>Rewrite to match the goal's form with comp and case\_prod.\<close>
            thus "((\<lambda>x. x = ?gen (s,b)) \<circ> ?gen) p = (case p of (t,c) \<Rightarrow> t = s)"
              using hp' by (by100 simp)
          qed
          show ?thesis using h1 h2 by (by100 simp)
        qed
        \<comment> \<open>Step 2: Expand c(s) and show pow\_gs(gen(s,b)) = term(s).\<close>
        define cnt where "cnt = length (filter (\<lambda>(t,c). t = s) w)"
        have hfilter_ne: "filter (\<lambda>(t,c). t = s) w \<noteq> []"
        proof -
          have "(s,b) \<in> set (filter (\<lambda>(t,c). t = s) w)" using hsb by (by5000 auto)
          thus ?thesis by (by100 force)
        qed
        have hcnt_pos: "cnt > 0" using hfilter_ne unfolding cnt_def by (by100 simp)
        have hpol: "snd (hd (filter (\<lambda>(t,cb). t = s) w)) = b"
        proof -
          \<comment> \<open>The first element of filter has fst = s. By single polarity, its snd = b.\<close>
          obtain t' c' rest where hfilt: "filter (\<lambda>(t,c). t = s) w = (t', c') # rest"
            using hfilter_ne by (cases "filter (\<lambda>(t,c). t = s) w") (by100 auto)+
          have "(t', c') \<in> set (filter (\<lambda>(t,c). t = s) w)" using hfilt by (by100 simp)
          hence "(t', c') \<in> set w \<and> t' = s" by (by5000 auto)
          hence "(s, c') \<in> set w" by (by100 simp)
          have "c' = b"
          proof (rule ccontr)
            assume "c' \<noteq> b" hence "c' = (\<not>b)" by (by100 auto)
            hence "(s, \<not>b) \<in> set w" using \<open>(s, c') \<in> set w\<close> by (by100 simp)
            thus False using huni hsb by (by100 blast)
          qed
          thus ?thesis using hfilt by (by100 simp)
        qed
        \<comment> \<open>c(s) = (if b then int cnt else -int cnt).\<close>
        have hc_val: "c s = (if b then int cnt else - int cnt)"
          using hfilter_ne hpol unfolding c_def cnt_def by (by5000 auto)
        \<comment> \<open>pow\_gs(gen(s,b)) = pow(gen(s,b), cnt).\<close>
        have "?pow_gs (?gen (s,b)) = top1_group_pow mul e (?gen (s,b)) cnt"
          using hcount_eq unfolding cnt_def by (by100 simp)
        \<comment> \<open>term(s) = pow(gen(s,b), cnt) by expanding c.\<close>
        also have "\<dots> = ?term s"
        proof (cases b)
          case True
          hence "c s = int cnt" using hc_val by (by100 simp)
          hence hcge: "c s \<ge> 0" using hcnt_pos by (by100 simp)
          have "nat (c s) = cnt" using \<open>c s = int cnt\<close> by (by100 simp)
          \<comment> \<open>gen(s, True) = \<iota> s. pow(\<iota> s, cnt) = term(s) since c(s) \<ge> 0.\<close>
          show ?thesis using True hcge \<open>nat (c s) = cnt\<close> by (by100 simp)
        next
          case False
          hence "c s = - int cnt" using hc_val by (by100 simp)
          hence hclt: "c s < 0" using hcnt_pos by (by100 simp)
          have hclt': "\<not> (c s \<ge> 0)" using hclt by (by100 simp)
          have "nat (- c s) = cnt" using \<open>c s = - int cnt\<close> by (by100 simp)
          \<comment> \<open>gen(s, False) = invg(\<iota> s). pow(invg(\<iota> s), cnt) = term(s) since c(s) < 0.\<close>
          show ?thesis using False hclt' \<open>nat (- c s) = cnt\<close> by (by100 simp)
        qed
        finally show "?pow_gs (?gen (s,b)) = ?term s" .
      qed
      \<comment> \<open>(4) map fst (remdups w) = remdups (map fst w).\<close>
      have hfr: "map fst (remdups w) = remdups (map fst w)"
        by (rule remdups_fst_single_pol[OF huni])
      \<comment> \<open>Chain.\<close>
      have "map ?pow_gs (remdups ?gs) = map ?pow_gs (map ?gen (remdups w))"
        using hrm by (by100 simp)
      also have "\<dots> = map (\<lambda>p. ?pow_gs (?gen p)) (remdups w)" by (by100 simp)
      also have "\<dots> = map ?term (map fst (remdups w))"
      proof (rule nth_equalityI)
        show "length (map (\<lambda>p. ?pow_gs (?gen p)) (remdups w)) = length (map ?term (map fst (remdups w)))"
          by (by100 simp)
        fix i assume hi': "i < length (map (\<lambda>p. ?pow_gs (?gen p)) (remdups w))"
        hence hi: "i < length (remdups w)" by (by100 simp)
        obtain s b where hx: "remdups w ! i = (s, b)" by (cases "remdups w ! i") (by100 blast)
        have hsb_w: "(s, b) \<in> set w"
        proof -
          have "remdups w ! i \<in> set (remdups w)" using hi nth_mem by (by100 blast)
          thus ?thesis using hx by (by100 simp)
        qed
        have "map (\<lambda>p. ?pow_gs (?gen p)) (remdups w) ! i = ?pow_gs (?gen (remdups w ! i))"
          using hi by (by100 simp)
        also have "\<dots> = ?pow_gs (?gen (s, b))" using hx by (by100 simp)
        also have "\<dots> = ?term s" using hpt[OF hsb_w] .
        also have "\<dots> = map ?term (map fst (remdups w)) ! i"
          using hi hx by (by100 simp)
        finally show "map (\<lambda>p. ?pow_gs (?gen p)) (remdups w) ! i = map ?term (map fst (remdups w)) ! i" .
      qed
      also have "\<dots> = map ?term (remdups (map fst w))" using hfr by (by100 simp)
      finally have "map ?pow_gs (remdups ?gs) = map ?term (remdups (map fst w))" .
      thus ?thesis by (by100 simp)
    qed
    hence "foldr mul (map ?pow_gs (remdups ?gs)) e = foldr mul (map ?term ?supp_list) e"
      using \<open>foldr mul (map ?term (remdups (map fst w))) e = foldr mul (map ?term ?supp_list) e\<close>
      by (by100 simp)
    hence "foldr mul ?gs e = foldr mul (map ?term ?supp_list) e" using hcollapse by (by100 simp)
    \<comment> \<open>Step 6: Combine with heval\_foldr and hcanonical\_ne.\<close>
    hence "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) w) = foldr mul (map ?term ?supp_list) e"
      using heval_foldr by (by100 simp)
    hence "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) w) = foldr mul (map ?term ?supp_list) e"
      using heval_foldr by (by100 simp)
    thus ?thesis using hcanonical_ne by (by100 simp)
  qed
qed

text \<open>Free abelian word kernel: if a word evaluates to e in a free abelian group,
  then it evaluates to eH in any abelian group H.
  This delegates to free\_abelian\_word\_kernel\_v2 which is placed after word\_product infrastructure.\<close>
lemma free_abelian_word_kernel:
  fixes w :: "('s \<times> bool) list"
  assumes hfree: "top1_is_free_abelian_group_full_on G mul e invg \<iota> S"
      and hH: "top1_is_abelian_group_on H mulH eH invgH"
      and hphi: "\<forall>s\<in>S. \<phi> s \<in> H"
      and hws: "\<forall>s \<in> fst ` set w. s \<in> S"
      and heval: "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) w) = e"
  shows "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) w) = eH"
proof -
  have hG_grp: "top1_is_group_on G mul e invg"
    using hfree unfolding top1_is_free_abelian_group_full_on_def
      top1_is_abelian_group_on_def by (by100 blast)
  have hG_abel: "top1_is_abelian_group_on G mul e invg"
    using hfree unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  have hH_grp: "top1_is_group_on H mulH eH invgH"
    using hH unfolding top1_is_abelian_group_on_def by (by100 blast)
  have h\<iota>_in: "\<forall>s\<in>S. \<iota> s \<in> G"
    using hfree unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  \<comment> \<open>By strong induction on length w.
     If w = [], trivial.
     If w nonempty, look at w!0 = (s0, b0). Either (s0, \<not>b0) appears in tl w or not.
     If yes: move it adjacent to w!0 (abelian), cancel the pair, apply IH (shorter word).
     If no: net coeff of s0 \<noteq> 0, contradicting independence + eval = e.\<close>
  show ?thesis using hws heval
  proof (induction "length w" arbitrary: w rule: less_induct)
    case (less w)
    show ?case
    proof (cases "w = []")
      case True thus ?thesis by (by100 simp)
    next
      case False
      obtain s0 b0 where hfirst: "w ! 0 = (s0, b0)" by (cases "w ! 0") (by100 blast)
      have hw_ne: "w \<noteq> []" using False by (by100 simp)
      have h0_len: "0 < length w" using hw_ne by (by100 simp)
      have hs0_S: "s0 \<in> S"
        using h0_len hfirst less(2) nth_mem by (by100 fastforce)
      show ?thesis
      proof (cases "\<exists>j. j < length w \<and> j > 0 \<and> w ! j = (s0, \<not>b0)")
        case True
        then obtain j where hj: "j < length w" and hj0: "j > 0"
            and hwj: "w ! j = (s0, \<not>b0)" by (by100 blast)
        \<comment> \<open>Cancel pair at positions 0 and j.\<close>
        let ?w' = "tl (take j w) @ drop (Suc j) w"
        \<comment> \<open>Cancel pair at positions 0 and j. Using foldr approach:
           word\_product\_as\_foldr + abelian\_foldr\_mul\_extract to extract positions 0 and j,
           then inverse cancellation. Same result in G (eval=e) and H (eval\_H=eH).\<close>
        have heval_G': "top1_group_word_product mul e invg
            (map (\<lambda>(s,b). (\<iota> s, b)) ?w') = e"
        proof -
          have hG_abel: "top1_is_abelian_group_on G mul e invg"
            using hfree unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
          let ?mw = "map (\<lambda>(s,b). (\<iota> s, b)) w"
          have h\<iota>_in: "\<forall>s\<in>S. \<iota> s \<in> G"
            using hfree unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
          have hmw_G: "\<forall>i<length ?mw. fst (?mw ! i) \<in> G"
          proof (intro allI impI)
            fix i assume "i < length ?mw"
            hence hi: "i < length w" by (by100 simp)
            obtain si bi where "w ! i = (si, bi)" by (cases "w ! i") (by100 blast)
            have "si \<in> fst ` set w" using hi \<open>w ! i = (si, bi)\<close> nth_mem by (by100 force)
            hence "si \<in> S" using less(2) by (by100 blast)
            thus "fst (?mw ! i) \<in> G" using h\<iota>_in hi \<open>w ! i = (si, bi)\<close> by (by100 simp)
          qed
          have hmw_0: "?mw ! 0 = (\<iota> s0, b0)" using hfirst h0_len by (by100 simp)
          have hmw_j: "?mw ! j = (\<iota> s0, \<not>b0)" using hwj hj by (by100 simp)
          have "top1_group_word_product mul e invg ?mw
              = top1_group_word_product mul e invg (tl (take j ?mw) @ drop (Suc j) ?mw)"
            apply (rule word_product_cancel_matching_pair[where s="\<iota> s0" and b=b0])
            apply (rule hG_abel)
            apply (rule hmw_G)
            apply (rule hmw_0)
            apply (rule hj0)
            apply (simp only: length_map, rule hj)
            apply (rule hmw_j)
            done
          have "tl (take j ?mw) @ drop (Suc j) ?mw
              = map (\<lambda>(s,b). (\<iota> s, b)) (take (j-1) (tl w) @ drop j (tl w))"
            by (rule tl_take_drop_map_pair[OF hj0])
          moreover have "take (j-1) (tl w) @ drop j (tl w) = tl (take j w) @ drop (Suc j) w"
            using tl_take_drop_eq[OF hj0, symmetric] .
          ultimately have "tl (take j ?mw) @ drop (Suc j) ?mw = map (\<lambda>(s,b). (\<iota> s, b)) ?w'"
            by (by100 simp)
          hence "top1_group_word_product mul e invg ?mw
              = top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ?w')"
            using \<open>top1_group_word_product mul e invg ?mw = top1_group_word_product mul e invg (tl (take j ?mw) @ drop (Suc j) ?mw)\<close>
            by (by100 simp)
          thus ?thesis using less(3) by (by100 simp)
        qed
        have hlen': "length ?w' < length w" using hj by (by100 fastforce)
        have hset_sub: "set ?w' \<subseteq> set w"
        proof (rule subsetI)
          fix x assume "x \<in> set ?w'"
          have "set ?w' \<subseteq> set (tl (take j w)) \<union> set (drop (j + 1) w)" by (by100 auto)
          moreover have "set (tl (take j w)) \<subseteq> set (take j w)"
            by (cases "take j w") (by100 auto)+
          moreover have "set (take j w) \<subseteq> set w" by (rule set_take_subset)
          moreover have "set (drop (j + 1) w) \<subseteq> set w" by (rule set_drop_subset)
          ultimately show "x \<in> set w" using \<open>x \<in> set ?w'\<close> by (by100 blast)
        qed
        have hws': "\<forall>s \<in> fst ` set ?w'. s \<in> S"
          using less(2) hset_sub by (by100 blast)
        have hIH: "top1_group_word_product mulH eH invgH
            (map (\<lambda>(s,b). (\<phi> s, b)) ?w') = eH"
          by (rule less(1)[OF hlen' hws' heval_G'])
        have "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) w)
            = top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ?w')"
        proof -
          let ?mw = "map (\<lambda>(s,b). (\<phi> s, b)) w"
          have hmw_H: "\<forall>i<length ?mw. fst (?mw ! i) \<in> H"
          proof (intro allI impI)
            fix i assume "i < length ?mw"
            hence hi: "i < length w" by (by100 simp)
            obtain si bi where "w ! i = (si, bi)" by (cases "w ! i") (by100 blast)
            have "si \<in> fst ` set w" using hi \<open>w ! i = (si, bi)\<close> nth_mem by (by100 force)
            hence "si \<in> S" using less(2) by (by100 blast)
            thus "fst (?mw ! i) \<in> H" using hphi hi \<open>w ! i = (si, bi)\<close> by (by100 simp)
          qed
          have "top1_group_word_product mulH eH invgH ?mw
              = top1_group_word_product mulH eH invgH (tl (take j ?mw) @ drop (Suc j) ?mw)"
            apply (rule word_product_cancel_matching_pair[where s="\<phi> s0" and b=b0])
            apply (rule hH)
            apply (rule hmw_H)
            using hfirst h0_len apply (by100 simp)
            apply (rule hj0)
            apply (simp only: length_map, rule hj)
            using hwj hj apply (by100 simp)
            done
          have htld: "tl (take j ?mw) @ drop (Suc j) ?mw = map (\<lambda>(s,b). (\<phi> s, b)) ?w'"
          proof -
            have "tl (take j ?mw) @ drop (Suc j) ?mw
                = map (\<lambda>(s,b). (\<phi> s, b)) (take (j-1) (tl w) @ drop j (tl w))"
              by (rule tl_take_drop_map_pair[OF hj0])
            moreover have "take (j-1) (tl w) @ drop j (tl w) = tl (take j w) @ drop (Suc j) w"
              using tl_take_drop_eq[OF hj0, symmetric] .
            ultimately show ?thesis by (by100 simp)
          qed
          show ?thesis
            using \<open>top1_group_word_product mulH eH invgH ?mw = top1_group_word_product mulH eH invgH (tl (take j ?mw) @ drop (Suc j) ?mw)\<close>
                  htld by (by100 simp)
        qed
        thus ?thesis using hIH by (by100 simp)
      next
        case no_pair: False
        \<comment> \<open>s0 has no matching pair. Split: either some OTHER generator has a matching
           pair (cancel it via IH), or no generator has any matching pair (independence).\<close>
        show ?thesis
        proof (cases "\<exists>s1 b1. (s1, b1) \<in> set w \<and> (s1, \<not>b1) \<in> set w")
          case True
          \<comment> \<open>Some generator has a matching pair. Cancel it and use IH directly.\<close>
          \<comment> \<open>Move one element of the pair to position 0, cancel, apply IH.\<close>
          \<comment> \<open>This case gives eval\_H = eH directly via cancel in G and H + IH.\<close>
          then obtain s1 b1 where hpair1: "(s1, b1) \<in> set w" "(s1, \<not>b1) \<in> set w"
            by (by100 blast)
          \<comment> \<open>Move (s1, b1) to position 0, then cancel against (s1, \<not>b1).\<close>
          from hpair1(1) obtain i1 where hi1: "i1 < length w" and hwi1: "w ! i1 = (s1, b1)"
            using in_set_conv_nth by (by100 metis)
          \<comment> \<open>Form w1 = w!i1 # take i1 w @ drop (Suc i1) w (move position i1 to front).\<close>
          let ?w1 = "w ! i1 # take i1 w @ drop (Suc i1) w"
          have hw1_0: "?w1 ! 0 = (s1, b1)" using hwi1 by (by100 simp)
          have hw1_len: "length ?w1 = length w" using hi1 by (by100 simp)
          \<comment> \<open>eval\_G(?w1) = eval\_G(w) via abelian\_word\_product\_move\_front.\<close>
          \<comment> \<open>Membership lemma for mapped word.\<close>
          have hmw_G: "\<forall>k<length (map (\<lambda>(s,b). (\<iota> s, b)) w). fst ((map (\<lambda>(s,b). (\<iota> s, b)) w) ! k) \<in> G"
          proof (intro allI impI)
            fix k assume "k < length (map (\<lambda>(s,b). (\<iota> s, b)) w)"
            hence hk: "k < length w" by (by100 simp)
            obtain sk bk where "w ! k = (sk, bk)" by (cases "w ! k") (by100 blast)
            have "sk \<in> fst ` set w" using hk \<open>w ! k = (sk, bk)\<close> nth_mem by (by100 force)
            hence "sk \<in> S" using less(2) by (by100 blast)
            thus "fst ((map (\<lambda>(s,b). (\<iota> s, b)) w) ! k) \<in> G"
              using h\<iota>_in hk \<open>w ! k = (sk, bk)\<close> by (by100 simp)
          qed
          have heval_w1_G: "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ?w1)
              = top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) w)"
          proof -
            have "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) w)
                = top1_group_word_product mul e invg
                    ((map (\<lambda>(s,b). (\<iota> s, b)) w) ! i1 # take i1 (map (\<lambda>(s,b). (\<iota> s, b)) w) @ drop (Suc i1) (map (\<lambda>(s,b). (\<iota> s, b)) w))"
              by (rule abelian_word_product_move_front[OF hG_abel hmw_G])
                 (simp add: hi1)
            moreover have "(map (\<lambda>(s,b). (\<iota> s, b)) w) ! i1 # take i1 (map (\<lambda>(s,b). (\<iota> s, b)) w) @ drop (Suc i1) (map (\<lambda>(s,b). (\<iota> s, b)) w)
                = map (\<lambda>(s,b). (\<iota> s, b)) ?w1"
            proof -
              have "(map (\<lambda>(s,b). (\<iota> s, b)) w) ! i1 = (\<iota> s1, b1)"
                using hi1 hwi1 by (by100 simp)
              moreover have "take i1 (map (\<lambda>(s,b). (\<iota> s, b)) w) = map (\<lambda>(s,b). (\<iota> s, b)) (take i1 w)"
                by (rule take_map)
              moreover have "drop (Suc i1) (map (\<lambda>(s,b). (\<iota> s, b)) w) = map (\<lambda>(s,b). (\<iota> s, b)) (drop (Suc i1) w)"
                by (rule drop_map)
              ultimately show ?thesis using hwi1 by (by100 simp)
            qed
            ultimately show ?thesis by (by100 simp)
          qed
          \<comment> \<open>eval\_H(?w1) = eval\_H(w) similarly.\<close>
          have hmw_H: "\<forall>k<length (map (\<lambda>(s,b). (\<phi> s, b)) w). fst ((map (\<lambda>(s,b). (\<phi> s, b)) w) ! k) \<in> H"
          proof (intro allI impI)
            fix k assume "k < length (map (\<lambda>(s,b). (\<phi> s, b)) w)"
            hence hk: "k < length w" by (by100 simp)
            obtain sk bk where "w ! k = (sk, bk)" by (cases "w ! k") (by100 blast)
            have "sk \<in> fst ` set w" using hk \<open>w ! k = (sk, bk)\<close> nth_mem by (by100 force)
            hence "sk \<in> S" using less(2) by (by100 blast)
            thus "fst ((map (\<lambda>(s,b). (\<phi> s, b)) w) ! k) \<in> H"
              using hphi hk \<open>w ! k = (sk, bk)\<close> by (by100 simp)
          qed
          have heval_w1_H: "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ?w1)
              = top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) w)"
          proof -
            have "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) w)
                = top1_group_word_product mulH eH invgH
                    ((map (\<lambda>(s,b). (\<phi> s, b)) w) ! i1 # take i1 (map (\<lambda>(s,b). (\<phi> s, b)) w) @ drop (Suc i1) (map (\<lambda>(s,b). (\<phi> s, b)) w))"
              by (rule abelian_word_product_move_front[OF hH hmw_H])
                 (simp add: hi1)
            moreover have "(map (\<lambda>(s,b). (\<phi> s, b)) w) ! i1 # take i1 (map (\<lambda>(s,b). (\<phi> s, b)) w) @ drop (Suc i1) (map (\<lambda>(s,b). (\<phi> s, b)) w)
                = map (\<lambda>(s,b). (\<phi> s, b)) ?w1"
            proof -
              have "(map (\<lambda>(s,b). (\<phi> s, b)) w) ! i1 = (\<phi> s1, b1)"
                using hi1 hwi1 by (by100 simp)
              moreover have "take i1 (map (\<lambda>(s,b). (\<phi> s, b)) w) = map (\<lambda>(s,b). (\<phi> s, b)) (take i1 w)"
                by (rule take_map)
              moreover have "drop (Suc i1) (map (\<lambda>(s,b). (\<phi> s, b)) w) = map (\<lambda>(s,b). (\<phi> s, b)) (drop (Suc i1) w)"
                by (rule drop_map)
              ultimately show ?thesis using hwi1 by (by100 simp)
            qed
            ultimately show ?thesis by (by100 simp)
          qed
          \<comment> \<open>Find (s1, \<not>b1) at position j1 > 0 in ?w1.\<close>
          have hset_w1: "set ?w1 = set w"
          proof
            show "set ?w1 \<subseteq> set w"
            proof (rule subsetI)
              fix x assume "x \<in> set ?w1"
              hence "x = w ! i1 \<or> x \<in> set (take i1 w) \<or> x \<in> set (drop (Suc i1) w)"
                by (by5000 auto)
              moreover have "w ! i1 \<in> set w" using hi1 nth_mem by (by100 blast)
              moreover have "set (take i1 w) \<subseteq> set w" by (rule set_take_subset)
              moreover have "set (drop (Suc i1) w) \<subseteq> set w" by (rule set_drop_subset)
              ultimately show "x \<in> set w" by (by100 blast)
            qed
          next
            show "set w \<subseteq> set ?w1"
            proof (rule subsetI)
              fix x assume "x \<in> set w"
              have "w = take i1 w @ [w ! i1] @ drop (Suc i1) w"
                using id_take_nth_drop[OF hi1] by (by100 simp)
              hence "x \<in> set (take i1 w @ [w ! i1] @ drop (Suc i1) w)" using \<open>x \<in> set w\<close>
                by (by100 simp)
              thus "x \<in> set ?w1" by (by5000 auto)
            qed
          qed
          have "(s1, \<not>b1) \<in> set ?w1" using hpair1(2) hset_w1 by (by100 blast)
          then obtain j1 where hj1: "j1 < length ?w1" and hj1_0: "j1 > 0"
              and hw1j1: "?w1 ! j1 = (s1, \<not>b1)"
          proof -
            from \<open>(s1, \<not>b1) \<in> set ?w1\<close> obtain j1 where hj1: "j1 < length ?w1"
                and hw1j1: "?w1 ! j1 = (s1, \<not>b1)" using in_set_conv_nth by (by100 metis)
            have "j1 > 0"
            proof (rule ccontr)
              assume "\<not> j1 > 0" hence "j1 = 0" by (by100 simp)
              hence "(s1, b1) = (s1, \<not>b1)" using hw1_0 hw1j1 by (by100 simp)
              thus False by (by100 simp)
            qed
            thus ?thesis using that hj1 hw1j1 by (by100 blast)
          qed
          \<comment> \<open>Cancel pair in ?w1 at positions 0 and j1. Same pattern as existing True case.\<close>
          let ?w' = "tl (take j1 ?w1) @ drop (Suc j1) ?w1"
          have heval_G': "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ?w') = e"
          proof -
            let ?mw1 = "map (\<lambda>(s,b). (\<iota> s, b)) ?w1"
            have hmw1_G: "\<forall>k<length ?mw1. fst (?mw1 ! k) \<in> G"
            proof (intro allI impI)
              fix k assume "k < length ?mw1"
              hence hk: "k < length ?w1" by (by100 simp)
              obtain sk bk where "?w1 ! k = (sk, bk)" by (cases "?w1 ! k") (by100 blast)
              have "?w1 ! k \<in> set ?w1" using hk nth_mem by (by100 blast)
              hence "(sk, bk) \<in> set ?w1" using \<open>?w1 ! k = (sk, bk)\<close> by (by100 simp)
              hence "(sk, bk) \<in> set w" using hset_w1 by (by100 blast)
              hence "sk \<in> fst ` set w" by (by100 force)
              hence "sk \<in> S" using less(2) by (by100 blast)
              have "\<iota> sk \<in> G" using h\<iota>_in \<open>sk \<in> S\<close> by (by100 blast)
              have "?mw1 ! k = (\<lambda>(s,b). (\<iota> s, b)) (?w1 ! k)"
                using nth_map[OF hk] by (by100 simp)
              hence "?mw1 ! k = (\<iota> sk, bk)" using \<open>?w1 ! k = (sk, bk)\<close> by (by100 simp)
              thus "fst (?mw1 ! k) \<in> G" using \<open>\<iota> sk \<in> G\<close> by (by100 simp)
            qed
            have hmw1_0: "?mw1 ! 0 = (\<iota> s1, b1)"
            proof -
              have "0 < length ?w1" using hw1_len hw_ne by (by100 simp)
              hence "?mw1 ! 0 = (\<lambda>(s,b). (\<iota> s, b)) (?w1 ! 0)"
                using nth_map[of 0 ?w1] by (by100 simp)
              thus ?thesis using hw1_0 by (by100 simp)
            qed
            have hmw1_j: "?mw1 ! j1 = (\<iota> s1, \<not>b1)"
            proof -
              have "j1 < length ?w1" using hj1 .
              hence "?mw1 ! j1 = (\<lambda>(s,b). (\<iota> s, b)) (?w1 ! j1)"
                using nth_map[of j1 ?w1] by (by100 simp)
              thus ?thesis using hw1j1 by (by100 simp)
            qed
            have "top1_group_word_product mul e invg ?mw1
                = top1_group_word_product mul e invg (tl (take j1 ?mw1) @ drop (Suc j1) ?mw1)"
              apply (rule word_product_cancel_matching_pair[where s="\<iota> s1" and b=b1])
              apply (rule hG_abel)
              apply (rule hmw1_G)
              apply (rule hmw1_0)
              apply (rule hj1_0)
              apply (simp only: length_map, rule hj1)
              apply (rule hmw1_j)
              done
            have "tl (take j1 ?mw1) @ drop (Suc j1) ?mw1 = map (\<lambda>(s,b). (\<iota> s, b)) ?w'"
            proof -
              have "tl (take j1 (map (\<lambda>(s,b). (\<iota> s, b)) ?w1)) @ drop (Suc j1) (map (\<lambda>(s,b). (\<iota> s, b)) ?w1)
                  = map (\<lambda>(s,b). (\<iota> s, b)) (take (j1 - 1) (tl ?w1) @ drop j1 (tl ?w1))"
                by (rule tl_take_drop_map_pair[OF hj1_0])
              moreover have "take (j1 - 1) (tl ?w1) @ drop j1 (tl ?w1) = ?w'"
                using tl_take_drop_eq[OF hj1_0, symmetric] .
              ultimately show ?thesis by (by5000 simp)
            qed
            hence "top1_group_word_product mul e invg ?mw1
                = top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ?w')"
              using \<open>top1_group_word_product mul e invg ?mw1 = top1_group_word_product mul e invg (tl (take j1 ?mw1) @ drop (Suc j1) ?mw1)\<close>
              by (by5000 simp)
            thus ?thesis using heval_w1_G less(3) by (by100 simp)
          qed
          have hlen': "length ?w' < length w"
            using hj1 hw1_len by (by5000 fastforce)
          have hset_w'_sub: "set ?w' \<subseteq> set ?w1"
          proof (rule subsetI)
            fix x assume "x \<in> set ?w'"
            have "set ?w' \<subseteq> set (tl (take j1 ?w1)) \<union> set (drop (j1 + 1) ?w1)" by (by100 auto)
            moreover have "set (tl (take j1 ?w1)) \<subseteq> set (take j1 ?w1)"
              by (cases "take j1 ?w1") (by100 auto)+
            moreover have "set (take j1 ?w1) \<subseteq> set ?w1" by (rule set_take_subset)
            moreover have "set (drop (j1 + 1) ?w1) \<subseteq> set ?w1" by (rule set_drop_subset)
            ultimately show "x \<in> set ?w1" using \<open>x \<in> set ?w'\<close> by (by100 blast)
          qed
          have hws': "\<forall>s \<in> fst ` set ?w'. s \<in> S"
            using less(2) hset_w'_sub hset_w1 by (by5000 force)
          \<comment> \<open>IH on ?w'.\<close>
          have hIH: "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ?w') = eH"
            by (rule less(1)[OF hlen' hws' heval_G'])
          \<comment> \<open>Cancel in H: eval\_H(?w1) = eval\_H(?w') = eH.\<close>
          have "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ?w1)
              = top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ?w')"
          proof -
            let ?mw1H = "map (\<lambda>(s,b). (\<phi> s, b)) ?w1"
            have hmw1_H: "\<forall>k<length ?mw1H. fst (?mw1H ! k) \<in> H"
            proof (intro allI impI)
              fix k assume "k < length ?mw1H"
              hence hk: "k < length ?w1" by (by100 simp)
              obtain sk bk where "?w1 ! k = (sk, bk)" by (cases "?w1 ! k") (by100 blast)
              have "?w1 ! k \<in> set ?w1" using hk nth_mem by (by100 blast)
              hence "(sk, bk) \<in> set ?w1" using \<open>?w1 ! k = (sk, bk)\<close> by (by100 simp)
              hence "(sk, bk) \<in> set w" using hset_w1 by (by100 blast)
              hence "sk \<in> fst ` set w" by (by100 force)
              hence "sk \<in> S" using less(2) by (by100 blast)
              have "\<phi> sk \<in> H" using hphi \<open>sk \<in> S\<close> by (by100 blast)
              have "?mw1H ! k = (\<lambda>(s,b). (\<phi> s, b)) (?w1 ! k)"
                using nth_map[OF hk] by (by100 simp)
              hence "?mw1H ! k = (\<phi> sk, bk)" using \<open>?w1 ! k = (sk, bk)\<close> by (by100 simp)
              thus "fst (?mw1H ! k) \<in> H" using \<open>\<phi> sk \<in> H\<close> by (by100 simp)
            qed
            have hmw1H_0: "?mw1H ! 0 = (\<phi> s1, b1)"
            proof -
              have "0 < length ?w1" using hw1_len hw_ne by (by100 simp)
              hence "?mw1H ! 0 = (\<lambda>(s,b). (\<phi> s, b)) (?w1 ! 0)"
                using nth_map[of 0 ?w1] by (by100 simp)
              thus ?thesis using hw1_0 by (by100 simp)
            qed
            have hmw1H_j: "?mw1H ! j1 = (\<phi> s1, \<not>b1)"
            proof -
              have "j1 < length ?w1" using hj1 .
              hence "?mw1H ! j1 = (\<lambda>(s,b). (\<phi> s, b)) (?w1 ! j1)"
                using nth_map[of j1 ?w1] by (by100 simp)
              thus ?thesis using hw1j1 by (by100 simp)
            qed
            have "top1_group_word_product mulH eH invgH ?mw1H
                = top1_group_word_product mulH eH invgH (tl (take j1 ?mw1H) @ drop (Suc j1) ?mw1H)"
              apply (rule word_product_cancel_matching_pair[where s="\<phi> s1" and b=b1])
              apply (rule hH)
              apply (rule hmw1_H)
              apply (rule hmw1H_0)
              apply (rule hj1_0)
              apply (simp only: length_map, rule hj1)
              apply (rule hmw1H_j)
              done
            have "tl (take j1 ?mw1H) @ drop (Suc j1) ?mw1H = map (\<lambda>(s,b). (\<phi> s, b)) ?w'"
            proof -
              have "tl (take j1 (map (\<lambda>(s,b). (\<phi> s, b)) ?w1)) @ drop (Suc j1) (map (\<lambda>(s,b). (\<phi> s, b)) ?w1)
                  = map (\<lambda>(s,b). (\<phi> s, b)) (take (j1 - 1) (tl ?w1) @ drop j1 (tl ?w1))"
                by (rule tl_take_drop_map_pair[OF hj1_0])
              moreover have "take (j1 - 1) (tl ?w1) @ drop j1 (tl ?w1) = ?w'"
                using tl_take_drop_eq[OF hj1_0, symmetric] .
              ultimately show ?thesis by (by5000 simp)
            qed
            thus ?thesis
              using \<open>top1_group_word_product mulH eH invgH ?mw1H = top1_group_word_product mulH eH invgH (tl (take j1 ?mw1H) @ drop (Suc j1) ?mw1H)\<close>
              by (by5000 simp)
          qed
          hence "top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ?w1) = eH"
            using hIH by (by100 simp)
          thus ?thesis using heval_w1_H by (by100 simp)
        next
          case all_single: False
          \<comment> \<open>No generator has any matching pair. All single polarity.
             By no\_matching\_pair\_word\_ne\_e, eval\_G(w) \<noteq> e.\<close>
          have huni: "\<forall>s b. (s, b) \<in> set w \<longrightarrow> (s, \<not>b) \<notin> set w"
            using all_single by (by100 blast)
          have "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) w) \<noteq> e"
            by (rule no_matching_pair_word_ne_e[OF hfree less(2) hw_ne huni])
          thus ?thesis using less(3) by (by100 blast)
        qed
      qed
    qed
  qed
qed

text \<open>Helper: in a free abelian group, if the word product equals e, then the
  net coefficient for every generator is zero.
  Proof: apply free\_abelian\_word\_kernel with H = \<int> and indicator map \<phi>(s') = if s'=s then 1 else 0.
  The word product in \<int> equals count\_True(s) - count\_False(s) = 0, so counts are equal.\<close>
lemma free_abelian_eval_e_zero_net_coeff:
  fixes w :: "('s \<times> bool) list"
  assumes hfree: "top1_is_free_abelian_group_full_on G mul e invg \<iota> S"
      and hall: "\<forall>s \<in> fst ` set w. s \<in> S"
      and heval: "top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) w) = e"
  shows "\<forall>s. length (filter (\<lambda>(t,b). t = s \<and> b) w)
           = length (filter (\<lambda>(t,b). t = s \<and> \<not>b) w)"
proof -
  \<comment> \<open>\<int> with (+, 0, uminus) is an abelian group.\<close>
  have hZ: "top1_is_abelian_group_on (UNIV::int set) (+) (0::int) uminus"
    unfolding top1_is_abelian_group_on_def top1_is_group_on_def
    by (by5000 auto)
  show ?thesis
  proof (intro allI)
    fix s :: 's
    \<comment> \<open>Indicator map: \<phi>(s') = 1 if s'=s, else 0.\<close>
    define \<phi> :: "'s \<Rightarrow> int" where "\<phi> = (\<lambda>s'. if s' = s then 1 else 0)"
    have hphi: "\<forall>t\<in>S. \<phi> t \<in> (UNIV::int set)" unfolding \<phi>_def by (by100 simp)
    \<comment> \<open>By free\_abelian\_word\_kernel, the word evaluates to 0 in \<int>.\<close>
    have hkernel: "top1_group_word_product (+) (0::int) uminus
        (map (\<lambda>(s',b). (\<phi> s', b)) w) = 0"
      using free_abelian_word_kernel[OF hfree hZ hphi hall heval] by (by100 simp)
    \<comment> \<open>Word product in \<int> = count\_True(s) - count\_False(s), by induction on w.\<close>
    have hrelate: "top1_group_word_product (+) (0::int) uminus
        (map (\<lambda>(s',b). (\<phi> s', b)) w)
      = int (length (filter (\<lambda>(t,c). t = s \<and> c) w))
        - int (length (filter (\<lambda>(t,c). t = s \<and> \<not>c) w))"
    proof (induction w)
      case Nil show ?case by (by100 simp)
    next
      case (Cons a rest)
      obtain s' b' where ha: "a = (s', b')" by (cases a) (by100 blast)
      show ?case
      proof (cases b')
        case True show ?thesis using Cons ha True unfolding \<phi>_def
          by (cases "s' = s") (by5000 simp)+
      next
        case False show ?thesis using Cons ha False unfolding \<phi>_def
          by (cases "s' = s") (by5000 simp)+
      qed
    qed
    \<comment> \<open>Combine: 0 = count\_True - count\_False implies count\_True = count\_False.\<close>
    show "length (filter (\<lambda>(t,b). t = s \<and> b) w) = length (filter (\<lambda>(t,b). t = s \<and> \<not>b) w)"
      using hkernel hrelate by (by100 linarith)
  qed
qed

text \<open>Lemma 67.7 (extension property): free abelian group G with basis S has the universal
  property: for any abelian group H and map \<phi>: S \<rightarrow> H, there exists a unique homomorphism
  \<psi>: G \<rightarrow> H with \<psi> \<circ> \<iota> = \<phi> on S.\<close>
lemma Lemma_67_7_free_abelian_extension:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and \<iota> :: "'s \<Rightarrow> 'g" and S :: "'s set"
    and H :: "'h set" and mulH :: "'h \<Rightarrow> 'h \<Rightarrow> 'h"
    and eH :: 'h and invgH :: "'h \<Rightarrow> 'h"
    and \<phi> :: "'s \<Rightarrow> 'h"
  assumes hfree: "top1_is_free_abelian_group_full_on G mul e invg \<iota> S"
      and hH: "top1_is_abelian_group_on H mulH eH invgH"
      and hphi: "\<forall>s\<in>S. \<phi> s \<in> H"
  shows "\<exists>\<psi>. top1_group_hom_on G mul H mulH \<psi>
    \<and> (\<forall>s\<in>S. \<psi> (\<iota> s) = \<phi> s)"
proof -
  have hG_grp: "top1_is_group_on G mul e invg"
    using hfree unfolding top1_is_free_abelian_group_full_on_def
      top1_is_abelian_group_on_def by (by100 blast)
  have hG_abel: "top1_is_abelian_group_on G mul e invg"
    using hfree unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  have h\<iota>_in: "\<forall>s\<in>S. \<iota> s \<in> G"
    using hfree unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  have hG_gen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
    using hfree unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  have hH_grp: "top1_is_group_on H mulH eH invgH"
    using hH unfolding top1_is_abelian_group_on_def by (by100 blast)
  \<comment> \<open>For each g \<in> G, pick a word over S and evaluate in H.
     Well-definedness: if w1 and w2 both represent g, then w1 @ flip\_rev(w2)
     evaluates to e in G. By free\_abelian\_word\_kernel, it evaluates to eH in H.
     So eval\_H(w1) = eval\_H(w2).\<close>
  \<comment> \<open>Step 1: word representations exist (using subgroup\_generated\_word\_rep).\<close>
  \<comment> \<open>Step 2: define \<psi> via SOME word.\<close>
  let ?eval_G = "\<lambda>ws. top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
  let ?eval_H = "\<lambda>ws. top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ws)"
  let ?good = "\<lambda>ws g. (\<forall>i<length ws. fst (ws ! i) \<in> S) \<and> ?eval_G ws = g"
  \<comment> \<open>Every g \<in> G has a good word.\<close>
  have hword_exists: "\<forall>g\<in>G. \<exists>ws. ?good ws g"
  proof
    fix g assume "g \<in> G"
    hence "g \<in> top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
      using hG_gen by (by100 simp)
    have h\<iota>S_sub: "\<iota> ` S \<subseteq> G" using h\<iota>_in by (by100 blast)
    obtain ws where hws: "\<forall>i<length ws. fst (ws ! i) \<in> \<iota> ` S"
        and hg: "g = top1_group_word_product mul e invg ws"
      using subgroup_generated_word_rep[OF hG_grp h\<iota>S_sub \<open>g \<in> top1_subgroup_generated_on G mul e invg (\<iota> ` S)\<close>]
      by (by100 blast)
    \<comment> \<open>Convert from words over \<iota>(S) to words over S using inv\_into.\<close>
    let ?ws' = "map (\<lambda>(x,b). (inv_into S \<iota> x, b)) ws"
    have hws'_S: "\<forall>i<length ?ws'. fst (?ws' ! i) \<in> S"
    proof (intro allI impI)
      fix i assume hi: "i < length ?ws'"
      hence hi': "i < length ws" by (by100 simp)
      obtain xi bi where hwi: "ws ! i = (xi, bi)" by (cases "ws ! i") (by100 blast)
      have hxi_img: "xi \<in> \<iota> ` S" using hws hi' hwi by (by100 force)
      hence "inv_into S \<iota> xi \<in> S" by (rule inv_into_into)
      moreover have "?ws' ! i = (inv_into S \<iota> xi, bi)" using hi' hwi by (by100 simp)
      ultimately show "fst (?ws' ! i) \<in> S" by (by100 simp)
    qed
    have hmap_back: "map (\<lambda>(s,b). (\<iota> s, b)) ?ws' = ws"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>(s,b). (\<iota> s, b)) ?ws') = length ws" by (by100 fastforce)
    next
      fix i assume "i < length (map (\<lambda>(s,b). (\<iota> s, b)) ?ws')"
      hence hi: "i < length ws" by (by100 auto)
      obtain xi bi where hwi: "ws ! i = (xi, bi)" by (cases "ws ! i") (by100 fastforce)
      have hxi_img: "xi \<in> \<iota> ` S" using hws hi hwi by (by100 force)
      have "map (\<lambda>(s,b). (\<iota> s, b)) ?ws' ! i = (\<iota> (inv_into S \<iota> xi), bi)"
        using hi hwi by (by100 simp)
      also have "\<iota> (inv_into S \<iota> xi) = xi"
        by (rule f_inv_into_f[OF hxi_img])
      finally show "map (\<lambda>(s,b). (\<iota> s, b)) ?ws' ! i = ws ! i" using hwi by (by100 simp)
    qed
    have hws'_eval: "?eval_G ?ws' = g" using hmap_back hg by (by100 simp)
    have "?good ?ws' g" using hws'_S hws'_eval by (by100 blast)
    thus "\<exists>ws. ?good ws g" by (by100 blast)
  qed
  \<comment> \<open>Well-definedness: if ?good ws1 g and ?good ws2 g, then ?eval\_H ws1 = ?eval\_H ws2.\<close>
  have hwell_def: "\<forall>g\<in>G. \<forall>ws1 ws2. ?good ws1 g \<longrightarrow> ?good ws2 g \<longrightarrow> ?eval_H ws1 = ?eval_H ws2"
  proof (intro ballI allI impI)
    fix g ws1 ws2
    assume hg: "g \<in> G" and hgood1: "?good ws1 g" and hgood2: "?good ws2 g"
    have hS1: "\<forall>i<length ws1. fst (ws1 ! i) \<in> S" using hgood1 by (by100 blast)
    have hS2: "\<forall>i<length ws2. fst (ws2 ! i) \<in> S" using hgood2 by (by100 blast)
    have heval1: "?eval_G ws1 = g" using hgood1 by (by100 blast)
    have heval2: "?eval_G ws2 = g" using hgood2 by (by100 blast)
    \<comment> \<open>ws1 @ rev\_flip(ws2) evaluates to e in G.\<close>
    let ?ws2_inv = "map (\<lambda>(s,b). (s, \<not>b)) (rev ws2)"
    \<comment> \<open>Mapped words for G.\<close>
    let ?mws1 = "map (\<lambda>(s,b). (\<iota> s, b)) ws1"
    let ?mws2 = "map (\<lambda>(s,b). (\<iota> s, b)) ws2"
    let ?mws2_inv = "map (\<lambda>(s,b). (\<iota> s, b)) ?ws2_inv"
    have hmws1_G: "\<forall>i<length ?mws1. fst (?mws1 ! i) \<in> G"
    proof (intro allI impI)
      fix i assume "i < length ?mws1"
      hence hi: "i < length ws1" by (by100 simp)
      obtain si bi where "ws1 ! i = (si, bi)" by (cases "ws1 ! i") (by100 blast)
      hence "si \<in> S" using hS1 hi by (by100 force)
      thus "fst (?mws1 ! i) \<in> G" using h\<iota>_in hi \<open>ws1 ! i = (si, bi)\<close> by (by100 simp)
    qed
    have hmws2_G: "\<forall>i<length ?mws2. fst (?mws2 ! i) \<in> G"
    proof (intro allI impI)
      fix i assume "i < length ?mws2"
      hence hi: "i < length ws2" by (by100 simp)
      obtain si bi where "ws2 ! i = (si, bi)" by (cases "ws2 ! i") (by100 blast)
      hence "si \<in> S" using hS2 hi by (by100 force)
      thus "fst (?mws2 ! i) \<in> G" using h\<iota>_in hi \<open>ws2 ! i = (si, bi)\<close> by (by100 simp)
    qed
    \<comment> \<open>map (\<lambda>(s,b). (\<iota> s, b)) (map (\<lambda>(s,b). (s,\<not>b)) (rev ws2))
       = map (\<lambda>(x,b). (x, \<not>b)) (rev ?mws2)\<close>
    have hflip_comm: "?mws2_inv = map (\<lambda>(x,b). (x, \<not>b)) (rev ?mws2)"
      by (rule map_pair_fst_flip_rev)
    have hmws2_inv_G: "\<forall>i<length ?mws2_inv. fst (?mws2_inv ! i) \<in> G"
      by (rule mapped_word_fst_flip_rev[OF hmws2_G])
    have heval_concat: "?eval_G (ws1 @ ?ws2_inv) = e"
    proof -
      have "map (\<lambda>(s,b). (\<iota> s, b)) (ws1 @ ?ws2_inv) = ?mws1 @ ?mws2_inv"
        by (by100 simp)
      hence "?eval_G (ws1 @ ?ws2_inv)
          = top1_group_word_product mul e invg (?mws1 @ ?mws2_inv)"
        by (by100 simp)
      also have "\<dots> = mul (top1_group_word_product mul e invg ?mws1)
                          (top1_group_word_product mul e invg ?mws2_inv)"
        by (rule word_product_append[OF hG_grp hmws1_G hmws2_inv_G])
      also have "top1_group_word_product mul e invg ?mws2_inv
          = invg (top1_group_word_product mul e invg ?mws2)"
        using hflip_comm word_product_rev_inv[OF hG_grp hmws2_G] by (by100 simp)
      also have "mul (top1_group_word_product mul e invg ?mws1)
                     (invg (top1_group_word_product mul e invg ?mws2))
                 = mul g (invg g)"
        using heval1 heval2 by (by100 simp)
      also have "\<dots> = e"
      proof -
        have "g \<in> G" using hg by (by100 blast)
        thus ?thesis using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      qed
      finally show ?thesis .
    qed
    have hS_concat: "\<forall>s \<in> fst ` set (ws1 @ ?ws2_inv). s \<in> S"
    proof (intro ballI)
      fix s assume "s \<in> fst ` set (ws1 @ ?ws2_inv)"
      hence "s \<in> fst ` set ws1 \<or> s \<in> fst ` set ?ws2_inv" by (by100 auto)
      thus "s \<in> S"
      proof
        assume "s \<in> fst ` set ws1"
        then obtain p where "p \<in> set ws1" and "fst p = s" by (by100 blast)
        then obtain i where "i < length ws1" and "ws1 ! i = p"
          using in_set_conv_nth by (by100 metis)
        hence "fst (ws1 ! i) = s" using \<open>fst p = s\<close> by (by100 simp)
        thus ?thesis using hS1 \<open>i < length ws1\<close> by (by100 blast)
      next
        assume "s \<in> fst ` set ?ws2_inv"
        then obtain p where "p \<in> set ?ws2_inv" and "fst p = s" by (by100 blast)
        then obtain q where "q \<in> set ws2" and "fst q = s"
        proof -
          from \<open>p \<in> set ?ws2_inv\<close> obtain x b where "p = (x, \<not>b)" and "(x, b) \<in> set ws2"
            by (by100 auto)
          hence "fst (x, b) = s" using \<open>fst p = s\<close> by (by100 simp)
          thus ?thesis using that \<open>(x, b) \<in> set ws2\<close> by (by100 blast)
        qed
        then obtain i where "i < length ws2" and "ws2 ! i = q"
          using in_set_conv_nth by (by100 metis)
        hence "fst (ws2 ! i) = s" using \<open>fst q = s\<close> by (by100 simp)
        thus ?thesis using hS2 \<open>i < length ws2\<close> by (by100 blast)
      qed
    qed
    have hevalH_eH: "?eval_H (ws1 @ ?ws2_inv) = eH"
      by (rule free_abelian_word_kernel[OF hfree hH hphi hS_concat heval_concat])
    \<comment> \<open>Decompose hevalH\_eH: eval\_H(ws1 @ rev\_flip ws2) = mulH(eval\_H ws1, invgH(eval\_H ws2)) = eH.
       Then eval\_H ws1 = eval\_H ws2 by group cancellation.\<close>
    \<comment> \<open>Decompose eval\_H(ws1 @ flip\_rev ws2) into mulH(eval\_H ws1, invgH(eval\_H ws2)).\<close>
    have hmH1: "\<forall>i<length (map (\<lambda>(s,b). (\<phi> s, b)) ws1). fst (map (\<lambda>(s,b). (\<phi> s, b)) ws1 ! i) \<in> H"
    proof (intro allI impI)
      fix i assume "i < length (map (\<lambda>(s,b). (\<phi> s, b)) ws1)"
      hence hi: "i < length ws1" by (by100 simp)
      obtain si bi where "ws1 ! i = (si, bi)" by (cases "ws1 ! i") (by100 blast)
      have "si \<in> S" using hS1 hi \<open>ws1 ! i = (si, bi)\<close> by (by100 force)
      thus "fst (map (\<lambda>(s,b). (\<phi> s, b)) ws1 ! i) \<in> H" using hphi hi \<open>ws1 ! i = (si, bi)\<close> by (by100 simp)
    qed
    have hmH2: "\<forall>i<length (map (\<lambda>(s,b). (\<phi> s, b)) ws2). fst (map (\<lambda>(s,b). (\<phi> s, b)) ws2 ! i) \<in> H"
    proof (intro allI impI)
      fix i assume "i < length (map (\<lambda>(s,b). (\<phi> s, b)) ws2)"
      hence hi: "i < length ws2" by (by100 simp)
      obtain si bi where "ws2 ! i = (si, bi)" by (cases "ws2 ! i") (by100 blast)
      have "si \<in> S" using hS2 hi \<open>ws2 ! i = (si, bi)\<close> by (by100 force)
      thus "fst (map (\<lambda>(s,b). (\<phi> s, b)) ws2 ! i) \<in> H" using hphi hi \<open>ws2 ! i = (si, bi)\<close> by (by100 simp)
    qed
    \<comment> \<open>eval\_H(ws1 @ flip\_rev ws2) = mulH(eval\_H ws1, eval\_H(flip\_rev ws2)).\<close>
    have hflip_H: "map (\<lambda>(s,b). (\<phi> s, b)) ?ws2_inv = map (\<lambda>(x,b). (x, \<not>b)) (rev (map (\<lambda>(s,b). (\<phi> s, b)) ws2))"
      by (rule map_pair_fst_flip_rev)
    have hmH2_inv: "\<forall>i<length (map (\<lambda>(s,b). (\<phi> s, b)) ?ws2_inv). fst (map (\<lambda>(s,b). (\<phi> s, b)) ?ws2_inv ! i) \<in> H"
      by (rule mapped_word_fst_flip_rev[OF hmH2])
    have hconcat_H: "?eval_H (ws1 @ ?ws2_inv) = mulH (?eval_H ws1) (?eval_H ?ws2_inv)"
      using word_product_append[OF hH_grp hmH1 hmH2_inv] map_pair_fst_append by (by100 simp)
    have hrev_H: "?eval_H ?ws2_inv = invgH (?eval_H ws2)"
      using hflip_H word_product_rev_inv[OF hH_grp hmH2] by (by100 simp)
    have ha_H: "?eval_H ws1 \<in> H" using word_product_in_group[OF hH_grp hmH1] by (by100 blast)
    have hb_H: "?eval_H ws2 \<in> H" using word_product_in_group[OF hH_grp hmH2] by (by100 blast)
    \<comment> \<open>mulH(eval\_H ws1, invgH(eval\_H ws2)) = eH, so eval\_H ws1 = eval\_H ws2.\<close>
    have "mulH (?eval_H ws1) (invgH (?eval_H ws2)) = eH"
      using hevalH_eH hconcat_H hrev_H by (by100 simp)
    hence "?eval_H ws1 = ?eval_H ws2"
    proof -
      assume hmul_eH: "mulH (?eval_H ws1) (invgH (?eval_H ws2)) = eH"
      have hinvb: "invgH (?eval_H ws2) \<in> H"
        using hH_grp hb_H unfolding top1_is_group_on_def by (by100 blast)
      have hid_r: "\<forall>x\<in>H. mulH x eH = x"
        using hH_grp unfolding top1_is_group_on_def by (by100 blast)
      have hid_l: "\<forall>x\<in>H. mulH eH x = x"
        using hH_grp unfolding top1_is_group_on_def by (by100 blast)
      have hinv_l: "mulH (invgH (?eval_H ws2)) (?eval_H ws2) = eH"
        using hH_grp hb_H unfolding top1_is_group_on_def by (by100 blast)
      have "mulH (?eval_H ws1) eH = ?eval_H ws1"
        using hid_r ha_H by (by100 blast)
      hence "?eval_H ws1 = mulH (?eval_H ws1) (mulH (invgH (?eval_H ws2)) (?eval_H ws2))"
        using hinv_l by (by100 simp)
      also have "\<dots> = mulH (mulH (?eval_H ws1) (invgH (?eval_H ws2))) (?eval_H ws2)"
        using group_assoc[OF hH_grp ha_H hinvb hb_H] by (by100 simp)
      also have "\<dots> = mulH eH (?eval_H ws2)" using hmul_eH by (by100 simp)
      also have "\<dots> = ?eval_H ws2" using hid_l hb_H by (by100 blast)
      finally show ?thesis .
    qed
    thus "?eval_H ws1 = ?eval_H ws2" .
  qed
  \<comment> \<open>Define \<psi>.\<close>
  define \<psi> where "\<psi> g = ?eval_H (SOME ws. ?good ws g)" for g
  \<comment> \<open>Key: \<psi>(g) equals ?eval\_H ws for ANY good ws for g (by well-definedness).\<close>
  have h\<psi>_val: "\<And>g ws. g \<in> G \<Longrightarrow> ?good ws g \<Longrightarrow> \<psi> g = ?eval_H ws"
  proof -
    fix g ws assume hg: "g \<in> G" and hgood: "?good ws g"
    have "\<exists>ws. ?good ws g" using hword_exists hg by (by100 blast)
    hence hsome: "?good (SOME ws. ?good ws g) g"
      by (rule someI_ex)
    show "\<psi> g = ?eval_H ws" unfolding \<psi>_def
      using hwell_def[rule_format, OF hg] hsome hgood by (by100 blast)
  qed
  \<comment> \<open>\<psi> is a homomorphism.\<close>
  have h\<psi>_hom: "top1_group_hom_on G mul H mulH \<psi>"
  proof -
    have h\<psi>_in: "\<And>g. g \<in> G \<Longrightarrow> \<psi> g \<in> H"
    proof -
      fix g assume hg: "g \<in> G"
      obtain ws where hgood: "?good ws g" using hword_exists hg by (by100 blast)
      have "\<psi> g = ?eval_H ws" by (rule h\<psi>_val[OF hg hgood])
      also have "\<dots> \<in> H"
      proof -
        have hmw_H: "\<forall>i<length (map (\<lambda>(s,b). (\<phi> s, b)) ws). fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! i) \<in> H"
        proof (intro allI impI)
          fix i assume "i < length (map (\<lambda>(s,b). (\<phi> s, b)) ws)"
          hence hi: "i < length ws" by (by100 simp)
          obtain si bi where "ws ! i = (si, bi)" by (cases "ws ! i") (by100 blast)
          have "si \<in> S" using hgood hi \<open>ws ! i = (si, bi)\<close> by (by100 force)
          thus "fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! i) \<in> H"
            using hphi hi \<open>ws ! i = (si, bi)\<close> by (by100 simp)
        qed
        show ?thesis using word_product_in_group[OF hH_grp hmw_H] by (by100 blast)
      qed
      finally show "\<psi> g \<in> H" .
    qed
    show ?thesis unfolding top1_group_hom_on_def
    proof (intro conjI ballI)
      fix g show "g \<in> G \<Longrightarrow> \<psi> g \<in> H" by (rule h\<psi>_in)
    next
      fix g1 g2 assume hg1: "g1 \<in> G" and hg2: "g2 \<in> G"
      obtain ws1 where hw1: "?good ws1 g1" using hword_exists hg1 by (by100 blast)
      obtain ws2 where hw2: "?good ws2 g2" using hword_exists hg2 by (by100 blast)
      have hg1g2: "mul g1 g2 \<in> G" using hG_grp hg1 hg2 unfolding top1_is_group_on_def by (by100 blast)
      \<comment> \<open>ws1 @ ws2 is good for mul g1 g2.\<close>
      have hS1': "\<forall>i<length ws1. fst (ws1 ! i) \<in> S" using hw1 by (by100 blast)
      have hS2': "\<forall>i<length ws2. fst (ws2 ! i) \<in> S" using hw2 by (by100 blast)
      have heval1': "?eval_G ws1 = g1" using hw1 by (by100 blast)
      have heval2': "?eval_G ws2 = g2" using hw2 by (by100 blast)
      have hmws1_G: "\<forall>i<length (map (\<lambda>(s,b). (\<iota> s, b)) ws1). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws1 ! i) \<in> G"
      proof (intro allI impI)
        fix i assume "i < length (map (\<lambda>(s,b). (\<iota> s, b)) ws1)"
        hence hi: "i < length ws1" by (by100 simp)
        obtain si bi where hwi: "ws1 ! i = (si, bi)" by (cases "ws1 ! i") (by100 blast)
        have "si \<in> S" using hS1' hi hwi by (by100 force)
        have "map (\<lambda>(s,b). (\<iota> s, b)) ws1 ! i = (\<iota> si, bi)" using hi hwi by (by100 simp)
        thus "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws1 ! i) \<in> G"
          using h\<iota>_in \<open>si \<in> S\<close> by (by100 simp)
      qed
      have hmws2_G: "\<forall>i<length (map (\<lambda>(s,b). (\<iota> s, b)) ws2). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws2 ! i) \<in> G"
      proof (intro allI impI)
        fix i assume "i < length (map (\<lambda>(s,b). (\<iota> s, b)) ws2)"
        hence hi: "i < length ws2" by (by100 simp)
        obtain si bi where hwi: "ws2 ! i = (si, bi)" by (cases "ws2 ! i") (by100 blast)
        have "si \<in> S" using hS2' hi hwi by (by100 force)
        have "map (\<lambda>(s,b). (\<iota> s, b)) ws2 ! i = (\<iota> si, bi)" using hi hwi by (by100 simp)
        thus "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws2 ! i) \<in> G"
          using h\<iota>_in \<open>si \<in> S\<close> by (by100 simp)
      qed
      have hgood12: "?good (ws1 @ ws2) (mul g1 g2)"
      proof (intro conjI)
        show "\<forall>i<length (ws1 @ ws2). fst ((ws1 @ ws2) ! i) \<in> S"
          using hS1' hS2' nth_append
          apply (simp only: nth_append if_True if_False)
          apply (by100 simp)
          done
        show "?eval_G (ws1 @ ws2) = mul g1 g2"
          using heval1' heval2' word_product_append[OF hG_grp hmws1_G hmws2_G]
          by (by100 simp)
      qed
      have "\<psi> (mul g1 g2) = ?eval_H (ws1 @ ws2)"
        by (rule h\<psi>_val[OF hg1g2 hgood12])
      also have "\<dots> = mulH (?eval_H ws1) (?eval_H ws2)"
      proof -
        have hmH1: "\<forall>i<length (map (\<lambda>(s,b). (\<phi> s, b)) ws1). fst (map (\<lambda>(s,b). (\<phi> s, b)) ws1 ! i) \<in> H"
        proof (intro allI impI)
          fix i assume "i < length (map (\<lambda>(s,b). (\<phi> s, b)) ws1)"
          hence hi: "i < length ws1" by (by100 simp)
          obtain si bi where "ws1 ! i = (si, bi)" by (cases "ws1 ! i") (by100 blast)
          have "si \<in> S" using hS1' hi \<open>ws1 ! i = (si, bi)\<close> by (by100 force)
          thus "fst (map (\<lambda>(s,b). (\<phi> s, b)) ws1 ! i) \<in> H"
            using hphi hi \<open>ws1 ! i = (si, bi)\<close> by (by100 simp)
        qed
        have hmH2: "\<forall>i<length (map (\<lambda>(s,b). (\<phi> s, b)) ws2). fst (map (\<lambda>(s,b). (\<phi> s, b)) ws2 ! i) \<in> H"
        proof (intro allI impI)
          fix i assume "i < length (map (\<lambda>(s,b). (\<phi> s, b)) ws2)"
          hence hi: "i < length ws2" by (by100 simp)
          obtain si bi where "ws2 ! i = (si, bi)" by (cases "ws2 ! i") (by100 blast)
          have "si \<in> S" using hS2' hi \<open>ws2 ! i = (si, bi)\<close> by (by100 force)
          thus "fst (map (\<lambda>(s,b). (\<phi> s, b)) ws2 ! i) \<in> H"
            using hphi hi \<open>ws2 ! i = (si, bi)\<close> by (by100 simp)
        qed
        have "map (\<lambda>(s,b). (\<phi> s, b)) (ws1 @ ws2) = map (\<lambda>(s,b). (\<phi> s, b)) ws1 @ map (\<lambda>(s,b). (\<phi> s, b)) ws2"
          by (by100 simp)
        thus ?thesis
          using word_product_append[OF hH_grp hmH1 hmH2] by (by100 simp)
      qed
      also have "?eval_H ws1 = \<psi> g1" by (rule h\<psi>_val[OF hg1 hw1, symmetric])
      also have "?eval_H ws2 = \<psi> g2" by (rule h\<psi>_val[OF hg2 hw2, symmetric])
      finally show "\<psi> (mul g1 g2) = mulH (\<psi> g1) (\<psi> g2)" .
    qed
  qed
  \<comment> \<open>\<psi> extends \<phi>.\<close>
  have h\<psi>_ext: "\<forall>s\<in>S. \<psi> (\<iota> s) = \<phi> s"
  proof (intro ballI)
    fix s assume hs: "s \<in> S"
    have h\<iota>s_G: "\<iota> s \<in> G" using h\<iota>_in hs by (by100 blast)
    have hgood_s: "?good [(s, True)] (\<iota> s)"
    proof (intro conjI)
      show "\<forall>i<length [(s, True)]. fst ([(s, True)] ! i) \<in> S" using hs by (by100 auto)
      show "?eval_G [(s, True)] = \<iota> s"
        using hG_grp h\<iota>s_G unfolding top1_is_group_on_def by (by100 simp)
    qed
    have "\<psi> (\<iota> s) = ?eval_H [(s, True)]"
      by (rule h\<psi>_val[OF h\<iota>s_G hgood_s])
    also have "?eval_H [(s, True)] = \<phi> s"
      using hH_grp hphi hs unfolding top1_is_group_on_def by (by100 simp)
    finally show "\<psi> (\<iota> s) = \<phi> s" .
  qed
  show ?thesis using h\<psi>_hom h\<psi>_ext by (by100 blast)
qed

text \<open>Corollary: coordinate projections exist for free abelian groups.
  For each s0 \<in> S, there is a homomorphism \<epsilon>: G \<rightarrow> Z with \<epsilon>(\<iota>(s0)) = 1
  and \<epsilon>(\<iota>(s)) = 0 for s \<noteq> s0.\<close>
lemma free_abelian_coordinate_projection:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and \<iota> :: "'s \<Rightarrow> 'g" and S :: "'s set" and s0 :: 's
  assumes "top1_is_free_abelian_group_full_on G mul e invg \<iota> S"
      and "s0 \<in> S"
  shows "\<exists>\<epsilon>. top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>
    \<and> \<epsilon> (\<iota> s0) = 1
    \<and> (\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<epsilon> (\<iota> s) = 0)"
proof -
  have hZ: "top1_is_abelian_group_on (UNIV::int set) (+) (0::int) uminus"
    unfolding top1_is_abelian_group_on_def top1_is_group_on_def by (by100 auto)
  let ?\<phi> = "\<lambda>s. if s = s0 then (1::int) else 0"
  have hphi: "\<forall>s\<in>S. ?\<phi> s \<in> (UNIV::int set)" by (by100 blast)
  from Lemma_67_7_free_abelian_extension[OF assms(1) hZ hphi]
  obtain \<psi> where hpsi: "top1_group_hom_on G mul (UNIV::int set) (+) \<psi>"
    and hpsi_val: "\<forall>s\<in>S. \<psi> (\<iota> s) = ?\<phi> s"
    by (by100 blast)
  have "\<psi> (\<iota> s0) = 1" using hpsi_val assms(2) by (by100 simp)
  moreover have "\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<psi> (\<iota> s) = 0" using hpsi_val by (by100 auto)
  ultimately show ?thesis using hpsi by (by100 blast)
qed

text \<open>A group homomorphism distributes over foldr products.\<close>
lemma hom_foldr_mul_early:
  assumes hG: "top1_is_group_on G mul e invg"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hhom: "top1_group_hom_on G mul H mulH f"
      and hxs: "\<forall>i<length xs. xs!i \<in> G"
  shows "f (foldr mul xs e) = foldr mulH (map f xs) eH"
  using hxs
proof (induction xs)
  case Nil show ?case using hom_preserves_id[OF hG hH hhom] by (by100 simp)
next
  case (Cons a xs')
  have ha: "a \<in> G" using Cons.prems by (by100 force)
  have hxs': "\<forall>i<length xs'. xs'!i \<in> G" using Cons.prems by (by100 force)
  have hprod: "foldr mul xs' e \<in> G"
    by (rule foldr_mul_closed[OF hG hxs'])
  have "f (foldr mul (a # xs') e) = f (mul a (foldr mul xs' e))" by (by100 simp)
  also have "\<dots> = mulH (f a) (f (foldr mul xs' e))"
    using hhom ha hprod unfolding top1_group_hom_on_def by (by100 blast)
  also have "\<dots> = mulH (f a) (foldr mulH (map f xs') eH)"
    using Cons.IH[OF hxs'] by (by100 simp)
  finally show ?case by (by100 simp)
qed

lemma hom_group_pow_early:
  assumes hG: "top1_is_group_on G mul e invg"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hhom: "top1_group_hom_on G mul H mulH f"
      and hx: "x \<in> G"
  shows "f (top1_group_pow mul e x n) = top1_group_pow mulH eH (f x) n"
proof (induction n)
  case 0
  have "f (top1_group_pow mul e x 0) = f e" by (by100 simp)
  also have "\<dots> = eH" by (rule hom_preserves_id[OF hG hH hhom])
  finally show ?case by (by100 simp)
next
  case (Suc n)
  have hpow_G: "top1_group_pow mul e x n \<in> G" by (rule group_pow_in_group'[OF hG hx])
  have "f (top1_group_pow mul e x (Suc n)) = f (mul x (top1_group_pow mul e x n))"
    by (by100 simp)
  also have "\<dots> = mulH (f x) (f (top1_group_pow mul e x n))"
    using hhom hx hpow_G unfolding top1_group_hom_on_def by (by100 blast)
  also have "\<dots> = mulH (f x) (top1_group_pow mulH eH (f x) n)"
    using Suc.IH by (by100 simp)
  finally show ?case by (by100 simp)
qed

text \<open>The kernel of a coordinate projection of a free abelian group is free abelian
  on the complementary generators.\<close>
lemma free_abelian_kernel_coordinate:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and iota :: "'s \<Rightarrow> 'g" and S :: "'s set" and s0 :: 's
  assumes hfree: "top1_is_free_abelian_group_full_on G mul e invg iota S"
      and hs0: "s0 \<in> S"
      and heps: "top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>"
      and heps_s0: "\<epsilon> (iota s0) = 1"
      and heps_other: "\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<epsilon> (iota s) = 0"
  shows "top1_is_free_abelian_group_full_on
    {g \<in> G. \<epsilon> g = 0} mul e invg iota (S - {s0})"
proof -
  let ?K = "{g \<in> G. \<epsilon> g = 0}"
  let ?S' = "S - {s0}"
  have hG_grp: "top1_is_group_on G mul e invg"
    using hfree unfolding top1_is_free_abelian_group_full_on_def
      top1_is_abelian_group_on_def by (by100 blast)
  have hG_abel: "top1_is_abelian_group_on G mul e invg"
    using hfree unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  have hZ: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
    unfolding top1_is_group_on_def by (by100 auto)
  \<comment> \<open>Condition 1: K is an abelian group (kernel of hom from abelian group).\<close>
  have hK_abel: "top1_is_abelian_group_on ?K mul e invg"
  proof -
    have he_K: "e \<in> ?K"
    proof -
      have "e \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      have "\<epsilon> e = 0" using hom_preserves_id[OF hG_grp hZ heps] by (by100 simp)
      thus ?thesis using \<open>e \<in> G\<close> by (by100 simp)
    qed
    have hmul_K: "\<forall>x\<in>?K. \<forall>y\<in>?K. mul x y \<in> ?K"
    proof (intro ballI)
      fix x y assume "x \<in> ?K" "y \<in> ?K"
      hence hx: "x \<in> G" "\<epsilon> x = 0" and hy: "y \<in> G" "\<epsilon> y = 0" by (by100 auto)+
      have "mul x y \<in> G" using hG_grp hx(1) hy(1) unfolding top1_is_group_on_def by (by100 blast)
      have "\<epsilon> (mul x y) = \<epsilon> x + \<epsilon> y" using heps hx(1) hy(1)
        unfolding top1_group_hom_on_def by (by100 simp)
      hence "\<epsilon> (mul x y) = 0" using hx(2) hy(2) by (by100 simp)
      thus "mul x y \<in> ?K" using \<open>mul x y \<in> G\<close> by (by100 simp)
    qed
    have hinv_K: "\<forall>x\<in>?K. invg x \<in> ?K"
    proof (intro ballI)
      fix x assume "x \<in> ?K"
      hence hx: "x \<in> G" "\<epsilon> x = 0" by (by100 auto)+
      have "invg x \<in> G" using hG_grp hx(1) unfolding top1_is_group_on_def by (by100 blast)
      have "\<epsilon> (invg x) = - \<epsilon> x"
        using hom_preserves_inv[OF hG_grp hZ heps hx(1)] by (by100 simp)
      hence "\<epsilon> (invg x) = 0" using hx(2) by (by100 simp)
      thus "invg x \<in> ?K" using \<open>invg x \<in> G\<close> by (by100 simp)
    qed
    have hK_sub: "?K \<subseteq> G" by (by100 blast)
    \<comment> \<open>K is a subgroup of an abelian group, hence abelian.\<close>
    show ?thesis unfolding top1_is_abelian_group_on_def top1_is_group_on_def
      using he_K hmul_K hinv_K hK_sub hG_abel
      unfolding top1_is_abelian_group_on_def top1_is_group_on_def by (by5000 blast)
  qed
  \<comment> \<open>Condition 2: \<iota>(s) \<in> K for s \<in> S'.\<close>
  have hiota_K: "\<forall>s\<in>?S'. iota s \<in> ?K"
  proof (intro ballI)
    fix s assume "s \<in> ?S'"
    hence "s \<in> S" "s \<noteq> s0" by (by100 auto)+
    have "iota s \<in> G" using hfree \<open>s \<in> S\<close>
      unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
    have "\<epsilon> (iota s) = 0" using heps_other \<open>s \<in> S\<close> \<open>s \<noteq> s0\<close> by (by100 blast)
    thus "iota s \<in> ?K" using \<open>iota s \<in> G\<close> by (by100 simp)
  qed
  \<comment> \<open>Condition 3: \<iota> injective on S'.\<close>
  have hiota_inj: "inj_on iota ?S'"
  proof -
    have "inj_on iota S" using hfree
      unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
    thus ?thesis using inj_on_subset by (by5000 blast)
  qed
  \<comment> \<open>Condition 4: K = ⟨\<iota>(S')⟩ (generated by the restricted generators).\<close>
  have hK_gen: "?K = top1_subgroup_generated_on ?K mul e invg (iota ` ?S')"
  proof (rule set_eqI, rule iffI)
    fix g assume hg: "g \<in> ?K"
    \<comment> \<open>g \<in> K \<subseteq> G = ⟨\<iota>(S)⟩. Express g as a word in \<iota>(S) \<union> invg(\<iota>(S)).\<close>
    have hg_G: "g \<in> G" using hg by (by100 blast)
    have hK_grp: "top1_is_group_on ?K mul e invg"
      using hK_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
    have hg_eps: "\<epsilon> g = 0" using hg by (by100 blast)
    \<comment> \<open>g is in the subgroup generated by \<iota>(S') within K.\<close>
    \<comment> \<open>Key: g \<in> G = ⟨\<iota>(S)⟩. By word repr, g is a product of \<iota>(s) and invg(\<iota>(s)).
       In the abelian group, split by s0 vs non-s0. The s0-part evaluates to e
       (since \<epsilon>(g) = 0 forces balanced s0-counts). So g = non-s0 part \<in> ⟨\<iota>(S')⟩.\<close>
    \<comment> \<open>Suffices to show g \<in> ⟨\<iota>(S')⟩_G, since ⟨\<iota>(S')⟩_G \<subseteq> K
       (all generators have \<epsilon> = 0, and K is closed under mul/invg).\<close>
    have hiotaS'_sub_K: "iota ` ?S' \<subseteq> ?K" using hiota_K by (by100 blast)
    have hiotaS'_sub_G: "iota ` ?S' \<subseteq> G"
    proof (rule image_subsetI)
      fix s assume "s \<in> ?S'"
      hence "s \<in> S" by (by100 blast)
      thus "iota s \<in> G" using hfree unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
    qed
    have hgenG_sub_K: "top1_subgroup_generated_on G mul e invg (iota ` ?S') \<subseteq> ?K"
      by (rule subgroup_generated_minimal[OF hiotaS'_sub_K _ hK_grp], by100 blast)
    have hgenK_eq_genG: "top1_subgroup_generated_on ?K mul e invg (iota ` ?S')
        = top1_subgroup_generated_on G mul e invg (iota ` ?S')"
    proof (rule set_eqI, rule iffI)
      fix x assume hx: "x \<in> top1_subgroup_generated_on ?K mul e invg (iota ` ?S')"
      \<comment> \<open>⟨\<iota>(S')⟩_G is a subgroup of K containing \<iota>(S'), so ⟨\<iota>(S')⟩_K \<subseteq> ⟨\<iota>(S')⟩_G.\<close>
      have hgenG_grp: "top1_is_group_on (top1_subgroup_generated_on G mul e invg (iota ` ?S')) mul e invg"
        by (rule intersection_of_subgroups_is_group[OF hG_grp hiotaS'_sub_G])
      have hgenG_sub_K': "top1_subgroup_generated_on G mul e invg (iota ` ?S') \<subseteq> ?K"
        using hgenG_sub_K by (by100 blast)
      have hiotaS'_in_genG: "iota ` ?S' \<subseteq> top1_subgroup_generated_on G mul e invg (iota ` ?S')"
      proof (rule image_subsetI)
        fix s assume "s \<in> ?S'"
        hence "iota s \<in> iota ` ?S'" by (by100 blast)
        thus "iota s \<in> top1_subgroup_generated_on G mul e invg (iota ` ?S')"
          by (rule subgroup_generated_contains[OF hG_grp hiotaS'_sub_G])
      qed
      \<comment> \<open>⟨\<iota>(S')⟩_K \<subseteq> ⟨\<iota>(S')⟩_G by subgroup\_generated\_minimal in K.\<close>
      have "top1_subgroup_generated_on ?K mul e invg (iota ` ?S')
          \<subseteq> top1_subgroup_generated_on G mul e invg (iota ` ?S')"
        by (rule subgroup_generated_minimal[OF hiotaS'_in_genG hgenG_sub_K' hgenG_grp])
      thus "x \<in> top1_subgroup_generated_on G mul e invg (iota ` ?S')"
        using hx by (by100 blast)
    next
      fix x assume hx: "x \<in> top1_subgroup_generated_on G mul e invg (iota ` ?S')"
      hence hx_K: "x \<in> ?K" using hgenG_sub_K by (by100 blast)
      \<comment> \<open>x \<in> ⟨\<iota>(S')⟩_G means x is in every subgroup of G containing \<iota>(S').
         Any subgroup H of K containing \<iota>(S') is also a subgroup of G.
         So ⟨\<iota>(S')⟩_G \<subseteq> H. Hence x \<in> H for all such H, i.e., x \<in> ⟨\<iota>(S')⟩_K.\<close>
      show "x \<in> top1_subgroup_generated_on ?K mul e invg (iota ` ?S')"
        unfolding top1_subgroup_generated_on_def
      proof (rule InterI, clarify)
        fix H assume hH_sub: "H \<subseteq> ?K" and hH_grp: "top1_is_group_on H mul e invg"
            and hH_gen: "iota ` ?S' \<subseteq> H"
        have "H \<subseteq> G" using hH_sub by (by100 blast)
        hence "top1_subgroup_generated_on G mul e invg (iota ` ?S') \<subseteq> H"
          by (rule subgroup_generated_minimal[OF hH_gen _ hH_grp])
        thus "x \<in> H" using hx by (by100 blast)
      qed
    qed
    \<comment> \<open>Now show g \<in> ⟨\<iota>(S')⟩_G. Since g \<in> G = ⟨\<iota>(S)⟩ and \<epsilon>(g) = 0.\<close>
    have "g \<in> top1_subgroup_generated_on G mul e invg (iota ` ?S')"
    proof (cases "g = e")
      case True
      have "e \<in> top1_subgroup_generated_on G mul e invg (iota ` ?S')"
      proof -
        have "top1_is_group_on (top1_subgroup_generated_on G mul e invg (iota ` ?S')) mul e invg"
          by (rule intersection_of_subgroups_is_group[OF hG_grp hiotaS'_sub_G])
        thus ?thesis unfolding top1_is_group_on_def by (by100 blast)
      qed
      thus ?thesis using True by (by100 simp)
    next
      case False
      \<comment> \<open>g \<in> G = ⟨\<iota>(S)⟩, g \<noteq> e. By word representation:\<close>
      have hiotaS_sub: "iota ` S \<subseteq> G"
        using hfree unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
      have hG_gen: "G = top1_subgroup_generated_on G mul e invg (iota ` S)"
        using hfree unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
      have hg_gen: "g \<in> top1_subgroup_generated_on G mul e invg (iota ` S)"
        using hg_G hG_gen by (by100 simp)
      from subgroup_generated_word_repr[OF hG_grp hiotaS_sub hg_gen] False
      obtain ws where hws_len: "length ws > 0"
          and hws_gen: "\<forall>i < length ws. ws ! i \<in> iota ` S \<or> (\<exists>s \<in> iota ` S. ws ! i = invg s)"
          and hws_prod: "foldr mul ws e = g"
        by (by100 blast)
      \<comment> \<open>Split ws into s0-related and non-s0 entries.\<close>
      let ?is_s0 = "\<lambda>x. x = iota s0 \<or> x = invg (iota s0)"
      let ?ws_s0 = "filter ?is_s0 ws"
      let ?ws_rest = "filter (\<lambda>x. \<not> ?is_s0 x) ws"
      \<comment> \<open>All entries are in G.\<close>
      have hws_G: "\<forall>i < length ws. ws ! i \<in> G"
      proof (intro allI impI)
        fix i assume "i < length ws"
        from hws_gen[rule_format, OF this]
        show "ws ! i \<in> G"
        proof (elim disjE)
          assume "ws ! i \<in> iota ` S"
          thus ?thesis using hiotaS_sub by (by100 blast)
        next
          assume "\<exists>s \<in> iota ` S. ws ! i = invg s"
          then obtain s where "s \<in> iota ` S" "ws ! i = invg s" by (by100 blast)
          hence "s \<in> G" using hiotaS_sub by (by100 blast)
          hence "invg s \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
          thus ?thesis using \<open>ws ! i = invg s\<close> by (by100 simp)
        qed
      qed
      \<comment> \<open>By abelian split: g = (s0-part) \<cdot> (rest-part).\<close>
      have hsplit: "g = mul (foldr mul ?ws_s0 e) (foldr mul ?ws_rest e)"
      proof -
        have "foldr mul ws e = mul (foldr mul (filter ?is_s0 ws) e)
            (foldr mul (filter (\<lambda>x. \<not> ?is_s0 x) ws) e)"
          by (rule abelian_foldr_mul_split_filter[OF hG_abel hws_G])
        moreover have "(\<lambda>x. \<not> ?is_s0 x) = (\<lambda>x. x \<noteq> iota s0 \<and> x \<noteq> invg (iota s0))"
          by (by100 auto)
        ultimately show ?thesis using hws_prod by (by5000 simp)
      qed
      \<comment> \<open>The rest-part entries are from \<iota>(S') \<union> invg(\<iota>(S')).\<close>
      \<comment> \<open>The s0-part has \<epsilon> = 0 (since \<epsilon>(g) = 0 and \<epsilon>(rest) = 0).\<close>
      \<comment> \<open>Hence s0-part = e, and g = rest-part \<in> ⟨\<iota>(S')⟩.\<close>
      \<comment> \<open>Step 1: \<epsilon>(rest) = 0 (each non-s0 entry has \<epsilon> = 0).\<close>
      \<comment> \<open>Step 2: \<epsilon>(s0-part) = \<epsilon>(g) - \<epsilon>(rest) = 0 - 0 = 0.\<close>
      \<comment> \<open>Step 3: s0-part is a product of balanced \<iota>(s0) and invg(\<iota>(s0)), so = e.\<close>
      \<comment> \<open>Step 4: g = e \<cdot> rest = rest \<in> ⟨\<iota>(S')⟩.\<close>
      \<comment> \<open>The rest entries are from \<iota>(S') \<union> invg(\<iota>(S')).\<close>
      have hrest_gen: "\<forall>x \<in> set ?ws_rest. x \<in> iota ` ?S' \<or> (\<exists>s \<in> iota ` ?S'. x = invg s)"
      proof (intro ballI)
        fix x assume "x \<in> set ?ws_rest"
        hence "x \<in> set ws" "\<not> ?is_s0 x" by (by100 auto)+
        from \<open>x \<in> set ws\<close> obtain i where "i < length ws" "ws ! i = x"
          using in_set_conv_nth by (by5000 metis)
        from hws_gen[rule_format, OF \<open>i < length ws\<close>]
        have "ws ! i \<in> iota ` S \<or> (\<exists>s \<in> iota ` S. ws ! i = invg s)" .
        thus "x \<in> iota ` ?S' \<or> (\<exists>s \<in> iota ` ?S'. x = invg s)"
          using \<open>ws ! i = x\<close> \<open>\<not> ?is_s0 x\<close> by (by5000 auto)
      qed
      \<comment> \<open>The rest-part is in ⟨\<iota>(S')⟩_G.\<close>
      have hrest_in_gen: "foldr mul ?ws_rest e
          \<in> top1_subgroup_generated_on G mul e invg (iota ` ?S')"
      proof -
        let ?H = "top1_subgroup_generated_on G mul e invg (iota ` ?S')"
        have hH_grp: "top1_is_group_on ?H mul e invg"
          by (rule intersection_of_subgroups_is_group[OF hG_grp hiotaS'_sub_G])
        have hH_sub: "?H \<subseteq> G"
          by (rule subgroup_generated_subset[OF hG_grp hiotaS'_sub_G])
        have hiotaS'_in_H: "\<forall>s\<in>?S'. iota s \<in> ?H"
        proof (intro ballI)
          fix s assume "s \<in> ?S'"
          hence "iota s \<in> iota ` ?S'" by (by100 blast)
          thus "iota s \<in> ?H"
            by (rule subgroup_generated_contains[OF hG_grp hiotaS'_sub_G])
        qed
        \<comment> \<open>By induction on the list: foldr of generators/inverses is in H.\<close>
        have "\<forall>xs. (\<forall>x\<in>set xs. x \<in> iota ` ?S' \<or> (\<exists>s\<in>iota ` ?S'. x = invg s))
            \<longrightarrow> foldr mul xs e \<in> ?H"
        proof (intro allI impI)
          fix xs :: "'g list"
          assume hxs: "\<forall>x\<in>set xs. x \<in> iota ` ?S' \<or> (\<exists>s\<in>iota ` ?S'. x = invg s)"
          show "foldr mul xs e \<in> ?H"
          using hxs proof (induction xs)
            case Nil
            show ?case using hH_grp unfolding top1_is_group_on_def by (by100 simp)
          next
            case (Cons a xs)
            have ha_entry: "a \<in> iota ` ?S' \<or> (\<exists>s\<in>iota ` ?S'. a = invg s)"
              using Cons(2) by (by100 simp)
            have hxs_entry: "\<forall>x\<in>set xs. x \<in> iota ` ?S' \<or> (\<exists>s\<in>iota ` ?S'. x = invg s)"
              using Cons(2) by (by100 simp)
            have hIH: "foldr mul xs e \<in> ?H" using Cons(1) hxs_entry by (by100 blast)
            have ha_H: "a \<in> ?H"
            proof (cases "a \<in> iota ` ?S'")
              case True
              thus ?thesis using subgroup_generated_contains[OF hG_grp hiotaS'_sub_G] by (by100 blast)
            next
              case False
              hence "\<exists>s\<in>iota ` ?S'. a = invg s" using ha_entry by (by100 blast)
              then obtain s where "s \<in> iota ` ?S'" "a = invg s" by (by100 blast)
              have "s \<in> ?H" using subgroup_generated_contains[OF hG_grp hiotaS'_sub_G \<open>s \<in> iota ` ?S'\<close>] .
              hence "invg s \<in> ?H" using hH_grp unfolding top1_is_group_on_def by (by100 blast)
              thus ?thesis using \<open>a = invg s\<close> by (by100 simp)
            qed
            have "foldr mul (a # xs) e = mul a (foldr mul xs e)" by (by100 simp)
            also have "\<dots> \<in> ?H" using hH_grp ha_H hIH unfolding top1_is_group_on_def by (by100 blast)
            finally show ?case .
          qed
        qed
        thus ?thesis using hrest_gen by (by100 blast)
      qed
      \<comment> \<open>The s0-part evaluates to e (balanced \<iota>(s0) and invg(\<iota>(s0))).\<close>
      have hs0_eq_e: "foldr mul ?ws_s0 e = e"
      proof -
        let ?a = "iota s0"
        let ?ia = "invg (iota s0)"
        have ha_G: "?a \<in> G" using hfree hs0
          unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
        have hia_G: "?ia \<in> G" using hG_grp ha_G unfolding top1_is_group_on_def by (by100 blast)
        \<comment> \<open>All entries of ws_s0 are in G.\<close>
        have hws_s0_G: "\<forall>i<length ?ws_s0. ?ws_s0 ! i \<in> G"
        proof (intro allI impI)
          fix i assume "i < length ?ws_s0"
          have "?ws_s0 ! i \<in> set ?ws_s0"
            using nth_mem \<open>i < length ?ws_s0\<close> by (by100 blast)
          hence "?ws_s0 ! i = ?a \<or> ?ws_s0 ! i = ?ia"
            by (by5000 auto)
          thus "?ws_s0 ! i \<in> G" using ha_G hia_G by (by5000 auto)
        qed
        \<comment> \<open>Compute \<epsilon> on ws_s0 via hom_foldr_mul.\<close>
        have hZ_grp: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
          unfolding top1_is_group_on_def by (by100 auto)
        have heps_s0_prod: "\<epsilon> (foldr mul ?ws_s0 e)
            = foldr (+) (map \<epsilon> ?ws_s0) (0::int)"
          using hom_foldr_mul_early[OF hG_grp hZ_grp heps hws_s0_G] by (by100 simp)
        \<comment> \<open>\<epsilon>(rest) = 0 (each entry has \<epsilon> = 0).\<close>
        have hws_rest_G: "\<forall>i<length ?ws_rest. ?ws_rest ! i \<in> G"
        proof (intro allI impI)
          fix i assume "i < length ?ws_rest"
          have "?ws_rest ! i \<in> set ?ws_rest"
            using nth_mem \<open>i < length ?ws_rest\<close> by (by100 blast)
          hence "?ws_rest ! i \<in> set ws" by (by5000 auto)
          then obtain j where "j < length ws" "ws ! j = ?ws_rest ! i"
            using in_set_conv_nth by (by5000 metis)
          have "ws ! j \<in> G" using hws_G \<open>j < length ws\<close> by (by100 blast)
          thus "?ws_rest ! i \<in> G" using \<open>ws ! j = ?ws_rest ! i\<close> by (by100 simp)
        qed
        have heps_rest: "\<epsilon> (foldr mul ?ws_rest e) = 0"
        proof -
          have "map \<epsilon> ?ws_rest = map (\<lambda>x. 0::int) ?ws_rest"
          proof (rule list.map_cong0)
            fix x assume "x \<in> set ?ws_rest"
            hence "x \<in> set ws" "\<not> ?is_s0 x" by (by100 auto)+
            then obtain j where "j < length ws" "ws ! j = x"
              using in_set_conv_nth by (by5000 metis)
            from hws_gen[rule_format, OF \<open>j < length ws\<close>]
            have "ws ! j \<in> iota ` S \<or> (\<exists>s \<in> iota ` S. ws ! j = invg s)" .
            hence "x \<in> iota ` S \<or> (\<exists>s \<in> iota ` S. x = invg s)"
              using \<open>ws ! j = x\<close> by (by100 simp)
            thus "\<epsilon> x = 0"
            proof (elim disjE)
              assume "x \<in> iota ` S"
              then obtain s where "s \<in> S" "x = iota s" by (by100 blast)
              hence "s \<noteq> s0" using \<open>\<not> ?is_s0 x\<close> by (by100 auto)
              thus "\<epsilon> x = 0" using heps_other \<open>s \<in> S\<close> \<open>x = iota s\<close> by (by100 simp)
            next
              assume "\<exists>s \<in> iota ` S. x = invg s"
              then obtain s where "s \<in> S" "x = invg (iota s)" by (by100 blast)
              have "iota s \<in> G" using hiotaS_sub \<open>s \<in> S\<close> by (by100 blast)
              have "\<epsilon> (iota s) = 0"
              proof (cases "s = s0")
                case True
                \<comment> \<open>If s = s0, then x = invg(iota s0), so is_s0 x = True. Contradiction.\<close>
                hence "x = ?ia" using \<open>x = invg (iota s)\<close> by (by100 simp)
                hence "?is_s0 x" by (by100 blast)
                thus ?thesis using \<open>\<not> ?is_s0 x\<close> by (by100 blast)
              next
                case False thus ?thesis using heps_other \<open>s \<in> S\<close> by (by100 blast)
              qed
              have "\<epsilon> x = - \<epsilon> (iota s)"
                using hom_preserves_inv[OF hG_grp hZ_grp heps \<open>iota s \<in> G\<close>]
                  \<open>x = invg (iota s)\<close> by (by100 simp)
              thus "\<epsilon> x = 0" using \<open>\<epsilon> (iota s) = 0\<close> by (by100 simp)
            qed
          qed
          hence "foldr (+) (map \<epsilon> ?ws_rest) (0::int) = foldr (+) (map (\<lambda>x. 0::int) ?ws_rest) 0"
            by (rule arg_cong[of _ _ "\<lambda>xs. foldr (+) xs 0"])
          also have "\<dots> = (0::int)"
          proof -
            define ys where "ys = ?ws_rest"
            have "foldr (+) (map (\<lambda>x. 0::int) ys) 0 = 0"
              by (induction ys, by100 simp, by100 simp)
            thus ?thesis unfolding ys_def by (by100 simp)
          qed
          finally have "foldr (+) (map \<epsilon> ?ws_rest) (0::int) = 0" .
          moreover have "\<epsilon> (foldr mul ?ws_rest e) = foldr (+) (map \<epsilon> ?ws_rest) (0::int)"
            using hom_foldr_mul_early[OF hG_grp hZ_grp heps hws_rest_G] by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        \<comment> \<open>\<epsilon>(s0-part) = \<epsilon>(g) - \<epsilon>(rest) = 0.\<close>
        have heps_s0_val: "\<epsilon> (foldr mul ?ws_s0 e) = 0"
        proof -
          have hprod_s0_G: "foldr mul ?ws_s0 e \<in> G"
            by (rule foldr_mul_closed[OF hG_grp hws_s0_G])
          have hprod_rest_G: "foldr mul ?ws_rest e \<in> G"
            by (rule foldr_mul_closed[OF hG_grp hws_rest_G])
          have "\<epsilon> g = \<epsilon> (mul (foldr mul ?ws_s0 e) (foldr mul ?ws_rest e))"
            using hsplit by (by100 simp)
          also have "\<dots> = \<epsilon> (foldr mul ?ws_s0 e) + \<epsilon> (foldr mul ?ws_rest e)"
            using heps hprod_s0_G hprod_rest_G unfolding top1_group_hom_on_def by (by100 blast)
          finally show ?thesis using hg_eps heps_rest by (by100 linarith)
        qed
        \<comment> \<open>ws_s0 consists of k copies of \<iota>(s0) and k copies of invg(\<iota>(s0)).\<close>
        \<comment> \<open>In the abelian group, split ws_s0 into \<iota>(s0)-entries and invg(\<iota>(s0))-entries.\<close>
        let ?ws_pos = "filter (\<lambda>x. x = ?a) ?ws_s0"
        let ?ws_neg = "filter (\<lambda>x. x = ?ia) ?ws_s0"
        have hws_s0_split: "foldr mul ?ws_s0 e = mul (foldr mul ?ws_pos e) (foldr mul ?ws_neg e)"
        proof -
          have h1: "foldr mul ?ws_s0 e = mul (foldr mul (filter (\<lambda>x. x = ?a) ?ws_s0) e)
              (foldr mul (filter (\<lambda>x. \<not>(x = ?a)) ?ws_s0) e)"
            by (rule abelian_foldr_mul_split_filter[OF hG_abel hws_s0_G])
          \<comment> \<open>filter (\<lambda>x. x \<noteq> ?a) ws_s0 = filter (\<lambda>x. x = ?ia) ws_s0
             since ws_s0 only contains ?a and ?ia.\<close>
          have "filter (\<lambda>x. \<not>(x = ?a)) ?ws_s0 = filter (\<lambda>x. x = ?ia) ?ws_s0"
        proof (rule filter_cong, by100 simp)
            fix x assume "x \<in> set ?ws_s0"
            hence "x = ?a \<or> x = ?ia" by (by5000 auto)
            moreover have "?a \<noteq> ?ia"
            proof
              assume "?a = ?ia"
              hence "\<epsilon> ?a = \<epsilon> ?ia" by (by100 simp)
              have "\<epsilon> ?ia = - \<epsilon> ?a"
                using hom_preserves_inv[OF hG_grp hZ_grp heps ha_G] by (by100 simp)
              hence "\<epsilon> ?ia = -(1::int)" using heps_s0 by (by100 simp)
              hence "(1::int) = -1" using \<open>\<epsilon> ?a = \<epsilon> ?ia\<close> heps_s0 by (by100 linarith)
              thus False by (by100 simp)
            qed
            ultimately show "(\<not>(x = ?a)) = (x = ?ia)" by (by100 auto)
          qed
          thus ?thesis using h1 by (by100 simp)
        qed
        \<comment> \<open>pos-part = pow(\<iota>(s0), k+), neg-part = pow(invg(\<iota>(s0)), k-).\<close>
        \<comment> \<open>\<epsilon>(pos) = k+, \<epsilon>(neg) = -k-. \<epsilon>(s0-part) = k+ - k- = 0, so k+ = k-.\<close>
        \<comment> \<open>pow(x, k) \<cdot> pow(invg(x), k) = e.\<close>
        \<comment> \<open>pos-part = pow(\<iota>(s0), k+) by abelian\_foldr\_mul\_filter\_eq.\<close>
        let ?kp = "length ?ws_pos"
        let ?kn = "length ?ws_neg"
        \<comment> \<open>?ws\_pos = filter on filter = filter (x = a) on ws.\<close>
        have hpos_eq: "?ws_pos = filter (\<lambda>x. x = ?a) ws"
        proof -
          have "filter (\<lambda>x. x = ?a) (filter ?is_s0 ws) = filter (\<lambda>x. ?is_s0 x \<and> x = ?a) ws"
            by (by5000 simp)
          also have "\<dots> = filter (\<lambda>x. x = ?a) ws"
            by (rule filter_cong, by100 simp, by100 auto)
          finally show ?thesis by (by100 simp)
        qed
        have hneg_eq: "?ws_neg = filter (\<lambda>x. x = ?ia) ws"
        proof -
          have "filter (\<lambda>x. x = ?ia) (filter ?is_s0 ws) = filter (\<lambda>x. ?is_s0 x \<and> x = ?ia) ws"
            by (by5000 simp)
          also have "\<dots> = filter (\<lambda>x. x = ?ia) ws"
            by (rule filter_cong, by100 simp, by100 auto)
          finally show ?thesis by (by100 simp)
        qed
        have hpos_pow: "foldr mul ?ws_pos e = top1_group_pow mul e ?a ?kp"
          using abelian_foldr_mul_filter_eq[OF hG_grp ha_G, of ws] hpos_eq by (by100 simp)
        have hneg_pow: "foldr mul ?ws_neg e = top1_group_pow mul e ?ia ?kn"
          using abelian_foldr_mul_filter_eq[OF hG_grp hia_G, of ws] hneg_eq by (by100 simp)
        \<comment> \<open>\<epsilon> on the pos/neg parts.\<close>
        have hpos_G: "foldr mul ?ws_pos e \<in> G"
          using hpos_pow group_pow_in_group'[OF hG_grp ha_G] by (by100 simp)
        have hneg_G: "foldr mul ?ws_neg e \<in> G"
          using hneg_pow group_pow_in_group'[OF hG_grp hia_G] by (by100 simp)
        have heps_pos: "\<epsilon> (foldr mul ?ws_pos e) = int ?kp"
        proof -
          have "\<epsilon> (top1_group_pow mul e ?a ?kp) = top1_group_pow (+) (0::int) 1 ?kp"
            using hom_group_pow_early[OF hG_grp hZ_grp heps ha_G] heps_s0 by (by100 simp)
          also have "\<dots> = int ?kp"
          proof -
            define m where "m = ?kp"
            have "top1_group_pow (+) (0::int) 1 m = int m"
              by (induction m, by100 simp, by100 simp)
            thus ?thesis unfolding m_def by (by100 simp)
          qed
          finally show ?thesis using hpos_pow by (by100 simp)
        qed
        have heps_neg: "\<epsilon> (foldr mul ?ws_neg e) = - int ?kn"
        proof -
          have "\<epsilon> ?ia = -(1::int)"
            using hom_preserves_inv[OF hG_grp hZ_grp heps ha_G] heps_s0 by (by100 simp)
          hence "\<epsilon> (top1_group_pow mul e ?ia ?kn) = top1_group_pow (+) (0::int) (-(1::int)) ?kn"
            using hom_group_pow_early[OF hG_grp hZ_grp heps hia_G] by (by100 simp)
          also have "\<dots> = - int ?kn"
          proof -
            define m where "m = ?kn"
            have "top1_group_pow (+) (0::int) (-(1::int)) m = - int m"
              by (induction m, by100 simp, by100 simp)
            thus ?thesis unfolding m_def by (by100 simp)
          qed
          finally show ?thesis using hneg_pow by (by100 simp)
        qed
        \<comment> \<open>From \<epsilon>(s0-part) = 0: k+ = k-.\<close>
        have hkp_eq_kn: "?kp = ?kn"
        proof -
          have "\<epsilon> (foldr mul ?ws_s0 e) = \<epsilon> (mul (foldr mul ?ws_pos e) (foldr mul ?ws_neg e))"
            using hws_s0_split by (by100 simp)
          also have "\<dots> = \<epsilon> (foldr mul ?ws_pos e) + \<epsilon> (foldr mul ?ws_neg e)"
            using heps hpos_G hneg_G unfolding top1_group_hom_on_def by (by100 blast)
          also have "\<dots> = int ?kp - int ?kn" using heps_pos heps_neg by (by100 linarith)
          finally show ?thesis using heps_s0_val by (by100 linarith)
        qed
        \<comment> \<open>pow(x, k) \<cdot> pow(invg(x), k) = e by induction.\<close>
        have hpow_cancel: "\<And>n. mul (top1_group_pow mul e ?a n) (top1_group_pow mul e ?ia n) = e"
        proof -
          fix n show "mul (top1_group_pow mul e ?a n) (top1_group_pow mul e ?ia n) = e"
          proof (induction n)
            case 0
            have "mul e e = e" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
            thus ?case by (by100 simp)
          next
            case (Suc n)
            \<comment> \<open>pow(a, Suc n) = mul a (pow(a, n)). Similarly for ia.\<close>
            \<comment> \<open>mul (mul a (pow(a,n))) (mul ia (pow(ia,n)))
               = mul a (mul (pow(a,n)) (mul ia (pow(ia,n))))  [assoc]
               = mul a (mul (mul (pow(a,n)) ia) (pow(ia,n)))  [assoc]
               = mul a (mul ia (mul (pow(a,n)) (pow(ia,n))))  [commute in abelian]
               = mul (mul a ia) (mul (pow(a,n)) (pow(ia,n)))  [assoc]
               = mul e (mul (pow(a,n)) (pow(ia,n)))           [a * ia = e]
               = mul (pow(a,n)) (pow(ia,n))                   [e * x = x]
               = e                                            [IH]  \<close>
            let ?pn = "top1_group_pow mul e ?a n"
            let ?pin = "top1_group_pow mul e ?ia n"
            have hpn_G: "?pn \<in> G" using group_pow_in_group'[OF hG_grp ha_G] by (by100 simp)
            have hpin_G: "?pin \<in> G" using group_pow_in_group'[OF hG_grp hia_G] by (by100 simp)
            have haia: "mul ?a ?ia = e" using hG_grp ha_G unfolding top1_is_group_on_def by (by100 blast)
            \<comment> \<open>In abelian group: mul(mul a pn)(mul ia pin) = mul(mul a ia)(mul pn pin).\<close>
            have "mul (mul ?a ?pn) (mul ?ia ?pin)
                = mul (mul ?a ?ia) (mul ?pn ?pin)"
            proof -
              have hG_grp_loc: "top1_is_group_on G mul e invg"
                using hG_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
              have hassoc: "\<And>x y z. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> z \<in> G \<Longrightarrow>
                  mul (mul x y) z = mul x (mul y z)"
                using hG_grp_loc unfolding top1_is_group_on_def by (by100 blast)
              have hcomm: "\<And>x y. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> mul x y = mul y x"
                using hG_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
              have h_ia_pin: "mul ?ia ?pin \<in> G"
                using hG_grp_loc hia_G hpin_G unfolding top1_is_group_on_def by (by100 blast)
              have h_pn_pin: "mul ?pn ?pin \<in> G"
                using hG_grp_loc hpn_G hpin_G unfolding top1_is_group_on_def by (by100 blast)
              \<comment> \<open>(a \<cdot> pn) \<cdot> (ia \<cdot> pin) = a \<cdot> (pn \<cdot> (ia \<cdot> pin)).\<close>
              have s1: "mul (mul ?a ?pn) (mul ?ia ?pin) = mul ?a (mul ?pn (mul ?ia ?pin))"
                by (rule hassoc[OF ha_G hpn_G h_ia_pin])
              \<comment> \<open>pn \<cdot> (ia \<cdot> pin) = (pn \<cdot> ia) \<cdot> pin.\<close>
              have s2: "mul ?pn (mul ?ia ?pin) = mul (mul ?pn ?ia) ?pin"
                using hassoc[OF hpn_G hia_G hpin_G] by (by100 simp)
              \<comment> \<open>pn \<cdot> ia = ia \<cdot> pn (commutativity).\<close>
              have s3: "mul ?pn ?ia = mul ?ia ?pn"
                by (rule hcomm[OF hpn_G hia_G])
              \<comment> \<open>Reassemble: a \<cdot> ((ia \<cdot> pn) \<cdot> pin) = a \<cdot> (ia \<cdot> (pn \<cdot> pin)).\<close>
              have h_ia_pn: "mul ?ia ?pn \<in> G"
                using hG_grp_loc hia_G hpn_G unfolding top1_is_group_on_def by (by100 blast)
              have s4: "mul (mul ?ia ?pn) ?pin = mul ?ia (mul ?pn ?pin)"
                by (rule hassoc[OF hia_G hpn_G hpin_G])
              \<comment> \<open>a \<cdot> (ia \<cdot> (pn \<cdot> pin)) = (a \<cdot> ia) \<cdot> (pn \<cdot> pin).\<close>
              have s5: "mul ?a (mul ?ia (mul ?pn ?pin)) = mul (mul ?a ?ia) (mul ?pn ?pin)"
                using hassoc[OF ha_G hia_G h_pn_pin] by (by100 simp)
              show ?thesis using s1 s2 s3 s4 s5 by (by100 simp)
            qed
            also have "\<dots> = mul e e" using Suc.IH haia by (by100 simp)
            also have "\<dots> = e" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
            finally show ?case by (by100 simp)
          qed
        qed
        show ?thesis
          using hws_s0_split hpos_pow hneg_pow hkp_eq_kn hpow_cancel[of ?kp] by (by5000 simp)
      qed
      \<comment> \<open>Therefore g = e \<cdot> rest = rest \<in> ⟨\<iota>(S')⟩.\<close>
      have "g = mul e (foldr mul ?ws_rest e)"
        using hsplit hs0_eq_e by (by100 simp)
      also have "\<dots> = foldr mul ?ws_rest e"
      proof -
        have "foldr mul ?ws_rest e \<in> G"
          using hrest_in_gen
            subgroup_generated_subset[OF hG_grp hiotaS'_sub_G]
          by (by100 blast)
        thus ?thesis using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      qed
      finally show ?thesis using hrest_in_gen by (by100 simp)
    qed
    thus "g \<in> top1_subgroup_generated_on ?K mul e invg (iota ` ?S')"
      using hgenK_eq_genG by (by100 simp)
  next
    fix g assume "g \<in> top1_subgroup_generated_on ?K mul e invg (iota ` ?S')"
    \<comment> \<open>\<iota>(S') \<subseteq> K, K is a group, so ⟨\<iota>(S')⟩_K \<subseteq> K.\<close>
    have "iota ` ?S' \<subseteq> ?K" using hiota_K by (by100 blast)
    have hK_sub: "?K \<subseteq> ?K" by (by100 blast)
    have hK_grp: "top1_is_group_on ?K mul e invg"
      using hK_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
    show "g \<in> ?K"
      using subgroup_generated_subset[OF hK_grp \<open>iota ` ?S' \<subseteq> ?K\<close>]
        \<open>g \<in> top1_subgroup_generated_on ?K mul e invg (iota ` ?S')\<close>
      by (by100 blast)
  qed
  \<comment> \<open>Condition 5: Independence on S'.\<close>
  have hK_indep: "\<forall>c :: 's \<Rightarrow> int. finite {s \<in> ?S'. c s \<noteq> 0} \<longrightarrow>
      (\<exists>s\<in>?S'. c s \<noteq> 0) \<longrightarrow>
      foldr mul (map (\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (iota s) (nat (c s))
                          else top1_group_pow mul e (invg (iota s)) (nat (- c s)))
           (SOME xs. set xs = {s \<in> ?S'. c s \<noteq> 0} \<and> distinct xs)) e \<noteq> e"
  proof (intro allI impI)
    fix c :: "'s \<Rightarrow> int"
    assume hfin_c: "finite {s \<in> ?S'. c s \<noteq> 0}" and hex_c: "\<exists>s\<in>?S'. c s \<noteq> 0"
    \<comment> \<open>Extend c to S by setting c(s0) = 0. Then apply G's independence.\<close>
    let ?c' = "\<lambda>s. if s \<in> ?S' then c s else 0"
    have "{s \<in> S. ?c' s \<noteq> 0} = {s \<in> ?S'. c s \<noteq> 0}"
    proof (rule set_eqI, rule iffI)
      fix s assume "s \<in> {s \<in> S. ?c' s \<noteq> 0}"
      hence hs: "s \<in> S" and hc: "(if s \<in> S - {s0} then c s else 0) \<noteq> 0"
        by (by100 auto)+
      have "s \<in> ?S'"
      proof (rule ccontr)
        assume "s \<notin> ?S'"
        hence "?c' s = 0" by (by5000 auto)
        thus False using hc by (by100 simp)
      qed
      moreover have "c s \<noteq> 0" using hc \<open>s \<in> ?S'\<close> by (by100 simp)
      ultimately show "s \<in> {s \<in> ?S'. c s \<noteq> 0}" by (by100 blast)
    next
      fix s assume "s \<in> {s \<in> ?S'. c s \<noteq> 0}"
      hence "s \<in> ?S'" "c s \<noteq> 0" by (by100 auto)+
      hence "s \<in> S" "?c' s \<noteq> 0" by (by100 auto)+
      thus "s \<in> {s \<in> S. ?c' s \<noteq> 0}" by (by100 blast)
    qed
    have hfin_c': "finite {s \<in> S. ?c' s \<noteq> 0}" using hfin_c \<open>{s \<in> S. ?c' s \<noteq> 0} = _\<close>
      by (by100 simp)
    have hex_c': "\<exists>s\<in>S. ?c' s \<noteq> 0"
    proof -
      from hex_c obtain s where "s \<in> ?S'" "c s \<noteq> 0" by (by100 blast)
      hence "s \<in> S" "?c' s \<noteq> 0" by (by100 auto)+
      thus ?thesis by (by100 blast)
    qed
    \<comment> \<open>The canonical products for c and c' on S are the same (since c'(s0) = 0).\<close>
    \<comment> \<open>Support sets are equal, so SOME chooses the same list.\<close>
    have hsupport_eq: "{s \<in> S. ?c' s \<noteq> 0} = {s \<in> ?S'. c s \<noteq> 0}"
      using \<open>{s \<in> S. ?c' s \<noteq> 0} = _\<close> by (by100 simp)
    \<comment> \<open>On the support, c' = c.\<close>
    have hval_eq: "\<forall>s\<in>{s \<in> ?S'. c s \<noteq> 0}. ?c' s = c s" by (by100 auto)
    \<comment> \<open>G's independence gives the product \<noteq> e.\<close>
    have hG_indep_all: "\<forall>c'. finite {s \<in> S. c' s \<noteq> 0} \<longrightarrow>
        (\<exists>s\<in>S. c' s \<noteq> 0) \<longrightarrow>
        foldr mul (map (\<lambda>s. if c' s \<ge> 0
          then top1_group_pow mul e (iota s) (nat (c' s))
          else top1_group_pow mul e (invg (iota s)) (nat (- c' s)))
          (SOME xs. set xs = {s \<in> S. c' s \<noteq> 0} \<and> distinct xs)) e \<noteq> e"
      using hfree unfolding top1_is_free_abelian_group_full_on_def by (by5000 blast)
    have hG_indep: "foldr mul (map (\<lambda>s. if ?c' s \<ge> 0
          then top1_group_pow mul e (iota s) (nat (?c' s))
          else top1_group_pow mul e (invg (iota s)) (nat (- ?c' s)))
        (SOME xs. set xs = {s \<in> S. ?c' s \<noteq> 0} \<and> distinct xs)) e \<noteq> e"
      using hG_indep_all[rule_format, OF hfin_c' hex_c'] by (by100 simp)
    \<comment> \<open>The product for c on S' equals the product for c' on S (same support, same values).\<close>
    \<comment> \<open>The SOME lists are the same (same set predicate via hsupport_eq).\<close>
    let ?L = "SOME xs. set xs = {s \<in> ?S'. c s \<noteq> 0} \<and> distinct xs"
    have h_list_eq: "(SOME xs. set xs = {s \<in> S. ?c' s \<noteq> 0} \<and> distinct xs) = ?L"
      using hsupport_eq by (by100 simp)
    \<comment> \<open>The map functions agree on elements of the list.\<close>
    have h_on_support: "\<forall>s \<in> {s \<in> ?S'. c s \<noteq> 0}. ?c' s = c s"
      using hval_eq by (by100 blast)
    \<comment> \<open>The two foldr expressions are equal.\<close>
    \<comment> \<open>First rewrite the SOME using hsupport_eq.\<close>
    define L where "L = (SOME xs :: 's list. set xs = {s \<in> ?S'. c s \<noteq> 0} \<and> distinct xs)"
    have hG_indep': "foldr mul (map (\<lambda>s. if ?c' s \<ge> 0
          then top1_group_pow mul e (iota s) (nat (?c' s))
          else top1_group_pow mul e (invg (iota s)) (nat (- ?c' s))) L) e \<noteq> e"
      using hG_indep h_list_eq L_def by (by100 simp)
    \<comment> \<open>Now show map with ?c' agrees with map with c on L.\<close>
    have h_set_L: "set L \<subseteq> {s \<in> ?S'. c s \<noteq> 0}"
    proof -
      have "\<exists>xs :: 's list. set xs = {s \<in> ?S'. c s \<noteq> 0} \<and> distinct xs"
        using finite_distinct_list[OF hfin_c] by (by100 blast)
      hence "set L = {s \<in> ?S'. c s \<noteq> 0} \<and> distinct L"
        unfolding L_def by (rule someI_ex)
      thus ?thesis by (by100 blast)
    qed
    have h_pointwise: "\<forall>s\<in>set L.
        (if ?c' s \<ge> 0 then top1_group_pow mul e (iota s) (nat (?c' s))
         else top1_group_pow mul e (invg (iota s)) (nat (- ?c' s)))
      = (if c s \<ge> 0 then top1_group_pow mul e (iota s) (nat (c s))
         else top1_group_pow mul e (invg (iota s)) (nat (- c s)))"
    proof (intro ballI)
      fix s assume "s \<in> set L"
      hence "s \<in> {s \<in> ?S'. c s \<noteq> 0}" using h_set_L by (by100 blast)
      hence "?c' s = c s" using h_on_support by (by100 blast)
      thus "(if ?c' s \<ge> 0 then top1_group_pow mul e (iota s) (nat (?c' s))
         else top1_group_pow mul e (invg (iota s)) (nat (- ?c' s)))
      = (if c s \<ge> 0 then top1_group_pow mul e (iota s) (nat (c s))
         else top1_group_pow mul e (invg (iota s)) (nat (- c s)))"
        by (by100 simp)
    qed
    have h_map_eq: "map (\<lambda>s. if ?c' s \<ge> 0
          then top1_group_pow mul e (iota s) (nat (?c' s))
          else top1_group_pow mul e (invg (iota s)) (nat (- ?c' s))) L
      = map (\<lambda>s. if c s \<ge> 0
          then top1_group_pow mul e (iota s) (nat (c s))
          else top1_group_pow mul e (invg (iota s)) (nat (- c s))) L"
    proof (rule list.map_cong0)
      fix s assume "s \<in> set L"
      thus "(if ?c' s \<ge> 0 then top1_group_pow mul e (iota s) (nat (?c' s))
         else top1_group_pow mul e (invg (iota s)) (nat (- ?c' s)))
        = (if c s \<ge> 0 then top1_group_pow mul e (iota s) (nat (c s))
           else top1_group_pow mul e (invg (iota s)) (nat (- c s)))"
        using h_pointwise by (by100 blast)
    qed
    show "foldr mul (map (\<lambda>s. if c s \<ge> 0
          then top1_group_pow mul e (iota s) (nat (c s))
          else top1_group_pow mul e (invg (iota s)) (nat (- c s)))
        (SOME xs. set xs = {s \<in> ?S'. c s \<noteq> 0} \<and> distinct xs)) e \<noteq> e"
    proof -
      from h_map_eq have "foldr mul (map (\<lambda>s. if ?c' s \<ge> 0
          then top1_group_pow mul e (iota s) (nat (?c' s))
          else top1_group_pow mul e (invg (iota s)) (nat (- ?c' s))) L) e
        = foldr mul (map (\<lambda>s. if c s \<ge> 0
          then top1_group_pow mul e (iota s) (nat (c s))
          else top1_group_pow mul e (invg (iota s)) (nat (- c s))) L) e"
        by (rule arg_cong[of _ _ "\<lambda>xs. foldr mul xs e"])
      thus ?thesis using hG_indep' L_def by (by5000 simp)
    qed
  qed
  show ?thesis unfolding top1_is_free_abelian_group_full_on_def
    using hK_abel hiota_K hiota_inj hK_gen hK_indep by (by100 blast)
qed

text \<open>Group power distributes over addition of exponents.\<close>
lemma group_pow_add:
  assumes "top1_is_group_on G mul e invg" "x \<in> G"
  shows "top1_group_pow mul e x (m + n) = mul (top1_group_pow mul e x m) (top1_group_pow mul e x n)"
  using assms(2)
proof (induction m)
  case 0
  have "top1_group_pow mul e x n \<in> G" by (rule group_pow_in_group'[OF assms])
  thus ?case using assms(1) unfolding top1_is_group_on_def by (by100 simp)
next
  case (Suc m)
  have hpow_m: "top1_group_pow mul e x m \<in> G" by (rule group_pow_in_group'[OF assms])
  have hpow_n: "top1_group_pow mul e x n \<in> G" by (rule group_pow_in_group'[OF assms])
  have hIH_eq: "top1_group_pow mul e x (m + n) = mul (top1_group_pow mul e x m) (top1_group_pow mul e x n)"
    using Suc.IH[OF Suc.prems] by (by100 simp)
  have "top1_group_pow mul e x (Suc m + n) = mul x (top1_group_pow mul e x (m + n))"
    by (by100 simp)
  also have "\<dots> = mul x (mul (top1_group_pow mul e x m) (top1_group_pow mul e x n))"
    using hIH_eq by (by100 simp)
  also have "\<dots> = mul (mul x (top1_group_pow mul e x m)) (top1_group_pow mul e x n)"
  proof -
    have hassoc: "\<forall>a\<in>G. \<forall>b\<in>G. \<forall>c\<in>G. mul (mul a b) c = mul a (mul b c)"
      using assms(1) unfolding top1_is_group_on_def by (by100 blast)
    thus ?thesis using hassoc[rule_format, OF assms(2) hpow_m hpow_n] by (by100 simp)
  qed
  finally show ?case by (by100 simp)
qed

text \<open>In an abelian group, the "doubles" subgroup {g\<cdot>g | g \<in> G} is normal.\<close>
lemma abelian_doubles_normal:
  assumes hG: "top1_is_abelian_group_on G mul e invg"
  shows "top1_normal_subgroup_on G mul e invg {mul g g | g. g \<in> G}"
proof -
  let ?D = "{mul g g | g. g \<in> G}"
  have hG_grp: "top1_is_group_on G mul e invg"
    using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hassoc: "\<And>x y z. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> z \<in> G \<Longrightarrow> mul (mul x y) z = mul x (mul y z)"
    using hG_grp unfolding top1_is_group_on_def by (by100 blast)
  have hcomm: "\<And>x y. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> mul x y = mul y x"
    using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hD_sub: "?D \<subseteq> G"
    using hG_grp unfolding top1_is_group_on_def by (by5000 blast)
  \<comment> \<open>e \<in> D.\<close>
  have he_G: "e \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
  have "mul e e = e" using hG_grp he_G unfolding top1_is_group_on_def by (by100 blast)
  hence he_D: "e \<in> ?D" using he_G by (by5000 force)
  \<comment> \<open>Closure under mul: (g^2)(h^2) = (gh)^2 in abelian.\<close>
  have hmul_cl: "\<forall>x\<in>?D. \<forall>y\<in>?D. mul x y \<in> ?D"
  proof (intro ballI)
    fix x y assume "x \<in> ?D" "y \<in> ?D"
    then obtain gx gy where hgx: "gx \<in> G" "x = mul gx gx"
        and hgy: "gy \<in> G" "y = mul gy gy" by (by100 blast)
    have hgxgy: "mul gx gy \<in> G" using hG_grp hgx(1) hgy(1) unfolding top1_is_group_on_def by (by100 blast)
    \<comment> \<open>(gx\<cdot>gx)\<cdot>(gy\<cdot>gy) = (gx\<cdot>gy)\<cdot>(gx\<cdot>gy) in abelian group.\<close>
    have "mul x y = mul (mul gx gx) (mul gy gy)" using hgx(2) hgy(2) by (by100 simp)
    also have "\<dots> = mul gx (mul gx (mul gy gy))"
      using hassoc[OF hgx(1) hgx(1)] hG_grp hgy(1) unfolding top1_is_group_on_def by (by5000 blast)
    also have "mul gx (mul gy gy) = mul (mul gx gy) gy"
      using hassoc[OF hgx(1) hgy(1) hgy(1)] by (by100 simp)
    also have "mul gx (mul (mul gx gy) gy) = mul (mul gx (mul gx gy)) gy"
      using hassoc[OF hgx(1) hgxgy hgy(1)] by (by100 simp)
    also have "mul gx (mul gx gy) = mul (mul gx gy) gx"
    proof -
      have "mul gx (mul gx gy) = mul (mul gx gx) gy"
        using hassoc[OF hgx(1) hgx(1) hgy(1)] by (by100 simp)
      also have "\<dots> = mul (mul gx gy) gx"
      proof -
        have "mul gx gx = mul gx gx" by (by100 simp)
        have "mul (mul gx gx) gy = mul gx (mul gx gy)"
          using hassoc[OF hgx(1) hgx(1) hgy(1)] by (by100 simp)
        also have "mul gx gy = mul gy gx" using hcomm[OF hgx(1) hgy(1)] .
        also have "mul gx (mul gy gx) = mul (mul gx gy) gx"
          using hassoc[OF hgx(1) hgy(1) hgx(1)] by (by100 simp)
        finally show ?thesis .
      qed
      finally show ?thesis .
    qed
    also have "mul (mul (mul gx gy) gx) gy = mul (mul gx gy) (mul gx gy)"
      using hassoc[OF hgxgy hgx(1) hgy(1)] by (by100 simp)
    finally show "mul x y \<in> ?D" using hgxgy by (by100 force)
  qed
  \<comment> \<open>Closure under invg: invg(g^2) = (invg g)^2 in abelian.\<close>
  have hinv_cl: "\<forall>x\<in>?D. invg x \<in> ?D"
  proof (intro ballI)
    fix x assume "x \<in> ?D"
    then obtain gx where hgx: "gx \<in> G" "x = mul gx gx" by (by100 blast)
    have higx: "invg gx \<in> G" using hG_grp hgx(1) unfolding top1_is_group_on_def by (by100 blast)
    have higxigx: "mul (invg gx) (invg gx) \<in> G"
      using hG_grp higx unfolding top1_is_group_on_def by (by100 blast)
    \<comment> \<open>(invg gx)^2 \<cdot> gx^2 = ((invg gx)\<cdot>gx)^2 = e^2 = e.\<close>
    have "mul (mul (invg gx) (invg gx)) (mul gx gx) = e"
    proof -
      have "mul (mul (invg gx) (invg gx)) (mul gx gx)
          = mul (mul (invg gx) gx) (mul (invg gx) gx)"
      proof -
        \<comment> \<open>Same rearrangement as in hmul\_cl but with invg(gx) and gx.\<close>
        have ha: "invg gx \<in> G" using higx .
        have hb: "gx \<in> G" using hgx(1) .
        have hab: "mul (invg gx) gx \<in> G" using hG_grp ha hb unfolding top1_is_group_on_def by (by100 blast)
        have "mul (mul (invg gx) (invg gx)) (mul gx gx)
            = mul (invg gx) (mul (invg gx) (mul gx gx))"
          using hassoc[OF ha ha] hG_grp hb unfolding top1_is_group_on_def by (by5000 blast)
        also have "mul (invg gx) (mul gx gx) = mul (mul (invg gx) gx) gx"
          using hassoc[OF ha hb hb] by (by100 simp)
        also have "mul (invg gx) (mul (mul (invg gx) gx) gx) = mul (mul (invg gx) (mul (invg gx) gx)) gx"
          using hassoc[OF ha hab hb] by (by100 simp)
        also have "mul (invg gx) (mul (invg gx) gx) = mul (mul (invg gx) gx) (invg gx)"
        proof -
          have "mul (invg gx) (mul (invg gx) gx) = mul (mul (invg gx) (invg gx)) gx"
            using hassoc[OF ha ha hb] by (by100 simp)
          also have "\<dots> = mul (invg gx) (mul (invg gx) gx)"
            using hassoc[OF ha ha hb] by (by100 simp)
          finally have eq1: "mul (invg gx) (mul (invg gx) gx) = mul (invg gx) (mul (invg gx) gx)" .
          \<comment> \<open>We need a different approach. Use commutativity directly.\<close>
          show ?thesis using hcomm[OF ha hab] by (by100 simp)
        qed
        also have "mul (mul (mul (invg gx) gx) (invg gx)) gx = mul (mul (invg gx) gx) (mul (invg gx) gx)"
          using hassoc[OF hab ha hb] by (by100 simp)
        finally show ?thesis by (by100 simp)
      qed
      also have "mul (invg gx) gx = e"
        using hG_grp hgx(1) unfolding top1_is_group_on_def by (by100 blast)
      also have "mul e e = e" using hG_grp he_G unfolding top1_is_group_on_def by (by100 blast)
      finally show ?thesis .
    qed
    hence "mul (mul (invg gx) (invg gx)) x = e" using hgx(2) by (by100 simp)
    \<comment> \<open>So invg x = (invg gx)^2 (unique left inverse).\<close>
    have hx_G: "x \<in> G" using hD_sub \<open>x \<in> ?D\<close> by (by100 blast)
    have "invg x = mul (invg gx) (invg gx)"
    proof -
      have "mul (invg x) x = e" using hG_grp hx_G unfolding top1_is_group_on_def by (by100 blast)
      have "mul (mul (invg gx) (invg gx)) x = e" using \<open>mul (mul (invg gx) (invg gx)) x = e\<close> .
      \<comment> \<open>Both are left inverses of x, so they are equal.\<close>
      have hinvx_G: "invg x \<in> G" using hG_grp hx_G unfolding top1_is_group_on_def by (by100 blast)
      have "mul (invg x) x = mul (mul (invg gx) (invg gx)) x"
        using \<open>mul (invg x) x = e\<close> \<open>mul (mul (invg gx) (invg gx)) x = e\<close> by (by100 simp)
      \<comment> \<open>Right cancel x.\<close>
      hence "mul (mul (invg x) x) (invg x) = mul (mul (mul (invg gx) (invg gx)) x) (invg x)"
        by (by100 simp)
      have "mul (mul (invg x) x) (invg x) = invg x"
      proof -
        have "mul (invg x) x = e" using \<open>mul (invg x) x = e\<close> .
        thus ?thesis using hG_grp hinvx_G unfolding top1_is_group_on_def by (by100 blast)
      qed
      moreover have "mul (mul (mul (invg gx) (invg gx)) x) (invg x) = mul (invg gx) (invg gx)"
      proof -
        have "mul (mul (mul (invg gx) (invg gx)) x) (invg x)
            = mul (mul (invg gx) (invg gx)) (mul x (invg x))"
          using hassoc[OF higxigx hx_G hinvx_G] by (by100 simp)
        also have "mul x (invg x) = e"
          using hG_grp hx_G unfolding top1_is_group_on_def by (by100 blast)
        also have "mul (mul (invg gx) (invg gx)) e = mul (invg gx) (invg gx)"
          using hG_grp higxigx unfolding top1_is_group_on_def by (by100 blast)
        finally show ?thesis .
      qed
      ultimately have "invg x = mul (invg gx) (invg gx)"
      proof -
        assume h1: "mul (mul (invg x) x) (invg x) = invg x"
        assume h2: "mul (mul (mul (invg gx) (invg gx)) x) (invg x) = mul (invg gx) (invg gx)"
        have "invg x = mul (mul (mul (invg gx) (invg gx)) x) (invg x)"
          using h1 \<open>mul (mul (invg x) x) (invg x) = mul (mul (mul (invg gx) (invg gx)) x) (invg x)\<close>
          by (by100 simp)
        also have "\<dots> = mul (invg gx) (invg gx)" using h2 .
        finally show "invg x = mul (invg gx) (invg gx)" .
      qed
      thus ?thesis by (by100 simp)
    qed
    thus "invg x \<in> ?D" using higx by (by5000 force)
  qed
  \<comment> \<open>Assoc, id, inverse inherited from G.\<close>
  have hD_grp: "top1_is_group_on ?D mul e invg"
    unfolding top1_is_group_on_def
    using hD_sub he_D hmul_cl hinv_cl hG_grp unfolding top1_is_group_on_def by (by5000 blast)
  \<comment> \<open>Conjugation trivial in abelian.\<close>
  have hconj: "\<forall>g\<in>G. \<forall>n\<in>?D. mul (mul g n) (invg g) \<in> ?D"
  proof (intro ballI)
    fix g n assume "g \<in> G" "n \<in> ?D"
    have hn_G: "n \<in> G" using hD_sub \<open>n \<in> ?D\<close> by (by100 blast)
    have hinvg_G: "invg g \<in> G" using hG_grp \<open>g \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
    have "mul (mul g n) (invg g) = mul g (mul n (invg g))"
      using hassoc[OF \<open>g \<in> G\<close> hn_G hinvg_G] by (by100 simp)
    also have "mul n (invg g) = mul (invg g) n" using hcomm[OF hn_G hinvg_G] .
    also have "mul g (mul (invg g) n) = mul (mul g (invg g)) n"
      using hassoc[OF \<open>g \<in> G\<close> hinvg_G hn_G] by (by100 simp)
    also have "mul g (invg g) = e" using hG_grp \<open>g \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
    also have "mul e n = n" using hG_grp hn_G unfolding top1_is_group_on_def by (by100 blast)
    finally show "mul (mul g n) (invg g) \<in> ?D" using \<open>n \<in> ?D\<close> by (by100 simp)
  qed
  show ?thesis unfolding top1_normal_subgroup_on_def using hD_sub hD_grp hconj by (by100 blast)
qed


text \<open>In an abelian group G with coordinate projection \<epsilon>: G \<rightarrow> Z (\<epsilon>(a) = 1),
  the quotient G/2G has twice as many cosets as K/2K where K = ker(\<epsilon>).
  This follows the book proof of Theorem 67.8: the short exact sequence
  0 \<rightarrow> K \<rightarrow> G \<rightarrow>^\<epsilon> Z \<rightarrow> 0 splits, giving G \<cong> K \<times> Z, hence G/2G \<cong> K/2K \<times> Z/2Z.\<close>
lemma quotient_double_by_kernel:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and \<epsilon> :: "'g \<Rightarrow> int" and a :: 'g
  assumes hG: "top1_is_abelian_group_on G mul e invg"
      and heps: "top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>"
      and ha: "a \<in> G" and heps_a: "\<epsilon> a = 1"
      and hK_free: "top1_is_free_abelian_group_full_on {g \<in> G. \<epsilon> g = 0} mul e invg iota' S'"
      and hQK_fin: "finite (top1_quotient_group_carrier_on
            {g \<in> G. \<epsilon> g = 0} mul {mul g g | g. g \<in> {g \<in> G. \<epsilon> g = 0}})"
  shows "card (top1_quotient_group_carrier_on G mul {mul g g | g. g \<in> G})
       = 2 * card (top1_quotient_group_carrier_on
            {g \<in> G. \<epsilon> g = 0} mul {mul g g | g. g \<in> {g \<in> G. \<epsilon> g = 0}})"
proof -
  let ?K = "{g \<in> G. \<epsilon> g = 0}"
  let ?twoG = "{mul g g | g. g \<in> G}"
  let ?twoK = "{mul g g | g. g \<in> ?K}"
  let ?QG = "top1_quotient_group_carrier_on G mul ?twoG"
  let ?QK = "top1_quotient_group_carrier_on ?K mul ?twoK"
  have hG_grp: "top1_is_group_on G mul e invg"
    using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hZ_grp: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
    unfolding top1_is_group_on_def by (by100 auto)
  \<comment> \<open>Define the even and odd coset sets via define (not let) to avoid expansion issues.\<close>
  define QG_even where "QG_even = {C \<in> ?QG. \<exists>g\<in>C. even (\<epsilon> g)}"
  define QG_odd where "QG_odd = {C \<in> ?QG. \<exists>g\<in>C. odd (\<epsilon> g)}"
  \<comment> \<open>Key facts about \<epsilon> on cosets: \<epsilon> is constant mod 2 on each coset.\<close>
  \<comment> \<open>Since 2G \<subseteq> ker(\<epsilon> mod 2), elements in the same coset have the same \<epsilon> parity.\<close>
  have heps_coset: "\<And>g h. g \<in> G \<Longrightarrow> h \<in> ?twoG \<Longrightarrow> even (\<epsilon> g) = even (\<epsilon> (mul g h))"
  proof -
    fix g h assume hg: "g \<in> G" and hh: "h \<in> ?twoG"
    from hh obtain h' where "h' \<in> G" "h = mul h' h'" by (by100 blast)
    have "h \<in> G" using hG_grp \<open>h' \<in> G\<close> \<open>h = mul h' h'\<close> unfolding top1_is_group_on_def by (by100 blast)
    have "\<epsilon> (mul g h) = \<epsilon> g + \<epsilon> h"
      using heps hg \<open>h \<in> G\<close> unfolding top1_group_hom_on_def by (by100 blast)
    moreover have "\<epsilon> h = \<epsilon> h' + \<epsilon> h'"
    proof -
      have "\<epsilon> (mul h' h') = \<epsilon> h' + \<epsilon> h'"
        using heps \<open>h' \<in> G\<close> unfolding top1_group_hom_on_def by (by100 blast)
      thus ?thesis using \<open>h = mul h' h'\<close> by (by100 simp)
    qed
    ultimately show "even (\<epsilon> g) = even (\<epsilon> (mul g h))" by (by100 simp)
  qed
  \<comment> \<open>Partition: every QG coset is even or odd (not both).\<close>
  \<comment> \<open>card QG = card QG\_even + card QG\_odd.\<close>
  \<comment> \<open>card QG\_even = card QK (K-cosets embed into even G-cosets).\<close>
  \<comment> \<open>card QG\_odd = card QG\_even (shift by a).\<close>
  \<comment> \<open>Step 1: Partition QG = QG\_even \<union> QG\_odd, disjoint.\<close>
  have hpartition: "?QG = QG_even \<union> QG_odd"
  proof (rule set_eqI, rule iffI)
    fix C assume "C \<in> ?QG"
    then obtain g0 where hg0: "g0 \<in> G" "C = top1_group_coset_on G mul ?twoG g0"
      unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    have "g0 \<in> C"
    proof -
      have "e \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      have "mul e e = e" using hG_grp \<open>e \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
      hence "e \<in> ?twoG" using \<open>e \<in> G\<close> by (by5000 force)
      have "mul g0 e = g0" using hG_grp hg0(1) unfolding top1_is_group_on_def by (by100 blast)
      thus ?thesis using hg0(2) \<open>e \<in> ?twoG\<close>
        unfolding top1_group_coset_on_def by (by5000 force)
    qed
    show "C \<in> QG_even \<union> QG_odd"
    proof (cases "even (\<epsilon> g0)")
      case True thus ?thesis using \<open>C \<in> ?QG\<close> \<open>g0 \<in> C\<close>
        unfolding QG_even_def by (by100 blast)
    next
      case False thus ?thesis using \<open>C \<in> ?QG\<close> \<open>g0 \<in> C\<close>
        unfolding QG_odd_def by (by100 blast)
    qed
  next
    fix C assume "C \<in> QG_even \<union> QG_odd"
    thus "C \<in> ?QG" unfolding QG_even_def QG_odd_def by (by100 blast)
  qed
  have hdisjoint: "QG_even \<inter> QG_odd = {}"
  proof (rule ccontr)
    assume "QG_even \<inter> QG_odd \<noteq> {}"
    then obtain C where hC_ev: "C \<in> QG_even" and hC_od: "C \<in> QG_odd" by (by100 blast)
    from hC_ev obtain g1 where hg1: "g1 \<in> C" "even (\<epsilon> g1)"
      unfolding QG_even_def by (by100 blast)
    from hC_od obtain g2 where hg2: "g2 \<in> C" "odd (\<epsilon> g2)"
      unfolding QG_odd_def by (by100 blast)
    \<comment> \<open>g1, g2 in same coset C \<Longrightarrow> \<epsilon>(g1) \<equiv> \<epsilon>(g2) mod 2. Contradiction.\<close>
    have "C \<in> ?QG" using hC_ev unfolding QG_even_def by (by100 blast)
    then obtain g0 where hg0: "g0 \<in> G" "C = top1_group_coset_on G mul ?twoG g0"
      unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    from hg1(1) hg0(2) obtain h1 where "h1 \<in> ?twoG" "g1 = mul g0 h1"
      unfolding top1_group_coset_on_def by (by100 blast)
    from hg2(1) hg0(2) obtain h2 where "h2 \<in> ?twoG" "g2 = mul g0 h2"
      unfolding top1_group_coset_on_def by (by100 blast)
    have "even (\<epsilon> g0) = even (\<epsilon> g1)"
      using heps_coset[OF hg0(1) \<open>h1 \<in> ?twoG\<close>] \<open>g1 = mul g0 h1\<close> by (by100 simp)
    moreover have "even (\<epsilon> g0) = even (\<epsilon> g2)"
      using heps_coset[OF hg0(1) \<open>h2 \<in> ?twoG\<close>] \<open>g2 = mul g0 h2\<close> by (by100 simp)
    ultimately have "even (\<epsilon> g1) = even (\<epsilon> g2)" by (by100 simp)
    thus False using hg1(2) hg2(2) by (by100 simp)
  qed
  \<comment> \<open>Steps 2-4: card QG\_even = card QK, card QG\_odd = card QG\_even.\<close>
  \<comment> \<open>Step 2: |QG\_even| = |QK|. The inclusion K \<hookrightarrow> G maps K-cosets to even G-cosets.\<close>
  \<comment> \<open>Step 3: |QG\_odd| = |QG\_even|. Multiplication by [a] shifts even \<leftrightarrow> odd.\<close>
  \<comment> \<open>Key algebraic fact: K \<inter> 2G = 2K.\<close>
  have hK_grp: "top1_is_group_on ?K mul e invg"
    using hK_free unfolding top1_is_free_abelian_group_full_on_def
      top1_is_abelian_group_on_def by (by100 blast)
  have hK_cap_2G: "?K \<inter> ?twoG = ?twoK"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> ?K \<inter> ?twoG"
    hence hx_K: "x \<in> ?K" and hx_2G: "x \<in> ?twoG" by (by100 auto)+
    from hx_2G obtain g where hg: "g \<in> G" "x = mul g g" by (by100 blast)
    have "\<epsilon> (mul g g) = \<epsilon> g + \<epsilon> g"
      using heps hg(1) unfolding top1_group_hom_on_def by (by100 blast)
    hence "\<epsilon> x = \<epsilon> g + \<epsilon> g" using hg(2) by (by100 simp)
    moreover have "\<epsilon> x = 0" using hx_K by (by100 simp)
    ultimately have "\<epsilon> g = 0" by (by100 linarith)
    hence "g \<in> ?K" using hg(1) by (by100 simp)
    thus "x \<in> ?twoK" using hg by (by100 blast)
  next
    fix x assume "x \<in> ?twoK"
    then obtain k where "k \<in> ?K" "x = mul k k" by (by100 blast)
    have "k \<in> G" using \<open>k \<in> ?K\<close> by (by100 blast)
    have "x \<in> ?twoG" using \<open>k \<in> G\<close> \<open>x = mul k k\<close> by (by100 blast)
    moreover have "mul k k \<in> ?K"
      using hK_grp \<open>k \<in> ?K\<close> unfolding top1_is_group_on_def by (by100 blast)
    hence "x \<in> ?K" using \<open>x = mul k k\<close> by (by100 simp)
    ultimately show "x \<in> ?K \<inter> ?twoG" by (by100 blast)
  qed
  \<comment> \<open>2G is normal in G (abelian \<Rightarrow> all subgroups normal).\<close>
  have h2G_normal: "top1_normal_subgroup_on G mul e invg ?twoG"
    by (rule abelian_doubles_normal[OF hG])
  have h2G_sub: "?twoG \<subseteq> G"
    using h2G_normal unfolding top1_normal_subgroup_on_def by (by100 blast)
  have h2G_grp: "top1_is_group_on ?twoG mul e invg"
    using h2G_normal unfolding top1_normal_subgroup_on_def by (by100 blast)
  have hK_abel: "top1_is_abelian_group_on ?K mul e invg"
    using hK_free unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  have h2K_normal: "top1_normal_subgroup_on ?K mul e invg ?twoK"
    by (rule abelian_doubles_normal[OF hK_abel])
  \<comment> \<open>Step 2: |QG\_even| = |QK|.\<close>
  \<comment> \<open>Bijection \<psi>: QK \<rightarrow> QG\_even sending coset\_K(k) \<mapsto> coset\_G(k).
     Well-defined: K \<inter> 2G = 2K ensures k1 \<equiv> k2 mod 2K \<Longrightarrow> k1 \<equiv> k2 mod 2G.
     Injective: k1 \<equiv> k2 mod 2G and k1,k2 \<in> K \<Longrightarrow> k1-k2 \<in> K \<inter> 2G = 2K.
     Surjective: every even coset has a K-representative (projection via pow(a, \<epsilon>(g))).\<close>
  have heven_card: "card QG_even = card ?QK"
  proof -
    define \<psi> where "\<psi> CK = top1_group_coset_on G mul ?twoG (SOME k. k \<in> CK)" for CK
    have hpsi_bij: "bij_betw \<psi> ?QK QG_even"
      unfolding bij_betw_def
    proof (rule conjI)
      \<comment> \<open>Injectivity: different K-cosets give different G-cosets.\<close>
      show "inj_on \<psi> ?QK"
      proof (rule inj_onI)
        fix CK1 CK2 assume hCK1: "CK1 \<in> ?QK" and hCK2: "CK2 \<in> ?QK"
            and heq: "\<psi> CK1 = \<psi> CK2"
        \<comment> \<open>Get representatives.\<close>
        let ?k1 = "SOME k. k \<in> CK1" and ?k2 = "SOME k. k \<in> CK2"
        \<comment> \<open>Representatives are in their cosets and in K.\<close>
        \<comment> \<open>Representatives are in their cosets.\<close>
        have hk1_CK1: "?k1 \<in> CK1"
        proof (rule someI_ex)
          from hCK1 obtain k0 where "k0 \<in> ?K" "CK1 = top1_group_coset_on ?K mul ?twoK k0"
            unfolding top1_quotient_group_carrier_on_def by (by100 blast)
          have "e \<in> ?K" using hK_grp unfolding top1_is_group_on_def by (by100 blast)
          have "mul e e = e" using hK_grp \<open>e \<in> ?K\<close> unfolding top1_is_group_on_def by (by100 blast)
          hence "e \<in> ?twoK" using \<open>e \<in> ?K\<close> by (by5000 force)
          have "mul k0 e = k0" using hK_grp \<open>k0 \<in> ?K\<close> unfolding top1_is_group_on_def by (by100 blast)
          hence "k0 \<in> CK1" using \<open>CK1 = _\<close> \<open>e \<in> ?twoK\<close>
            unfolding top1_group_coset_on_def by (by5000 force)
          thus "\<exists>k. k \<in> CK1" by (by100 blast)
        qed
        have hk2_CK2: "?k2 \<in> CK2"
        proof (rule someI_ex)
          from hCK2 obtain k0 where "k0 \<in> ?K" "CK2 = top1_group_coset_on ?K mul ?twoK k0"
            unfolding top1_quotient_group_carrier_on_def by (by100 blast)
          have "e \<in> ?K" using hK_grp unfolding top1_is_group_on_def by (by100 blast)
          have "mul e e = e" using hK_grp \<open>e \<in> ?K\<close> unfolding top1_is_group_on_def by (by100 blast)
          hence "e \<in> ?twoK" using \<open>e \<in> ?K\<close> by (by5000 force)
          have "mul k0 e = k0" using hK_grp \<open>k0 \<in> ?K\<close> unfolding top1_is_group_on_def by (by100 blast)
          hence "k0 \<in> CK2" using \<open>CK2 = _\<close> \<open>e \<in> ?twoK\<close>
            unfolding top1_group_coset_on_def by (by5000 force)
          thus "\<exists>k. k \<in> CK2" by (by100 blast)
        qed
        \<comment> \<open>Representatives are in K.\<close>
        have hk1_K: "?k1 \<in> ?K"
        proof -
          from hCK1 obtain k0 where "k0 \<in> ?K" "CK1 = top1_group_coset_on ?K mul ?twoK k0"
            unfolding top1_quotient_group_carrier_on_def by (by100 blast)
          from hk1_CK1 \<open>CK1 = _\<close> obtain h where "h \<in> ?twoK" "?k1 = mul k0 h"
            unfolding top1_group_coset_on_def by (by100 blast)
          from \<open>h \<in> ?twoK\<close> obtain h' where "h' \<in> ?K" "h = mul h' h'" by (by100 blast)
          have "h \<in> ?K" using hK_grp \<open>h' \<in> ?K\<close> \<open>h = mul h' h'\<close>
            unfolding top1_is_group_on_def by (by100 blast)
          have "mul k0 h \<in> ?K" using hK_grp \<open>k0 \<in> ?K\<close> \<open>h \<in> ?K\<close>
            unfolding top1_is_group_on_def by (by100 blast)
          thus ?thesis using \<open>?k1 = mul k0 h\<close> by (by100 simp)
        qed
        have hk2_K: "?k2 \<in> ?K"
        proof -
          from hCK2 obtain k0 where "k0 \<in> ?K" "CK2 = top1_group_coset_on ?K mul ?twoK k0"
            unfolding top1_quotient_group_carrier_on_def by (by100 blast)
          from hk2_CK2 \<open>CK2 = _\<close> obtain h where "h \<in> ?twoK" "?k2 = mul k0 h"
            unfolding top1_group_coset_on_def by (by100 blast)
          from \<open>h \<in> ?twoK\<close> obtain h' where "h' \<in> ?K" "h = mul h' h'" by (by100 blast)
          have "h \<in> ?K" using hK_grp \<open>h' \<in> ?K\<close> \<open>h = mul h' h'\<close>
            unfolding top1_is_group_on_def by (by100 blast)
          have "mul k0 h \<in> ?K" using hK_grp \<open>k0 \<in> ?K\<close> \<open>h \<in> ?K\<close>
            unfolding top1_is_group_on_def by (by100 blast)
          thus ?thesis using \<open>?k2 = mul k0 h\<close> by (by100 simp)
        qed
        \<comment> \<open>coset\_G(k1) = coset\_G(k2) \<Longrightarrow> mul(invg k1) k2 \<in> 2G \<inter> K = 2K.\<close>
        have "mul (invg ?k1) ?k2 \<in> ?twoK"
        proof -
          have hk1_G: "?k1 \<in> G" using hk1_K by (by100 blast)
          have hk2_G: "?k2 \<in> G" using hk2_K by (by100 blast)
          \<comment> \<open>From heq: coset\_G(k1) = coset\_G(k2).\<close>
          have "top1_group_coset_on G mul ?twoG ?k1 = top1_group_coset_on G mul ?twoG ?k2"
            using heq unfolding \<psi>_def by (by100 simp)
          \<comment> \<open>By normal\_coset\_eq: mul(invg k1) k2 \<in> 2G.\<close>
          hence "mul (invg ?k1) ?k2 \<in> ?twoG"
            using normal_coset_eq[OF hG_grp h2G_normal hk1_G hk2_G] by (by100 simp)
          \<comment> \<open>Also mul(invg k1) k2 \<in> K (K closed under mul, invg).\<close>
          moreover have "mul (invg ?k1) ?k2 \<in> ?K"
          proof -
            have "invg ?k1 \<in> ?K" using hK_grp hk1_K unfolding top1_is_group_on_def by (by100 blast)
            thus ?thesis using hK_grp \<open>invg ?k1 \<in> ?K\<close> hk2_K
              unfolding top1_is_group_on_def by (by100 blast)
          qed
          \<comment> \<open>By K \<inter> 2G = 2K.\<close>
          ultimately show ?thesis using hK_cap_2G by (by100 blast)
        qed
        \<comment> \<open>By normal\_coset\_eq for K: coset\_K(k1) = coset\_K(k2).\<close>
        hence hK_coset_eq: "top1_group_coset_on ?K mul ?twoK ?k1 = top1_group_coset_on ?K mul ?twoK ?k2"
          using normal_coset_eq[OF hK_grp h2K_normal hk1_K hk2_K] by (by100 simp)
        \<comment> \<open>k1 \<in> CK1 which equals coset\_K(k1), and k2 \<in> CK2 = coset\_K(k2).
           Since coset\_K(k1) = coset\_K(k2), CK1 = CK2.\<close>
        show "CK1 = CK2"
        proof -
          \<comment> \<open>CK1 = coset\_K(k1): since k1 \<in> CK1 \<in> QK, CK1 is the K-coset of k1.\<close>
          from hCK1 obtain k01 where "k01 \<in> ?K" "CK1 = top1_group_coset_on ?K mul ?twoK k01"
            unfolding top1_quotient_group_carrier_on_def by (by100 blast)
          have "?k1 \<in> top1_group_coset_on ?K mul ?twoK k01"
            using hk1_CK1 \<open>CK1 = _\<close> by (by100 simp)
          \<comment> \<open>k1 = mul k01 h for some h \<in> 2K, so coset(k01) = coset(k1).\<close>
          then obtain h1 where "h1 \<in> ?twoK" "?k1 = mul k01 h1"
            unfolding top1_group_coset_on_def by (by100 blast)
          have "mul (invg k01) ?k1 = h1"
          proof -
            have hassoc: "\<forall>a\<in>?K. \<forall>b\<in>?K. \<forall>c\<in>?K. mul (mul a b) c = mul a (mul b c)"
              using hK_grp unfolding top1_is_group_on_def by (by100 blast)
            have "invg k01 \<in> ?K" using hK_grp \<open>k01 \<in> ?K\<close> unfolding top1_is_group_on_def by (by100 blast)
            have "h1 \<in> ?K"
            proof -
              from \<open>h1 \<in> ?twoK\<close> obtain h' where "h' \<in> ?K" "h1 = mul h' h'" by (by100 blast)
              thus ?thesis using hK_grp unfolding top1_is_group_on_def by (by100 blast)
            qed
            have "mul (invg k01) ?k1 = mul (invg k01) (mul k01 h1)"
              using \<open>?k1 = mul k01 h1\<close> by (by100 simp)
            also have "\<dots> = mul (mul (invg k01) k01) h1"
              using hassoc[rule_format, OF \<open>invg k01 \<in> ?K\<close> \<open>k01 \<in> ?K\<close> \<open>h1 \<in> ?K\<close>] by (by100 simp)
            also have "mul (invg k01) k01 = e"
              using hK_grp \<open>k01 \<in> ?K\<close> unfolding top1_is_group_on_def by (by100 blast)
            also have "mul e h1 = h1"
              using hK_grp \<open>h1 \<in> ?K\<close> unfolding top1_is_group_on_def by (by100 blast)
            finally show ?thesis .
          qed
          hence "mul (invg k01) ?k1 \<in> ?twoK" using \<open>h1 \<in> ?twoK\<close> by (by100 simp)
          hence "top1_group_coset_on ?K mul ?twoK k01 = top1_group_coset_on ?K mul ?twoK ?k1"
            using normal_coset_eq[OF hK_grp h2K_normal \<open>k01 \<in> ?K\<close> hk1_K] by (by100 simp)
          hence hCK1_eq: "CK1 = top1_group_coset_on ?K mul ?twoK ?k1"
            using \<open>CK1 = _\<close> by (by100 simp)
          \<comment> \<open>Similarly CK2 = coset\_K(k2).\<close>
          from hCK2 obtain k02 where "k02 \<in> ?K" "CK2 = top1_group_coset_on ?K mul ?twoK k02"
            unfolding top1_quotient_group_carrier_on_def by (by100 blast)
          have "?k2 \<in> top1_group_coset_on ?K mul ?twoK k02"
            using hk2_CK2 \<open>CK2 = _\<close> by (by100 simp)
          then obtain h2 where "h2 \<in> ?twoK" "?k2 = mul k02 h2"
            unfolding top1_group_coset_on_def by (by100 blast)
          have "mul (invg k02) ?k2 = h2"
          proof -
            have hassoc2: "\<forall>a\<in>?K. \<forall>b\<in>?K. \<forall>c\<in>?K. mul (mul a b) c = mul a (mul b c)"
              using hK_grp unfolding top1_is_group_on_def by (by100 blast)
            have "invg k02 \<in> ?K" using hK_grp \<open>k02 \<in> ?K\<close> unfolding top1_is_group_on_def by (by100 blast)
            have "h2 \<in> ?K"
            proof -
              from \<open>h2 \<in> ?twoK\<close> obtain h' where "h' \<in> ?K" "h2 = mul h' h'" by (by100 blast)
              thus ?thesis using hK_grp unfolding top1_is_group_on_def by (by100 blast)
            qed
            have "mul (invg k02) ?k2 = mul (invg k02) (mul k02 h2)"
              using \<open>?k2 = mul k02 h2\<close> by (by100 simp)
            also have "\<dots> = mul (mul (invg k02) k02) h2"
              using hassoc2[rule_format, OF \<open>invg k02 \<in> ?K\<close> \<open>k02 \<in> ?K\<close> \<open>h2 \<in> ?K\<close>] by (by100 simp)
            also have "mul (invg k02) k02 = e"
              using hK_grp \<open>k02 \<in> ?K\<close> unfolding top1_is_group_on_def by (by100 blast)
            also have "mul e h2 = h2"
              using hK_grp \<open>h2 \<in> ?K\<close> unfolding top1_is_group_on_def by (by100 blast)
            finally show ?thesis .
          qed
          hence "mul (invg k02) ?k2 \<in> ?twoK" using \<open>h2 \<in> ?twoK\<close> by (by100 simp)
          hence "top1_group_coset_on ?K mul ?twoK k02 = top1_group_coset_on ?K mul ?twoK ?k2"
            using normal_coset_eq[OF hK_grp h2K_normal \<open>k02 \<in> ?K\<close> hk2_K] by (by100 simp)
          hence hCK2_eq: "CK2 = top1_group_coset_on ?K mul ?twoK ?k2"
            using \<open>CK2 = _\<close> by (by100 simp)
          show ?thesis using hCK1_eq hCK2_eq hK_coset_eq by (by100 simp)
        qed
      qed
    next
      \<comment> \<open>Image = QG\_even.\<close>
      show "\<psi> ` ?QK = QG_even"
      proof (rule set_eqI, rule iffI)
        \<comment> \<open>\<subseteq>: k \<in> K has \<epsilon>(k)=0 (even), so coset\_G(k) \<in> QG\_even.\<close>
        fix C assume "C \<in> \<psi> ` ?QK"
        then obtain CK where "CK \<in> ?QK" "C = \<psi> CK" by (by100 blast)
        let ?k = "SOME k. k \<in> CK"
        have hk_CK: "?k \<in> CK"
        proof (rule someI_ex)
          from \<open>CK \<in> ?QK\<close> obtain k0 where "k0 \<in> ?K" "CK = top1_group_coset_on ?K mul ?twoK k0"
            unfolding top1_quotient_group_carrier_on_def by (by100 blast)
          have "e \<in> ?K" using hK_grp unfolding top1_is_group_on_def by (by100 blast)
          have "mul e e = e" using hK_grp \<open>e \<in> ?K\<close> unfolding top1_is_group_on_def by (by100 blast)
          hence "e \<in> ?twoK" using \<open>e \<in> ?K\<close> by (by5000 force)
          have "mul k0 e = k0" using hK_grp \<open>k0 \<in> ?K\<close> unfolding top1_is_group_on_def by (by100 blast)
          hence "k0 \<in> CK" using \<open>CK = _\<close> \<open>e \<in> ?twoK\<close>
            unfolding top1_group_coset_on_def by (by5000 force)
          thus "\<exists>k. k \<in> CK" by (by100 blast)
        qed
        have hk_K: "?k \<in> ?K"
        proof -
          from \<open>CK \<in> ?QK\<close> obtain k0 where "k0 \<in> ?K" "CK = top1_group_coset_on ?K mul ?twoK k0"
            unfolding top1_quotient_group_carrier_on_def by (by100 blast)
          from hk_CK \<open>CK = _\<close> obtain h where "h \<in> ?twoK" "?k = mul k0 h"
            unfolding top1_group_coset_on_def by (by100 blast)
          from \<open>h \<in> ?twoK\<close> obtain h' where "h' \<in> ?K" "h = mul h' h'" by (by100 blast)
          have "h \<in> ?K" using hK_grp \<open>h' \<in> ?K\<close> \<open>h = mul h' h'\<close>
            unfolding top1_is_group_on_def by (by100 blast)
          have "mul k0 h \<in> ?K" using hK_grp \<open>k0 \<in> ?K\<close> \<open>h \<in> ?K\<close>
            unfolding top1_is_group_on_def by (by100 blast)
          thus ?thesis using \<open>?k = mul k0 h\<close> by (by100 simp)
        qed
        have "C = top1_group_coset_on G mul ?twoG ?k"
          using \<open>C = \<psi> CK\<close> unfolding \<psi>_def by (by100 simp)
        moreover have "C \<in> ?QG"
        proof -
          have "?k \<in> G" using hk_K by (by100 blast)
          hence "top1_group_coset_on G mul ?twoG ?k \<in> ?QG"
            unfolding top1_quotient_group_carrier_on_def by (by100 blast)
          thus ?thesis using \<open>C = top1_group_coset_on G mul ?twoG ?k\<close> by (by100 simp)
        qed
        moreover have "\<exists>g\<in>C. even (\<epsilon> g)"
        proof -
          have "?k \<in> C"
          proof -
            have "?k \<in> G" using hk_K by (by100 blast)
            have "?k \<in> top1_group_coset_on G mul ?twoG ?k"
              by (rule coset_self_mem[OF hG_grp h2G_sub h2G_grp \<open>?k \<in> G\<close>])
            thus ?thesis using \<open>C = top1_group_coset_on G mul ?twoG ?k\<close> by (by100 simp)
          qed
          moreover have "even (\<epsilon> ?k)" using hk_K by (by100 simp)
          ultimately show ?thesis by (by100 blast)
        qed
        ultimately show "C \<in> QG_even" unfolding QG_even_def by (by100 blast)
      next
        \<comment> \<open>\<supseteq>: every even coset has a K-representative.\<close>
        fix C assume "C \<in> QG_even"
        hence hC_QG: "C \<in> ?QG" and hC_even: "\<exists>g\<in>C. even (\<epsilon> g)"
          unfolding QG_even_def by (by100 auto)+
        \<comment> \<open>Get representative g0 with even \<epsilon>.\<close>
        from hC_QG obtain g0 where hg0: "g0 \<in> G" "C = top1_group_coset_on G mul ?twoG g0"
          unfolding top1_quotient_group_carrier_on_def by (by100 blast)
        \<comment> \<open>g0 has even \<epsilon> (from C being even and \<epsilon>-coset parity).\<close>
        have "even (\<epsilon> g0)"
        proof -
          from hC_even obtain g1 where "g1 \<in> C" "even (\<epsilon> g1)" by (by100 blast)
          from \<open>g1 \<in> C\<close> hg0(2) obtain h where "h \<in> ?twoG" "g1 = mul g0 h"
            unfolding top1_group_coset_on_def by (by100 blast)
          have "even (\<epsilon> g0) = even (\<epsilon> g1)"
            using heps_coset[OF hg0(1) \<open>h \<in> ?twoG\<close>] \<open>g1 = mul g0 h\<close> by (by100 simp)
          thus ?thesis using \<open>even (\<epsilon> g1)\<close> by (by100 simp)
        qed
        \<comment> \<open>Project: k = g0 \<cdot> invg(a^{\<epsilon>(g0)}) where a^{\<epsilon>(g0)} \<in> 2G.\<close>
        \<comment> \<open>Then k \<in> K and coset\_G(k) = coset\_G(g0) = C.\<close>
        \<comment> \<open>Projection: k = g0 \<cdot> invg(pow(a, |\<epsilon>(g0)|)) \<in> K, coset\_G(k) = C.\<close>
        obtain m :: nat where hm: "\<epsilon> g0 = 2 * int m \<or> \<epsilon> g0 = -(2 * int m)"
        proof -
          from \<open>even (\<epsilon> g0)\<close> obtain k :: int where hk: "(\<epsilon> g0) = 2 * k" by (by100 auto)
          show ?thesis
          proof (cases "k \<ge> 0")
            case True
            have "\<epsilon> g0 = 2 * int (nat k)" using hk True by (by100 simp)
            thus ?thesis using that by (by100 blast)
          next
            case False
            have "\<epsilon> g0 = -(2 * int (nat (-k)))" using hk False by (by100 simp)
            thus ?thesis using that by (by100 blast)
          qed
        qed
        define pow_a where "pow_a = (if \<epsilon> g0 \<ge> 0
            then top1_group_pow mul e a (nat (\<epsilon> g0))
            else top1_group_pow mul e (invg a) (nat (- \<epsilon> g0)))"
        have hpow_G: "pow_a \<in> G"
          unfolding pow_a_def using group_pow_in_group'[OF hG_grp ha]
            group_pow_in_group'[OF hG_grp] hG_grp ha unfolding top1_is_group_on_def
          by (by5000 auto)
        have hpow_2G: "pow_a \<in> ?twoG"
        proof -
          have hia_G: "invg a \<in> G" using hG_grp ha unfolding top1_is_group_on_def by (by100 blast)
          from hm show ?thesis
          proof (elim disjE)
            assume hpos: "\<epsilon> g0 = 2 * int m"
            have hnat_pos: "nat (\<epsilon> g0) = 2 * m" using hpos by (by100 simp)
            hence "pow_a = top1_group_pow mul e a (2 * m)"
              unfolding pow_a_def using hpos by (by100 simp)
            moreover have "top1_group_pow mul e a (2 * m)
                = mul (top1_group_pow mul e a m) (top1_group_pow mul e a m)"
            proof -
              have "m + m = 2 * m" by (by100 simp)
              thus ?thesis using group_pow_add[OF hG_grp ha, of m m] by (by5000 metis)
            qed
            moreover have "top1_group_pow mul e a m \<in> G"
              by (rule group_pow_in_group'[OF hG_grp ha])
            ultimately show ?thesis by (by100 force)
          next
            assume hneg: "\<epsilon> g0 = -(2 * int m)"
            have hnat_neg: "nat (- \<epsilon> g0) = 2 * m" using hneg by (by100 simp)
            hence "pow_a = top1_group_pow mul e (invg a) (2 * m)"
              unfolding pow_a_def using hneg by (by100 simp)
            moreover have "top1_group_pow mul e (invg a) (2 * m)
                = mul (top1_group_pow mul e (invg a) m) (top1_group_pow mul e (invg a) m)"
            proof -
              have "m + m = 2 * m" by (by100 simp)
              thus ?thesis using group_pow_add[OF hG_grp hia_G, of m m] by (by5000 metis)
            qed
            moreover have "top1_group_pow mul e (invg a) m \<in> G"
              by (rule group_pow_in_group'[OF hG_grp hia_G])
            ultimately show ?thesis by (by100 force)
          qed
        qed
        \<comment> \<open>\<epsilon>(pow\_a) = \<epsilon>(g0).\<close>
        have heps_pow: "\<epsilon> pow_a = \<epsilon> g0"
        proof -
          have hia_G: "invg a \<in> G" using hG_grp ha unfolding top1_is_group_on_def by (by100 blast)
          from hm show ?thesis
          proof (elim disjE)
            assume hpos: "\<epsilon> g0 = 2 * int m"
            hence "pow_a = top1_group_pow mul e a (nat (\<epsilon> g0))"
              unfolding pow_a_def by (by100 simp)
            hence "\<epsilon> pow_a = top1_group_pow (+) (0::int) (\<epsilon> a) (nat (\<epsilon> g0))"
              using hom_group_pow_early[OF hG_grp hZ_grp heps ha] by (by100 simp)
            also have "\<dots> = top1_group_pow (+) (0::int) 1 (nat (\<epsilon> g0))"
              using heps_a by (by100 simp)
            also have "\<dots> = int (nat (\<epsilon> g0))"
            proof -
              define mm where "mm = nat (\<epsilon> g0)"
              have "top1_group_pow (+) (0::int) 1 mm = int mm" by (induction mm, by100 simp, by100 simp)
              thus ?thesis unfolding mm_def by (by100 simp)
            qed
            also have "\<dots> = \<epsilon> g0" using hpos by (by100 simp)
            finally show ?thesis .
          next
            assume hneg: "\<epsilon> g0 = -(2 * int m)"
            hence "pow_a = top1_group_pow mul e (invg a) (nat (- \<epsilon> g0))"
              unfolding pow_a_def by (by100 simp)
            hence "\<epsilon> pow_a = top1_group_pow (+) (0::int) (\<epsilon> (invg a)) (nat (- \<epsilon> g0))"
              using hom_group_pow_early[OF hG_grp hZ_grp heps hia_G] by (by100 simp)
            also have "\<epsilon> (invg a) = -1"
              using hom_preserves_inv[OF hG_grp hZ_grp heps ha] heps_a by (by100 simp)
            hence "top1_group_pow (+) (0::int) (\<epsilon> (invg a)) (nat (- \<epsilon> g0))
                = top1_group_pow (+) (0::int) (-1) (nat (- \<epsilon> g0))"
              by (by100 simp)
            also have "\<dots> = - int (nat (- \<epsilon> g0))"
            proof -
              define mm where "mm = nat (- \<epsilon> g0)"
              have "top1_group_pow (+) (0::int) (-1) mm = - int mm" by (induction mm, by100 simp, by100 simp)
              thus ?thesis unfolding mm_def by (by100 simp)
            qed
            also have "\<dots> = \<epsilon> g0" using hneg by (by100 simp)
            finally show ?thesis .
          qed
        qed
        \<comment> \<open>k = g0 \<cdot> invg(pow\_a) \<in> K.\<close>
        define k where "k = mul g0 (invg pow_a)"
        have hk_G: "k \<in> G"
          using hG_grp hg0(1) hpow_G unfolding k_def top1_is_group_on_def by (by100 blast)
        have "\<epsilon> k = 0"
        proof -
          have "\<epsilon> (invg pow_a) = - \<epsilon> pow_a"
            using hom_preserves_inv[OF hG_grp hZ_grp heps hpow_G] by (by100 simp)
          have hinv_pa_G: "invg pow_a \<in> G"
            using hG_grp hpow_G unfolding top1_is_group_on_def by (by100 blast)
          have "k = mul g0 (invg pow_a)" unfolding k_def by (by100 simp)
          hence "\<epsilon> k = \<epsilon> (mul g0 (invg pow_a))" by (by100 simp)
          also have "\<dots> = \<epsilon> g0 + \<epsilon> (invg pow_a)"
            using heps hg0(1) hinv_pa_G unfolding top1_group_hom_on_def by (by100 blast)
          finally have "\<epsilon> k = \<epsilon> g0 + \<epsilon> (invg pow_a)" .
          thus ?thesis using \<open>\<epsilon> (invg pow_a) = - \<epsilon> pow_a\<close> heps_pow by (by100 linarith)
        qed
        hence hk_K: "k \<in> ?K" using hk_G by (by100 simp)
        \<comment> \<open>coset\_G(g0) = coset\_G(k) since g0 = mul k pow\_a and pow\_a \<in> 2G.\<close>
        have hcoset_eq: "C = top1_group_coset_on G mul ?twoG k"
        proof -
          \<comment> \<open>Show mul(invg k) g0 = pow\_a \<in> 2G, then use normal\_coset\_eq.\<close>
          have "mul (invg k) g0 = pow_a"
          proof -
            have hinv_k: "invg k = mul pow_a (invg g0)"
            proof -
              \<comment> \<open>k = mul g0 (invg pow\_a). In abelian: invg(mul x y) = mul(invg y)(invg x) = mul(invg x)(invg y).\<close>
              have hinv_pa: "invg pow_a \<in> G" using hG_grp hpow_G unfolding top1_is_group_on_def by (by100 blast)
              have hinv_g0: "invg g0 \<in> G" using hG_grp hg0(1) unfolding top1_is_group_on_def by (by100 blast)
              \<comment> \<open>invg(k) = invg(mul g0 (invg pow\_a)).\<close>
              \<comment> \<open>mul(invg k)(mul g0 (invg pow\_a)) = e (since invg k is the inverse of k).\<close>
              have "mul (invg k) k = e" using hG_grp hk_G unfolding top1_is_group_on_def by (by100 blast)
              hence "mul (invg k) (mul g0 (invg pow_a)) = e"
                unfolding k_def by (by100 simp)
              \<comment> \<open>Also mul(mul pow\_a (invg g0))(mul g0 (invg pow\_a)) = e in abelian.\<close>
              \<comment> \<open>= mul pow\_a (mul(invg g0)(mul g0 (invg pow\_a))) [assoc].\<close>
              \<comment> \<open>= mul pow\_a (mul(mul(invg g0) g0)(invg pow\_a)) [assoc].\<close>
              \<comment> \<open>= mul pow\_a (mul e (invg pow\_a)) [invg·g0 = e].\<close>
              \<comment> \<open>= mul pow\_a (invg pow\_a) [e·x = x].\<close>
              \<comment> \<open>= e.\<close>
              have "mul (mul pow_a (invg g0)) (mul g0 (invg pow_a)) = e"
              proof -
                have hassoc: "\<forall>a\<in>G. \<forall>b\<in>G. \<forall>c\<in>G. mul (mul a b) c = mul a (mul b c)"
                  using hG_grp unfolding top1_is_group_on_def by (by100 blast)
                have hcomm: "\<And>x y. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> mul x y = mul y x"
                  using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
                have "mul (invg g0) g0 = e"
                  using hG_grp hg0(1) unfolding top1_is_group_on_def by (by100 blast)
                have "mul pow_a (invg pow_a) = e"
                  using hG_grp hpow_G unfolding top1_is_group_on_def by (by100 blast)
                \<comment> \<open>In abelian: mul(mul pow\_a (invg g0))(mul g0 (invg pow\_a))
                   = mul(mul pow\_a (invg pow\_a))(mul(invg g0) g0) [rearrange]
                   = mul e e = e.\<close>
                \<comment> \<open>Rearrange: (pow\_a \<cdot> invg g0) \<cdot> (g0 \<cdot> invg pow\_a)
                   = pow\_a \<cdot> ((invg g0) \<cdot> (g0 \<cdot> invg pow\_a)) [assoc]
                   = pow\_a \<cdot> (((invg g0) \<cdot> g0) \<cdot> invg pow\_a) [assoc]
                   = pow\_a \<cdot> (e \<cdot> invg pow\_a) = pow\_a \<cdot> invg pow\_a = e.\<close>
                have hinvg0_G: "invg g0 \<in> G" using hG_grp hg0(1) unfolding top1_is_group_on_def by (by100 blast)
                have hinvpa_G: "invg pow_a \<in> G" using hG_grp hpow_G unfolding top1_is_group_on_def by (by100 blast)
                have hg0_invpa: "mul g0 (invg pow_a) \<in> G"
                  using hG_grp hg0(1) hinvpa_G unfolding top1_is_group_on_def by (by100 blast)
                have hpa_invg0: "mul pow_a (invg g0) \<in> G"
                  using hG_grp hpow_G hinvg0_G unfolding top1_is_group_on_def by (by100 blast)
                have "mul (mul pow_a (invg g0)) (mul g0 (invg pow_a))
                    = mul pow_a (mul (invg g0) (mul g0 (invg pow_a)))"
                  using hassoc[rule_format, OF hpow_G hinvg0_G hg0_invpa] by (by100 simp)
                also have "mul (invg g0) (mul g0 (invg pow_a)) = mul (mul (invg g0) g0) (invg pow_a)"
                  using hassoc[rule_format, OF hinvg0_G hg0(1) hinvpa_G] by (by100 simp)
                also have "mul (invg g0) g0 = e" using \<open>mul (invg g0) g0 = e\<close> .
                also have "mul e (invg pow_a) = invg pow_a"
                  using hG_grp hinvpa_G unfolding top1_is_group_on_def by (by100 blast)
                also have "mul pow_a (invg pow_a) = e" using \<open>mul pow_a (invg pow_a) = e\<close> .
                finally show ?thesis .
              qed
              \<comment> \<open>invg k = mul pow\_a (invg g0) (unique inverse).\<close>
              have "invg k \<in> G" using hG_grp hk_G unfolding top1_is_group_on_def by (by100 blast)
              have "mul pow_a (invg g0) \<in> G"
                using hG_grp hpow_G hinv_g0 unfolding top1_is_group_on_def by (by100 blast)
              \<comment> \<open>mul(pow\_a \<cdot> invg g0)(k) = e, and invg k is the unique left inverse.\<close>
              have "mul (mul pow_a (invg g0)) k = e"
                using \<open>mul (mul pow_a (invg g0)) (mul g0 (invg pow_a)) = e\<close>
                unfolding k_def by (by100 simp)
              \<comment> \<open>Also mul(invg k) k = e.\<close>
              have "mul (invg k) k = e" using hG_grp hk_G unfolding top1_is_group_on_def by (by100 blast)
              \<comment> \<open>Both are left inverses. Right-multiply both sides by invg k.\<close>
              hence "mul (mul (invg k) k) (invg k) = mul (mul (mul pow_a (invg g0)) k) (invg k)"
                using \<open>mul (mul pow_a (invg g0)) k = e\<close> by (by100 simp)
              have "mul (mul (invg k) k) (invg k) = invg k"
              proof -
                have "mul (invg k) k = e" using \<open>mul (invg k) k = e\<close> .
                thus ?thesis using hG_grp \<open>invg k \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
              qed
              moreover have "mul (mul (mul pow_a (invg g0)) k) (invg k) = mul pow_a (invg g0)"
              proof -
                have hassoc_loc: "\<forall>a\<in>G. \<forall>b\<in>G. \<forall>c\<in>G. mul (mul a b) c = mul a (mul b c)"
                  using hG_grp unfolding top1_is_group_on_def by (by100 blast)
                have "mul (mul (mul pow_a (invg g0)) k) (invg k)
                    = mul (mul pow_a (invg g0)) (mul k (invg k))"
                  using hassoc_loc[rule_format, OF \<open>mul pow_a (invg g0) \<in> G\<close> hk_G \<open>invg k \<in> G\<close>]
                  by (by100 simp)
                also have "mul k (invg k) = e"
                  using hG_grp hk_G unfolding top1_is_group_on_def by (by100 blast)
                also have "mul (mul pow_a (invg g0)) e = mul pow_a (invg g0)"
                  using hG_grp \<open>mul pow_a (invg g0) \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
                finally show ?thesis .
              qed
              ultimately have "invg k = mul pow_a (invg g0)"
              proof -
                assume h1: "mul (mul (invg k) k) (invg k) = invg k"
                assume h2: "mul (mul (mul pow_a (invg g0)) k) (invg k) = mul pow_a (invg g0)"
                have "invg k = mul (mul (mul pow_a (invg g0)) k) (invg k)"
                  using h1 \<open>mul (mul (invg k) k) (invg k) = mul (mul (mul pow_a (invg g0)) k) (invg k)\<close>
                  by (by100 simp)
                also have "\<dots> = mul pow_a (invg g0)" using h2 .
                finally show "invg k = mul pow_a (invg g0)" .
              qed
              thus ?thesis by (by100 simp)
            qed
            have hassoc: "\<forall>a\<in>G. \<forall>b\<in>G. \<forall>c\<in>G. mul (mul a b) c = mul a (mul b c)"
              using hG_grp unfolding top1_is_group_on_def by (by100 blast)
            have hinv_g0: "invg g0 \<in> G" using hG_grp hg0(1) unfolding top1_is_group_on_def by (by100 blast)
            have "mul (invg k) g0 = mul (mul pow_a (invg g0)) g0"
              using hinv_k by (by100 simp)
            also have "\<dots> = mul pow_a (mul (invg g0) g0)"
              using hassoc[rule_format, OF hpow_G hinv_g0 hg0(1)] by (by100 simp)
            also have "mul (invg g0) g0 = e"
              using hG_grp hg0(1) unfolding top1_is_group_on_def by (by100 blast)
            also have "mul pow_a e = pow_a"
              using hG_grp hpow_G unfolding top1_is_group_on_def by (by100 blast)
            finally show ?thesis .
          qed
          hence "mul (invg k) g0 \<in> ?twoG" using hpow_2G by (by100 simp)
          hence "top1_group_coset_on G mul ?twoG k = top1_group_coset_on G mul ?twoG g0"
            using normal_coset_eq[OF hG_grp h2G_normal hk_G hg0(1)] by (by100 simp)
          thus ?thesis using hg0(2) by (by100 simp)
        qed
        \<comment> \<open>k \<in> K, so coset\_K(k) \<in> QK, and \<psi>(coset\_K(k)) = coset\_G(k) = C.\<close>
        have "top1_group_coset_on ?K mul ?twoK k \<in> ?QK"
          unfolding top1_quotient_group_carrier_on_def using hk_K by (by100 blast)
        moreover have "\<psi> (top1_group_coset_on ?K mul ?twoK k) = C"
        proof -
          let ?CK_k = "top1_group_coset_on ?K mul ?twoK k"
          let ?k' = "SOME k'. k' \<in> ?CK_k"
          \<comment> \<open>k \<in> coset\_K(k), so SOME picks some k' in coset\_K(k).\<close>
          have "k \<in> ?CK_k"
            by (rule coset_self_mem[OF hK_grp])
               (use h2K_normal hk_K in \<open>unfold top1_normal_subgroup_on_def, by100 blast\<close>)+
          hence hk'_mem: "?k' \<in> ?CK_k" by (rule someI)
          \<comment> \<open>k' is in K.\<close>
          from hk'_mem obtain h where "h \<in> ?twoK" "?k' = mul k h"
            unfolding top1_group_coset_on_def by (by100 blast)
          from \<open>h \<in> ?twoK\<close> obtain h' where "h' \<in> ?K" "h = mul h' h'" by (by100 blast)
          have "h \<in> ?K" using hK_grp \<open>h' \<in> ?K\<close> \<open>h = mul h' h'\<close>
            unfolding top1_is_group_on_def by (by100 blast)
          have "mul k h \<in> ?K" using hK_grp hk_K \<open>h \<in> ?K\<close>
            unfolding top1_is_group_on_def by (by100 blast)
          have hk'_K: "?k' \<in> ?K" using \<open>mul k h \<in> ?K\<close> \<open>?k' = mul k h\<close> by (by100 simp)
          have hk'_G: "?k' \<in> G" using hk'_K by (by100 blast)
          \<comment> \<open>k' and k differ by h \<in> 2K \<subseteq> 2G, so coset\_G(k') = coset\_G(k).\<close>
          have "h \<in> ?twoG"
            using \<open>h \<in> ?twoK\<close> hK_cap_2G by (by100 blast)
          have "mul (invg ?k') k \<in> {mul g g | g. g \<in> G}"
          proof -
            have "?k' = mul k h" using \<open>?k' = mul k h\<close> .
            have hk_G: "k \<in> G" using hk_K by (by100 blast)
            have hh_G: "h \<in> G" using \<open>h \<in> ?K\<close> by (by100 blast)
            have hinvk': "invg ?k' \<in> G" using hG_grp hk'_G unfolding top1_is_group_on_def by (by100 blast)
            \<comment> \<open>invg(mul k h) \<cdot> k = invg(h) \<cdot> invg(k) \<cdot> k = invg(h) in abelian.\<close>
            have "mul (invg ?k') k = invg h"
            proof -
              have "mul ?k' (invg h) = k"
              proof -
                have hassoc': "\<forall>a\<in>G. \<forall>b\<in>G. \<forall>c\<in>G. mul (mul a b) c = mul a (mul b c)"
                  using hG_grp unfolding top1_is_group_on_def by (by100 blast)
                have hinvh: "invg h \<in> G" using hG_grp hh_G unfolding top1_is_group_on_def by (by100 blast)
                have "mul ?k' (invg h) = mul (mul k h) (invg h)"
                  using \<open>?k' = mul k h\<close> by (by100 simp)
                also have "\<dots> = mul k (mul h (invg h))"
                  using hassoc'[rule_format, OF hk_G hh_G hinvh] by (by100 simp)
                also have "mul h (invg h) = e"
                  using hG_grp hh_G unfolding top1_is_group_on_def by (by100 blast)
                also have "mul k e = k"
                  using hG_grp hk_G unfolding top1_is_group_on_def by (by100 blast)
                finally show ?thesis .
              qed
              \<comment> \<open>So mul(invg k') k = mul(invg k')(mul k'(invg h)) = invg h.\<close>
              have hassoc': "\<forall>a\<in>G. \<forall>b\<in>G. \<forall>c\<in>G. mul (mul a b) c = mul a (mul b c)"
                using hG_grp unfolding top1_is_group_on_def by (by100 blast)
              have hinvh: "invg h \<in> G" using hG_grp \<open>h \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
              have "mul (invg ?k') k = mul (invg ?k') (mul ?k' (invg h))"
                using \<open>mul ?k' (invg h) = k\<close> by (by100 simp)
              also have "\<dots> = mul (mul (invg ?k') ?k') (invg h)"
                using hassoc'[rule_format, OF hinvk' hk'_G hinvh] by (by100 simp)
              also have "mul (invg ?k') ?k' = e"
                using hG_grp hk'_G unfolding top1_is_group_on_def by (by100 blast)
              also have "mul e (invg h) = invg h"
                using hG_grp hinvh unfolding top1_is_group_on_def by (by100 blast)
              finally show ?thesis .
            qed
            \<comment> \<open>invg h \<in> 2G: h \<in> 2G, so invg h \<in> 2G (2G is a group).\<close>
            moreover have "invg h \<in> {mul g g | g. g \<in> G}"
              using h2G_normal \<open>h \<in> ?twoG\<close> unfolding top1_normal_subgroup_on_def top1_is_group_on_def
              by (by100 blast)
            ultimately show ?thesis by (by100 simp)
          qed
          hence "top1_group_coset_on G mul ?twoG ?k' = top1_group_coset_on G mul ?twoG k"
            using normal_coset_eq[OF hG_grp h2G_normal hk'_G] hk_K by (by100 blast)
          thus ?thesis unfolding \<psi>_def using hcoset_eq by (by100 simp)
        qed
        ultimately show "C \<in> \<psi> ` ?QK" by (by100 blast)
      qed
    qed
    thus ?thesis using bij_betw_same_card[OF hpsi_bij] by (by100 simp)
  qed
  have hodd_card: "card QG_odd = card QG_even"
  proof -
    \<comment> \<open>The quotient group multiplication by [a] is a bijection QG \<rightarrow> QG
       mapping even cosets to odd cosets. Formally: it maps QG\_even onto QG\_odd.\<close>
    let ?mulQG = "top1_quotient_group_mul_on mul"
    let ?coset_a = "top1_group_coset_on G mul ?twoG a"
    \<comment> \<open>Use bij\_betw\_iff\_card: finite sets of equal card have a bijection, and vice versa.\<close>
    \<comment> \<open>Alternatively, just construct the bijection via coset representatives.\<close>
    \<comment> \<open>For each even coset C = coset(g0), the odd coset coset(mul a g0) is the shift.
       This defines a bijection QG\_even \<rightarrow> QG\_odd.\<close>
    define shift where "shift C = (let g0 = SOME g. g \<in> C in
        top1_group_coset_on G mul ?twoG (mul a g0))" for C
    have hia_G: "invg a \<in> G" using hG_grp ha unfolding top1_is_group_on_def by (by100 blast)
    \<comment> \<open>shift is a bijection QG\_even \<rightarrow> QG\_odd.\<close>
    have hshift_bij: "bij_betw shift QG_even QG_odd"
      unfolding bij_betw_def
    proof (rule conjI)
      show "inj_on shift QG_even"
      proof (rule inj_onI)
        fix C1 C2 assume hC1: "C1 \<in> QG_even" and hC2: "C2 \<in> QG_even"
            and heq: "shift C1 = shift C2"
        \<comment> \<open>Get representatives g1, g2 from C1, C2.\<close>
        from hC1 have "C1 \<in> ?QG" unfolding QG_even_def by (by100 blast)
        then obtain g1_rep where hg1: "g1_rep \<in> G" "C1 = top1_group_coset_on G mul ?twoG g1_rep"
          unfolding top1_quotient_group_carrier_on_def by (by100 blast)
        from hC2 have "C2 \<in> ?QG" unfolding QG_even_def by (by100 blast)
        then obtain g2_rep where hg2: "g2_rep \<in> G" "C2 = top1_group_coset_on G mul ?twoG g2_rep"
          unfolding top1_quotient_group_carrier_on_def by (by100 blast)
        \<comment> \<open>SOME picks representatives; they are in G.\<close>
        let ?s1 = "SOME g. g \<in> C1" and ?s2 = "SOME g. g \<in> C2"
        have hs1_C1: "?s1 \<in> C1"
        proof (rule someI)
          have "mul g1_rep e = g1_rep" using hG_grp hg1(1) unfolding top1_is_group_on_def by (by100 blast)
          moreover have "e \<in> ?twoG"
          proof -
            have "e \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
            have "mul e e = e" using hG_grp \<open>e \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
            thus ?thesis using \<open>e \<in> G\<close> by (by5000 force)
          qed
          ultimately show "g1_rep \<in> C1" using hg1(2) unfolding top1_group_coset_on_def by (by5000 force)
        qed
        have hs2_C2: "?s2 \<in> C2"
        proof (rule someI)
          have "mul g2_rep e = g2_rep" using hG_grp hg2(1) unfolding top1_is_group_on_def by (by100 blast)
          moreover have "e \<in> ?twoG"
          proof -
            have "e \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
            have "mul e e = e" using hG_grp \<open>e \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
            thus ?thesis using \<open>e \<in> G\<close> by (by5000 force)
          qed
          ultimately show "g2_rep \<in> C2" using hg2(2) unfolding top1_group_coset_on_def by (by5000 force)
        qed
        have hs1_G: "?s1 \<in> G"
        proof -
          from hs1_C1 hg1(2) obtain h where "h \<in> ?twoG" "?s1 = mul g1_rep h"
            unfolding top1_group_coset_on_def by (by100 blast)
          from \<open>h \<in> ?twoG\<close> obtain h' where "h' \<in> G" by (by100 blast)
          have "h \<in> G" using \<open>h' \<in> G\<close> \<open>h \<in> ?twoG\<close> hG_grp unfolding top1_is_group_on_def by (by5000 blast)
          have "mul g1_rep h \<in> G" using hG_grp hg1(1) \<open>h \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
          thus ?thesis using \<open>?s1 = mul g1_rep h\<close> by (by100 simp)
        qed
        have hs2_G: "?s2 \<in> G"
        proof -
          from hs2_C2 hg2(2) obtain h where "h \<in> ?twoG" "?s2 = mul g2_rep h"
            unfolding top1_group_coset_on_def by (by100 blast)
          from \<open>h \<in> ?twoG\<close> obtain h' where "h' \<in> G" by (by100 blast)
          have "h \<in> G" using \<open>h' \<in> G\<close> \<open>h \<in> ?twoG\<close> hG_grp unfolding top1_is_group_on_def by (by5000 blast)
          have "mul g2_rep h \<in> G" using hG_grp hg2(1) \<open>h \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
          thus ?thesis using \<open>?s2 = mul g2_rep h\<close> by (by100 simp)
        qed
        \<comment> \<open>shift(C1) = coset(mul a s1), shift(C2) = coset(mul a s2). Equal by heq.\<close>
        have has1_G: "mul a ?s1 \<in> G" using hG_grp ha hs1_G unfolding top1_is_group_on_def by (by100 blast)
        have has2_G: "mul a ?s2 \<in> G" using hG_grp ha hs2_G unfolding top1_is_group_on_def by (by100 blast)
        \<comment> \<open>From equal cosets: mul(invg(mul a s1))(mul a s2) \<in> 2G.\<close>
        have hcoset_as: "top1_group_coset_on G mul ?twoG (mul a ?s1) = top1_group_coset_on G mul ?twoG (mul a ?s2)"
          using heq unfolding shift_def Let_def by (by100 simp)
        hence "mul (invg (mul a ?s1)) (mul a ?s2) \<in> ?twoG"
          using normal_coset_eq[OF hG_grp h2G_normal has1_G has2_G] by (by100 simp)
        \<comment> \<open>In abelian: invg(mul a s1) = mul(invg s1)(invg a), so
           mul(invg(mul a s1))(mul a s2) = mul(invg s1)(mul(invg a)(mul a s2)) = mul(invg s1) s2.\<close>
        moreover have "mul (invg (mul a ?s1)) (mul a ?s2) = mul (invg ?s1) ?s2"
        proof -
          have hassoc: "\<And>x y z. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> z \<in> G \<Longrightarrow> mul (mul x y) z = mul x (mul y z)"
            using hG_grp unfolding top1_is_group_on_def by (by100 blast)
          have hcomm: "\<And>x y. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> mul x y = mul y x"
            using hG unfolding top1_is_abelian_group_on_def by (by100 blast)
          have hinvs1: "invg ?s1 \<in> G" using hG_grp hs1_G unfolding top1_is_group_on_def by (by100 blast)
          \<comment> \<open>invg(a\<cdot>s1) = invg(s1)\<cdot>invg(a) in abelian.\<close>
          have hinv_as1: "invg (mul a ?s1) \<in> G" using hG_grp has1_G unfolding top1_is_group_on_def by (by100 blast)
          \<comment> \<open>mul(invg(a\<cdot>s1))(a\<cdot>s2) = e when s1=s2 (trivially). In general:
             = invg(a\<cdot>s1)\<cdot>a\<cdot>s2. Since invg(a\<cdot>s1)\<cdot>(a\<cdot>s1) = e, we have
             invg(a\<cdot>s1)\<cdot>a = invg(s1) (by right-multiplying both sides by invg(s1) and simplifying).
             Actually, simpler: mul(invg(a\<cdot>s1))(a\<cdot>s2) in abelian = mul(invg a)(invg s1)(a)(s2)
             = mul(invg a)(a)(invg s1)(s2) = mul(e)(invg s1)(s2) = mul(invg s1)(s2).\<close>
          have "mul (invg (mul a ?s1)) (mul a ?s2) = mul (mul (invg (mul a ?s1)) a) ?s2"
            using hassoc[OF hinv_as1 ha hs2_G] by (by100 simp)
          moreover have "mul (invg (mul a ?s1)) a = invg ?s1"
          proof -
            \<comment> \<open>mul(invg(a\<cdot>s1))(a) = mul(invg(a\<cdot>s1))(a\<cdot>(mul s1 (invg s1)))
               = mul(invg(a\<cdot>s1))(mul(a\<cdot>s1)(invg s1)) = mul(e)(invg s1) = invg s1.\<close>
            have "mul (invg (mul a ?s1)) (mul (mul a ?s1) (invg ?s1))
                = mul (mul (invg (mul a ?s1)) (mul a ?s1)) (invg ?s1)"
              using hassoc[OF hinv_as1 has1_G hinvs1] by (by100 simp)
            also have "mul (invg (mul a ?s1)) (mul a ?s1) = e"
              using hG_grp has1_G unfolding top1_is_group_on_def by (by100 blast)
            also have "mul e (invg ?s1) = invg ?s1"
              using hG_grp hinvs1 unfolding top1_is_group_on_def by (by100 blast)
            finally have h1: "mul (invg (mul a ?s1)) (mul (mul a ?s1) (invg ?s1)) = invg ?s1" .
            \<comment> \<open>Also mul(a\<cdot>s1)(invg s1) = mul a (mul s1 (invg s1)) = mul a e = a.\<close>
            have "mul (mul a ?s1) (invg ?s1) = mul a (mul ?s1 (invg ?s1))"
              using hassoc[OF ha hs1_G hinvs1] by (by100 simp)
            also have "mul ?s1 (invg ?s1) = e"
              using hG_grp hs1_G unfolding top1_is_group_on_def by (by100 blast)
            also have "mul a e = a"
              using hG_grp ha unfolding top1_is_group_on_def by (by100 blast)
            finally have "mul (mul a ?s1) (invg ?s1) = a" .
            with h1 show ?thesis by (by100 simp)
          qed
          ultimately show ?thesis by (by100 simp)
        qed
        ultimately have "mul (invg ?s1) ?s2 \<in> ?twoG" by (by100 simp)
        \<comment> \<open>So coset(s1) = coset(s2), meaning C1 = C2.\<close>
        hence "top1_group_coset_on G mul ?twoG ?s1 = top1_group_coset_on G mul ?twoG ?s2"
          using normal_coset_eq[OF hG_grp h2G_normal hs1_G hs2_G] by (by100 simp)
        \<comment> \<open>s1 \<in> C1 = coset(g1\_rep), so coset(s1) = C1. Similarly for s2.\<close>
        moreover have "C1 = top1_group_coset_on G mul ?twoG ?s1"
        proof -
          \<comment> \<open>s1 \<in> C1 = coset(g1\_rep). So s1 = mul g1\_rep h for h \<in> 2G.
             mul(invg g1\_rep) s1 = h \<in> 2G. By normal\_coset\_eq: coset(g1\_rep) = coset(s1).\<close>
          from hs1_C1 hg1(2) obtain h where "h \<in> ?twoG" "?s1 = mul g1_rep h"
            unfolding top1_group_coset_on_def by (by100 blast)
          have hh_G: "h \<in> G"
          proof -
            from \<open>h \<in> ?twoG\<close> obtain h' where "h' \<in> G" "h = mul h' h'" by (by100 blast)
            thus ?thesis using hG_grp unfolding top1_is_group_on_def by (by100 blast)
          qed
          have "mul (invg g1_rep) ?s1 = h"
          proof -
            have hinvg1: "invg g1_rep \<in> G" using hG_grp hg1(1) unfolding top1_is_group_on_def by (by100 blast)
            have hassoc_l: "\<And>x y z. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> z \<in> G \<Longrightarrow> mul (mul x y) z = mul x (mul y z)"
              using hG_grp unfolding top1_is_group_on_def by (by100 blast)
            have "mul (invg g1_rep) ?s1 = mul (invg g1_rep) (mul g1_rep h)"
              using \<open>?s1 = mul g1_rep h\<close> by (by100 simp)
            also have "\<dots> = mul (mul (invg g1_rep) g1_rep) h"
              using hassoc_l[OF hinvg1 hg1(1) hh_G] by (by100 simp)
            also have "mul (invg g1_rep) g1_rep = e"
              using hG_grp hg1(1) unfolding top1_is_group_on_def by (by100 blast)
            also have "mul e h = h"
              using hG_grp hh_G unfolding top1_is_group_on_def by (by100 blast)
            finally show ?thesis .
          qed
          hence "mul (invg g1_rep) ?s1 \<in> ?twoG" using \<open>h \<in> ?twoG\<close> by (by100 simp)
          hence hcoset_eq1: "top1_group_coset_on G mul ?twoG g1_rep = top1_group_coset_on G mul ?twoG ?s1"
            using normal_coset_eq[OF hG_grp h2G_normal hg1(1) hs1_G] by (by100 simp)
          show ?thesis using hg1(2) hcoset_eq1 by (by5000 metis)
        qed
        moreover have "C2 = top1_group_coset_on G mul ?twoG ?s2"
        proof -
          from hs2_C2 hg2(2) obtain h where "h \<in> ?twoG" "?s2 = mul g2_rep h"
            unfolding top1_group_coset_on_def by (by100 blast)
          have hh_G: "h \<in> G"
          proof -
            from \<open>h \<in> ?twoG\<close> obtain h' where "h' \<in> G" "h = mul h' h'" by (by100 blast)
            thus ?thesis using hG_grp unfolding top1_is_group_on_def by (by100 blast)
          qed
          have "mul (invg g2_rep) ?s2 = h"
          proof -
            have hinvg2: "invg g2_rep \<in> G" using hG_grp hg2(1) unfolding top1_is_group_on_def by (by100 blast)
            have hassoc_l: "\<And>x y z. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> z \<in> G \<Longrightarrow> mul (mul x y) z = mul x (mul y z)"
              using hG_grp unfolding top1_is_group_on_def by (by100 blast)
            have "mul (invg g2_rep) ?s2 = mul (invg g2_rep) (mul g2_rep h)"
              using \<open>?s2 = mul g2_rep h\<close> by (by100 simp)
            also have "\<dots> = mul (mul (invg g2_rep) g2_rep) h"
              using hassoc_l[OF hinvg2 hg2(1) hh_G] by (by100 simp)
            also have "mul (invg g2_rep) g2_rep = e"
              using hG_grp hg2(1) unfolding top1_is_group_on_def by (by100 blast)
            also have "mul e h = h"
              using hG_grp hh_G unfolding top1_is_group_on_def by (by100 blast)
            finally show ?thesis .
          qed
          hence "mul (invg g2_rep) ?s2 \<in> ?twoG" using \<open>h \<in> ?twoG\<close> by (by100 simp)
          hence hcoset_eq2: "top1_group_coset_on G mul ?twoG g2_rep = top1_group_coset_on G mul ?twoG ?s2"
            using normal_coset_eq[OF hG_grp h2G_normal hg2(1) hs2_G] by (by100 simp)
          show ?thesis using hg2(2) hcoset_eq2 by (by5000 metis)
        qed
        ultimately show "C1 = C2" by (by100 simp)
      qed
    next
      show "shift ` QG_even = QG_odd"
      proof (rule set_eqI, rule iffI)
        \<comment> \<open>\<subseteq>: shift maps even cosets to odd cosets.\<close>
        fix C assume "C \<in> shift ` QG_even"
        then obtain C0 where hC0: "C0 \<in> QG_even" "C = shift C0" by (by100 blast)
        from hC0(1) have "C0 \<in> ?QG" unfolding QG_even_def by (by100 blast)
        then obtain g0 where hg0: "g0 \<in> G" "C0 = top1_group_coset_on G mul ?twoG g0"
          unfolding top1_quotient_group_carrier_on_def by (by100 blast)
        \<comment> \<open>g0 has even \<epsilon> (from C0 \<in> QG\_even + \<epsilon>-coset parity).\<close>
        have hg0_even: "even (\<epsilon> g0)"
        proof -
          from hC0(1) obtain g1 where "g1 \<in> C0" "even (\<epsilon> g1)" unfolding QG_even_def by (by100 blast)
          from \<open>g1 \<in> C0\<close> hg0(2) obtain h where "h \<in> ?twoG" "g1 = mul g0 h"
            unfolding top1_group_coset_on_def by (by100 blast)
          thus ?thesis using heps_coset[OF hg0(1) \<open>h \<in> ?twoG\<close>] \<open>g1 = mul g0 h\<close> \<open>even (\<epsilon> g1)\<close> by (by100 simp)
        qed
        \<comment> \<open>shift(C0) = coset(mul a (SOME g \<in> C0)). Since SOME picks g0' from C0,
           and g0' has even \<epsilon>, mul a g0' has odd \<epsilon>.\<close>
        have hag0_G: "mul a g0 \<in> G" using hG_grp ha hg0(1) unfolding top1_is_group_on_def by (by100 blast)
        \<comment> \<open>shift(C0) \<in> QG (it's a G-coset).\<close>
        \<comment> \<open>shift(C0) has odd elements (mul a g0 has \<epsilon> = 1 + \<epsilon>(g0) which is odd).\<close>
        show "C \<in> QG_odd"
        proof -
          let ?s0 = "SOME g. g \<in> C0"
          have hs0_C0: "?s0 \<in> C0"
          proof (rule someI)
            show "g0 \<in> C0"
            proof -
              have "e \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
              have "mul e e = e" using hG_grp \<open>e \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
              hence "e \<in> ?twoG" using \<open>e \<in> G\<close> by (by5000 force)
              have "mul g0 e = g0" using hG_grp hg0(1) unfolding top1_is_group_on_def by (by100 blast)
              thus ?thesis using hg0(2) \<open>e \<in> ?twoG\<close> unfolding top1_group_coset_on_def by (by5000 force)
            qed
          qed
          have hs0_G: "?s0 \<in> G"
          proof -
            from hs0_C0 hg0(2) obtain h where "h \<in> ?twoG" "?s0 = mul g0 h"
              unfolding top1_group_coset_on_def by (by100 blast)
            from \<open>h \<in> ?twoG\<close> obtain h' where "h' \<in> G" by (by100 blast)
            have "h \<in> G" using \<open>h' \<in> G\<close> \<open>h \<in> ?twoG\<close> hG_grp unfolding top1_is_group_on_def by (by5000 blast)
            have "mul g0 h \<in> G" using hG_grp hg0(1) \<open>h \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
            thus ?thesis using \<open>?s0 = mul g0 h\<close> by (by100 simp)
          qed
          have has0_G: "mul a ?s0 \<in> G" using hG_grp ha hs0_G unfolding top1_is_group_on_def by (by100 blast)
          \<comment> \<open>C = shift(C0) = coset(mul a s0).\<close>
          have hC_eq: "C = top1_group_coset_on G mul ?twoG (mul a ?s0)"
            using hC0(2) unfolding shift_def Let_def by (by100 simp)
          \<comment> \<open>C \<in> QG.\<close>
          have "C \<in> ?QG" using hC_eq has0_G
            unfolding top1_quotient_group_carrier_on_def by (by100 blast)
          \<comment> \<open>mul a s0 \<in> C and has odd \<epsilon>.\<close>
          moreover have "\<exists>g\<in>C. odd (\<epsilon> g)"
          proof -
            have "mul a ?s0 \<in> C"
              using hC_eq coset_self_mem[OF hG_grp h2G_sub h2G_grp has0_G] by (by100 simp)
            moreover have "odd (\<epsilon> (mul a ?s0))"
            proof -
              have "\<epsilon> (mul a ?s0) = \<epsilon> a + \<epsilon> ?s0"
                using heps ha hs0_G unfolding top1_group_hom_on_def by (by100 blast)
              hence "\<epsilon> (mul a ?s0) = 1 + \<epsilon> ?s0" using heps_a by (by100 simp)
              moreover have "even (\<epsilon> ?s0)"
              proof -
                from hs0_C0 hg0(2) obtain h where "h \<in> ?twoG" "?s0 = mul g0 h"
                  unfolding top1_group_coset_on_def by (by100 blast)
                thus ?thesis using heps_coset[OF hg0(1) \<open>h \<in> ?twoG\<close>] hg0_even \<open>?s0 = mul g0 h\<close> by (by100 simp)
              qed
              ultimately show ?thesis by (by100 simp)
            qed
            ultimately show ?thesis by (by100 blast)
          qed
          ultimately show ?thesis unfolding QG_odd_def by (by100 blast)
        qed
      next
        \<comment> \<open>\<supseteq>: every odd coset is shift of some even coset.\<close>
        fix C assume "C \<in> QG_odd"
        hence hC_QG: "C \<in> ?QG" unfolding QG_odd_def by (by100 blast)
        then obtain g0 where hg0: "g0 \<in> G" "C = top1_group_coset_on G mul ?twoG g0"
          unfolding top1_quotient_group_carrier_on_def by (by100 blast)
        \<comment> \<open>g0 has odd \<epsilon>.\<close>
        have hg0_odd: "odd (\<epsilon> g0)"
        proof -
          from \<open>C \<in> QG_odd\<close> obtain g1 where "g1 \<in> C" "odd (\<epsilon> g1)" unfolding QG_odd_def by (by100 blast)
          from \<open>g1 \<in> C\<close> hg0(2) obtain h where "h \<in> ?twoG" "g1 = mul g0 h"
            unfolding top1_group_coset_on_def by (by100 blast)
          thus ?thesis using heps_coset[OF hg0(1) \<open>h \<in> ?twoG\<close>] \<open>g1 = mul g0 h\<close> \<open>odd (\<epsilon> g1)\<close> by (by100 simp)
        qed
        \<comment> \<open>Let C' = coset(mul(invg a) g0). C' is even (\<epsilon> = \<epsilon>(g0) - 1 = even).
           shift(C') = coset(mul a (SOME g \<in> C')). Need this = C.\<close>
        let ?g0' = "mul (invg a) g0"
        have hg0'_G: "?g0' \<in> G" using hG_grp hia_G hg0(1) unfolding top1_is_group_on_def by (by100 blast)
        have hg0'_even: "even (\<epsilon> ?g0')"
        proof -
          have "\<epsilon> ?g0' = \<epsilon> (invg a) + \<epsilon> g0"
            using heps hia_G hg0(1) unfolding top1_group_hom_on_def by (by100 blast)
          also have "\<epsilon> (invg a) = -1"
            using hom_preserves_inv[OF hG_grp hZ_grp heps ha] heps_a by (by100 simp)
          finally show ?thesis using hg0_odd by (by100 simp)
        qed
        have "top1_group_coset_on G mul ?twoG ?g0' \<in> QG_even"
        proof -
          have "top1_group_coset_on G mul ?twoG ?g0' \<in> ?QG"
            using hg0'_G unfolding top1_quotient_group_carrier_on_def by (by100 blast)
          moreover have "\<exists>g \<in> top1_group_coset_on G mul ?twoG ?g0'. even (\<epsilon> g)"
          proof -
            have "?g0' \<in> top1_group_coset_on G mul ?twoG ?g0'"
              by (rule coset_self_mem[OF hG_grp h2G_sub h2G_grp hg0'_G])
            thus ?thesis using hg0'_even by (by100 blast)
          qed
          ultimately show ?thesis unfolding QG_even_def by (by100 blast)
        qed
        moreover have "shift (top1_group_coset_on G mul ?twoG ?g0') = C"
        proof -
          let ?C' = "top1_group_coset_on G mul ?twoG ?g0'"
          let ?s = "SOME g. g \<in> ?C'"
          \<comment> \<open>SOME picks a representative from coset(invg(a)\<cdot>g0).\<close>
          have hs_C': "?s \<in> ?C'"
          proof (rule someI)
            show "?g0' \<in> ?C'"
              by (rule coset_self_mem[OF hG_grp h2G_sub h2G_grp hg0'_G])
          qed
          have hs_G: "?s \<in> G"
          proof -
            from hs_C' obtain h where "h \<in> ?twoG" "?s = mul ?g0' h"
              unfolding top1_group_coset_on_def by (by100 blast)
            from \<open>h \<in> ?twoG\<close> obtain h' where "h' \<in> G" by (by100 blast)
            have "h \<in> G" using \<open>h' \<in> G\<close> \<open>h \<in> ?twoG\<close> hG_grp unfolding top1_is_group_on_def by (by5000 blast)
            have "mul ?g0' h \<in> G" using hG_grp hg0'_G \<open>h \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
            thus ?thesis using \<open>?s = mul ?g0' h\<close> by (by100 simp)
          qed
          \<comment> \<open>shift(?C') = coset(mul a ?s). Need this = coset(g0) = C.\<close>
          have "shift ?C' = top1_group_coset_on G mul ?twoG (mul a ?s)"
            unfolding shift_def Let_def by (by100 simp)
          \<comment> \<open>?s differs from ?g0' by some h \<in> 2G, so mul a ?s differs from mul a ?g0' by h \<in> 2G.
             coset(mul a ?s) = coset(mul a ?g0') = coset(g0) (since a\<cdot>(invg a\<cdot>g0) = g0).\<close>
          moreover have "top1_group_coset_on G mul ?twoG (mul a ?s) = top1_group_coset_on G mul ?twoG g0"
          proof -
            \<comment> \<open>?s and ?g0' are in same G-coset.\<close>
            from hs_C' obtain h where hh: "h \<in> ?twoG" "?s = mul ?g0' h"
              unfolding top1_group_coset_on_def by (by100 blast)
            from hh(1) obtain h' where "h' \<in> G" "h = mul h' h'" by (by100 blast)
            have hh_G: "h \<in> G" using \<open>h' \<in> G\<close> \<open>h = mul h' h'\<close> hG_grp unfolding top1_is_group_on_def by (by100 blast)
            \<comment> \<open>mul a ?s = mul a (mul ?g0' h) = mul (mul a ?g0') h = mul g0 h (since a\<cdot>invg(a)\<cdot>g0 = g0).\<close>
            have hassoc: "\<And>x y z. x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> z \<in> G \<Longrightarrow> mul (mul x y) z = mul x (mul y z)"
              using hG_grp unfolding top1_is_group_on_def by (by100 blast)
            have "mul a ?s = mul a (mul ?g0' h)" using hh(2) by (by100 simp)
            also have "\<dots> = mul (mul a ?g0') h" using hassoc[OF ha hg0'_G hh_G] by (by100 simp)
            also have "mul a ?g0' = g0"
            proof -
              have "mul a (mul (invg a) g0) = mul (mul a (invg a)) g0"
                using hassoc[OF ha hia_G hg0(1)] by (by100 simp)
              also have "mul a (invg a) = e"
                using hG_grp ha unfolding top1_is_group_on_def by (by100 blast)
              also have "mul e g0 = g0"
                using hG_grp hg0(1) unfolding top1_is_group_on_def by (by100 blast)
              finally show ?thesis by (by100 simp)
            qed
            finally have "mul a ?s = mul g0 h" by (by100 simp)
            \<comment> \<open>So mul(invg g0)(mul a ?s) = h \<in> 2G.\<close>
            hence "mul (invg g0) (mul a ?s) = h"
            proof -
              have hinvg0: "invg g0 \<in> G" using hG_grp hg0(1) unfolding top1_is_group_on_def by (by100 blast)
              have "mul (invg g0) (mul a ?s) = mul (invg g0) (mul g0 h)"
                using \<open>mul a ?s = mul g0 h\<close> by (by100 simp)
              also have "\<dots> = mul (mul (invg g0) g0) h"
                using hassoc[OF hinvg0 hg0(1) hh_G] by (by100 simp)
              also have "mul (invg g0) g0 = e"
                using hG_grp hg0(1) unfolding top1_is_group_on_def by (by100 blast)
              also have "mul e h = h"
                using hG_grp hh_G unfolding top1_is_group_on_def by (by100 blast)
              finally show ?thesis using \<open>mul a ?s = mul g0 h\<close> by (by100 simp)
            qed
            hence "mul (invg g0) (mul a ?s) \<in> ?twoG" using hh(1) by (by100 simp)
            have has_G: "mul a ?s \<in> G" using hG_grp ha hs_G unfolding top1_is_group_on_def by (by100 blast)
            thus ?thesis using normal_coset_eq[OF hG_grp h2G_normal hg0(1) has_G]
              \<open>mul (invg g0) (mul a ?s) \<in> ?twoG\<close> by (by100 simp)
          qed
          ultimately show ?thesis using hg0(2) by (by5000 metis)
        qed
        ultimately show "C \<in> shift ` QG_even" by (by100 blast)
      qed
    qed
    show ?thesis using bij_betw_same_card[OF hshift_bij] by (by100 simp)
  qed
  have hfin_even: "finite QG_even"
  proof (rule ccontr)
    assume "\<not> finite QG_even"
    hence "card QG_even = 0" by (by100 simp)
    hence "card ?QK = 0" using heven_card by (by100 simp)
    moreover have "?QK \<noteq> {}"
    proof -
      have "e \<in> ?K"
      proof -
        have "e \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
        have "\<epsilon> e = 0" using hom_preserves_id[OF hG_grp hZ_grp heps] by (by100 simp)
        thus ?thesis using \<open>e \<in> G\<close> by (by100 simp)
      qed
      thus ?thesis unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    qed
    ultimately show False using hQK_fin by (by100 force)
  qed
  have hfin_odd: "finite QG_odd"
  proof (rule ccontr)
    assume "\<not> finite QG_odd"
    hence "card QG_odd = 0" by (by100 simp)
    hence "card QG_even = 0" using hodd_card by (by100 simp)
    hence "card ?QK = 0" using heven_card by (by100 simp)
    moreover have "?QK \<noteq> {}"
    proof -
      have "e \<in> ?K"
      proof -
        have "e \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
        have "\<epsilon> e = 0" using hom_preserves_id[OF hG_grp hZ_grp heps] by (by100 simp)
        thus ?thesis using \<open>e \<in> G\<close> by (by100 simp)
      qed
      thus ?thesis unfolding top1_quotient_group_carrier_on_def by (by100 blast)
    qed
    ultimately show False using hQK_fin by (by100 force)
  qed
  have "card ?QG = card QG_even + card QG_odd"
    using hpartition card_Un_disjoint[OF hfin_even hfin_odd hdisjoint] by (by100 simp)
  also have "\<dots> = card ?QK + card ?QK" using heven_card hodd_card by (by100 simp)
  also have "\<dots> = 2 * card ?QK" by (by100 simp)
  finally show ?thesis .
qed

text \<open>Key lemma for Theorem 67.8: |G/2G| = 2^|S| for free abelian G on finite basis S.\<close>
lemma free_abelian_mod2_card:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and iota :: "'s \<Rightarrow> 'g" and S :: "'s set"
  assumes "top1_is_free_abelian_group_full_on G mul e invg iota S"
      and "finite S"
  shows "card (top1_quotient_group_carrier_on G mul {mul g g | g. g \<in> G}) = 2 ^ card S"
proof -
  \<comment> \<open>Munkres 67.8: G \<cong> Z^S, so G/2G \<cong> (Z/2Z)^S has 2^|S| elements.\<close>
  \<comment> \<open>Proof by induction on |S|.\<close>
  show ?thesis using assms
  proof (induction "card S" arbitrary: G mul e invg S iota)
    case 0
    \<comment> \<open>card S = 0 \<Rightarrow> S = {} \<Rightarrow> G = {e}. 2G = {e}. G/2G = {{e}}. |G/2G| = 1 = 2^0.\<close>
    hence "S = {}" using \<open>finite S\<close> by (by100 simp)
    hence hS_empty: "S = {}" using \<open>finite S\<close> by (by100 simp)
    have hG_grp: "top1_is_group_on G mul e invg"
      using 0(2) unfolding top1_is_free_abelian_group_full_on_def
        top1_is_abelian_group_on_def by (by100 blast)
    have hG_gen: "G = top1_subgroup_generated_on G mul e invg (iota ` S)"
      using 0(2) unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
    hence hG_trivial: "G = {e}"
    proof -
      have "iota ` S = {}" using hS_empty by (by100 simp)
      hence "G = top1_subgroup_generated_on G mul e invg {}" using hG_gen by (by100 simp)
      also have "\<dots> = {e}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> top1_subgroup_generated_on G mul e invg {}"
        hence hx: "\<And>H. H \<subseteq> G \<Longrightarrow> top1_is_group_on H mul e invg \<Longrightarrow> x \<in> H"
          unfolding top1_subgroup_generated_on_def by (by100 blast)
        \<comment> \<open>{e} is a subgroup of G.\<close>
        have he_G: "e \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
        have "{e} \<subseteq> G" using he_G by (by100 blast)
        moreover have "top1_is_group_on {e} mul e invg"
        proof -
          have hmul_ee: "mul e e = e" using hG_grp he_G unfolding top1_is_group_on_def by (by100 blast)
          have hinve_G: "invg e \<in> G" using hG_grp he_G unfolding top1_is_group_on_def by (by100 blast)
          have hinve: "invg e = e"
          proof -
            have "mul e (invg e) = invg e" using hG_grp hinve_G unfolding top1_is_group_on_def by (by100 blast)
            moreover have "mul e (invg e) = e" using hG_grp he_G unfolding top1_is_group_on_def by (by100 blast)
            ultimately show ?thesis by (by100 simp)
          qed
          have "\<forall>x\<in>{e}. x = e" by (by100 blast)
          thus ?thesis unfolding top1_is_group_on_def
            using hmul_ee hinve by (by100 force)
        qed
        ultimately have "x \<in> {e}" using hx by (by100 blast)
        thus "x \<in> {e}" .
      next
        fix x assume "x \<in> {e}"
        hence "x = e" by (by100 blast)
        show "x \<in> top1_subgroup_generated_on G mul e invg {}"
          unfolding top1_subgroup_generated_on_def
        proof (rule InterI, clarify)
          fix H assume "H \<subseteq> G" "top1_is_group_on H mul e invg"
          thus "x \<in> H" using \<open>x = e\<close> unfolding top1_is_group_on_def by (by100 blast)
        qed
      qed
      finally show ?thesis .
    qed
    hence h2G: "{mul g g | g. g \<in> G} = {e}"
    proof -
      have "e \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      have "{mul g g | g. g \<in> G} = {mul e e}" using hG_trivial by (by100 blast)
      also have "mul e e = e" using hG_grp \<open>e \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
      finally show ?thesis by (by100 blast)
    qed
    hence "top1_quotient_group_carrier_on G mul {mul g g | g. g \<in> G} = {{e}}"
    proof -
      have "top1_quotient_group_carrier_on G mul {e}
          = {top1_group_coset_on G mul {e} g | g. g \<in> G}"
        unfolding top1_quotient_group_carrier_on_def by (by100 blast)
      also have "\<dots> = {{e}}" using hG_trivial
      proof -
        assume hG_e: "G = {e}"
        have "top1_group_coset_on G mul {e} e = {mul e n | n. n \<in> {e}}"
          unfolding top1_group_coset_on_def by (by100 blast)
        also have "\<dots> = {mul e e}" by (by100 blast)
        also have "\<dots> = {e}"
        proof -
          have "e \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
          have "mul e e = e" using hG_grp \<open>e \<in> G\<close> unfolding top1_is_group_on_def by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        finally have hcoset_e: "top1_group_coset_on G mul {e} e = {e}" .
        show "{top1_group_coset_on G mul {e} g | g. g \<in> G} = {{e}}"
          using hG_e hcoset_e by (by100 blast)
      qed
      finally show ?thesis using h2G by (by100 simp)
    qed
    thus ?case using \<open>S = {}\<close> \<open>finite S\<close> by (by100 simp)
  next
    case (Suc n)
    \<comment> \<open>card S = Suc n. Pick s0 \<in> S, let S' = S - {s0}.
       G decomposes as "Z-component for s0" × "subgroup generated by S'".
       G/2G \<cong> (Z/2Z) × (H/2H) where H = \<langle>\<iota>(S')\<rangle>.
       By IH, |H/2H| = 2^n. So |G/2G| = 2 \<times> 2^n = 2^{n+1}.\<close>
    \<comment> \<open>Following Munkres 67.8: pick s0 \<in> S, use coordinate projection \<epsilon>_{s0}.\<close>
    have hfree: "top1_is_free_abelian_group_full_on G mul e invg iota S"
      using Suc.prems(1) by (by100 blast)
    have hfin: "finite S" using Suc.prems(2) by (by100 blast)
    have "card S > 0" using Suc.hyps by (by100 simp)
    then obtain s0 where hs0: "s0 \<in> S" using card_gt_0_iff hfin by (by100 force)
    let ?S' = "S - {s0}"
    have hcard': "card ?S' = n" using Suc.hyps hfin hs0 by (by100 simp)
    \<comment> \<open>Get coordinate projection \<epsilon>_{s0}: G \<rightarrow> Z.\<close>
    obtain \<epsilon> where heps: "top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>"
        and heps_s0: "\<epsilon> (iota s0) = 1"
        and heps_other: "\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<epsilon> (iota s) = 0"
      using free_abelian_coordinate_projection[OF hfree hs0] by (by100 blast)
    \<comment> \<open>The kernel ker(\<epsilon>) is free abelian on S'.\<close>
    let ?K = "{g \<in> G. \<epsilon> g = 0}"
    have hK_free: "top1_is_free_abelian_group_full_on ?K mul e invg iota ?S'"
      by (rule free_abelian_kernel_coordinate[OF hfree hs0 heps heps_s0 heps_other])
    have hfin': "finite ?S'" using hfin by (by100 simp)
    \<comment> \<open>Apply IH: |K/2K| = 2^n.\<close>
    have hIH: "card (top1_quotient_group_carrier_on ?K mul {mul g g | g. g \<in> ?K}) = 2 ^ n"
    proof -
      note hIH_raw = Suc.hyps(1)
      show ?thesis using hIH_raw[OF hcard'[symmetric] hK_free hfin'] hcard' by (by100 simp)
    qed
    \<comment> \<open>G/2G = 2 \<times> K/2K by quotient\_2G\_decomposition.\<close>
    \<comment> \<open>Need: unique decomposition g = k + m\<cdot>\<iota>(s0) with k \<in> K.\<close>
    \<comment> \<open>Following book (Theorem 67.8): \<epsilon> mod 2 partitions G/2G into even/odd halves,
       each bijects with K/2K. So |G/2G| = 2 \<times> |K/2K| = 2 \<times> 2^n = 2^{n+1}.\<close>
    have habel: "top1_is_abelian_group_on G mul e invg"
      using hfree unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
    have ha_G: "iota s0 \<in> G"
      using hfree hs0 unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
    have "card (top1_quotient_group_carrier_on G mul {mul g g | g. g \<in> G})
       = 2 * card (top1_quotient_group_carrier_on ?K mul {mul g g | g. g \<in> ?K})"
    proof (rule quotient_double_by_kernel[OF habel heps ha_G heps_s0 hK_free])
      \<comment> \<open>Finiteness of K/2K from IH: card = 2^n.\<close>
      show "finite (top1_quotient_group_carrier_on ?K mul {mul g g | g. g \<in> ?K})"
      proof (rule ccontr)
        assume "\<not> finite (top1_quotient_group_carrier_on ?K mul {mul g g | g. g \<in> ?K})"
        hence "card (top1_quotient_group_carrier_on ?K mul {mul g g | g. g \<in> ?K}) = 0"
          by (by100 simp)
        thus False using hIH by (by100 simp)
      qed
    qed
    hence "card (top1_quotient_group_carrier_on G mul {mul g g | g. g \<in> G}) = 2 * 2 ^ n"
      using hIH by (by100 simp)
    also have "\<dots> = 2 ^ Suc n" by (by100 simp)
    finally show ?case using Suc.hyps by (by100 simp)
  qed
qed

(** from \<S>67 Theorem 67.8: rank of free abelian group is well-defined.
    Any two bases of a free abelian group have the same cardinality. **)
theorem Theorem_67_8_rank_unique:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and iota1 :: "'s1 \<Rightarrow> 'g" and S1 :: "'s1 set"
    and iota2 :: "'s2 \<Rightarrow> 'g" and S2 :: "'s2 set"
  assumes "top1_is_free_abelian_group_full_on G mul e invg iota1 S1"
      and "top1_is_free_abelian_group_full_on G mul e invg iota2 S2"
      and "finite S1" and "finite S2"
  shows "\<exists>f. bij_betw f S1 S2"
proof -
  \<comment> \<open>Munkres 67.8: Tensor with Z/2Z: G/2G is a vector space over Z/2Z of dimension
     equal to the rank. Dimension of a vector space is unique.
     Step 1: G \<cong> Z^S1 (free abelian on S1) and G \<cong> Z^S2 (free abelian on S2).
     Step 2: G/2G \<cong> (Z/2Z)^S1 \<cong> (Z/2Z)^S2.
     Step 3: Vector space dimension: |S1| = dim (Z/2Z)^S1 = dim (Z/2Z)^S2 = |S2|.
     Step 4: Hence |S1| = |S2|, i.e. there exists a bijection.\<close>
  \<comment> \<open>Munkres 67.8: G/2G has cardinality 2^|S| for any basis S.
     So 2^|S1| = |G/2G| = 2^|S2|, hence |S1| = |S2|.\<close>
  let ?twoG = "{mul g g | g. g \<in> G}"
  \<comment> \<open>Step 1: |G/2G| = 2^|S1| and |G/2G| = 2^|S2|.
     Proof: G \<cong> Z^S_i, so G/2G \<cong> (Z/2Z)^S_i, hence |G/2G| = 2^|S_i|.\<close>
  have hfinS1: "finite S1" by (rule assms(3))
  have hfinS2: "finite S2" by (rule assms(4))
  \<comment> \<open>Helper: for free abelian G on finite basis S, |G/2G| = 2^|S|.\<close>
  have hcard_helper: "\<And>S iota. top1_is_free_abelian_group_full_on G mul e invg iota S \<Longrightarrow>
      finite S \<Longrightarrow>
      card (top1_quotient_group_carrier_on G mul ?twoG) = 2 ^ card S"
    by (rule free_abelian_mod2_card)
  have hcard1: "card (top1_quotient_group_carrier_on G mul ?twoG) = 2 ^ card S1"
    by (rule hcard_helper[OF assms(1) hfinS1])
  have hcard2: "card (top1_quotient_group_carrier_on G mul ?twoG) = 2 ^ card S2"
    by (rule hcard_helper[OF assms(2) hfinS2])
  \<comment> \<open>Step 2: 2^|S1| = 2^|S2| implies |S1| = |S2|.\<close>
  have "card S1 = card S2"
  proof -
    have "2 ^ card S1 = (2::nat) ^ card S2" using hcard1 hcard2 by (by100 simp)
    thus ?thesis by (by100 simp)
  qed
  \<comment> \<open>Step 3: Finite sets of equal cardinality have a bijection.\<close>
  show ?thesis by (rule finite_same_card_bij[OF hfinS1 hfinS2 \<open>card S1 = card S2\<close>])
qed


end
