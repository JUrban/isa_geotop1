theory AlgTop0
  imports "AlgTopBase.AlgTop_JCT_Base"
begin

section \<open>\<S>63 The Jordan Curve Theorem\<close>

\<comment> \<open>top1_simple_closed_curve_on defined earlier (before \<S>61).\<close>

\<comment> \<open>Helix covering construction: provides E, TE, p0 for both 63.1(a) and g-lift.\<close>
lemma helix_covering_construction:
  assumes "is_topology_on X TX"
      and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
  defines "E \<equiv> {(x::('a \<times> int)). (even (snd x) \<and> fst x \<in> U) \<or> (odd (snd x) \<and> fst x \<in> V - U)}"
  defines "TE \<equiv> {W. W \<subseteq> E \<and>
        (\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX) \<and>
        (\<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX)}"
  defines "p0 \<equiv> (fst :: ('a \<times> int) \<Rightarrow> 'a)"
  shows "top1_covering_map_on E TE X TX p0 \<and> is_topology_on E TE"
proof -
    have hU_TX: "U \<in> TX" using assms(2) unfolding openin_on_def by (by100 blast)
    have hV_TX: "V \<in> TX" using assms(3) unfolding openin_on_def by (by100 blast)
    have hA_TX: "A \<in> TX" using assms(7) unfolding openin_on_def by (by100 blast)
    have hB_TX: "B \<in> TX" using assms(8) unfolding openin_on_def by (by100 blast)
    have hAB: "A \<union> B = U \<inter> V" using assms(5) by simp
    have hTX_empty: "{} \<in> TX" using assms(1) unfolding is_topology_on_def by (by100 blast)
    have hTE: "is_topology_on E TE"
      unfolding is_topology_on_def
    proof (intro conjI allI impI)
      show "{} \<in> TE" unfolding TE_def using hTX_empty by simp
      show "E \<in> TE" unfolding TE_def
      proof (intro CollectI conjI allI)
        show "E \<subseteq> E" by simp
        fix n :: int
        show "{x \<in> U. (x, 2*n) \<in> E} \<in> TX"
          unfolding E_def using hU_TX by auto
        have "{x \<in> A. (x, 2*n+2) \<in> E} = A"
          unfolding E_def using hAB by auto
        moreover have "{x \<in> B. (x, 2*n) \<in> E} = B"
          unfolding E_def using hAB by auto
        moreover have "{x \<in> V-U. (x, 2*n+1) \<in> E} = V - U"
          unfolding E_def by auto
        moreover have "A \<union> B \<union> (V - U) = V" using hAB by (by100 blast)
        ultimately show "{x \<in> A. (x, 2*n+2) \<in> E} \<union> {x \<in> B. (x, 2*n) \<in> E} \<union> {x \<in> V-U. (x, 2*n+1) \<in> E} \<in> TX"
          using hV_TX by simp
      qed
    next
      fix U0 :: "('a \<times> int) set set" assume hU0: "U0 \<subseteq> TE"
      show "\<Union>U0 \<in> TE" unfolding TE_def
      proof (intro CollectI conjI allI)
        show "\<Union>U0 \<subseteq> E" using hU0 unfolding TE_def by (by100 blast)
        fix n :: int
        have heven_eq: "{x \<in> U. (x, 2*n) \<in> \<Union>U0} = \<Union>{{x \<in> U. (x, 2*n) \<in> W} | W. W \<in> U0}"
          by (by100 blast)
        have "{{x \<in> U. (x, 2*n) \<in> W} | W. W \<in> U0} \<subseteq> TX"
          using hU0 unfolding TE_def by (by100 blast)
        hence "\<Union>{{x \<in> U. (x, 2*n) \<in> W} | W. W \<in> U0} \<in> TX"
          using assms(1) unfolding is_topology_on_def by (by100 blast)
        thus "{x \<in> U. (x, 2*n) \<in> \<Union>U0} \<in> TX" using heven_eq by simp
        have hodd_eq: "{x \<in> A. (x, 2*n+2) \<in> \<Union>U0} \<union> {x \<in> B. (x, 2*n) \<in> \<Union>U0} \<union>
            {x \<in> V-U. (x, 2*n+1) \<in> \<Union>U0}
            = \<Union>{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> U0}" by (by100 blast)
        have "{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> U0} \<subseteq> TX"
          using hU0 unfolding TE_def by (by100 blast)
        hence "\<Union>{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> U0} \<in> TX"
          using assms(1) unfolding is_topology_on_def by (by100 blast)
        thus "{x \<in> A. (x, 2*n+2) \<in> \<Union>U0} \<union> {x \<in> B. (x, 2*n) \<in> \<Union>U0} \<union>
            {x \<in> V-U. (x, 2*n+1) \<in> \<Union>U0} \<in> TX" using hodd_eq by simp
      qed
    next
      fix F :: "('a \<times> int) set set" assume hF: "finite F \<and> F \<noteq> {} \<and> F \<subseteq> TE"
      have hTX_fin_inter: "\<And>G. finite G \<Longrightarrow> G \<noteq> {} \<Longrightarrow> G \<subseteq> TX \<Longrightarrow> \<Inter>G \<in> TX"
        using assms(1) unfolding is_topology_on_def by (by100 blast)
      show "\<Inter>F \<in> TE" unfolding TE_def
      proof (intro CollectI conjI allI)
        show "\<Inter>F \<subseteq> E" using hF unfolding TE_def by (by100 blast)
        fix n :: int
        have "{x \<in> U. (x, 2*n) \<in> \<Inter>F} = \<Inter>{{x \<in> U. (x, 2*n) \<in> W} | W. W \<in> F}"
          using hF by (by100 blast)
        moreover have "... \<in> TX"
        proof -
          have heven_fin: "finite {{x \<in> U. (x, 2*n) \<in> W} | W. W \<in> F}" using hF by simp
          have heven_ne: "{{x \<in> U. (x, 2*n) \<in> W} | W. W \<in> F} \<noteq> {}" using hF by (by100 blast)
          have heven_sub: "{{x \<in> U. (x, 2*n) \<in> W} | W. W \<in> F} \<subseteq> TX"
            using hF unfolding TE_def by (by100 blast)
          have "\<Inter>{{x \<in> U. (x, 2*n) \<in> W} | W. W \<in> F} \<in> TX"
            by (rule hTX_fin_inter[OF heven_fin heven_ne heven_sub])
          thus ?thesis .
        qed
        ultimately show "{x \<in> U. (x, 2*n) \<in> \<Inter>F} \<in> TX" by simp
        have heq: "{x \<in> A. (x, 2*n+2) \<in> \<Inter>F} \<union> {x \<in> B. (x, 2*n) \<in> \<Inter>F} \<union>
            {x \<in> V-U. (x, 2*n+1) \<in> \<Inter>F}
            = \<Inter>{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> F}"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> {x \<in> A. (x, 2*n+2) \<in> \<Inter>F} \<union> {x \<in> B. (x, 2*n) \<in> \<Inter>F} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> \<Inter>F}"
          thus "x \<in> \<Inter>{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> F}" by (by100 blast)
        next
          fix x assume hx: "x \<in> \<Inter>{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> F}"
          from hF obtain W0 where "W0 \<in> F" by (by100 blast)
          hence "x \<in> {x \<in> A. (x, 2*n+2) \<in> W0} \<union> {x \<in> B. (x, 2*n) \<in> W0} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> W0}" using hx by (by100 blast)
          hence hcases: "x \<in> A \<or> x \<in> B \<or> x \<in> V - U" by (by100 blast)
          have hAllW: "\<forall>W\<in>F. x \<in> {x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> W}" using hx by (by100 blast)
          show "x \<in> {x \<in> A. (x, 2*n+2) \<in> \<Inter>F} \<union> {x \<in> B. (x, 2*n) \<in> \<Inter>F} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> \<Inter>F}"
          proof -
            { assume hxA: "x \<in> A"
              hence "x \<notin> B" using assms(6) by (by100 blast)
              hence hxnVU: "x \<notin> V - U" using assms(5) hxA by (by100 blast)
              have "\<forall>W\<in>F. x \<in> {x \<in> A. (x, 2*n+2) \<in> W}"
                using hAllW hxA \<open>x \<notin> B\<close> hxnVU by (by100 fast)
              hence "\<forall>W\<in>F. (x, 2*n+2) \<in> W" by (by100 blast)
              hence "x \<in> {x \<in> A. (x, 2*n+2) \<in> \<Inter>F}" using \<open>x \<in> A\<close> by (by100 blast)
              hence ?thesis by (by100 blast) }
            moreover
            { assume hxB: "x \<in> B"
              hence "x \<notin> A" using assms(6) by (by100 blast)
              hence hxnVU: "x \<notin> V - U" using assms(5) hxB by (by100 blast)
              have "\<forall>W\<in>F. x \<in> {x \<in> B. (x, 2*n) \<in> W}"
                using hAllW hxB \<open>x \<notin> A\<close> hxnVU by (by100 fast)
              hence "\<forall>W\<in>F. (x, 2*n) \<in> W" by (by100 blast)
              hence "x \<in> {x \<in> B. (x, 2*n) \<in> \<Inter>F}" using \<open>x \<in> B\<close> by (by100 blast)
              hence ?thesis by (by100 blast) }
            moreover
            { assume hxVU: "x \<in> V - U"
              hence "x \<notin> A" "x \<notin> B" using assms(5) by (by100 blast)+
              have "\<forall>W\<in>F. x \<in> {x \<in> V-U. (x, 2*n+1) \<in> W}"
                using hAllW hxVU \<open>x \<notin> A\<close> \<open>x \<notin> B\<close> by (by100 fast)
              hence "\<forall>W\<in>F. (x, 2*n+1) \<in> W" by (by100 blast)
              hence "x \<in> {x \<in> V-U. (x, 2*n+1) \<in> \<Inter>F}" using \<open>x \<in> V - U\<close> by (by100 blast)
              hence ?thesis by (by100 blast) }
            ultimately show ?thesis using hcases by (by100 fast)
          qed
        qed
        have "\<Inter>{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> F} \<in> TX"
        proof -
          have hodd_fin: "finite {{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> F}" using hF by simp
          have hodd_ne: "{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> F} \<noteq> {}" using hF by (by100 blast)
          have hodd_sub: "{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> F} \<subseteq> TX"
            using hF unfolding TE_def by (by100 blast)
          have "\<Inter>{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> F} \<in> TX"
            by (rule hTX_fin_inter[OF hodd_fin hodd_ne hodd_sub])
          thus ?thesis .
        qed
        thus "{x \<in> A. (x, 2*n+2) \<in> \<Inter>F} \<union> {x \<in> B. (x, 2*n) \<in> \<Inter>F} \<union>
            {x \<in> V-U. (x, 2*n+1) \<in> \<Inter>F} \<in> TX" using heq by simp
      qed
    qed
    have hcov: "top1_covering_map_on E TE X TX p0"
      unfolding top1_covering_map_on_def
    proof (intro conjI)
      show "top1_continuous_map_on E TE X TX p0"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix e assume "e \<in> E"
        thus "p0 e \<in> X" unfolding p0_def E_def using assms(2,3,4) unfolding openin_on_def by auto
      next
        fix W assume hW: "W \<in> TX"
        show "{e \<in> E. p0 e \<in> W} \<in> TE" unfolding TE_def
        proof (intro CollectI conjI allI)
          show "{e \<in> E. p0 e \<in> W} \<subseteq> E" by (by100 blast)
          fix n :: int
          have "{x \<in> U. (x, 2*n) \<in> {e \<in> E. p0 e \<in> W}} = U \<inter> W"
            unfolding p0_def E_def by auto
          thus "{x \<in> U. (x, 2*n) \<in> {e \<in> E. p0 e \<in> W}} \<in> TX"
            using topology_inter_open[OF assms(1) hU_TX hW] by simp
          have h1: "{x \<in> A. (x, 2*n+2) \<in> {e \<in> E. p0 e \<in> W}} = A \<inter> W"
            unfolding p0_def E_def using hAB by auto
          have h2: "{x \<in> B. (x, 2*n) \<in> {e \<in> E. p0 e \<in> W}} = B \<inter> W"
            unfolding p0_def E_def using hAB by auto
          have h3: "{x \<in> V-U. (x, 2*n+1) \<in> {e \<in> E. p0 e \<in> W}} = (V-U) \<inter> W"
            unfolding p0_def E_def by auto
          have "(A \<inter> W) \<union> (B \<inter> W) \<union> ((V-U) \<inter> W) = V \<inter> W" using hAB by (by100 blast)
          moreover have "V \<inter> W \<in> TX"
            by (rule topology_inter_open[OF assms(1) hV_TX hW])
          ultimately show "{x \<in> A. (x, 2*n+2) \<in> {e \<in> E. p0 e \<in> W}} \<union>
              {x \<in> B. (x, 2*n) \<in> {e \<in> E. p0 e \<in> W}} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> {e \<in> E. p0 e \<in> W}} \<in> TX"
            using h1 h2 h3 by simp
        qed
      qed
    next
      show "p0 ` E = X"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> p0 ` E"
        thus "x \<in> X" unfolding p0_def E_def using assms(2,3,4) unfolding openin_on_def by auto
      next
        fix x assume "x \<in> X"
        hence "x \<in> U \<or> x \<in> V - U" using assms(4) by (by100 blast)
        thus "x \<in> p0 ` E"
        proof
          assume "x \<in> U"
          hence "(x, 0::int) \<in> E" unfolding E_def by simp
          thus ?thesis unfolding p0_def by (by100 force)
        next
          assume "x \<in> V - U"
          hence "(x, 1::int) \<in> E" unfolding E_def by simp
          thus ?thesis unfolding p0_def by (by100 force)
        qed
      qed
    next
      show "\<forall>b\<in>X. \<exists>Ub. b \<in> Ub \<and> top1_evenly_covered_on E TE X TX p0 Ub"
      proof
        fix b assume "b \<in> X"
        hence "b \<in> U \<or> b \<in> V - U" using assms(4) by (by100 blast)
        thus "\<exists>Ub. b \<in> Ub \<and> top1_evenly_covered_on E TE X TX p0 Ub"
        proof
          assume "b \<in> U"
          let ?\<V> = "(\<lambda>n::int. U \<times> {2*n}) ` UNIV"
          show ?thesis
          proof (intro exI[of _ U] conjI)
            show "b \<in> U" by (rule \<open>b \<in> U\<close>)
            show "top1_evenly_covered_on E TE X TX p0 U"
              unfolding top1_evenly_covered_on_def
            proof (intro conjI exI[of _ ?\<V>])
              show "openin_on X TX U" by (rule assms(2))
              \<comment> \<open>U-sheets open in TE.\<close>
              show "\<forall>V\<in>?\<V>. openin_on E TE V"
              proof
                fix Sn assume "Sn \<in> ?\<V>"
                then obtain k where hSn: "Sn = U \<times> {2*k}" by auto
                show "openin_on E TE Sn" unfolding openin_on_def
                proof (intro conjI)
                  show "Sn \<subseteq> E" unfolding hSn E_def by auto
                  show "Sn \<in> TE" unfolding TE_def hSn
                  proof (intro CollectI conjI allI)
                    show "U \<times> {2*k} \<subseteq> E" unfolding E_def by auto
                    fix m :: int
                    have "{x \<in> U. (x, 2*m) \<in> U \<times> {2*k}} = (if m = k then U else {})" by auto
                    thus "{x \<in> U. (x, 2*m) \<in> U \<times> {2*k}} \<in> TX"
                      using hU_TX hTX_empty by simp
                    have hA: "{x \<in> A. (x, 2*m+2) \<in> U \<times> {2*k}} = (if m+1=k then A else {})"
                      using hAB by auto
                    have hB: "{x \<in> B. (x, 2*m) \<in> U \<times> {2*k}} = (if m=k then B else {})"
                      using hAB by auto
                    have hVU: "{x \<in> V-U. (x, 2*m+1) \<in> U \<times> {2*k}} = {}" by auto
                    have hresult: "(if m+1=k then A else {}) \<union> (if m=k then B else {}) \<union> {} \<in> TX"
                    proof -
                      have "(if m+1=k then A else {}) \<in> TX" using hA_TX hTX_empty by simp
                      moreover have "(if m=k then B else {}) \<in> TX" using hB_TX hTX_empty by simp
                      moreover have "{} \<in> TX" by (rule hTX_empty)
                      ultimately have "{(if m+1=k then A else {}), (if m=k then B else {}), {}} \<subseteq> TX"
                        by (by100 blast)
                      hence "\<Union>{(if m+1=k then A else {}), (if m=k then B else {}), {}} \<in> TX"
                        using assms(1) unfolding is_topology_on_def by (by100 blast)
                      thus ?thesis by (by100 simp)
                    qed
                    have "{x \<in> A. (x, 2*m+2) \<in> U \<times> {2*k}} \<union>
                        {x \<in> B. (x, 2*m) \<in> U \<times> {2*k}} \<union>
                        {x \<in> V-U. (x, 2*m+1) \<in> U \<times> {2*k}}
                        = (if m+1=k then A else {}) \<union> (if m=k then B else {}) \<union> {}"
                      using hA hB hVU by presburger
                    thus "{x \<in> A. (x, 2*m+2) \<in> U \<times> {2*k}} \<union>
                        {x \<in> B. (x, 2*m) \<in> U \<times> {2*k}} \<union>
                        {x \<in> V-U. (x, 2*m+1) \<in> U \<times> {2*k}} \<in> TX"
                      using hresult by simp
                  qed
                qed
              qed
              show "\<forall>V\<in>?\<V>. \<forall>V'\<in>?\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}" by force
              \<comment> \<open>Union = p0\<inverse>(U).\<close>
              show "{x \<in> E. p0 x \<in> U} = \<Union>?\<V>"
              proof (rule set_eqI, rule iffI)
                fix e assume "e \<in> {x \<in> E. p0 x \<in> U}"
                hence "e \<in> E" "fst e \<in> U" unfolding p0_def by auto
                hence "even (snd e)" unfolding E_def by auto
                then obtain k where "snd e = 2 * k" using evenE by auto
                hence "e \<in> U \<times> {2*k}" using \<open>fst e \<in> U\<close> by (cases e) auto
                thus "e \<in> \<Union>?\<V>" by (by100 blast)
              next
                fix e assume "e \<in> \<Union>?\<V>"
                then obtain n where "e \<in> U \<times> {2*n}" by (by100 blast)
                hence "e \<in> E" "p0 e \<in> U" unfolding E_def p0_def by auto
                thus "e \<in> {x \<in> E. p0 x \<in> U}" by simp
              qed
              \<comment> \<open>Sheet homeomorphisms.\<close>
              show "\<forall>V\<in>?\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                  (subspace_topology X TX U) p0"
              proof
                fix Sn assume "Sn \<in> ?\<V>"
                then obtain k where hSn: "Sn = U \<times> {2*k}" by auto
                have hSn_sub: "Sn \<subseteq> E" unfolding hSn E_def by auto
                have hU_sub: "U \<subseteq> X" using assms(2) unfolding openin_on_def by (by100 blast)
                show "top1_homeomorphism_on Sn (subspace_topology E TE Sn) U
                    (subspace_topology X TX U) p0"
                  unfolding top1_homeomorphism_on_def
                proof (intro conjI)
                  show "is_topology_on Sn (subspace_topology E TE Sn)"
                    by (rule subspace_topology_is_topology_on[OF hTE hSn_sub])
                  show "is_topology_on U (subspace_topology X TX U)"
                    by (rule subspace_topology_is_topology_on[OF assms(1) hU_sub])
                  show "bij_betw p0 Sn U" unfolding bij_betw_def p0_def hSn
                    by (intro conjI inj_onI, auto)
                  \<comment> \<open>p0 continuous.\<close>
                  show "top1_continuous_map_on Sn (subspace_topology E TE Sn) U
                      (subspace_topology X TX U) p0"
                    unfolding top1_continuous_map_on_def
                  proof (intro conjI ballI)
                    fix e assume "e \<in> Sn" thus "p0 e \<in> U" unfolding hSn p0_def by auto
                  next
                    fix W assume "W \<in> subspace_topology X TX U"
                    then obtain W0 where "W0 \<in> TX" "W = U \<inter> W0"
                      unfolding subspace_topology_def by (by100 blast)
                    define W' where "W' = {e \<in> E. p0 e \<in> W}"
                    have "W' \<in> TE" unfolding TE_def W'_def
                    proof (intro CollectI conjI allI)
                      show "{e \<in> E. p0 e \<in> W} \<subseteq> E" by (by100 blast)
                      fix m :: int
                      have hW_sub: "W \<subseteq> U" using \<open>W = U \<inter> W0\<close> by (by100 blast)
                      show "{x \<in> U. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} \<in> TX"
                      proof -
                        have "{x \<in> U. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} = U \<inter> W"
                          unfolding p0_def E_def by auto
                        moreover have "U \<inter> W = W" using hW_sub by (by100 blast)
                        moreover have "W \<in> TX"
                        proof -
                          have "U \<inter> W0 \<in> TX" by (rule topology_inter_open[OF assms(1) hU_TX \<open>W0 \<in> TX\<close>])
                          thus ?thesis using \<open>W = U \<inter> W0\<close> by simp
                        qed
                        ultimately show ?thesis by simp
                      qed
                      show "{x \<in> A. (x, 2*m+2) \<in> {e \<in> E. p0 e \<in> W}} \<union>
                          {x \<in> B. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} \<union>
                          {x \<in> V-U. (x, 2*m+1) \<in> {e \<in> E. p0 e \<in> W}} \<in> TX"
                      proof -
                        have h1: "{x \<in> A. (x, 2*m+2) \<in> {e \<in> E. p0 e \<in> W}} = A \<inter> W"
                          unfolding p0_def E_def using hAB by auto
                        have h2: "{x \<in> B. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} = B \<inter> W"
                          unfolding p0_def E_def using hAB by auto
                        have h3: "{x \<in> V-U. (x, 2*m+1) \<in> {e \<in> E. p0 e \<in> W}} = {}"
                          unfolding p0_def E_def using hW_sub by auto
                        have hW_TX: "W \<in> TX"
                        proof -
                          have "U \<inter> W0 \<in> TX" by (rule topology_inter_open[OF assms(1) hU_TX \<open>W0 \<in> TX\<close>])
                          thus ?thesis using \<open>W = U \<inter> W0\<close> by simp
                        qed
                        have "V \<inter> W \<in> TX" by (rule topology_inter_open[OF assms(1) hV_TX hW_TX])
                        moreover have "{x \<in> A. (x, 2*m+2) \<in> {e \<in> E. p0 e \<in> W}} \<union>
                            {x \<in> B. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} \<union>
                            {x \<in> V-U. (x, 2*m+1) \<in> {e \<in> E. p0 e \<in> W}} = V \<inter> W"
                        proof -
                          have "(A \<inter> W) \<union> (B \<inter> W) \<union> {} = V \<inter> W"
                            using hAB hW_sub by (by100 blast)
                          thus ?thesis using h1 h2 h3 by presburger
                        qed
                        ultimately show ?thesis by simp
                      qed
                    qed
                    moreover have "{e \<in> Sn. p0 e \<in> W} = Sn \<inter> W'"
                      unfolding W'_def using hSn_sub by (by100 blast)
                    ultimately show "{e \<in> Sn. p0 e \<in> W} \<in> subspace_topology E TE Sn"
                      unfolding subspace_topology_def by (by100 blast)
                  qed
                  \<comment> \<open>Inverse continuous.\<close>
                  show "top1_continuous_map_on U (subspace_topology X TX U) Sn
                      (subspace_topology E TE Sn) (inv_into Sn p0)"
                    unfolding top1_continuous_map_on_def
                  proof (intro conjI ballI)
                    fix x assume "x \<in> U"
                    have "inv_into Sn p0 x = (x, 2*k)"
                    proof (rule inv_into_f_eq)
                      show "inj_on p0 Sn" unfolding p0_def hSn by (intro inj_onI) auto
                      show "(x, 2*k) \<in> Sn" unfolding hSn using \<open>x \<in> U\<close> by simp
                      show "p0 (x, 2*k) = x" unfolding p0_def by simp
                    qed
                    thus "inv_into Sn p0 x \<in> Sn" unfolding hSn using \<open>x \<in> U\<close> by simp
                  next
                    fix W assume "W \<in> subspace_topology E TE Sn"
                    then obtain W' where "W' \<in> TE" "W = Sn \<inter> W'"
                      unfolding subspace_topology_def by (by100 blast)
                    have hinj: "inj_on p0 Sn" unfolding p0_def hSn by (intro inj_onI) auto
                    have hslice: "{x \<in> U. (x, 2*k) \<in> W'} \<in> TX"
                    proof -
                      have "\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W'} \<in> TX"
                        using \<open>W' \<in> TE\<close> unfolding TE_def by (by100 blast)
                      hence "{x \<in> U. (x, 2*k) \<in> W'} \<in> TX" by (rule spec)
                      thus ?thesis .
                    qed
                    have "{x \<in> U. inv_into Sn p0 x \<in> W} = {x \<in> U. (x, 2*k) \<in> W'}"
                    proof (rule set_eqI, rule iffI)
                      fix x assume "x \<in> {x \<in> U. inv_into Sn p0 x \<in> W}"
                      hence "x \<in> U" "inv_into Sn p0 x \<in> W" by auto
                      have "inv_into Sn p0 x = (x, 2*k)"
                        by (rule inv_into_f_eq[OF hinj]) (simp_all add: hSn p0_def \<open>x \<in> U\<close>)
                      thus "x \<in> {x \<in> U. (x, 2*k) \<in> W'}"
                        using \<open>inv_into Sn p0 x \<in> W\<close> \<open>W = Sn \<inter> W'\<close> hSn \<open>x \<in> U\<close> by auto
                    next
                      fix x assume "x \<in> {x \<in> U. (x, 2*k) \<in> W'}"
                      hence "x \<in> U" "(x, 2*k) \<in> W'" by auto
                      have "inv_into Sn p0 x = (x, 2*k)"
                        by (rule inv_into_f_eq[OF hinj]) (simp_all add: hSn p0_def \<open>x \<in> U\<close>)
                      have "inv_into Sn p0 x \<in> W'"
                        using \<open>inv_into Sn p0 x = (x, 2*k)\<close> \<open>(x, 2*k) \<in> W'\<close> by simp
                      moreover have "inv_into Sn p0 x \<in> Sn"
                        using \<open>inv_into Sn p0 x = (x, 2*k)\<close> hSn \<open>x \<in> U\<close> by simp
                      ultimately have "inv_into Sn p0 x \<in> W"
                        using \<open>W = Sn \<inter> W'\<close> by (by100 blast)
                      thus "x \<in> {x \<in> U. inv_into Sn p0 x \<in> W}" using \<open>x \<in> U\<close> by simp
                    qed
                    moreover have "{x \<in> U. (x, 2*k) \<in> W'} \<in> subspace_topology X TX U"
                      using hslice unfolding subspace_topology_def by (by100 blast)
                    ultimately show "{x \<in> U. inv_into Sn p0 x \<in> W} \<in> subspace_topology X TX U"
                      by simp
                  qed
                qed
              qed
            qed
          qed
        next
          assume "b \<in> V - U"
          \<comment> \<open>V evenly covered. V-sheets defined via vsheet.\<close>
          define vsheet :: "int \<Rightarrow> ('a \<times> int) set" where
            "vsheet = (\<lambda>n. {e \<in> E. fst e \<in> V \<and>
              (fst e \<in> A \<and> snd e = 2*(n+1) \<or> fst e \<in> B \<and> snd e = 2*n \<or> fst e \<in> V - U \<and> snd e = 2*n+1)})"
          let ?\<V>V = "vsheet ` UNIV"
          show ?thesis
          proof (intro exI[of _ V] conjI)
            show "b \<in> V" using \<open>b \<in> V - U\<close> by (by100 blast)
            show "top1_evenly_covered_on E TE X TX p0 V"
              unfolding top1_evenly_covered_on_def
            proof (intro conjI exI[of _ ?\<V>V])
              show "openin_on X TX V" by (rule assms(3))
              show hVsheets_open: "\<forall>Vn\<in>?\<V>V. openin_on E TE Vn"
              proof
                fix Sn assume "Sn \<in> ?\<V>V"
                then obtain k where hSn: "Sn = vsheet k" by (by100 blast)
                show "openin_on E TE Sn" unfolding openin_on_def
                proof (intro conjI)
                  show "Sn \<subseteq> E" unfolding hSn vsheet_def by (by100 blast)
                  show "Sn \<in> TE" unfolding TE_def hSn
                  proof (intro CollectI conjI allI)
                    show "vsheet k \<subseteq> E" unfolding vsheet_def by (by100 blast)
                    fix m :: int
                    \<comment> \<open>Even slice: {x \<in> U. (x,2m) \<in> vsheet k} = A if m=k+1, B if m=k, else {}.\<close>
                    have heven: "{x \<in> U. (x, 2*m) \<in> vsheet k} =
                        (if m = k+1 then A else if m = k then B else {})"
                      unfolding vsheet_def E_def using hAB assms(6) by auto
                    show "{x \<in> U. (x, 2*m) \<in> vsheet k} \<in> TX"
                    proof -
                      have "(if m=k+1 then A else if m=k then B else {}) \<in> TX"
                        using hA_TX hB_TX hTX_empty by simp
                      thus ?thesis using heven by simp
                    qed
                    \<comment> \<open>Odd slice: at m=k gives V, else {}.\<close>
                    have hodd_A: "{x \<in> A. (x, 2*m+2) \<in> vsheet k} = (if m=k then A else {})"
                      unfolding vsheet_def E_def using hAB assms(6) by auto
                    have hodd_B: "{x \<in> B. (x, 2*m) \<in> vsheet k} = (if m=k then B else {})"
                      unfolding vsheet_def E_def using hAB assms(6) by auto
                    have hodd_VU: "{x \<in> V-U. (x, 2*m+1) \<in> vsheet k} = (if m=k then V-U else {})"
                      unfolding vsheet_def E_def by auto
                    have hodd_eq: "(if m=k then A else {}) \<union> (if m=k then B else {}) \<union>
                        (if m=k then V-U else {}) = (if m=k then V else {})"
                      using hAB by auto
                    show "{x \<in> A. (x, 2*m+2) \<in> vsheet k} \<union>
                        {x \<in> B. (x, 2*m) \<in> vsheet k} \<union>
                        {x \<in> V-U. (x, 2*m+1) \<in> vsheet k} \<in> TX"
                    proof -
                      have "(if m=k then V else {}) \<in> TX" using hV_TX hTX_empty by simp
                      thus ?thesis using hodd_A hodd_B hodd_VU hodd_eq by presburger
                    qed
                  qed
                qed
              qed
              show "\<forall>Vn\<in>?\<V>V. \<forall>Vn'\<in>?\<V>V. Vn \<noteq> Vn' \<longrightarrow> Vn \<inter> Vn' = {}"
              proof (intro ballI impI)
                fix S1 S2 assume "S1 \<in> ?\<V>V" "S2 \<in> ?\<V>V" "S1 \<noteq> S2"
                then obtain n1 n2 where hS: "S1 = vsheet n1" "S2 = vsheet n2" by (by100 blast)
                have "n1 \<noteq> n2" using \<open>S1 \<noteq> S2\<close> hS by auto
                show "S1 \<inter> S2 = {}"
                proof (rule ccontr)
                  assume "S1 \<inter> S2 \<noteq> {}"
                  then obtain e where "e \<in> S1" "e \<in> S2" by (by100 blast)
                  hence "fst e \<in> A \<and> snd e = 2*(n1+1) \<or> fst e \<in> B \<and> snd e = 2*n1 \<or>
                      fst e \<in> V-U \<and> snd e = 2*n1+1"
                    "fst e \<in> A \<and> snd e = 2*(n2+1) \<or> fst e \<in> B \<and> snd e = 2*n2 \<or>
                      fst e \<in> V-U \<and> snd e = 2*n2+1"
                    unfolding hS vsheet_def by auto
                  thus False using \<open>n1 \<noteq> n2\<close> assms(6) hAB by auto
                qed
              qed
              show "{x \<in> E. p0 x \<in> V} = \<Union>?\<V>V"
              proof (rule set_eqI, rule iffI)
                fix e assume "e \<in> {x \<in> E. p0 x \<in> V}"
                hence he: "e \<in> E" "fst e \<in> V" unfolding p0_def by auto
                have "fst e \<in> A \<or> fst e \<in> B \<or> fst e \<in> V - U" using he(2) hAB by (by100 blast)
                thus "e \<in> \<Union>?\<V>V"
                proof (elim disjE)
                  assume "fst e \<in> A"
                  hence "even (snd e)" using he(1) unfolding E_def using hAB by auto
                  then obtain k where "snd e = 2 * k" using evenE by auto
                  have "e \<in> vsheet (k - 1)" unfolding vsheet_def
                    using he \<open>fst e \<in> A\<close> \<open>snd e = 2*k\<close> by (cases e) auto
                  thus ?thesis by (by100 blast)
                next
                  assume "fst e \<in> B"
                  hence "even (snd e)" using he(1) unfolding E_def using hAB by auto
                  then obtain k where "snd e = 2 * k" using evenE by auto
                  have "e \<in> vsheet k" unfolding vsheet_def
                    using he \<open>fst e \<in> B\<close> \<open>snd e = 2*k\<close> by (cases e) auto
                  thus ?thesis by (by100 blast)
                next
                  assume "fst e \<in> V - U"
                  hence "odd (snd e)" using he(1) unfolding E_def by auto
                  then obtain k where "snd e = 2 * k + 1" using oddE by auto
                  have "e \<in> vsheet k" unfolding vsheet_def
                    using he \<open>fst e \<in> V - U\<close> \<open>snd e = 2*k+1\<close> by (cases e) auto
                  thus ?thesis by (by100 blast)
                qed
              next
                fix e assume "e \<in> \<Union>?\<V>V"
                then obtain n where "e \<in> vsheet n" by (by100 blast)
                hence "e \<in> E" "fst e \<in> V" unfolding vsheet_def by auto
                thus "e \<in> {x \<in> E. p0 x \<in> V}" unfolding p0_def by simp
              qed
              show "\<forall>Vn\<in>?\<V>V. top1_homeomorphism_on Vn (subspace_topology E TE Vn) V
                  (subspace_topology X TX V) p0"
              proof
                fix Sn assume "Sn \<in> ?\<V>V"
                then obtain k where hSn: "Sn = vsheet k" by (by100 blast)
                have hSn_sub: "Sn \<subseteq> E" unfolding hSn vsheet_def by (by100 blast)
                have hV_sub: "V \<subseteq> X" using assms(3) unfolding openin_on_def by (by100 blast)
                have hbij: "bij_betw p0 Sn V" unfolding bij_betw_def
                proof (intro conjI)
                  show "inj_on p0 Sn" unfolding p0_def hSn
                  proof (intro inj_onI)
                    fix e1 e2 assume he1: "e1 \<in> vsheet k" and he2: "e2 \<in> vsheet k"
                        and hfst: "fst e1 = fst e2"
                    have h1: "fst e1 \<in> A \<and> snd e1 = 2*(k+1) \<or> fst e1 \<in> B \<and> snd e1 = 2*k \<or>
                        fst e1 \<in> V-U \<and> snd e1 = 2*k+1"
                      using he1 unfolding vsheet_def by auto
                    have h2: "fst e2 \<in> A \<and> snd e2 = 2*(k+1) \<or> fst e2 \<in> B \<and> snd e2 = 2*k \<or>
                        fst e2 \<in> V-U \<and> snd e2 = 2*k+1"
                      using he2 unfolding vsheet_def by auto
                    have "snd e1 = snd e2" using h1 h2 hfst assms(6) hAB by auto
                    thus "e1 = e2" using hfst by (cases e1, cases e2) auto
                  qed
                  show "p0 ` Sn = V"
                  proof (rule set_eqI, rule iffI)
                    fix x assume "x \<in> p0 ` Sn"
                    thus "x \<in> V" unfolding p0_def hSn vsheet_def by auto
                  next
                    fix x assume "x \<in> V"
                    hence "x \<in> A \<or> x \<in> B \<or> x \<in> V - U" using hAB by (by100 blast)
                    thus "x \<in> p0 ` Sn"
                    proof (elim disjE)
                      assume "x \<in> A"
                      hence "(x, 2*(k+1)) \<in> vsheet k" unfolding vsheet_def E_def
                        using \<open>x \<in> V\<close> hAB by auto
                      thus ?thesis unfolding p0_def hSn by force
                    next
                      assume "x \<in> B"
                      hence "(x, 2*k) \<in> vsheet k" unfolding vsheet_def E_def
                        using \<open>x \<in> V\<close> hAB by auto
                      thus ?thesis unfolding p0_def hSn by force
                    next
                      assume "x \<in> V - U"
                      hence "(x, 2*k+1) \<in> vsheet k" unfolding vsheet_def E_def
                        using \<open>x \<in> V\<close> by auto
                      thus ?thesis unfolding p0_def hSn by force
                    qed
                  qed
                qed
                have hp0_img: "p0 ` Sn = V" using hbij unfolding bij_betw_def by (by100 blast)
                have hinj: "inj_on p0 Sn" using hbij unfolding bij_betw_def by (by100 blast)
                show "top1_homeomorphism_on Sn (subspace_topology E TE Sn) V
                    (subspace_topology X TX V) p0"
                  unfolding top1_homeomorphism_on_def
                proof (intro conjI)
                  show "is_topology_on Sn (subspace_topology E TE Sn)"
                    by (rule subspace_topology_is_topology_on[OF hTE hSn_sub])
                  show "is_topology_on V (subspace_topology X TX V)"
                    by (rule subspace_topology_is_topology_on[OF assms(1) hV_sub])
                  show "bij_betw p0 Sn V" by (rule hbij)
                  \<comment> \<open>p0 continuous: preimage of TX-open in V = TE-open in Sn.\<close>
                  show "top1_continuous_map_on Sn (subspace_topology E TE Sn) V
                      (subspace_topology X TX V) p0"
                    unfolding top1_continuous_map_on_def
                  proof (intro conjI ballI)
                    fix e assume "e \<in> Sn"
                    thus "p0 e \<in> V" unfolding hSn p0_def vsheet_def by auto
                  next
                    fix W assume "W \<in> subspace_topology X TX V"
                    then obtain W0 where hW0: "W0 \<in> TX" "W = V \<inter> W0"
                      unfolding subspace_topology_def by (by100 blast)
                    have hW_sub: "W \<subseteq> V" using hW0 by (by100 blast)
                    have hW_TX: "V \<inter> W0 \<in> TX"
                      by (rule topology_inter_open[OF assms(1) hV_TX hW0(1)])
                    hence hW_in_TX: "W \<in> TX" using hW0 by simp
                    \<comment> \<open>Build W' \<in> TE with Sn \<inter> W' = {e \<in> Sn. p0 e \<in> W}.\<close>
                    define W' where "W' = {e \<in> E. p0 e \<in> W}"
                    have "W' \<in> TE" unfolding TE_def W'_def
                    proof (intro CollectI conjI allI)
                      show "{e \<in> E. p0 e \<in> W} \<subseteq> E" by (by100 blast)
                      fix m :: int
                      have "{x \<in> U. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} = U \<inter> W"
                        unfolding p0_def E_def by auto
                      thus "{x \<in> U. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} \<in> TX"
                        using topology_inter_open[OF assms(1) hU_TX hW_in_TX] by simp
                      have h1: "{x \<in> A. (x, 2*m+2) \<in> {e \<in> E. p0 e \<in> W}} = A \<inter> W"
                        unfolding p0_def E_def using hAB by auto
                      have h2: "{x \<in> B. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} = B \<inter> W"
                        unfolding p0_def E_def using hAB by auto
                      have h3: "{x \<in> V-U. (x, 2*m+1) \<in> {e \<in> E. p0 e \<in> W}} = (V-U) \<inter> W"
                        unfolding p0_def E_def using hW_sub by auto
                      have "(A\<inter>W) \<union> (B\<inter>W) \<union> ((V-U)\<inter>W) = V \<inter> W" using hAB by (by100 blast)
                      hence "... \<in> TX" using topology_inter_open[OF assms(1) hV_TX hW_in_TX] by simp
                      thus "{x \<in> A. (x, 2*m+2) \<in> {e \<in> E. p0 e \<in> W}} \<union>
                          {x \<in> B. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} \<union>
                          {x \<in> V-U. (x, 2*m+1) \<in> {e \<in> E. p0 e \<in> W}} \<in> TX"
                        using h1 h2 h3 \<open>(A\<inter>W) \<union> (B\<inter>W) \<union> ((V-U)\<inter>W) = V \<inter> W\<close> by presburger
                    qed
                    have "{e \<in> Sn. p0 e \<in> W} = Sn \<inter> W'"
                      unfolding W'_def using hSn_sub by (by100 blast)
                    thus "{e \<in> Sn. p0 e \<in> W} \<in> subspace_topology E TE Sn"
                      using \<open>W' \<in> TE\<close> unfolding subspace_topology_def by (by100 blast)
                  qed
                  \<comment> \<open>Inverse continuous: preimage under inv_into uses odd-slice of TE.\<close>
                  show "top1_continuous_map_on V (subspace_topology X TX V) Sn
                      (subspace_topology E TE Sn) (inv_into Sn p0)"
                    unfolding top1_continuous_map_on_def
                  proof (intro conjI ballI)
                    fix x assume "x \<in> V"
                    thus "inv_into Sn p0 x \<in> Sn" using hp0_img by (simp add: inv_into_into)
                  next
                    fix W assume "W \<in> subspace_topology E TE Sn"
                    then obtain W' where hW': "W' \<in> TE" "W = Sn \<inter> W'"
                      unfolding subspace_topology_def by (by100 blast)
                    have hslice: "{x \<in> A. (x, 2*k+2) \<in> W'} \<union> {x \<in> B. (x, 2*k) \<in> W'} \<union>
                        {x \<in> V-U. (x, 2*k+1) \<in> W'} \<in> TX"
                    proof -
                      have "\<forall>n::int. {x \<in> A. (x, 2*n+2) \<in> W'} \<union> {x \<in> B. (x, 2*n) \<in> W'} \<union>
                          {x \<in> V-U. (x, 2*n+1) \<in> W'} \<in> TX"
                        using hW'(1) unfolding TE_def by (by100 blast)
                      hence "{x \<in> A. (x, 2*k+2) \<in> W'} \<union> {x \<in> B. (x, 2*k) \<in> W'} \<union>
                          {x \<in> V-U. (x, 2*k+1) \<in> W'} \<in> TX" by blast
                      thus ?thesis .
                    qed
                    \<comment> \<open>inv_into maps: x\<in>A \<mapsto> (x,2(k+1)), x\<in>B \<mapsto> (x,2k), x\<in>V\U \<mapsto> (x,2k+1).\<close>
                    have hinv_A: "\<And>x. x \<in> A \<Longrightarrow> x \<in> V \<Longrightarrow> inv_into Sn p0 x = (x, 2*(k+1))"
                    proof -
                      fix x assume "x \<in> A" "x \<in> V"
                      have "(x, 2*(k+1)) \<in> Sn" unfolding hSn vsheet_def E_def
                        using \<open>x \<in> A\<close> \<open>x \<in> V\<close> hAB by auto
                      thus "inv_into Sn p0 x = (x, 2*(k+1))"
                        by (intro inv_into_f_eq[OF hinj]) (simp_all add: p0_def)
                    qed
                    have hinv_B: "\<And>x. x \<in> B \<Longrightarrow> x \<in> V \<Longrightarrow> inv_into Sn p0 x = (x, 2*k)"
                    proof -
                      fix x assume "x \<in> B" "x \<in> V"
                      have "(x, 2*k) \<in> Sn" unfolding hSn vsheet_def E_def
                        using \<open>x \<in> B\<close> \<open>x \<in> V\<close> hAB by auto
                      thus "inv_into Sn p0 x = (x, 2*k)"
                        by (intro inv_into_f_eq[OF hinj]) (simp_all add: p0_def)
                    qed
                    have hinv_VU: "\<And>x. x \<in> V - U \<Longrightarrow> inv_into Sn p0 x = (x, 2*k+1)"
                    proof -
                      fix x assume "x \<in> V - U"
                      have "(x, 2*k+1) \<in> Sn" unfolding hSn vsheet_def E_def
                        using \<open>x \<in> V - U\<close> by auto
                      thus "inv_into Sn p0 x = (x, 2*k+1)"
                        by (intro inv_into_f_eq[OF hinj]) (simp_all add: p0_def)
                    qed
                    have hpre: "{x \<in> V. inv_into Sn p0 x \<in> W} =
                        {x \<in> A. (x, 2*(k+1)) \<in> W'} \<union> {x \<in> B. (x, 2*k) \<in> W'} \<union>
                        {x \<in> V-U. (x, 2*k+1) \<in> W'}"
                    proof (rule set_eqI, rule iffI)
                      fix x assume hx: "x \<in> {x \<in> V. inv_into Sn p0 x \<in> W}"
                      hence "x \<in> V" "inv_into Sn p0 x \<in> W'" "inv_into Sn p0 x \<in> Sn"
                        using hW'(2) hp0_img inv_into_into[of x p0 Sn] by auto
                      have "x \<in> A \<or> x \<in> B \<or> x \<in> V-U" using \<open>x \<in> V\<close> hAB by (by100 blast)
                      thus "x \<in> {x \<in> A. (x, 2*(k+1)) \<in> W'} \<union> {x \<in> B. (x, 2*k) \<in> W'} \<union>
                          {x \<in> V-U. (x, 2*k+1) \<in> W'}"
                      proof (elim disjE)
                        assume "x \<in> A"
                        thus ?thesis using hinv_A \<open>x \<in> V\<close> \<open>inv_into Sn p0 x \<in> W'\<close> by auto
                      next
                        assume "x \<in> B"
                        thus ?thesis using hinv_B \<open>x \<in> V\<close> \<open>inv_into Sn p0 x \<in> W'\<close> by auto
                      next
                        assume "x \<in> V - U"
                        thus ?thesis using hinv_VU \<open>inv_into Sn p0 x \<in> W'\<close> by auto
                      qed
                    next
                      fix x assume "x \<in> {x \<in> A. (x, 2*(k+1)) \<in> W'} \<union>
                          {x \<in> B. (x, 2*k) \<in> W'} \<union> {x \<in> V-U. (x, 2*k+1) \<in> W'}"
                      hence "x \<in> V" using hAB by (by100 blast)
                      have "inv_into Sn p0 x \<in> W'"
                        using \<open>x \<in> _ \<union> _ \<union> _\<close> hinv_A hinv_B hinv_VU \<open>x \<in> V\<close> by auto
                      moreover have "inv_into Sn p0 x \<in> Sn"
                        using \<open>x \<in> V\<close> hp0_img by (simp add: inv_into_into)
                      ultimately show "x \<in> {x \<in> V. inv_into Sn p0 x \<in> W}"
                        using \<open>x \<in> V\<close> hW'(2) by (by100 blast)
                    qed
                    have hpre_sub: "{x \<in> V. inv_into Sn p0 x \<in> W} \<subseteq> V" by (by100 blast)
                    have hpre_TX: "{x \<in> V. inv_into Sn p0 x \<in> W} \<in> TX"
                      using hpre hslice by simp
                    show "{x \<in> V. inv_into Sn p0 x \<in> W} \<in> subspace_topology X TX V"
                    proof -
                      have "{x \<in> V. inv_into Sn p0 x \<in> W} =
                          V \<inter> {x \<in> V. inv_into Sn p0 x \<in> W}" using hpre_sub by (by100 blast)
                      thus ?thesis using hpre_TX unfolding subspace_topology_def by (by100 blast)
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
    show ?thesis using hTE hcov by simp
  qed

(** from \<S>63 Theorem 63.1: if X = U \<union> V with U \<inter> V = A \<union> B (disjoint open),
    and alpha: a to b in U, beta: b to a in V, then the loop f = alpha * beta is
    nontrivial in pi_1(X, a) (plus further properties: homotopy lifts, f^m and f^k
    are nonconjugate when the components are different). Used in Munkres' proof of
    the Jordan Curve Theorem. **)

theorem Theorem_63_1_loop_nontrivial:
  assumes "is_topology_on X TX"
      and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
      and "a \<in> A" and "b \<in> B"
      and "top1_is_path_on U (subspace_topology X TX U) a b alpha"
      and "top1_is_path_on V (subspace_topology X TX V) b a beta"
  shows "\<not> top1_path_homotopic_on X TX a a
           (top1_path_product alpha beta) (top1_constant_path a)"
proof
  assume hnul: "top1_path_homotopic_on X TX a a
      (top1_path_product alpha beta) (top1_constant_path a)"
  \<comment> \<open>Munkres 63.1: Construct covering space p: E \<rightarrow> X as infinite helix.
     E = ... \<sqcup> U_0 \<sqcup> V_0 \<sqcup> U_1 \<sqcup> V_1 \<sqcup> ... with A-sheets and B-sheets glued alternately.
     Concretely: E = Z \<times> (U \<sqcup> V), identifying (n, A-point in V_n) with (n, A-point in U_n)
     and (n, B-point in U_n) with (n+1, B-point in V_n).\<close>
  \<comment> \<open>Step 1+2: Build covering space E (type 'a \<times> int) and lift f to get different endpoints.\<close>
  have "\<exists>(E::('a \<times> int) set) TE (p0::('a \<times> int) \<Rightarrow> 'a) e0 e1.
      top1_covering_map_on E TE X TX p0
    \<and> is_topology_on E TE
    \<and> e0 \<in> E \<and> p0 e0 = a
    \<and> e1 \<in> E \<and> p0 e1 = a
    \<and> e0 \<noteq> e1
    \<and> (\<exists>ftilde. top1_is_path_on E TE e0 e1 ftilde
        \<and> (\<forall>s\<in>I_set. p0 (ftilde s) = top1_path_product alpha beta s))"
  proof -
    \<comment> \<open>Helix covering: E = canonical representatives of quotient Y/~.
       E = {(x, 2n) | x \<in> U} \<union> {(x, 2n+1) | x \<in> V\U}. Covering map p = fst.\<close>
    have ha_X: "a \<in> X" using assms(4,5,9) by (by100 blast)
    have hb_X: "b \<in> X" using assms(4,5,10) by (by100 blast)
    have ha_U: "a \<in> U" using assms(5,9) by (by100 blast)
    have hb_U: "b \<in> U" using assms(5,10) by (by100 blast)
    have ha_V: "a \<in> V" using assms(5,9) by (by100 blast)
    have hb_V: "b \<in> V" using assms(5,10) by (by100 blast)
    have hU_open_TX: "U \<in> TX" using assms(2) unfolding openin_on_def by (by100 blast)
    have hV_open_TX: "V \<in> TX" using assms(3) unfolding openin_on_def by (by100 blast)
    have hA_open_TX: "A \<in> TX" using assms(7) unfolding openin_on_def by (by100 blast)
    have hB_open_TX: "B \<in> TX" using assms(8) unfolding openin_on_def by (by100 blast)
    have hAB_UV: "A \<union> B = U \<inter> V" using assms(5) by simp
    have hAB_disj: "A \<inter> B = {}" using assms(6) .
    \<comment> \<open>Define normalization: maps Y = \<Union>(U\<times>{2n}) \<union> \<Union>(V\<times>{2n+1}) to canonical reps.\<close>
    define norm :: "'a \<times> int \<Rightarrow> 'a \<times> int" where
      "norm = (\<lambda>(x, m). if even m then (x, m)
               else if x \<in> A then (x, m + 1)
               else if x \<in> B then (x, m - 1)
               else (x, m))"
    \<comment> \<open>Define E = set of canonical representatives.\<close>
    define E :: "('a \<times> int) set" where
      "E = {(x, m). (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)}"
    \<comment> \<open>Define quotient topology on E.\<close>
    define TE :: "('a \<times> int) set set" where
      "TE = {W. W \<subseteq> E \<and>
        (\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX) \<and>
        (\<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX)}"
    define p0 :: "'a \<times> int \<Rightarrow> 'a" where "p0 = fst"
    define e0 :: "'a \<times> int" where "e0 = (a, 0)"
    define e1 :: "'a \<times> int" where "e1 = (a, 2)"
    \<comment> \<open>Basic facts about e0, e1.\<close>
    have he0_E: "e0 \<in> E" unfolding e0_def E_def using ha_U by simp
    have he1_E: "e1 \<in> E" unfolding e1_def E_def using ha_U by simp
    have hp0e0: "p0 e0 = a" unfolding p0_def e0_def by simp
    have hp0e1: "p0 e1 = a" unfolding p0_def e1_def by simp
    have hne: "e0 \<noteq> e1" unfolding e0_def e1_def by simp
    \<comment> \<open>TE is a topology on E, and p0 is a covering map. Use shared lemma.\<close>
    have hcov_and_TE: "top1_covering_map_on E TE X TX p0 \<and> is_topology_on E TE"
    proof -
      note h = helix_covering_construction[OF assms(1-8)]
      have hE_eq: "E = {x. even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
        unfolding E_def by auto
      have hTE_eq: "TE = {W. W \<subseteq> E \<and>
          (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
          (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
                {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
        unfolding TE_def E_def by auto
      have hp0_eq: "p0 = fst" unfolding p0_def by simp
      show ?thesis using h hE_eq hTE_eq hp0_eq by simp
    qed
    have hTE: "is_topology_on E TE" using hcov_and_TE by simp
    have hcov: "top1_covering_map_on E TE X TX p0" using hcov_and_TE by simp
    \<comment> \<open>The TE topology and covering map proofs (previously ~687 lines inline)
       are now in helix_covering_construction. The old proofs are removed.\<close>
    \<comment> \<open>Define the lift: \<alpha>-tilde on [0,1/2] maps to (alpha(2s), 0).
       \<beta>-tilde on [1/2,1] maps to norm(\<beta>(2s-1), 1).\<close>
    define ftilde :: "real \<Rightarrow> ('a \<times> int)" where
      "ftilde = (\<lambda>s. if s \<le> 1/2
        then (alpha (2*s), 0)
        else (let y = beta (2*s - 1) in
              if y \<in> A then (y, 2)
              else if y \<in> B then (y, 0)
              else (y, 1)))"
    \<comment> \<open>Lift is a path from e0 to e1.\<close>
    have hft_path: "top1_is_path_on E TE e0 e1 ftilde"
    proof -
      \<comment> \<open>ftilde = path_product of \<alpha>-lift and \<beta>-lift. Use path product.\<close>
      define \<alpha>_lift where "\<alpha>_lift = (\<lambda>s. (alpha s, 0::int))"
      define \<beta>_lift where "\<beta>_lift = (\<lambda>s. let y = beta s in
        if y \<in> A then (y, 2::int) else if y \<in> B then (y, 0::int) else (y, 1::int))"
      have hft_eq: "ftilde = top1_path_product \<alpha>_lift \<beta>_lift"
        unfolding ftilde_def top1_path_product_def \<alpha>_lift_def \<beta>_lift_def by (rule ext) auto
      \<comment> \<open>\<alpha>_lift: path from (a,0) to (b,0) in U-sheet 0.\<close>
      have h\<alpha>_lift_path: "top1_is_path_on E TE (a, 0) (b, 0) \<alpha>_lift"
      proof -
        \<comment> \<open>\<alpha> is a path in U. The U-sheet S0 = U \<times> {0} is open in E, and
           p0|S0: S0 \<rightarrow> U is a homeomorphism. The inverse sends x to (x, 0).
           So \<alpha>_lift = inv(p0|S0) \<circ> \<alpha> is continuous.\<close>
        have hS0: "U \<times> {0::int} \<subseteq> E" unfolding E_def by auto
        \<comment> \<open>\<alpha> is continuous from I to U with subspace topology from TX.\<close>
        have h\<alpha>_path_U: "top1_is_path_on U (subspace_topology X TX U) a b alpha"
          by (rule assms(11))
        \<comment> \<open>\<alpha>_lift = (\<lambda>s. (alpha s, 0)). Continuous because: for each open W \<in> TE,
           {s \<in> I | \<alpha>_lift s \<in> W} = {s \<in> I | alpha s \<in> {x \<in> U. (x,0) \<in> W}}.
           And {x \<in> U. (x,0) \<in> W} is open in TX (from TE definition, even slice).
           So this is open in I (since \<alpha> is continuous).\<close>
        show ?thesis unfolding top1_is_path_on_def
        proof (intro conjI)
          show "top1_continuous_map_on I_set I_top E TE \<alpha>_lift"
            unfolding top1_continuous_map_on_def
          proof (intro conjI ballI)
            fix s assume "s \<in> I_set"
            hence "alpha s \<in> U" using h\<alpha>_path_U
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "\<alpha>_lift s \<in> E" unfolding \<alpha>_lift_def E_def by auto
          next
            fix W assume hW: "W \<in> TE"
            \<comment> \<open>Need {s \<in> I. \<alpha>_lift s \<in> W} \<in> I_top.\<close>
            have hslice: "{x \<in> U. (x, 0::int) \<in> W} \<in> TX"
            proof -
              have "\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
              hence "{x \<in> U. (x, 2*(0::int)) \<in> W} \<in> TX" by (rule spec)
              thus ?thesis by simp
            qed
            have heq: "{s \<in> I_set. \<alpha>_lift s \<in> W} = {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
            proof (rule set_eqI, rule iffI)
              fix s assume "s \<in> {s \<in> I_set. \<alpha>_lift s \<in> W}"
              hence "s \<in> I_set" "\<alpha>_lift s \<in> W" by auto
              hence "alpha s \<in> U" "(alpha s, 0::int) \<in> W"
                using h\<alpha>_path_U unfolding top1_is_path_on_def top1_continuous_map_on_def
                  \<alpha>_lift_def by auto
              thus "s \<in> {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
                using \<open>s \<in> I_set\<close> by (by100 blast)
            next
              fix s assume "s \<in> {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
              hence "s \<in> I_set" "alpha s \<in> U" "(alpha s, 0::int) \<in> W" by auto
              thus "s \<in> {s \<in> I_set. \<alpha>_lift s \<in> W}" unfolding \<alpha>_lift_def by simp
            qed
            \<comment> \<open>The slice {x \<in> U. (x,0) \<in> W} is TX-open. It's also a subset of U,
               so it's open in the subspace topology of U from TX.
               \<alpha> continuous from I to U means preimage of this set is I_top-open.\<close>
            have hslice_U: "{x \<in> U. (x, 0::int) \<in> W} \<in> subspace_topology X TX U"
            proof -
              have "{x \<in> U. (x, 0::int) \<in> W} = U \<inter> {x \<in> U. (x, 0::int) \<in> W}" by (by100 fast)
              thus ?thesis using hslice unfolding subspace_topology_def by (by100 blast)
            qed
            have "{s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}} \<in> I_top"
              using h\<alpha>_path_U hslice_U
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "{s \<in> I_set. \<alpha>_lift s \<in> W} \<in> I_top" using heq by simp
          qed
          show "\<alpha>_lift 0 = (a, 0::int)"
            unfolding \<alpha>_lift_def using assms(11)
            unfolding top1_is_path_on_def by simp
          show "\<alpha>_lift 1 = (b, 0::int)"
            unfolding \<alpha>_lift_def using assms(11)
            unfolding top1_is_path_on_def by simp
        qed
      qed
      \<comment> \<open>\<beta>_lift: path from (b,0) to (a,2) in E.\<close>
      have h\<beta>_lift_path: "top1_is_path_on E TE (b, 0) (a, 2) \<beta>_lift"
      proof -
        have h\<beta>_path_V: "top1_is_path_on V (subspace_topology X TX V) b a beta"
          by (rule assms(12))
        show ?thesis unfolding top1_is_path_on_def
        proof (intro conjI)
          show "top1_continuous_map_on I_set I_top E TE \<beta>_lift"
            unfolding top1_continuous_map_on_def
          proof (intro conjI ballI)
            fix s assume "s \<in> I_set"
            hence "beta s \<in> V" using h\<beta>_path_V
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "\<beta>_lift s \<in> E" unfolding \<beta>_lift_def E_def Let_def
              using hAB_UV hAB_disj by auto
          next
            fix W assume hW: "W \<in> TE"
            \<comment> \<open>{s \<in> I. \<beta>_lift s \<in> W}. For s with beta(s) \<in> A: \<beta>_lift s = (beta s, 2).
               For beta(s) \<in> B: (beta s, 0). For beta(s) \<in> V\U: (beta s, 1).
               The odd V-slice condition of TE gives:
               {x \<in> A. (x,2) \<in> W} \<union> {x \<in> B. (x,0) \<in> W} \<union> {x \<in> V\U. (x,1) \<in> W} \<in> TX.
               This is exactly the set {x \<in> V. \<beta>_lift_at x \<in> W} (the "V-slice" at level n=0).
               Since \<beta> is continuous from I to V, preimage is I_top-open.\<close>
            have hV_slice: "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
                {x \<in> V - U. (x, 1::int) \<in> W} \<in> TX"
            proof -
              have "\<forall>n::int. {x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V-U. (x, 2*n+1) \<in> W} \<in> TX"
                using hW unfolding TE_def by (by100 blast)
              hence "{x \<in> A. (x, 2*(0::int)+2) \<in> W} \<union> {x \<in> B. (x, 2*(0::int)) \<in> W} \<union>
                  {x \<in> V-U. (x, 2*(0::int)+1) \<in> W} \<in> TX" by (rule spec)
              thus ?thesis by simp
            qed
            have heq: "{s \<in> I_set. \<beta>_lift s \<in> W} =
                {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union>
                    {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W})}"
            proof (rule set_eqI, rule iffI)
              fix s assume hs: "s \<in> {s \<in> I_set. \<beta>_lift s \<in> W}"
              hence "s \<in> I_set" "\<beta>_lift s \<in> W" by auto
              have "beta s \<in> V" using \<open>s \<in> I_set\<close> h\<beta>_path_V
                unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
              hence "beta s \<in> A \<or> beta s \<in> B \<or> beta s \<in> V - U"
                using hAB_UV by (by100 blast)
              have "\<beta>_lift s \<in> W" by (rule \<open>\<beta>_lift s \<in> W\<close>)
              have "beta s \<in> {x \<in> A. (x, 2::int) \<in> W} \<union>
                  {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W}"
              proof -
                have "beta s \<in> A \<or> beta s \<in> B \<or> beta s \<in> V - U" by (rule \<open>beta s \<in> A \<or> _\<close>)
                thus ?thesis
                proof (elim disjE)
                  assume "beta s \<in> A"
                  hence "\<beta>_lift s = (beta s, 2::int)" unfolding \<beta>_lift_def Let_def by simp
                  hence "(beta s, 2::int) \<in> W" using \<open>\<beta>_lift s \<in> W\<close> by simp
                  thus ?thesis using \<open>beta s \<in> A\<close> by (by100 blast)
                next
                  assume "beta s \<in> B"
                  hence "\<beta>_lift s = (beta s, 0::int)" unfolding \<beta>_lift_def Let_def
                    using hAB_disj by auto
                  hence "(beta s, 0::int) \<in> W" using \<open>\<beta>_lift s \<in> W\<close> by simp
                  thus ?thesis using \<open>beta s \<in> B\<close> by (by100 blast)
                next
                  assume hbsVU: "beta s \<in> V - U"
                  hence "beta s \<notin> A" using hAB_UV by (by100 fast)
                  moreover have "beta s \<notin> B" using hbsVU hAB_UV by (by100 fast)
                  ultimately have "\<beta>_lift s = (beta s, 1::int)" unfolding \<beta>_lift_def Let_def by auto
                  hence "(beta s, 1::int) \<in> W" using \<open>\<beta>_lift s \<in> W\<close> by simp
                  thus ?thesis using hbsVU by (by100 blast)
                qed
              qed
              thus "s \<in> {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union>
                  {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W})}"
                using \<open>s \<in> I_set\<close> by (by100 blast)
            next
              fix s assume hs: "s \<in> {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union>
                  {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W})}"
              hence "s \<in> I_set" by simp
              from hs have hcases: "beta s \<in> A \<and> (beta s, 2::int) \<in> W \<or>
                  beta s \<in> B \<and> (beta s, 0::int) \<in> W \<or>
                  beta s \<in> V - U \<and> (beta s, 1::int) \<in> W" by (by100 blast)
              have "\<beta>_lift s \<in> W"
              proof -
                from hcases show ?thesis
                proof (elim disjE conjE)
                  assume "beta s \<in> A" "(beta s, 2::int) \<in> W"
                  hence "\<beta>_lift s = (beta s, 2::int)" unfolding \<beta>_lift_def Let_def by simp
                  thus ?thesis using \<open>(beta s, 2) \<in> W\<close> by simp
                next
                  assume "beta s \<in> B" "(beta s, 0::int) \<in> W"
                  hence "\<beta>_lift s = (beta s, 0::int)" unfolding \<beta>_lift_def Let_def
                    using hAB_disj by auto
                  thus ?thesis using \<open>(beta s, 0) \<in> W\<close> by simp
                next
                  assume "beta s \<in> V - U" "(beta s, 1::int) \<in> W"
                  hence "beta s \<notin> A" "beta s \<notin> B" using hAB_UV by (by100 blast)+
                  hence "\<beta>_lift s = (beta s, 1::int)" unfolding \<beta>_lift_def Let_def by auto
                  thus ?thesis using \<open>(beta s, 1) \<in> W\<close> by simp
                qed
              qed
              thus "s \<in> {s \<in> I_set. \<beta>_lift s \<in> W}" using \<open>s \<in> I_set\<close> by (by100 blast)
            qed
            have hV_sub_open: "{x \<in> A. (x, 2::int) \<in> W} \<union>
                {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W}
                \<in> subspace_topology X TX V"
            proof -
              have hsub: "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
                  {x \<in> V - U. (x, 1::int) \<in> W} \<subseteq> V" using hAB_UV by (by100 blast)
              hence "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
                  {x \<in> V - U. (x, 1::int) \<in> W} =
                  V \<inter> ({x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
                      {x \<in> V - U. (x, 1::int) \<in> W})" by (by100 blast)
              thus ?thesis using hV_slice unfolding subspace_topology_def by (by100 blast)
            qed
            have "{s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union>
                {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W})} \<in> I_top"
              using h\<beta>_path_V hV_sub_open
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "{s \<in> I_set. \<beta>_lift s \<in> W} \<in> I_top" using heq by simp
          qed
          show "\<beta>_lift 0 = (b, 0::int)"
            unfolding \<beta>_lift_def Let_def using assms(12) assms(10) hAB_disj
            unfolding top1_is_path_on_def by auto
          show "\<beta>_lift 1 = (a, 2::int)"
            unfolding \<beta>_lift_def Let_def using assms(12) assms(9)
            unfolding top1_is_path_on_def by auto
        qed
      qed
      have hTX_E: "is_topology_on E TE" by (rule hTE)
      have "top1_is_path_on E TE (a, 0) (a, 2) (top1_path_product \<alpha>_lift \<beta>_lift)"
        by (rule top1_path_product_is_path[OF hTX_E h\<alpha>_lift_path h\<beta>_lift_path])
      thus ?thesis unfolding hft_eq e0_def e1_def .
    qed
    \<comment> \<open>Lift projects correctly.\<close>
    have hft_lift: "\<forall>s\<in>I_set. p0 (ftilde s) = top1_path_product alpha beta s"
    proof
      fix s assume hs: "s \<in> I_set"
      have hs_range: "0 \<le> s" "s \<le> 1" using hs unfolding top1_unit_interval_def by auto
      show "p0 (ftilde s) = top1_path_product alpha beta s"
      proof (cases "s \<le> 1/2")
        case True
        hence "ftilde s = (alpha (2*s), 0)" unfolding ftilde_def by simp
        hence "p0 (ftilde s) = alpha (2*s)" unfolding p0_def by simp
        moreover have "top1_path_product alpha beta s = alpha (2*s)"
          unfolding top1_path_product_def using True by simp
        ultimately show ?thesis by simp
      next
        case False
        hence hs_half: "s > 1/2" by simp
        have "p0 (ftilde s) = beta (2*s - 1)"
        proof -
          define y where "y = beta (2*s - 1)"
          have "ftilde s = (if y \<in> A then (y, 2) else if y \<in> B then (y, 0) else (y, 1))"
            unfolding ftilde_def y_def using hs_half by (simp add: Let_def)
          hence "p0 (ftilde s) = y" unfolding p0_def by (cases "y \<in> A"; cases "y \<in> B"; simp)
          thus ?thesis unfolding y_def by simp
        qed
        moreover have "top1_path_product alpha beta s = beta (2*s - 1)"
          unfolding top1_path_product_def using False by simp
        ultimately show ?thesis by simp
      qed
    qed
    show ?thesis
      using hcov hTE he0_E he1_E hp0e0 hp0e1 hne hft_path hft_lift
      by (intro exI[of _ E] exI[of _ TE] exI[of _ p0] exI[of _ e0] exI[of _ e1])
         (by100 blast)
  qed
  \<comment> \<open>Step 3: If f were nulhomotopic, the lift would be a loop (same start and end).
     But we showed the lift has different endpoints. Contradiction.\<close>
  \<comment> \<open>From step 2, obtain covering E, map p0, points e0 \<noteq> e1, and lift ftilde.\<close>
  from this obtain E :: "('a \<times> int) set" and TE :: "('a \<times> int) set set"
      and p0 :: "('a \<times> int) \<Rightarrow> 'a"
      and e0 :: "'a \<times> int" and e1 :: "'a \<times> int"
      and ftilde :: "real \<Rightarrow> ('a \<times> int)" where
      hcov: "top1_covering_map_on E TE X TX p0"
      and hTE: "is_topology_on E TE"
      and he0: "e0 \<in> E" and hp0e0: "p0 e0 = a"
      and he1: "e1 \<in> E" and hp0e1: "p0 e1 = a"
      and hne: "e0 \<noteq> e1"
      and hft: "top1_is_path_on E TE e0 e1 ftilde"
      and hft_lift: "\<forall>s\<in>I_set. p0 (ftilde s) = top1_path_product alpha beta s"
    by (by100 blast)
  \<comment> \<open>hnul gives a homotopy from \<alpha>*\<beta> to const_a. Lift it via Lemma_54_2.\<close>
  \<comment> \<open>The lifted homotopy starts from lift of \<alpha>*\<beta> = ftilde (starts at e0),
     and ends at lift of const_a (starts at e0) = const_{e0}.
     By Theorem_54_3 (unique endpoints), ftilde(1) = const_{e0}(1) = e0.
     But ftilde(1) = e1 \<noteq> e0. Contradiction.\<close>
  \<comment> \<open>By Theorem_54_3: path-homotopic loops with same start lift to paths with same endpoint.\<close>
  have hfab_path: "top1_is_path_on X TX a a (top1_path_product alpha beta)"
    using hnul unfolding top1_path_homotopic_on_def by (by100 blast)
  have hca_path: "top1_is_path_on X TX a a (top1_constant_path a)"
    using hnul unfolding top1_path_homotopic_on_def by (by100 blast)
  \<comment> \<open>hTE already obtained from step 2.\<close>
  have hTX: "is_topology_on X TX" by (rule assms(1))
  have hconst_lift: "top1_is_path_on E TE e0 e0 (top1_constant_path e0)"
    by (rule top1_constant_path_is_path[OF hTE he0])
  have hconst_lifts: "\<forall>s\<in>I_set. p0 (top1_constant_path e0 s) = top1_constant_path a s"
    unfolding top1_constant_path_def using hp0e0 by simp
  have "e1 = e0"
    using conjunct1[OF Theorem_54_3[OF hcov hTE hTX he0 hp0e0
        hfab_path hca_path hnul hft hft_lift hconst_lift hconst_lifts]]
    by simp
  thus False using hne by simp
qed

\<comment> \<open>Theorem 63.1(c): In the helix covering, g = \<gamma>*\<delta> lifts to a LOOP at e0
   (because a, a' \<in> A: no sheet shift). Combined with f = \<alpha>*\<beta> lifting
   to a NON-loop (sheet shift by 2), this means:
   [f]^m = [g]^k \<Rightarrow> m = 0 (since lifts have endpoints (a,2m) vs (a,0)).
   For 63.5: this contradicts \<pi>_1(X) \<cong> Z (rank 1 \<Rightarrow> common multiples exist).\<close>
\<comment> \<open>Lemma: g = \<gamma>*\<delta> (with a, a' \<in> A) lifts to a loop in the helix covering.
   This is the KEY property distinguishing f-lift (non-loop) from g-lift (loop).
   Combined with Theorem_54_3, this gives: if [f]^m = [g]^k then m = 0.\<close>
lemma helix_g_lift_is_loop:
  assumes "is_topology_on X TX"
      and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
      and "a \<in> A" and "b \<in> B" and "a' \<in> A"
      and "top1_is_path_on U (subspace_topology X TX U) a a' gamma"
      and "top1_is_path_on V (subspace_topology X TX V) a' a delta"
  shows "\<exists>(E::('a \<times> int) set) TE (p0::('a \<times> int) \<Rightarrow> 'a) e0.
      top1_covering_map_on E TE X TX p0
    \<and> is_topology_on E TE
    \<and> e0 \<in> E \<and> p0 e0 = a
    \<and> (\<exists>gtilde. top1_is_path_on E TE e0 e0 gtilde
        \<and> (\<forall>s\<in>I_set. p0 (gtilde s) = top1_path_product gamma delta s))"
proof -
    \<comment> \<open>Use the same helix covering as in Theorem_63_1.\<close>
    have ha_U: "a \<in> U" using assms(5,9) by (by100 blast)
    have ha'_U: "a' \<in> U" using assms(5,11) by (by100 blast)
    have ha_V: "a \<in> V" using assms(5,9) by (by100 blast)
    have ha'_V: "a' \<in> V" using assms(5,11) by (by100 blast)
    have hU_open_TX: "U \<in> TX" using assms(2) unfolding openin_on_def by (by100 blast)
    have hV_open_TX: "V \<in> TX" using assms(3) unfolding openin_on_def by (by100 blast)
    have hA_open_TX: "A \<in> TX" using assms(7) unfolding openin_on_def by (by100 blast)
    have hB_open_TX: "B \<in> TX" using assms(8) unfolding openin_on_def by (by100 blast)
    have hAB_UV: "A \<union> B = U \<inter> V" using assms(5) by simp
    have hAB_disj: "A \<inter> B = {}" using assms(6) .
    \<comment> \<open>Same E, TE, p0 as 63.1.\<close>
    define E :: "('a \<times> int) set" where
      "E = {(x, m). (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)}"
    define TE :: "('a \<times> int) set set" where
      "TE = {W. W \<subseteq> E \<and>
        (\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX) \<and>
        (\<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX)}"
    define p0 :: "'a \<times> int \<Rightarrow> 'a" where "p0 = fst"
    define e0 :: "'a \<times> int" where "e0 = (a, 0)"
    have he0_E: "e0 \<in> E" unfolding e0_def E_def using ha_U by simp
    have hp0e0: "p0 e0 = a" unfolding p0_def e0_def by simp
    have hcov_and_TE: "top1_covering_map_on E TE X TX p0 \<and> is_topology_on E TE"
    proof -
      note h = helix_covering_construction[OF assms(1-8)]
      have "E = {x. even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
        unfolding E_def by auto
      moreover have "TE = {W. W \<subseteq> E \<and>
          (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
          (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
                {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
        unfolding TE_def E_def by auto
      moreover have "p0 = fst" unfolding p0_def by simp
      ultimately show ?thesis using h by simp
    qed
    hence hTE: "is_topology_on E TE" and hcov: "top1_covering_map_on E TE X TX p0"
      by auto
    \<comment> \<open>g-lift: \<gamma>_lift on [0,1/2], \<delta>_lift on [1/2,1].
       \<gamma>_lift(s) = (\<gamma>(s), 0). \<delta>_lift(s) = norm(\<delta>(s), -1).
       Since a' \<in> A: norm(a', -1) = (a', 0) = \<gamma>_lift(1). Junction OK.
       Since a \<in> A: norm(a, -1) = (a, 0) = e0. LOOP!\<close>
    define gtilde :: "real \<Rightarrow> ('a \<times> int)" where
      "gtilde = (\<lambda>s. if s \<le> 1/2
        then (gamma (2*s), 0)
        else (let y = delta (2*s - 1) in
              if y \<in> A then (y, 0)
              else if y \<in> B then (y, -2)
              else (y, -1)))"
    \<comment> \<open>Note: norm(y, -1) = (y, 0) if y \<in> A, (y, -2) if y \<in> B, (y, -1) if y \<in> V\U.\<close>
    have hgt_path: "top1_is_path_on E TE e0 e0 gtilde"
    proof -
      define \<gamma>_lift where "\<gamma>_lift = (\<lambda>s. (gamma s, 0::int))"
      define \<delta>_lift where "\<delta>_lift = (\<lambda>s. let y = delta s in
        if y \<in> A then (y, 0::int) else if y \<in> B then (y, -2::int) else (y, -1::int))"
      have hgt_eq: "gtilde = top1_path_product \<gamma>_lift \<delta>_lift"
        unfolding gtilde_def top1_path_product_def \<gamma>_lift_def \<delta>_lift_def by (rule ext) auto
      \<comment> \<open>\<gamma>_lift: path from (a,0) to (a',0) in E. Same as \<alpha>-lift but with \<gamma>.\<close>
      have h\<gamma>_lift: "top1_is_path_on E TE (a, 0) (a', 0) \<gamma>_lift"
      proof -
        have h\<gamma>_U: "top1_is_path_on U (subspace_topology X TX U) a a' gamma" by (rule assms(12))
        show ?thesis unfolding top1_is_path_on_def
        proof (intro conjI)
          show "top1_continuous_map_on I_set I_top E TE \<gamma>_lift"
            unfolding top1_continuous_map_on_def
          proof (intro conjI ballI)
            fix s assume "s \<in> I_set"
            hence "gamma s \<in> U" using h\<gamma>_U
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "\<gamma>_lift s \<in> E" unfolding \<gamma>_lift_def E_def by auto
          next
            fix W assume hW: "W \<in> TE"
            have hslice: "{x \<in> U. (x, 0::int) \<in> W} \<in> TX"
            proof -
              have "\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
              hence "{x \<in> U. (x, 2*(0::int)) \<in> W} \<in> TX" by (rule spec)
              thus ?thesis by simp
            qed
            have "{s \<in> I_set. \<gamma>_lift s \<in> W} = {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
            proof (rule set_eqI, rule iffI)
              fix s assume "s \<in> {s \<in> I_set. \<gamma>_lift s \<in> W}"
              thus "s \<in> {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
                using h\<gamma>_U unfolding top1_is_path_on_def top1_continuous_map_on_def \<gamma>_lift_def
                by auto
            next
              fix s assume "s \<in> {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
              thus "s \<in> {s \<in> I_set. \<gamma>_lift s \<in> W}" unfolding \<gamma>_lift_def by simp
            qed
            moreover have "{s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}} \<in> I_top"
            proof -
              have "{x \<in> U. (x, 0::int) \<in> W} \<in> subspace_topology X TX U"
                using hslice unfolding subspace_topology_def by (by100 blast)
              thus ?thesis using h\<gamma>_U unfolding top1_is_path_on_def top1_continuous_map_on_def
                by (by100 blast)
            qed
            ultimately show "{s \<in> I_set. \<gamma>_lift s \<in> W} \<in> I_top" by simp
          qed
          show "\<gamma>_lift 0 = (a, 0::int)" unfolding \<gamma>_lift_def
            using h\<gamma>_U unfolding top1_is_path_on_def by simp
          show "\<gamma>_lift 1 = (a', 0::int)" unfolding \<gamma>_lift_def
            using h\<gamma>_U unfolding top1_is_path_on_def by simp
        qed
      qed
      \<comment> \<open>\<delta>_lift: path from (a',0) to (a,0) in E. Uses odd-slice at level -1.\<close>
      have h\<delta>_lift: "top1_is_path_on E TE (a', 0) (a, 0) \<delta>_lift"
      proof -
        have h\<delta>_V: "top1_is_path_on V (subspace_topology X TX V) a' a delta" by (rule assms(13))
        show ?thesis unfolding top1_is_path_on_def
        proof (intro conjI)
          show "top1_continuous_map_on I_set I_top E TE \<delta>_lift"
            unfolding top1_continuous_map_on_def
          proof (intro conjI ballI)
            fix s assume "s \<in> I_set"
            hence "delta s \<in> V" using h\<delta>_V
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "\<delta>_lift s \<in> E" unfolding \<delta>_lift_def E_def Let_def
              using hAB_UV hAB_disj by auto
          next
            fix W assume hW: "W \<in> TE"
            \<comment> \<open>Odd-slice at n = -1: {x\<in>A.(x,0)\<in>W} \<union> {x\<in>B.(x,-2)\<in>W} \<union> {x\<in>V\U.(x,-1)\<in>W}.\<close>
            have hV_slice: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
                {x \<in> V - U. (x, -1::int) \<in> W} \<in> TX"
            proof -
              have "\<forall>n::int. {x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V-U. (x, 2*n+1) \<in> W} \<in> TX"
                using hW unfolding TE_def by (by100 blast)
              hence "{x \<in> A. (x, 2*(-1::int)+2) \<in> W} \<union> {x \<in> B. (x, 2*(-1::int)) \<in> W} \<union>
                  {x \<in> V-U. (x, 2*(-1::int)+1) \<in> W} \<in> TX" by (rule spec)
              thus ?thesis by simp
            qed
            have heq: "{s \<in> I_set. \<delta>_lift s \<in> W} =
                {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                    {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})}"
            proof (rule set_eqI, rule iffI)
              fix s assume hs: "s \<in> {s \<in> I_set. \<delta>_lift s \<in> W}"
              hence "s \<in> I_set" "\<delta>_lift s \<in> W" by auto
              have "delta s \<in> V" using \<open>s \<in> I_set\<close> h\<delta>_V
                unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
              hence "delta s \<in> A \<or> delta s \<in> B \<or> delta s \<in> V - U"
                using hAB_UV by (by100 fast)
              have "delta s \<in> {x \<in> A. (x, 0::int) \<in> W} \<union>
                  {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W}"
              proof -
                from \<open>delta s \<in> A \<or> delta s \<in> B \<or> delta s \<in> V - U\<close> show ?thesis
                proof (elim disjE)
                  assume "delta s \<in> A"
                  hence "\<delta>_lift s = (delta s, 0::int)" unfolding \<delta>_lift_def Let_def by simp
                  hence "(delta s, 0::int) \<in> W" using \<open>\<delta>_lift s \<in> W\<close> by simp
                  thus ?thesis using \<open>delta s \<in> A\<close> by (by100 blast)
                next
                  assume "delta s \<in> B"
                  hence "\<delta>_lift s = (delta s, -2::int)" unfolding \<delta>_lift_def Let_def
                    using hAB_disj by auto
                  hence "(delta s, -2::int) \<in> W" using \<open>\<delta>_lift s \<in> W\<close> by simp
                  thus ?thesis using \<open>delta s \<in> B\<close> by (by100 blast)
                next
                  assume "delta s \<in> V - U"
                  hence "delta s \<notin> A" "delta s \<notin> B" using hAB_UV by (by100 blast)+
                  hence "\<delta>_lift s = (delta s, -1::int)" unfolding \<delta>_lift_def Let_def by auto
                  hence "(delta s, -1::int) \<in> W" using \<open>\<delta>_lift s \<in> W\<close> by simp
                  thus ?thesis using \<open>delta s \<in> V - U\<close> by (by100 blast)
                qed
              qed
              thus "s \<in> {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                  {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})}"
                using \<open>s \<in> I_set\<close> by (by100 blast)
            next
              fix s assume hs: "s \<in> {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                  {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})}"
              hence "s \<in> I_set" by simp
              from hs have hcases: "delta s \<in> A \<and> (delta s, 0::int) \<in> W \<or>
                  delta s \<in> B \<and> (delta s, -2::int) \<in> W \<or>
                  delta s \<in> V - U \<and> (delta s, -1::int) \<in> W" by (by100 blast)
              have "\<delta>_lift s \<in> W"
              proof -
                from hcases show ?thesis
                proof (elim disjE conjE)
                  assume "delta s \<in> A" "(delta s, 0::int) \<in> W"
                  hence "\<delta>_lift s = (delta s, 0::int)" unfolding \<delta>_lift_def Let_def by simp
                  thus ?thesis using \<open>(delta s, 0) \<in> W\<close> by simp
                next
                  assume "delta s \<in> B" "(delta s, -2::int) \<in> W"
                  hence "\<delta>_lift s = (delta s, -2::int)" unfolding \<delta>_lift_def Let_def
                    using hAB_disj by auto
                  thus ?thesis using \<open>(delta s, -2) \<in> W\<close> by simp
                next
                  assume "delta s \<in> V - U" "(delta s, -1::int) \<in> W"
                  hence "delta s \<notin> A" "delta s \<notin> B" using hAB_UV by (by100 blast)+
                  hence "\<delta>_lift s = (delta s, -1::int)" unfolding \<delta>_lift_def Let_def by auto
                  thus ?thesis using \<open>(delta s, -1) \<in> W\<close> by simp
                qed
              qed
              thus "s \<in> {s \<in> I_set. \<delta>_lift s \<in> W}" using \<open>s \<in> I_set\<close> by (by100 blast)
            qed
            have hV_sub_open: "{x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W}
                \<in> subspace_topology X TX V"
            proof -
              have hsub: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
                  {x \<in> V - U. (x, -1::int) \<in> W} \<subseteq> V" using hAB_UV by (by100 blast)
              thus ?thesis using hV_slice unfolding subspace_topology_def by (by100 blast)
            qed
            have "{s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})} \<in> I_top"
              using h\<delta>_V hV_sub_open
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "{s \<in> I_set. \<delta>_lift s \<in> W} \<in> I_top" using heq by simp
          qed
          show "\<delta>_lift 0 = (a', 0::int)"
            unfolding \<delta>_lift_def Let_def using assms(13) assms(11) hAB_disj
            unfolding top1_is_path_on_def by auto
          show "\<delta>_lift 1 = (a, 0::int)"
            unfolding \<delta>_lift_def Let_def using assms(13) assms(9)
            unfolding top1_is_path_on_def by auto
        qed
      qed
      have hTX_E: "is_topology_on E TE" by (rule hTE)
      have "top1_is_path_on E TE (a, 0) (a, 0) (top1_path_product \<gamma>_lift \<delta>_lift)"
        by (rule top1_path_product_is_path[OF hTX_E h\<gamma>_lift h\<delta>_lift])
      thus ?thesis unfolding hgt_eq e0_def .
    qed
    have hgt_lift: "\<forall>s\<in>I_set. p0 (gtilde s) = top1_path_product gamma delta s"
    proof
      fix s assume hs: "s \<in> I_set"
      have hs_range: "0 \<le> s" "s \<le> 1" using hs unfolding top1_unit_interval_def by auto
      show "p0 (gtilde s) = top1_path_product gamma delta s"
      proof (cases "s \<le> 1/2")
        case True
        hence "gtilde s = (gamma (2*s), 0)" unfolding gtilde_def by simp
        thus ?thesis unfolding p0_def top1_path_product_def using True by simp
      next
        case False
        hence hs_half: "s > 1/2" by simp
        define y where "y = delta (2*s - 1)"
        have "gtilde s = (if y \<in> A then (y, 0) else if y \<in> B then (y, -2) else (y, -1))"
          unfolding gtilde_def y_def using hs_half by (simp add: Let_def)
        hence "p0 (gtilde s) = y" unfolding p0_def by (cases "y \<in> A"; cases "y \<in> B"; simp)
        thus ?thesis unfolding y_def top1_path_product_def using False by simp
      qed
    qed
    show ?thesis
      using hcov hTE he0_E hp0e0 hgt_path hgt_lift
      by (intro exI[of _ E] exI[of _ TE] exI[of _ p0] exI[of _ e0]) (by100 blast)
  qed

text \<open>N-fold product of a loop: f^0 = const, f^(n+1) = f * f^n.\<close>
primrec top1_path_power :: "(real \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (real \<Rightarrow> 'a)" where
  "top1_path_power f x 0 = top1_constant_path x"
| "top1_path_power f x (Suc n) = top1_path_product f (top1_path_power f x n)"

declare top1_path_power.simps[simp del]

lemma top1_path_power_0[simp]:
  "top1_path_power f x 0 = top1_constant_path x"
  unfolding top1_path_power_def by simp

lemma top1_path_power_Suc[simp]:
  "top1_path_power f x (Suc n) = top1_path_product f (top1_path_power f x n)"
  unfolding top1_path_power_def by simp

lemma top1_path_power_is_path:
  assumes "is_topology_on X TX" and "top1_is_loop_on X TX a f"
  shows "top1_is_path_on X TX a a (top1_path_power f a n)"
proof (induction n)
  case 0
  have haX: "a \<in> X"
    using top1_is_loop_on_start[OF assms(2)]
          top1_is_loop_on_continuous[OF assms(2)]
    unfolding top1_continuous_map_on_def top1_unit_interval_def by force
  thus ?case by (simp only: top1_path_power_0 top1_constant_path_is_path[OF assms(1) haX])
next
  case (Suc n)
  have hf: "top1_is_path_on X TX a a f"
    using assms(2) unfolding top1_is_loop_on_def by simp
  show ?case by (simp only: top1_path_power_Suc top1_path_product_is_path[OF assms(1) hf Suc])
qed

lemma top1_path_power_is_loop:
  assumes "is_topology_on X TX" and "top1_is_loop_on X TX a f"
  shows "top1_is_loop_on X TX a (top1_path_power f a n)"
  using top1_path_power_is_path[OF assms] unfolding top1_is_loop_on_def by simp

text \<open>Helper: a path in a subspace U (with subspace topology from X) is also a path in X.\<close>
lemma path_in_subspace_is_path_in_space:
  assumes "is_topology_on X TX" and "U \<subseteq> X" and "openin_on X TX U"
  and "top1_is_path_on U (subspace_topology X TX U) a' b' f"
  shows "top1_is_path_on X TX a' b' f"
  unfolding top1_is_path_on_def top1_continuous_map_on_def
proof (intro conjI ballI)
  fix s assume hs: "s \<in> I_set"
  have "f s \<in> U" using assms(4) hs unfolding top1_is_path_on_def top1_continuous_map_on_def
    by (by100 blast)
  thus "f s \<in> X" using assms(2) by (by100 blast)
next
  fix W assume hW: "W \<in> TX"
  have hUW: "U \<inter> W \<in> subspace_topology X TX U"
    unfolding subspace_topology_def using hW by blast
  have h_pre: "{s \<in> I_set. f s \<in> U \<inter> W} \<in> I_top"
    using assms(4) hUW unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
  have h_in_U: "\<forall>s\<in>I_set. f s \<in> U"
    using assms(4) unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
  have "{s \<in> I_set. f s \<in> W} = {s \<in> I_set. f s \<in> U \<inter> W}"
    using h_in_U by (by100 blast)
  thus "{s \<in> I_set. f s \<in> W} \<in> I_top" using h_pre by simp
next
  show "f 0 = a'" using assms(4) unfolding top1_is_path_on_def by (by100 blast)
next
  show "f 1 = b'" using assms(4) unfolding top1_is_path_on_def by (by100 blast)
qed

\<comment> \<open>Theorem 63.1(c) — Main result: subgroups generated by [f] and [g] intersect trivially.
   Under the same hypotheses as Theorem_63_1_loop_nontrivial, with additional paths
   \<gamma>: a \<rightarrow> a' in U and \<delta>: a' \<rightarrow> a in V (where a' \<in> A), and g = \<gamma>*\<delta>:
   If the m-fold product f^m is path-homotopic to the k-fold product g^k in X, then m = 0.
   Proof sketch (Munkres Step 3+5):
     - f^m lifts from e_0 = (a,0) to (a, 2*m) in the helix covering (by concatenating shifted lifts).
     - g^k lifts to a loop at e_0 = (a,0) (since each g-lift is a loop, by helix_g_lift_is_loop).
     - By Theorem_54_3 (unique lift endpoints), if [f]^m = [g]^k then (a,2*m) = (a,0), so m = 0.\<close>

\<comment> \<open>Standalone f^m lift: in the helix covering, f^m lifts from (a,0) to (a,2m).
   Factored out for reuse by both 63.1(c) and 63.1(c)_reverse.\<close>
lemma helix_f_power_lift:
  assumes "is_topology_on X TX"
      and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
      and "a \<in> A" and "b \<in> B"
      and "top1_is_path_on U (subspace_topology X TX U) a b alpha"
      and "top1_is_path_on V (subspace_topology X TX V) b a beta"
      and "top1_covering_map_on E TE X TX p0"
      and "is_topology_on E TE"
      and "(a, 0::int) \<in> E"
      and "p0 (a, 0::int) = a"
      \<comment> \<open>TE slice conditions (needed for lift continuity proofs).\<close>
      and "\<And>W n. W \<in> TE \<Longrightarrow> {x \<in> U. (x, 2*n) \<in> W} \<in> TX"
      and "\<And>W n. W \<in> TE \<Longrightarrow> {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX"
      \<comment> \<open>E membership for even/odd sheets.\<close>
      and "\<And>x n. x \<in> U \<Longrightarrow> (x, 2*n) \<in> E"
      and "\<And>x n. x \<in> V - U \<Longrightarrow> (x, 2*n + 1) \<in> E"
      and "\<And>x n. x \<in> A \<Longrightarrow> (x, 2*n + 2) \<in> E"
      and "\<And>x n. x \<in> B \<Longrightarrow> (x, 2*n) \<in> E"
      and "p0 = fst"
      \<comment> \<open>TE characterization: W \<in> TE iff W \<subseteq> E + slice conditions.\<close>
      \<comment> \<open>E characterization for T_E proof.\<close>
      and "\<And>x m. (x, m) \<in> E \<Longrightarrow> (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)"
      and "\<And>W. \<lbrakk>W \<subseteq> E; \<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX;
          \<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                    {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX\<rbrakk> \<Longrightarrow> W \<in> TE"
  shows "\<exists>ftm. top1_is_path_on E TE (a, 0) (a, 2 * int m) ftm \<and>
      (\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product alpha beta) a m s)"
proof -
  \<comment> \<open>Base f-lift: ftilde_0 from (a,0) to (a,2).\<close>
  define ftilde_0 :: "real \<Rightarrow> ('a \<times> int)" where
    "ftilde_0 = (\<lambda>s. if s \<le> 1/2 then (alpha (2*s), 0)
      else (let y = beta (2*s - 1) in
            if y \<in> A then (y, 2) else if y \<in> B then (y, 0) else (y, 1)))"
  define \<alpha>_lift where "\<alpha>_lift = (\<lambda>s. (alpha s, 0::int))"
  define \<beta>_lift where "\<beta>_lift = (\<lambda>s. let y = beta s in
    if y \<in> A then (y, 2::int) else if y \<in> B then (y, 0::int) else (y, 1::int))"
  have hft_eq: "ftilde_0 = top1_path_product \<alpha>_lift \<beta>_lift"
    unfolding ftilde_0_def top1_path_product_def \<alpha>_lift_def \<beta>_lift_def by (rule ext) auto
  have h\<alpha>_lift_path: "top1_is_path_on E TE (a, 0) (b, 0) \<alpha>_lift"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top E TE \<alpha>_lift"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> I_set"
      hence "alpha s \<in> U" using assms(11)
        unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      thus "\<alpha>_lift s \<in> E" unfolding \<alpha>_lift_def using assms(19)[of "alpha s" 0] by simp
    next
      fix W assume hW: "W \<in> TE"
      have hslice: "{x \<in> U. (x, 0::int) \<in> W} \<in> TX"
        using assms(17)[OF hW, of 0] by simp
      have "{s \<in> I_set. \<alpha>_lift s \<in> W} = {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
      proof (rule set_eqI, rule iffI)
        fix s assume "s \<in> {s \<in> I_set. \<alpha>_lift s \<in> W}"
        hence hs: "s \<in> I_set" and "\<alpha>_lift s \<in> W" by auto
        have "alpha s \<in> U" using assms(11) hs
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        thus "s \<in> {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
          using hs \<open>\<alpha>_lift s \<in> W\<close> unfolding \<alpha>_lift_def by auto
      next
        fix s assume "s \<in> {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
        thus "s \<in> {s \<in> I_set. \<alpha>_lift s \<in> W}" unfolding \<alpha>_lift_def by simp
      qed
      moreover have "{s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}} \<in> I_top"
      proof -
        have "{x \<in> U. (x, 0::int) \<in> W} \<in> subspace_topology X TX U"
          unfolding subspace_topology_def using hslice by blast
        thus ?thesis using assms(11)
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      qed
      ultimately show "{s \<in> I_set. \<alpha>_lift s \<in> W} \<in> I_top" by simp
    qed
  next
    show "\<alpha>_lift 0 = (a, 0)" unfolding \<alpha>_lift_def
      using assms(11) unfolding top1_is_path_on_def by (by100 blast)
  next
    show "\<alpha>_lift 1 = (b, 0)" unfolding \<alpha>_lift_def
      using assms(11) unfolding top1_is_path_on_def by (by100 blast)
  qed
  have h\<beta>_lift_path: "top1_is_path_on E TE (b, 0) (a, 2) \<beta>_lift"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top E TE \<beta>_lift"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume hs: "s \<in> I_set"
      have "beta s \<in> V" using assms(12) hs
        unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      thus "\<beta>_lift s \<in> E"
      proof -
        have "beta s \<in> V" by (rule \<open>beta s \<in> V\<close>)
        show ?thesis
        proof (cases "beta s \<in> A")
          case True
          hence "\<beta>_lift s = (beta s, 2)" unfolding \<beta>_lift_def Let_def by simp
          moreover have "(beta s, 2) \<in> E" using assms(21)[of "beta s" 0] True by simp
          ultimately show ?thesis by simp
        next
          case False
          show ?thesis
          proof (cases "beta s \<in> B")
            case True
            hence "\<beta>_lift s = (beta s, 0)" unfolding \<beta>_lift_def Let_def using False by simp
            moreover have "(beta s, 0) \<in> E" using assms(22)[of "beta s" 0] True by simp
            ultimately show ?thesis by simp
          next
            case bFalse: False
            hence "beta s \<in> V - U" using \<open>beta s \<in> V\<close> assms(5) \<open>beta s \<notin> A\<close> by (by100 blast)
            hence "\<beta>_lift s = (beta s, 1)" unfolding \<beta>_lift_def Let_def using False bFalse by simp
            moreover have "(beta s, 1) \<in> E" using assms(20)[of "beta s" 0] \<open>beta s \<in> V - U\<close> by simp
            ultimately show ?thesis by simp
          qed
        qed
      qed
    next
      fix W assume hW: "W \<in> TE"
      have hV_slice: "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
          {x \<in> V - U. (x, 1::int) \<in> W} \<in> TX"
        using assms(18)[OF hW, of 0] by simp
      have heq: "{s \<in> I_set. \<beta>_lift s \<in> W} =
          {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
              {x \<in> V - U. (x, 1::int) \<in> W})}"
      proof (rule set_eqI, rule iffI)
        fix s assume "s \<in> {s \<in> I_set. \<beta>_lift s \<in> W}"
        hence hs: "s \<in> I_set" and hW': "\<beta>_lift s \<in> W" by auto
        have "beta s \<in> V" using assms(12) hs
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        thus "s \<in> {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union>
            {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W})}"
          using hs hW' assms(5,6) unfolding \<beta>_lift_def Let_def by (auto split: if_splits)
      next
        fix s assume "s \<in> {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union>
            {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W})}"
        hence hs: "s \<in> I_set" and hds: "beta s \<in> {x \<in> A. (x, 2::int) \<in> W} \<union>
            {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W}" by auto
        have hAsub: "A \<subseteq> U" and hBsub: "B \<subseteq> U" using assms(5) by (by100 blast)+
        have "\<beta>_lift s \<in> W"
        proof -
          have "beta s \<in> A \<and> (beta s, 2) \<in> W \<or>
                beta s \<in> B \<and> (beta s, 0) \<in> W \<or>
                beta s \<in> V - U \<and> (beta s, 1) \<in> W" using hds by (by100 blast)
          thus ?thesis unfolding \<beta>_lift_def Let_def using assms(6) hAsub hBsub
            by (auto split: if_splits)
        qed
        thus "s \<in> {s \<in> I_set. \<beta>_lift s \<in> W}" using hs by (by100 blast)
      qed
      have hV_sub_open: "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
          {x \<in> V - U. (x, 1::int) \<in> W} \<in> subspace_topology X TX V"
      proof -
        have "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
            {x \<in> V - U. (x, 1::int) \<in> W} \<subseteq> V"
          using assms(5) by (by100 blast)
        thus ?thesis using hV_slice unfolding subspace_topology_def by (by100 blast)
      qed
      have "{s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
          {x \<in> V - U. (x, 1::int) \<in> W})} \<in> I_top"
        using assms(12) hV_sub_open
        unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      thus "{s \<in> I_set. \<beta>_lift s \<in> W} \<in> I_top" using heq by simp
    qed
  next
    show "\<beta>_lift 0 = (b, 0)" unfolding \<beta>_lift_def Let_def
      using assms(12) assms(10) assms(6) unfolding top1_is_path_on_def by auto
  next
    show "\<beta>_lift 1 = (a, 2)" unfolding \<beta>_lift_def Let_def
      using assms(12) assms(9) assms(6) unfolding top1_is_path_on_def by auto
  qed
  have hft0_path: "top1_is_path_on E TE (a, 0) (a, 2) ftilde_0"
    unfolding hft_eq by (rule top1_path_product_is_path[OF assms(14) h\<alpha>_lift_path h\<beta>_lift_path])
  have hft0_proj: "\<forall>s\<in>I_set. p0 (ftilde_0 s) = top1_path_product alpha beta s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "p0 (ftilde_0 s) = top1_path_product alpha beta s"
    proof (cases "s \<le> 1/2")
      case True thus ?thesis unfolding ftilde_0_def assms(23) top1_path_product_def by simp
    next
      case False
      define y where "y = beta (2*s - 1)"
      have "ftilde_0 s = (if y \<in> A then (y, 2) else if y \<in> B then (y, 0) else (y, 1))"
        unfolding ftilde_0_def y_def using False by (simp add: Let_def)
      hence "p0 (ftilde_0 s) = y" unfolding assms(23) by (cases "y \<in> A"; cases "y \<in> B"; simp)
      thus ?thesis unfolding y_def top1_path_product_def using False by simp
    qed
  qed
  \<comment> \<open>Deck transformation T and induction — same as Theorem_63_1_c.\<close>
  define T :: "'a \<times> int \<Rightarrow> 'a \<times> int" where "T = (\<lambda>(x,m). (x, m + 2))"
  have hT_E: "\<And>e. e \<in> E \<Longrightarrow> T e \<in> E"
  proof -
    fix e assume he: "e \<in> E"
    obtain x n where hxn: "e = (x, n)" by (cases e) auto
    have "(even n \<and> x \<in> U) \<or> (odd n \<and> x \<in> V - U)"
      using assms(24)[of x n] he hxn by simp
    thus "T e \<in> E"
    proof
      assume "even n \<and> x \<in> U"
      hence "x \<in> U" "even (n + 2)" by auto
      thus ?thesis using assms(19)[of x "(n+2) div 2"] hxn unfolding T_def by simp
    next
      assume "odd n \<and> x \<in> V - U"
      hence "x \<in> V - U" "odd (n + 2)" by auto
      thus ?thesis using assms(20)[of x "(n + 2 - 1) div 2"] hxn unfolding T_def
        by (simp add: algebra_simps)
    qed
  qed
  have hT_p0: "\<And>e. p0 (T e) = p0 e" unfolding T_def assms(23) by auto
  have hT_cont: "top1_continuous_map_on E TE E TE T"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix e assume "e \<in> E" thus "T e \<in> E" using hT_E by simp
  next
    fix W assume hW: "W \<in> TE"
    show "{e \<in> E. T e \<in> W} \<in> TE"
    proof (rule assms(25))
      show "{e \<in> E. T e \<in> W} \<subseteq> E" by (by100 blast)
    next
      show "\<forall>n::int. {x \<in> U. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}} \<in> TX"
      proof
        fix n :: int
        have "{x \<in> U. (x, 2*n) \<in> {e \<in> E. T e \<in> W}} = {x \<in> U. (x, 2*(n+1)) \<in> W}"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> {x \<in> U. (x, 2*n) \<in> {e \<in> E. T e \<in> W}}"
          hence "x \<in> U" "T (x, 2*n) \<in> W" by auto
          thus "x \<in> {x \<in> U. (x, 2*(n+1)) \<in> W}" unfolding T_def by (simp add: algebra_simps)
        next
          fix x assume "x \<in> {x \<in> U. (x, 2*(n+1)) \<in> W}"
          hence "x \<in> U" "(x, 2*n + 2) \<in> W" by (auto simp: algebra_simps)
          moreover have "(x, 2*n) \<in> E" using \<open>x \<in> U\<close> assms(19) by simp
          moreover have "T (x, 2*n) = (x, 2*n + 2)" unfolding T_def by simp
          ultimately show "x \<in> {x \<in> U. (x, 2*n) \<in> {e \<in> E. T e \<in> W}}" by auto
        qed
        also have "... \<in> TX" using assms(17)[OF hW, of "n+1"] by (simp add: algebra_simps)
        finally show "{x \<in> U. (x, 2*n) \<in> {e \<in> E. T e \<in> W}} \<in> TX" .
      qed
    next
      show "\<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> {e \<in> E. T e \<in> W}} \<union>
          {x \<in> B. (x, 2*n) \<in> {e \<in> E. T e \<in> W}} \<union>
          {x \<in> V - U. (x, 2*n + 1) \<in> {e \<in> E. T e \<in> W}} \<in> TX"
      proof
        fix n :: int
        have h_A: "{x \<in> A. (x, 2*n + 2) \<in> {e \<in> E. T e \<in> W}} = {x \<in> A. (x, 2*(n+1) + 2) \<in> W}"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> {x \<in> A. (x, 2*n + 2) \<in> {e \<in> E. T e \<in> W}}"
          thus "x \<in> {x \<in> A. (x, 2*(n+1) + 2) \<in> W}" unfolding T_def by (simp add: algebra_simps)
        next
          fix x assume "x \<in> {x \<in> A. (x, 2*(n+1) + 2) \<in> W}"
          hence "x \<in> A" "(x, 2*n + 4) \<in> W" by (auto simp: algebra_simps)
          moreover have "(x, 2*n+2) \<in> E" using \<open>x \<in> A\<close> assms(21) by simp
          moreover have "T (x, 2*n+2) = (x, 2*n+4)" unfolding T_def by simp
          ultimately show "x \<in> {x \<in> A. (x, 2*n+2) \<in> {e \<in> E. T e \<in> W}}" by auto
        qed
        have h_B: "{x \<in> B. (x, 2*n) \<in> {e \<in> E. T e \<in> W}} = {x \<in> B. (x, 2*(n+1)) \<in> W}"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> {x \<in> B. (x, 2*n) \<in> {e \<in> E. T e \<in> W}}"
          thus "x \<in> {x \<in> B. (x, 2*(n+1)) \<in> W}" unfolding T_def by (simp add: algebra_simps)
        next
          fix x assume "x \<in> {x \<in> B. (x, 2*(n+1)) \<in> W}"
          hence "x \<in> B" "(x, 2*n+2) \<in> W" by (auto simp: algebra_simps)
          moreover have "(x, 2*n) \<in> E" using \<open>x \<in> B\<close> assms(22) by simp
          moreover have "T (x, 2*n) = (x, 2*n+2)" unfolding T_def by simp
          ultimately show "x \<in> {x \<in> B. (x, 2*n) \<in> {e \<in> E. T e \<in> W}}" by auto
        qed
        have h_VU: "{x \<in> V-U. (x, 2*n+1) \<in> {e \<in> E. T e \<in> W}} = {x \<in> V-U. (x, 2*(n+1)+1) \<in> W}"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> {x \<in> V-U. (x, 2*n+1) \<in> {e \<in> E. T e \<in> W}}"
          thus "x \<in> {x \<in> V-U. (x, 2*(n+1)+1) \<in> W}" unfolding T_def by (simp add: algebra_simps)
        next
          fix x assume "x \<in> {x \<in> V-U. (x, 2*(n+1)+1) \<in> W}"
          hence "x \<in> V-U" "(x, 2*n+3) \<in> W" by (auto simp: algebra_simps)
          moreover have "(x, 2*n+1) \<in> E" using \<open>x \<in> V-U\<close> assms(20) by simp
          moreover have "T (x, 2*n+1) = (x, 2*n+3)" unfolding T_def by simp
          ultimately show "x \<in> {x \<in> V-U. (x, 2*n+1) \<in> {e \<in> E. T e \<in> W}}" by auto
        qed
        have "{x \<in> A. (x, 2*n+2) \<in> {e \<in> E. T e \<in> W}} \<union>
            {x \<in> B. (x, 2*n) \<in> {e \<in> E. T e \<in> W}} \<union>
            {x \<in> V-U. (x, 2*n+1) \<in> {e \<in> E. T e \<in> W}}
          = {x \<in> A. (x, 2*(n+1)+2) \<in> W} \<union> {x \<in> B. (x, 2*(n+1)) \<in> W} \<union>
            {x \<in> V-U. (x, 2*(n+1)+1) \<in> W}"
          using h_A h_B h_VU by simp
        also have "... \<in> TX" using assms(18)[OF hW, of "n+1"] by (simp add: algebra_simps)
        finally show "{x \<in> A. (x, 2*n+2) \<in> {e \<in> E. T e \<in> W}} \<union>
            {x \<in> B. (x, 2*n) \<in> {e \<in> E. T e \<in> W}} \<union>
            {x \<in> V-U. (x, 2*n+1) \<in> {e \<in> E. T e \<in> W}} \<in> TX" .
      qed
    qed
  qed
  \<comment> \<open>Induction: f^m lift from (a,0) to (a,2m).\<close>
  show ?thesis
  proof (induction m)
    case 0
    have "top1_is_path_on E TE (a, 0) (a, 0) (top1_constant_path (a, 0))"
      by (rule top1_constant_path_is_path[OF assms(14,15)])
    moreover have "\<forall>s\<in>I_set. p0 (top1_constant_path (a, 0) s) =
        top1_path_power (top1_path_product alpha beta) a 0 s"
      by (simp add: top1_constant_path_def assms(16))
    ultimately show ?case by (intro exI[of _ "top1_constant_path (a, 0)"]) auto
  next
    case (Suc m)
    obtain ftm where hftm: "top1_is_path_on E TE (a, 0) (a, 2 * int m) ftm"
        and hftm_proj: "\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product alpha beta) a m s"
      using Suc by (by100 blast)
    define Tftm where "Tftm = T \<circ> ftm"
    have hTftm_path: "top1_is_path_on E TE (a, 2) (a, 2 * int m + 2) Tftm"
      unfolding top1_is_path_on_def top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume hs: "s \<in> I_set"
      have "ftm s \<in> E" using hftm hs unfolding top1_is_path_on_def top1_continuous_map_on_def
        by (by100 blast)
      thus "Tftm s \<in> E" unfolding Tftm_def comp_def using hT_E by (by100 blast)
    next
      fix W assume hW: "W \<in> TE"
      have hTinvW: "{e \<in> E. T e \<in> W} \<in> TE"
        using hT_cont hW unfolding top1_continuous_map_on_def by (by100 blast)
      have "{s \<in> I_set. Tftm s \<in> W} = {s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}}"
      proof (rule set_eqI, rule iffI)
        fix s assume "s \<in> {s \<in> I_set. Tftm s \<in> W}"
        hence hs: "s \<in> I_set" and "Tftm s \<in> W" by auto
        have "ftm s \<in> E" using hftm hs unfolding top1_is_path_on_def top1_continuous_map_on_def
          by (by100 blast)
        moreover have "T (ftm s) \<in> W" using \<open>Tftm s \<in> W\<close> unfolding Tftm_def comp_def by simp
        ultimately show "s \<in> {s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}}" using hs by (by100 blast)
      next
        fix s assume "s \<in> {s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}}"
        thus "s \<in> {s \<in> I_set. Tftm s \<in> W}" unfolding Tftm_def comp_def by (by100 blast)
      qed
      moreover have "{s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}} \<in> I_top"
        using hftm hTinvW unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      ultimately show "{s \<in> I_set. Tftm s \<in> W} \<in> I_top" by simp
    next
      show "Tftm 0 = (a, 2)"
      proof -
        have "ftm 0 = (a, 0)" using hftm unfolding top1_is_path_on_def by (by100 blast)
        thus ?thesis unfolding Tftm_def comp_def T_def by simp
      qed
    next
      show "Tftm 1 = (a, 2 * int m + 2)"
      proof -
        have "ftm 1 = (a, 2 * int m)" using hftm unfolding top1_is_path_on_def by (by100 blast)
        thus ?thesis unfolding Tftm_def comp_def T_def by simp
      qed
    qed
    have hTftm_proj: "\<forall>s\<in>I_set. p0 (Tftm s) = top1_path_power (top1_path_product alpha beta) a m s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "p0 (Tftm s) = p0 (T (ftm s))" unfolding Tftm_def comp_def by simp
      also have "... = p0 (ftm s)" using hT_p0 by simp
      also have "... = top1_path_power (top1_path_product alpha beta) a m s"
        using hftm_proj hs by (by100 blast)
      finally show "p0 (Tftm s) = top1_path_power (top1_path_product alpha beta) a m s" .
    qed
    define ftSm where "ftSm = top1_path_product ftilde_0 Tftm"
    have hftSm_path: "top1_is_path_on E TE (a, 0) (a, 2 * int m + 2) ftSm"
      unfolding ftSm_def by (rule top1_path_product_is_path[OF assms(14) hft0_path hTftm_path])
    have hftSm_end: "top1_is_path_on E TE (a, 0) (a, 2 * int (Suc m)) ftSm"
      using hftSm_path by (simp add: algebra_simps)
    have hftSm_proj: "\<forall>s\<in>I_set. p0 (ftSm s) = top1_path_power (top1_path_product alpha beta) a (Suc m) s"
    proof
      fix s assume hs: "s \<in> I_set"
      show "p0 (ftSm s) = top1_path_power (top1_path_product alpha beta) a (Suc m) s"
      proof (cases "s \<le> 1/2")
        case True
        have "ftSm s = ftilde_0 (2*s)" unfolding ftSm_def top1_path_product_def using True by simp
        have "2*s \<in> I_set" using hs True unfolding top1_unit_interval_def by auto
        hence "p0 (ftilde_0 (2*s)) = top1_path_product alpha beta (2*s)"
          using hft0_proj by (by100 blast)
        moreover have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
            = (top1_path_product alpha beta) (2*s)"
        proof -
          have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
              = top1_path_product (top1_path_product alpha beta)
                  (top1_path_power (top1_path_product alpha beta) a m) s" by simp
          also have "... = (top1_path_product alpha beta) (2*s)"
            unfolding top1_path_product_def using True by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>ftSm s = ftilde_0 (2*s)\<close> by simp
      next
        case False
        have "ftSm s = Tftm (2*s - 1)" unfolding ftSm_def top1_path_product_def using False by simp
        have "2*s - 1 \<in> I_set" using hs False unfolding top1_unit_interval_def by auto
        hence "p0 (Tftm (2*s - 1)) = top1_path_power (top1_path_product alpha beta) a m (2*s - 1)"
          using hTftm_proj by (by100 blast)
        moreover have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
            = top1_path_power (top1_path_product alpha beta) a m (2*s - 1)"
        proof -
          have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
              = top1_path_product (top1_path_product alpha beta)
                  (top1_path_power (top1_path_product alpha beta) a m) s" by simp
          also have "... = top1_path_power (top1_path_product alpha beta) a m (2*s - 1)"
            unfolding top1_path_product_def using False by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>ftSm s = Tftm (2*s - 1)\<close> by simp
      qed
    qed
    show ?case by (intro exI[of _ ftSm]) (use hftSm_end hftSm_proj in blast)
  qed
qed

lemma Theorem_63_1_c_subgroups_trivial:
  assumes "is_topology_on X TX"
      and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
      and "a \<in> A" and "b \<in> B"
      and "top1_is_path_on U (subspace_topology X TX U) a b alpha"
      and "top1_is_path_on V (subspace_topology X TX V) b a beta"
      \<comment> \<open>Additional 63.1(c) data: a' \<in> A, paths \<gamma> and \<delta>.\<close>
      and "a' \<in> A"
      and "top1_is_path_on U (subspace_topology X TX U) a a' gamma"
      and "top1_is_path_on V (subspace_topology X TX V) a' a delta"
      \<comment> \<open>Homotopy between f^m and g^k.\<close>
      and "top1_path_homotopic_on X TX a a
            (top1_path_power (top1_path_product alpha beta) a m)
            (top1_path_power (top1_path_product gamma delta) a k)"
  shows "m = 0"
proof (rule ccontr)
  assume "m \<noteq> 0" hence hm: "m > 0" by simp
  \<comment> \<open>Step 1: Construct helix covering (same as Theorem_63_1).\<close>
  have ha_U: "a \<in> U" using assms(5,9) by (by100 blast)
  have hb_U: "b \<in> U" using assms(5,10) by (by100 blast)
  have ha_V: "a \<in> V" using assms(5,9) by (by100 blast)
  have hb_V: "b \<in> V" using assms(5,10) by (by100 blast)
  have ha'_U: "a' \<in> U" using assms(5,13) by (by100 blast)
  have ha'_V: "a' \<in> V" using assms(5,13) by (by100 blast)
  have hU_open_TX: "U \<in> TX" using assms(2) unfolding openin_on_def by (by100 blast)
  have hV_open_TX: "V \<in> TX" using assms(3) unfolding openin_on_def by (by100 blast)
  have hA_open_TX: "A \<in> TX" using assms(7) unfolding openin_on_def by (by100 blast)
  have hB_open_TX: "B \<in> TX" using assms(8) unfolding openin_on_def by (by100 blast)
  define E :: "('a \<times> int) set" where
    "E = {(x, m). (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)}"
  define TE :: "('a \<times> int) set set" where
    "TE = {W. W \<subseteq> E \<and>
      (\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX) \<and>
      (\<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX)}"
  define p0 :: "'a \<times> int \<Rightarrow> 'a" where "p0 = fst"
  define e0 :: "'a \<times> int" where "e0 = (a, 0)"
  have he0_E: "e0 \<in> E" unfolding e0_def E_def using ha_U by simp
  have hp0e0: "p0 e0 = a" unfolding p0_def e0_def by simp
  have hcov_and_TE: "top1_covering_map_on E TE X TX p0 \<and> is_topology_on E TE"
  proof -
    note h = helix_covering_construction[OF assms(1-8)]
    have "E = {x. even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
      unfolding E_def by auto
    moreover have "TE = {W. W \<subseteq> E \<and>
        (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
        (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
              {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
      unfolding TE_def E_def by auto
    moreover have "p0 = fst" unfolding p0_def by simp
    ultimately show ?thesis using h by simp
  qed
  hence hTE: "is_topology_on E TE" and hcov: "top1_covering_map_on E TE X TX p0"
    by auto
  \<comment> \<open>Step 2: f^m lifts from e0 = (a,0) to (a, 2*(int m)) in E.\<close>
  \<comment> \<open>First construct the base f-lift (sheet 0): from (a,0) to (a,2).\<close>
  define ftilde_0 :: "real \<Rightarrow> ('a \<times> int)" where
    "ftilde_0 = (\<lambda>s. if s \<le> 1/2
      then (alpha (2*s), 0)
      else (let y = beta (2*s - 1) in
            if y \<in> A then (y, 2)
            else if y \<in> B then (y, 0)
            else (y, 1)))"
  have hft0_path: "top1_is_path_on E TE e0 (a, 2) ftilde_0"
  proof -
    define \<alpha>_lift where "\<alpha>_lift = (\<lambda>s. (alpha s, 0::int))"
    define \<beta>_lift where "\<beta>_lift = (\<lambda>s. let y = beta s in
      if y \<in> A then (y, 2::int) else if y \<in> B then (y, 0::int) else (y, 1::int))"
    have hft_eq: "ftilde_0 = top1_path_product \<alpha>_lift \<beta>_lift"
      unfolding ftilde_0_def top1_path_product_def \<alpha>_lift_def \<beta>_lift_def by (rule ext) auto
    have h\<alpha>_lift_path: "top1_is_path_on E TE (a, 0) (b, 0) \<alpha>_lift"
      unfolding top1_is_path_on_def
    proof (intro conjI)
      show "top1_continuous_map_on I_set I_top E TE \<alpha>_lift"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix s assume "s \<in> I_set"
        hence "alpha s \<in> U" using assms(11)
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        thus "\<alpha>_lift s \<in> E" unfolding \<alpha>_lift_def E_def by auto
      next
        fix W assume hW: "W \<in> TE"
        have hslice: "{x \<in> U. (x, 0::int) \<in> W} \<in> TX"
        proof -
          have "\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
          hence "{x \<in> U. (x, 2*(0::int)) \<in> W} \<in> TX" by (rule spec)
          thus ?thesis by simp
        qed
        have "{s \<in> I_set. \<alpha>_lift s \<in> W} = {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
        proof (rule set_eqI, rule iffI)
          fix s assume "s \<in> {s \<in> I_set. \<alpha>_lift s \<in> W}"
          hence hs: "s \<in> I_set" and hW': "\<alpha>_lift s \<in> W" by auto
          have "alpha s \<in> U" using assms(11) hs
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          thus "s \<in> {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
            using hs hW' unfolding \<alpha>_lift_def by auto
        next
          fix s assume "s \<in> {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
          thus "s \<in> {s \<in> I_set. \<alpha>_lift s \<in> W}" unfolding \<alpha>_lift_def by simp
        qed
        moreover have "{s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}} \<in> I_top"
        proof -
          have "{x \<in> U. (x, 0::int) \<in> W} \<in> subspace_topology X TX U"
            unfolding subspace_topology_def using hslice by blast
          thus ?thesis using assms(11)
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        qed
        ultimately show "{s \<in> I_set. \<alpha>_lift s \<in> W} \<in> I_top" by simp
      qed
    next
      show "\<alpha>_lift 0 = (a, 0)" unfolding \<alpha>_lift_def
        using assms(11) unfolding top1_is_path_on_def by (by100 blast)
    next
      show "\<alpha>_lift 1 = (b, 0)" unfolding \<alpha>_lift_def
        using assms(11) unfolding top1_is_path_on_def by (by100 blast)
    qed
    have h\<beta>_lift_path: "top1_is_path_on E TE (b, 0) (a, 2) \<beta>_lift"
      unfolding top1_is_path_on_def
    proof (intro conjI)
      show "top1_continuous_map_on I_set I_top E TE \<beta>_lift"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix s assume hs: "s \<in> I_set"
        have "beta s \<in> V" using assms(12) hs
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        thus "\<beta>_lift s \<in> E" unfolding \<beta>_lift_def E_def Let_def
          using assms(5) by auto
      next
        fix W assume hW: "W \<in> TE"
        \<comment> \<open>V-slice at sheet 0: {x \<in> A. (x,2) \<in> W} \<union> {x \<in> B. (x,0) \<in> W} \<union> {x \<in> V-U. (x,1) \<in> W} \<in> TX.\<close>
        have hV_slice: "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
            {x \<in> V - U. (x, 1::int) \<in> W} \<in> TX"
        proof -
          have "\<forall>n::int. {x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
          hence "{x \<in> A. (x, 2*(0::int)+2) \<in> W} \<union> {x \<in> B. (x, 2*(0::int)) \<in> W} \<union>
              {x \<in> V-U. (x, 2*(0::int)+1) \<in> W} \<in> TX" by (rule spec)
          thus ?thesis by simp
        qed
        \<comment> \<open>The preimage: \<beta>_lift(s) \<in> W iff beta(s) \<in> V-slice.\<close>
        have heq: "{s \<in> I_set. \<beta>_lift s \<in> W} =
            {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
                {x \<in> V - U. (x, 1::int) \<in> W})}"
        proof (rule set_eqI, rule iffI)
          fix s assume "s \<in> {s \<in> I_set. \<beta>_lift s \<in> W}"
          hence hs: "s \<in> I_set" and hW': "\<beta>_lift s \<in> W" by auto
          have "beta s \<in> V" using assms(12) hs
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          have "beta s \<in> A \<union> B \<or> beta s \<in> V - U" using \<open>beta s \<in> V\<close> assms(5) by (by100 blast)
          thus "s \<in> {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
              {x \<in> V - U. (x, 1::int) \<in> W})}"
            using hs hW' assms(6) unfolding \<beta>_lift_def Let_def by (auto split: if_splits)
        next
          fix s assume "s \<in> {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union>
              {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W})}"
          hence hs: "s \<in> I_set" and hbs: "beta s \<in> {x \<in> A. (x, 2::int) \<in> W} \<union>
              {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W}" by auto
          have "\<beta>_lift s \<in> W"
          proof -
            have hAsub: "A \<subseteq> U" and hBsub: "B \<subseteq> U" using assms(5) by (by100 blast)+
            have "beta s \<in> A \<and> (beta s, 2) \<in> W \<or>
                  beta s \<in> B \<and> (beta s, 0) \<in> W \<or>
                  beta s \<in> V - U \<and> (beta s, 1) \<in> W" using hbs by (by100 blast)
            thus ?thesis unfolding \<beta>_lift_def Let_def using assms(6) hAsub hBsub
              by (auto split: if_splits)
          qed
          thus "s \<in> {s \<in> I_set. \<beta>_lift s \<in> W}" using hs by (by100 blast)
        qed
        \<comment> \<open>The V-slice is open in TX, hence in subspace topology of V.\<close>
        have hV_sub_open: "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
            {x \<in> V - U. (x, 1::int) \<in> W} \<in> subspace_topology X TX V"
        proof -
          have hsub: "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
              {x \<in> V - U. (x, 1::int) \<in> W} \<subseteq> V"
            using assms(5) by (by100 blast)
          thus ?thesis using hV_slice unfolding subspace_topology_def by (by100 blast)
        qed
        have "{s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
            {x \<in> V - U. (x, 1::int) \<in> W})} \<in> I_top"
          using assms(12) hV_sub_open
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        thus "{s \<in> I_set. \<beta>_lift s \<in> W} \<in> I_top" using heq by simp
      qed
    next
      show "\<beta>_lift 0 = (b, 0)" unfolding \<beta>_lift_def Let_def
        using assms(12) assms(10) assms(6) unfolding top1_is_path_on_def by auto
    next
      show "\<beta>_lift 1 = (a, 2)" unfolding \<beta>_lift_def Let_def
        using assms(12) assms(9) assms(6) unfolding top1_is_path_on_def by auto
    qed
    show ?thesis unfolding hft_eq e0_def
      by (rule top1_path_product_is_path[OF hTE h\<alpha>_lift_path h\<beta>_lift_path])
  qed
  have hft0_proj: "\<forall>s\<in>I_set. p0 (ftilde_0 s) = top1_path_product alpha beta s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "p0 (ftilde_0 s) = top1_path_product alpha beta s"
    proof (cases "s \<le> 1/2")
      case True
      thus ?thesis unfolding ftilde_0_def p0_def top1_path_product_def by simp
    next
      case False
      define y where "y = beta (2*s - 1)"
      have "ftilde_0 s = (if y \<in> A then (y, 2) else if y \<in> B then (y, 0) else (y, 1))"
        unfolding ftilde_0_def y_def using False by (simp add: Let_def)
      hence "p0 (ftilde_0 s) = y"
        unfolding p0_def by (cases "y \<in> A"; cases "y \<in> B"; simp)
      thus ?thesis unfolding y_def top1_path_product_def using False by simp
    qed
  qed
  \<comment> \<open>Deck transformation: T(x,m) = (x, m+2). Shifts sheets by 1.\<close>
  define T :: "'a \<times> int \<Rightarrow> 'a \<times> int" where "T = (\<lambda>(x,m). (x, m + 2))"
  have hT_E: "\<And>e. e \<in> E \<Longrightarrow> T e \<in> E" unfolding T_def E_def by auto
  have hT_p0: "\<And>e. p0 (T e) = p0 e" unfolding T_def p0_def by auto
  have hT_cont: "top1_continuous_map_on E TE E TE T"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix e assume "e \<in> E" thus "T e \<in> E" using hT_E by simp
  next
    fix W assume hW: "W \<in> TE"
    \<comment> \<open>T^{-1}(W) = {e \<in> E. T e \<in> W}. Show this is in TE.\<close>
    show "{e \<in> E. T e \<in> W} \<in> TE"
      unfolding TE_def
    proof (intro CollectI conjI allI)
      show "{e \<in> E. T e \<in> W} \<subseteq> E" by (by100 blast)
    next
      \<comment> \<open>Even slices: {x \<in> U. (x, 2n) \<in> T^{-1}(W)} = {x \<in> U. (x, 2n+2) \<in> W} = even slice n+1 of W.\<close>
      fix n :: int
      have "{x \<in> U. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}} = {x \<in> U. (x, 2 * (n + 1)) \<in> W}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {x \<in> U. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}}"
        hence "x \<in> U" "T (x, 2*n) \<in> W" by auto
        hence "(x, 2*n + 2) \<in> W" unfolding T_def by simp
        thus "x \<in> {x \<in> U. (x, 2 * (n + 1)) \<in> W}" using \<open>x \<in> U\<close> by (simp add: algebra_simps)
      next
        fix x assume "x \<in> {x \<in> U. (x, 2 * (n + 1)) \<in> W}"
        hence "x \<in> U" "(x, 2*n + 2) \<in> W" by (auto simp: algebra_simps)
        have "(x, 2*n) \<in> E" unfolding E_def using \<open>x \<in> U\<close> by auto
        moreover have "T (x, 2*n) = (x, 2*n + 2)" unfolding T_def by simp
        ultimately show "x \<in> {x \<in> U. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}}"
          using \<open>x \<in> U\<close> \<open>(x, 2*n + 2) \<in> W\<close> by auto
      qed
      also have "... \<in> TX" using hW unfolding TE_def by (by100 blast)
      finally show "{x \<in> U. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}} \<in> TX" .
    next
      \<comment> \<open>Odd slices: shift by +2, getting odd slice n+1 of W.\<close>
      fix n :: int
      have h_A: "{x \<in> A. (x, 2 * n + 2) \<in> {e \<in> E. T e \<in> W}} = {x \<in> A. (x, 2 * (n+1) + 2) \<in> W}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {x \<in> A. (x, 2 * n + 2) \<in> {e \<in> E. T e \<in> W}}"
        hence "x \<in> A" "T (x, 2*n + 2) \<in> W" by auto
        thus "x \<in> {x \<in> A. (x, 2 * (n+1) + 2) \<in> W}" unfolding T_def by (simp add: algebra_simps)
      next
        fix x assume "x \<in> {x \<in> A. (x, 2 * (n+1) + 2) \<in> W}"
        hence "x \<in> A" "(x, 2*n + 4) \<in> W" by (auto simp: algebra_simps)
        have "x \<in> U" using \<open>x \<in> A\<close> assms(5) by (by100 fast)
        have "(x, 2*n+2) \<in> E" unfolding E_def using \<open>x \<in> U\<close> by auto
        moreover have "T (x, 2*n+2) = (x, 2*n+4)" unfolding T_def by simp
        ultimately show "x \<in> {x \<in> A. (x, 2 * n + 2) \<in> {e \<in> E. T e \<in> W}}"
          using \<open>x \<in> A\<close> \<open>(x, 2*n+4) \<in> W\<close> by auto
      qed
      have h_B: "{x \<in> B. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}} = {x \<in> B. (x, 2 * (n+1)) \<in> W}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {x \<in> B. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}}"
        hence "x \<in> B" "T (x, 2*n) \<in> W" by auto
        thus "x \<in> {x \<in> B. (x, 2 * (n+1)) \<in> W}" unfolding T_def by (simp add: algebra_simps)
      next
        fix x assume "x \<in> {x \<in> B. (x, 2 * (n+1)) \<in> W}"
        hence "x \<in> B" "(x, 2*n + 2) \<in> W" by (auto simp: algebra_simps)
        have "x \<in> U" using \<open>x \<in> B\<close> assms(5) by (by100 blast)
        have "(x, 2*n) \<in> E" unfolding E_def using \<open>x \<in> U\<close> by auto
        moreover have "T (x, 2*n) = (x, 2*n+2)" unfolding T_def by simp
        ultimately show "x \<in> {x \<in> B. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}}"
          using \<open>x \<in> B\<close> \<open>(x, 2*n+2) \<in> W\<close> by auto
      qed
      have h_VU: "{x \<in> V - U. (x, 2 * n + 1) \<in> {e \<in> E. T e \<in> W}} = {x \<in> V - U. (x, 2 * (n+1) + 1) \<in> W}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {x \<in> V - U. (x, 2 * n + 1) \<in> {e \<in> E. T e \<in> W}}"
        hence "x \<in> V - U" "T (x, 2*n+1) \<in> W" by auto
        thus "x \<in> {x \<in> V - U. (x, 2 * (n+1) + 1) \<in> W}" unfolding T_def by (simp add: algebra_simps)
      next
        fix x assume "x \<in> {x \<in> V - U. (x, 2 * (n+1) + 1) \<in> W}"
        hence "x \<in> V - U" "(x, 2*n + 3) \<in> W" by (auto simp: algebra_simps)
        have "(x, 2*n+1) \<in> E" unfolding E_def using \<open>x \<in> V - U\<close> by auto
        moreover have "T (x, 2*n+1) = (x, 2*n+3)" unfolding T_def by simp
        ultimately show "x \<in> {x \<in> V - U. (x, 2 * n + 1) \<in> {e \<in> E. T e \<in> W}}"
          using \<open>x \<in> V - U\<close> \<open>(x, 2*n+3) \<in> W\<close> by auto
      qed
      have "{x \<in> A. (x, 2 * n + 2) \<in> {e \<in> E. T e \<in> W}} \<union>
          {x \<in> B. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}} \<union>
          {x \<in> V - U. (x, 2 * n + 1) \<in> {e \<in> E. T e \<in> W}}
        = {x \<in> A. (x, 2*(n+1)+2) \<in> W} \<union> {x \<in> B. (x, 2*(n+1)) \<in> W} \<union>
          {x \<in> V - U. (x, 2*(n+1)+1) \<in> W}"
        using h_A h_B h_VU by simp
      also have "... \<in> TX" using hW unfolding TE_def by (by100 blast)
      finally show "{x \<in> A. (x, 2 * n + 2) \<in> {e \<in> E. T e \<in> W}} \<union>
          {x \<in> B. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}} \<union>
          {x \<in> V - U. (x, 2 * n + 1) \<in> {e \<in> E. T e \<in> W}} \<in> TX" .
    qed
  qed
  \<comment> \<open>T^n maps e0=(a,0) to (a, 2*int n).\<close>
  have hT_iter: "\<And>n::nat. (T ^^ n) e0 = (a, 2 * int n)"
  proof -
    fix n :: nat show "(T ^^ n) e0 = (a, 2 * int n)"
    proof (induction n)
      case 0 thus ?case unfolding e0_def by simp
    next
      case (Suc n) thus ?case unfolding T_def by simp
    qed
  qed
  \<comment> \<open>By induction: f^m lifts from e0 to (a, 2*int m).\<close>
  have hfm_lift: "\<exists>ftilde_m. top1_is_path_on E TE e0 (a, 2 * int m) ftilde_m \<and>
      (\<forall>s\<in>I_set. p0 (ftilde_m s) = top1_path_power (top1_path_product alpha beta) a m s)"
  proof (induction m)
    case 0
    have "top1_is_path_on E TE e0 e0 (top1_constant_path e0)"
      by (rule top1_constant_path_is_path[OF hTE he0_E])
    moreover have "e0 = (a, 2 * int 0)" unfolding e0_def by simp
    moreover have "\<forall>s\<in>I_set. p0 (top1_constant_path e0 s) = top1_path_power (top1_path_product alpha beta) a 0 s"
    proof
      fix s assume "s \<in> I_set"
      have lhs: "p0 (top1_constant_path e0 s) = a"
        unfolding top1_constant_path_def using hp0e0 by simp
      have rhs: "top1_path_power (top1_path_product alpha beta) a 0 s = a"
        by (simp add: top1_constant_path_def)
      show "p0 (top1_constant_path e0 s) = top1_path_power (top1_path_product alpha beta) a 0 s"
        using lhs rhs by simp
    qed
    ultimately show ?case by (intro exI[of _ "top1_constant_path e0"]) auto
  next
    case (Suc m)
    obtain ftm where hftm: "top1_is_path_on E TE e0 (a, 2 * int m) ftm"
        and hftm_proj: "\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product alpha beta) a m s"
      using Suc by (by100 blast)
    \<comment> \<open>T \<circ> ftm: path from T(e0)=(a,2) to T((a,2m))=(a,2m+2), projects to f^m.\<close>
    define Tftm where "Tftm = T \<circ> ftm"
    have hTftm_path: "top1_is_path_on E TE (a, 2) (a, 2 * int m + 2) Tftm"
      unfolding top1_is_path_on_def top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume hs: "s \<in> I_set"
      have "ftm s \<in> E" using hftm hs unfolding top1_is_path_on_def top1_continuous_map_on_def
        by (by100 blast)
      thus "Tftm s \<in> E" unfolding Tftm_def comp_def using hT_E by (by100 blast)
    next
      fix W assume hW: "W \<in> TE"
      have hTinvW: "{e \<in> E. T e \<in> W} \<in> TE"
        using hT_cont hW unfolding top1_continuous_map_on_def by (by100 blast)
      have "{s \<in> I_set. Tftm s \<in> W} = {s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}}"
      proof (rule set_eqI, rule iffI)
        fix s assume "s \<in> {s \<in> I_set. Tftm s \<in> W}"
        hence hs: "s \<in> I_set" and hTW: "Tftm s \<in> W" by auto
        have "ftm s \<in> E" using hftm hs unfolding top1_is_path_on_def top1_continuous_map_on_def
          by (by100 blast)
        moreover have "T (ftm s) \<in> W" using hTW unfolding Tftm_def comp_def by simp
        ultimately show "s \<in> {s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}}" using hs by (by100 blast)
      next
        fix s assume "s \<in> {s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}}"
        thus "s \<in> {s \<in> I_set. Tftm s \<in> W}" unfolding Tftm_def comp_def by (by100 blast)
      qed
      moreover have "{s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}} \<in> I_top"
        using hftm hTinvW unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      ultimately show "{s \<in> I_set. Tftm s \<in> W} \<in> I_top" by simp
    next
      show "Tftm 0 = (a, 2)"
      proof -
        have "ftm 0 = e0" using hftm unfolding top1_is_path_on_def by (by100 blast)
        thus ?thesis unfolding Tftm_def comp_def T_def e0_def by simp
      qed
    next
      show "Tftm 1 = (a, 2 * int m + 2)"
      proof -
        have "ftm 1 = (a, 2 * int m)" using hftm unfolding top1_is_path_on_def by (by100 blast)
        thus ?thesis unfolding Tftm_def comp_def T_def by simp
      qed
    qed
    have hTftm_proj: "\<forall>s\<in>I_set. p0 (Tftm s) = top1_path_power (top1_path_product alpha beta) a m s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "p0 (Tftm s) = p0 (T (ftm s))" unfolding Tftm_def comp_def by simp
      also have "... = p0 (ftm s)" using hT_p0 by simp
      also have "... = top1_path_power (top1_path_product alpha beta) a m s"
        using hftm_proj hs by (by100 blast)
      finally show "p0 (Tftm s) = top1_path_power (top1_path_product alpha beta) a m s" .
    qed
    \<comment> \<open>Concatenate: ftilde_0 * (T \<circ> ftm) from e0 to (a, 2*(m+1)).\<close>
    define ftSm where "ftSm = top1_path_product ftilde_0 Tftm"
    have hftSm_path: "top1_is_path_on E TE e0 (a, 2 * int m + 2) ftSm"
    proof -
      have "top1_is_path_on E TE (a, 0) (a, 2 * int m + 2) ftSm"
        unfolding ftSm_def
        by (rule top1_path_product_is_path[OF hTE])
           (use hft0_path hTftm_path e0_def in auto)
      thus ?thesis unfolding e0_def by simp
    qed
    have h_int_eq: "(2::int) * int m + 2 = 2 + 2 * int m" by linarith
    have hftSm_end: "top1_is_path_on E TE e0 (a, 2 * int (Suc m)) ftSm"
      using hftSm_path by (simp add: h_int_eq algebra_simps)
    have hftSm_proj: "\<forall>s\<in>I_set. p0 (ftSm s) = top1_path_power (top1_path_product alpha beta) a (Suc m) s"
    proof
      fix s assume hs: "s \<in> I_set"
      show "p0 (ftSm s) = top1_path_power (top1_path_product alpha beta) a (Suc m) s"
      proof (cases "s \<le> 1/2")
        case True
        have "ftSm s = ftilde_0 (2*s)" unfolding ftSm_def top1_path_product_def using True by simp
        have "2*s \<in> I_set" using hs True unfolding top1_unit_interval_def by auto
        hence "p0 (ftilde_0 (2*s)) = top1_path_product alpha beta (2*s)"
          using hft0_proj by (by100 blast)
        moreover have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
            = (top1_path_product alpha beta) (2*s)"
        proof -
          have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
              = top1_path_product (top1_path_product alpha beta)
                  (top1_path_power (top1_path_product alpha beta) a m) s" by simp
          also have "... = (top1_path_product alpha beta) (2*s)"
            unfolding top1_path_product_def using True by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>ftSm s = ftilde_0 (2*s)\<close> unfolding p0_def by simp
      next
        case False
        have "ftSm s = Tftm (2*s - 1)" unfolding ftSm_def top1_path_product_def using False by simp
        have "2*s - 1 \<in> I_set" using hs False unfolding top1_unit_interval_def by auto
        hence "p0 (Tftm (2*s - 1)) = top1_path_power (top1_path_product alpha beta) a m (2*s - 1)"
          using hTftm_proj by (by100 blast)
        moreover have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
            = top1_path_power (top1_path_product alpha beta) a m (2*s - 1)"
        proof -
          have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
              = top1_path_product (top1_path_product alpha beta)
                  (top1_path_power (top1_path_product alpha beta) a m) s" by simp
          also have "... = top1_path_power (top1_path_product alpha beta) a m (2*s - 1)"
            unfolding top1_path_product_def using False by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>ftSm s = Tftm (2*s - 1)\<close> unfolding p0_def by simp
      qed
    qed
    show ?case by (intro exI[of _ ftSm]) (use hftSm_end hftSm_proj in blast)
  qed
  \<comment> \<open>Step 3: g^k lifts to a loop at e0 = (a,0) in E.\<close>
  \<comment> \<open>First get the single g-lift from helix_g_lift_is_loop.\<close>
  have hg1_lift: "\<exists>gt. top1_is_path_on E TE e0 e0 gt \<and>
      (\<forall>s\<in>I_set. p0 (gt s) = top1_path_product gamma delta s)"
  proof -
    \<comment> \<open>Rather than extracting from helix_g_lift_is_loop (whose E'/TE'/p0' would need
       matching to our local E/TE/p0), we directly define the g-lift using the same
       formula as in helix_g_lift_is_loop and prove its properties.\<close>
    define gtilde :: "real \<Rightarrow> ('a \<times> int)" where
      "gtilde = (\<lambda>s. if s \<le> 1/2
        then (gamma (2*s), 0)
        else (let y = delta (2*s - 1) in
              if y \<in> A then (y, 0)
              else if y \<in> B then (y, -2)
              else (y, -1)))"
    have hgt_path: "top1_is_path_on E TE e0 e0 gtilde"
    proof -
      define \<gamma>_lift where "\<gamma>_lift = (\<lambda>s. (gamma s, 0::int))"
      define \<delta>_lift where "\<delta>_lift = (\<lambda>s. let y = delta s in
        if y \<in> A then (y, 0::int) else if y \<in> B then (y, -2::int) else (y, -1::int))"
      have hgt_eq: "gtilde = top1_path_product \<gamma>_lift \<delta>_lift"
        unfolding gtilde_def top1_path_product_def \<gamma>_lift_def \<delta>_lift_def by (rule ext) auto
      have h\<gamma>_lift_path: "top1_is_path_on E TE (a, 0) (a', 0) \<gamma>_lift"
        unfolding top1_is_path_on_def
      proof (intro conjI)
        show "top1_continuous_map_on I_set I_top E TE \<gamma>_lift"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s assume "s \<in> I_set"
          hence "gamma s \<in> U" using assms(14)
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          thus "\<gamma>_lift s \<in> E" unfolding \<gamma>_lift_def E_def by auto
        next
          fix W assume hW: "W \<in> TE"
          have hslice: "{x \<in> U. (x, 0::int) \<in> W} \<in> TX"
          proof -
            have "\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
            hence "{x \<in> U. (x, 2*(0::int)) \<in> W} \<in> TX" by (rule spec)
            thus ?thesis by simp
          qed
          have "{s \<in> I_set. \<gamma>_lift s \<in> W} = {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
          proof (rule set_eqI, rule iffI)
            fix s assume "s \<in> {s \<in> I_set. \<gamma>_lift s \<in> W}"
            hence hs: "s \<in> I_set" and hW': "\<gamma>_lift s \<in> W" by auto
            have "gamma s \<in> U" using assms(14) hs
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "s \<in> {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
              using hs hW' unfolding \<gamma>_lift_def by auto
          next
            fix s assume "s \<in> {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
            thus "s \<in> {s \<in> I_set. \<gamma>_lift s \<in> W}" unfolding \<gamma>_lift_def by simp
          qed
          moreover have "{s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}} \<in> I_top"
          proof -
            have "{x \<in> U. (x, 0::int) \<in> W} \<in> subspace_topology X TX U"
              unfolding subspace_topology_def using hslice by blast
            thus ?thesis using assms(14)
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          qed
          ultimately show "{s \<in> I_set. \<gamma>_lift s \<in> W} \<in> I_top" by simp
        qed
      next
        show "\<gamma>_lift 0 = (a, 0)" unfolding \<gamma>_lift_def
          using assms(14) unfolding top1_is_path_on_def by (by100 blast)
      next
        show "\<gamma>_lift 1 = (a', 0)" unfolding \<gamma>_lift_def
          using assms(14) unfolding top1_is_path_on_def by (by100 blast)
      qed
      have h\<delta>_lift_path: "top1_is_path_on E TE (a', 0) (a, 0) \<delta>_lift"
        unfolding top1_is_path_on_def
      proof (intro conjI)
        show "top1_continuous_map_on I_set I_top E TE \<delta>_lift"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s assume hs: "s \<in> I_set"
          have "delta s \<in> V" using assms(15) hs
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          thus "\<delta>_lift s \<in> E" unfolding \<delta>_lift_def E_def Let_def using assms(5) by auto
        next
          fix W assume hW: "W \<in> TE"
          have hV_slice: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
              {x \<in> V - U. (x, -1::int) \<in> W} \<in> TX"
          proof -
            have "\<forall>n::int. {x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V-U. (x, 2*n+1) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
            hence "{x \<in> A. (x, 2*(-1::int)+2) \<in> W} \<union> {x \<in> B. (x, 2*(-1::int)) \<in> W} \<union>
                {x \<in> V-U. (x, 2*(-1::int)+1) \<in> W} \<in> TX" by (rule spec)
            thus ?thesis by simp
          qed
          have heq: "{s \<in> I_set. \<delta>_lift s \<in> W} =
              {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
                  {x \<in> V - U. (x, -1::int) \<in> W})}"
          proof (rule set_eqI, rule iffI)
            fix s assume "s \<in> {s \<in> I_set. \<delta>_lift s \<in> W}"
            hence hs: "s \<in> I_set" and hW': "\<delta>_lift s \<in> W" by auto
            have "delta s \<in> V" using assms(15) hs
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "s \<in> {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})}"
              using hs hW' assms(5,6) unfolding \<delta>_lift_def Let_def by (auto split: if_splits)
          next
            fix s assume "s \<in> {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})}"
            hence hs: "s \<in> I_set" and hds: "delta s \<in> {x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W}" by auto
            have hAsub: "A \<subseteq> U" and hBsub: "B \<subseteq> U" using assms(5) by (by100 blast)+
            have "\<delta>_lift s \<in> W"
            proof -
              have "delta s \<in> A \<and> (delta s, 0) \<in> W \<or>
                    delta s \<in> B \<and> (delta s, -2) \<in> W \<or>
                    delta s \<in> V - U \<and> (delta s, -1) \<in> W" using hds by (by100 blast)
              thus ?thesis unfolding \<delta>_lift_def Let_def using assms(6) hAsub hBsub
                by (auto split: if_splits)
            qed
            thus "s \<in> {s \<in> I_set. \<delta>_lift s \<in> W}" using hs by (by100 blast)
          qed
          have hV_sub_open: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
              {x \<in> V - U. (x, -1::int) \<in> W} \<in> subspace_topology X TX V"
          proof -
            have hsub: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
                {x \<in> V - U. (x, -1::int) \<in> W} \<subseteq> V"
              using assms(5) by (by100 blast)
            thus ?thesis using hV_slice unfolding subspace_topology_def by (by100 blast)
          qed
          have "{s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
              {x \<in> V - U. (x, -1::int) \<in> W})} \<in> I_top"
            using assms(15) hV_sub_open
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          thus "{s \<in> I_set. \<delta>_lift s \<in> W} \<in> I_top" using heq by simp
        qed
      next
        show "\<delta>_lift 0 = (a', 0)" unfolding \<delta>_lift_def Let_def
          using assms(15) assms(13) assms(6) unfolding top1_is_path_on_def by auto
      next
        show "\<delta>_lift 1 = (a, 0)" unfolding \<delta>_lift_def Let_def
          using assms(15) assms(9) assms(6) unfolding top1_is_path_on_def by auto
      qed
      show ?thesis unfolding hgt_eq e0_def
        by (rule top1_path_product_is_path[OF hTE h\<gamma>_lift_path h\<delta>_lift_path])
    qed
    have hgt_proj: "\<forall>s\<in>I_set. p0 (gtilde s) = top1_path_product gamma delta s"
    proof
      fix s assume hs: "s \<in> I_set"
      show "p0 (gtilde s) = top1_path_product gamma delta s"
      proof (cases "s \<le> 1/2")
        case True
        thus ?thesis unfolding gtilde_def p0_def top1_path_product_def by simp
      next
        case False
        define y where "y = delta (2*s - 1)"
        have "gtilde s = (if y \<in> A then (y, 0) else if y \<in> B then (y, -2) else (y, -1))"
          unfolding gtilde_def y_def using False by (simp add: Let_def)
        hence "p0 (gtilde s) = y"
          unfolding p0_def by (cases "y \<in> A"; cases "y \<in> B"; simp)
        thus ?thesis unfolding y_def top1_path_product_def using False by simp
      qed
    qed
    show ?thesis by (intro exI[of _ gtilde]) (use hgt_path hgt_proj in blast)
  qed
  obtain gt1 where hgt1: "top1_is_path_on E TE e0 e0 gt1"
      and hgt1_proj: "\<forall>s\<in>I_set. p0 (gt1 s) = top1_path_product gamma delta s"
    using hg1_lift by (by100 blast)
  \<comment> \<open>By induction: g^k lifts to a loop at e0.\<close>
  have hgk_lift: "\<exists>gtilde_k. top1_is_path_on E TE e0 e0 gtilde_k \<and>
      (\<forall>s\<in>I_set. p0 (gtilde_k s) = top1_path_power (top1_path_product gamma delta) a k s)"
  proof (induction k)
    case 0
    have "top1_is_path_on E TE e0 e0 (top1_constant_path e0)"
      by (rule top1_constant_path_is_path[OF hTE he0_E])
    moreover have "\<forall>s\<in>I_set. p0 (top1_constant_path e0 s) = top1_path_power (top1_path_product gamma delta) a 0 s"
    proof
      fix s assume "s \<in> I_set"
      have "p0 (top1_constant_path e0 s) = p0 e0" unfolding top1_constant_path_def by simp
      also have "... = a" using hp0e0 by simp
      also have "... = top1_constant_path a s" unfolding top1_constant_path_def by simp
      also have "... = top1_path_power (top1_path_product gamma delta) a 0 s" by simp
      finally show "p0 (top1_constant_path e0 s) = top1_path_power (top1_path_product gamma delta) a 0 s" .
    qed
    ultimately show ?case by (intro exI[of _ "top1_constant_path e0"]) (by100 blast)
  next
    case (Suc k)
    obtain gtk where hgtk: "top1_is_path_on E TE e0 e0 gtk"
        and hgtk_proj: "\<forall>s\<in>I_set. p0 (gtk s) = top1_path_power (top1_path_product gamma delta) a k s"
      using Suc by (by100 blast)
    define gtSk where "gtSk = top1_path_product gt1 gtk"
    have hgtSk: "top1_is_path_on E TE e0 e0 gtSk"
      unfolding gtSk_def by (rule top1_path_product_is_path[OF hTE hgt1 hgtk])
    have hgtSk_proj: "\<forall>s\<in>I_set. p0 (gtSk s) = top1_path_power (top1_path_product gamma delta) a (Suc k) s"
    proof
      fix s assume hs: "s \<in> I_set"
      show "p0 (gtSk s) = top1_path_power (top1_path_product gamma delta) a (Suc k) s"
      proof (cases "s \<le> 1/2")
        case True
        have "gtSk s = gt1 (2*s)" unfolding gtSk_def top1_path_product_def using True by simp
        have "2*s \<in> I_set" using hs True unfolding top1_unit_interval_def by auto
        hence "p0 (gt1 (2*s)) = top1_path_product gamma delta (2*s)"
          using hgt1_proj by (by100 blast)
        moreover have "top1_path_power (top1_path_product gamma delta) a (Suc k) s
            = top1_path_product gamma delta (2*s)"
        proof -
          have "top1_path_power (top1_path_product gamma delta) a (Suc k) s
              = top1_path_product (top1_path_product gamma delta)
                  (top1_path_power (top1_path_product gamma delta) a k) s" by simp
          also have "... = (top1_path_product gamma delta) (2*s)"
            unfolding top1_path_product_def using True by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>gtSk s = gt1 (2*s)\<close> unfolding p0_def by simp
      next
        case False
        have hs_half: "s > 1/2" using False by simp
        have "gtSk s = gtk (2*s - 1)" unfolding gtSk_def top1_path_product_def using False by simp
        have "2*s - 1 \<in> I_set" using hs False unfolding top1_unit_interval_def by auto
        hence "p0 (gtk (2*s - 1)) = top1_path_power (top1_path_product gamma delta) a k (2*s - 1)"
          using hgtk_proj by (by100 blast)
        moreover have "top1_path_power (top1_path_product gamma delta) a (Suc k) s
            = top1_path_power (top1_path_product gamma delta) a k (2*s - 1)"
        proof -
          have "top1_path_power (top1_path_product gamma delta) a (Suc k) s
              = top1_path_product (top1_path_product gamma delta)
                  (top1_path_power (top1_path_product gamma delta) a k) s" by simp
          also have "... = top1_path_power (top1_path_product gamma delta) a k (2*s - 1)"
            unfolding top1_path_product_def using False by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>gtSk s = gtk (2*s - 1)\<close> unfolding p0_def by simp
      qed
    qed
    show ?case by (intro exI[of _ gtSk]) (use hgtSk hgtSk_proj in blast)
  qed
  \<comment> \<open>Step 4: By Theorem_54_3, since [f]^m = [g]^k (path-homotopic),
     the lifts have the same endpoint: (a, 2*(int m)) = (a, 0) = e0.\<close>
  obtain ftilde_m where hft: "top1_is_path_on E TE e0 (a, 2 * int m) ftilde_m"
      and hft_proj: "\<forall>s\<in>I_set. p0 (ftilde_m s) = top1_path_power (top1_path_product alpha beta) a m s"
    using hfm_lift by (by100 blast)
  obtain gtilde_k where hgt: "top1_is_path_on E TE e0 e0 gtilde_k"
      and hgt_proj: "\<forall>s\<in>I_set. p0 (gtilde_k s) = top1_path_power (top1_path_product gamma delta) a k s"
    using hgk_lift by (by100 blast)
  have hf_loop_X: "top1_is_loop_on X TX a (top1_path_product alpha beta)"
  proof -
    have h\<alpha>_X: "top1_is_path_on X TX a b alpha"
      by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(2) assms(11)])
         (use assms(4) in blast)
    have h\<beta>_X: "top1_is_path_on X TX b a beta"
      by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(3) assms(12)])
         (use assms(4) in blast)
    show ?thesis unfolding top1_is_loop_on_def
      using top1_path_product_is_path[OF assms(1) h\<alpha>_X h\<beta>_X] by simp
  qed
  have hg_loop_X: "top1_is_loop_on X TX a (top1_path_product gamma delta)"
  proof -
    have h\<gamma>_X: "top1_is_path_on X TX a a' gamma"
      by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(2) assms(14)])
         (use assms(4) in blast)
    have h\<delta>_X: "top1_is_path_on X TX a' a delta"
      by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(3) assms(15)])
         (use assms(4) in blast)
    show ?thesis unfolding top1_is_loop_on_def
      using top1_path_product_is_path[OF assms(1) h\<gamma>_X h\<delta>_X] by simp
  qed
  have hfm_path: "top1_is_path_on X TX a a (top1_path_power (top1_path_product alpha beta) a m)"
    by (rule top1_path_power_is_path[OF assms(1) hf_loop_X])
  have hgk_path: "top1_is_path_on X TX a a (top1_path_power (top1_path_product gamma delta) a k)"
    by (rule top1_path_power_is_path[OF assms(1) hg_loop_X])
  have "e0 = (a, 2 * int m)"
  proof -
    have heq: "(a, 2 * int m) = e0 \<and>
        top1_path_homotopic_on E TE e0 (a, 2 * int m) ftilde_m gtilde_k"
      by (rule Theorem_54_3[OF hcov hTE assms(1) he0_E hp0e0
          hfm_path hgk_path assms(16) hft hft_proj hgt hgt_proj])
    thus ?thesis by simp
  qed
  hence "2 * int m = (0::int)" unfolding e0_def by simp
  hence "m = 0" by simp
  thus False using hm by simp
qed

\<comment> \<open>Abstract endpoint lemma: if f^m lifts from e0 to (a,2m) and h^k lifts to a loop at e0,
   and [f^m] \<simeq> [h^k], then m = 0 by Theorem_54_3.\<close>
lemma covering_lift_endpoint_contradiction:
  assumes "top1_covering_map_on E TE X TX p0"
      and "is_topology_on E TE" and "is_topology_on X TX"
      and "(a, 0::int) \<in> E" and "p0 (a, 0::int) = a"
      \<comment> \<open>f^m lifts from (a,0) to (a, 2*int m).\<close>
      and "top1_is_path_on E TE (a, 0) (a, 2 * int m) ftm"
      and "\<forall>s\<in>I_set. p0 (ftm s) = fm s"
      and "top1_is_path_on X TX a a fm"
      \<comment> \<open>h^k lifts to a LOOP at (a,0).\<close>
      and "top1_is_path_on E TE (a, 0) (a, 0) hkl"
      and "\<forall>s\<in>I_set. p0 (hkl s) = hk s"
      and "top1_is_path_on X TX a a hk"
      \<comment> \<open>f^m \<simeq> h^k.\<close>
      and "top1_path_homotopic_on X TX a a fm hk"
  shows "m = 0"
proof -
  have "(a, 2 * int m) = (a, 0::int)"
    using conjunct1[OF Theorem_54_3[OF assms(1-5,8,11,12,6,7,9,10)]] by simp
  hence "2 * int m = (0::int)" by simp
  thus ?thesis by simp
qed

\<comment> \<open>63.1(c) for the reverse loop g\<inverse>: same helix, reverse g-lift is a loop.\<close>
lemma Theorem_63_1_c_subgroups_trivial_reverse:
  assumes "is_topology_on X TX"
      and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
      and "a \<in> A" and "b \<in> B"
      and "top1_is_path_on U (subspace_topology X TX U) a b alpha"
      and "top1_is_path_on V (subspace_topology X TX V) b a beta"
      and "a' \<in> A"
      and "top1_is_path_on U (subspace_topology X TX U) a a' gamma"
      and "top1_is_path_on V (subspace_topology X TX V) a' a delta"
      and "top1_path_homotopic_on X TX a a
            (top1_path_power (top1_path_product alpha beta) a m)
            (top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k)"
  shows "m = 0"
proof -
  \<comment> \<open>Build helix (same as 63.1(c)).\<close>
  have ha_U: "a \<in> U" using assms(5,9) by (by100 blast)
  define E :: "('a \<times> int) set" where
    "E = {(x, m). (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)}"
  define TE :: "('a \<times> int) set set" where
    "TE = {W. W \<subseteq> E \<and>
      (\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX) \<and>
      (\<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX)}"
  define p0 :: "'a \<times> int \<Rightarrow> 'a" where "p0 = fst"
  have he0: "(a, 0::int) \<in> E" unfolding E_def using ha_U by simp
  have hp0: "p0 (a, 0::int) = a" unfolding p0_def by simp
  have hcov_TE: "top1_covering_map_on E TE X TX p0 \<and> is_topology_on E TE"
  proof -
    note h = helix_covering_construction[OF assms(1-8)]
    have "E = {x. even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
      unfolding E_def by auto
    moreover have "TE = {W. W \<subseteq> E \<and>
        (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
        (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
              {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
      unfolding TE_def E_def by auto
    moreover have "p0 = fst" unfolding p0_def by simp
    ultimately show ?thesis using h by simp
  qed
  hence hTE: "is_topology_on E TE" and hcov: "top1_covering_map_on E TE X TX p0" by auto
  \<comment> \<open>f^m lift from (a,0) to (a,2m). Same construction as in Theorem_63_1_c.\<close>
  have hfm_lift: "\<exists>ftm. top1_is_path_on E TE (a, 0) (a, 2 * int m) ftm \<and>
      (\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product alpha beta) a m s)"
  proof (rule helix_f_power_lift[OF assms(1-12) hcov hTE he0 hp0])
    show "\<And>W n. W \<in> TE \<Longrightarrow> {x \<in> U. (x, 2 * n) \<in> W} \<in> TX"
      unfolding TE_def by (by100 blast)
    show "\<And>W n. W \<in> TE \<Longrightarrow> {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
        {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX"
      unfolding TE_def by (by100 blast)
    show "\<And>x n. x \<in> U \<Longrightarrow> (x, 2*n) \<in> E" unfolding E_def by auto
    show "\<And>x n. x \<in> V - U \<Longrightarrow> (x, 2*n + 1) \<in> E" unfolding E_def by auto
    show "\<And>x n. x \<in> A \<Longrightarrow> (x, 2*n + 2) \<in> E"
    proof -
      fix x :: 'a and n :: int assume "x \<in> A"
      hence "x \<in> U" using assms(5) by (by100 blast)
      thus "(x, 2*n + 2) \<in> E" unfolding E_def by auto
    qed
    show "\<And>x n. x \<in> B \<Longrightarrow> (x, 2*n) \<in> E"
    proof -
      fix x :: 'a and n :: int assume "x \<in> B"
      hence "x \<in> U" using assms(5) by (by100 blast)
      thus "(x, 2*n) \<in> E" unfolding E_def by auto
    qed
    show "p0 = fst" unfolding p0_def by simp
    show "\<And>x m. (x, m) \<in> E \<Longrightarrow> (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)"
      unfolding E_def by auto
    show "\<And>W. \<lbrakk>W \<subseteq> E; \<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX;
        \<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX\<rbrakk> \<Longrightarrow> W \<in> TE"
      unfolding TE_def by (by100 blast)
  qed
  \<comment> \<open>(g\<inverse>)^k lift: reverse of g-lift is a loop at (a,0), projects to g\<inverse>.
     By induction, (g\<inverse>)^k lifts to a loop at (a,0).\<close>
  \<comment> \<open>Construct single g-lift directly (same formula as in 63.1(c) proof).\<close>
  define gtilde :: "real \<Rightarrow> ('a \<times> int)" where
    "gtilde = (\<lambda>s. if s \<le> 1/2 then (gamma (2*s), 0)
      else (let y = delta (2*s - 1) in
            if y \<in> A then (y, 0) else if y \<in> B then (y, -2) else (y, -1)))"
  have hg1_lift: "\<exists>gt. top1_is_path_on E TE (a, 0) (a, 0) gt \<and>
      (\<forall>s\<in>I_set. p0 (gt s) = top1_path_product gamma delta s)"
  proof (intro exI[of _ gtilde] conjI)
    show "top1_is_path_on E TE (a, 0) (a, 0) gtilde"
    proof -
      define \<gamma>_lift where "\<gamma>_lift = (\<lambda>s. (gamma s, 0::int))"
      define \<delta>_lift where "\<delta>_lift = (\<lambda>s. let y = delta s in
        if y \<in> A then (y, 0::int) else if y \<in> B then (y, -2::int) else (y, -1::int))"
      have hgt_eq: "gtilde = top1_path_product \<gamma>_lift \<delta>_lift"
        unfolding gtilde_def top1_path_product_def \<gamma>_lift_def \<delta>_lift_def by (rule ext) auto
      have h\<gamma>_lift_path: "top1_is_path_on E TE (a, 0) (a', 0) \<gamma>_lift"
        unfolding top1_is_path_on_def
      proof (intro conjI)
        show "top1_continuous_map_on I_set I_top E TE \<gamma>_lift"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s assume "s \<in> I_set"
          hence "gamma s \<in> U" using assms(14)
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          thus "\<gamma>_lift s \<in> E" unfolding \<gamma>_lift_def E_def by auto
        next
          fix W assume hW: "W \<in> TE"
          have hslice: "{x \<in> U. (x, 0::int) \<in> W} \<in> TX"
          proof -
            have "\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
            hence "{x \<in> U. (x, 2*(0::int)) \<in> W} \<in> TX" by (rule spec)
            thus ?thesis by simp
          qed
          have "{s \<in> I_set. \<gamma>_lift s \<in> W} = {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
          proof (rule set_eqI, rule iffI)
            fix s assume "s \<in> {s \<in> I_set. \<gamma>_lift s \<in> W}"
            hence hs: "s \<in> I_set" and hW': "\<gamma>_lift s \<in> W" by auto
            have "gamma s \<in> U" using assms(14) hs
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "s \<in> {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
              using hs hW' unfolding \<gamma>_lift_def by auto
          next
            fix s assume "s \<in> {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
            thus "s \<in> {s \<in> I_set. \<gamma>_lift s \<in> W}" unfolding \<gamma>_lift_def by simp
          qed
          moreover have "{s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}} \<in> I_top"
          proof -
            have "{x \<in> U. (x, 0::int) \<in> W} \<in> subspace_topology X TX U"
              unfolding subspace_topology_def using hslice by blast
            thus ?thesis using assms(14)
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          qed
          ultimately show "{s \<in> I_set. \<gamma>_lift s \<in> W} \<in> I_top" by simp
        qed
      next
        show "\<gamma>_lift 0 = (a, 0)" unfolding \<gamma>_lift_def
          using assms(14) unfolding top1_is_path_on_def by (by100 blast)
      next
        show "\<gamma>_lift 1 = (a', 0)" unfolding \<gamma>_lift_def
          using assms(14) unfolding top1_is_path_on_def by (by100 blast)
      qed
      have h\<delta>_lift_path: "top1_is_path_on E TE (a', 0) (a, 0) \<delta>_lift"
        unfolding top1_is_path_on_def
      proof (intro conjI)
        show "top1_continuous_map_on I_set I_top E TE \<delta>_lift"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s assume hs: "s \<in> I_set"
          have "delta s \<in> V" using assms(15) hs
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          thus "\<delta>_lift s \<in> E" unfolding \<delta>_lift_def E_def Let_def using assms(5) by auto
        next
          fix W assume hW: "W \<in> TE"
          have hV_slice: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
              {x \<in> V - U. (x, -1::int) \<in> W} \<in> TX"
          proof -
            have "\<forall>n::int. {x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V-U. (x, 2*n+1) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
            hence "{x \<in> A. (x, 2*(-1::int)+2) \<in> W} \<union> {x \<in> B. (x, 2*(-1::int)) \<in> W} \<union>
                {x \<in> V-U. (x, 2*(-1::int)+1) \<in> W} \<in> TX" by (rule spec)
            thus ?thesis by simp
          qed
          have heq: "{s \<in> I_set. \<delta>_lift s \<in> W} =
              {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
                  {x \<in> V - U. (x, -1::int) \<in> W})}"
          proof (rule set_eqI, rule iffI)
            fix s assume "s \<in> {s \<in> I_set. \<delta>_lift s \<in> W}"
            hence hs: "s \<in> I_set" and hW': "\<delta>_lift s \<in> W" by auto
            have "delta s \<in> V" using assms(15) hs
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "s \<in> {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})}"
              using hs hW' assms(5,6) unfolding \<delta>_lift_def Let_def by (auto split: if_splits)
          next
            fix s assume "s \<in> {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})}"
            hence hs: "s \<in> I_set" and hds: "delta s \<in> {x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W}" by auto
            have hAsub: "A \<subseteq> U" and hBsub: "B \<subseteq> U" using assms(5) by (by100 blast)+
            have "\<delta>_lift s \<in> W"
            proof -
              have "delta s \<in> A \<and> (delta s, 0) \<in> W \<or>
                    delta s \<in> B \<and> (delta s, -2) \<in> W \<or>
                    delta s \<in> V - U \<and> (delta s, -1) \<in> W" using hds by (by100 blast)
              thus ?thesis unfolding \<delta>_lift_def Let_def using assms(6) hAsub hBsub
                by (auto split: if_splits)
            qed
            thus "s \<in> {s \<in> I_set. \<delta>_lift s \<in> W}" using hs by (by100 blast)
          qed
          have hV_sub_open: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
              {x \<in> V - U. (x, -1::int) \<in> W} \<in> subspace_topology X TX V"
          proof -
            have hsub: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
                {x \<in> V - U. (x, -1::int) \<in> W} \<subseteq> V"
              using assms(5) by (by100 blast)
            thus ?thesis using hV_slice unfolding subspace_topology_def by (by100 blast)
          qed
          have "{s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
              {x \<in> V - U. (x, -1::int) \<in> W})} \<in> I_top"
            using assms(15) hV_sub_open
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          thus "{s \<in> I_set. \<delta>_lift s \<in> W} \<in> I_top" using heq by simp
        qed
      next
        show "\<delta>_lift 0 = (a', 0)" unfolding \<delta>_lift_def Let_def
          using assms(15) assms(13) assms(6) unfolding top1_is_path_on_def by auto
      next
        show "\<delta>_lift 1 = (a, 0)" unfolding \<delta>_lift_def Let_def
          using assms(15) assms(9) assms(6) unfolding top1_is_path_on_def by auto
      qed
      show ?thesis unfolding hgt_eq
        by (rule top1_path_product_is_path[OF hTE h\<gamma>_lift_path h\<delta>_lift_path])
    qed
    show "\<forall>s\<in>I_set. p0 (gtilde s) = top1_path_product gamma delta s"
    proof
      fix s assume hs: "s \<in> I_set"
      show "p0 (gtilde s) = top1_path_product gamma delta s"
      proof (cases "s \<le> 1/2")
        case True thus ?thesis unfolding gtilde_def p0_def top1_path_product_def by simp
      next
        case False
        define y where "y = delta (2*s - 1)"
        have "gtilde s = (if y \<in> A then (y, 0) else if y \<in> B then (y, -2) else (y, -1))"
          unfolding gtilde_def y_def using False by (simp add: Let_def)
        hence "p0 (gtilde s) = y"
          unfolding p0_def by (cases "y \<in> A"; cases "y \<in> B"; simp)
        thus ?thesis unfolding y_def top1_path_product_def using False by simp
      qed
    qed
  qed
  obtain gt where hgt: "top1_is_path_on E TE (a, 0) (a, 0) gt"
      and hgt_proj: "\<forall>s\<in>I_set. p0 (gt s) = top1_path_product gamma delta s"
    using hg1_lift by (by100 blast)
  \<comment> \<open>Reverse g-lift: loop at (a,0), projects to g\<inverse>.\<close>
  define gt_rev where "gt_rev = top1_path_reverse gt"
  have hgt_rev_path: "top1_is_path_on E TE (a, 0) (a, 0) gt_rev"
  proof -
    have "top1_is_path_on E TE (a, 0) (a, 0) (top1_path_reverse gt)"
      using top1_path_reverse_is_path[OF hgt] hgt
      unfolding top1_is_path_on_def top1_path_reverse_def by auto
    thus ?thesis unfolding gt_rev_def by simp
  qed
  have hgt_rev_proj: "\<forall>s\<in>I_set. p0 (gt_rev s) = top1_path_reverse (top1_path_product gamma delta) s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "1 - s \<in> I_set" using hs unfolding top1_unit_interval_def by auto
    show "p0 (gt_rev s) = top1_path_reverse (top1_path_product gamma delta) s"
      unfolding gt_rev_def top1_path_reverse_def using hgt_proj \<open>1 - s \<in> I_set\<close> p0_def by auto
  qed
  \<comment> \<open>By induction: (g\<inverse>)^k lifts to a loop at (a,0).\<close>
  have hginvk_lift: "\<exists>gkl. top1_is_path_on E TE (a, 0) (a, 0) gkl \<and>
      (\<forall>s\<in>I_set. p0 (gkl s) = top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k s)"
  proof (induction k)
    case 0
    have "top1_is_path_on E TE (a, 0) (a, 0) (top1_constant_path (a, 0))"
      by (rule top1_constant_path_is_path[OF hTE he0])
    moreover have "\<forall>s\<in>I_set. p0 (top1_constant_path (a, 0) s) =
        top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a 0 s"
      by (simp add: top1_constant_path_def hp0)
    ultimately show ?case by (intro exI[of _ "top1_constant_path (a, 0)"]) auto
  next
    case (Suc k)
    obtain gkl where hgkl_k: "top1_is_path_on E TE (a, 0) (a, 0) gkl"
        and hgkl_proj_k: "\<forall>s\<in>I_set. p0 (gkl s) =
            top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k s"
      using Suc by (by100 blast)
    define gSk where "gSk = top1_path_product gt_rev gkl"
    have "top1_is_path_on E TE (a, 0) (a, 0) gSk"
      unfolding gSk_def by (rule top1_path_product_is_path[OF hTE hgt_rev_path hgkl_k])
    moreover have "\<forall>s\<in>I_set. p0 (gSk s) =
        top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a (Suc k) s"
    proof
      fix s assume hs: "s \<in> I_set"
      show "p0 (gSk s) = top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a (Suc k) s"
      proof (cases "s \<le> 1/2")
        case True
        have "gSk s = gt_rev (2*s)" unfolding gSk_def top1_path_product_def using True by simp
        have "2*s \<in> I_set" using hs True unfolding top1_unit_interval_def by auto
        hence "p0 (gt_rev (2*s)) = top1_path_reverse (top1_path_product gamma delta) (2*s)"
          using hgt_rev_proj by (by100 blast)
        moreover have "top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a (Suc k) s
            = top1_path_reverse (top1_path_product gamma delta) (2*s)"
        proof -
          have "top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a (Suc k) s
              = top1_path_product (top1_path_reverse (top1_path_product gamma delta))
                  (top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k) s" by simp
          also have "... = (top1_path_reverse (top1_path_product gamma delta)) (2*s)"
            unfolding top1_path_product_def using True by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>gSk s = gt_rev (2*s)\<close> unfolding p0_def by simp
      next
        case False
        have "gSk s = gkl (2*s - 1)" unfolding gSk_def top1_path_product_def using False by simp
        have "2*s - 1 \<in> I_set" using hs False unfolding top1_unit_interval_def by auto
        hence "p0 (gkl (2*s - 1)) = top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k (2*s - 1)"
          using hgkl_proj_k by (by100 blast)
        moreover have "top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a (Suc k) s
            = top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k (2*s - 1)"
        proof -
          have "top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a (Suc k) s
              = top1_path_product (top1_path_reverse (top1_path_product gamma delta))
                  (top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k) s" by simp
          also have "... = top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k (2*s - 1)"
            unfolding top1_path_product_def using False by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>gSk s = gkl (2*s - 1)\<close> unfolding p0_def by simp
      qed
    qed
    ultimately show ?case by (intro exI[of _ gSk]) (by100 blast)
  qed
  \<comment> \<open>Apply covering_lift_endpoint_contradiction.\<close>
  obtain ftm where hftm: "top1_is_path_on E TE (a, 0) (a, 2 * int m) ftm"
      and hftm_proj: "\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product alpha beta) a m s"
    using hfm_lift by (by100 blast)
  obtain gkl where hgkl: "top1_is_path_on E TE (a, 0) (a, 0) gkl"
      and hgkl_proj: "\<forall>s\<in>I_set. p0 (gkl s) = top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k s"
    using hginvk_lift by (by100 blast)
  have hfm_path: "top1_is_path_on X TX a a (top1_path_power (top1_path_product alpha beta) a m)"
  proof -
    have hf_loop: "top1_is_loop_on X TX a (top1_path_product alpha beta)"
    proof -
      have "top1_is_path_on X TX a b alpha"
        by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(2) assms(11)])
           (use assms(4) in blast)
      moreover have "top1_is_path_on X TX b a beta"
        by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(3) assms(12)])
           (use assms(4) in blast)
      ultimately show ?thesis unfolding top1_is_loop_on_def
        using top1_path_product_is_path[OF assms(1)] by (by100 blast)
    qed
    show ?thesis by (rule top1_path_power_is_path[OF assms(1) hf_loop])
  qed
  have hginvk_path: "top1_is_path_on X TX a a
      (top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k)"
  proof -
    have hg_path: "top1_is_path_on X TX a a (top1_path_product gamma delta)"
    proof -
      have "top1_is_path_on X TX a a' gamma"
        by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(2) assms(14)])
           (use assms(4) in blast)
      moreover have "top1_is_path_on X TX a' a delta"
        by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(3) assms(15)])
           (use assms(4) in blast)
      ultimately show ?thesis using top1_path_product_is_path[OF assms(1)] by (by100 blast)
    qed
    have hginv_loop: "top1_is_loop_on X TX a (top1_path_reverse (top1_path_product gamma delta))"
    proof -
      have "top1_is_path_on X TX a a (top1_path_reverse (top1_path_product gamma delta))"
        using top1_path_reverse_is_path[OF hg_path] hg_path
        unfolding top1_is_path_on_def top1_path_reverse_def by auto
      thus ?thesis unfolding top1_is_loop_on_def by simp
    qed
    show ?thesis by (rule top1_path_power_is_path[OF assms(1) hginv_loop])
  qed
  show "m = 0"
    by (rule covering_lift_endpoint_contradiction[OF hcov hTE assms(1) he0 hp0
        hftm hftm_proj hfm_path hgkl hgkl_proj hginvk_path assms(16)])
qed

\<comment> \<open>Corollary for 63.5: In the setting of 63.1 on S^2-{p,q}, if we have two loops f and g
   where f = \<alpha>*\<beta> and g = \<gamma>*\<delta> (constructed from different component decompositions),
   both nontrivial, the fact that \<pi>_1(S^2-{p,q}) \<cong> Z forces [f]^m = [g]^k for some
   nonzero m,k. But 63.1(c) says m must be 0. Contradiction.\<close>
lemma pi1_S2_minus_two_points_infinite_cyclic:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "p \<in> top1_S2" and "q \<in> top1_S2" and "p \<noteq> q"
      and "a \<in> top1_S2 - {p} - {q}"
  shows "\<exists>gen. top1_is_loop_on (top1_S2 - {p} - {q})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) a gen \<and>
    (\<forall>f. top1_is_loop_on (top1_S2 - {p} - {q})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) a f \<longrightarrow>
      (\<exists>n::nat. top1_path_homotopic_on (top1_S2 - {p} - {q})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) a a
        f (top1_path_power gen a n) \<or>
       top1_path_homotopic_on (top1_S2 - {p} - {q})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) a a
        f (top1_path_power (top1_path_reverse gen) a n)))"
proof -
  \<comment> \<open>Chain: S^2-{p} \<cong> R^2 (stereographic), S^2-{p,q} \<cong> R^2-{h(q)},
     R^2-{point} deformation retracts to S^1, \<pi>_1(S^1) \<cong> Z (Theorem_54_5_iso).\<close>
  let ?X = "top1_S2 - {p} - {q}" and ?TX = "subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})"
  \<comment> \<open>Step 1: Stereographic projection \<sigma> from p gives S^2-{p} \<cong> R^2.\<close>
  obtain \<sigma> where h\<sigma>: "top1_homeomorphism_on (top1_S2 - {p})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p}))
      (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) \<sigma>"
    using S2_minus_point_homeo_R2[OF assms(2)] by blast
  \<comment> \<open>Step 2: Restrict to S^2-{p,q}: \<sigma> maps this to R^2-{\<sigma>(q)}.\<close>
  define q' where "q' = \<sigma> q"
  have hq_in: "q \<in> top1_S2 - {p}" using assms(3,4) by (by100 blast)
  have ha_in: "a \<in> top1_S2 - {p}" using assms(5) by (by100 blast)
  define a' where "a' = \<sigma> a"
  \<comment> \<open>Step 3: \<sigma> restricts to homeomorphism S^2-{p,q} \<cong> R^2-{q'}.\<close>
  \<comment> \<open>Step 4: R^2-{q'} is homeomorphic to R^2-{0} (by translation).\<close>
  \<comment> \<open>Step 5: R^2-{0} deformation retracts to S^1 (Theorem_58_2_inclusion_iso).\<close>
  \<comment> \<open>Step 6: \<pi>_1(S^1) \<cong> Z (Theorem_54_5_iso).\<close>
  \<comment> \<open>Step 7: Chain of isomorphisms: \<pi>_1(S^2-{p,q}) \<cong> \<pi>_1(R^2-{q'}) \<cong> \<pi>_1(R^2-{0}) \<cong> \<pi>_1(S^1) \<cong> Z.\<close>
  \<comment> \<open>Step 8: Extract generator and generate-all property.\<close>
  \<comment> \<open>Step 3: \<sigma> restricts to homeomorphism ?X \<cong> R^2-{q'}.\<close>
  define R2_q' :: "(real \<times> real) set" where "R2_q' = UNIV - {q'}"
  define TR2_q' where "TR2_q' = subspace_topology UNIV
      (product_topology_on top1_open_sets top1_open_sets) R2_q'"
  have h\<sigma>_restrict: "top1_homeomorphism_on ?X ?TX R2_q' TR2_q' \<sigma>"
  proof -
    have h_step: "top1_homeomorphism_on ((top1_S2 - {p}) - {q})
        (subspace_topology (top1_S2 - {p}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p}))
          ((top1_S2 - {p}) - {q}))
        ((UNIV :: (real \<times> real) set) - {\<sigma> q})
        (subspace_topology (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)
          (UNIV - {\<sigma> q})) \<sigma>"
      by (rule homeomorphism_restrict_point[OF h\<sigma> hq_in])
    \<comment> \<open>Simplify: (S^2-{p})-{q} = S^2-{p}-{q} = ?X, subspace of subspace = subspace.\<close>
    have hX_eq: "(top1_S2 - {p}) - {q} = ?X" by (by100 blast)
    have hY_eq: "(UNIV :: (real \<times> real) set) - {\<sigma> q} = R2_q'" unfolding R2_q'_def q'_def by simp
    have hTX_eq: "subspace_topology (top1_S2 - {p}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p}))
        ((top1_S2 - {p}) - {q}) = ?TX"
    proof -
      have "?X \<subseteq> top1_S2 - {p}" by (by100 blast)
      hence "subspace_topology (top1_S2 - {p}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p}))
          ?X = subspace_topology top1_S2 top1_S2_topology ?X"
        by (rule subspace_topology_trans)
      moreover have "(top1_S2 - {p}) - {q} = ?X" by (by100 blast)
      ultimately show ?thesis by simp
    qed
    have hTY_eq: "subspace_topology (UNIV :: (real \<times> real) set)
        (product_topology_on top1_open_sets top1_open_sets) (UNIV - {\<sigma> q}) = TR2_q'"
      unfolding TR2_q'_def R2_q'_def q'_def by simp
    show ?thesis using h_step hX_eq hY_eq hTX_eq hTY_eq by simp
  qed
  \<comment> \<open>Step 4: Translation t(x) = x - q' gives R^2-{q'} \<cong> R^2-{0}.\<close>
  define R2_0 :: "(real \<times> real) set" where "R2_0 = UNIV - {(0, 0)}"
  define TR2_0 where "TR2_0 = subspace_topology UNIV
      (product_topology_on top1_open_sets top1_open_sets) R2_0"
  define t :: "real \<times> real \<Rightarrow> real \<times> real" where
    "t = (\<lambda>(x, y). (x - fst q', y - snd q'))"
  have ht_homeo: "top1_homeomorphism_on R2_q' TR2_q' R2_0 TR2_0 t"
  proof -
    have ht_eq: "t = (\<lambda>x. (fst x - fst q', snd x - snd q'))"
      unfolding t_def by (rule ext) auto
    show ?thesis unfolding R2_q'_def TR2_q'_def R2_0_def TR2_0_def ht_eq
      by (rule translation_homeo_R2[of q'])
  qed
  \<comment> \<open>Step 5-6: \<pi>_1(R^2-{0}) \<cong> \<pi>_1(S^1) \<cong> Z. Use existing Theorem_58_2 + Theorem_54_5.\<close>
  \<comment> \<open>Step 7: Chain: \<pi>_1(S^2-{p,q}) \<cong> \<pi>_1(R^2-{q'}) \<cong> \<pi>_1(R^2-{0}) \<cong> \<pi>_1(S^1) \<cong> Z.
     The composition \<sigma> ; t maps a \<in> S^2-{p,q} to t(\<sigma>(a)) \<in> R^2-{0}.
     By Theorem_58_7, the induced map on \<pi>_1 is an isomorphism.\<close>
  \<comment> \<open>Step 8: Extract generator from the isomorphism with Z and convert to path_power form.\<close>
  \<comment> \<open>Step 5: Compose \<sigma> and t to get homeomorphism X \<rightarrow> R^2-{0}.\<close>
  have hTX: "is_topology_on ?X ?TX"
    by (rule subspace_topology_is_topology_on[OF
        is_topology_on_strict_imp[OF assms(1)]]) (by100 blast)
  have hTR2_0: "is_topology_on R2_0 TR2_0"
    unfolding TR2_0_def R2_0_def
    by (rule subspace_topology_is_topology_on[OF
        product_topology_on_is_topology_on[OF
          top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
          simplified]]) (by100 simp)
  define h where "h = t \<circ> \<sigma>"
  have hh_homeo: "top1_homeomorphism_on ?X ?TX R2_0 TR2_0 h"
    unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on ?X ?TX" by (rule hTX)
    show "is_topology_on R2_0 TR2_0" by (rule hTR2_0)
    show "bij_betw h ?X R2_0"
    proof -
      have "bij_betw \<sigma> ?X R2_q'" using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
      moreover have "bij_betw t R2_q' R2_0" using ht_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      ultimately show ?thesis unfolding h_def using bij_betw_comp_iff by (by100 blast)
    qed
    show "top1_continuous_map_on ?X ?TX R2_0 TR2_0 h"
    proof -
      have h1: "top1_continuous_map_on ?X ?TX R2_q' TR2_q' \<sigma>"
        using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
      have h2: "top1_continuous_map_on R2_q' TR2_q' R2_0 TR2_0 t"
        using ht_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      show ?thesis unfolding h_def by (rule top1_continuous_map_on_comp[OF h1 h2])
    qed
    show "top1_continuous_map_on R2_0 TR2_0 ?X ?TX (inv_into ?X h)"
    proof -
      have hinv_\<sigma>: "top1_continuous_map_on R2_q' TR2_q' ?X ?TX (inv_into ?X \<sigma>)"
        using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
      have hinv_t: "top1_continuous_map_on R2_0 TR2_0 R2_q' TR2_q' (inv_into R2_q' t)"
        using ht_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have hcomp_inv: "top1_continuous_map_on R2_0 TR2_0 ?X ?TX (inv_into ?X \<sigma> \<circ> inv_into R2_q' t)"
        by (rule top1_continuous_map_on_comp[OF hinv_t hinv_\<sigma>])
      \<comment> \<open>inv_into X (t \<circ> \<sigma>) = inv_into X \<sigma> \<circ> inv_into R2_q' t on R2_0.\<close>
      \<comment> \<open>inv_into X h continuous: show preimage of TX-open under inv_into = h-image is TR2_0-open.
         h = t \<circ> \<sigma>, both open maps (homeomorphisms), so h is an open map.\<close>
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix y assume "y \<in> R2_0"
        have hbij: "bij_betw h ?X R2_0"
        proof -
          have "bij_betw \<sigma> ?X R2_q'" using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
          moreover have "bij_betw t R2_q' R2_0" using ht_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          ultimately show ?thesis unfolding h_def using bij_betw_comp_iff by (by100 blast)
        qed
        have "y \<in> h ` ?X" using \<open>y \<in> R2_0\<close> hbij unfolding bij_betw_def by (by100 blast)
        thus "inv_into ?X h y \<in> ?X" using inv_into_into[OF \<open>y \<in> h ` ?X\<close>] by (by100 blast)
      next
        fix W assume "W \<in> ?TX"
        \<comment> \<open>Need: {y \<in> R2_0. inv_into X h y \<in> W} \<in> TR2_0.
           This equals h ` (W \<inter> X) = h ` W (since W \<subseteq> X from topology).
           h ` W = t ` (\<sigma> ` W). \<sigma> ` W is open in TR2_q' (σ is open map).
           t ` (\<sigma> ` W) is open in TR2_0 (t is open map).\<close>
        have hbij: "bij_betw h ?X R2_0"
        proof -
          have "bij_betw \<sigma> ?X R2_q'" using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
          moreover have "bij_betw t R2_q' R2_0" using ht_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          ultimately show ?thesis unfolding h_def using bij_betw_comp_iff by (by100 blast)
        qed
        \<comment> \<open>{y \<in> R2_0 | inv h y \<in> W} = h ` W (since h bijection X \<rightarrow> R2_0).\<close>
        have hW_sub: "W \<subseteq> ?X"
        proof -
          have "?TX = subspace_topology top1_S2 top1_S2_topology ?X" by (by100 simp)
          then obtain W0 where "W0 \<in> top1_S2_topology" "W = ?X \<inter> W0"
            using \<open>W \<in> ?TX\<close> unfolding subspace_topology_def by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        have heq: "{y \<in> R2_0. inv_into ?X h y \<in> W} = h ` W"
        proof (rule set_eqI, rule iffI)
          fix y assume "y \<in> {y \<in> R2_0. inv_into ?X h y \<in> W}"
          hence hy: "y \<in> R2_0" and hinv: "inv_into ?X h y \<in> W" by (by100 auto)
          have "y \<in> h ` ?X" using hy hbij unfolding bij_betw_def by (by100 blast)
          have "y = h (inv_into ?X h y)" using f_inv_into_f[OF \<open>y \<in> h ` ?X\<close>] by (by100 simp)
          thus "y \<in> h ` W" using hinv by (by100 blast)
        next
          fix y assume "y \<in> h ` W"
          then obtain x where hx: "x \<in> W" "y = h x" by (by100 blast)
          have "x \<in> ?X" using hx(1) hW_sub by (by100 blast)
          hence "inv_into ?X h y = x"
            using inv_into_f_f[OF bij_betw_imp_inj_on[OF hbij] \<open>x \<in> ?X\<close>] hx(2) by (by100 simp)
          moreover have "y \<in> R2_0"
          proof -
            have "x \<in> ?X" using hx(1) hW_sub by (by100 blast)
            hence "h x \<in> h ` ?X" by (by100 blast)
            hence "h x \<in> R2_0" using hbij unfolding bij_betw_def by (by100 blast)
            thus ?thesis using hx(2) by simp
          qed
          ultimately show "y \<in> {y \<in> R2_0. inv_into ?X h y \<in> W}" using hx(1) by (by100 blast)
        qed
        \<comment> \<open>h ` W is open: h = t \<circ> \<sigma>, \<sigma> maps open to open, t maps open to open.\<close>
        have "\<sigma> ` W \<in> TR2_q'"
        proof -
          \<comment> \<open>\<sigma>\<inverse> continuous: {x \<in> X. \<sigma> x \<in> V} = {x \<in> X. x \<in> \<sigma>\<inverse>(V)} for V open.
             Since \<sigma> bijective: \<sigma> ` W = {v \<in> R2_q'. \<sigma>\<inverse>(v) \<in> W} = preimage of W under \<sigma>\<inverse>.\<close>
          have hinv_\<sigma>_cont: "top1_continuous_map_on R2_q' TR2_q' ?X ?TX (inv_into ?X \<sigma>)"
            using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
          have hbij_\<sigma>: "bij_betw \<sigma> ?X R2_q'"
            using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
          have "\<sigma> ` W = {v \<in> R2_q'. inv_into ?X \<sigma> v \<in> W}"
          proof (rule set_eqI, rule iffI)
            fix v assume "v \<in> \<sigma> ` W"
            then obtain x where "x \<in> W" "v = \<sigma> x" by (by100 blast)
            have "x \<in> ?X" using \<open>x \<in> W\<close> hW_sub by (by100 blast)
            hence "inv_into ?X \<sigma> v = x"
              using inv_into_f_f[OF bij_betw_imp_inj_on[OF hbij_\<sigma>] \<open>x \<in> ?X\<close>] \<open>v = \<sigma> x\<close> by (by100 simp)
            moreover have "v \<in> R2_q'" using \<open>x \<in> ?X\<close> hbij_\<sigma> \<open>v = \<sigma> x\<close> unfolding bij_betw_def by (by100 blast)
            ultimately show "v \<in> {v \<in> R2_q'. inv_into ?X \<sigma> v \<in> W}" using \<open>x \<in> W\<close> by (by100 blast)
          next
            fix v assume "v \<in> {v \<in> R2_q'. inv_into ?X \<sigma> v \<in> W}"
            hence "v \<in> R2_q'" "inv_into ?X \<sigma> v \<in> W" by (by100 auto)
            have "v \<in> \<sigma> ` ?X" using \<open>v \<in> R2_q'\<close> hbij_\<sigma> unfolding bij_betw_def by (by100 blast)
            have "v = \<sigma> (inv_into ?X \<sigma> v)" using f_inv_into_f[OF \<open>v \<in> \<sigma> ` ?X\<close>] by (by100 simp)
            thus "v \<in> \<sigma> ` W" using \<open>inv_into ?X \<sigma> v \<in> W\<close> by (by100 blast)
          qed
          moreover have "{v \<in> R2_q'. inv_into ?X \<sigma> v \<in> W} \<in> TR2_q'"
            using hinv_\<sigma>_cont \<open>W \<in> ?TX\<close> unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
        have "t ` (\<sigma> ` W) \<in> TR2_0"
        proof -
          have hinv_t_cont: "top1_continuous_map_on R2_0 TR2_0 R2_q' TR2_q' (inv_into R2_q' t)"
            using ht_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have hbij_t: "bij_betw t R2_q' R2_0"
            using ht_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have hsW_sub: "\<sigma> ` W \<subseteq> R2_q'"
          proof -
            have "\<sigma> ` W \<subseteq> \<sigma> ` ?X" using hW_sub by (by100 blast)
            moreover have "bij_betw \<sigma> ?X R2_q'"
              using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
            ultimately show ?thesis using bij_betw_imp_surj_on by (by100 fast)
          qed
          have "t ` (\<sigma> ` W) = {v \<in> R2_0. inv_into R2_q' t v \<in> \<sigma> ` W}"
          proof (rule set_eqI, rule iffI)
            fix v assume "v \<in> t ` (\<sigma> ` W)"
            then obtain u where "u \<in> \<sigma> ` W" "v = t u" by (by100 blast)
            have "u \<in> R2_q'" using \<open>u \<in> \<sigma> ` W\<close> hsW_sub by (by100 blast)
            hence "inv_into R2_q' t v = u"
              using inv_into_f_f[OF bij_betw_imp_inj_on[OF hbij_t] \<open>u \<in> R2_q'\<close>] \<open>v = t u\<close> by (by100 simp)
            moreover have "v \<in> R2_0" using \<open>u \<in> R2_q'\<close> hbij_t \<open>v = t u\<close> unfolding bij_betw_def by (by100 blast)
            ultimately show "v \<in> {v \<in> R2_0. inv_into R2_q' t v \<in> \<sigma> ` W}" using \<open>u \<in> \<sigma> ` W\<close> by (by100 blast)
          next
            fix v assume "v \<in> {v \<in> R2_0. inv_into R2_q' t v \<in> \<sigma> ` W}"
            hence "v \<in> R2_0" "inv_into R2_q' t v \<in> \<sigma> ` W" by (by100 auto)
            have "v \<in> t ` R2_q'" using \<open>v \<in> R2_0\<close> hbij_t unfolding bij_betw_def by (by100 blast)
            have "v = t (inv_into R2_q' t v)" using f_inv_into_f[OF \<open>v \<in> t ` R2_q'\<close>] by (by100 simp)
            thus "v \<in> t ` (\<sigma> ` W)" using \<open>inv_into R2_q' t v \<in> \<sigma> ` W\<close> by (by100 blast)
          qed
          moreover have "{v \<in> R2_0. inv_into R2_q' t v \<in> \<sigma> ` W} \<in> TR2_0"
            using hinv_t_cont \<open>\<sigma> ` W \<in> TR2_q'\<close> unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
        have "h ` W = t ` (\<sigma> ` W)" unfolding h_def by (by100 auto)
        show "{y \<in> R2_0. inv_into ?X h y \<in> W} \<in> TR2_0"
          unfolding heq \<open>h ` W = t ` (\<sigma> ` W)\<close> by (rule \<open>t ` (\<sigma> ` W) \<in> TR2_0\<close>)
      qed
    qed
  qed
  \<comment> \<open>Step 6: Homeomorphism \<Rightarrow> homotopy equivalence.\<close>
  have hh_htpeq: "top1_homotopy_equivalence_on ?X ?TX R2_0 TR2_0 h (inv_into ?X h)"
    unfolding top1_homotopy_equivalence_on_def
  proof (intro conjI)
    show "top1_continuous_map_on ?X ?TX R2_0 TR2_0 h"
      using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    show "top1_continuous_map_on R2_0 TR2_0 ?X ?TX (inv_into ?X h)"
      using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    \<comment> \<open>inv \<circ> h = id on X, h \<circ> inv = id on R2_0.\<close>
    \<comment> \<open>Both homotopies: inv\<circ>h = id on X and h\<circ>inv = id on R2_0.
       The constant homotopy H(x,t) = x works. This is the fst projection X\<times>I \<rightarrow> X.\<close>
    show "top1_homotopic_on ?X ?TX ?X ?TX (inv_into ?X h \<circ> h) (\<lambda>x. x)"
      unfolding top1_homotopic_on_def
    proof (intro conjI exI[of _ "\<lambda>(x,t). x"])
      have hh_cont: "top1_continuous_map_on ?X ?TX R2_0 TR2_0 h"
        using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have hinv_cont: "top1_continuous_map_on R2_0 TR2_0 ?X ?TX (inv_into ?X h)"
        using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      show "top1_continuous_map_on ?X ?TX ?X ?TX (inv_into ?X h \<circ> h)"
        by (rule top1_continuous_map_on_comp[OF hh_cont hinv_cont])
      show "top1_continuous_map_on ?X ?TX ?X ?TX (\<lambda>x. x)"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x assume "x \<in> ?X" thus "x \<in> ?X" .
      next
        fix W assume "W \<in> ?TX"
        then obtain W0 where "W0 \<in> top1_S2_topology" "W = ?X \<inter> W0"
          unfolding subspace_topology_def by (by100 blast)
        hence "{x \<in> ?X. x \<in> W} = W" by (by100 blast)
        thus "{x \<in> ?X. x \<in> W} \<in> ?TX" using \<open>W \<in> ?TX\<close> by (by100 simp)
      qed
      show "top1_continuous_map_on (?X \<times> I_set) (product_topology_on ?TX I_top) ?X ?TX (\<lambda>(x, t). x)"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix p assume hp: "p \<in> ?X \<times> I_set"
        obtain x t where hxt: "p = (x, t)" "x \<in> ?X" "t \<in> I_set"
          using hp by (by100 blast)
        show "(case p of (x, t) \<Rightarrow> x) \<in> ?X" using hxt by (by100 simp)
      next
        fix W assume hW: "W \<in> ?TX"
        have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
        have hI_mem: "I_set \<in> I_top" using hTI unfolding is_topology_on_def by (by100 blast)
        \<comment> \<open>{p \<in> X\<times>I. fst p \<in> W} = W \<times> I_set (since W \<subseteq> X from subspace topology).\<close>
        have hW_sub: "W \<subseteq> ?X"
        proof -
          obtain W0 where "W = ?X \<inter> W0" using hW unfolding subspace_topology_def by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        have "{p \<in> ?X \<times> I_set. (case p of (x, t) \<Rightarrow> x) \<in> W} = W \<times> I_set"
        proof (rule set_eqI, rule iffI)
          fix p assume hp: "p \<in> {p \<in> ?X \<times> I_set. (case p of (x, t) \<Rightarrow> x) \<in> W}"
          obtain x t where hxt: "p = (x,t)" "x \<in> ?X" "t \<in> I_set" "(case (x,t) of (x,t) \<Rightarrow> x) \<in> W"
            using hp by (by100 blast)
          have "x \<in> W" using hxt(4) by (by100 simp)
          thus "p \<in> W \<times> I_set" using hxt(1,3) by (by100 blast)
        next
          fix p assume hp: "p \<in> W \<times> I_set"
          obtain x t where "p = (x,t)" "x \<in> W" "t \<in> I_set" using hp by (by100 blast)
          hence "x \<in> ?X" using hW_sub by (by100 blast)
          show "p \<in> {p \<in> ?X \<times> I_set. (case p of (x, t) \<Rightarrow> x) \<in> W}"
            using \<open>p = (x,t)\<close> \<open>x \<in> W\<close> \<open>x \<in> ?X\<close> \<open>t \<in> I_set\<close> by (by100 simp)
        qed
        moreover have "W \<times> I_set \<in> product_topology_on ?TX I_top"
          by (rule product_rect_open[OF hW hI_mem])
        ultimately show "{p \<in> ?X \<times> I_set. (case p of (x, t) \<Rightarrow> x) \<in> W} \<in> product_topology_on ?TX I_top"
          by (by100 simp)
      qed
      show "\<forall>x\<in>?X. (case (x, 0::real) of (x, t) \<Rightarrow> x) = (inv_into ?X h \<circ> h) x"
      proof
        fix x assume hx: "x \<in> ?X"
        have hbij_h: "bij_betw h ?X R2_0"
          using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        have "inv_into ?X h (h x) = x"
          using inv_into_f_f[OF bij_betw_imp_inj_on[OF hbij_h] hx] by (by100 simp)
        thus "(case (x, 0::real) of (x, t) \<Rightarrow> x) = (inv_into ?X h \<circ> h) x"
          unfolding comp_def by (by100 simp)
      qed
      show "\<forall>x\<in>?X. (case (x, 1::real) of (x, t) \<Rightarrow> x) = x" by (by100 simp)
    qed
    show "top1_homotopic_on R2_0 TR2_0 R2_0 TR2_0 (h \<circ> inv_into ?X h) (\<lambda>y. y)"
      unfolding top1_homotopic_on_def
    proof (intro conjI exI[of _ "\<lambda>(y,t). y"])
      have hh_cont: "top1_continuous_map_on ?X ?TX R2_0 TR2_0 h"
        using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have hinv_cont: "top1_continuous_map_on R2_0 TR2_0 ?X ?TX (inv_into ?X h)"
        using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      show "top1_continuous_map_on R2_0 TR2_0 R2_0 TR2_0 (h \<circ> inv_into ?X h)"
        by (rule top1_continuous_map_on_comp[OF hinv_cont hh_cont])
      show "top1_continuous_map_on R2_0 TR2_0 R2_0 TR2_0 (\<lambda>y. y)"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix y assume "y \<in> R2_0" thus "y \<in> R2_0" .
      next
        fix W assume "W \<in> TR2_0"
        have "W \<subseteq> R2_0"
        proof -
          obtain W0 where "W = R2_0 \<inter> W0"
            using \<open>W \<in> TR2_0\<close> unfolding TR2_0_def R2_0_def subspace_topology_def by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        hence "{y \<in> R2_0. y \<in> W} = W" by (by100 blast)
        thus "{y \<in> R2_0. y \<in> W} \<in> TR2_0" using \<open>W \<in> TR2_0\<close> by (by100 simp)
      qed
      show "top1_continuous_map_on (R2_0 \<times> I_set) (product_topology_on TR2_0 I_top) R2_0 TR2_0 (\<lambda>(y, t). y)"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix p assume hp: "p \<in> R2_0 \<times> I_set"
        obtain y t where "p = (y, t)" "y \<in> R2_0" using hp by (by100 blast)
        thus "(case p of (y, t) \<Rightarrow> y) \<in> R2_0" by (by100 simp)
      next
        fix W assume hW: "W \<in> TR2_0"
        have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
        have hI_mem: "I_set \<in> I_top" using hTI unfolding is_topology_on_def by (by100 blast)
        have hW_sub: "W \<subseteq> R2_0"
        proof -
          obtain W0 where "W = R2_0 \<inter> W0"
            using hW unfolding TR2_0_def R2_0_def subspace_topology_def by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        have "{p \<in> R2_0 \<times> I_set. (case p of (y, t) \<Rightarrow> y) \<in> W} = W \<times> I_set"
        proof (rule set_eqI, rule iffI)
          fix p assume hp: "p \<in> {p \<in> R2_0 \<times> I_set. (case p of (y, t) \<Rightarrow> y) \<in> W}"
          obtain y t where hyt: "p = (y,t)" "y \<in> R2_0" "t \<in> I_set"
              "(case (y,t) of (y,t) \<Rightarrow> y) \<in> W"
            using hp by (by100 blast)
          have "y \<in> W" using hyt(4) by (by100 simp)
          thus "p \<in> W \<times> I_set" using hyt(1,3) by (by100 blast)
        next
          fix p assume hp: "p \<in> W \<times> I_set"
          obtain y t where "p = (y,t)" "y \<in> W" "t \<in> I_set" using hp by (by100 blast)
          hence "y \<in> R2_0" using hW_sub by (by100 blast)
          show "p \<in> {p \<in> R2_0 \<times> I_set. (case p of (y, t) \<Rightarrow> y) \<in> W}"
            using \<open>p = (y,t)\<close> \<open>y \<in> W\<close> \<open>y \<in> R2_0\<close> \<open>t \<in> I_set\<close> by (by100 simp)
        qed
        moreover have "W \<times> I_set \<in> product_topology_on TR2_0 I_top"
          by (rule product_rect_open[OF hW hI_mem])
        ultimately show "{p \<in> R2_0 \<times> I_set. (case p of (y, t) \<Rightarrow> y) \<in> W} \<in> product_topology_on TR2_0 I_top"
          by (by100 simp)
      qed
      show "\<forall>y\<in>R2_0. (case (y, 0::real) of (y, t) \<Rightarrow> y) = (h \<circ> inv_into ?X h) y"
      proof
        fix y assume hy: "y \<in> R2_0"
        have hbij_h: "bij_betw h ?X R2_0"
          using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        have "y \<in> h ` ?X" using hy hbij_h unfolding bij_betw_def by (by100 blast)
        have "h (inv_into ?X h y) = y" using f_inv_into_f[OF \<open>y \<in> h ` ?X\<close>] by (by100 simp)
        thus "(case (y, 0::real) of (y, t) \<Rightarrow> y) = (h \<circ> inv_into ?X h) y"
          unfolding comp_def by (by100 simp)
      qed
      show "\<forall>y\<in>R2_0. (case (y, 1::real) of (y, t) \<Rightarrow> y) = y" by (by100 simp)
    qed
  qed
  have ha_X: "a \<in> ?X" using assms(5) by (by100 blast)
  have hpi1_iso_R2: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier ?X ?TX a)
      (top1_fundamental_group_mul ?X ?TX a)
      (top1_fundamental_group_carrier R2_0 TR2_0 (h a))
      (top1_fundamental_group_mul R2_0 TR2_0 (h a))"
    using Theorem_58_7[OF hTX hTR2_0 hh_htpeq ha_X] by (by100 blast)
  \<comment> \<open>Step 7: Chain with Theorem_58_2 (R^2-{0} \<cong> S^1) and Theorem_54_5 (\<pi>_1(S^1) \<cong> Z).
     This gives \<pi>_1(X, a) \<cong> Z.\<close>
  \<comment> \<open>Step 8: Extract generator from Z-isomorphism.\<close>
  \<comment> \<open>Step 7-8: From \<pi>_1(X,a) \<cong> Z, extract generator.\<close>
  \<comment> \<open>The chain \<pi>_1(X,a) \<cong> \<pi>_1(R^2-{0}, h(a)) \<cong> \<pi>_1(S^1, (1,0)) \<cong> Z
     gives a group isomorphism \<phi>: \<pi>_1(X,a) \<rightarrow> Z.
     Let gen_class = \<phi>\<inverse>(1). Pick a representative gen from gen_class.
     For any loop f: \<phi>([f]) = n. [f] = [gen]^n in the group.
     For n \<ge> 0: f \<simeq> gen^n (path_power). For n < 0: f \<simeq> (gen\<inverse>)^{|n|}.\<close>
  \<comment> \<open>From hpi1_iso_R2 + Theorem_58_2 + Theorem_54_5: \<pi>_1(X,a) \<cong> Z.\<close>
  have hpi1_iso_Z: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier ?X ?TX a)
      (top1_fundamental_group_mul ?X ?TX a)
      top1_Z_group top1_Z_mul"
  proof -
    \<comment> \<open>Step 1: \<pi>_1(R^2-{0}, h(a)) \<cong> \<pi>_1(R^2-{0}, (1,0)) via basepoint change.\<close>
    have hR2_0_pc: "top1_path_connected_on R2_0 TR2_0"
      unfolding R2_0_def TR2_0_def using R2_minus_point_path_connected[of "(0,0)"] by (by100 simp)
    have hha_R2: "h a \<in> R2_0"
    proof -
      have "a \<in> ?X" using ha_X .
      hence "\<sigma> a \<in> R2_q'"
        using h\<sigma>_restrict unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      hence "t (\<sigma> a) \<in> R2_0"
        using ht_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      thus ?thesis unfolding h_def comp_def by (by100 simp)
    qed
    have h10_R2: "(1::real, 0::real) \<in> R2_0" unfolding R2_0_def by (by100 simp)
    have hbp_change: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier R2_0 TR2_0 (h a))
        (top1_fundamental_group_mul R2_0 TR2_0 (h a))
        (top1_fundamental_group_carrier R2_0 TR2_0 (1, 0))
        (top1_fundamental_group_mul R2_0 TR2_0 (1, 0))"
      by (rule Theorem_52_1_iso[OF hTR2_0 hR2_0_pc hha_R2 h10_R2])
    \<comment> \<open>Step 2: \<pi>_1(S^1, (1,0)) \<cong> \<pi>_1(R^2-{0}, (1,0)) (Theorem_58_2 with matching TR2_0).\<close>
    have hTR2_0_eq: "TR2_0 = subspace_topology UNIV
        (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0::real, 0::real)})"
      unfolding TR2_0_def R2_0_def by (by100 simp)
    have hR2_0_eq: "R2_0 = UNIV - {(0::real, 0::real)}" unfolding R2_0_def by (by100 simp)
    have h58_2: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1
          (subspace_topology (UNIV - {(0::real, 0::real)})
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
              (UNIV - {(0, 0)})) top1_S1) (1, 0))
        (top1_fundamental_group_mul top1_S1
          (subspace_topology (UNIV - {(0::real, 0::real)})
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
              (UNIV - {(0, 0)})) top1_S1) (1, 0))
        (top1_fundamental_group_carrier (UNIV - {(0::real, 0::real)})
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - {(0, 0)})) (1, 0))
        (top1_fundamental_group_mul (UNIV - {(0::real, 0::real)})
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - {(0, 0)})) (1, 0))"
      by (rule Theorem_58_2_inclusion_iso)
    \<comment> \<open>Step 3: Match S^1 topologies. subspace R2_0 TR2_0 S^1 = top1_S1_topology.\<close>
    have hS1_top_eq: "subspace_topology R2_0 TR2_0 top1_S1 = top1_S1_topology"
    proof -
      have hS1_sub: "top1_S1 \<subseteq> R2_0" unfolding R2_0_def top1_S1_def by (by100 auto)
      \<comment> \<open>Direct proof: both sides equal {S^1 \<inter> W | W \<in> product_topology_on ...}.\<close>
      show ?thesis
      proof (rule set_eqI, rule iffI)
        fix W assume "W \<in> subspace_topology R2_0 TR2_0 top1_S1"
        then obtain V where hV: "V \<in> TR2_0" "W = top1_S1 \<inter> V"
          unfolding subspace_topology_def by (by100 blast)
        have hV_in: "V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) R2_0"
          using hV(1) unfolding TR2_0_def by simp
        then obtain V0 where hV0: "V0 \<in> product_topology_on top1_open_sets top1_open_sets"
            "V = R2_0 \<inter> V0" unfolding subspace_topology_def by (by100 blast)
        have "W = top1_S1 \<inter> V0" using hV(2) hV0(2) hS1_sub by (by100 blast)
        thus "W \<in> top1_S1_topology" unfolding top1_S1_topology_def subspace_topology_def
          using hV0(1) by (by100 blast)
      next
        fix W assume "W \<in> top1_S1_topology"
        then obtain V0 where hV0: "V0 \<in> product_topology_on top1_open_sets top1_open_sets"
            "W = top1_S1 \<inter> V0" unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
        have "R2_0 \<inter> V0 \<in> TR2_0" unfolding TR2_0_def R2_0_def subspace_topology_def
          using hV0(1) by (by100 blast)
        moreover have "W = top1_S1 \<inter> (R2_0 \<inter> V0)" using hV0(2) hS1_sub by (by100 blast)
        ultimately show "W \<in> subspace_topology R2_0 TR2_0 top1_S1"
          unfolding subspace_topology_def by (by100 blast)
      qed
    qed
    \<comment> \<open>Step 4: \<pi>_1(S^1, (1,0)) \<cong> Z (Theorem_54_5_iso).\<close>
    have h54_5: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        top1_Z_group top1_Z_mul"
      by (rule Theorem_54_5_iso)
    \<comment> \<open>Step 5: Compose the chain. Need transitivity of groups_isomorphic_on.\<close>
    \<comment> \<open>Compose: need transitivity + symmetry of groups_isomorphic_on.
       groups_isomorphic_on G mulG H mulH \<equiv> \<exists>f. group_iso_on G mulG H mulH f
       group_iso_on \<equiv> group_hom_on + bij_betw.
       Transitivity: compose hom + bij. Symmetry: inverse.\<close>
    \<comment> \<open>Rewrite h58_2 using hS1_top_eq to match S^1 topologies.\<close>
    have h58_2': "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_carrier R2_0 TR2_0 (1, 0))
        (top1_fundamental_group_mul R2_0 TR2_0 (1, 0))"
    proof -
      \<comment> \<open>h58_2 uses expanded R2_0/TR2_0; goal uses abbreviated names. Bridge via hS1_top_eq.\<close>
      have "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier top1_S1 (subspace_topology R2_0 TR2_0 top1_S1) (1, 0))
          (top1_fundamental_group_mul top1_S1 (subspace_topology R2_0 TR2_0 top1_S1) (1, 0))
          (top1_fundamental_group_carrier R2_0 TR2_0 (1, 0))
          (top1_fundamental_group_mul R2_0 TR2_0 (1, 0))"
        using h58_2 unfolding R2_0_def TR2_0_def by simp
      thus ?thesis using hS1_top_eq by simp
    qed
    \<comment> \<open>Chain: compose 4 group isos. Use transitivity + symmetry.\<close>
    show ?thesis unfolding top1_groups_isomorphic_on_def
    proof -
      \<comment> \<open>Extract individual isomorphisms.\<close>
      obtain f1 where hf1: "top1_group_iso_on
          (top1_fundamental_group_carrier ?X ?TX a) (top1_fundamental_group_mul ?X ?TX a)
          (top1_fundamental_group_carrier R2_0 TR2_0 (h a)) (top1_fundamental_group_mul R2_0 TR2_0 (h a)) f1"
        using hpi1_iso_R2 unfolding top1_groups_isomorphic_on_def by (by100 blast)
      obtain f2 where hf2: "top1_group_iso_on
          (top1_fundamental_group_carrier R2_0 TR2_0 (h a)) (top1_fundamental_group_mul R2_0 TR2_0 (h a))
          (top1_fundamental_group_carrier R2_0 TR2_0 (1, 0)) (top1_fundamental_group_mul R2_0 TR2_0 (1, 0)) f2"
        using hbp_change unfolding top1_groups_isomorphic_on_def by (by100 blast)
      obtain f3 where hf3: "top1_group_iso_on
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)) (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
          (top1_fundamental_group_carrier R2_0 TR2_0 (1, 0)) (top1_fundamental_group_mul R2_0 TR2_0 (1, 0)) f3"
        using h58_2' unfolding top1_groups_isomorphic_on_def by (by100 blast)
      obtain f4 where hf4: "top1_group_iso_on
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)) (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
          top1_Z_group top1_Z_mul f4"
        using h54_5 unfolding top1_groups_isomorphic_on_def by (by100 blast)
      \<comment> \<open>Name the carrier and multiplication sets.\<close>
      define G1 where "G1 = top1_fundamental_group_carrier ?X ?TX a"
      define M1 where "M1 = top1_fundamental_group_mul ?X ?TX a"
      define G2 where "G2 = top1_fundamental_group_carrier R2_0 TR2_0 (h a)"
      define M2 where "M2 = top1_fundamental_group_mul R2_0 TR2_0 (h a)"
      define G3 where "G3 = top1_fundamental_group_carrier R2_0 TR2_0 (1, 0)"
      define M3 where "M3 = top1_fundamental_group_mul R2_0 TR2_0 (1, 0)"
      define G4 where "G4 = top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
      define M4 where "M4 = top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0)"
      \<comment> \<open>Compose: f4 \<circ> inv(f3) \<circ> f2 \<circ> f1 : \<pi>_1(X) \<rightarrow> Z.\<close>
      define \<psi> where "\<psi> = f4 \<circ> (inv_into G4 f3 \<circ> (f2 \<circ> f1))"
      have hf1': "top1_group_iso_on G1 M1 G2 M2 f1"
        using hf1 unfolding G1_def M1_def G2_def M2_def .
      have hf2': "top1_group_iso_on G2 M2 G3 M3 f2"
        using hf2 unfolding G2_def M2_def G3_def M3_def .
      have hf3': "top1_group_iso_on G4 M4 G3 M3 f3"
        using hf3 unfolding G4_def M4_def G3_def M3_def .
      have hf4': "top1_group_iso_on G4 M4 top1_Z_group top1_Z_mul f4"
        using hf4 unfolding G4_def M4_def .
      \<comment> \<open>Bijections.\<close>
      have hb1: "bij_betw f1 G1 G2" using hf1' unfolding top1_group_iso_on_def by (by100 blast)
      have hb2: "bij_betw f2 G2 G3" using hf2' unfolding top1_group_iso_on_def by (by100 blast)
      have hb3: "bij_betw f3 G4 G3" using hf3' unfolding top1_group_iso_on_def by (by100 blast)
      have hb3i: "bij_betw (inv_into G4 f3) G3 G4"
        by (rule bij_betw_inv_into[OF hb3])
      have hb4: "bij_betw f4 G4 top1_Z_group" using hf4' unfolding top1_group_iso_on_def by (by100 blast)
      \<comment> \<open>Compose bijections.\<close>
      \<comment> \<open>Build bij_betw for \<psi> directly.\<close>
      \<comment> \<open>Prove \<psi> is a group iso: bij_betw + group_hom_on.\<close>
      \<comment> \<open>\<psi> is a group iso: compose 4 individual group isos.\<close>
      \<comment> \<open>Bijection: chain bij_betw via bij_betw_trans.\<close>
      have hb12: "bij_betw (f2 \<circ> f1) G1 G3"
        by (rule bij_betw_trans[OF hb1 hb2])
      have hb123: "bij_betw (inv_into G4 f3 \<circ> (f2 \<circ> f1)) G1 G4"
        by (rule bij_betw_trans[OF hb12 hb3i])
      have hb1234: "bij_betw (f4 \<circ> (inv_into G4 f3 \<circ> (f2 \<circ> f1))) G1 top1_Z_group"
        by (rule bij_betw_trans[OF hb123 hb4])
      have h\<psi>_bij: "bij_betw \<psi> G1 top1_Z_group"
        unfolding \<psi>_def using hb1234 .
      have h\<psi>_iso: "top1_group_iso_on G1 M1 top1_Z_group top1_Z_mul \<psi>"
        unfolding top1_group_iso_on_def
      proof (intro conjI)
        show "bij_betw \<psi> G1 top1_Z_group" by (rule h\<psi>_bij)
      next
        \<comment> \<open>Homomorphism: \<psi>(M1 x y) = top1_Z_mul (\<psi> x) (\<psi> y).\<close>
        have hh1: "top1_group_hom_on G1 M1 G2 M2 f1"
          using hf1' unfolding top1_group_iso_on_def by (by100 blast)
        have hh2: "top1_group_hom_on G2 M2 G3 M3 f2"
          using hf2' unfolding top1_group_iso_on_def by (by100 blast)
        have hh3: "top1_group_hom_on G4 M4 G3 M3 f3"
          using hf3' unfolding top1_group_iso_on_def by (by100 blast)
        have hh4: "top1_group_hom_on G4 M4 top1_Z_group top1_Z_mul f4"
          using hf4' unfolding top1_group_iso_on_def by (by100 blast)
        \<comment> \<open>inv_into G4 f3 is a homomorphism G3 \<rightarrow> G4.\<close>
        have hh3i_map: "\<And>z. z \<in> G3 \<Longrightarrow> inv_into G4 f3 z \<in> G4"
          using hb3i unfolding bij_betw_def by (by100 blast)
        have hh3i_hom:
            "inv_into G4 f3 (M3 x y) = M4 (inv_into G4 f3 x) (inv_into G4 f3 y)"
          if hx: "x \<in> G3" and hy: "y \<in> G3" for x y
        proof -
          have hx4: "inv_into G4 f3 x \<in> G4" using hh3i_map hx by simp
          have hy4: "inv_into G4 f3 y \<in> G4" using hh3i_map hy by simp
          have hxim: "x \<in> f3 ` G4" using hx hb3 unfolding bij_betw_def by (by100 blast)
          have hyim: "y \<in> f3 ` G4" using hy hb3 unfolding bij_betw_def by (by100 blast)
          have hfx: "f3 (inv_into G4 f3 x) = x" by (rule f_inv_into_f[OF hxim])
          have hfy: "f3 (inv_into G4 f3 y) = y" by (rule f_inv_into_f[OF hyim])
          have "f3 (M4 (inv_into G4 f3 x) (inv_into G4 f3 y))
              = M3 (f3 (inv_into G4 f3 x)) (f3 (inv_into G4 f3 y))"
            using hh3 hx4 hy4 unfolding top1_group_hom_on_def by (by100 blast)
          hence hf3_eq: "f3 (M4 (inv_into G4 f3 x) (inv_into G4 f3 y)) = M3 x y"
            using hfx hfy by simp
          \<comment> \<open>M4 closed on G4: path product of loops is a loop.\<close>
          have hM4_cl: "M4 (inv_into G4 f3 x) (inv_into G4 f3 y) \<in> G4"
          proof -
            have hTR2: "is_topology_on (UNIV::((real\<times>real) set))
                (product_topology_on top1_open_sets top1_open_sets)"
              using product_topology_on_is_topology_on[OF
                top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]
              by simp
            have hTS1: "is_topology_on top1_S1 top1_S1_topology"
              unfolding top1_S1_topology_def
              using subspace_topology_is_topology_on[OF hTR2 subset_UNIV] .
            obtain fa where hfa: "top1_is_loop_on top1_S1 top1_S1_topology (1,0) fa"
                "inv_into G4 f3 x = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) fa g}"
              using hx4 unfolding G4_def top1_fundamental_group_carrier_def by (by100 blast)
            obtain fb where hfb: "top1_is_loop_on top1_S1 top1_S1_topology (1,0) fb"
                "inv_into G4 f3 y = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) fb g}"
              using hy4 unfolding G4_def top1_fundamental_group_carrier_def by (by100 blast)
            have hprod_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1,0) (top1_path_product fa fb)"
              by (rule top1_path_product_is_loop[OF hTS1 hfa(1) hfb(1)])
            have hmul_class: "M4
                {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) fa g}
                {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) fb g}
              = {h. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (top1_path_product fa fb) h}"
              unfolding M4_def
              by (rule top1_fundamental_group_mul_class[OF hTS1 hfa(1) hfb(1)])
            have "M4 (inv_into G4 f3 x) (inv_into G4 f3 y) =
                {h. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (top1_path_product fa fb) h}"
              using hmul_class hfa(2) hfb(2) by simp
            thus ?thesis unfolding G4_def top1_fundamental_group_carrier_def
              using hprod_loop by (by100 blast)
          qed
          have "inv_into G4 f3 (f3 (M4 (inv_into G4 f3 x) (inv_into G4 f3 y)))
              = M4 (inv_into G4 f3 x) (inv_into G4 f3 y)"
            by (rule inv_into_f_f[OF bij_betw_imp_inj_on[OF hb3] hM4_cl])
          thus "inv_into G4 f3 (M3 x y) = M4 (inv_into G4 f3 x) (inv_into G4 f3 y)"
            using hf3_eq by simp
        qed
        show "top1_group_hom_on G1 M1 top1_Z_group top1_Z_mul \<psi>"
          unfolding top1_group_hom_on_def
        proof (intro conjI ballI)
          fix x assume "x \<in> G1"
          thus "\<psi> x \<in> top1_Z_group"
            using h\<psi>_bij unfolding bij_betw_def by (by100 blast)
        next
          fix a b assume "a \<in> G1" and "b \<in> G1"
          note ha = \<open>a \<in> G1\<close> and hb = \<open>b \<in> G1\<close>
          have hf1a: "f1 a \<in> G2" using hh1 ha unfolding top1_group_hom_on_def by (by100 blast)
          have hf1b: "f1 b \<in> G2" using hh1 hb unfolding top1_group_hom_on_def by (by100 blast)
          have hf2f1a: "f2 (f1 a) \<in> G3" using hh2 hf1a unfolding top1_group_hom_on_def by (by100 blast)
          have hf2f1b: "f2 (f1 b) \<in> G3" using hh2 hf1b unfolding top1_group_hom_on_def by (by100 blast)
          have hif2f1a: "inv_into G4 f3 (f2 (f1 a)) \<in> G4" using hh3i_map hf2f1a by simp
          have hif2f1b: "inv_into G4 f3 (f2 (f1 b)) \<in> G4" using hh3i_map hf2f1b by simp
          \<comment> \<open>Chain the homomorphism equations.\<close>
          have "\<psi> (M1 a b) = f4 (inv_into G4 f3 (f2 (f1 (M1 a b))))"
            unfolding \<psi>_def by simp
          also have "f1 (M1 a b) = M2 (f1 a) (f1 b)"
            using hh1 ha hb unfolding top1_group_hom_on_def by (by100 blast)
          also have "f2 (M2 (f1 a) (f1 b)) = M3 (f2 (f1 a)) (f2 (f1 b))"
            using hh2 hf1a hf1b unfolding top1_group_hom_on_def by (by100 blast)
          also have "inv_into G4 f3 (M3 (f2 (f1 a)) (f2 (f1 b)))
              = M4 (inv_into G4 f3 (f2 (f1 a))) (inv_into G4 f3 (f2 (f1 b)))"
            using hh3i_hom hf2f1a hf2f1b by simp
          also have "f4 (M4 (inv_into G4 f3 (f2 (f1 a))) (inv_into G4 f3 (f2 (f1 b))))
              = top1_Z_mul (f4 (inv_into G4 f3 (f2 (f1 a)))) (f4 (inv_into G4 f3 (f2 (f1 b))))"
            using hh4 hif2f1a hif2f1b unfolding top1_group_hom_on_def by (by100 blast)
          also have "f4 (inv_into G4 f3 (f2 (f1 a))) = \<psi> a" unfolding \<psi>_def by simp
          also have "f4 (inv_into G4 f3 (f2 (f1 b))) = \<psi> b" unfolding \<psi>_def by simp
          finally show "\<psi> (M1 a b) = top1_Z_mul (\<psi> a) (\<psi> b)" .
        qed
      qed
      show "\<exists>f. top1_group_iso_on G1 M1 top1_Z_group top1_Z_mul f"
        using h\<psi>_iso unfolding G1_def M1_def by (by100 blast)
    qed
  qed
  \<comment> \<open>Extract generator from Z-isomorphism.\<close>
  obtain \<psi> where h\<psi>: "top1_group_iso_on
      (top1_fundamental_group_carrier ?X ?TX a)
      (top1_fundamental_group_mul ?X ?TX a)
      top1_Z_group top1_Z_mul \<psi>"
    using hpi1_iso_Z unfolding top1_groups_isomorphic_on_def by (by100 blast)
  have h\<psi>_bij: "bij_betw \<psi> (top1_fundamental_group_carrier ?X ?TX a) top1_Z_group"
    using h\<psi> unfolding top1_group_iso_on_def by (by100 blast)
  have h\<psi>_hom: "top1_group_hom_on
      (top1_fundamental_group_carrier ?X ?TX a) (top1_fundamental_group_mul ?X ?TX a)
      top1_Z_group top1_Z_mul \<psi>"
    using h\<psi> unfolding top1_group_iso_on_def by (by100 blast)
  \<comment> \<open>\<psi>\<inverse>(1): preimage of 1 under \<psi> is a homotopy class.\<close>
  define gen_class where "gen_class = inv_into (top1_fundamental_group_carrier ?X ?TX a) \<psi> (1::int)"
  have hgc_in: "gen_class \<in> top1_fundamental_group_carrier ?X ?TX a"
  proof -
    have "(1::int) \<in> \<psi> ` (top1_fundamental_group_carrier ?X ?TX a)"
      using h\<psi>_bij unfolding bij_betw_def top1_Z_group_def by simp
    thus ?thesis unfolding gen_class_def by (rule inv_into_into)
  qed
  have h\<psi>gc: "\<psi> gen_class = (1::int)"
    unfolding gen_class_def
    by (rule f_inv_into_f) (simp add: top1_Z_group_def h\<psi>_bij[unfolded bij_betw_def])
  \<comment> \<open>Extract a representative loop from gen_class.\<close>
  obtain gen where hgen_loop: "top1_is_loop_on ?X ?TX a gen"
      and hgen_class: "gen_class = {g. top1_loop_equiv_on ?X ?TX a gen g}"
    using hgc_in unfolding top1_fundamental_group_carrier_def by (by100 blast)
  \<comment> \<open>Now show the generator property: every loop is homotopic to gen^n or (gen\<inverse>)^n.\<close>
  show ?thesis
  proof (intro exI[of _ gen] conjI allI impI)
    show "top1_is_loop_on ?X ?TX a gen" by (rule hgen_loop)
  next
    fix f assume hf_loop: "top1_is_loop_on ?X ?TX a f"
    \<comment> \<open>[f] \<in> \<pi>_1(X,a)\<close>
    define f_class where "f_class = {g. top1_loop_equiv_on ?X ?TX a f g}"
    have hfc_in: "f_class \<in> top1_fundamental_group_carrier ?X ?TX a"
      unfolding f_class_def top1_fundamental_group_carrier_def
      using hf_loop by (by100 blast)
    \<comment> \<open>\<psi>([f]) = n for some integer n.\<close>
    define n_int where "n_int = \<psi> f_class"
    \<comment> \<open>We need: f \<simeq> gen^n or f \<simeq> (gen\<inverse>)^|n| where n = |n_int|.\<close>
    \<comment> \<open>Key: [gen]^n = [gen^n] in the fundamental group (mul iterated = path_power class).\<close>
    \<comment> \<open>And \<psi>([gen]^n) = n\<cdot>\<psi>([gen]) = n\<cdot>1 = n.\<close>
    \<comment> \<open>Since \<psi> bijective: [f] = [gen]^n when \<psi>([f]) = n.\<close>
    \<comment> \<open>Then f \<in> [gen^n] means f \<simeq> gen^n.\<close>
    \<comment> \<open>Key bridge lemma: \<psi>([gen^k]) = int k for all k::nat.\<close>
    have hTX_local: "is_topology_on ?X ?TX"
      by (rule subspace_topology_is_topology_on[OF
            is_topology_on_strict_imp[OF assms(1)]]) (by100 blast)
    \<comment> \<open>\<psi> maps identity class to 0.\<close>
    have h\<psi>_id: "\<psi> (top1_fundamental_group_id ?X ?TX a) = (0::int)"
    proof -
      define e_class where "e_class = top1_fundamental_group_id ?X ?TX a"
      have haX: "a \<in> ?X" using assms(5) by (by100 blast)
      have hconst_loop: "top1_is_loop_on ?X ?TX a (top1_constant_path a)"
        unfolding top1_is_loop_on_def
        by (rule top1_constant_path_is_path[OF hTX_local haX])
      have he_in: "e_class \<in> top1_fundamental_group_carrier ?X ?TX a"
        unfolding e_class_def top1_fundamental_group_id_def top1_fundamental_group_carrier_def
        using hconst_loop by (by100 blast)
      \<comment> \<open>mul(e, e) = e: use left identity const*const \<simeq> const + mul_class.\<close>
      have hmul_ee: "top1_fundamental_group_mul ?X ?TX a e_class e_class = e_class"
      proof -
        have hmul_class: "top1_fundamental_group_mul ?X ?TX a
            {g. top1_loop_equiv_on ?X ?TX a (top1_constant_path a) g}
            {g. top1_loop_equiv_on ?X ?TX a (top1_constant_path a) g}
          = {h. top1_loop_equiv_on ?X ?TX a
              (top1_path_product (top1_constant_path a) (top1_constant_path a)) h}"
          by (rule top1_fundamental_group_mul_class[OF hTX_local hconst_loop hconst_loop])
        have hlid: "top1_path_homotopic_on ?X ?TX a a
            (top1_path_product (top1_constant_path a) (top1_constant_path a)) (top1_constant_path a)"
          by (rule Theorem_51_2_left_identity[OF hTX_local
                top1_constant_path_is_path[OF hTX_local haX]])
        have hprod_loop: "top1_is_loop_on ?X ?TX a
            (top1_path_product (top1_constant_path a) (top1_constant_path a))"
          by (rule top1_path_product_is_loop[OF hTX_local hconst_loop hconst_loop])
        \<comment> \<open>Class equality: loop_equiv (const*const) h \<longleftrightarrow> loop_equiv const h.\<close>
        have hclass_eq: "{h. top1_loop_equiv_on ?X ?TX a
              (top1_path_product (top1_constant_path a) (top1_constant_path a)) h}
            = {g. top1_loop_equiv_on ?X ?TX a (top1_constant_path a) g}"
        proof (intro set_eqI iffI)
          fix h assume "h \<in> {h. top1_loop_equiv_on ?X ?TX a
              (top1_path_product (top1_constant_path a) (top1_constant_path a)) h}"
          hence "top1_loop_equiv_on ?X ?TX a
              (top1_path_product (top1_constant_path a) (top1_constant_path a)) h" by simp
          moreover have "top1_loop_equiv_on ?X ?TX a (top1_constant_path a)
              (top1_path_product (top1_constant_path a) (top1_constant_path a))"
            unfolding top1_loop_equiv_on_def
            using hconst_loop hprod_loop Lemma_51_1_path_homotopic_sym[OF hlid]
            unfolding top1_is_loop_on_def by (by100 blast)
          ultimately show "h \<in> {g. top1_loop_equiv_on ?X ?TX a (top1_constant_path a) g}"
            using top1_loop_equiv_on_trans[OF hTX_local] by (by100 blast)
        next
          fix h assume "h \<in> {g. top1_loop_equiv_on ?X ?TX a (top1_constant_path a) g}"
          hence "top1_loop_equiv_on ?X ?TX a (top1_constant_path a) h" by simp
          moreover have "top1_loop_equiv_on ?X ?TX a
              (top1_path_product (top1_constant_path a) (top1_constant_path a)) (top1_constant_path a)"
            unfolding top1_loop_equiv_on_def
            using hconst_loop hprod_loop hlid
            unfolding top1_is_loop_on_def by (by100 blast)
          ultimately show "h \<in> {h. top1_loop_equiv_on ?X ?TX a
              (top1_path_product (top1_constant_path a) (top1_constant_path a)) h}"
            using top1_loop_equiv_on_trans[OF hTX_local] by (by100 blast)
        qed
        show ?thesis using hmul_class hclass_eq
          unfolding e_class_def top1_fundamental_group_id_def by simp
      qed
      \<comment> \<open>\<psi>(mul e e) = \<psi>(e) + \<psi>(e), and mul e e = e.\<close>
      have "\<psi> e_class = top1_Z_mul (\<psi> e_class) (\<psi> e_class)"
      proof -
        have "\<psi> (top1_fundamental_group_mul ?X ?TX a e_class e_class)
            = top1_Z_mul (\<psi> e_class) (\<psi> e_class)"
          using h\<psi>_hom he_in unfolding top1_group_hom_on_def by (by100 blast)
        thus ?thesis using hmul_ee by simp
      qed
      hence "\<psi> e_class = \<psi> e_class + \<psi> e_class" unfolding top1_Z_mul_def .
      hence "\<psi> e_class = 0" by linarith
      thus ?thesis unfolding e_class_def .
    qed
    \<comment> \<open>Path power class correspondence: [gen^(Suc k)] = mul [gen] [gen^k].\<close>
    have hpower_class_step: "\<And>k::nat.
        {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a (Suc k)) g} =
        top1_fundamental_group_mul ?X ?TX a gen_class
          {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a k) g}"
    proof -
      fix k :: nat
      have hpk_loop: "top1_is_loop_on ?X ?TX a (top1_path_power gen a k)"
        by (rule top1_path_power_is_loop[OF hTX_local hgen_loop])
      have "top1_fundamental_group_mul ?X ?TX a
          {g. top1_loop_equiv_on ?X ?TX a gen g}
          {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a k) g}
        = {h. top1_loop_equiv_on ?X ?TX a (top1_path_product gen (top1_path_power gen a k)) h}"
        by (rule top1_fundamental_group_mul_class[OF hTX_local hgen_loop hpk_loop])
      also have "top1_path_product gen (top1_path_power gen a k) = top1_path_power gen a (Suc k)"
        by simp
      finally have "top1_fundamental_group_mul ?X ?TX a
          {g. top1_loop_equiv_on ?X ?TX a gen g}
          {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a k) g}
        = {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a (Suc k)) g}" .
      thus "{g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a (Suc k)) g} =
        top1_fundamental_group_mul ?X ?TX a gen_class
          {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a k) g}"
        using hgen_class by simp
    qed
    have hpk_in_carrier: "\<And>k::nat. {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a k) g}
        \<in> top1_fundamental_group_carrier ?X ?TX a"
      unfolding top1_fundamental_group_carrier_def
      using top1_path_power_is_loop[OF hTX_local hgen_loop] by (by100 blast)
    have h\<psi>_power: "\<And>k::nat. \<psi> {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a k) g} = int k"
    proof -
      fix k :: nat show "\<psi> {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a k) g} = int k"
      proof (induction k)
        case 0
        have "{g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a 0) g}
            = {g. top1_loop_equiv_on ?X ?TX a (top1_constant_path a) g}"
          by simp
        also have "\<dots> = top1_fundamental_group_id ?X ?TX a"
          unfolding top1_fundamental_group_id_def by simp
        finally show ?case using h\<psi>_id by simp
      next
        case (Suc k)
        have "\<psi> {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a (Suc k)) g}
            = \<psi> (top1_fundamental_group_mul ?X ?TX a gen_class
                {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a k) g})"
          using hpower_class_step by simp
        also have "\<dots> = top1_Z_mul (\<psi> gen_class)
            (\<psi> {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a k) g})"
          using h\<psi>_hom hgc_in hpk_in_carrier
          unfolding top1_group_hom_on_def by (by100 blast)
        also have "\<dots> = top1_Z_mul 1 (int k)"
          using h\<psi>gc Suc.IH by simp
        also have "\<dots> = int (Suc k)" unfolding top1_Z_mul_def by simp
        finally show ?case .
      qed
    qed
    \<comment> \<open>\<psi>([gen\<inverse>]) = -1. From gen*gen\<inverse> \<simeq> const, so \<psi>([gen*gen\<inverse>]) = \<psi>(e) = 0.
       Also \<psi>([gen*gen\<inverse>]) = \<psi>([gen]) + \<psi>([gen\<inverse>]) = 1 + \<psi>([gen\<inverse>]). So \<psi>([gen\<inverse>]) = -1.\<close>
    define rev_class where "rev_class = {g. top1_loop_equiv_on ?X ?TX a (top1_path_reverse gen) g}"
    have hrc_in: "rev_class \<in> top1_fundamental_group_carrier ?X ?TX a"
      unfolding rev_class_def top1_fundamental_group_carrier_def
      using top1_path_reverse_is_loop[OF hgen_loop] by (by100 blast)
    have haX: "a \<in> ?X" using assms(5) by (by100 blast)
    have hconst_loop: "top1_is_loop_on ?X ?TX a (top1_constant_path a)"
      unfolding top1_is_loop_on_def
      by (rule top1_constant_path_is_path[OF hTX_local haX])
    have h\<psi>_rev: "\<psi> rev_class = -(1::int)"
    proof -
      \<comment> \<open>gen * gen\<inverse> \<simeq> const.\<close>
      have hgen_path: "top1_is_path_on ?X ?TX a a gen"
        using hgen_loop unfolding top1_is_loop_on_def .
      have hinv_left: "top1_path_homotopic_on ?X ?TX a a
          (top1_path_product gen (top1_path_reverse gen)) (top1_constant_path a)"
        by (rule Theorem_51_2_invgerse_left[OF hTX_local hgen_path])
      \<comment> \<open>mul(gen_class, rev_class) = [gen * gen\<inverse>].\<close>
      have hmul_gr: "top1_fundamental_group_mul ?X ?TX a gen_class rev_class
          = {h. top1_loop_equiv_on ?X ?TX a (top1_path_product gen (top1_path_reverse gen)) h}"
        unfolding rev_class_def
        using top1_fundamental_group_mul_class[OF hTX_local hgen_loop
              top1_path_reverse_is_loop[OF hgen_loop]]
              hgen_class by simp
      \<comment> \<open>[gen * gen\<inverse>] = [const] = e_class, using hinv_left.\<close>
      have hprod_rev_loop: "top1_is_loop_on ?X ?TX a (top1_path_product gen (top1_path_reverse gen))"
        by (rule top1_path_product_is_loop[OF hTX_local hgen_loop
              top1_path_reverse_is_loop[OF hgen_loop]])
      have hclass_eq: "{h. top1_loop_equiv_on ?X ?TX a (top1_path_product gen (top1_path_reverse gen)) h}
          = top1_fundamental_group_id ?X ?TX a"
        unfolding top1_fundamental_group_id_def
      proof (intro set_eqI iffI)
        fix h assume "h \<in> {h. top1_loop_equiv_on ?X ?TX a
            (top1_path_product gen (top1_path_reverse gen)) h}"
        hence "top1_loop_equiv_on ?X ?TX a (top1_path_product gen (top1_path_reverse gen)) h" by simp
        moreover have "top1_loop_equiv_on ?X ?TX a (top1_constant_path a)
            (top1_path_product gen (top1_path_reverse gen))"
          unfolding top1_loop_equiv_on_def
          using hconst_loop hprod_rev_loop Lemma_51_1_path_homotopic_sym[OF hinv_left]
          unfolding top1_is_loop_on_def by (by100 blast)
        ultimately show "h \<in> {g. top1_loop_equiv_on ?X ?TX a (top1_constant_path a) g}"
          using top1_loop_equiv_on_trans[OF hTX_local] by (by100 blast)
      next
        fix h assume "h \<in> {g. top1_loop_equiv_on ?X ?TX a (top1_constant_path a) g}"
        hence "top1_loop_equiv_on ?X ?TX a (top1_constant_path a) h" by simp
        moreover have "top1_loop_equiv_on ?X ?TX a
            (top1_path_product gen (top1_path_reverse gen)) (top1_constant_path a)"
          unfolding top1_loop_equiv_on_def
          using hconst_loop hprod_rev_loop hinv_left
          unfolding top1_is_loop_on_def by (by100 blast)
        ultimately show "h \<in> {h. top1_loop_equiv_on ?X ?TX a
            (top1_path_product gen (top1_path_reverse gen)) h}"
          using top1_loop_equiv_on_trans[OF hTX_local] by (by100 blast)
      qed
      hence hmul_gr_id: "top1_fundamental_group_mul ?X ?TX a gen_class rev_class
          = top1_fundamental_group_id ?X ?TX a"
        using hmul_gr by simp
      \<comment> \<open>\<psi>(mul gen_class rev_class) = \<psi>(gen_class) + \<psi>(rev_class) = 1 + \<psi>(rev_class).\<close>
      have "\<psi> (top1_fundamental_group_mul ?X ?TX a gen_class rev_class)
          = top1_Z_mul (\<psi> gen_class) (\<psi> rev_class)"
        using h\<psi>_hom hgc_in hrc_in unfolding top1_group_hom_on_def by (by100 blast)
      hence "top1_Z_mul 1 (\<psi> rev_class) = 0"
        using hmul_gr_id h\<psi>_id h\<psi>gc by simp
      thus "\<psi> rev_class = -1" unfolding top1_Z_mul_def by linarith
    qed
    have hrev_gen_loop: "top1_is_loop_on ?X ?TX a (top1_path_reverse gen)"
      by (rule top1_path_reverse_is_loop[OF hgen_loop])
    have hpower_rev_class_step: "\<And>k::nat.
        {g. top1_loop_equiv_on ?X ?TX a (top1_path_power (top1_path_reverse gen) a (Suc k)) g} =
        top1_fundamental_group_mul ?X ?TX a rev_class
          {g. top1_loop_equiv_on ?X ?TX a (top1_path_power (top1_path_reverse gen) a k) g}"
    proof -
      fix k :: nat
      have hrpk_loop: "top1_is_loop_on ?X ?TX a (top1_path_power (top1_path_reverse gen) a k)"
        by (rule top1_path_power_is_loop[OF hTX_local hrev_gen_loop])
      have "top1_fundamental_group_mul ?X ?TX a
          {g. top1_loop_equiv_on ?X ?TX a (top1_path_reverse gen) g}
          {g. top1_loop_equiv_on ?X ?TX a (top1_path_power (top1_path_reverse gen) a k) g}
        = {h. top1_loop_equiv_on ?X ?TX a
            (top1_path_product (top1_path_reverse gen) (top1_path_power (top1_path_reverse gen) a k)) h}"
        by (rule top1_fundamental_group_mul_class[OF hTX_local hrev_gen_loop hrpk_loop])
      also have "top1_path_product (top1_path_reverse gen) (top1_path_power (top1_path_reverse gen) a k)
          = top1_path_power (top1_path_reverse gen) a (Suc k)" by simp
      finally show "{g. top1_loop_equiv_on ?X ?TX a
          (top1_path_power (top1_path_reverse gen) a (Suc k)) g} =
        top1_fundamental_group_mul ?X ?TX a rev_class
          {g. top1_loop_equiv_on ?X ?TX a (top1_path_power (top1_path_reverse gen) a k) g}"
        unfolding rev_class_def by simp
    qed
    have hrpk_in_carrier: "\<And>k::nat. {g. top1_loop_equiv_on ?X ?TX a
          (top1_path_power (top1_path_reverse gen) a k) g}
        \<in> top1_fundamental_group_carrier ?X ?TX a"
      unfolding top1_fundamental_group_carrier_def
      using top1_path_power_is_loop[OF hTX_local top1_path_reverse_is_loop[OF hgen_loop]]
      by (by100 blast)
    have h\<psi>_rev_power: "\<And>k::nat. \<psi> {g. top1_loop_equiv_on ?X ?TX a
        (top1_path_power (top1_path_reverse gen) a k) g} = - int k"
    proof -
      fix k :: nat show "\<psi> {g. top1_loop_equiv_on ?X ?TX a
          (top1_path_power (top1_path_reverse gen) a k) g} = - int k"
      proof (induction k)
        case 0
        have "{g. top1_loop_equiv_on ?X ?TX a (top1_path_power (top1_path_reverse gen) a 0) g}
            = {g. top1_loop_equiv_on ?X ?TX a (top1_constant_path a) g}" by simp
        also have "\<dots> = top1_fundamental_group_id ?X ?TX a"
          unfolding top1_fundamental_group_id_def by simp
        finally show ?case using h\<psi>_id by simp
      next
        case (Suc k)
        have "\<psi> {g. top1_loop_equiv_on ?X ?TX a (top1_path_power (top1_path_reverse gen) a (Suc k)) g}
            = \<psi> (top1_fundamental_group_mul ?X ?TX a rev_class
                {g. top1_loop_equiv_on ?X ?TX a (top1_path_power (top1_path_reverse gen) a k) g})"
          using hpower_rev_class_step by simp
        also have "\<dots> = top1_Z_mul (\<psi> rev_class)
            (\<psi> {g. top1_loop_equiv_on ?X ?TX a (top1_path_power (top1_path_reverse gen) a k) g})"
          using h\<psi>_hom hrc_in hrpk_in_carrier
          unfolding top1_group_hom_on_def by (by100 blast)
        also have "\<dots> = top1_Z_mul (-1) (- int k)"
          using h\<psi>_rev Suc.IH by simp
        also have "\<dots> = - int (Suc k)" unfolding top1_Z_mul_def by simp
        finally show ?case .
      qed
    qed
    \<comment> \<open>Case analysis on sign of n_int.\<close>
    show "\<exists>n. top1_path_homotopic_on ?X ?TX a a f (top1_path_power gen a n) \<or>
         top1_path_homotopic_on ?X ?TX a a f (top1_path_power (top1_path_reverse gen) a n)"
    proof (cases "n_int \<ge> 0")
      case True
      define k where "k = nat n_int"
      have "\<psi> {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a k) g} = int k"
        by (rule h\<psi>_power)
      moreover have "int k = n_int" using True k_def by simp
      ultimately have h\<psi>_eq: "\<psi> {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a k) g} = n_int"
        by simp
      \<comment> \<open>Both f_class and [gen^k] map to n_int under \<psi>. By injectivity: f_class = [gen^k].\<close>
      have hpk_class_in: "{g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a k) g}
          \<in> top1_fundamental_group_carrier ?X ?TX a"
        unfolding top1_fundamental_group_carrier_def
        using top1_path_power_is_loop[OF hTX_local hgen_loop] by (by100 blast)
      have hfc_eq_pk: "f_class = {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a k) g}"
        using bij_betw_imp_inj_on[OF h\<psi>_bij] hfc_in hpk_class_in h\<psi>_eq
        unfolding n_int_def inj_on_def by (by100 blast)
      have "f \<in> f_class" unfolding f_class_def
        using top1_loop_equiv_on_refl[OF hf_loop] by simp
      hence "f \<in> {g. top1_loop_equiv_on ?X ?TX a (top1_path_power gen a k) g}"
        using hfc_eq_pk by simp
      hence "top1_loop_equiv_on ?X ?TX a (top1_path_power gen a k) f" by simp
      hence "top1_path_homotopic_on ?X ?TX a a (top1_path_power gen a k) f"
        unfolding top1_loop_equiv_on_def by (by100 blast)
      hence "top1_path_homotopic_on ?X ?TX a a f (top1_path_power gen a k)"
        by (rule Lemma_51_1_path_homotopic_sym)
      thus ?thesis by (by100 blast)
    next
      case False
      hence hn_neg: "n_int < 0" by simp
      define k where "k = nat (- n_int)"
      have "\<psi> {g. top1_loop_equiv_on ?X ?TX a (top1_path_power (top1_path_reverse gen) a k) g} = - int k"
        by (rule h\<psi>_rev_power)
      moreover have "- int k = n_int" using hn_neg k_def by simp
      ultimately have h\<psi>_eq: "\<psi> {g. top1_loop_equiv_on ?X ?TX a
          (top1_path_power (top1_path_reverse gen) a k) g} = n_int"
        by simp
      have hrev_loop: "top1_is_loop_on ?X ?TX a (top1_path_reverse gen)"
        by (rule top1_path_reverse_is_loop[OF hgen_loop])
      have hpk_class_in: "{g. top1_loop_equiv_on ?X ?TX a
            (top1_path_power (top1_path_reverse gen) a k) g}
          \<in> top1_fundamental_group_carrier ?X ?TX a"
        unfolding top1_fundamental_group_carrier_def
        using top1_path_power_is_loop[OF hTX_local hrev_loop] by (by100 blast)
      have hfc_eq_rpk: "f_class = {g. top1_loop_equiv_on ?X ?TX a
          (top1_path_power (top1_path_reverse gen) a k) g}"
        using bij_betw_imp_inj_on[OF h\<psi>_bij] hfc_in hpk_class_in h\<psi>_eq
        unfolding n_int_def inj_on_def by (by100 blast)
      have "f \<in> f_class" unfolding f_class_def
        using top1_loop_equiv_on_refl[OF hf_loop] by simp
      hence "f \<in> {g. top1_loop_equiv_on ?X ?TX a
          (top1_path_power (top1_path_reverse gen) a k) g}"
        using hfc_eq_rpk by simp
      hence "top1_loop_equiv_on ?X ?TX a (top1_path_power (top1_path_reverse gen) a k) f" by simp
      hence "top1_path_homotopic_on ?X ?TX a a (top1_path_power (top1_path_reverse gen) a k) f"
        unfolding top1_loop_equiv_on_def by (by100 blast)
      hence "top1_path_homotopic_on ?X ?TX a a f (top1_path_power (top1_path_reverse gen) a k)"
        by (rule Lemma_51_1_path_homotopic_sym)
      thus ?thesis by (by100 blast)
    qed
  qed
qed

text \<open>Corollary: \<pi>_1(S2-\{p,q\}) is isomorphic to Z as a group.
  Derived from pi1\_S2\_minus\_two\_points\_infinite\_cyclic: the Z-isomorphism
  hpi1\_iso\_Z is an intermediate result in its proof (line 3375).
  Proved as pi1\_S2\_minus\_two\_points\_iso\_Z in AlgTopCached.thy.\<close>

text \<open>If f \<simeq> g (loops at a), then f^n \<simeq> g^n.\<close>
lemma path_homotopic_path_power:
  assumes "is_topology_on X TX"
      and "top1_path_homotopic_on X TX a a f g"
      and "top1_is_path_on X TX a a f" and "top1_is_path_on X TX a a g"
  shows "top1_path_homotopic_on X TX a a (top1_path_power f a n) (top1_path_power g a n)"
proof (induction n)
  case 0
  have haX: "a \<in> X"
  proof -
    have "f 0 = a" using assms(3) unfolding top1_is_path_on_def by (by100 blast)
    moreover have "f 0 \<in> X"
    proof -
      have "\<forall>s\<in>I_set. f s \<in> X" using assms(3)
        unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
      ultimately show ?thesis by (by100 blast)
    qed
    ultimately show ?thesis by simp
  qed
  show ?case by (simp add: Lemma_51_1_path_homotopic_refl[OF
      top1_constant_path_is_path[OF assms(1) haX]])
next
  case (Suc n)
  \<comment> \<open>f^{n+1} = f * f^n \<simeq> g * g^n = g^{n+1} by product compatibility.\<close>
  have hfn: "top1_is_path_on X TX a a (top1_path_power f a n)"
    by (rule top1_path_power_is_path[OF assms(1)]) (simp add: assms(3) top1_is_loop_on_def)
  have hgn: "top1_is_path_on X TX a a (top1_path_power g a n)"
    by (rule top1_path_power_is_path[OF assms(1)]) (simp add: assms(4) top1_is_loop_on_def)
  have h1: "top1_path_homotopic_on X TX a a (top1_path_product f (top1_path_power f a n))
      (top1_path_product g (top1_path_power f a n))"
    by (rule path_homotopic_product_left[OF assms(1) assms(2) hfn])
  have h2: "top1_path_homotopic_on X TX a a (top1_path_product g (top1_path_power f a n))
      (top1_path_product g (top1_path_power g a n))"
    by (rule path_homotopic_product_right[OF assms(1) Suc assms(4)])
  show ?case by (simp add: Lemma_51_1_path_homotopic_trans[OF assms(1) h1 h2])
qed


text \<open>Path power addition: f^a * f^b \<simeq> f^{a+b} (for loops at a).\<close>
lemma path_power_product_add:
  assumes "is_topology_on X TX" and "top1_is_loop_on X TX a f"
  shows "top1_path_homotopic_on X TX a a
    (top1_path_product (top1_path_power f a m) (top1_path_power f a n))
    (top1_path_power f a (m + n))"
proof (induction m)
  case 0
  \<comment> \<open>const * f^n \<simeq> f^n = f^{0+n}.\<close>
  show ?case by (simp add: Theorem_51_2_left_identity[OF assms(1)
      top1_path_power_is_path[OF assms]])
next
  case (Suc m)
  \<comment> \<open>f^{m+1} * f^n = (f * f^m) * f^n \<simeq> f * (f^m * f^n) \<simeq> f * f^{m+n} = f^{m+1+n}.\<close>
  have hf: "top1_is_path_on X TX a a f" using assms(2) unfolding top1_is_loop_on_def by simp
  have hfm: "top1_is_path_on X TX a a (top1_path_power f a m)"
    by (rule top1_path_power_is_path[OF assms])
  have hfn: "top1_is_path_on X TX a a (top1_path_power f a n)"
    by (rule top1_path_power_is_path[OF assms])
  have hfmn: "top1_is_path_on X TX a a (top1_path_power f a (m + n))"
    by (rule top1_path_power_is_path[OF assms])
  have hfm_fn: "top1_is_path_on X TX a a (top1_path_product (top1_path_power f a m) (top1_path_power f a n))"
    by (rule top1_path_product_is_path[OF assms(1) hfm hfn])
  \<comment> \<open>Step 1: (f * f^m) * f^n \<simeq> f * (f^m * f^n) by associativity.\<close>
  have h_assoc: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_product f (top1_path_power f a m)) (top1_path_power f a n))
      (top1_path_product f (top1_path_product (top1_path_power f a m) (top1_path_power f a n)))"
    by (rule Lemma_51_1_path_homotopic_sym[OF
        Theorem_51_2_associativity[OF assms(1) hf hfm hfn]])
  \<comment> \<open>Step 2: f * (f^m * f^n) \<simeq> f * f^{m+n} by IH.\<close>
  have h_IH: "top1_path_homotopic_on X TX a a
      (top1_path_product f (top1_path_product (top1_path_power f a m) (top1_path_power f a n)))
      (top1_path_product f (top1_path_power f a (m + n)))"
    by (rule path_homotopic_product_right[OF assms(1) Suc hf])
  \<comment> \<open>Combine.\<close>
  have "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_power f a (Suc m)) (top1_path_power f a n))
      (top1_path_product f (top1_path_product (top1_path_power f a m) (top1_path_power f a n)))"
    using h_assoc by simp
  hence "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_power f a (Suc m)) (top1_path_power f a n))
      (top1_path_product f (top1_path_power f a (m + n)))"
    by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) _ h_IH])
  thus ?case by simp
qed

text \<open>Path power multiplication: (f^m)^n \<simeq> f^{m*n} (for loops at a).\<close>
lemma path_power_mult:
  assumes "is_topology_on X TX" and "top1_is_loop_on X TX a f"
  shows "top1_path_homotopic_on X TX a a
    (top1_path_power (top1_path_power f a m) a n)
    (top1_path_power f a (m * n))"
proof (induction n)
  case 0
  have haX: "a \<in> X"
    using top1_is_loop_on_start[OF assms(2)]
          top1_is_loop_on_continuous[OF assms(2)]
    unfolding top1_continuous_map_on_def top1_unit_interval_def by force
  show ?case by (simp add: Lemma_51_1_path_homotopic_refl[OF
      top1_constant_path_is_path[OF assms(1) haX]])
next
  case (Suc n)
  have hfm_loop: "top1_is_loop_on X TX a (top1_path_power f a m)"
    by (rule top1_path_power_is_loop[OF assms])
  have hfm: "top1_is_path_on X TX a a (top1_path_power f a m)"
    using hfm_loop unfolding top1_is_loop_on_def by simp
  have h1: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_power f a m) (top1_path_power (top1_path_power f a m) a n))
      (top1_path_product (top1_path_power f a m) (top1_path_power f a (m * n)))"
    by (rule path_homotopic_product_right[OF assms(1) Suc hfm])
  have h2: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_power f a m) (top1_path_power f a (m * n)))
      (top1_path_power f a (m + m * n))"
    by (rule path_power_product_add[OF assms])
  have h12: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_power f a m) (top1_path_power (top1_path_power f a m) a n))
      (top1_path_power f a (m + m * n))"
    by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) h1 h2])
  have hgoal_lhs: "top1_path_power (top1_path_power f a m) a (Suc n)
      = top1_path_product (top1_path_power f a m) (top1_path_power (top1_path_power f a m) a n)"
    by simp
  have hgoal_rhs: "m * Suc n = m + m * n" by simp
  show ?case using h12 unfolding hgoal_lhs hgoal_rhs .
qed


text \<open>Reverse distributes over power: (f^n)\<inverse> \<simeq> (f\<inverse>)^n.\<close>
lemma path_power_reverse:
  assumes "is_topology_on X TX" and "top1_is_loop_on X TX a f"
  shows "top1_path_homotopic_on X TX a a
    (top1_path_reverse (top1_path_power f a n))
    (top1_path_power (top1_path_reverse f) a n)"
proof (induction n)
  case 0
  \<comment> \<open>(const)\<inverse> = const = (f\<inverse>)^0. Definitional.\<close>
  have haX: "a \<in> X"
    using top1_is_loop_on_start[OF assms(2)] top1_is_loop_on_continuous[OF assms(2)]
    unfolding top1_continuous_map_on_def top1_unit_interval_def by force
  have "top1_path_reverse (top1_constant_path a) = top1_constant_path a"
    unfolding top1_path_reverse_def top1_constant_path_def by auto
  thus ?case by (simp add: Lemma_51_1_path_homotopic_refl[OF
      top1_constant_path_is_path[OF assms(1) haX]])
next
  case (Suc n)
  \<comment> \<open>(f * f^n)\<inverse> = (f^n)\<inverse> * f\<inverse> (definitional).
     \<simeq> (f\<inverse>)^n * f\<inverse> (IH + product left).
     \<simeq> (f\<inverse>)^n * (f\<inverse>)^1 (product right with f\<inverse> \<simeq> (f\<inverse>)^1 via right identity sym).
     \<simeq> (f\<inverse>)^{n+1} (path_power_product_add).\<close>
  have hf: "top1_is_path_on X TX a a f" using assms(2) unfolding top1_is_loop_on_def by simp
  have hfr: "top1_is_path_on X TX a a (top1_path_reverse f)"
    using top1_path_reverse_is_path[OF hf] hf unfolding top1_is_path_on_def top1_path_reverse_def by auto
  have hfr_loop: "top1_is_loop_on X TX a (top1_path_reverse f)"
    by (rule top1_path_reverse_is_loop[OF assms(2)])
  have hfn: "top1_is_path_on X TX a a (top1_path_power f a n)"
    by (rule top1_path_power_is_path[OF assms])
  have hfn_rev: "top1_is_path_on X TX a a (top1_path_reverse (top1_path_power f a n))"
    using top1_path_reverse_is_path[OF hfn] hfn
    unfolding top1_is_path_on_def top1_path_reverse_def by auto
  have hfrn: "top1_is_path_on X TX a a (top1_path_power (top1_path_reverse f) a n)"
    by (rule top1_path_power_is_path[OF assms(1) hfr_loop])
  \<comment> \<open>Step 1: (f * f^n)\<inverse> = (f^n)\<inverse> * f\<inverse> (definitional equality).\<close>
  have hrev_eq: "top1_path_reverse (top1_path_power f a (Suc n))
      = top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f)"
  proof (rule ext)
    fix s :: real
    have hf0: "f 0 = a" and hf1: "f 1 = a"
      using hf unfolding top1_is_path_on_def by (by100 blast)+
    have hfn0: "top1_path_power f a n 0 = a" and hfn1: "top1_path_power f a n 1 = a"
      using hfn unfolding top1_is_path_on_def by (by100 blast)+
    show "top1_path_reverse (top1_path_power f a (Suc n)) s
        = top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f) s"
    proof (cases "s < 1/2")
      case True
      \<comment> \<open>s < 1/2, so 1-s > 1/2. LHS uses else branch, RHS uses then branch.\<close>
      have h1s: "\<not> ((1::real) - s \<le> 1/2)" using True by linarith
      have lhs: "top1_path_reverse (top1_path_power f a (Suc n)) s
          = top1_path_power f a n (1 - 2*s)"
      proof -
        have "top1_path_reverse (top1_path_power f a (Suc n)) s
            = top1_path_product f (top1_path_power f a n) (1 - s)"
          unfolding top1_path_reverse_def by simp
        also have "... = top1_path_power f a n (2 * (1 - s) - 1)"
          unfolding top1_path_product_def using h1s by simp
        also have "(2::real) * (1 - s) - 1 = 1 - 2 * s" by (simp add: algebra_simps)
        finally show ?thesis by simp
      qed
      have hs2: "s \<le> 1/2" using True by simp
      have rhs: "top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f) s
          = top1_path_power f a n (1 - 2*s)"
        unfolding top1_path_product_def top1_path_reverse_def using hs2 by simp
      show ?thesis using lhs rhs by simp
    next
      case False
      hence hs_ge: "s \<ge> 1/2" by simp
      show ?thesis
      proof (cases "s > 1/2")
        case True
        have h1s: "((1::real) - s) \<le> 1/2" using True by linarith
        have lhs: "top1_path_reverse (top1_path_power f a (Suc n)) s
            = f (2 - 2*s)"
        proof -
          have "top1_path_reverse (top1_path_power f a (Suc n)) s
              = top1_path_product f (top1_path_power f a n) (1 - s)"
            unfolding top1_path_reverse_def by simp
          also have "... = f (2 * (1 - s))"
            unfolding top1_path_product_def using h1s by simp
          also have "(2::real) * (1 - s) = 2 - 2 * s" by (simp add: algebra_simps)
          finally show ?thesis by simp
        qed
        have hs2: "\<not> (s \<le> 1/2)" using True by simp
        have rhs: "top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f) s
            = f (2 - 2*s)"
          unfolding top1_path_product_def top1_path_reverse_def using hs2 by simp
        show ?thesis using lhs rhs by simp
      next
        case False
        hence hs_eq: "s = 1/2" using hs_ge by simp
        \<comment> \<open>At s = 1/2: both sides = a (boundary between branches).\<close>
        have lhs': "top1_path_reverse (top1_path_power f a (Suc n)) (1/2) = a"
        proof -
          have "top1_path_reverse (top1_path_power f a (Suc n)) (1/2)
              = top1_path_product f (top1_path_power f a n) (1/2)"
            unfolding top1_path_reverse_def by simp
          also have "... = f (2 * (1/2))"
            unfolding top1_path_product_def by simp
          also have "... = f 1" by simp
          also have "... = a" using hf1 by simp
          finally show ?thesis .
        qed
        have rhs: "top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f) (1/2)
            = top1_path_power f a n (1 - 2 * (1/2))"
          unfolding top1_path_product_def top1_path_reverse_def by simp
        hence rhs': "top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f) (1/2) = a"
          using hfn0 by simp
        have hs12: "s = 1/2" using hs_eq by linarith
        have "top1_path_reverse (top1_path_power f a (Suc n)) s = a"
          by (subst hs12, rule lhs')
        moreover have "top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f) s = a"
          by (subst hs12, rule rhs')
        ultimately show ?thesis by simp
      qed
    qed
  qed
  \<comment> \<open>Step 2: (f^n)\<inverse> * f\<inverse> \<simeq> (f\<inverse>)^n * f\<inverse> (IH + product_left).\<close>
  have h2: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f))
      (top1_path_product (top1_path_power (top1_path_reverse f) a n) (top1_path_reverse f))"
    by (rule path_homotopic_product_left[OF assms(1) Suc hfr])
  \<comment> \<open>Step 3: (f\<inverse>)^n * f\<inverse> \<simeq> (f\<inverse>)^n * (f\<inverse>)^1 (right identity sym: f\<inverse> \<simeq> f\<inverse> * const = (f\<inverse>)^1).\<close>
  have hfr_eq_fr1: "top1_path_homotopic_on X TX a a
      (top1_path_reverse f) (top1_path_power (top1_path_reverse f) a 1)"
  proof -
    have "(top1_path_power (top1_path_reverse f) a 1) =
        top1_path_product (top1_path_reverse f) (top1_constant_path a)" by simp
    moreover have "top1_path_homotopic_on X TX a a
        (top1_path_product (top1_path_reverse f) (top1_constant_path a)) (top1_path_reverse f)"
      by (rule Theorem_51_2_right_identity[OF assms(1) hfr])
    ultimately show ?thesis using Lemma_51_1_path_homotopic_sym by simp
  qed
  have h3: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_power (top1_path_reverse f) a n) (top1_path_reverse f))
      (top1_path_product (top1_path_power (top1_path_reverse f) a n) (top1_path_power (top1_path_reverse f) a 1))"
    by (rule path_homotopic_product_right[OF assms(1) hfr_eq_fr1 hfrn])
  \<comment> \<open>Step 4: (f\<inverse>)^n * (f\<inverse>)^1 \<simeq> (f\<inverse>)^{n+1} (path_power_product_add).\<close>
  have h4: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_power (top1_path_reverse f) a n) (top1_path_power (top1_path_reverse f) a 1))
      (top1_path_power (top1_path_reverse f) a (n + 1))"
    by (rule path_power_product_add[OF assms(1) hfr_loop])
  \<comment> \<open>Chain: rev(f^{n+1}) = rev(f^n) * rev(f) \<simeq> (f\<inverse>)^n * f\<inverse> \<simeq> (f\<inverse>)^n * (f\<inverse>)^1 \<simeq> (f\<inverse>)^{n+1}.\<close>
  have h23: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f))
      (top1_path_product (top1_path_power (top1_path_reverse f) a n) (top1_path_power (top1_path_reverse f) a 1))"
    by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) h2 h3])
  have h234: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f))
      (top1_path_power (top1_path_reverse f) a (n + 1))"
    by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) h23 h4])
  show ?case using h234 unfolding hrev_eq by simp
qed

text \<open>Corollary: if f \<simeq> g, then f\<inverse> \<simeq> g\<inverse>.\<close>
lemma path_homotopic_reverse:
  assumes "is_topology_on X TX"
      and "top1_path_homotopic_on X TX a a f g"
      and "top1_is_path_on X TX a a f" and "top1_is_path_on X TX a a g"
  shows "top1_path_homotopic_on X TX a a (top1_path_reverse f) (top1_path_reverse g)"
proof -
  \<comment> \<open>If F is a homotopy from f to g, then G(s,t) = F(1-s,t) is a homotopy from f\<inverse> to g\<inverse>.\<close>
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hFl: "\<forall>t\<in>I_set. F (0, t) = a" and hFr: "\<forall>t\<in>I_set. F (1, t) = a"
    using assms(2) unfolding top1_path_homotopic_on_def by blast
  define G where "G = (\<lambda>(s::real, t::real). F (1 - s, t))"
  have hrf: "top1_is_path_on X TX a a (top1_path_reverse f)"
    using top1_path_reverse_is_path[OF assms(3)] unfolding top1_path_reverse_def
    using assms(3) unfolding top1_is_path_on_def by auto
  have hrg: "top1_is_path_on X TX a a (top1_path_reverse g)"
    using top1_path_reverse_is_path[OF assms(4)] unfolding top1_path_reverse_def
    using assms(4) unfolding top1_is_path_on_def by auto
  show ?thesis unfolding top1_path_homotopic_on_def
  proof (intro exI[of _ G] conjI)
    show "top1_is_path_on X TX a a (top1_path_reverse f)" by (rule hrf)
    show "top1_is_path_on X TX a a (top1_path_reverse g)" by (rule hrg)
    show "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX G"
    proof -
      define \<phi> :: "real \<times> real \<Rightarrow> real \<times> real" where "\<phi> = (\<lambda>(s, t). (1 - s, t))"
      have hG_eq: "G = F \<circ> \<phi>" unfolding G_def \<phi>_def comp_def by auto
      have h\<phi>_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology (I_set \<times> I_set) II_topology \<phi>"
      proof -
        have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
        have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
          unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
        have hid: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
            (I_set \<times> I_set) (product_topology_on I_top I_top) id"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> I_set \<times> I_set" thus "id p \<in> I_set \<times> I_set" by (by100 simp)
        next
          fix W assume hW: "W \<in> product_topology_on I_top I_top"
          \<comment> \<open>{p \<in> I^2. id p \<in> W} = I^2 \<inter> W. Since I^2 \<in> T and W \<in> T, intersection \<in> T.\<close>
          have hII_mem: "(I_set \<times> I_set) \<in> product_topology_on I_top I_top"
            using hTII[unfolded II_topology_def] unfolding is_topology_on_def by (by100 blast)
          have heq: "{p \<in> I_set \<times> I_set. id p \<in> W} = (I_set \<times> I_set) \<inter> W" by (by100 auto)
          show "{p \<in> I_set \<times> I_set. id p \<in> W} \<in> product_topology_on I_top I_top"
            unfolding heq
            by (rule topology_inter_open[OF hTII[unfolded II_topology_def] hII_mem hW])
        qed
        have hprojs: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
            I_set I_top (pi1 \<circ> id) \<and>
            top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
            I_set I_top (pi2 \<circ> id)"
          using iffD1[OF Theorem_18_4[OF hTII[unfolded II_topology_def] hTI hTI] hid] by (by100 simp)
        have hfst: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top fst"
          using hprojs unfolding II_topology_def pi1_def comp_def by (by100 simp)
        have hsnd: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top snd"
          using hprojs unfolding II_topology_def pi2_def comp_def by (by100 simp)
        have hrev: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
          by (rule op_minus_continuous_on_interval)
        have hcomp: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top ((\<lambda>t. 1-t) \<circ> fst)"
          by (rule top1_continuous_map_on_comp[OF hfst hrev])
        have hpi1: "pi1 \<circ> \<phi> = (\<lambda>t. 1 - t) \<circ> fst"
          unfolding \<phi>_def pi1_def comp_def by (by100 auto)
        have hpi2: "pi2 \<circ> \<phi> = snd"
          unfolding \<phi>_def pi2_def comp_def by (by100 auto)
        have "top1_continuous_map_on (I_set \<times> I_set) II_topology
            (I_set \<times> I_set) (product_topology_on I_top I_top) \<phi>"
          using iffD2[OF Theorem_18_4[OF hTII hTI hTI]]
            hcomp[folded hpi1] hsnd[folded hpi2] by (by100 blast)
        thus ?thesis unfolding II_topology_def by (by100 simp)
      qed
      show ?thesis unfolding hG_eq by (rule top1_continuous_map_on_comp[OF h\<phi>_cont hF])
    qed
    show "\<forall>s\<in>I_set. G (s, 0) = top1_path_reverse f s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "1 - s \<in> I_set" using hs unfolding top1_unit_interval_def by auto
      show "G (s, 0) = top1_path_reverse f s"
        unfolding G_def top1_path_reverse_def using hF0 \<open>1 - s \<in> I_set\<close> by auto
    qed
    show "\<forall>s\<in>I_set. G (s, 1) = top1_path_reverse g s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "1 - s \<in> I_set" using hs unfolding top1_unit_interval_def by auto
      thus "G (s, 1) = top1_path_reverse g s"
        unfolding G_def top1_path_reverse_def using hF1 by auto
    qed
    show "\<forall>t\<in>I_set. G (0, t) = a"
    proof
      fix t assume ht: "t \<in> I_set"
      show "G (0, t) = a" unfolding G_def using hFr ht by simp
    qed
    show "\<forall>t\<in>I_set. G (1, t) = a"
    proof
      fix t assume ht: "t \<in> I_set"
      show "G (1, t) = a" unfolding G_def using hFl ht by simp
    qed
  qed
qed
\<comment> \<open>Key algebraic fact for 63.5: in an infinite cyclic group,
   any two nontrivial elements have a common nonzero power.
   Applied here: if [f] and [g] are both nontrivial in \<pi>_1(X) \<cong> Z,
   then \<exists> m>0, k>0. [f]^m = [g]^k (or [f]^m = [g^{-1}]^k).
   This contradicts Theorem_63_1_c.\<close>
lemma infinite_cyclic_common_power:
  assumes "is_topology_on X TX"
      and "top1_is_loop_on X TX a f"
      and "top1_is_loop_on X TX a g"
      and "\<not> top1_path_homotopic_on X TX a a f (top1_constant_path a)"
      and "\<not> top1_path_homotopic_on X TX a a g (top1_constant_path a)"
      and "\<exists>gen. top1_is_loop_on X TX a gen \<and>
            (\<forall>h. top1_is_loop_on X TX a h \<longrightarrow>
              (\<exists>n::nat. top1_path_homotopic_on X TX a a h (top1_path_power gen a n) \<or>
               top1_path_homotopic_on X TX a a h (top1_path_power (top1_path_reverse gen) a n)))"
  shows "\<exists>m k. m > 0 \<and>
      (top1_path_homotopic_on X TX a a
        (top1_path_power f a m) (top1_path_power g a k) \<or>
       top1_path_homotopic_on X TX a a
        (top1_path_power f a m) (top1_path_power (top1_path_reverse g) a k))"
proof -
  obtain gen where hgen: "top1_is_loop_on X TX a gen"
      and hgen_generates: "\<forall>h. top1_is_loop_on X TX a h \<longrightarrow>
        (\<exists>n::nat. top1_path_homotopic_on X TX a a h (top1_path_power gen a n) \<or>
         top1_path_homotopic_on X TX a a h (top1_path_power (top1_path_reverse gen) a n))"
    using assms(6) by (by100 blast)
  \<comment> \<open>[f] = gen^n1 or (gen^{-1})^n1 for some n1.\<close>
  obtain n1 where hn1: "top1_path_homotopic_on X TX a a f (top1_path_power gen a n1) \<or>
      top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_reverse gen) a n1)"
    using hgen_generates assms(2) by (by100 blast)
  obtain n2 where hn2: "top1_path_homotopic_on X TX a a g (top1_path_power gen a n2) \<or>
      top1_path_homotopic_on X TX a a g (top1_path_power (top1_path_reverse gen) a n2)"
    using hgen_generates assms(3) by (by100 blast)
  \<comment> \<open>n1 > 0 (since f nontrivial) and n2 > 0 (since g nontrivial).\<close>
  have hn1_pos: "n1 > 0"
  proof (rule ccontr)
    assume "\<not> n1 > 0" hence "n1 = 0" by simp
    hence "top1_path_homotopic_on X TX a a f (top1_constant_path a)"
      using hn1 by (simp add: top1_constant_path_def)
    thus False using assms(4) by simp
  qed
  have hn2_pos: "n2 > 0"
  proof (rule ccontr)
    assume "\<not> n2 > 0" hence "n2 = 0" by simp
    hence "top1_path_homotopic_on X TX a a g (top1_constant_path a)"
      using hn2 by (simp add: top1_constant_path_def)
    thus False using assms(5) by simp
  qed
  \<comment> \<open>Case analysis on signs. When both same sign: [f^n2] \<simeq> gen^{n1*n2} \<simeq> [g^n1].
     When opposite signs: need integer powers (path_reverse). Key facts used:
     - path_homotopic_path_power: f \<simeq> g \<Rightarrow> f^n \<simeq> g^n
     - path_power_mult: (f^m)^n \<simeq> f^{m*n}
     - Commutativity of nat multiplication: n1*n2 = n2*n1.\<close>
  have hf_path: "top1_is_path_on X TX a a f" using assms(2) unfolding top1_is_loop_on_def by simp
  have hg_path: "top1_is_path_on X TX a a g" using assms(3) unfolding top1_is_loop_on_def by simp
  have hgen_path: "top1_is_path_on X TX a a gen" using hgen unfolding top1_is_loop_on_def by simp
  have hgenn1: "top1_is_path_on X TX a a (top1_path_power gen a n1)"
    by (rule top1_path_power_is_path[OF assms(1) hgen])
  have hgenn2: "top1_is_path_on X TX a a (top1_path_power gen a n2)"
    by (rule top1_path_power_is_path[OF assms(1) hgen])
  \<comment> \<open>Handle the case where both f and g are positive powers of gen.\<close>
  show ?thesis using hn1 hn2
  proof (elim disjE)
    assume h1: "top1_path_homotopic_on X TX a a f (top1_path_power gen a n1)"
       and h2: "top1_path_homotopic_on X TX a a g (top1_path_power gen a n2)"
    \<comment> \<open>[f^n2] \<simeq> (gen^n1)^n2 \<simeq> gen^{n1*n2} and [g^n1] \<simeq> (gen^n2)^n1 \<simeq> gen^{n2*n1} = gen^{n1*n2}.\<close>
    have hfn2: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power (top1_path_power gen a n1) a n2)"
      by (rule path_homotopic_path_power[OF assms(1) h1 hf_path hgenn1])
    have hgn1: "top1_path_homotopic_on X TX a a (top1_path_power g a n1)
        (top1_path_power (top1_path_power gen a n2) a n1)"
      by (rule path_homotopic_path_power[OF assms(1) h2 hg_path hgenn2])
    have hmult1: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen a n1) a n2) (top1_path_power gen a (n1 * n2))"
      by (rule path_power_mult[OF assms(1) hgen])
    have hmult2: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen a n2) a n1) (top1_path_power gen a (n2 * n1))"
      by (rule path_power_mult[OF assms(1) hgen])
    have "n1 * n2 = n2 * n1" by simp
    have hfn2_eq: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power gen a (n1 * n2))"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2 hmult1])
    have hgn1_eq: "top1_path_homotopic_on X TX a a (top1_path_power g a n1)
        (top1_path_power gen a (n1 * n2))"
    proof -
      have "top1_path_homotopic_on X TX a a (top1_path_power g a n1)
          (top1_path_power gen a (n2 * n1))"
        by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hgn1 hmult2])
      moreover have "n2 * n1 = n1 * n2" by (rule mult.commute)
      ultimately show ?thesis by simp
    qed
    \<comment> \<open>By symmetry+transitivity: [f^n2] \<simeq> gen^{n1*n2} \<simeq> [g^n1].\<close>
    have hgn1_sym: "top1_path_homotopic_on X TX a a
        (top1_path_power gen a (n1 * n2)) (top1_path_power g a n1)"
      by (rule Lemma_51_1_path_homotopic_sym[OF hgn1_eq])
    have "top1_path_homotopic_on X TX a a (top1_path_power f a n2) (top1_path_power g a n1)"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2_eq hgn1_sym])
    thus ?thesis using hn2_pos by (intro exI[of _ n2] exI[of _ n1]) blast
  next
    \<comment> \<open>Case 2: [f] = gen^n1, [g] = (gen\<inverse>)^n2. Then [f^n2] = gen^{n1*n2} = [(g\<inverse>)^n1].\<close>
    assume h1: "top1_path_homotopic_on X TX a a f (top1_path_power gen a n1)"
       and h2: "top1_path_homotopic_on X TX a a g (top1_path_power (top1_path_reverse gen) a n2)"
    \<comment> \<open>g\<inverse> \<simeq> gen^n2 (reverse of (gen\<inverse>)^n2). Use path_reverse of g.\<close>
    have hfn2: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power (top1_path_power gen a n1) a n2)"
      by (rule path_homotopic_path_power[OF assms(1) h1 hf_path hgenn1])
    have hmult1: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen a n1) a n2) (top1_path_power gen a (n1 * n2))"
      by (rule path_power_mult[OF assms(1) hgen])
    have hfn2_eq: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power gen a (n1 * n2))"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2 hmult1])
    \<comment> \<open>g\<inverse> \<simeq> gen^n2. Path power of g\<inverse>: (g\<inverse>)^n1 \<simeq> (gen^n2)^n1 \<simeq> gen^{n2*n1}.\<close>
    define g' where "g' = top1_path_reverse g"
    have hg'_loop: "top1_is_loop_on X TX a g'"
      unfolding g'_def by (rule top1_path_reverse_is_loop[OF assms(3)])
    have hg'_path: "top1_is_path_on X TX a a g'"
      using hg'_loop unfolding top1_is_loop_on_def by simp
    \<comment> \<open>g \<simeq> (gen\<inverse>)^n2, so g\<inverse> \<simeq> ((gen\<inverse>)^n2)\<inverse> \<simeq> gen^n2.
       But proving ((gen\<inverse>)^n2)\<inverse> \<simeq> gen^n2 is complex. Proof omitted here.\<close>
    have hg'_gen: "top1_path_homotopic_on X TX a a g' (top1_path_power gen a n2)"
    proof -
      define gen_inv where "gen_inv = top1_path_reverse gen"
      have hgi_loop: "top1_is_loop_on X TX a gen_inv"
        unfolding gen_inv_def by (rule top1_path_reverse_is_loop[OF hgen])
      have hgi_n2: "top1_is_path_on X TX a a (top1_path_power gen_inv a n2)"
        by (rule top1_path_power_is_path[OF assms(1) hgi_loop])
      \<comment> \<open>g \<simeq> gen_inv^n2, so g\<inverse> \<simeq> (gen_inv^n2)\<inverse>.\<close>
      have h_rev: "top1_path_homotopic_on X TX a a g' (top1_path_reverse (top1_path_power gen_inv a n2))"
        unfolding g'_def
        by (rule path_homotopic_reverse[OF assms(1) h2[folded gen_inv_def] hg_path hgi_n2])
      \<comment> \<open>(gen_inv^n2)\<inverse> \<simeq> (gen_inv\<inverse>)^n2 = gen^n2.\<close>
      have h_dist: "top1_path_homotopic_on X TX a a
          (top1_path_reverse (top1_path_power gen_inv a n2))
          (top1_path_power (top1_path_reverse gen_inv) a n2)"
        by (rule path_power_reverse[OF assms(1) hgi_loop])
      have "top1_path_reverse gen_inv = gen" unfolding gen_inv_def top1_path_reverse_def by auto
      hence "top1_path_power (top1_path_reverse gen_inv) a n2 = top1_path_power gen a n2" by simp
      thus ?thesis using Lemma_51_1_path_homotopic_trans[OF assms(1) h_rev h_dist] by simp
    qed
    have hg'n1: "top1_path_homotopic_on X TX a a (top1_path_power g' a n1)
        (top1_path_power (top1_path_power gen a n2) a n1)"
      by (rule path_homotopic_path_power[OF assms(1) hg'_gen hg'_path hgenn2])
    have hmult2: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen a n2) a n1) (top1_path_power gen a (n2 * n1))"
      by (rule path_power_mult[OF assms(1) hgen])
    have hg'n1_eq: "top1_path_homotopic_on X TX a a (top1_path_power g' a n1)
        (top1_path_power gen a (n1 * n2))"
    proof -
      have "top1_path_homotopic_on X TX a a (top1_path_power g' a n1)
          (top1_path_power gen a (n2 * n1))"
        by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hg'n1 hmult2])
      moreover have "n2 * n1 = n1 * n2" by (rule mult.commute)
      ultimately show ?thesis by simp
    qed
    have "top1_path_homotopic_on X TX a a (top1_path_power f a n2) (top1_path_power g' a n1)"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2_eq
          Lemma_51_1_path_homotopic_sym[OF hg'n1_eq]])
    thus ?thesis using hn2_pos unfolding g'_def
      by (intro exI[of _ n2] exI[of _ n1]) blast
  next
    \<comment> \<open>Case 3: [f] = (gen\<inverse>)^n1, [g] = gen^n2. Symmetric to case 2.\<close>
    assume h1: "top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_reverse gen) a n1)"
       and h2: "top1_path_homotopic_on X TX a a g (top1_path_power gen a n2)"
    \<comment> \<open>[f^n2] \<simeq> ((gen\<inverse>)^n1)^n2 \<simeq> (gen\<inverse>)^{n1*n2}. [g^n1] \<simeq> gen^{n2*n1}.
       So [f^n2] \<simeq> (gen\<inverse>)^{n1*n2} and [(g\<inverse>)^n1] \<simeq> (gen\<inverse>)^{n2*n1}.
       Thus [f^n2] \<simeq> [(g\<inverse>)^n1].\<close>
    define gen' where "gen' = top1_path_reverse gen"
    have hgen'_loop: "top1_is_loop_on X TX a gen'"
      unfolding gen'_def by (rule top1_path_reverse_is_loop[OF hgen])
    have hgen'n1: "top1_is_path_on X TX a a (top1_path_power gen' a n1)"
      by (rule top1_path_power_is_path[OF assms(1) hgen'_loop])
    have hfn2: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power (top1_path_power gen' a n1) a n2)"
      using path_homotopic_path_power[OF assms(1) h1[folded gen'_def] hf_path hgen'n1] by simp
    have hmult1: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen' a n1) a n2) (top1_path_power gen' a (n1 * n2))"
      by (rule path_power_mult[OF assms(1) hgen'_loop])
    have hfn2_eq: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power gen' a (n1 * n2))"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2 hmult1])
    \<comment> \<open>g\<inverse> \<simeq> (gen)^{-n2} = (gen\<inverse>)^n2 = gen'^n2.\<close>
    define g' where "g' = top1_path_reverse g"
    have hg'_loop: "top1_is_loop_on X TX a g'"
      unfolding g'_def by (rule top1_path_reverse_is_loop[OF assms(3)])
    have hg'_path: "top1_is_path_on X TX a a g'"
      using hg'_loop unfolding top1_is_loop_on_def by simp
    have hg'_gen': "top1_path_homotopic_on X TX a a g' (top1_path_power gen' a n2)"
    proof -
      \<comment> \<open>g \<simeq> gen^n2, so g\<inverse> \<simeq> (gen^n2)\<inverse> \<simeq> (gen\<inverse>)^n2 = gen'^n2.\<close>
      have h_rev: "top1_path_homotopic_on X TX a a g' (top1_path_reverse (top1_path_power gen a n2))"
        unfolding g'_def
        by (rule path_homotopic_reverse[OF assms(1) h2 hg_path hgenn2])
      have h_dist: "top1_path_homotopic_on X TX a a
          (top1_path_reverse (top1_path_power gen a n2))
          (top1_path_power (top1_path_reverse gen) a n2)"
        by (rule path_power_reverse[OF assms(1) hgen])
      show ?thesis using Lemma_51_1_path_homotopic_trans[OF assms(1) h_rev h_dist]
        unfolding gen'_def by simp
    qed
    have hgen'n2: "top1_is_path_on X TX a a (top1_path_power gen' a n2)"
      by (rule top1_path_power_is_path[OF assms(1) hgen'_loop])
    have hg'n1: "top1_path_homotopic_on X TX a a (top1_path_power g' a n1)
        (top1_path_power (top1_path_power gen' a n2) a n1)"
      by (rule path_homotopic_path_power[OF assms(1) hg'_gen' hg'_path hgen'n2])
    have hmult2: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen' a n2) a n1) (top1_path_power gen' a (n2 * n1))"
      by (rule path_power_mult[OF assms(1) hgen'_loop])
    have hg'n1_eq: "top1_path_homotopic_on X TX a a (top1_path_power g' a n1)
        (top1_path_power gen' a (n1 * n2))"
    proof -
      have "top1_path_homotopic_on X TX a a (top1_path_power g' a n1)
          (top1_path_power gen' a (n2 * n1))"
        by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hg'n1 hmult2])
      moreover have "n2 * n1 = n1 * n2" by (rule mult.commute)
      ultimately show ?thesis by simp
    qed
    have "top1_path_homotopic_on X TX a a (top1_path_power f a n2) (top1_path_power g' a n1)"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2_eq
          Lemma_51_1_path_homotopic_sym[OF hg'n1_eq]])
    thus ?thesis using hn2_pos unfolding g'_def
      by (intro exI[of _ n2] exI[of _ n1]) blast
  next
    assume h1: "top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_reverse gen) a n1)"
       and h2: "top1_path_homotopic_on X TX a a g (top1_path_power (top1_path_reverse gen) a n2)"
    \<comment> \<open>Same as case 1 but with gen\<inverse>. [f^n2] \<simeq> (gen\<inverse>^n1)^n2 \<simeq> gen\<inverse>^{n1*n2} \<simeq> (gen\<inverse>^n2)^n1 \<simeq> [g^n1].\<close>
    define gen' where "gen' = top1_path_reverse gen"
    have hgen'_loop: "top1_is_loop_on X TX a gen'"
      unfolding gen'_def by (rule top1_path_reverse_is_loop[OF hgen])
    have hgen'n1: "top1_is_path_on X TX a a (top1_path_power gen' a n1)"
      by (rule top1_path_power_is_path[OF assms(1) hgen'_loop])
    have hgen'n2: "top1_is_path_on X TX a a (top1_path_power gen' a n2)"
      by (rule top1_path_power_is_path[OF assms(1) hgen'_loop])
    have hfn2: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power (top1_path_power gen' a n1) a n2)"
      using path_homotopic_path_power[OF assms(1) h1[folded gen'_def] hf_path hgen'n1] by simp
    have hgn1: "top1_path_homotopic_on X TX a a (top1_path_power g a n1)
        (top1_path_power (top1_path_power gen' a n2) a n1)"
      using path_homotopic_path_power[OF assms(1) h2[folded gen'_def] hg_path hgen'n2] by simp
    have hmult1: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen' a n1) a n2) (top1_path_power gen' a (n1 * n2))"
      by (rule path_power_mult[OF assms(1) hgen'_loop])
    have hmult2: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen' a n2) a n1) (top1_path_power gen' a (n2 * n1))"
      by (rule path_power_mult[OF assms(1) hgen'_loop])
    have hfn2_eq: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power gen' a (n1 * n2))"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2 hmult1])
    have hgn1_eq: "top1_path_homotopic_on X TX a a (top1_path_power g a n1)
        (top1_path_power gen' a (n1 * n2))"
    proof -
      have "top1_path_homotopic_on X TX a a (top1_path_power g a n1)
          (top1_path_power gen' a (n2 * n1))"
        by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hgn1 hmult2])
      moreover have "n2 * n1 = n1 * n2" by (rule mult.commute)
      ultimately show ?thesis by simp
    qed
    have "top1_path_homotopic_on X TX a a (top1_path_power f a n2) (top1_path_power g a n1)"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2_eq
          Lemma_51_1_path_homotopic_sym[OF hgn1_eq]])
    thus ?thesis using hn2_pos by (intro exI[of _ n2] exI[of _ n1]) (by100 blast)
  qed
qed


(** from \<S>63 Theorem 63.2: an arc D in S^2 does not separate S^2.
    Munkres' proof: by contradiction + Theorem 63.1; use that \<pi>_1(S^2) is trivial. **)
text \<open>Helper: R^2 is locally path-connected (every open set has path-connected neighborhoods).\<close>
text \<open>Helper: an open ball in R^2 is path-connected (convex, straight-line paths stay inside).\<close>

text \<open>Helper: non-separation implies path exists between any two points.\<close>
lemma S2_nonsep_path_exists:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "closedin_on top1_S2 top1_S2_topology D"
      and "\<not> top1_separates_on top1_S2 top1_S2_topology D"
      and "a \<in> top1_S2 - D" and "b \<in> top1_S2 - D"
  shows "\<exists>f. top1_is_path_on (top1_S2 - D) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D)) a b f"
proof -
  have hne: "top1_S2 - D \<noteq> {}" using assms(4) by (by100 blast)
  have hpc: "top1_path_connected_on (top1_S2 - D) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D))"
  proof -
    have hconn: "top1_connected_on (top1_S2 - D) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D))"
      using assms(3) unfolding top1_separates_on_def by (by100 blast)
    have hTS2D: "is_topology_on (top1_S2 - D) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D))"
      using hconn unfolding top1_connected_on_def by (by100 blast)
    have hS2D_open: "top1_S2 - D \<in> top1_S2_topology"
      using closedin_complement_openin[OF assms(2)] unfolding openin_on_def by simp
    \<comment> \<open>S^2-D is lpc via: pick b'\<notin>S^2-D, S^2-{b'}\<cong>R^2 lpc, restrict to open S^2-D.\<close>
    have hlocp: "top1_locally_path_connected_on (top1_S2 - D)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D))"
    proof (cases "D = {}")
      case True
      hence hS2D_eq: "top1_S2 - D = top1_S2" by simp
      \<comment> \<open>S^2 is simply connected, hence path-connected, hence connected.
         For lpc: pick any b \<in> S^2, S^2-{b} \<cong> R^2 is lpc and open in S^2.
         S^2 is covered by S^2-{north} and S^2-{south}, both lpc and open.
         Union of open lpc sets that cover = lpc.\<close>
      \<comment> \<open>S^2 is lpc: every point is in S^2-{N} or S^2-{S} (both open, \<cong> R^2, hence lpc).\<close>
      have hS2_lpc: "top1_locally_path_connected_on top1_S2 top1_S2_topology"
        unfolding top1_locally_path_connected_on_def
      proof (intro conjI ballI)
        show "is_topology_on top1_S2 top1_S2_topology"
          using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
      next
        fix x assume hx: "x \<in> top1_S2"
        \<comment> \<open>x \<noteq> north_pole or x \<noteq> south_pole (S^2 has \<ge> 2 points).\<close>
        define south where "south = (0::real, 0::real, -1::real)"
        have hs_S2: "south \<in> top1_S2" unfolding south_def top1_S2_def by simp
        have hn_S2: "north_pole \<in> top1_S2" unfolding north_pole_def top1_S2_def by simp
        have hns: "north_pole \<noteq> south" unfolding north_pole_def south_def by simp
        \<comment> \<open>Choose b = north_pole if x \<noteq> north_pole, else south.\<close>
        define b where "b = (if x \<noteq> north_pole then north_pole else south)"
        have hb_S2: "b \<in> top1_S2" unfolding b_def using hn_S2 hs_S2 by auto
        have hxb: "x \<noteq> b" unfolding b_def using hns by auto
        have hx_in: "x \<in> top1_S2 - {b}" using hx hxb by (by100 blast)
        \<comment> \<open>S^2-{b} is open in S^2 and lpc.\<close>
        have hS2b_open: "top1_S2 - {b} \<in> top1_S2_topology"
        proof -
          have "closedin_on top1_S2 top1_S2_topology {b}"
          proof (rule compact_in_strict_hausdorff_closedin_on[OF top1_S2_is_hausdorff top1_S2_is_topology_on_strict])
            show "{b} \<subseteq> top1_S2" using hb_S2 by simp
            show "top1_compact_on {b} (subspace_topology top1_S2 top1_S2_topology {b})"
              unfolding top1_compact_on_def
            proof (intro conjI allI impI)
              show "is_topology_on {b} (subspace_topology top1_S2 top1_S2_topology {b})"
                by (rule subspace_topology_is_topology_on[OF
                    is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict]])
                  (simp add: hb_S2)
            next
              fix Uc assume hUc: "Uc \<subseteq> subspace_topology top1_S2 top1_S2_topology {b} \<and> {b} \<subseteq> \<Union>Uc"
              then obtain U where hU: "U \<in> Uc" and "b \<in> U" by (by100 blast)
              show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> {b} \<subseteq> \<Union>F"
                apply (rule exI[of _ "{U}"]) using hU \<open>b \<in> U\<close> by auto
            qed
          qed
          thus ?thesis using closedin_complement_openin unfolding openin_on_def by simp
        qed
        obtain h_st where hh_st: "top1_homeomorphism_on (top1_S2 - {b})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
            (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) h_st"
          using S2_minus_point_homeo_R2[OF hb_S2] by blast
        have hS2b_lpc: "top1_locally_path_connected_on (top1_S2 - {b})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))"
          by (rule homeomorphism_preserves_lpc[OF homeomorphism_inverse[OF hh_st] R2_locally_path_connected])
        \<comment> \<open>x is in S^2-{b} which is lpc. So x has lpc neighborhoods.\<close>
        show "top1_locally_path_connected_at top1_S2 top1_S2_topology x"
          unfolding top1_locally_path_connected_at_def
        proof (intro allI impI)
          fix U assume hU: "neighborhood_of x top1_S2 top1_S2_topology U \<and> U \<subseteq> top1_S2"
          hence hUo: "U \<in> top1_S2_topology" and hxU: "x \<in> U" unfolding neighborhood_of_def by auto
          \<comment> \<open>U \<inter> (S^2-{b}) is open in S^2-{b}, contains x.\<close>
          have hU_int: "U \<inter> (top1_S2 - {b}) \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
          proof -
            have "(top1_S2 - {b}) \<inter> U \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
              by (rule subspace_topology_memI[OF hUo])
            moreover have "(top1_S2 - {b}) \<inter> U = U \<inter> (top1_S2 - {b})" by (by100 blast)
            ultimately show ?thesis by simp
          qed
          have hx_int: "x \<in> U \<inter> (top1_S2 - {b})" using hxU hx_in by (by100 blast)
          \<comment> \<open>By S^2-{b} lpc: \<exists> pc V with x \<in> V \<subseteq> U \<inter> (S^2-{b}).\<close>
          have "top1_locally_path_connected_at (top1_S2 - {b})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) x"
            using hS2b_lpc hx_in unfolding top1_locally_path_connected_on_def by (by100 blast)
          hence "\<exists>V. neighborhood_of x (top1_S2 - {b})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) V
              \<and> V \<subseteq> U \<inter> (top1_S2 - {b}) \<and> V \<subseteq> top1_S2 - {b}
              \<and> top1_path_connected_on V (subspace_topology (top1_S2 - {b})
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) V)"
            unfolding top1_locally_path_connected_at_def
            using hU_int hx_int unfolding neighborhood_of_def by (by100 blast)
          then obtain V where hVo: "V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
              and hxV: "x \<in> V" and hVsub: "V \<subseteq> U \<inter> (top1_S2 - {b})" and hVS2b: "V \<subseteq> top1_S2 - {b}"
              and hVpc: "top1_path_connected_on V (subspace_topology (top1_S2 - {b})
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) V)"
            unfolding neighborhood_of_def by (by100 blast)
          \<comment> \<open>V is open in S^2 (open in S^2-{b} which is open in S^2).\<close>
          obtain W where hW: "W \<in> top1_S2_topology" and hV_eq: "V = (top1_S2 - {b}) \<inter> W"
            using hVo unfolding subspace_topology_def by (by100 blast)
          have hV_S2: "V \<in> top1_S2_topology"
          proof -
            have "V = (top1_S2 - {b}) \<inter> W" by (rule hV_eq)
            thus ?thesis using topology_inter2[OF
                is_topology_on_strict_imp[OF assms(1)] hS2b_open hW] hV_eq by simp
          qed
          have hVU: "V \<subseteq> U" using hVsub by (by100 blast)
          have hVS2: "V \<subseteq> top1_S2" using hVS2b by (by100 blast)
          \<comment> \<open>V pc in subspace of S^2 (subspace_topology_trans).\<close>
          have "subspace_topology (top1_S2 - {b})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) V
              = subspace_topology top1_S2 top1_S2_topology V"
            by (rule subspace_topology_trans[OF hVS2b])
          hence hVpc': "top1_path_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
            using hVpc by simp
          show "\<exists>V. neighborhood_of x top1_S2 top1_S2_topology V \<and> V \<subseteq> U \<and> V \<subseteq> top1_S2
               \<and> top1_path_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
            using hV_S2 hxV hVU hVS2 hVpc' unfolding neighborhood_of_def by (by100 blast)
        qed
      qed
      moreover have "subspace_topology top1_S2 top1_S2_topology top1_S2 = top1_S2_topology"
      proof (rule subspace_topology_self_carrier)
        show "\<forall>U\<in>top1_S2_topology. U \<subseteq> top1_S2"
          using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
      qed
      ultimately show ?thesis using hS2D_eq by simp
    next
      case False
      then obtain b' where hb': "b' \<in> D" by (by100 blast)
      have hb'_S2: "b' \<in> top1_S2" using hb' assms(2) unfolding closedin_on_def by (by100 blast)
      obtain h_st where hh_st: "top1_homeomorphism_on (top1_S2 - {b'})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b'}))
          (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) h_st"
        using S2_minus_point_homeo_R2[OF hb'_S2] by blast
      have hS2b_lpc: "top1_locally_path_connected_on (top1_S2 - {b'})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b'}))"
        by (rule homeomorphism_preserves_lpc[OF homeomorphism_inverse[OF hh_st] R2_locally_path_connected])
      have hS2D_sub: "top1_S2 - D \<subseteq> top1_S2 - {b'}" using hb' by (by100 fast)
      have hS2D_open_in_S2b: "top1_S2 - D \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b'})"
      proof -
        have "(top1_S2 - {b'}) \<inter> (top1_S2 - D) = top1_S2 - D" using hS2D_sub by (by100 blast)
        moreover have "(top1_S2 - {b'}) \<inter> (top1_S2 - D) \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b'})"
          by (rule subspace_topology_memI[OF hS2D_open])
        ultimately show ?thesis by simp
      qed
      have "top1_locally_path_connected_on (top1_S2 - D)
          (subspace_topology (top1_S2 - {b'}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b'})) (top1_S2 - D))"
        by (rule open_subset_locally_path_connected[OF hS2b_lpc hS2D_open_in_S2b hS2D_sub])
      moreover have "subspace_topology (top1_S2 - {b'}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b'})) (top1_S2 - D)
          = subspace_topology top1_S2 top1_S2_topology (top1_S2 - D)"
        by (rule subspace_topology_trans[OF hS2D_sub])
      ultimately show ?thesis by simp
    qed
    show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF hTS2D hconn hlocp hne])
  qed
  thus ?thesis using assms(4,5) unfolding top1_path_connected_on_def by (by100 blast)
qed

text \<open>Helper: not connected implies two points with no connecting path.\<close>
lemma not_connected_imp_no_path:
  assumes hT: "is_topology_on X TX"
      and hncn: "\<not> top1_connected_on X TX"
  shows "\<exists>a b. a \<in> X \<and> b \<in> X \<and> \<not> (\<exists>f. top1_is_path_on X TX a b f)"
proof -
  have "\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
    using hncn hT unfolding top1_connected_on_def by (by100 blast)
  then obtain U V where hU: "U \<in> TX" and hV: "V \<in> TX" and hUne: "U \<noteq> {}" and hVne: "V \<noteq> {}"
      and hdisj: "U \<inter> V = {}" and hcover: "U \<union> V = X"
    by blast
  obtain a where ha: "a \<in> U" using hUne by (by100 blast)
  obtain b where hb: "b \<in> V" using hVne by (by100 blast)
  have haX: "a \<in> X" and hbX: "b \<in> X" using ha hb hcover by (by100 blast)+
  have hno_path: "\<not> (\<exists>f. top1_is_path_on X TX a b f)"
  proof
    assume "\<exists>f. top1_is_path_on X TX a b f"
    then obtain f where hf: "top1_is_path_on X TX a b f" by (by100 blast)
    \<comment> \<open>f(I) is connected (continuous image of connected [0,1]).\<close>
    have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
      using hf unfolding top1_is_path_on_def by (by100 blast)
    have hI_conn: "top1_connected_on I_set I_top"
    proof -
      have "connected {0..1::real}" by (rule connected_Icc)
      have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
        by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
      have "connected I_set" using \<open>connected {0..1::real}\<close> hI01 by simp
      thus ?thesis using top1_connected_on_subspace_openI
        unfolding top1_unit_interval_topology_def by (by100 blast)
    qed
    have hI_top: "is_topology_on I_set I_top"
      using hI_conn unfolding top1_connected_on_def by (by100 blast)
    have hfI_conn: "top1_connected_on (f ` I_set) (subspace_topology X TX (f ` I_set))"
      by (rule Theorem_23_5[OF hI_top hT hI_conn hf_cont])
    \<comment> \<open>f(I) meets both U and V.\<close>
    have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by auto
    have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by auto
    have hfa: "f 0 = a" using hf unfolding top1_is_path_on_def by (by100 blast)
    have hfb: "f 1 = b" using hf unfolding top1_is_path_on_def by (by100 blast)
    have hfI_U: "f ` I_set \<inter> U \<noteq> {}" using hfa h0I ha by (by100 blast)
    have hfI_V: "f ` I_set \<inter> V \<noteq> {}" using hfb h1I hb by (by100 blast)
    \<comment> \<open>f(I) \<inter> U and f(I) \<inter> V are open in subspace of f(I), nonempty, disjoint, cover f(I).\<close>
    have hfI_sub: "f ` I_set \<subseteq> X" using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
    have hfIU_open: "f ` I_set \<inter> U \<in> subspace_topology X TX (f ` I_set)"
      by (rule subspace_topology_memI[OF hU])
    have hfIV_open: "f ` I_set \<inter> V \<in> subspace_topology X TX (f ` I_set)"
      by (rule subspace_topology_memI[OF hV])
    have hfI_disj: "(f ` I_set \<inter> U) \<inter> (f ` I_set \<inter> V) = {}" using hdisj by (by100 blast)
    have hfI_cover: "(f ` I_set \<inter> U) \<union> (f ` I_set \<inter> V) = f ` I_set"
      using hfI_sub hcover by (by100 blast)
    \<comment> \<open>This contradicts f(I) being connected.\<close>
    have "\<exists>U' V'. U' \<in> subspace_topology X TX (f ` I_set)
        \<and> V' \<in> subspace_topology X TX (f ` I_set)
        \<and> U' \<noteq> {} \<and> V' \<noteq> {} \<and> U' \<inter> V' = {} \<and> U' \<union> V' = f ` I_set"
      apply (rule exI[of _ "f ` I_set \<inter> U"])
      apply (rule exI[of _ "f ` I_set \<inter> V"])
      apply (intro conjI)
      apply (rule hfIU_open) apply (rule hfIV_open)
      apply (rule hfI_U) apply (rule hfI_V)
      apply (rule hfI_disj) apply (rule hfI_cover)
      done
    thus False using hfI_conn unfolding top1_connected_on_def by (by100 blast)
  qed
  show ?thesis using haX hbX hno_path by (by100 blast)
qed

lemma arc_in_S2_closed:
  assumes "D \<subseteq> top1_S2"
      and "top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D)"
  shows "closedin_on top1_S2 top1_S2_topology D"
proof (rule compact_in_strict_hausdorff_closedin_on[OF top1_S2_is_hausdorff
    top1_S2_is_topology_on_strict assms(1)])
  obtain h where hh: "top1_homeomorphism_on I_set I_top D
      (subspace_topology top1_S2 top1_S2_topology D) h"
    using assms(2) unfolding top1_is_arc_on_def by (by100 blast)
  have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
    by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
  have "compact I_set" unfolding hI01 by (rule compact_Icc)
  have hI_compact: "top1_compact_on I_set I_top"
    unfolding top1_unit_interval_topology_def
    using top1_compact_on_subspace_UNIV_iff_compact[of I_set] \<open>compact I_set\<close> by simp
  have hcont: "top1_continuous_map_on I_set I_top D
      (subspace_topology top1_S2 top1_S2_topology D) h"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hTD: "is_topology_on D (subspace_topology top1_S2 top1_S2_topology D)"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have himg: "h ` I_set = D"
    using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  have "top1_compact_on (h ` I_set) (subspace_topology D
      (subspace_topology top1_S2 top1_S2_topology D) (h ` I_set))"
    by (rule top1_compact_on_continuous_image[OF hI_compact hTD hcont])
  hence "top1_compact_on D (subspace_topology D
      (subspace_topology top1_S2 top1_S2_topology D) D)"
    using himg by simp
  moreover have "subspace_topology D (subspace_topology top1_S2 top1_S2_topology D) D
      = subspace_topology top1_S2 top1_S2_topology D"
    by (rule subspace_topology_self_carrier) (auto simp: subspace_topology_def)
  ultimately show "top1_compact_on D (subspace_topology top1_S2 top1_S2_topology D)" by simp
qed

lemma arc_connected:
  assumes "top1_is_arc_on D TD"
  shows "top1_connected_on D TD"
proof -
  obtain h where hh: "top1_homeomorphism_on I_set I_top D TD h"
    using assms unfolding top1_is_arc_on_def by (by100 blast)
  have hI_conn: "top1_connected_on I_set I_top"
  proof -
    have "connected {0..1::real}" by (rule connected_Icc)
    have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
      by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
    have "connected I_set" using \<open>connected {0..1::real}\<close> hI01 by simp
    have "top1_connected_on I_set (subspace_topology UNIV top1_open_sets I_set)"
      using \<open>connected I_set\<close> top1_connected_on_subspace_openI by (by100 blast)
    thus ?thesis unfolding top1_unit_interval_topology_def by simp
  qed
  have hI_top: "is_topology_on I_set I_top"
    using hI_conn unfolding top1_connected_on_def by (by100 blast)
  have hTD: "is_topology_on D TD"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hcont: "top1_continuous_map_on I_set I_top D TD h"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have himg: "h ` I_set = D"
    using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  have "top1_connected_on (h ` I_set) (subspace_topology D TD (h ` I_set))"
    by (rule Theorem_23_5[OF hI_top hTD hI_conn hcont])
  hence "top1_connected_on D (subspace_topology D TD D)" using himg by simp
  moreover have "subspace_topology D TD D = TD"
  proof -
    have hTD_strict: "is_topology_on_strict D TD"
      using assms unfolding top1_is_arc_on_def by (by100 blast)
    show ?thesis by (rule subspace_topology_self_carrier)
       (use hTD_strict in \<open>unfold is_topology_on_strict_def, by100 blast\<close>)
  qed
  ultimately show ?thesis by simp
qed

lemma arc_split_at_midpoint:
  assumes hT: "is_topology_on_strict X TX"
      and hH: "is_hausdorff_on X TX"
      and hDX: "D \<subseteq> X"
      and hArc: "top1_is_arc_on D (subspace_topology X TX D)"
  shows "\<exists>d D1 D2. d \<in> D \<and> D = D1 \<union> D2 \<and> D1 \<inter> D2 = {d}
      \<and> top1_is_arc_on D1 (subspace_topology X TX D1)
      \<and> top1_is_arc_on D2 (subspace_topology X TX D2)"
proof -
  obtain h where hh: "top1_homeomorphism_on I_set I_top D (subspace_topology X TX D) h"
    using hArc unfolding top1_is_arc_on_def by (by100 blast)
  define d where "d = h (1/2 :: real)"
  define D1 where "D1 = h ` {t \<in> I_set. t \<le> 1/2}"
  define D2 where "D2 = h ` {t \<in> I_set. t \<ge> 1/2}"
  have hd_D: "d \<in> D"
  proof -
    have h12: "(1/2 :: real) \<in> I_set" unfolding top1_unit_interval_def by auto
    have hbij: "bij_betw h I_set D" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    thus ?thesis unfolding d_def using h12 hbij unfolding bij_betw_def by (by100 blast)
  qed
  have hD_union: "D = D1 \<union> D2"
  proof -
    have hbij: "bij_betw h I_set D" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have "I_set = {t \<in> I_set. t \<le> 1/2} \<union> {t \<in> I_set. t \<ge> 1/2}" by auto
    thus ?thesis unfolding D1_def D2_def using hbij unfolding bij_betw_def by (by100 blast)
  qed
  have hD_inter: "D1 \<inter> D2 = {d}"
  proof (rule set_eqI, rule iffI)
    fix x assume hx: "x \<in> D1 \<inter> D2"
    have hxD1: "x \<in> D1" and hxD2: "x \<in> D2" using hx by (by100 blast)+
    obtain s where hs: "s \<in> I_set" "s \<le> 1/2" "h s = x"
      using hxD1 unfolding D1_def by (by100 blast)
    obtain t where ht: "t \<in> I_set" "t \<ge> 1/2" "h t = x"
      using hxD2 unfolding D2_def by (by100 blast)
    have hinj: "inj_on h I_set" using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have "s = t" using hinj hs(1) ht(1) hs(3) ht(3) unfolding inj_on_def by (by100 blast)
    hence hs12: "s = 1/2" using hs(2) ht(2) by (by100 linarith)
    have "x = d" using hs(3) hs12 unfolding d_def by simp
    thus "x \<in> {d}" by simp
  next
    fix x assume "x \<in> {d}"
    hence "x = d" by simp
    have h12: "(1/2::real) \<in> I_set" unfolding top1_unit_interval_def by auto
    have "d \<in> D1" unfolding D1_def d_def using h12 by (by100 blast)
    moreover have "d \<in> D2" unfolding D2_def d_def using h12 by (by100 blast)
    ultimately show "x \<in> D1 \<inter> D2" using \<open>x = d\<close> by (by100 blast)
  qed
  \<comment> \<open>Each half is an arc: [0,1/2] and [1/2,1] are homeomorphic to [0,1], compose with h.\<close>
  have hD1_arc: "top1_is_arc_on D1 (subspace_topology X TX D1)"
  proof -
    \<comment> \<open>g(t) = h(t/2) maps [0,1] onto D1 = h([0,1/2]).\<close>
    define g where "g = (\<lambda>t. h (t / 2))"
    have hg_img: "g ` I_set = D1"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> g ` I_set"
      then obtain t where ht: "t \<in> I_set" "x = g t" by (by100 blast)
      have "t/2 \<in> I_set" and "t/2 \<le> 1/2"
        using ht(1) unfolding top1_unit_interval_def by auto
      thus "x \<in> D1" unfolding D1_def g_def ht(2) using \<open>t/2 \<in> I_set\<close> \<open>t/2 \<le> 1/2\<close> by (by100 blast)
    next
      fix x assume "x \<in> D1"
      then obtain s where hs: "s \<in> I_set" "s \<le> 1/2" "h s = x" unfolding D1_def by (by100 blast)
      have "2*s \<in> I_set" using hs(1) hs(2) unfolding top1_unit_interval_def by auto
      moreover have "g (2*s) = x" unfolding g_def using hs(3) by simp
      ultimately show "x \<in> g ` I_set" by (by100 blast)
    qed
    have hg_inj: "inj_on g I_set"
    proof (rule inj_onI)
      fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set" and "g s = g t"
      hence "h (s/2) = h (t/2)" unfolding g_def by simp
      have "s/2 \<in> I_set" using hs unfolding top1_unit_interval_def by auto
      moreover have "t/2 \<in> I_set" using ht unfolding top1_unit_interval_def by auto
      moreover have hinj: "inj_on h I_set"
        using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      ultimately have "s/2 = t/2" using \<open>h (s/2) = h (t/2)\<close> hinj unfolding inj_on_def by (by100 blast)
      thus "s = t" by simp
    qed
    \<comment> \<open>g = h \<circ> (\<lambda>t. t/2) is continuous [0,1] \<rightarrow> D \<rightarrow> D1.\<close>
    have hg_cont: "top1_continuous_map_on I_set I_top D1 (subspace_topology X TX D1) g"
    proof -
      \<comment> \<open>h is continuous [0,1] \<rightarrow> D (subspace of X).\<close>
      have hh_cont: "top1_continuous_map_on I_set I_top D (subspace_topology X TX D) h"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      \<comment> \<open>t/2 maps [0,1] into [0,1], continuous.\<close>
      have hdiv2_maps: "\<forall>t\<in>I_set. t/2 \<in> I_set"
        unfolding top1_unit_interval_def by auto
      \<comment> \<open>g(t) = h(t/2) maps I_set into D1.\<close>
      have hg_maps: "\<forall>t\<in>I_set. g t \<in> D1"
      proof
        fix t assume ht: "t \<in> I_set"
        have "t/2 \<in> I_set" using hdiv2_maps ht by (by100 blast)
        moreover have "t/2 \<le> 1/2" using ht unfolding top1_unit_interval_def by auto
        ultimately have "t/2 \<in> {s \<in> I_set. s \<le> 1/2}" by (by100 blast)
        thus "g t \<in> D1" unfolding g_def D1_def by (by100 blast)
      qed
      \<comment> \<open>For continuity: preimage of V \<in> subspace X TX D1 under g is in I_top.\<close>
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix t assume "t \<in> I_set" thus "g t \<in> D1" using hg_maps by (by100 blast)
      next
        fix V assume hV: "V \<in> subspace_topology X TX D1"
        \<comment> \<open>V = D1 \<inter> W for W \<in> TX. Since D1 \<subseteq> D, V' = D \<inter> W \<in> subspace X TX D.\<close>
        obtain W where hW: "W \<in> TX" and hV_eq: "V = D1 \<inter> W"
          using hV unfolding subspace_topology_def by (by100 blast)
        have hDW: "D \<inter> W \<in> subspace_topology X TX D" by (rule subspace_topology_memI[OF hW])
        \<comment> \<open>{t \<in> I. h(t/2) \<in> V} = {t \<in> I. h(t/2) \<in> D1 \<inter> W} = {t \<in> I. t/2 \<in> I \<and> t/2 \<le> 1/2 \<and> h(t/2) \<in> W}
           = {t \<in> I. h(t/2) \<in> W} (since t/2 \<le> 1/2 always and h(t/2) \<in> D1 iff h(t/2) \<in> W \<inter> D1).\<close>
        have hpre_eq: "{t \<in> I_set. g t \<in> V} = {t \<in> I_set. h (t/2) \<in> W}"
        proof (rule set_eqI, rule iffI)
          fix t assume "t \<in> {t \<in> I_set. g t \<in> V}"
          hence ht: "t \<in> I_set" and "g t \<in> V" by auto
          thus "t \<in> {t \<in> I_set. h (t/2) \<in> W}" unfolding g_def hV_eq by (by100 blast)
        next
          fix t assume "t \<in> {t \<in> I_set. h (t/2) \<in> W}"
          hence ht: "t \<in> I_set" and "h (t/2) \<in> W" by auto
          have "g t \<in> D1" using hg_maps ht by (by100 blast)
          hence "g t \<in> V" using \<open>h (t/2) \<in> W\<close> unfolding g_def hV_eq by (by100 blast)
          thus "t \<in> {t \<in> I_set. g t \<in> V}" using ht by (by100 blast)
        qed
        \<comment> \<open>{t \<in> I. h(t/2) \<in> W} = {t \<in> I. t/2 \<in> {s \<in> I. h s \<in> W}} (where {s \<in> I. h s \<in> W} \<in> I_top).\<close>
        have hpre_h: "{s \<in> I_set. h s \<in> D \<inter> W} \<in> I_top"
          using hh_cont hDW unfolding top1_continuous_map_on_def by (by100 blast)
        \<comment> \<open>Need: {t \<in> I. t/2 \<in> {s \<in> I. h s \<in> D \<inter> W}} \<in> I_top.\<close>
        \<comment> \<open>This is the preimage of an I_top-open set under t \<mapsto> t/2.\<close>
        \<comment> \<open>{t \<in> I. h(t/2) \<in> W} = {t \<in> I. h(t/2) \<in> D \<inter> W} (since h(t/2) \<in> D always).\<close>
        have hpre_eq2: "{t \<in> I_set. h (t/2) \<in> W} = {t \<in> I_set. h (t/2) \<in> D \<inter> W}"
        proof (rule set_eqI, rule iffI)
          fix t assume "t \<in> {t \<in> I_set. h (t/2) \<in> W}"
          hence ht: "t \<in> I_set" and "h (t/2) \<in> W" by auto
          have "t/2 \<in> I_set" using hdiv2_maps ht by (by100 blast)
          have hbij: "bij_betw h I_set D" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
          have "h (t/2) \<in> D" using \<open>t/2 \<in> I_set\<close> hbij unfolding bij_betw_def by (by100 blast)
          thus "t \<in> {t \<in> I_set. h (t/2) \<in> D \<inter> W}" using ht \<open>h (t/2) \<in> W\<close> by (by100 blast)
        next
          fix t assume "t \<in> {t \<in> I_set. h (t/2) \<in> D \<inter> W}" thus "t \<in> {t \<in> I_set. h (t/2) \<in> W}" by (by100 blast)
        qed
        \<comment> \<open>{t \<in> I. h(t/2) \<in> D\<inter>W} is the preimage of {s \<in> I. h s \<in> D\<inter>W} under t\<mapsto>t/2,
           intersected with I. {s \<in> I. h s \<in> D\<inter>W} \<in> I_top (from h continuous).
           I_top = subspace UNIV top1_open_sets I_set. So {s \<in> I. h s \<in> D\<inter>W} = I \<inter> U0 for U0 open.
           Then {t \<in> I. t/2 \<in> I \<inter> U0} = I \<inter> (\<lambda>t. t/2)^{-1}(U0). Since t\<mapsto>t/2 is continuous,
           (\<lambda>t. t/2)^{-1}(U0) is open. So I \<inter> (\<lambda>t. t/2)^{-1}(U0) \<in> I_top.\<close>
        obtain U0 where hU0: "U0 \<in> top1_open_sets" and hpre_h_eq: "{s \<in> I_set. h s \<in> D \<inter> W} = I_set \<inter> U0"
        proof -
          have hpre_mem: "{s \<in> I_set. h s \<in> D \<inter> W} \<in> I_top" by (rule hpre_h)
          have "{s \<in> I_set. h s \<in> D \<inter> W} \<in> {I_set \<inter> U | U. U \<in> top1_open_sets}"
            using hpre_mem unfolding top1_unit_interval_topology_def subspace_topology_def by simp
          then obtain U0 where "U0 \<in> top1_open_sets" "{s \<in> I_set. h s \<in> D \<inter> W} = I_set \<inter> U0"
            by (by100 blast)
          thus ?thesis using that by auto
        qed
        have "{t \<in> I_set. h (t/2) \<in> D \<inter> W} = {t \<in> I_set. t/2 \<in> I_set \<inter> U0}"
        proof (rule set_eqI, rule iffI)
          fix t assume "t \<in> {t \<in> I_set. h (t/2) \<in> D \<inter> W}"
          hence ht: "t \<in> I_set" and "h (t/2) \<in> D \<inter> W" by auto
          have "t/2 \<in> I_set" using hdiv2_maps ht by (by100 blast)
          moreover have "t/2 \<in> U0" using \<open>h (t/2) \<in> D \<inter> W\<close> \<open>t/2 \<in> I_set\<close> hpre_h_eq by (by100 blast)
          ultimately show "t \<in> {t \<in> I_set. t/2 \<in> I_set \<inter> U0}" using ht by (by100 blast)
        next
          fix t assume "t \<in> {t \<in> I_set. t/2 \<in> I_set \<inter> U0}"
          hence ht: "t \<in> I_set" and "t/2 \<in> I_set \<inter> U0" by auto
          hence "h (t/2) \<in> D \<inter> W" using hpre_h_eq by (by100 blast)
          thus "t \<in> {t \<in> I_set. h (t/2) \<in> D \<inter> W}" using ht by (by100 blast)
        qed
        moreover have "{t \<in> I_set. t/2 \<in> I_set \<inter> U0} = I_set \<inter> ((\<lambda>t. t/2) -` U0)"
          using hdiv2_maps by (by100 blast)
        moreover have "open U0" using hU0 unfolding top1_open_sets_def by (by100 blast)
        moreover have "open ((\<lambda>t::real. t/2) -` U0)"
        proof -
          have "continuous_on UNIV (\<lambda>t::real. t/2)" by (intro continuous_intros) simp
          thus ?thesis using \<open>open U0\<close> by (simp add: continuous_on_open_vimage[OF open_UNIV])
        qed
        moreover have "(\<lambda>t::real. t/2) -` U0 \<in> top1_open_sets"
          using \<open>open ((\<lambda>t::real. t/2) -` U0)\<close> unfolding top1_open_sets_def by (by100 blast)
        ultimately have "{t \<in> I_set. h (t/2) \<in> D \<inter> W} = I_set \<inter> ((\<lambda>t. t/2) -` U0)" by simp
        moreover have "I_set \<inter> ((\<lambda>t. t/2) -` U0) \<in> I_top"
          unfolding top1_unit_interval_topology_def
          by (rule subspace_topology_memI) (rule \<open>(\<lambda>t::real. t/2) -` U0 \<in> top1_open_sets\<close>)
        ultimately have "{t \<in> I_set. h (t/2) \<in> D \<inter> W} \<in> I_top" by simp
        thus "{t \<in> I_set. g t \<in> V} \<in> I_top"
          using hpre_eq hpre_eq2 by simp
      qed
    qed
    have hI_compact: "top1_compact_on I_set I_top"
    proof -
      have "compact {0..1::real}" by (rule compact_Icc)
      have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
        by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
      have "compact I_set" using \<open>compact {0..1::real}\<close> hI01 by simp
      have "top1_compact_on I_set (subspace_topology (UNIV::real set) top1_open_sets I_set)"
        using top1_compact_on_subspace_UNIV_iff_compact[of I_set] \<open>compact I_set\<close> by simp
      thus ?thesis unfolding top1_unit_interval_topology_def by simp
    qed
    have hI_top: "is_topology_on I_set I_top"
      unfolding top1_unit_interval_topology_def
      by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) (by100 simp)
    have hD1_sub: "D1 \<subseteq> X"
      using hDX hD_union unfolding D1_def by (by100 blast)
    have hTD1: "is_topology_on D1 (subspace_topology X TX D1)"
      by (rule subspace_topology_is_topology_on[OF is_topology_on_strict_imp[OF hT] hD1_sub])
    have hD1_haus: "is_hausdorff_on D1 (subspace_topology X TX D1)"
    proof -
      have "is_hausdorff_on X TX" by (rule hH)
      thus ?thesis by (rule hausdorff_subspace[OF _ hD1_sub])
    qed
    have hg_bij: "bij_betw g I_set D1" unfolding bij_betw_def using hg_inj hg_img by (by100 blast)
    have "top1_homeomorphism_on I_set I_top D1 (subspace_topology X TX D1) g"
      by (rule Theorem_26_6[OF hI_top hTD1 hI_compact hD1_haus hg_cont hg_bij])
    moreover have "is_topology_on_strict D1 (subspace_topology X TX D1)"
      by (rule subspace_topology_is_strict[OF hT hD1_sub])
    ultimately show ?thesis unfolding top1_is_arc_on_def by (by100 blast)
  qed
  have hD2_arc: "top1_is_arc_on D2 (subspace_topology X TX D2)"
  proof -
    define g' where "g' = (\<lambda>t. h ((1 + t) / 2))"
    have hg'_img: "g' ` I_set = D2"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> g' ` I_set"
      then obtain t where ht: "t \<in> I_set" "x = g' t" by (by100 blast)
      have "(1+t)/2 \<in> I_set" and "(1+t)/2 \<ge> 1/2"
        using ht(1) unfolding top1_unit_interval_def by auto
      thus "x \<in> D2" unfolding D2_def g'_def ht(2)
        using \<open>(1+t)/2 \<in> I_set\<close> \<open>(1+t)/2 \<ge> 1/2\<close> by (by100 blast)
    next
      fix x assume "x \<in> D2"
      then obtain s where hs: "s \<in> I_set" "s \<ge> 1/2" "h s = x" unfolding D2_def by (by100 blast)
      have "2*s - 1 \<in> I_set" using hs(1) hs(2) unfolding top1_unit_interval_def by auto
      moreover have "g' (2*s - 1) = x" unfolding g'_def using hs(3) by simp
      ultimately show "x \<in> g' ` I_set" by (by100 blast)
    qed
    have hg'_inj: "inj_on g' I_set"
    proof (rule inj_onI)
      fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set" and "g' s = g' t"
      hence "h ((1+s)/2) = h ((1+t)/2)" unfolding g'_def by simp
      have hs2: "(1+s)/2 \<in> I_set" using hs unfolding top1_unit_interval_def by auto
      have ht2: "(1+t)/2 \<in> I_set" using ht unfolding top1_unit_interval_def by auto
      have hinj: "inj_on h I_set"
        using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have "(1+s)/2 = (1+t)/2"
        using hinj hs2 ht2 \<open>h ((1+s)/2) = h ((1+t)/2)\<close> unfolding inj_on_def by (by100 blast)
      thus "s = t" by simp
    qed
    have hD2_sub: "D2 \<subseteq> X" using hDX hD_union unfolding D2_def by (by100 blast)
    have hTD2: "is_topology_on D2 (subspace_topology X TX D2)"
      by (rule subspace_topology_is_topology_on[OF is_topology_on_strict_imp[OF hT] hD2_sub])
    have hD2_haus: "is_hausdorff_on D2 (subspace_topology X TX D2)"
      by (rule hausdorff_subspace[OF hH hD2_sub])
    have hg'_bij: "bij_betw g' I_set D2"
      unfolding bij_betw_def using hg'_inj hg'_img by (by100 blast)
    \<comment> \<open>g' continuity: same argument as for g, with (1+t)/2 instead of t/2.\<close>
    have hg'_cont: "top1_continuous_map_on I_set I_top D2 (subspace_topology X TX D2) g'"
    proof -
      have hh_cont: "top1_continuous_map_on I_set I_top D (subspace_topology X TX D) h"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      have hdiv2_maps: "\<forall>t\<in>I_set. (1+t)/2 \<in> I_set"
        unfolding top1_unit_interval_def by auto
      have hg'_maps: "\<forall>t\<in>I_set. g' t \<in> D2"
      proof
        fix t assume ht: "t \<in> I_set"
        have "(1+t)/2 \<in> I_set" using hdiv2_maps ht by (by100 blast)
        moreover have "(1+t)/2 \<ge> 1/2" using ht unfolding top1_unit_interval_def by auto
        ultimately have "(1+t)/2 \<in> {s \<in> I_set. s \<ge> 1/2}" by (by100 blast)
        thus "g' t \<in> D2" unfolding g'_def D2_def by (by100 blast)
      qed
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix t assume "t \<in> I_set" thus "g' t \<in> D2" using hg'_maps by (by100 blast)
      next
        fix V assume hV: "V \<in> subspace_topology X TX D2"
        obtain W where hW: "W \<in> TX" and hV_eq: "V = D2 \<inter> W"
          using hV unfolding subspace_topology_def by (by100 blast)
        have hDW: "D \<inter> W \<in> subspace_topology X TX D" by (rule subspace_topology_memI[OF hW])
        have hpre_mem: "{s \<in> I_set. h s \<in> D \<inter> W} \<in> I_top"
          using hh_cont hDW unfolding top1_continuous_map_on_def by (by100 blast)
        have "{s \<in> I_set. h s \<in> D \<inter> W} \<in> {I_set \<inter> U | U. U \<in> top1_open_sets}"
          using hpre_mem unfolding top1_unit_interval_topology_def subspace_topology_def by simp
        then obtain U0 where "U0 \<in> top1_open_sets" "{s \<in> I_set. h s \<in> D \<inter> W} = I_set \<inter> U0"
          by (by100 blast)
        have hpre_eq: "{t \<in> I_set. g' t \<in> V} = {t \<in> I_set. h ((1+t)/2) \<in> W}"
        proof (rule set_eqI, rule iffI)
          fix t assume "t \<in> {t \<in> I_set. g' t \<in> V}"
          thus "t \<in> {t \<in> I_set. h ((1+t)/2) \<in> W}" unfolding g'_def hV_eq by (by100 blast)
        next
          fix t assume "t \<in> {t \<in> I_set. h ((1+t)/2) \<in> W}"
          hence ht: "t \<in> I_set" and "h ((1+t)/2) \<in> W" by auto
          have "g' t \<in> D2" using hg'_maps ht by (by100 blast)
          thus "t \<in> {t \<in> I_set. g' t \<in> V}" using ht \<open>h ((1+t)/2) \<in> W\<close>
            unfolding g'_def hV_eq by (by100 blast)
        qed
        have hpre_eq2: "{t \<in> I_set. h ((1+t)/2) \<in> W} = {t \<in> I_set. (1+t)/2 \<in> I_set \<inter> U0}"
        proof (rule set_eqI, rule iffI)
          fix t assume "t \<in> {t \<in> I_set. h ((1+t)/2) \<in> W}"
          hence ht: "t \<in> I_set" and "h ((1+t)/2) \<in> W" by auto
          have ht2: "(1+t)/2 \<in> I_set" using hdiv2_maps ht by (by100 blast)
          have hbij: "bij_betw h I_set D" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
          have "h ((1+t)/2) \<in> D" using ht2 hbij unfolding bij_betw_def by (by100 blast)
          hence "(1+t)/2 \<in> {s \<in> I_set. h s \<in> D \<inter> W}" using ht2 \<open>h ((1+t)/2) \<in> W\<close> by (by100 blast)
          hence "(1+t)/2 \<in> I_set \<inter> U0" using \<open>{s \<in> I_set. h s \<in> D \<inter> W} = I_set \<inter> U0\<close> by (by100 blast)
          thus "t \<in> {t \<in> I_set. (1+t)/2 \<in> I_set \<inter> U0}" using ht by (by100 blast)
        next
          fix t assume "t \<in> {t \<in> I_set. (1+t)/2 \<in> I_set \<inter> U0}"
          hence ht: "t \<in> I_set" and "(1+t)/2 \<in> I_set \<inter> U0" by auto
          hence "h ((1+t)/2) \<in> D \<inter> W"
            using \<open>{s \<in> I_set. h s \<in> D \<inter> W} = I_set \<inter> U0\<close> by (by100 blast)
          thus "t \<in> {t \<in> I_set. h ((1+t)/2) \<in> W}" using ht by (by100 blast)
        qed
        have "{t \<in> I_set. (1+t)/2 \<in> I_set \<inter> U0} = I_set \<inter> ((\<lambda>t. (1+t)/2) -` U0)"
          using hdiv2_maps by (by100 blast)
        moreover have "open U0" using \<open>U0 \<in> top1_open_sets\<close> unfolding top1_open_sets_def by (by100 blast)
        moreover have hopen_pre: "open ((\<lambda>t::real. (1+t)/2) -` U0)"
        proof -
          have "continuous_on UNIV (\<lambda>t::real. (1+t)/2)" by (intro continuous_intros) simp
          thus ?thesis using \<open>open U0\<close> by (simp add: continuous_on_open_vimage[OF open_UNIV])
        qed
        moreover have "(\<lambda>t::real. (1+t)/2) -` U0 \<in> top1_open_sets"
          using hopen_pre unfolding top1_open_sets_def by (by100 blast)
        moreover have "I_set \<inter> ((\<lambda>t. (1+t)/2) -` U0) \<in> I_top"
          unfolding top1_unit_interval_topology_def
          by (rule subspace_topology_memI) (rule \<open>(\<lambda>t::real. (1+t)/2) -` U0 \<in> top1_open_sets\<close>)
        ultimately have "{t \<in> I_set. (1+t)/2 \<in> I_set \<inter> U0} \<in> I_top" by simp
        thus "{t \<in> I_set. g' t \<in> V} \<in> I_top" using hpre_eq hpre_eq2 by simp
      qed
    qed
    have hI_top: "is_topology_on I_set I_top"
      unfolding top1_unit_interval_topology_def
      by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) (by100 simp)
    have hI_compact: "top1_compact_on I_set I_top"
    proof -
      have "compact {0..1::real}" by (rule compact_Icc)
      have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
        by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
      have "compact I_set" using \<open>compact {0..1::real}\<close> hI01 by simp
      have "top1_compact_on I_set (subspace_topology (UNIV::real set) top1_open_sets I_set)"
        using top1_compact_on_subspace_UNIV_iff_compact[of I_set] \<open>compact I_set\<close> by simp
      thus ?thesis unfolding top1_unit_interval_topology_def by simp
    qed
    have "top1_homeomorphism_on I_set I_top D2 (subspace_topology X TX D2) g'"
      by (rule Theorem_26_6[OF hI_top hTD2 hI_compact hD2_haus hg'_cont hg'_bij])
    moreover have "is_topology_on_strict D2 (subspace_topology X TX D2)"
      by (rule subspace_topology_is_strict[OF hT hD2_sub])
    ultimately show ?thesis unfolding top1_is_arc_on_def by (by100 blast)
  qed
  show ?thesis using hd_D hD_union hD_inter hD1_arc hD2_arc by (by100 blast)
qed

(** from \<S>63 Theorem 63.3: general non-separation theorem. **)
theorem Theorem_63_3_general_nonseparation:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "closedin_on top1_S2 top1_S2_topology D1"
  and "closedin_on top1_S2 top1_S2_topology D2"
  and "top1_simply_connected_on (top1_S2 - (D1 \<inter> D2))
         (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2)))"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology D1"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology D2"
  shows "\<not> top1_separates_on top1_S2 top1_S2_topology (D1 \<union> D2)"
proof (rule ccontr)
  assume hnot: "\<not> \<not> top1_separates_on top1_S2 top1_S2_topology (D1 \<union> D2)"
  hence hsep: "top1_separates_on top1_S2 top1_S2_topology (D1 \<union> D2)" by blast
  \<comment> \<open>Munkres 63.3: Take a\<in>A, b\<in>B in different components of S^2-(D1\<union>D2).\<close>
  obtain a b where "a \<in> top1_S2 - (D1 \<union> D2)" "b \<in> top1_S2 - (D1 \<union> D2)"
      and hab_sep: "\<not> (\<exists>f. top1_is_path_on (top1_S2 - (D1 \<union> D2))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<union> D2))) a b f)"
  proof -
    have hTS2D: "is_topology_on (top1_S2 - (D1 \<union> D2))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<union> D2)))"
      by (rule subspace_topology_is_topology_on[OF is_topology_on_strict_imp[OF assms(1)]]) (by100 blast)
    have "\<exists>a b. a \<in> top1_S2 - (D1 \<union> D2) \<and> b \<in> top1_S2 - (D1 \<union> D2) \<and>
        \<not> (\<exists>f. top1_is_path_on (top1_S2 - (D1 \<union> D2))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<union> D2))) a b f)"
      by (rule not_connected_imp_no_path[OF hTS2D hsep[unfolded top1_separates_on_def]])
    thus ?thesis using that by (by100 blast)
  qed
  \<comment> \<open>Since D1 doesn't separate, join a to b in S^2-D1: path \<alpha>.\<close>
  have ha_D1: "a \<in> top1_S2 - D1" using \<open>a \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
  have hb_D1: "b \<in> top1_S2 - D1" using \<open>b \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
  have ha_D2: "a \<in> top1_S2 - D2" using \<open>a \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
  have hb_D2: "b \<in> top1_S2 - D2" using \<open>b \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
  obtain \<alpha> where "top1_is_path_on (top1_S2 - D1)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D1)) a b \<alpha>"
    using S2_nonsep_path_exists[OF assms(1) assms(2) assms(5) ha_D1 hb_D1] by (by100 blast)
  \<comment> \<open>Since D2 doesn't separate, join b to a in S^2-D2: path \<beta>.\<close>
  obtain \<beta> where "top1_is_path_on (top1_S2 - D2)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D2)) b a \<beta>"
    using S2_nonsep_path_exists[OF assms(1) assms(3) assms(6) hb_D2 ha_D2] by (by100 blast)
  \<comment> \<open>The loop f = \<alpha>*\<beta> lies in X=S^2-(D1\<inter>D2). By Theorem 63.1, [f] is nontrivial.
     Setup: X = S^2\(D1\<inter>D2), U = S^2\D1, V = S^2\D2.
     U \<union> V = X, U \<inter> V = S^2\(D1\<union>D2).
     A = path component of a in U\<inter>V, B = rest. Both open (lpc).
     \<alpha>: a\<rightarrow>b in U, \<beta>: b\<rightarrow>a in V. Theorem 63.1: \<alpha>*\<beta> nontrivial in \<pi>_1(X,a).\<close>
  have hf_nontrivial: "\<exists>f. top1_is_loop_on (top1_S2 - (D1 \<inter> D2))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2))) a f
      \<and> \<not> top1_path_homotopic_on (top1_S2 - (D1 \<inter> D2))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2))) a a f
          (top1_constant_path a)"
  proof -
    let ?X = "top1_S2 - (D1 \<inter> D2)"
    let ?TX = "subspace_topology top1_S2 top1_S2_topology ?X"
    let ?U = "top1_S2 - D1" and ?V = "top1_S2 - D2"
    have hTS2: "is_topology_on top1_S2 top1_S2_topology"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hTX: "is_topology_on ?X ?TX"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
    \<comment> \<open>U, V open in X.\<close>
    have hU_open: "openin_on ?X ?TX ?U"
    proof -
      have "closedin_on top1_S2 top1_S2_topology D1" by (rule assms(2))
      hence "top1_S2 - D1 \<in> top1_S2_topology"
        using hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
      have "?U \<subseteq> ?X" by (by100 blast)
      have "?U = ?X \<inter> (top1_S2 - D1)" by (by100 blast)
      hence "?U \<in> ?TX" using \<open>top1_S2 - D1 \<in> top1_S2_topology\<close>
        unfolding subspace_topology_def by (by100 blast)
      thus ?thesis using \<open>?U \<subseteq> ?X\<close> unfolding openin_on_def by (by100 blast)
    qed
    have hV_open: "openin_on ?X ?TX ?V"
    proof -
      have "closedin_on top1_S2 top1_S2_topology D2" by (rule assms(3))
      hence "top1_S2 - D2 \<in> top1_S2_topology"
        using hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
      have "?V \<subseteq> ?X" by (by100 blast)
      have "?V = ?X \<inter> (top1_S2 - D2)" by (by100 blast)
      hence "?V \<in> ?TX" using \<open>top1_S2 - D2 \<in> top1_S2_topology\<close>
        unfolding subspace_topology_def by (by100 blast)
      thus ?thesis using \<open>?V \<subseteq> ?X\<close> unfolding openin_on_def by (by100 blast)
    qed
    have hUV_eq: "?U \<union> ?V = ?X" by (by100 blast)
    \<comment> \<open>Decompose U \<inter> V into path component A of a and rest B.\<close>
    have hUV_inter: "?U \<inter> ?V = top1_S2 - (D1 \<union> D2)" by (by100 blast)
    \<comment> \<open>A = path component of a in U\<inter>V, B = rest.\<close>
    define A where "A = top1_path_component_of_on (?U \<inter> ?V)
        (subspace_topology ?X ?TX (?U \<inter> ?V)) a"
    define B where "B = (?U \<inter> ?V) - A"
    have ha_UV: "a \<in> ?U \<inter> ?V" using \<open>a \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
    have hb_UV: "b \<in> ?U \<inter> ?V" using \<open>b \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
    \<comment> \<open>a \<in> A, b \<notin> A (can't be connected to a), hence b \<in> B.\<close>
    have hTUV: "is_topology_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V))"
      by (rule subspace_topology_is_topology_on[OF hTX]) (by100 blast)
    have ha_A: "a \<in> A" unfolding A_def
      by (rule top1_path_component_of_on_self_mem[OF hTUV ha_UV])
    have hb_B: "b \<in> B"
    proof -
      have "b \<in> ?U \<inter> ?V" by (rule hb_UV)
      moreover have "b \<notin> A"
      proof
        assume "b \<in> A"
        \<comment> \<open>b \<in> A = path_component(a) means b connected to a in U\<inter>V = S^2\(D1\<union>D2).\<close>
        \<comment> \<open>But hab_sep says a,b NOT connected in S^2\(D1\<union>D2). Contradiction.\<close>
        hence "\<exists>f. top1_is_path_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) a b f"
          unfolding A_def top1_path_component_of_on_def top1_in_same_path_component_on_def
          by simp
        moreover have "?U \<inter> ?V = top1_S2 - (D1 \<union> D2)" by (by100 blast)
        moreover have "subspace_topology ?X ?TX (?U \<inter> ?V)
            = subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<union> D2))"
        proof -
          have "?U \<inter> ?V \<subseteq> ?X" by (by100 blast)
          have "subspace_topology ?X ?TX (?U \<inter> ?V)
              = subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)"
            by (rule subspace_topology_trans[OF \<open>?U \<inter> ?V \<subseteq> ?X\<close>])
          thus ?thesis using \<open>?U \<inter> ?V = top1_S2 - (D1 \<union> D2)\<close> by simp
        qed
        ultimately show False using hab_sep by simp
      qed
      ultimately show ?thesis unfolding B_def by (by100 blast)
    qed
    \<comment> \<open>A, B open in X (path components of lpc space are open).\<close>
    \<comment> \<open>A, B open: U\<inter>V is open in S^2, hence lpc. Path components of lpc = open.\<close>
    have hUV_open_S2: "?U \<inter> ?V \<in> top1_S2_topology"
    proof -
      have "top1_S2 - D1 \<in> top1_S2_topology"
        using assms(2) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
      moreover have "top1_S2 - D2 \<in> top1_S2_topology"
        using assms(3) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
      ultimately show ?thesis by (rule topology_inter_open[OF hTS2])
    qed
    have hUV_lpc: "top1_locally_path_connected_on (?U \<inter> ?V)
        (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V))"
    proof -
      have "?U \<inter> ?V \<subseteq> top1_S2" by (by100 blast)
      show ?thesis by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hUV_open_S2 \<open>?U \<inter> ?V \<subseteq> top1_S2\<close>])
    qed
    have hUV_lpc': "top1_locally_path_connected_on (?U \<inter> ?V)
        (subspace_topology ?X ?TX (?U \<inter> ?V))"
    proof -
      have "?U \<inter> ?V \<subseteq> ?X" by (by100 blast)
      have "subspace_topology ?X ?TX (?U \<inter> ?V) = subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)"
        by (rule subspace_topology_trans[OF \<open>?U \<inter> ?V \<subseteq> ?X\<close>])
      thus ?thesis using hUV_lpc by simp
    qed
    have hA_open_UV: "A \<in> subspace_topology ?X ?TX (?U \<inter> ?V)"
      unfolding A_def
      by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTUV hUV_lpc' ha_UV])
    have hA_sub': "A \<subseteq> ?U \<inter> ?V" unfolding A_def
      by (rule top1_path_component_of_on_subset[OF hTUV ha_UV])
    have hA_open: "openin_on ?X ?TX A"
    proof -
      have hU_in_TX: "?U \<in> ?TX" using hU_open unfolding openin_on_def by (by100 blast)
      have hV_in_TX: "?V \<in> ?TX" using hV_open unfolding openin_on_def by (by100 blast)
      have hUV_in_TX: "?U \<inter> ?V \<in> ?TX" by (rule topology_inter_open[OF hTX hU_in_TX hV_in_TX])
      obtain W where "W \<in> ?TX" "A = (?U \<inter> ?V) \<inter> W"
        using hA_open_UV unfolding subspace_topology_def by (by100 blast)
      hence "A \<in> ?TX" using hUV_in_TX by (simp add: topology_inter_open[OF hTX])
      moreover have "A \<subseteq> ?X" using hA_sub' by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by (by100 blast)
    qed
    have hB_open: "openin_on ?X ?TX B"
    proof -
      \<comment> \<open>B = (U\<inter>V)\A. Show B open in subspace U\<inter>V, then lift to X.\<close>
      \<comment> \<open>In U\<inter>V (lpc), each path component is open.
         B = union of path components \<noteq> A. Each open. Union open.\<close>
      have hB_open_UV: "B \<in> subspace_topology ?X ?TX (?U \<inter> ?V)"
      proof -
        \<comment> \<open>(?U\<inter>?V) \ A = B. A open in U\<inter>V. A also closed (complement = union of open path comp).
           So B = (U\<inter>V)\A open in U\<inter>V.\<close>
        \<comment> \<open>Key: \<forall> path component P of U\<inter>V, P is open (lpc).
           B = \<Union>{P \<in> path_components. P \<noteq> A}. Union of opens.\<close>
        have "\<forall>x \<in> ?U \<inter> ?V. top1_path_component_of_on (?U \<inter> ?V)
            (subspace_topology ?X ?TX (?U \<inter> ?V)) x
            \<in> subspace_topology ?X ?TX (?U \<inter> ?V)"
          by (intro ballI top1_path_component_of_on_open_if_locally_path_connected[OF hTUV hUV_lpc'])
        \<comment> \<open>B = \<Union>{path_component(x) | x \<in> U\<inter>V, path_component(x) \<noteq> A}.\<close>
        have "B = \<Union>{top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x
            | x. x \<in> ?U \<inter> ?V \<and> x \<notin> A}"
        proof (rule set_eqI, rule iffI)
          fix y assume "y \<in> B"
          hence "y \<in> ?U \<inter> ?V" "y \<notin> A" unfolding B_def by auto
          have "y \<in> top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) y"
            by (rule top1_path_component_of_on_self_mem[OF hTUV \<open>y \<in> ?U \<inter> ?V\<close>])
          thus "y \<in> \<Union>{top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x
              | x. x \<in> ?U \<inter> ?V \<and> x \<notin> A}"
            using \<open>y \<in> ?U \<inter> ?V\<close> \<open>y \<notin> A\<close> by (by100 blast)
        next
          fix y assume "y \<in> \<Union>{top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x
              | x. x \<in> ?U \<inter> ?V \<and> x \<notin> A}"
          then obtain x where hx: "x \<in> ?U \<inter> ?V" "x \<notin> A"
              and hy: "y \<in> top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x"
            by (by100 blast)
          have "y \<in> ?U \<inter> ?V"
            using top1_path_component_of_on_subset[OF hTUV hx(1)] hy by (by100 blast)
          moreover have "y \<notin> A"
          proof
            assume "y \<in> A"
            \<comment> \<open>y \<in> A = path_comp(a) and y \<in> path_comp(x).
               Path components overlap \<Rightarrow> equal. So path_comp(x) = A. But x \<notin> A.
               x \<in> path_comp(x) = A. Contradiction.\<close>
            hence "top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) a y"
              unfolding A_def top1_path_component_of_on_def by simp
            have "top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x y"
              using hy unfolding top1_path_component_of_on_def by simp
            \<comment> \<open>By symmetry+transitivity: a and x in same path component. So x \<in> A.\<close>
            have "top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) y a"
              by (rule top1_in_same_path_component_on_sym[OF hTUV
                  \<open>top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) a y\<close>])
            have "top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x a"
              by (rule top1_in_same_path_component_on_trans[OF hTUV
                  \<open>top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x y\<close>
                  \<open>top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) y a\<close>])
            hence "top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) a x"
              by (rule top1_in_same_path_component_on_sym[OF hTUV])
            have "x \<in> A" unfolding A_def top1_path_component_of_on_def
              using \<open>top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) a x\<close>
              by simp
            thus False using hx(2) by simp
          qed
          ultimately show "y \<in> B" unfolding B_def by (by100 blast)
        qed
        moreover have "\<forall>P \<in> {top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x
            | x. x \<in> ?U \<inter> ?V \<and> x \<notin> A}.
            P \<in> subspace_topology ?X ?TX (?U \<inter> ?V)"
          using \<open>\<forall>x \<in> ?U \<inter> ?V. top1_path_component_of_on (?U \<inter> ?V)
              (subspace_topology ?X ?TX (?U \<inter> ?V)) x
              \<in> subspace_topology ?X ?TX (?U \<inter> ?V)\<close> by (by100 blast)
        ultimately have "B \<in> subspace_topology ?X ?TX (?U \<inter> ?V)"
        proof -
          have hTUV_top: "is_topology_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V))"
            by (rule hTUV)
          have "{top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x
              | x. x \<in> ?U \<inter> ?V \<and> x \<notin> A} \<subseteq> subspace_topology ?X ?TX (?U \<inter> ?V)"
            using \<open>\<forall>P \<in> _. P \<in> subspace_topology ?X ?TX (?U \<inter> ?V)\<close> by (by100 blast)
          hence "\<Union>{top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x
              | x. x \<in> ?U \<inter> ?V \<and> x \<notin> A} \<in> subspace_topology ?X ?TX (?U \<inter> ?V)"
            using hTUV_top unfolding is_topology_on_def by (by100 blast)
          thus ?thesis
            using \<open>B = \<Union>{top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x
                | x. x \<in> ?U \<inter> ?V \<and> x \<notin> A}\<close> by simp
        qed
        thus ?thesis .
      qed
      \<comment> \<open>B open in U\<inter>V + U\<inter>V open in X \<Rightarrow> B open in X.\<close>
      obtain W where "W \<in> ?TX" "B = (?U \<inter> ?V) \<inter> W"
        using hB_open_UV unfolding subspace_topology_def by (by100 blast)
      have hU_in_TX: "?U \<in> ?TX" using hU_open unfolding openin_on_def by (by100 blast)
      have hV_in_TX: "?V \<in> ?TX" using hV_open unfolding openin_on_def by (by100 blast)
      have hUV_in_TX: "?U \<inter> ?V \<in> ?TX" by (rule topology_inter_open[OF hTX hU_in_TX hV_in_TX])
      have "B \<in> ?TX" using \<open>B = (?U \<inter> ?V) \<inter> W\<close> \<open>W \<in> ?TX\<close> hUV_in_TX
        by (simp add: topology_inter_open[OF hTX])
      moreover have "B \<subseteq> ?X" unfolding B_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by (by100 blast)
    qed
    have hAB_disj: "A \<inter> B = {}" unfolding B_def by (by100 blast)
    have hAB_cover: "A \<union> B = ?U \<inter> ?V" unfolding B_def using hA_sub' by auto
    \<comment> \<open>Lift \<alpha> to path in U (subspace of X), \<beta> to path in V (subspace of X).
       Key: subspace X TX U = subspace S^2 S^2_top U (by transitivity, U \<subseteq> X).\<close>
    have hU_sub_X: "?U \<subseteq> ?X" by (by100 blast)
    have hV_sub_X: "?V \<subseteq> ?X" by (by100 blast)
    have hU_top_eq: "subspace_topology ?X ?TX ?U = subspace_topology top1_S2 top1_S2_topology ?U"
      by (rule subspace_topology_trans[OF hU_sub_X])
    have hV_top_eq: "subspace_topology ?X ?TX ?V = subspace_topology top1_S2 top1_S2_topology ?V"
      by (rule subspace_topology_trans[OF hV_sub_X])
    have h\<alpha>_U: "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a b \<alpha>"
      using \<open>top1_is_path_on (top1_S2 - D1)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D1)) a b \<alpha>\<close>
      hU_top_eq by simp
    have h\<beta>_V: "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) b a \<beta>"
      using \<open>top1_is_path_on (top1_S2 - D2)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D2)) b a \<beta>\<close>
      hV_top_eq by simp
    \<comment> \<open>Apply Theorem 63.1: \<alpha>*\<beta> nontrivial in \<pi>_1(X,a).\<close>
    have "\<not> top1_path_homotopic_on ?X ?TX a a
        (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
    proof (rule Theorem_63_1_loop_nontrivial)
      show "is_topology_on ?X ?TX" by (rule hTX)
      show "openin_on ?X ?TX ?U" by (rule hU_open)
      show "openin_on ?X ?TX ?V" by (rule hV_open)
      show "?U \<union> ?V = ?X" by (rule hUV_eq)
      show "?U \<inter> ?V = A \<union> B" using hAB_cover by simp
      show "A \<inter> B = {}" by (rule hAB_disj)
      show "openin_on ?X ?TX A" by (rule hA_open)
      show "openin_on ?X ?TX B" by (rule hB_open)
      show "a \<in> A" by (rule ha_A)
      show "b \<in> B" by (rule hb_B)
      show "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a b \<alpha>" by (rule h\<alpha>_U)
      show "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) b a \<beta>" by (rule h\<beta>_V)
    qed
    moreover have "top1_is_loop_on ?X ?TX a (top1_path_product \<alpha> \<beta>)"
    proof -
      \<comment> \<open>\<alpha> path in U (\<subseteq> X) \<Rightarrow> \<alpha> path in X. \<beta> path in V (\<subseteq> X) \<Rightarrow> \<beta> path in X.\<close>
      have hTX_strict: "is_topology_on_strict ?X ?TX"
        by (rule subspace_topology_is_strict[OF assms(1)]) (by100 blast)
      have h\<alpha>_X: "top1_is_path_on ?X ?TX a b \<alpha>"
        by (rule path_in_subspace_imp_path_in_ambient[OF hTX_strict _ h\<alpha>_U]) (by100 blast)
      have h\<beta>_X: "top1_is_path_on ?X ?TX b a \<beta>"
        by (rule path_in_subspace_imp_path_in_ambient[OF hTX_strict _ h\<beta>_V]) (by100 blast)
      have "top1_is_path_on ?X ?TX a a (top1_path_product \<alpha> \<beta>)"
        by (rule top1_path_product_is_path[OF hTX h\<alpha>_X h\<beta>_X])
      thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>But S^2-(D1\<inter>D2) is simply connected by assumption. Contradiction.\<close>
  have ha_mem: "a \<in> top1_S2 - (D1 \<inter> D2)"
    using \<open>a \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
  show False using hf_nontrivial assms(4) ha_mem
    unfolding top1_simply_connected_on_def by (by100 blast)
qed


\<comment> \<open>Munkres' joining lemma (used in second proof of 63.2):
   If D = D1 \<union> D2 with D1 \<inter> D2 = {d}, and a,b can be joined by paths in
   S^2-D1 and S^2-D2, then they can be joined by a path in S^2-D.
   Proof: if not, apply Theorem 63.1 to X = S^2-{d}, U = S^2-D1, V = S^2-D2.
   U \<inter> V = S^2-D contains a,b (disconnected). Let A = path-component of a in U\<inter>V.
   B = rest. Then \<alpha>*\<beta> is nontrivial in \<pi>_1(S^2-{d}). But S^2-{d} simply connected.\<close>
lemma arc_joining_lemma:
  assumes hT: "is_topology_on_strict top1_S2 top1_S2_topology"
      and hD1_sub: "D1 \<subseteq> top1_S2" and hD2_sub: "D2 \<subseteq> top1_S2"
      and hD1_closed: "closedin_on top1_S2 top1_S2_topology D1"
      and hD2_closed: "closedin_on top1_S2 top1_S2_topology D2"
      and hD_inter: "D1 \<inter> D2 = {d}"
      and hd_S2: "d \<in> top1_S2"
      and hab: "a \<in> top1_S2 - (D1 \<union> D2)" "b \<in> top1_S2 - (D1 \<union> D2)"
      and hab_D1: "\<exists>f. top1_is_path_on (top1_S2 - D1)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D1)) a b f"
      and hab_D2: "\<exists>f. top1_is_path_on (top1_S2 - D2)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D2)) a b f"
  shows "\<exists>f. top1_is_path_on (top1_S2 - (D1 \<union> D2))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<union> D2))) a b f"
proof (rule ccontr)
  assume hnot: "\<not> ?thesis"
  let ?X = "top1_S2 - {d}"
  let ?TX = "subspace_topology top1_S2 top1_S2_topology ?X"
  let ?U = "top1_S2 - D1" and ?V = "top1_S2 - D2"
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using hT unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>U, V open in S^2 (complements of closed sets).\<close>
  have hU_open: "?U \<in> top1_S2_topology"
    using hD1_closed hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
  have hV_open: "?V \<in> top1_S2_topology"
    using hD2_closed hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
  \<comment> \<open>X = U \<union> V, U \<inter> V = S^2 - D.\<close>
  have hUV: "?U \<union> ?V = ?X" using hD_inter by (by100 blast)
  have hUV_inter: "?U \<inter> ?V = top1_S2 - (D1 \<union> D2)" by (by100 blast)
  \<comment> \<open>a, b \<in> U \<inter> V but not path-connected in U \<inter> V.\<close>
  have hab_UV: "a \<in> ?U \<inter> ?V" "b \<in> ?U \<inter> ?V"
    using hab hD_inter by auto
  \<comment> \<open>U \<inter> V is open in S^2 hence lpc. Components = path components.\<close>
  have hUV_open: "?U \<inter> ?V \<in> top1_S2_topology"
    by (rule topology_inter_open[OF hTS2 hU_open hV_open])
  have hlpc: "top1_locally_path_connected_on (?U \<inter> ?V)
      (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V))"
    by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hUV_open]) (by100 blast)
  \<comment> \<open>Let A = path-component of a in U \<inter> V. B = rest of U \<inter> V.\<close>
  \<comment> \<open>A and B are open (components of lpc space). a \<in> A, b \<in> B.\<close>
  \<comment> \<open>A \<union> B = U \<inter> V, A \<inter> B = {}.\<close>
  \<comment> \<open>Get paths \<alpha>: a \<rightarrow> b in U, \<beta>: b \<rightarrow> a in V.\<close>
  \<comment> \<open>By Theorem 63.1(a): \<alpha>*\<beta> nontrivial in \<pi>_1(X, a).\<close>
  \<comment> \<open>But X = S^2-{d} simply connected. Contradiction.\<close>
  \<comment> \<open>Step 1: A = path-component of a, B = rest.\<close>
  define PC_a :: "(real \<times> real \<times> real) set" where "PC_a = top1_path_component_of_on (?U \<inter> ?V)
      (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)) a"
  define Rest :: "(real \<times> real \<times> real) set" where "Rest = (?U \<inter> ?V) - PC_a"
  have ha_UV: "a \<in> ?U \<inter> ?V" using hab hD_inter by auto
  have hb_UV: "b \<in> ?U \<inter> ?V" using hab hD_inter by auto
  have hT_UV: "is_topology_on (?U \<inter> ?V)
      (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V))"
    by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
  have ha_PC: "a \<in> PC_a"
  proof -
    have "top1_in_same_path_component_on (?U \<inter> ?V)
        (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)) a a"
      unfolding top1_in_same_path_component_on_def
      using top1_constant_path_is_path[OF hT_UV ha_UV] by (by100 blast)
    thus ?thesis unfolding PC_a_def top1_path_component_of_on_def by (by100 blast)
  qed
  have hb_Rest: "b \<in> Rest"
  proof -
    have "\<not> (\<exists>f. top1_is_path_on (?U \<inter> ?V) (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)) a b f)"
      using hnot hUV_inter by simp
    hence "b \<notin> PC_a" unfolding PC_a_def top1_path_component_of_on_def
        top1_in_same_path_component_on_def by (by100 blast)
    thus ?thesis unfolding Rest_def using hb_UV by (by100 blast)
  qed
  have hPC_sub: "PC_a \<subseteq> ?U \<inter> ?V"
  proof
    fix y assume "y \<in> PC_a"
    hence "\<exists>f. top1_is_path_on (?U \<inter> ?V)
        (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)) a y f"
      unfolding PC_a_def top1_path_component_of_on_def top1_in_same_path_component_on_def
      by simp
    then obtain f where "top1_is_path_on (?U \<inter> ?V)
        (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)) a y f" by blast
    hence "f 1 = y" "f 1 \<in> ?U \<inter> ?V"
      unfolding top1_is_path_on_def top1_continuous_map_on_def
        top1_unit_interval_def by auto
    thus "y \<in> ?U \<inter> ?V" by simp
  qed
  have hPC_open_UV: "PC_a \<in> subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)"
    unfolding PC_a_def
    by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hT_UV hlpc ha_UV])
  have hUV_open_X: "openin_on ?X ?TX (?U \<inter> ?V)"
  proof -
    have "?U \<inter> ?V \<subseteq> ?X" using hD_inter by (by100 blast)
    have "?U \<inter> ?V = ?X \<inter> (?U \<inter> ?V)" using hD_inter by (by100 blast)
    hence "?U \<inter> ?V \<in> ?TX" using hUV_open unfolding subspace_topology_def by (by100 blast)
    thus ?thesis using \<open>?U \<inter> ?V \<subseteq> ?X\<close> unfolding openin_on_def by (by100 blast)
  qed
  have hPC_open: "openin_on ?X ?TX PC_a"
  proof -
    \<comment> \<open>PC_a open in U\<inter>V. U\<inter>V open in X. Open-in-open = open.\<close>
    have hPC_open_in_UV: "openin_on (?U \<inter> ?V) (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)) PC_a"
      using hPC_open_UV hPC_sub unfolding openin_on_def by (by100 blast)
    \<comment> \<open>Transfer: subspace of S^2 restricted to U\<inter>V = subspace of X restricted to U\<inter>V.\<close>
    have hUV_sub_X: "?U \<inter> ?V \<subseteq> ?X" using hD_inter by (by100 blast)
    \<comment> \<open>PC_a open in U\<inter>V (S^2-sub). Transfer to X.\<close>
    have "PC_a \<in> ?TX"
    proof -
      have "PC_a \<in> subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)" by (rule hPC_open_UV)
      then obtain W where hW_mem: "W \<in> top1_S2_topology" and hPC_W: "PC_a = (?U \<inter> ?V) \<inter> W"
        unfolding subspace_topology_def by (by100 blast)
      have "(?U \<inter> ?V) \<inter> W \<in> top1_S2_topology"
        by (rule topology_inter_open[OF hTS2 hUV_open hW_mem])
      have "PC_a = ?X \<inter> ((?U \<inter> ?V) \<inter> W)"
        using hPC_W hPC_sub hUV_sub_X by (by100 blast)
      thus ?thesis using \<open>(?U \<inter> ?V) \<inter> W \<in> top1_S2_topology\<close>
        unfolding subspace_topology_def by (by100 blast)
    qed
    thus ?thesis using hPC_sub hUV_sub_X unfolding openin_on_def by (by100 blast)
  qed
  have hRest_open: "openin_on ?X ?TX Rest"
  proof -
    have hRest_sub: "Rest \<subseteq> ?U \<inter> ?V" unfolding Rest_def by (by100 blast)
    have hUV_sub_X: "?U \<inter> ?V \<subseteq> ?X" using hD_inter by (by100 blast)
    have hRest_open_UV: "Rest \<in> subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)"
    proof -
      have "(?U \<inter> ?V) - PC_a \<in> subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)"
        unfolding PC_a_def
        by (rule top1_path_component_of_on_complement_open_if_locally_path_connected[OF hT_UV hlpc ha_UV])
      thus ?thesis unfolding Rest_def by simp
    qed
    obtain W0 where hW0: "W0 \<in> top1_S2_topology" "Rest = (?U \<inter> ?V) \<inter> W0"
    proof -
      have "Rest \<in> subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)"
        using hRest_open_UV by (by100 simp)
      then obtain W' where hW': "W' \<in> top1_S2_topology" "Rest = (?U \<inter> ?V) \<inter> W'"
      proof -
        assume h: "\<And>W'. \<lbrakk>W' \<in> top1_S2_topology; Rest = (?U \<inter> ?V) \<inter> W'\<rbrakk> \<Longrightarrow> thesis"
        from \<open>Rest \<in> subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)\<close>
        obtain W where "W \<in> top1_S2_topology" "Rest = (?U \<inter> ?V) \<inter> W"
          unfolding subspace_topology_def by blast
        thus thesis by (rule h)
      qed
      show ?thesis by (rule that[OF hW'])
    qed
    have "Rest = (?U \<inter> ?V) \<inter> W0"
      using hW0 hRest_sub by (by100 blast)
    have "(?U \<inter> ?V) \<inter> W0 \<in> top1_S2_topology"
      by (rule topology_inter_open[OF hTS2 hUV_open \<open>W0 \<in> top1_S2_topology\<close>])
    have "Rest \<subseteq> ?X" using hRest_sub hUV_sub_X by (by100 blast)
    have "Rest = ?X \<inter> ((?U \<inter> ?V) \<inter> W0)"
      using \<open>Rest = (?U \<inter> ?V) \<inter> W0\<close> \<open>Rest \<subseteq> ?X\<close> by (by100 blast)
    hence "Rest \<in> ?TX" using \<open>(?U \<inter> ?V) \<inter> W0 \<in> top1_S2_topology\<close>
      unfolding subspace_topology_def by (by100 blast)
    thus ?thesis using hRest_sub hUV_sub_X unfolding openin_on_def by (by100 blast)
  qed
  have hPCR_cover: "PC_a \<union> Rest = ?U \<inter> ?V"
    unfolding Rest_def using hPC_sub by (by100 blast)
  have hPCR_disj: "PC_a \<inter> Rest = {}" unfolding Rest_def by (by100 blast)
  \<comment> \<open>Step 2: Get paths \<alpha> and \<beta>.\<close>
  \<comment> \<open>Step 2: Get paths \<alpha> and \<beta>. Need them with subspace_topology X TX U.\<close>
  have hU_sub_X: "?U \<subseteq> ?X" using hD_inter by (by100 blast)
  have hV_sub_X: "?V \<subseteq> ?X" using hD_inter by (by100 blast)
  have hTU_eq: "subspace_topology ?X ?TX ?U = subspace_topology top1_S2 top1_S2_topology ?U"
    by (rule subspace_topology_trans[OF hU_sub_X])
  have hTV_eq: "subspace_topology ?X ?TX ?V = subspace_topology top1_S2 top1_S2_topology ?V"
    by (rule subspace_topology_trans[OF hV_sub_X])
  obtain \<alpha> where h\<alpha>: "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a b \<alpha>"
  proof -
    obtain f where "top1_is_path_on ?U (subspace_topology top1_S2 top1_S2_topology ?U) a b f"
      using hab_D1 by blast
    hence "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a b f" using hTU_eq by simp
    thus ?thesis using that by blast
  qed
  obtain \<beta> where h\<beta>: "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) b a \<beta>"
  proof -
    obtain f where hf: "top1_is_path_on ?V (subspace_topology top1_S2 top1_S2_topology ?V) a b f"
      using hab_D2 by blast
    \<comment> \<open>Reverse: path b \<rightarrow> a from path a \<rightarrow> b.\<close>
    have "top1_is_path_on ?V (subspace_topology top1_S2 top1_S2_topology ?V) b a (top1_path_reverse f)"
      by (rule top1_path_reverse_is_path[OF hf])
    hence "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) b a (top1_path_reverse f)"
      using hTV_eq by simp
    thus ?thesis using that by blast
  qed
  \<comment> \<open>Step 3: Apply Theorem 63.1(a).\<close>
  have hX_TX: "is_topology_on ?X ?TX"
    by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
  have hU_open_X: "openin_on ?X ?TX ?U"
  proof -
    have "?U \<subseteq> ?X" using hD_inter by (by100 blast)
    have "?U = ?X \<inter> ?U" using hD_inter by (by100 blast)
    hence "?U \<in> ?TX" using hU_open unfolding subspace_topology_def by (by100 blast)
    thus ?thesis using \<open>?U \<subseteq> ?X\<close> unfolding openin_on_def by (by100 blast)
  qed
  have hV_open_X: "openin_on ?X ?TX ?V"
  proof -
    have "?V \<subseteq> ?X" using hD_inter by (by100 blast)
    have "?V = ?X \<inter> ?V" using hD_inter by (by100 blast)
    hence "?V \<in> ?TX" using hV_open unfolding subspace_topology_def by (by100 blast)
    thus ?thesis using \<open>?V \<subseteq> ?X\<close> unfolding openin_on_def by (by100 blast)
  qed
  have hnontrivial: "\<not> top1_path_homotopic_on ?X ?TX a a
      (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
  proof (rule Theorem_63_1_loop_nontrivial)
    show "is_topology_on ?X ?TX" by (rule hX_TX)
    show "openin_on ?X ?TX ?U" by (rule hU_open_X)
    show "openin_on ?X ?TX ?V" by (rule hV_open_X)
    show "?U \<union> ?V = ?X" by (rule hUV)
    show "?U \<inter> ?V = PC_a \<union> Rest" using hPCR_cover by simp
    show "PC_a \<inter> Rest = {}" by (rule hPCR_disj)
    show "openin_on ?X ?TX PC_a" by (rule hPC_open)
    show "openin_on ?X ?TX Rest" by (rule hRest_open)
    show "a \<in> PC_a" by (rule ha_PC)
    show "b \<in> Rest" by (rule hb_Rest)
    show "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a b \<alpha>" by (rule h\<alpha>)
    show "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) b a \<beta>" by (rule h\<beta>)
  qed
  \<comment> \<open>Step 4: But X = S^2-{d} simply connected.\<close>
  have hsc: "top1_simply_connected_on ?X ?TX"
    by (rule S2_minus_point_simply_connected[OF hd_S2])
  have "top1_path_homotopic_on ?X ?TX a a
      (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
  proof -
    have ha_X: "a \<in> ?X" using hab hD_inter by (by100 blast)
    have hab_loop: "top1_is_loop_on ?X ?TX a (top1_path_product \<alpha> \<beta>)"
    proof -
      have hTX_strict: "is_topology_on_strict ?X ?TX"
        by (rule subspace_topology_is_strict[OF hT]) (by100 blast)
      have h\<alpha>_X: "top1_is_path_on ?X ?TX a b \<alpha>"
        by (rule path_in_subspace_imp_path_in_ambient[OF hTX_strict hU_sub_X h\<alpha>])
      have h\<beta>_X: "top1_is_path_on ?X ?TX b a \<beta>"
        by (rule path_in_subspace_imp_path_in_ambient[OF hTX_strict hV_sub_X h\<beta>])
      have hprod: "top1_is_path_on ?X ?TX a a (top1_path_product \<alpha> \<beta>)"
        by (rule top1_path_product_is_path[OF hX_TX h\<alpha>_X h\<beta>_X])
      thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
    qed
    show ?thesis using hsc ha_X hab_loop
      unfolding top1_simply_connected_on_def by (by100 blast)
  qed
  thus False using \<open>\<not> top1_path_homotopic_on ?X ?TX a a _ _\<close> by contradiction
qed

theorem Theorem_63_2_arc_no_separation:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "D \<subseteq> top1_S2"
  and "top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D)"
  shows "\<not> top1_separates_on top1_S2 top1_S2_topology D"
proof -
  \<comment> \<open>Munkres 63.2 SECOND proof (bisection + Theorem 63.3).
     Assume D separates. Split D = D1 \<union> D2 at midpoint d.
     By Theorem 63.3 contrapositive: since D separates and S^2\{d} simply connected,
     at least one of D1, D2 separates (assuming neither does → D doesn't).
     Repeat bisection. Get nested arcs D \<supset> D1 \<supset> D2 \<supset> ..., each separating,
     shrinking to a single point x. But S^2\{x} \<cong> R^2, hence a,b connected there.
     Path avoids h(x), hence avoids h(I_n) for large n. Contradiction.\<close>
  show ?thesis
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence hsep: "top1_separates_on top1_S2 top1_S2_topology D" by simp
    \<comment> \<open>Split D = D1 \<union> D2 at midpoint.\<close>
    obtain d D1 D2 where hd: "d \<in> D" and hD: "D = D1 \<union> D2" and hD12: "D1 \<inter> D2 = {d}"
        and hD1_arc: "top1_is_arc_on D1 (subspace_topology top1_S2 top1_S2_topology D1)"
        and hD2_arc: "top1_is_arc_on D2 (subspace_topology top1_S2 top1_S2_topology D2)"
      using arc_split_at_midpoint[OF assms(1) top1_S2_is_hausdorff assms(2) assms(3)] by (by100 blast)
    have hd_S2: "d \<in> top1_S2" using hd assms(2) by (by100 blast)
    \<comment> \<open>D1, D2 are closed in S^2 (compact subsets of Hausdorff).\<close>
    have hD1_sub: "D1 \<subseteq> top1_S2" using assms(2) hD by (by100 blast)
    have hD2_sub: "D2 \<subseteq> top1_S2" using assms(2) hD by (by100 blast)
    have hD1_closed: "closedin_on top1_S2 top1_S2_topology D1"
      by (rule arc_in_S2_closed[OF hD1_sub hD1_arc])
    have hD2_closed: "closedin_on top1_S2 top1_S2_topology D2"
      by (rule arc_in_S2_closed[OF hD2_sub hD2_arc])
    \<comment> \<open>S^2\{d} simply connected.\<close>
    have hsc: "top1_simply_connected_on (top1_S2 - {d})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {d}))"
      by (rule S2_minus_point_simply_connected[OF hd_S2])
    \<comment> \<open>D1 \<inter> D2 = {d} so S^2\(D1\<inter>D2) = S^2\{d} simply connected.\<close>
    have "top1_S2 - (D1 \<inter> D2) = top1_S2 - {d}" using hD12 by simp
    hence hsc': "top1_simply_connected_on (top1_S2 - (D1 \<inter> D2))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2)))"
      using hsc by simp
    \<comment> \<open>By Theorem 63.3 contrapositive: since D = D1\<union>D2 separates,
       at least one of D1, D2 must separate S^2.\<close>
    have "top1_separates_on top1_S2 top1_S2_topology D1
        \<or> top1_separates_on top1_S2 top1_S2_topology D2"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence h1: "\<not> top1_separates_on top1_S2 top1_S2_topology D1"
          and h2: "\<not> top1_separates_on top1_S2 top1_S2_topology D2" by auto
      have "\<not> top1_separates_on top1_S2 top1_S2_topology (D1 \<union> D2)"
      proof (rule Theorem_63_3_general_nonseparation)
        show "is_topology_on_strict top1_S2 top1_S2_topology" by (rule assms(1))
        show "closedin_on top1_S2 top1_S2_topology D1" by (rule hD1_closed)
        show "closedin_on top1_S2 top1_S2_topology D2" by (rule hD2_closed)
        show "top1_simply_connected_on (top1_S2 - (D1 \<inter> D2))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2)))"
          by (rule hsc')
        show "\<not> top1_separates_on top1_S2 top1_S2_topology D1" by (rule h1)
        show "\<not> top1_separates_on top1_S2 top1_S2_topology D2" by (rule h2)
      qed
      thus False using hsep hD by simp
    qed
    \<comment> \<open>BY JOINING LEMMA CONTRAPOSITIVE: at least one of D1, D2 separates a' from b'.
       The joining lemma says: if a' joinable to b' in S^2-D1 AND S^2-D2, then in S^2-D.
       Contrapositive: if NOT joinable in S^2-D, then NOT joinable in S^2-D1 OR S^2-D2.\<close>

    \<comment> \<open>Get specific a', b' that D separates.\<close>
    obtain a' b' where ha': "a' \<in> top1_S2 - D" and hb': "b' \<in> top1_S2 - D"
        and hab'_sep: "\<not> (\<exists>f. top1_is_path_on (top1_S2 - D)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D)) a' b' f)"
    proof -
      have hTS2D: "is_topology_on (top1_S2 - D)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D))"
        by (rule subspace_topology_is_topology_on[OF
            is_topology_on_strict_imp[OF assms(1)]]) (by100 blast)
      have "\<exists>a b. a \<in> top1_S2 - D \<and> b \<in> top1_S2 - D \<and> \<not> (\<exists>f. top1_is_path_on
          (top1_S2 - D) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D)) a b f)"
        by (rule not_connected_imp_no_path[OF hTS2D hsep[unfolded top1_separates_on_def]])
      thus ?thesis using that by (by100 blast)
    qed
    have ha'_S2: "a' \<in> top1_S2" using ha' by (by100 blast)
    have hb'_S2: "b' \<in> top1_S2" using hb' by (by100 blast)

    \<comment> \<open>Contrapositive of joining lemma: at least one half separates a' from b'.\<close>
    have hab'_D: "a' \<in> top1_S2 - (D1 \<union> D2)" "b' \<in> top1_S2 - (D1 \<union> D2)"
      using ha' hb' hD by auto
    have "\<not> (\<exists>f. top1_is_path_on (top1_S2 - D1)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D1)) a' b' f)
        \<or> \<not> (\<exists>f. top1_is_path_on (top1_S2 - D2)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D2)) a' b' f)"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence hab_D1: "\<exists>f. top1_is_path_on (top1_S2 - D1)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D1)) a' b' f"
        and hab_D2: "\<exists>f. top1_is_path_on (top1_S2 - D2)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D2)) a' b' f" by auto
      have "\<exists>f. top1_is_path_on (top1_S2 - (D1 \<union> D2))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<union> D2))) a' b' f"
        by (rule arc_joining_lemma[OF assms(1) hD1_sub hD2_sub hD1_closed hD2_closed
            hD12 hd_S2 hab'_D hab_D1 hab_D2])
      hence "\<exists>f. top1_is_path_on (top1_S2 - D)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D)) a' b' f"
        using hD by simp
      thus False using hab'_sep by contradiction
    qed

    \<comment> \<open>BISECTION ITERATION + LIMIT ARGUMENT:
       At each step, pick the half that separates a' from b'. Both halves are arcs
       (from arc_split_at_midpoint). Repeat to get nested arcs D \<supset> D^1 \<supset> D^2 \<supset> ...,
       each separating a' from b', with parametric length \<rightarrow> 0.
       The homeomorphism h0: [0,1] \<rightarrow> D maps nested sub-intervals to nested sub-arcs.
       By Cantor's intersection theorem: the intervals converge to a single point x.
       S^2-{h0(x)} is path-connected (simply connected). Path \<gamma>: a'\<rightarrow>b' in S^2-{h0(x)}.
       \<gamma>(I) compact, disjoint from {h0(x)} \<Rightarrow> dist(\<gamma>(I), h0(x)) > 0.
       h0 uniformly continuous on compact [0,1] \<Rightarrow> h0(sub-interval_n) \<subseteq> B(h0(x), \<epsilon>) for large n.
       So \<gamma> is a path from a' to b' in S^2 - D^n (since \<gamma>(I) \<inter> D^n = {}).
       But a', b' \<in> S^2 - D \<subseteq> S^2 - D^n. Contradiction with D^n separating a' from b'.\<close>
    \<comment> \<open>Step 1: Get homeomorphism h0: [0,1] \<rightarrow> D (standard topology).\<close>
    obtain h0 where hh0: "top1_homeomorphism_on I_set I_top D
        (subspace_topology top1_S2 top1_S2_topology D) h0"
      using assms(3) unfolding top1_is_arc_on_def by (by100 blast)
    have hh0_bij: "bij_betw h0 I_set D"
      using hh0 unfolding top1_homeomorphism_on_def by (by100 blast)
    have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
      by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
    have hh0_inj: "inj_on h0 {0..1::real}"
      using hh0_bij hI01 unfolding bij_betw_def by simp
    have hh0_img: "h0 ` {0..1} = D"
      using hh0_bij hI01 unfolding bij_betw_def by simp
    have hh0_cont_custom: "top1_continuous_map_on I_set I_top D
        (subspace_topology top1_S2 top1_S2_topology D) h0"
      using hh0 unfolding top1_homeomorphism_on_def by (by100 blast)
    have hh0_cont_std: "continuous_on {0..1::real} h0"
      unfolding continuous_on_open_invariant
    proof (intro allI impI)
      fix B :: "(real \<times> real \<times> real) set" assume "open B"
      \<comment> \<open>B is standard-open in R^3. B \<inter> D is open in D (subspace from S^2 subspace from R^3).
         h0\<inverse>(B \<inter> D) is open in I_set (from custom continuity).
         The I_set custom topology = standard [0,1] subspace topology.\<close>
      have "B \<in> (top1_open_sets :: (real \<times> real \<times> real) set set)"
        using \<open>open B\<close> unfolding top1_open_sets_def by simp
      have hR3eq: "top1_S2_topology = subspace_topology UNIV
          (top1_open_sets :: (real \<times> real \<times> real) set set) top1_S2"
        unfolding top1_S2_topology_def
        using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
              product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
      have hD_sub_S2: "D \<subseteq> top1_S2" using assms(2) by (by100 blast)
      have "B \<inter> D \<in> subspace_topology top1_S2 top1_S2_topology D"
      proof -
        have "B \<inter> top1_S2 \<in> top1_S2_topology"
          using \<open>B \<in> top1_open_sets\<close> hR3eq unfolding subspace_topology_def by (by100 blast)
        moreover have "B \<inter> D = D \<inter> (B \<inter> top1_S2)" using hD_sub_S2 by (by100 blast)
        ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
      qed
      hence "{s \<in> I_set. h0 s \<in> B \<inter> D} \<in> I_top"
        using hh0_cont_custom unfolding top1_continuous_map_on_def by (by100 blast)
      have hh0_range: "\<forall>s \<in> I_set. h0 s \<in> D"
        using hh0_cont_custom unfolding top1_continuous_map_on_def by (by100 blast)
      hence "{s \<in> I_set. h0 s \<in> B} = {s \<in> I_set. h0 s \<in> B \<inter> D}" by (by100 blast)
      hence hpre_Itop: "{s \<in> I_set. h0 s \<in> B} \<in> I_top"
        using \<open>{s \<in> I_set. h0 s \<in> B \<inter> D} \<in> I_top\<close> by simp
      \<comment> \<open>I_top = subspace_topology UNIV top1_open_sets I_set.
         An I_top-open set = I_set \<inter> W for some standard-open W.\<close>
      obtain W where "W \<in> (top1_open_sets :: real set set)" "{s \<in> I_set. h0 s \<in> B} = I_set \<inter> W"
        using hpre_Itop unfolding top1_unit_interval_topology_def subspace_topology_def
        by (by100 blast)
      have hW_open: "open W" using \<open>W \<in> top1_open_sets\<close> unfolding top1_open_sets_def by simp
      have hpre_W: "{s \<in> I_set. h0 s \<in> B} = I_set \<inter> W"
        by (rule \<open>{s \<in> I_set. h0 s \<in> B} = I_set \<inter> W\<close>)
      have "h0 -` B \<inter> {0..1} = {s \<in> I_set. h0 s \<in> B}" unfolding hI01 by (by100 blast)
      hence "h0 -` B \<inter> {0..1} = I_set \<inter> W" using hpre_W by simp
      hence "W \<inter> {0..1} = h0 -` B \<inter> {0..1::real}" unfolding hI01 by (by100 blast)
      thus "\<exists>T. open T \<and> T \<inter> {0..1} = h0 -` B \<inter> {0..1::real}"
        using hW_open by (by100 blast)
    qed
    \<comment> \<open>Step 2: Sequence of nested intervals. Use nat recursion.\<close>
    define pick_half :: "(real \<times> real) \<Rightarrow> (real \<times> real)" where
      "pick_half = (\<lambda>(lo, hi). let mid = (lo + hi) / 2 in
        if \<not> (\<exists>f. top1_is_path_on (top1_S2 - h0 ` {lo..mid})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {lo..mid})) a' b' f)
        then (lo, mid) else (mid, hi))"
    define seq :: "nat \<Rightarrow> real \<times> real" where
      "seq = rec_nat (0, 1) (\<lambda>_ iv. pick_half iv)"
    \<comment> \<open>Properties: nested, length \<rightarrow> 0, each h0(interval) separates a' from b'.\<close>
    have hseq_0: "seq 0 = (0, 1)" unfolding seq_def by simp
    have hseq_Suc: "\<And>n. seq (Suc n) = pick_half (seq n)" unfolding seq_def by simp
    have hpick_half_props: "\<And>lo hi. let mid = (lo + hi) / 2 in
        fst (pick_half (lo, hi)) = lo \<and> snd (pick_half (lo, hi)) = mid \<or>
        fst (pick_half (lo, hi)) = mid \<and> snd (pick_half (lo, hi)) = hi"
      unfolding pick_half_def by (simp add: Let_def)
    have hseq_len: "\<forall>n. snd (seq n) - fst (seq n) = (1/2)^n"
    proof (rule allI)
      fix n show "snd (seq n) - fst (seq n) = (1/2)^n"
      proof (induction n)
        case 0 show ?case using hseq_0 by simp
      next
        case (Suc n)
        have "seq (Suc n) = pick_half (seq n)" by (rule hseq_Suc)
        obtain lo hi where hlh: "seq n = (lo, hi)" by (cases "seq n")
        hence hlen: "hi - lo = (1/2)^n" using Suc by simp
        have hmid: "(lo + hi) / 2 - lo = (hi - lo) / 2" "hi - (lo + hi) / 2 = (hi - lo) / 2"
          by (simp_all add: field_simps)
        from hpick_half_props[of lo hi] hlh
        have "fst (pick_half (lo, hi)) = lo \<and> snd (pick_half (lo, hi)) = (lo+hi)/2 \<or>
            fst (pick_half (lo, hi)) = (lo+hi)/2 \<and> snd (pick_half (lo, hi)) = hi"
          by (simp add: Let_def)
        hence "snd (seq (Suc n)) - fst (seq (Suc n)) = (hi - lo) / 2"
          using \<open>seq (Suc n) = pick_half (seq n)\<close> hlh hmid by auto
        thus ?case using hlen by simp
      qed
    qed
    have hseq_nested: "\<forall>n. fst (seq n) \<le> fst (seq (Suc n)) \<and> snd (seq (Suc n)) \<le> snd (seq n)"
    proof (rule allI, intro conjI)
      fix n
      obtain lo hi where hlh: "seq n = (lo, hi)" by (cases "seq n")
      have hlen_pos: "hi - lo = (1/2)^n"
        using spec[OF hseq_len, of n] hlh by simp
      hence "lo \<le> hi" by (simp add: algebra_simps)
      hence hmid_range: "lo \<le> (lo+hi)/2" "(lo+hi)/2 \<le> hi" by auto
      note hph = hpick_half_props[of lo hi]
      have hcases: "fst (pick_half (lo, hi)) = lo \<and> snd (pick_half (lo, hi)) = (lo+hi)/2 \<or>
          fst (pick_half (lo, hi)) = (lo+hi)/2 \<and> snd (pick_half (lo, hi)) = hi"
        using hph by (simp add: Let_def)
      show "fst (seq n) \<le> fst (seq (Suc n))"
        using hcases hseq_Suc hlh hmid_range by auto
      show "snd (seq (Suc n)) \<le> snd (seq n)"
        using hcases hseq_Suc hlh hmid_range by auto
    qed
    have hseq_range: "\<forall>n. 0 \<le> fst (seq n) \<and> snd (seq n) \<le> 1"
    proof (rule allI)
      fix n show "0 \<le> fst (seq n) \<and> snd (seq n) \<le> 1"
      proof (induction n)
        case 0 show ?case using hseq_0 by simp
      next
        case (Suc n)
        have "fst (seq n) \<le> fst (seq (Suc n))" using hseq_nested by (by100 blast)
        moreover have "snd (seq (Suc n)) \<le> snd (seq n)" using hseq_nested by (by100 blast)
        ultimately show ?case using Suc by simp
      qed
    qed
    have hseq_sep: "\<forall>n. \<not> (\<exists>f. top1_is_path_on (top1_S2 - h0 ` {fst (seq n)..snd (seq n)})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {fst (seq n)..snd (seq n)}))
        a' b' f)"
    proof (rule allI)
      fix n show "\<not> (\<exists>f. top1_is_path_on (top1_S2 - h0 ` {fst (seq n)..snd (seq n)})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {fst (seq n)..snd (seq n)}))
          a' b' f)"
      proof (induction n)
        case 0
        have "h0 ` {fst (seq 0)..snd (seq 0)} = D"
          using hseq_0 hh0_img by simp
        thus ?case using hab'_sep by simp
      next
        case (Suc n)
        \<comment> \<open>IH: can't be joined in S^2-h0(I_n). pick_half picks the bad half.\<close>
        obtain lo hi where hlh: "seq n = (lo, hi)" by (cases "seq n")
        let ?mid = "(lo + hi) / 2"
        have "seq (Suc n) = pick_half (lo, hi)" using hseq_Suc hlh by simp
        show ?case
        proof (cases "\<not> (\<exists>f. top1_is_path_on (top1_S2 - h0 ` {lo..?mid})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {lo..?mid})) a' b' f)")
          case True
          \<comment> \<open>pick_half picks left half (lo, mid).\<close>
          have hph_True: "pick_half (lo, hi) = (lo, ?mid)"
            unfolding pick_half_def Let_def using True by simp
          hence "seq (Suc n) = (lo, ?mid)" using \<open>seq (Suc n) = pick_half (lo, hi)\<close> by simp
          hence "h0 ` {fst (seq (Suc n))..snd (seq (Suc n))} = h0 ` {lo..?mid}" by simp
          thus ?thesis using True by simp
        next
          case False
          hence hjoinable_left: "\<exists>f. top1_is_path_on (top1_S2 - h0 ` {lo..?mid})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {lo..?mid})) a' b' f"
            by simp
          have hph_False: "pick_half (lo, hi) = (?mid, hi)"
            unfolding pick_half_def Let_def using False by auto
          hence hseq_eq: "seq (Suc n) = (?mid, hi)" using \<open>seq (Suc n) = pick_half (lo, hi)\<close> by simp
          \<comment> \<open>By joining lemma contrapositive: since can't join in S^2-h0({lo..hi}),
             and CAN join in S^2-h0({lo..mid}), MUST NOT join in S^2-h0({mid..hi}).\<close>
          have hcant_join_right: "\<not> (\<exists>f. top1_is_path_on (top1_S2 - h0 ` {?mid..hi})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {?mid..hi})) a' b' f)"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            hence hjoinable_right: "\<exists>f. top1_is_path_on (top1_S2 - h0 ` {?mid..hi})
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {?mid..hi})) a' b' f"
              by simp
            \<comment> \<open>Both halves joinable. By arc_joining_lemma, full arc joinable. Contradiction.\<close>
            \<comment> \<open>Need: h0({lo..mid}) and h0({mid..hi}) are arcs, closed, intersect in {h0(mid)}.\<close>
            \<comment> \<open>a', b' \<in> S^2 - D \<subseteq> S^2 - h0({lo..hi}).\<close>
            \<comment> \<open>Setup for arc_joining_lemma.\<close>
            let ?D1 = "h0 ` {lo..?mid}" and ?D2 = "h0 ` {?mid..hi}"
            have hlen_n: "hi - lo = (1/2)^n"
              using spec[OF hseq_len, of n] hlh by simp
            hence "lo \<le> hi" by (simp add: algebra_simps)
            hence hmid_range: "lo \<le> ?mid" "?mid \<le> hi" by auto
            have hD1_sub: "?D1 \<subseteq> top1_S2"
            proof -
              have "0 \<le> lo" using spec[OF hseq_range, of n] hlh by simp
              have "hi \<le> 1" using spec[OF hseq_range, of n] hlh by simp
              have "?mid \<le> 1" using \<open>hi \<le> 1\<close> hmid_range by linarith
              have "{lo..?mid} \<subseteq> {0..1}" using \<open>0 \<le> lo\<close> \<open>?mid \<le> 1\<close> by auto
              hence "h0 ` {lo..?mid} \<subseteq> D" using hh0_img by (by100 blast)
              thus ?thesis using assms(2) by (by100 blast)
            qed
            have hD2_sub: "?D2 \<subseteq> top1_S2"
            proof -
              have "0 \<le> lo" using spec[OF hseq_range, of n] hlh by simp
              have "hi \<le> 1" using spec[OF hseq_range, of n] hlh by simp
              have "0 \<le> ?mid" using \<open>0 \<le> lo\<close> hmid_range by linarith
              have "{?mid..hi} \<subseteq> {0..1}" using \<open>0 \<le> ?mid\<close> \<open>hi \<le> 1\<close> by auto
              hence "h0 ` {?mid..hi} \<subseteq> D" using hh0_img by (by100 blast)
              thus ?thesis using assms(2) by (by100 blast)
            qed
            have hD1_closed: "closedin_on top1_S2 top1_S2_topology ?D1"
            proof -
              have "0 \<le> lo" using spec[OF hseq_range, of n] hlh by simp
              have "hi \<le> 1" using spec[OF hseq_range, of n] hlh by simp
              have "{lo..?mid} \<subseteq> {0..1}" using \<open>0 \<le> lo\<close> hmid_range \<open>hi \<le> 1\<close> by auto
              have "continuous_on {lo..?mid} h0"
                by (rule continuous_on_subset[OF hh0_cont_std \<open>{lo..?mid} \<subseteq> {0..1}\<close>])
              have "compact {lo..?mid}" by (rule compact_Icc)
              hence "compact (h0 ` {lo..?mid})"
                by (rule compact_continuous_image[OF \<open>continuous_on {lo..?mid} h0\<close>])
              hence "closed (h0 ` {lo..?mid})" by (rule compact_imp_closed)
              \<comment> \<open>closed in R^3 + subset of S^2 → closedin_on S^2.\<close>
              show ?thesis unfolding closedin_on_def
              proof (intro conjI)
                show "?D1 \<subseteq> top1_S2" by (rule hD1_sub)
                show "top1_S2 - ?D1 \<in> top1_S2_topology"
                proof -
                  have "open (- h0 ` {lo..?mid})" using \<open>closed (h0 ` {lo..?mid})\<close>
                    by (rule open_Compl)
                  have hR3eq: "top1_S2_topology = subspace_topology UNIV
                      (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
                    unfolding top1_S2_topology_def
                    using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                          product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
                  have "- h0 ` {lo..?mid} \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)"
                    using \<open>open (- h0 ` {lo..?mid})\<close> unfolding top1_open_sets_def by simp
                  have "top1_S2 \<inter> (- h0 ` {lo..?mid}) \<in> top1_S2_topology"
                    using \<open>- h0 ` {lo..?mid} \<in> top1_open_sets\<close> hR3eq
                    unfolding subspace_topology_def by (by100 blast)
                  moreover have "top1_S2 - ?D1 = top1_S2 \<inter> (- h0 ` {lo..?mid})" by (by100 blast)
                  ultimately show ?thesis by simp
                qed
              qed
            qed
            have hD2_closed: "closedin_on top1_S2 top1_S2_topology ?D2"
            proof -
              have "0 \<le> lo" using spec[OF hseq_range, of n] hlh by simp
              have "hi \<le> 1" using spec[OF hseq_range, of n] hlh by simp
              have "{?mid..hi} \<subseteq> {0..1}" using \<open>0 \<le> lo\<close> hmid_range \<open>hi \<le> 1\<close> by auto
              have "continuous_on {?mid..hi} h0"
                by (rule continuous_on_subset[OF hh0_cont_std \<open>{?mid..hi} \<subseteq> {0..1}\<close>])
              have "compact {?mid..hi}" by (rule compact_Icc)
              hence "compact (h0 ` {?mid..hi})"
                by (rule compact_continuous_image[OF \<open>continuous_on {?mid..hi} h0\<close>])
              hence "closed (h0 ` {?mid..hi})" by (rule compact_imp_closed)
              show ?thesis unfolding closedin_on_def
              proof (intro conjI)
                show "?D2 \<subseteq> top1_S2" by (rule hD2_sub)
                show "top1_S2 - ?D2 \<in> top1_S2_topology"
                proof -
                  have "open (- h0 ` {?mid..hi})" using \<open>closed (h0 ` {?mid..hi})\<close>
                    by (rule open_Compl)
                  have hR3eq: "top1_S2_topology = subspace_topology UNIV
                      (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
                    unfolding top1_S2_topology_def
                    using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                          product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
                  have "- h0 ` {?mid..hi} \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)"
                    using \<open>open (- h0 ` {?mid..hi})\<close> unfolding top1_open_sets_def by simp
                  have "top1_S2 \<inter> (- h0 ` {?mid..hi}) \<in> top1_S2_topology"
                    using \<open>- h0 ` {?mid..hi} \<in> top1_open_sets\<close> hR3eq
                    unfolding subspace_topology_def by (by100 blast)
                  moreover have "top1_S2 - ?D2 = top1_S2 \<inter> (- h0 ` {?mid..hi})" by (by100 blast)
                  ultimately show ?thesis by simp
                qed
              qed
            qed
            have hD12_inter: "?D1 \<inter> ?D2 = {h0 ?mid}"
            proof (rule set_eqI, rule iffI)
              fix y assume "y \<in> ?D1 \<inter> ?D2"
              then obtain s t where hs: "s \<in> {lo..?mid}" "y = h0 s"
                  and ht: "t \<in> {?mid..hi}" "y = h0 t" by (by100 blast)
              hence "h0 s = h0 t" by simp
              have "0 \<le> lo" using spec[OF hseq_range, of n] hlh by simp
              have "hi \<le> 1" using spec[OF hseq_range, of n] hlh by simp
              have "s \<in> {0..1}" using hs(1) \<open>0 \<le> lo\<close> hmid_range \<open>hi \<le> 1\<close> by auto
              have "t \<in> {0..1}" using ht(1) \<open>0 \<le> lo\<close> hmid_range \<open>hi \<le> 1\<close> by auto
              have "s = t" using \<open>h0 s = h0 t\<close> hh0_inj \<open>s \<in> {0..1}\<close> \<open>t \<in> {0..1}\<close>
                unfolding inj_on_def by (by100 blast)
              have "s \<le> ?mid" using hs(1) by simp
              have "?mid \<le> s" using ht(1) \<open>s = t\<close> by simp
              hence "s = ?mid" using \<open>s \<le> ?mid\<close> by linarith
              have "y = h0 ?mid" using hs(2) \<open>s = ?mid\<close> by simp
              thus "y \<in> {h0 ?mid}" by simp
            next
              fix y assume "y \<in> {h0 ?mid}"
              hence "y = h0 ?mid" by simp
              moreover have "?mid \<in> {lo..?mid}" "?mid \<in> {?mid..hi}" using hmid_range by auto
              ultimately show "y \<in> ?D1 \<inter> ?D2" by (by100 blast)
            qed
            have hd_S2: "h0 ?mid \<in> top1_S2"
            proof -
              have "?mid \<in> {lo..?mid}" using hmid_range by simp
              hence "h0 ?mid \<in> ?D1" by (by100 blast)
              thus ?thesis using hD1_sub by (by100 blast)
            qed
            have hD12_union: "?D1 \<union> ?D2 = h0 ` {lo..hi}"
              using hmid_range by (auto simp: image_Un[symmetric] ivl_disj_un_two_touch)
            have hab'_D12: "a' \<in> top1_S2 - (?D1 \<union> ?D2)" "b' \<in> top1_S2 - (?D1 \<union> ?D2)"
            proof -
              have "h0 ` {lo..hi} \<subseteq> D"
              proof -
                have "0 \<le> lo" using spec[OF hseq_range, of n] hlh by simp
                have "hi \<le> 1" using spec[OF hseq_range, of n] hlh by simp
                have "{lo..hi} \<subseteq> {0..1}" using \<open>0 \<le> lo\<close> \<open>hi \<le> 1\<close> by auto
                thus ?thesis using hh0_img by (by100 blast)
              qed
              hence "?D1 \<union> ?D2 \<subseteq> D" using hD12_union by simp
              thus "a' \<in> top1_S2 - (?D1 \<union> ?D2)" "b' \<in> top1_S2 - (?D1 \<union> ?D2)"
                using ha' hb' by (by100 blast)+
            qed
            have "\<exists>f. top1_is_path_on (top1_S2 - h0 ` {lo..hi})
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {lo..hi})) a' b' f"
            proof -
              have "?D1 \<union> ?D2 = h0 ` {lo..hi}"
                using hmid_range by (auto simp: image_Un[symmetric] ivl_disj_un_two_touch)
              have "\<exists>f. top1_is_path_on (top1_S2 - (?D1 \<union> ?D2))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?D1 \<union> ?D2))) a' b' f"
                by (rule arc_joining_lemma[OF assms(1) hD1_sub hD2_sub hD1_closed hD2_closed
                    hD12_inter hd_S2 hab'_D12 hjoinable_left hjoinable_right])
              thus ?thesis using \<open>?D1 \<union> ?D2 = h0 ` {lo..hi}\<close> by simp
            qed
            moreover have "h0 ` {fst (seq n)..snd (seq n)} = h0 ` {lo..hi}" using hlh by simp
            ultimately show False using Suc by simp
          qed
          have "h0 ` {fst (seq (Suc n))..snd (seq (Suc n))} = h0 ` {?mid..hi}"
            using hseq_eq by simp
          thus ?thesis using hcant_join_right by simp
        qed
      qed
    qed
    \<comment> \<open>Step 3: Cantor intersection. Monotone bounded sequences converge.\<close>
    define x where "x = (SUP n. fst (seq n))"
    have hfst_le_snd: "\<forall>n. fst (seq n) \<le> snd (seq n)"
    proof
      fix n have "snd (seq n) - fst (seq n) = (1/2)^n" using hseq_len by (by100 blast)
      moreover have "(1/2::real)^n \<ge> 0" by simp
      ultimately show "fst (seq n) \<le> snd (seq n)" by linarith
    qed
    have hfst_le_1: "\<forall>n. fst (seq n) \<le> 1"
    proof
      fix n show "fst (seq n) \<le> 1"
        using spec[OF hfst_le_snd, of n] spec[OF hseq_range, of n] by linarith
    qed
    have hbdd: "bdd_above (range (\<lambda>n. fst (seq n)))"
      by (intro bdd_aboveI[of _ 1]) (use hfst_le_1 in auto)
    have hx_range: "0 \<le> x \<and> x \<le> 1"
    proof (intro conjI)
      show "0 \<le> x"
      proof -
        have "fst (seq 0) \<in> range (\<lambda>n. fst (seq n))" by (by100 blast)
        hence "fst (seq 0) \<le> x" unfolding x_def
          using cSUP_upper[OF _ hbdd] by (by100 blast)
        thus ?thesis using hseq_0 by simp
      qed
      show "x \<le> 1"
      proof -
        have "\<forall>n. fst (seq n) \<le> 1" by (rule hfst_le_1)
        hence "Sup (range (\<lambda>n. fst (seq n))) \<le> 1"
          by (intro cSup_least) auto
        thus ?thesis unfolding x_def by simp
      qed
    qed
    have hx_ge_fst: "\<forall>n. fst (seq n) \<le> x"
    proof
      fix n
      have "fst (seq n) \<in> range (\<lambda>n. fst (seq n))" by (by100 blast)
      thus "fst (seq n) \<le> x" unfolding x_def using cSUP_upper[OF _ hbdd] by (by100 blast)
    qed
    have hx_le_snd: "\<forall>n. x \<le> snd (seq n)"
    proof
      fix n
      have "\<forall>m. fst (seq m) \<le> snd (seq n)"
      proof
        fix m show "fst (seq m) \<le> snd (seq n)"
        proof (cases "m \<le> n")
          case True
          have "fst (seq m) \<le> fst (seq n)"
            by (rule lift_Suc_mono_le[of "\<lambda>k. fst (seq k)"])
               (use hseq_nested in auto, rule True)
          also have "... \<le> snd (seq n)" using hfst_le_snd by (by100 blast)
          finally show ?thesis .
        next
          case False hence "n \<le> m" by simp
          have "snd (seq m) \<le> snd (seq n)"
            using \<open>n \<le> m\<close>
          proof (induction m)
            case 0 thus ?case by simp
          next
            case (Suc m)
            show ?case
            proof (cases "n \<le> m")
              case True
              have "snd (seq (Suc m)) \<le> snd (seq m)" using hseq_nested by (by100 blast)
              also have "... \<le> snd (seq n)" using Suc True by simp
              finally show ?thesis .
            next
              case False hence "n = Suc m" using Suc by simp
              thus ?thesis by simp
            qed
          qed
          have "fst (seq m) \<le> snd (seq m)" using hfst_le_snd by (by100 blast)
          thus ?thesis using \<open>snd (seq m) \<le> snd (seq n)\<close> by linarith
        qed
      qed
      thus "x \<le> snd (seq n)" unfolding x_def
        using cSup_least[of "range (\<lambda>m. fst (seq m))"] by auto
    qed
    have hx_limit: "\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. fst (seq n) \<le> x \<and> x \<le> snd (seq n) \<and>
        snd (seq n) - fst (seq n) < \<epsilon>"
    proof (intro allI impI)
      fix \<epsilon> :: real assume "0 < \<epsilon>"
      obtain N where "(1/2::real)^N < \<epsilon>"
        using real_arch_pow_inv[OF \<open>0 < \<epsilon>\<close>, of "1/2"] by auto
      show "\<exists>N. \<forall>n\<ge>N. fst (seq n) \<le> x \<and> x \<le> snd (seq n) \<and> snd (seq n) - fst (seq n) < \<epsilon>"
      proof (intro exI[of _ N] allI impI)
        fix n assume "N \<le> n"
        show "fst (seq n) \<le> x \<and> x \<le> snd (seq n) \<and> snd (seq n) - fst (seq n) < \<epsilon>"
        proof (intro conjI)
          show "fst (seq n) \<le> x" using hx_ge_fst by (by100 blast)
          show "x \<le> snd (seq n)" using hx_le_snd by (by100 blast)
          have "snd (seq n) - fst (seq n) = (1/2)^n" using hseq_len by (by100 blast)
          also have "... \<le> (1/2::real)^N" using \<open>N \<le> n\<close> by (rule power_decreasing) simp_all
          also have "... < \<epsilon>" by (rule \<open>(1/2)^N < \<epsilon>\<close>)
          finally show "snd (seq n) - fst (seq n) < \<epsilon>" .
        qed
      qed
    qed
    \<comment> \<open>Step 4: Path from a' to b' in S^2-{h0(x)}.\<close>
    have hx_S2: "h0 x \<in> top1_S2"
    proof -
      have "x \<in> {0..1}" using hx_range by simp
      hence "h0 x \<in> h0 ` {0..1}" by (by100 blast)
      hence "h0 x \<in> D" using hh0_img by simp
      thus ?thesis using assms(2) by (by100 blast)
    qed
    \<comment> \<open>Get custom path from S2_minus_point_simply_connected.\<close>
    have hh0x_in_D: "h0 x \<in> D"
    proof -
      have "x \<in> {0..1}" using hx_range by simp
      thus ?thesis using hh0_img by (by100 blast)
    qed
    have ha'_S2x: "a' \<in> top1_S2 - {h0 x}"
      using ha' hh0x_in_D by (by100 blast)
    have hb'_S2x: "b' \<in> top1_S2 - {h0 x}"
      using hb' hh0x_in_D by (by100 blast)
    have hpc_S2x: "top1_path_connected_on (top1_S2 - {h0 x})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {h0 x}))"
    proof -
      have "top1_simply_connected_on (top1_S2 - {h0 x})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {h0 x}))"
        by (rule S2_minus_point_simply_connected[OF hx_S2])
      thus ?thesis unfolding top1_simply_connected_on_def by (by100 blast)
    qed
    obtain \<alpha>_custom where h\<alpha>c: "top1_is_path_on (top1_S2 - {h0 x})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {h0 x})) a' b' \<alpha>_custom"
      using hpc_S2x ha'_S2x hb'_S2x unfolding top1_path_connected_on_def by (by100 blast)
    \<comment> \<open>Bridge custom path to standard continuous_on.\<close>
    \<comment> \<open>Bridge custom path to standard continuous_on. Same pattern as h0_cont_std.\<close>
    have h\<alpha>c_cont: "top1_continuous_map_on I_set I_top (top1_S2 - {h0 x})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {h0 x})) \<alpha>_custom"
      using h\<alpha>c unfolding top1_is_path_on_def by (by100 blast)
    have h\<alpha>c_range: "\<forall>t\<in>I_set. \<alpha>_custom t \<in> top1_S2 - {h0 x}"
      using h\<alpha>c_cont unfolding top1_continuous_map_on_def by (by100 blast)
    have h\<alpha>c_0: "\<alpha>_custom 0 = a'" using h\<alpha>c unfolding top1_is_path_on_def by (by100 blast)
    have h\<alpha>c_1: "\<alpha>_custom 1 = b'" using h\<alpha>c unfolding top1_is_path_on_def by (by100 blast)
    have h\<alpha>c_cont_std: "continuous_on {0..1::real} \<alpha>_custom"
      unfolding continuous_on_open_invariant
    proof (intro allI impI)
      fix B :: "(real \<times> real \<times> real) set" assume "open B"
      have "B \<in> (top1_open_sets :: (real \<times> real \<times> real) set set)"
        using \<open>open B\<close> unfolding top1_open_sets_def by simp
      have hR3eq: "top1_S2_topology = subspace_topology UNIV
          (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
        unfolding top1_S2_topology_def
        using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
              product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
      have hS2x_sub: "top1_S2 - {h0 x} \<subseteq> top1_S2" by (by100 blast)
      have "B \<inter> (top1_S2 - {h0 x}) \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {h0 x})"
      proof -
        have "B \<inter> top1_S2 \<in> top1_S2_topology"
          using \<open>B \<in> top1_open_sets\<close> hR3eq unfolding subspace_topology_def by (by100 blast)
        moreover have "B \<inter> (top1_S2 - {h0 x}) = (top1_S2 - {h0 x}) \<inter> (B \<inter> top1_S2)"
          by (by100 blast)
        ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
      qed
      hence "{s \<in> I_set. \<alpha>_custom s \<in> B \<inter> (top1_S2 - {h0 x})} \<in> I_top"
        using h\<alpha>c_cont unfolding top1_continuous_map_on_def by (by100 blast)
      have "{s \<in> I_set. \<alpha>_custom s \<in> B} = {s \<in> I_set. \<alpha>_custom s \<in> B \<inter> (top1_S2 - {h0 x})}"
        using h\<alpha>c_range by (by100 blast)
      hence "{s \<in> I_set. \<alpha>_custom s \<in> B} \<in> I_top"
        using \<open>{s \<in> I_set. \<alpha>_custom s \<in> B \<inter> _} \<in> I_top\<close> by simp
      then obtain W where "W \<in> (top1_open_sets :: real set set)"
          "{s \<in> I_set. \<alpha>_custom s \<in> B} = I_set \<inter> W"
        unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
      have "open W" using \<open>W \<in> top1_open_sets\<close> unfolding top1_open_sets_def by simp
      have "\<alpha>_custom -` B \<inter> {0..1} = {s \<in> I_set. \<alpha>_custom s \<in> B}" unfolding hI01 by (by100 blast)
      hence "\<alpha>_custom -` B \<inter> {0..1} = I_set \<inter> W"
        using \<open>{s \<in> I_set. \<alpha>_custom s \<in> B} = I_set \<inter> W\<close> by simp
      hence "W \<inter> {0..1} = \<alpha>_custom -` B \<inter> {0..1}" unfolding hI01 by (by100 blast)
      thus "\<exists>T. open T \<and> T \<inter> {0..1} = \<alpha>_custom -` B \<inter> {0..1::real}"
        using \<open>open W\<close> by (by100 blast)
    qed
    define \<alpha> where "\<alpha> = \<alpha>_custom"
    have h\<alpha>: "continuous_on {0..1::real} \<alpha>"
        "\<alpha> 0 = a'" "\<alpha> 1 = b'" "\<forall>t\<in>{0..1}. \<alpha> t \<in> top1_S2 - {h0 x}"
      unfolding \<alpha>_def using h\<alpha>c_cont_std h\<alpha>c_0 h\<alpha>c_1 h\<alpha>c_range unfolding hI01 by auto
    \<comment> \<open>Step 5: \<alpha>(I) compact, positive distance from h0(x).\<close>
    have h\<alpha>_compact: "compact (\<alpha> ` {0..1})" by (rule compact_continuous_image[OF h\<alpha>(1) compact_Icc])
    have h\<alpha>_disjoint: "h0 x \<notin> \<alpha> ` {0..1}"
    proof
      assume "h0 x \<in> \<alpha> ` {0..1}"
      then obtain t where "t \<in> {0..1}" "\<alpha> t = h0 x" by auto
      hence "\<alpha> t \<in> top1_S2 - {h0 x}" using h\<alpha>(4) \<open>t \<in> {0..1}\<close> by simp
      hence "\<alpha> t \<noteq> h0 x" by (by100 blast)
      thus False using \<open>\<alpha> t = h0 x\<close> by simp
    qed
    \<comment> \<open>Step 5: \<alpha>(I) compact hence closed. S^2-\<alpha>(I) open, contains h0(x).\<close>
    have h\<alpha>_closed: "closed (\<alpha> ` {0..1})" by (rule compact_imp_closed[OF h\<alpha>_compact])
    have hcompl_open: "open (- \<alpha> ` {0..1})" using h\<alpha>_closed by (rule open_Compl)
    have hh0x_in_compl: "h0 x \<in> - \<alpha> ` {0..1}" using h\<alpha>_disjoint by simp
    \<comment> \<open>Step 6: h0 continuous at x. Find open neighborhood of x whose h0-image avoids \<alpha>.\<close>
    have "\<exists>U. open U \<and> x \<in> U \<and> h0 ` (U \<inter> {0..1}) \<subseteq> - \<alpha> ` {0..1}"
    proof -
      have "open (- \<alpha> ` {0..1})" by (rule hcompl_open)
      moreover have "h0 x \<in> - \<alpha> ` {0..1}" by (rule hh0x_in_compl)
      \<comment> \<open>continuous_on_open_invariant: preimage of open is relatively open.\<close>
      obtain W where hW_open: "open W" and hW_eq: "W \<inter> {0..1} = h0 -` (- \<alpha> ` {0..1}) \<inter> {0..1}"
        using iffD1[OF continuous_on_open_invariant hh0_cont_std, rule_format, OF hcompl_open]
        by auto
      have "x \<in> W"
      proof -
        have "x \<in> h0 -` (- \<alpha> ` {0..1}) \<inter> {0..1}" using hh0x_in_compl hx_range by simp
        hence "x \<in> W \<inter> {0..1}" using hW_eq by auto
        thus "x \<in> W" by simp
      qed
      have "h0 ` (W \<inter> {0..1}) \<subseteq> - \<alpha> ` {0..1}"
      proof
        fix y assume "y \<in> h0 ` (W \<inter> {0..1})"
        then obtain t where "t \<in> W \<inter> {0..1}" "y = h0 t" by (by100 blast)
        hence "t \<in> h0 -` (- \<alpha> ` {0..1}) \<inter> {0..1}" using hW_eq by auto
        thus "y \<in> - \<alpha> ` {0..1}" using \<open>y = h0 t\<close> by simp
      qed
      thus ?thesis using hW_open \<open>x \<in> W\<close> by (by100 blast)
    qed
    then obtain U_nbhd where hU_open: "open U_nbhd" and hx_U: "x \<in> U_nbhd"
        and hU_avoids: "h0 ` (U_nbhd \<inter> {0..1}) \<subseteq> - \<alpha> ` {0..1}" by blast
    \<comment> \<open>For large m, I_m \<subseteq> U_nbhd (since I_m shrinks to {x} and U_nbhd is open).\<close>
    have "\<exists>N. {fst (seq N)..snd (seq N)} \<subseteq> U_nbhd \<inter> {0..1}"
    proof -
      obtain \<delta> where h\<delta>: "\<delta> > 0" "\<forall>y. dist y x < \<delta> \<longrightarrow> y \<in> U_nbhd"
        using hU_open hx_U unfolding open_dist by (by100 blast)
      obtain N where hN': "\<forall>n\<ge>N. fst (seq n) \<le> x \<and> x \<le> snd (seq n) \<and>
          snd (seq n) - fst (seq n) < \<delta>"
        using spec[OF hx_limit, of \<delta>] h\<delta>(1) by (by100 blast)
      have "{fst (seq N)..snd (seq N)} \<subseteq> U_nbhd \<inter> {0..1}"
      proof
        fix t assume "t \<in> {fst (seq N)..snd (seq N)}"
        hence ht: "fst (seq N) \<le> t" "t \<le> snd (seq N)" by auto
        have hN_props: "fst (seq N) \<le> x" "x \<le> snd (seq N)"
            "snd (seq N) - fst (seq N) < \<delta>"
          using hN' by auto
        have "dist t x < \<delta>"
          using ht hN_props unfolding dist_real_def by linarith
        hence "t \<in> U_nbhd" using h\<delta>(2) by simp
        moreover have "t \<in> {0..1}"
          using ht spec[OF hseq_range, of N] hfst_le_snd by auto
        ultimately show "t \<in> U_nbhd \<inter> {0..1}" by simp
      qed
      thus ?thesis by (by100 blast)
    qed
    then obtain N where hN_sub: "{fst (seq N)..snd (seq N)} \<subseteq> U_nbhd \<inter> {0..1}" by blast
    have hN: "h0 ` {fst (seq N)..snd (seq N)} \<subseteq> - \<alpha> ` {0..1}"
      using hN_sub hU_avoids by (by100 blast)
    have h\<alpha>_avoids: "\<alpha> ` {0..1} \<inter> h0 ` {fst (seq N)..snd (seq N)} = {}"
      using hN by (by100 blast)
    \<comment> \<open>\<alpha> is a path from a' to b' in S^2 - h0(I_N), contradicting separation.\<close>
    \<comment> \<open>\<alpha> maps into S^2-h0(I_N) (from h\<alpha>(4) + h\<alpha>_avoids).\<close>
    have h\<alpha>_in_DN: "\<forall>t\<in>I_set. \<alpha> t \<in> top1_S2 - h0 ` {fst (seq N)..snd (seq N)}"
    proof
      fix t assume "t \<in> I_set"
      hence "t \<in> {0..1::real}" unfolding hI01 by simp
      have "\<alpha> t \<in> top1_S2 - {h0 x}" using h\<alpha>(4) \<open>t \<in> {0..1}\<close> by simp
      hence h1: "\<alpha> t \<in> top1_S2" by (by100 blast)
      have h2: "\<alpha> t \<notin> h0 ` {fst (seq N)..snd (seq N)}"
      proof
        assume "\<alpha> t \<in> h0 ` {fst (seq N)..snd (seq N)}"
        hence "\<alpha> t \<in> \<alpha> ` {0..1} \<inter> h0 ` {fst (seq N)..snd (seq N)}"
          using \<open>t \<in> {0..1}\<close> by (by100 blast)
        thus False using h\<alpha>_avoids by (by100 blast)
      qed
      show "\<alpha> t \<in> top1_S2 - h0 ` {fst (seq N)..snd (seq N)}" using h1 h2 by (by100 blast)
    qed
    \<comment> \<open>Bridge standard \<alpha> to custom top1_is_path_on.\<close>
    have hpath_exists: "\<exists>f. top1_is_path_on (top1_S2 - h0 ` {fst (seq N)..snd (seq N)})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {fst (seq N)..snd (seq N)}))
        a' b' f"
    proof (intro exI[of _ \<alpha>])
      show "top1_is_path_on (top1_S2 - h0 ` {fst (seq N)..snd (seq N)})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {fst (seq N)..snd (seq N)}))
          a' b' \<alpha>"
        unfolding top1_is_path_on_def
      proof (intro conjI)
        show "top1_continuous_map_on I_set I_top
            (top1_S2 - h0 ` {fst (seq N)..snd (seq N)})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {fst (seq N)..snd (seq N)})) \<alpha>"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s assume "s \<in> I_set"
          thus "\<alpha> s \<in> top1_S2 - h0 ` {fst (seq N)..snd (seq N)}" using h\<alpha>_in_DN by simp
        next
          fix W assume "W \<in> subspace_topology top1_S2 top1_S2_topology
              (top1_S2 - h0 ` {fst (seq N)..snd (seq N)})"
          then obtain V where "V \<in> top1_S2_topology"
              "W = (top1_S2 - h0 ` {fst (seq N)..snd (seq N)}) \<inter> V"
            unfolding subspace_topology_def by (by100 blast)
          have hR3eq: "top1_S2_topology = subspace_topology UNIV
              (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
            unfolding top1_S2_topology_def
            using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                  product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
          obtain V' where hV': "V' \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)"
              "V = top1_S2 \<inter> V'"
            using \<open>V \<in> top1_S2_topology\<close> hR3eq
            unfolding subspace_topology_def by (by100 blast)
          have "open V'" using hV' unfolding top1_open_sets_def by simp
          have "{s \<in> I_set. \<alpha> s \<in> W} = {s \<in> I_set. \<alpha> s \<in> V'}"
          proof (rule set_eqI, rule iffI)
            fix s assume "s \<in> {s \<in> I_set. \<alpha> s \<in> W}"
            thus "s \<in> {s \<in> I_set. \<alpha> s \<in> V'}"
              using \<open>W = _ \<inter> V\<close> \<open>V = _ \<inter> V'\<close> by (by100 blast)
          next
            fix s assume "s \<in> {s \<in> I_set. \<alpha> s \<in> V'}"
            hence "s \<in> I_set" "\<alpha> s \<in> V'" by auto
            have "\<alpha> s \<in> top1_S2 - h0 ` {fst (seq N)..snd (seq N)}"
              using h\<alpha>_in_DN \<open>s \<in> I_set\<close> by simp
            thus "s \<in> {s \<in> I_set. \<alpha> s \<in> W}"
              using \<open>W = _ \<inter> V\<close> \<open>V = _ \<inter> V'\<close> \<open>\<alpha> s \<in> V'\<close> \<open>s \<in> I_set\<close> by (by100 blast)
          qed
          moreover have "{s \<in> I_set. \<alpha> s \<in> V'} \<in> I_top"
          proof -
            obtain U_r where "open U_r" "\<alpha> -` V' \<inter> {0..1} = U_r \<inter> {0..1}"
              using iffD1[OF continuous_on_open_invariant h\<alpha>(1), rule_format, OF \<open>open V'\<close>] by auto
            have "{s \<in> I_set. \<alpha> s \<in> V'} = I_set \<inter> U_r" unfolding hI01
              using \<open>\<alpha> -` V' \<inter> {0..1} = U_r \<inter> {0..1}\<close> by (by100 blast)
            moreover have "U_r \<in> (top1_open_sets :: real set set)"
              using \<open>open U_r\<close> unfolding top1_open_sets_def by simp
            ultimately show ?thesis
              unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
          qed
          ultimately show "{s \<in> I_set. \<alpha> s \<in> W} \<in> I_top" by simp
        qed
        show "\<alpha> 0 = a'" by (rule h\<alpha>(2))
        show "\<alpha> 1 = b'" by (rule h\<alpha>(3))
      qed
    qed
    show False using hseq_sep hpath_exists by blast
  qed
qed

(** from \<S>63 Theorem 63.4: Jordan Curve Theorem.

    Munkres' proof: use Theorem 61.3 (separation) + locally connected property +
    Theorem 63.1 argument to show at most 2 components. Each component has C as
    boundary by an auxiliary argument.

    NB: Currently stated for C \<subseteq> R^2 (as in the original formalization). **)
\<comment> \<open>Helper for 63.5: 3+ open components of S^2-(C1\<union>C2) give a contradiction.
   This encapsulates the 63.1(a)+(c) + \<pi>_1\<cong>Z argument.\<close>
lemma three_components_contradiction:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "closedin_on top1_S2 top1_S2_topology C1"
  and "closedin_on top1_S2 top1_S2_topology C2"
  and "top1_connected_on C1 (subspace_topology top1_S2 top1_S2_topology C1)"
  and "top1_connected_on C2 (subspace_topology top1_S2 top1_S2_topology C2)"
  and "card (C1 \<inter> C2) = 2"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology C1"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology C2"
  \<comment> \<open>Three disjoint nonempty open (in S^2) subsets covering S^2-(C1\<union>C2).\<close>
  and "W1 \<in> top1_S2_topology" and "W2 \<in> top1_S2_topology" and "B \<in> top1_S2_topology"
  and "W1 \<noteq> {}" and "W2 \<noteq> {}" and "B \<noteq> {}"
  and "W1 \<inter> W2 = {}" and "W1 \<inter> B = {}" and "W2 \<inter> B = {}"
  and "W1 \<union> W2 \<union> B = top1_S2 - (C1 \<union> C2)"
  shows False
proof -
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hC1sub: "C1 \<subseteq> top1_S2" using assms(2) unfolding closedin_on_def by (by100 blast)
  have hC2sub: "C2 \<subseteq> top1_S2" using assms(3) unfolding closedin_on_def by (by100 blast)
  obtain p q where hpq: "C1 \<inter> C2 = {p, q}" and hpq_ne: "p \<noteq> q"
    using assms(6) card_2_iff by (by100 metis)
  have hp_S2: "p \<in> top1_S2" and hq_S2: "q \<in> top1_S2"
    using hpq hC1sub by (by100 blast)+
  define X where "X = top1_S2 - {p} - {q}"
  define TX where "TX = subspace_topology top1_S2 top1_S2_topology X"
  define U where "U = top1_S2 - C1"
  define V where "V = top1_S2 - C2"
  have hX_eq: "U \<union> V = X"
    unfolding U_def V_def X_def using hpq by (by100 blast)
  have hUV_eq: "U \<inter> V = top1_S2 - (C1 \<union> C2)"
    unfolding U_def V_def by (by100 blast)
  have hTX: "is_topology_on X TX"
    unfolding TX_def by (rule subspace_topology_is_topology_on[OF hTS2])
      (unfold X_def, by100 blast)
  \<comment> \<open>Subsets and openness.\<close>
  have hU_sub_X: "U \<subseteq> X" unfolding U_def X_def using hpq hC1sub by (by100 blast)
  have hV_sub_X: "V \<subseteq> X" unfolding V_def X_def using hpq hC2sub by (by100 blast)
  have hU_open: "openin_on X TX U"
  proof -
    have "U \<in> top1_S2_topology"
      using assms(2) hTS2 unfolding closedin_on_def is_topology_on_def U_def by (by100 blast)
    thus ?thesis unfolding openin_on_def TX_def subspace_topology_def using hU_sub_X by (by100 blast)
  qed
  have hV_open: "openin_on X TX V"
  proof -
    have "V \<in> top1_S2_topology"
      using assms(3) hTS2 unfolding closedin_on_def is_topology_on_def V_def by (by100 blast)
    thus ?thesis unfolding openin_on_def TX_def subspace_topology_def using hV_sub_X by (by100 blast)
  qed
  \<comment> \<open>Path-connectivity.\<close>
  have hU_pc: "top1_path_connected_on U (subspace_topology top1_S2 top1_S2_topology U)"
  proof -
    have hU_conn: "top1_connected_on U (subspace_topology top1_S2 top1_S2_topology U)"
      using assms(7) unfolding top1_separates_on_def U_def by (by100 blast)
    have hU_S2: "U \<in> top1_S2_topology"
      using assms(2) hTS2 unfolding closedin_on_def is_topology_on_def U_def by (by100 blast)
    have hU_lpc: "top1_locally_path_connected_on U (subspace_topology top1_S2 top1_S2_topology U)"
      by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hU_S2])
         (unfold U_def, by100 blast)
    have hTU: "is_topology_on U (subspace_topology top1_S2 top1_S2_topology U)"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (unfold U_def, by100 blast)
    have "U \<noteq> {}"
    proof -
      have "C2 \<noteq> {p, q}"
      proof
        assume "C2 = {p, q}"
        have "{p} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {q} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hq_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{p} = {p, q} \<inter> (top1_S2 - {q})" using hpq_ne hp_S2 by (by100 auto)
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "{q} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {p} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hp_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{q} = {p, q} \<inter> (top1_S2 - {p})" using hpq_ne hq_S2 by (by100 auto)
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "\<not> top1_connected_on {p, q} (subspace_topology top1_S2 top1_S2_topology {p, q})"
          unfolding top1_connected_on_def
          using \<open>{p} \<in> _\<close> \<open>{q} \<in> _\<close> hpq_ne by (by100 blast)
        thus False using assms(5) \<open>C2 = {p, q}\<close> by (by100 simp)
      qed
      moreover have "{p, q} \<subseteq> C2" using hpq by (by100 blast)
      ultimately obtain c where "c \<in> C2" "c \<notin> {p, q}" by (by100 blast)
      hence "c \<notin> C1" using hpq by (by100 blast)
      hence "c \<in> U" unfolding U_def using \<open>c \<in> C2\<close> hC2sub by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF hTU hU_conn hU_lpc \<open>U \<noteq> {}\<close>])
  qed
  have hV_pc: "top1_path_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
  proof -
    have hV_conn: "top1_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
      using assms(8) unfolding top1_separates_on_def V_def by (by100 blast)
    have hV_S2: "V \<in> top1_S2_topology"
      using assms(3) hTS2 unfolding closedin_on_def is_topology_on_def V_def by (by100 blast)
    have hV_lpc: "top1_locally_path_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
      by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hV_S2])
         (unfold V_def, by100 blast)
    have hTV: "is_topology_on V (subspace_topology top1_S2 top1_S2_topology V)"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (unfold V_def, by100 blast)
    have "V \<noteq> {}"
    proof -
      have "C1 \<noteq> {p, q}"
      proof
        assume "C1 = {p, q}"
        have "{p} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {q} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hq_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{p} = {p, q} \<inter> (top1_S2 - {q})" using hpq_ne hp_S2 by (by100 auto)
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "{q} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {p} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hp_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{q} = {p, q} \<inter> (top1_S2 - {p})" using hpq_ne hq_S2 by (by100 auto)
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "\<not> top1_connected_on {p, q} (subspace_topology top1_S2 top1_S2_topology {p, q})"
          unfolding top1_connected_on_def
          using \<open>{p} \<in> _\<close> \<open>{q} \<in> _\<close> hpq_ne by (by100 blast)
        thus False using assms(4) \<open>C1 = {p, q}\<close> by (by100 simp)
      qed
      moreover have "{p, q} \<subseteq> C1" using hpq by (by100 blast)
      ultimately obtain c where "c \<in> C1" "c \<notin> {p, q}" by (by100 blast)
      hence "c \<notin> C2" using hpq by (by100 fast)
      hence "c \<in> V" unfolding V_def using \<open>c \<in> C1\<close> hC1sub by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF hTV hV_conn hV_lpc \<open>V \<noteq> {}\<close>])
  qed
  \<comment> \<open>Subspace topology transitivity.\<close>
  have hU_subtop: "subspace_topology X TX U = subspace_topology top1_S2 top1_S2_topology U"
    unfolding TX_def by (rule subspace_topology_trans[OF hU_sub_X])
  have hV_subtop: "subspace_topology X TX V = subspace_topology top1_S2 top1_S2_topology V"
    unfolding TX_def by (rule subspace_topology_trans[OF hV_sub_X])
  \<comment> \<open>W1, W2, B are subsets of X and open in X.\<close>
  have hW1_sub: "W1 \<subseteq> X" unfolding X_def using assms(18) hpq by (by100 blast)
  have hW2_sub: "W2 \<subseteq> X" unfolding X_def using assms(18) hpq by (by100 blast)
  have hB_sub: "B \<subseteq> X" unfolding X_def using assms(18) hpq by (by100 blast)
  have hW1_open_X: "openin_on X TX W1"
    unfolding openin_on_def TX_def subspace_topology_def using hW1_sub assms(9) by (by100 blast)
  have hW2_open_X: "openin_on X TX W2"
    unfolding openin_on_def TX_def subspace_topology_def using hW2_sub assms(10) by (by100 blast)
  have hB_open_X: "openin_on X TX B"
    unfolding openin_on_def TX_def subspace_topology_def using hB_sub assms(11) by (by100 blast)
  \<comment> \<open>Decomposition 1: A1 = W1\<union>W2, B1 = B.\<close>
  define A1 where "A1 = W1 \<union> W2"
  define B1 where "B1 = B"
  have hA1B1_eq: "U \<inter> V = A1 \<union> B1"
    unfolding A1_def B1_def using hUV_eq assms(18) by (by100 simp)
  have hA1B1_disj: "A1 \<inter> B1 = {}" unfolding A1_def B1_def using assms(16,17) by (by100 blast)
  have hA1_open: "openin_on X TX A1"
  proof -
    have "W1 \<in> TX" using hW1_open_X unfolding openin_on_def by (by100 blast)
    moreover have "W2 \<in> TX" using hW2_open_X unfolding openin_on_def by (by100 blast)
    ultimately have "W1 \<union> W2 \<in> TX" by (rule topology_union2[OF hTX])
    thus ?thesis unfolding A1_def openin_on_def using hW1_sub hW2_sub by (by100 blast)
  qed
  have hB1_open: "openin_on X TX B1" unfolding B1_def using hB_open_X by (by100 simp)
  \<comment> \<open>Pick points.\<close>
  obtain a where ha: "a \<in> W1" using assms(12) by (by100 blast)
  obtain b where hb: "b \<in> B" using assms(14) by (by100 blast)
  have ha_A1: "a \<in> A1" unfolding A1_def using ha by (by100 blast)
  have hb_B1: "b \<in> B1" unfolding B1_def using hb by (by100 simp)
  have ha_U: "a \<in> U" unfolding U_def using ha assms(18) by (by100 blast)
  have hb_U: "b \<in> U" unfolding U_def using hb assms(18) by (by100 blast)
  have ha_V: "a \<in> V" unfolding V_def using ha assms(18) by (by100 blast)
  have hb_V: "b \<in> V" unfolding V_def using hb assms(18) by (by100 blast)
  \<comment> \<open>Paths.\<close>
  obtain \<alpha> where h\<alpha>: "top1_is_path_on U (subspace_topology top1_S2 top1_S2_topology U) a b \<alpha>"
    using hU_pc ha_U hb_U unfolding top1_path_connected_on_def by (by100 blast)
  obtain \<beta> where h\<beta>: "top1_is_path_on V (subspace_topology top1_S2 top1_S2_topology V) b a \<beta>"
    using hV_pc hb_V ha_V unfolding top1_path_connected_on_def by (by100 blast)
  have h\<alpha>_X: "top1_is_path_on U (subspace_topology X TX U) a b \<alpha>"
    using h\<alpha> hU_subtop by (by100 simp)
  have h\<beta>_X: "top1_is_path_on V (subspace_topology X TX V) b a \<beta>"
    using h\<beta> hV_subtop by (by100 simp)
  have hf_nontrivial: "\<not> top1_path_homotopic_on X TX a a
      (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
    by (rule Theorem_63_1_loop_nontrivial[OF hTX hU_open hV_open hX_eq
        hA1B1_eq hA1B1_disj hA1_open hB1_open ha_A1 hb_B1 h\<alpha>_X h\<beta>_X])
  \<comment> \<open>Decomposition 2: A2 = W1, B2 = W2\<union>B.\<close>
  obtain a' where ha': "a' \<in> W2" using assms(13) by (by100 blast)
  have ha'_U: "a' \<in> U" unfolding U_def using ha' assms(18) by (by100 blast)
  have ha'_V: "a' \<in> V" unfolding V_def using ha' assms(18) by (by100 blast)
  obtain \<gamma> where h\<gamma>: "top1_is_path_on U (subspace_topology top1_S2 top1_S2_topology U) a a' \<gamma>"
    using hU_pc ha_U ha'_U unfolding top1_path_connected_on_def by (by100 blast)
  obtain \<delta> where h\<delta>: "top1_is_path_on V (subspace_topology top1_S2 top1_S2_topology V) a' a \<delta>"
    using hV_pc ha'_V ha_V unfolding top1_path_connected_on_def by (by100 blast)
  have h\<gamma>_X: "top1_is_path_on U (subspace_topology X TX U) a a' \<gamma>"
    using h\<gamma> hU_subtop by (by100 simp)
  have h\<delta>_X: "top1_is_path_on V (subspace_topology X TX V) a' a \<delta>"
    using h\<delta> hV_subtop by (by100 simp)
  define A2 where "A2 = W1"
  define B2 where "B2 = W2 \<union> B"
  have hA2B2_eq: "U \<inter> V = A2 \<union> B2"
    unfolding A2_def B2_def using hUV_eq assms(18) by (by100 blast)
  have hA2B2_disj: "A2 \<inter> B2 = {}" unfolding A2_def B2_def using assms(15,16) by (by100 blast)
  have hA2_open: "openin_on X TX A2" unfolding A2_def using hW1_open_X by (by100 simp)
  have hB2_open: "openin_on X TX B2"
  proof -
    have "W2 \<in> TX" using hW2_open_X unfolding openin_on_def by (by100 blast)
    moreover have "B \<in> TX" using hB_open_X unfolding openin_on_def by (by100 blast)
    ultimately have "W2 \<union> B \<in> TX" by (rule topology_union2[OF hTX])
    thus ?thesis unfolding B2_def openin_on_def using hW2_sub hB_sub by (by100 blast)
  qed
  have ha_A2: "a \<in> A2" unfolding A2_def using ha by (by100 simp)
  have ha'_B2: "a' \<in> B2" unfolding B2_def using ha' by (by100 blast)
  have hg_nontrivial: "\<not> top1_path_homotopic_on X TX a a
      (top1_path_product \<gamma> \<delta>) (top1_constant_path a)"
    by (rule Theorem_63_1_loop_nontrivial[OF hTX hU_open hV_open hX_eq
        hA2B2_eq hA2B2_disj hA2_open hB2_open ha_A2 ha'_B2 h\<gamma>_X h\<delta>_X])
  \<comment> \<open>Loops in X.\<close>
  have h_path_U_to_X: "\<And>a' b' f. top1_is_path_on U (subspace_topology X TX U) a' b' f
      \<Longrightarrow> top1_is_path_on X TX a' b' f"
    using path_in_subspace_is_path_in_space[OF hTX hU_sub_X hU_open] by (by100 blast)
  have h_path_V_to_X: "\<And>a' b' f. top1_is_path_on V (subspace_topology X TX V) a' b' f
      \<Longrightarrow> top1_is_path_on X TX a' b' f"
    using path_in_subspace_is_path_in_space[OF hTX hV_sub_X hV_open] by (by100 blast)
  have hf_loop: "top1_is_loop_on X TX a (top1_path_product \<alpha> \<beta>)"
    unfolding top1_is_loop_on_def
    using top1_path_product_is_path[OF hTX h_path_U_to_X[OF h\<alpha>_X] h_path_V_to_X[OF h\<beta>_X]]
    by (by100 blast)
  have hg_loop: "top1_is_loop_on X TX a (top1_path_product \<gamma> \<delta>)"
    unfolding top1_is_loop_on_def
    using top1_path_product_is_path[OF hTX h_path_U_to_X[OF h\<gamma>_X] h_path_V_to_X[OF h\<delta>_X]]
    by (by100 blast)
  \<comment> \<open>\<pi>_1(X) \<cong> Z \<Rightarrow> common power.\<close>
  have hpi1_cyclic: "\<exists>gen. top1_is_loop_on X TX a gen \<and>
      (\<forall>h. top1_is_loop_on X TX a h \<longrightarrow>
        (\<exists>n::nat. top1_path_homotopic_on X TX a a h (top1_path_power gen a n) \<or>
         top1_path_homotopic_on X TX a a h (top1_path_power (top1_path_reverse gen) a n)))"
  proof -
    have "a \<in> X" using ha hW1_sub by (by100 blast)
    thus ?thesis unfolding X_def TX_def
      by (rule pi1_S2_minus_two_points_infinite_cyclic[OF assms(1) hp_S2 hq_S2 hpq_ne])
  qed
  obtain m k where hm: "m > 0" and hmk:
      "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
        (top1_path_power (top1_path_product \<gamma> \<delta>) a k) \<or>
       top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
        (top1_path_power (top1_path_reverse (top1_path_product \<gamma> \<delta>)) a k)"
    using infinite_cyclic_common_power[OF hTX hf_loop hg_loop
      hf_nontrivial hg_nontrivial hpi1_cyclic] by (by100 blast)
  have ha'_A1: "a' \<in> A1" unfolding A1_def using ha' by (by100 blast)
  have "m = 0" using hmk
  proof
    assume hmk1: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
        (top1_path_power (top1_path_product \<gamma> \<delta>) a k)"
    show "m = 0"
      by (rule Theorem_63_1_c_subgroups_trivial[OF hTX hU_open hV_open hX_eq
        hA1B1_eq hA1B1_disj hA1_open hB1_open ha_A1 hb_B1
        h\<alpha>_X h\<beta>_X ha'_A1 h\<gamma>_X h\<delta>_X hmk1])
  next
    assume hmk2: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
        (top1_path_power (top1_path_reverse (top1_path_product \<gamma> \<delta>)) a k)"
    show "m = 0"
      by (rule Theorem_63_1_c_subgroups_trivial_reverse[OF hTX hU_open hV_open hX_eq
        hA1B1_eq hA1B1_disj hA1_open hB1_open ha_A1 hb_B1
        h\<alpha>_X h\<beta>_X ha'_A1 h\<gamma>_X h\<delta>_X hmk2])
  qed
  thus False using hm by (by100 simp)
qed

(** from \<S>63 Theorem 63.5: two closed-connected sets C1, C2 with |C1\<inter>C2|=2 and neither separates S^2 imply C1\<union>C2 separates into exactly two components. **)
theorem Theorem_63_5_two_closed_connected:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "closedin_on top1_S2 top1_S2_topology C1"
  and "closedin_on top1_S2 top1_S2_topology C2"
  and "top1_connected_on C1 (subspace_topology top1_S2 top1_S2_topology C1)"
  and "top1_connected_on C2 (subspace_topology top1_S2 top1_S2_topology C2)"
  and "card (C1 \<inter> C2) = 2"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology C1"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology C2"
  shows "\<exists>U V. U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {}
    \<and> U \<union> V = top1_S2 - (C1 \<union> C2)
    \<and> top1_connected_on U
        (subspace_topology top1_S2 top1_S2_topology U)
    \<and> top1_connected_on V
        (subspace_topology top1_S2 top1_S2_topology V)"
proof -
  \<comment> \<open>Munkres 63.5: By Theorem 61.4, C1\<union>C2 separates S^2 (\<ge>2 components).
     To show exactly 2: use Theorem 63.1. If there were 3+ components,
     one could construct two independent nontrivial elements in \<pi>_1(S^2-{p,q})
     (where C1\<inter>C2 = {p,q}), but \<pi>_1(S^2-{p,q}) \<cong> Z has only one generator.
     So exactly 2 components.\<close>
  have hsep: "top1_separates_on top1_S2 top1_S2_topology (C1 \<union> C2)"
  proof -
    have hC1sub: "C1 \<subseteq> top1_S2" using assms(2) unfolding closedin_on_def by blast
    have hC2sub: "C2 \<subseteq> top1_S2" using assms(3) unfolding closedin_on_def by blast
    show ?thesis
      by (rule Theorem_61_4_general_separation[OF assms(1) hC1sub hC2sub assms(2,3,4,5,6)])
  qed
  \<comment> \<open>At least two components: hsep gives S^2-(C1\<union>C2) disconnected.\<close>
  have hC1sub: "C1 \<subseteq> top1_S2" using assms(2) unfolding closedin_on_def by blast
  have hC2sub: "C2 \<subseteq> top1_S2" using assms(3) unfolding closedin_on_def by blast
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hC_closed: "closedin_on top1_S2 top1_S2_topology (C1 \<union> C2)"
  proof -
    have "C1 \<union> C2 \<subseteq> top1_S2" using hC1sub hC2sub by (by100 blast)
    have "top1_S2 - C1 \<in> top1_S2_topology"
      using assms(2) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
    have "top1_S2 - C2 \<in> top1_S2_topology"
      using assms(3) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
    have "top1_S2 - (C1 \<union> C2) = (top1_S2 - C1) \<inter> (top1_S2 - C2)" by (by100 blast)
    hence "top1_S2 - (C1 \<union> C2) \<in> top1_S2_topology"
      using topology_inter_open[OF hTS2 \<open>top1_S2 - C1 \<in> _\<close> \<open>top1_S2 - C2 \<in> _\<close>] by simp
    thus ?thesis using \<open>C1 \<union> C2 \<subseteq> top1_S2\<close> unfolding closedin_on_def by (by100 blast)
  qed
  \<comment> \<open>S^2-(C1\<union>C2) open in S^2, hence locally path-connected. Components = path components.\<close>
  have hopen: "top1_S2 - (C1 \<union> C2) \<in> top1_S2_topology"
    using hC_closed hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
  have hlpc: "top1_locally_path_connected_on (top1_S2 - (C1 \<union> C2))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (C1 \<union> C2)))"
    by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hopen]) (by100 blast)
  \<comment> \<open>Step 1: Extract intersection points.\<close>
  obtain p q where hpq: "C1 \<inter> C2 = {p, q}" and hpq_ne: "p \<noteq> q"
    using assms(6) card_2_iff by (by100 metis)
  have hp_S2: "p \<in> top1_S2" using hpq hC1sub by (by100 blast)
  have hq_S2: "q \<in> top1_S2" using hpq hC1sub by (by100 blast)
  \<comment> \<open>Step 2: S^2-C1 and S^2-C2 are path-connected (non-separation + lpc).\<close>
  have hU_pc: "top1_path_connected_on (top1_S2 - C1)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C1))"
  proof -
    have hU_conn: "top1_connected_on (top1_S2 - C1)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C1))"
      using assms(7) unfolding top1_separates_on_def by (by100 blast)
    have hU_open: "top1_S2 - C1 \<in> top1_S2_topology"
      using assms(2) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
    have hU_lpc: "top1_locally_path_connected_on (top1_S2 - C1)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C1))"
      by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hU_open])
         (by100 blast)
    have hTU: "is_topology_on (top1_S2 - C1)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C1))"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
    have "top1_S2 - C1 \<noteq> {}"
    proof -
      \<comment> \<open>C2 \<noteq> {p,q}: if C2 = {p,q}, singletons open in Hausdorff subspace \<Rightarrow> disconnected.\<close>
      have "C2 \<noteq> {p, q}"
      proof
        assume "C2 = {p, q}"
        have "{p} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {q} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hq_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{p} = {p, q} \<inter> (top1_S2 - {q})" using hpq_ne hp_S2 by auto
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "{q} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {p} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hp_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{q} = {p, q} \<inter> (top1_S2 - {p})" using hpq_ne hq_S2 by auto
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "\<not> top1_connected_on {p, q} (subspace_topology top1_S2 top1_S2_topology {p, q})"
          unfolding top1_connected_on_def
          using \<open>{p} \<in> _\<close> \<open>{q} \<in> _\<close> hpq_ne by (by100 blast)
        thus False using assms(5) \<open>C2 = {p, q}\<close> by simp
      qed
      moreover have "{p, q} \<subseteq> C2" using hpq by (by100 blast)
      ultimately obtain c where "c \<in> C2" "c \<notin> {p, q}"
        by (by100 blast)
      hence "c \<notin> C1" using hpq by (by100 blast)
      hence "c \<in> top1_S2 - C1" using \<open>c \<in> C2\<close> hC2sub by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF
        hTU hU_conn hU_lpc \<open>top1_S2 - C1 \<noteq> {}\<close>])
  qed
  have hV_pc: "top1_path_connected_on (top1_S2 - C2)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2))"
  proof -
    have hV_conn: "top1_connected_on (top1_S2 - C2)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2))"
      using assms(8) unfolding top1_separates_on_def by (by100 blast)
    have hV_open: "top1_S2 - C2 \<in> top1_S2_topology"
      using assms(3) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
    have hV_lpc: "top1_locally_path_connected_on (top1_S2 - C2)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2))"
      by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hV_open])
         (by100 blast)
    have hTV: "is_topology_on (top1_S2 - C2)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2))"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
    have "top1_S2 - C2 \<noteq> {}"
    proof -
      have "C1 \<noteq> {p, q}"
      proof
        assume "C1 = {p, q}"
        have "{p} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {q} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hq_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{p} = {p, q} \<inter> (top1_S2 - {q})" using hpq_ne hp_S2 by auto
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "{q} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {p} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hp_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{q} = {p, q} \<inter> (top1_S2 - {p})" using hpq_ne hq_S2 by auto
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "\<not> top1_connected_on {p, q} (subspace_topology top1_S2 top1_S2_topology {p, q})"
          unfolding top1_connected_on_def
          using \<open>{p} \<in> _\<close> \<open>{q} \<in> _\<close> hpq_ne by (by100 blast)
        thus False using assms(4) \<open>C1 = {p, q}\<close> by simp
      qed
      moreover have "{p, q} \<subseteq> C1" using hpq by (by100 blast)
      ultimately obtain c where "c \<in> C1" "c \<notin> {p, q}"
        by (by100 blast)
      hence "c \<notin> C2" using hpq by (by100 blast)
      hence "c \<in> top1_S2 - C2" using \<open>c \<in> C1\<close> hC1sub by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF
        hTV hV_conn hV_lpc \<open>top1_S2 - C2 \<noteq> {}\<close>])
  qed
  \<comment> \<open>Step 3: Exactly 2 components. \<ge>2 from hsep. \<le>2 needs 63.1(c) + \<pi>_1 \<cong> Z.\<close>
  \<comment> \<open>From \<not> connected, extract a separation into two nonempty open sets.\<close>
  have h_not_conn: "\<not> top1_connected_on (top1_S2 - (C1 \<union> C2))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (C1 \<union> C2)))"
    using hsep unfolding top1_separates_on_def by simp
  have hTsub: "is_topology_on (top1_S2 - (C1 \<union> C2))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (C1 \<union> C2)))"
    by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
  obtain W1 R where hW1R: "W1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (C1 \<union> C2))"
      "R \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (C1 \<union> C2))"
      "W1 \<noteq> {}" "R \<noteq> {}" "W1 \<inter> R = {}" "W1 \<union> R = top1_S2 - (C1 \<union> C2)"
    using h_not_conn hTsub unfolding top1_connected_on_def by blast
  \<comment> \<open>Key claim: R is connected. If not, S^2-(C1\<union>C2) has \<ge>3 components, contradiction.\<close>
  have hR_conn: "top1_connected_on R (subspace_topology top1_S2 top1_S2_topology R)"
  proof (rule ccontr)
    assume "\<not> top1_connected_on R (subspace_topology top1_S2 top1_S2_topology R)"
    \<comment> \<open>R is open in S^2 (it's open in the open subspace S^2-(C1\<union>C2)).\<close>
    have hR_sub: "R \<subseteq> top1_S2 - (C1 \<union> C2)" using hW1R(6) by (by100 blast)
    have hR_open_S2: "R \<in> top1_S2_topology"
    proof -
      obtain W where "W \<in> top1_S2_topology" "R = (top1_S2 - (C1 \<union> C2)) \<inter> W"
        using hW1R(2) unfolding subspace_topology_def by (by100 blast)
      hence "R = W \<inter> (top1_S2 - (C1 \<union> C2))" by (by100 blast)
      thus ?thesis using topology_inter_open[OF hTS2 \<open>W \<in> _\<close> hopen] by simp
    qed
    have hW1_open_S2: "W1 \<in> top1_S2_topology"
    proof -
      obtain W where "W \<in> top1_S2_topology" "W1 = (top1_S2 - (C1 \<union> C2)) \<inter> W"
        using hW1R(1) unfolding subspace_topology_def by (by100 blast)
      hence "W1 = W \<inter> (top1_S2 - (C1 \<union> C2))" by (by100 blast)
      thus ?thesis using topology_inter_open[OF hTS2 \<open>W \<in> _\<close> hopen] by simp
    qed
    have hTR: "is_topology_on R (subspace_topology top1_S2 top1_S2_topology R)"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (use hR_sub hC1sub hC2sub in blast)
    obtain W2 B where hW2B: "W2 \<in> subspace_topology top1_S2 top1_S2_topology R"
        "B \<in> subspace_topology top1_S2 top1_S2_topology R"
        "W2 \<noteq> {}" "B \<noteq> {}" "W2 \<inter> B = {}" "W2 \<union> B = R"
      using \<open>\<not> top1_connected_on R _\<close> hTR unfolding top1_connected_on_def by blast
    \<comment> \<open>Now W1, W2, B are 3 disjoint nonempty open sets covering S^2-(C1\<union>C2).\<close>
    have hW2_sub: "W2 \<subseteq> top1_S2 - (C1 \<union> C2)" using hW2B(6) hR_sub by (by100 blast)
    have hB_sub: "B \<subseteq> top1_S2 - (C1 \<union> C2)" using hW2B(6) hR_sub by (by100 blast)
    have hW1_sub: "W1 \<subseteq> top1_S2 - (C1 \<union> C2)" using hW1R(6) by (by100 blast)
    have hW2_open_S2: "W2 \<in> top1_S2_topology"
    proof -
      obtain W where hW: "W \<in> top1_S2_topology" "W2 = R \<inter> W"
        using hW2B(1) unfolding subspace_topology_def by (by100 blast)
      have "R \<inter> W = W \<inter> R" by (by100 blast)
      hence "W2 = W \<inter> R" using hW(2) by simp
      thus ?thesis using topology_inter_open[OF hTS2 hW(1) hR_open_S2] by simp
    qed
    have hB_open_S2: "B \<in> top1_S2_topology"
    proof -
      obtain W where hW: "W \<in> top1_S2_topology" "B = R \<inter> W"
        using hW2B(2) unfolding subspace_topology_def by (by100 blast)
      have "R \<inter> W = W \<inter> R" by (by100 blast)
      hence "B = W \<inter> R" using hW(2) by simp
      thus ?thesis using topology_inter_open[OF hTS2 hW(1) hR_open_S2] by simp
    qed
    have h3_disj: "W1 \<inter> W2 = {}" "W1 \<inter> B = {}" "W2 \<inter> B = {}"
      using hW1R(5) hW2B(5,6) by (by100 blast)+
    have h3_cover: "W1 \<union> W2 \<union> B = top1_S2 - (C1 \<union> C2)"
      using hW1R(6) hW2B(6) by (by100 blast)
    \<comment> \<open>Set up 63.1 framework: X = S^2-{p,q}, U' = S^2-C1, V' = S^2-C2.
       U' \<inter> V' = S^2-(C1\<union>C2). Decompose as A\<union>B in two ways:
       Way 1: A1 = W1\<union>W2, B1 = B.  Way 2: A2 = W1, B2 = W2\<union>B.\<close>
    let ?X = "top1_S2 - {p} - {q}"
    let ?TX = "subspace_topology top1_S2 top1_S2_topology ?X"
    let ?U = "top1_S2 - C1"
    let ?V = "top1_S2 - C2"
    have hX_eq: "?U \<union> ?V = ?X"
    proof -
      have "?U \<union> ?V = top1_S2 - (C1 \<inter> C2)" by (by100 blast)
      also have "... = top1_S2 - {p, q}" using hpq by simp
      also have "... = ?X" by (by100 blast)
      finally show ?thesis .
    qed
    have hUV_eq: "?U \<inter> ?V = top1_S2 - (C1 \<union> C2)" by (by100 blast)
    have hTX: "is_topology_on ?X ?TX"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
    have hU_open: "openin_on ?X ?TX ?U"
    proof -
      have "?U \<in> top1_S2_topology"
        using assms(2) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
      have "?U \<subseteq> ?X" using hpq hC1sub by (by100 blast)
      have "?U \<in> ?TX" unfolding subspace_topology_def using \<open>?U \<in> _\<close> \<open>?U \<subseteq> ?X\<close> by (by100 blast)
      thus ?thesis unfolding openin_on_def using \<open>?U \<subseteq> ?X\<close> by (by100 blast)
    qed
    have hV_open: "openin_on ?X ?TX ?V"
    proof -
      have "?V \<in> top1_S2_topology"
        using assms(3) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
      have "?V \<subseteq> ?X" using hpq hC2sub by (by100 blast)
      have "?V \<in> ?TX" unfolding subspace_topology_def using \<open>?V \<in> _\<close> \<open>?V \<subseteq> ?X\<close> by (by100 blast)
      thus ?thesis unfolding openin_on_def using \<open>?V \<subseteq> ?X\<close> by (by100 blast)
    qed
    \<comment> \<open>Subspace topology transitivity: U \<subseteq> X \<subseteq> S^2, so subspace of X on U = subspace of S^2 on U.\<close>
    have hU_sub_X: "?U \<subseteq> ?X" using hpq hC1sub by (by100 blast)
    have hV_sub_X: "?V \<subseteq> ?X" using hpq hC2sub by (by100 blast)
    have hU_subtop: "subspace_topology ?X ?TX ?U = subspace_topology top1_S2 top1_S2_topology ?U"
      by (rule subspace_topology_trans[OF hU_sub_X])
    have hV_subtop: "subspace_topology ?X ?TX ?V = subspace_topology top1_S2 top1_S2_topology ?V"
      by (rule subspace_topology_trans[OF hV_sub_X])
    \<comment> \<open>All three sets are open in X (they're open in S^2 and contained in X).\<close>
    have hW1_X: "W1 \<subseteq> ?X" using hW1_sub hpq by (by100 blast)
    have hW2_X: "W2 \<subseteq> ?X" using hW2_sub hpq by (by100 blast)
    have hB_X: "B \<subseteq> ?X" using hB_sub hpq by (by100 blast)
    have hW1_open_X: "openin_on ?X ?TX W1"
      unfolding openin_on_def using hW1_X hW1_open_S2
      unfolding subspace_topology_def by (by100 blast)
    have hW2_open_X: "openin_on ?X ?TX W2"
      unfolding openin_on_def using hW2_X hW2_open_S2
      unfolding subspace_topology_def by (by100 blast)
    have hB_open_X: "openin_on ?X ?TX B"
      unfolding openin_on_def using hB_X hB_open_S2
      unfolding subspace_topology_def by (by100 blast)
    \<comment> \<open>Decomposition 1: A1 = W1\<union>W2, B1 = B for loop f = \<alpha>*\<beta>.\<close>
    define A1 where "A1 = W1 \<union> W2"
    define B1 where "B1 = B"
    have hA1B1_eq: "?U \<inter> ?V = A1 \<union> B1"
    proof -
      have "A1 \<union> B1 = W1 \<union> W2 \<union> B" unfolding A1_def B1_def by (by100 blast)
      also have "... = top1_S2 - (C1 \<union> C2)" using h3_cover by simp
      also have "... = ?U \<inter> ?V" using hUV_eq by simp
      finally show ?thesis by simp
    qed
    have hA1B1_disj: "A1 \<inter> B1 = {}" unfolding A1_def B1_def
      using h3_disj by (by100 blast)
    have hA1_open: "openin_on ?X ?TX A1"
    proof -
      have hW1T: "W1 \<in> ?TX" using hW1_open_X unfolding openin_on_def by (by100 blast)
      have hW2T: "W2 \<in> ?TX" using hW2_open_X unfolding openin_on_def by (by100 blast)
      have "W1 \<union> W2 \<in> ?TX" by (rule topology_union2[OF hTX hW1T hW2T])
      thus ?thesis unfolding A1_def openin_on_def using hW1_X hW2_X by (by100 blast)
    qed
    have hB1_open: "openin_on ?X ?TX B1" unfolding B1_def using hB_open_X by simp
    \<comment> \<open>Pick a \<in> W1 \<subseteq> A1 and b \<in> B1 = B.\<close>
    obtain a where ha: "a \<in> W1" using hW1R(3) by (by100 blast)
    obtain b where hb: "b \<in> B" using hW2B(4) by (by100 blast)
    have ha_A1: "a \<in> A1" unfolding A1_def using ha by (by100 blast)
    have hb_B1: "b \<in> B1" unfolding B1_def using hb by simp
    have ha_X: "a \<in> ?X" using ha hW1_X by (by100 blast)
    have hb_X: "b \<in> ?X" using hb hB_X by (by100 blast)
    \<comment> \<open>Paths: \<alpha> from a to b in U (= S^2-C1), \<beta> from b to a in V (= S^2-C2).
       These exist because U and V are path-connected.\<close>
    have ha_U: "a \<in> ?U" using ha hW1_sub by (by100 blast)
    have hb_U: "b \<in> ?U" using hb hB_sub by (by100 blast)
    have ha_V: "a \<in> ?V" using ha hW1_sub by (by100 blast)
    have hb_V: "b \<in> ?V" using hb hB_sub by (by100 blast)
    obtain \<alpha> where h\<alpha>: "top1_is_path_on ?U
        (subspace_topology top1_S2 top1_S2_topology ?U) a b \<alpha>"
      using hU_pc ha_U hb_U unfolding top1_path_connected_on_def by (by100 blast)
    obtain \<beta> where h\<beta>: "top1_is_path_on ?V
        (subspace_topology top1_S2 top1_S2_topology ?V) b a \<beta>"
      using hV_pc hb_V ha_V unfolding top1_path_connected_on_def by (by100 blast)
    \<comment> \<open>f = \<alpha>*\<beta> is nontrivial by 63.1(a).\<close>
    have hf_nontrivial: "\<not> top1_path_homotopic_on ?X ?TX a a
        (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
    proof (rule Theorem_63_1_loop_nontrivial[OF hTX hU_open hV_open hX_eq
        hA1B1_eq hA1B1_disj hA1_open hB1_open ha_A1 hb_B1])
      \<comment> \<open>Need paths in subspace of X restricted to U and V.\<close>
      show "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a b \<alpha>"
        using h\<alpha> hU_subtop by simp
      show "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) b a \<beta>"
        using h\<beta> hV_subtop by simp
    qed
    \<comment> \<open>Decomposition 2: A2 = W1, B2 = W2\<union>B for loop g = \<gamma>*\<delta>.\<close>
    define A2 where "A2 = W1"
    define B2 where "B2 = W2 \<union> B"
    have hA2B2_eq: "?U \<inter> ?V = A2 \<union> B2"
    proof -
      have "A2 \<union> B2 = W1 \<union> (W2 \<union> B)" unfolding A2_def B2_def by (by100 blast)
      also have "... = W1 \<union> W2 \<union> B" by (by100 blast)
      also have "... = top1_S2 - (C1 \<union> C2)" using h3_cover by simp
      also have "... = ?U \<inter> ?V" using hUV_eq by simp
      finally show ?thesis by simp
    qed
    have hA2B2_disj: "A2 \<inter> B2 = {}" unfolding A2_def B2_def
      using h3_disj by (by100 blast)
    have hA2_open: "openin_on ?X ?TX A2" unfolding A2_def using hW1_open_X by simp
    have hB2_open: "openin_on ?X ?TX B2"
    proof -
      have hW2T: "W2 \<in> ?TX" using hW2_open_X unfolding openin_on_def by (by100 blast)
      have hBT: "B \<in> ?TX" using hB_open_X unfolding openin_on_def by (by100 blast)
      have "W2 \<union> B \<in> ?TX" by (rule topology_union2[OF hTX hW2T hBT])
      thus ?thesis unfolding B2_def openin_on_def using hW2_X hB_X by (by100 blast)
    qed
    \<comment> \<open>Pick a \<in> W1 = A2 (same a), a' \<in> W2 \<subseteq> B2.\<close>
    obtain a' where ha': "a' \<in> W2" using hW2B(3) by (by100 blast)
    have ha_A2: "a \<in> A2" unfolding A2_def using ha by simp
    have ha'_B2: "a' \<in> B2" unfolding B2_def using ha' by (by100 blast)
    have ha'_X: "a' \<in> ?X" using ha' hW2_X by (by100 blast)
    have ha'_U: "a' \<in> ?U" using ha' hW2_sub by (by100 blast)
    have ha'_V: "a' \<in> ?V" using ha' hW2_sub by (by100 blast)
    obtain \<gamma> where h\<gamma>: "top1_is_path_on ?U
        (subspace_topology top1_S2 top1_S2_topology ?U) a a' \<gamma>"
      using hU_pc ha_U ha'_U unfolding top1_path_connected_on_def by (by100 blast)
    obtain \<delta> where h\<delta>: "top1_is_path_on ?V
        (subspace_topology top1_S2 top1_S2_topology ?V) a' a \<delta>"
      using hV_pc ha'_V ha_V unfolding top1_path_connected_on_def by (by100 blast)
    \<comment> \<open>g = \<gamma>*\<delta> is nontrivial by 63.1(a) with decomposition A2, B2.\<close>
    have hg_nontrivial: "\<not> top1_path_homotopic_on ?X ?TX a a
        (top1_path_product \<gamma> \<delta>) (top1_constant_path a)"
    proof (rule Theorem_63_1_loop_nontrivial[OF hTX hU_open hV_open hX_eq
        hA2B2_eq hA2B2_disj hA2_open hB2_open ha_A2 ha'_B2])
      show "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a a' \<gamma>"
        using h\<gamma> hU_subtop by simp
      show "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) a' a \<delta>"
        using h\<delta> hV_subtop by simp
    qed
    \<comment> \<open>By \<pi>_1(X) \<cong> Z and both [f],[g] nontrivial: \<exists> m>0, k. [f]^m = [g]^k.\<close>
    have h\<alpha>_X: "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a b \<alpha>"
      using h\<alpha> hU_subtop by simp
    have h\<beta>_X: "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) b a \<beta>"
      using h\<beta> hV_subtop by simp
    have h\<gamma>_X: "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a a' \<gamma>"
      using h\<gamma> hU_subtop by simp
    have h\<delta>_X: "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) a' a \<delta>"
      using h\<delta> hV_subtop by simp
    \<comment> \<open>Paths in U (or V) restricted to X: since U \<subseteq> X, a path in U is a path in X.\<close>
    have h_path_U_to_X: "\<And>a' b' f. top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a' b' f
        \<Longrightarrow> top1_is_path_on ?X ?TX a' b' f"
    proof -
      fix a' b' f assume hf: "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a' b' f"
      show "top1_is_path_on ?X ?TX a' b' f"
        unfolding top1_is_path_on_def top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix s assume hs: "s \<in> I_set"
        have "f s \<in> ?U" using hf hs unfolding top1_is_path_on_def top1_continuous_map_on_def
          by (by100 blast)
        thus "f s \<in> ?X" using hU_sub_X by (by100 blast)
      next
        fix W assume hW: "W \<in> ?TX"
        have hUW_sub: "?U \<inter> W \<in> subspace_topology ?X ?TX ?U"
        proof -
          have "?U \<inter> W = ?U \<inter> W" by simp
          moreover have "W \<in> ?TX" by (rule hW)
          ultimately show ?thesis unfolding subspace_topology_def by blast
        qed
        have h_pre: "{s \<in> I_set. f s \<in> ?U \<inter> W} \<in> I_top"
          using hf hUW_sub
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        have h_in_U: "\<forall>s\<in>I_set. f s \<in> ?U"
          using hf unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        have "{s \<in> I_set. f s \<in> W} = {s \<in> I_set. f s \<in> ?U \<inter> W}"
          using h_in_U by (by100 blast)
        thus "{s \<in> I_set. f s \<in> W} \<in> I_top" using h_pre by simp
      next
        show "f 0 = a'" using hf unfolding top1_is_path_on_def by (by100 blast)
      next
        show "f 1 = b'" using hf unfolding top1_is_path_on_def by (by100 blast)
      qed
    qed
    have h_path_V_to_X: "\<And>a' b' f. top1_is_path_on ?V (subspace_topology ?X ?TX ?V) a' b' f
        \<Longrightarrow> top1_is_path_on ?X ?TX a' b' f"
    proof -
      fix a' b' f assume hf: "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) a' b' f"
      show "top1_is_path_on ?X ?TX a' b' f"
        unfolding top1_is_path_on_def top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix s assume hs: "s \<in> I_set"
        have "f s \<in> ?V" using hf hs unfolding top1_is_path_on_def top1_continuous_map_on_def
          by (by100 blast)
        thus "f s \<in> ?X" using hV_sub_X by (by100 blast)
      next
        fix W assume hW: "W \<in> ?TX"
        have hVW_sub: "?V \<inter> W \<in> subspace_topology ?X ?TX ?V"
        proof -
          have "?V \<inter> W = ?V \<inter> W" by simp
          moreover have "W \<in> ?TX" by (rule hW)
          ultimately show ?thesis unfolding subspace_topology_def by blast
        qed
        have h_pre: "{s \<in> I_set. f s \<in> ?V \<inter> W} \<in> I_top"
          using hf hVW_sub
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        have h_in_V: "\<forall>s\<in>I_set. f s \<in> ?V"
          using hf unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        have "{s \<in> I_set. f s \<in> W} = {s \<in> I_set. f s \<in> ?V \<inter> W}"
          using h_in_V by (by100 blast)
        thus "{s \<in> I_set. f s \<in> W} \<in> I_top" using h_pre by simp
      next
        show "f 0 = a'" using hf unfolding top1_is_path_on_def by (by100 blast)
      next
        show "f 1 = b'" using hf unfolding top1_is_path_on_def by (by100 blast)
      qed
    qed
    have hf_loop: "top1_is_loop_on ?X ?TX a (top1_path_product \<alpha> \<beta>)"
    proof -
      have h\<alpha>_path_X: "top1_is_path_on ?X ?TX a b \<alpha>" by (rule h_path_U_to_X[OF h\<alpha>_X])
      have h\<beta>_path_X: "top1_is_path_on ?X ?TX b a \<beta>" by (rule h_path_V_to_X[OF h\<beta>_X])
      show ?thesis unfolding top1_is_loop_on_def
        using top1_path_product_is_path[OF hTX h\<alpha>_path_X h\<beta>_path_X] by (by100 blast)
    qed
    have hg_loop: "top1_is_loop_on ?X ?TX a (top1_path_product \<gamma> \<delta>)"
    proof -
      have h\<gamma>_path_X: "top1_is_path_on ?X ?TX a a' \<gamma>" by (rule h_path_U_to_X[OF h\<gamma>_X])
      have h\<delta>_path_X: "top1_is_path_on ?X ?TX a' a \<delta>" by (rule h_path_V_to_X[OF h\<delta>_X])
      show ?thesis unfolding top1_is_loop_on_def
        using top1_path_product_is_path[OF hTX h\<gamma>_path_X h\<delta>_path_X] by (by100 blast)
    qed
    have hpi1_cyclic: "\<exists>gen. top1_is_loop_on ?X ?TX a gen \<and>
        (\<forall>h. top1_is_loop_on ?X ?TX a h \<longrightarrow>
          (\<exists>n::nat. top1_path_homotopic_on ?X ?TX a a h (top1_path_power gen a n) \<or>
           top1_path_homotopic_on ?X ?TX a a h (top1_path_power (top1_path_reverse gen) a n)))"
    proof -
      have "a \<in> ?X" using ha hW1_X by (by100 blast)
      thus ?thesis by (rule pi1_S2_minus_two_points_infinite_cyclic[OF assms(1) hp_S2 hq_S2 hpq_ne])
    qed
    obtain m k where hm: "m > 0" and hmk:
        "top1_path_homotopic_on ?X ?TX a a
          (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
          (top1_path_power (top1_path_product \<gamma> \<delta>) a k) \<or>
         top1_path_homotopic_on ?X ?TX a a
          (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
          (top1_path_power (top1_path_reverse (top1_path_product \<gamma> \<delta>)) a k)"
      using infinite_cyclic_common_power[OF hTX hf_loop hg_loop
        hf_nontrivial hg_nontrivial hpi1_cyclic] by (by100 blast)
    \<comment> \<open>By 63.1(c): m must be 0. But m > 0. Contradiction!\<close>
    \<comment> \<open>For 63.1(c), we use decomposition 1 (A1, B1) for \<alpha>*\<beta>, and a' \<in> A1 for \<gamma>*\<delta>.
       In the reverse case, use \<delta>\<inverse>*\<gamma>\<inverse> instead of \<gamma>*\<delta>, with same 63.1(c).\<close>
    have ha'_A1: "a' \<in> A1" unfolding A1_def using ha' by (by100 blast)
    have "m = 0" using hmk
    proof
      assume hmk1: "top1_path_homotopic_on ?X ?TX a a
          (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
          (top1_path_power (top1_path_product \<gamma> \<delta>) a k)"
      show "m = 0"
        by (rule Theorem_63_1_c_subgroups_trivial[OF hTX hU_open hV_open hX_eq
          hA1B1_eq hA1B1_disj hA1_open hB1_open ha_A1 hb_B1
          h\<alpha>_X h\<beta>_X ha'_A1 h\<gamma>_X h\<delta>_X hmk1])
    next
      assume hmk2: "top1_path_homotopic_on ?X ?TX a a
          (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
          (top1_path_power (top1_path_reverse (top1_path_product \<gamma> \<delta>)) a k)"
      \<comment> \<open>g\<inverse> = (\<gamma>*\<delta>)\<inverse> = \<delta>\<inverse>*\<gamma>\<inverse>: path from a to a' (reversed) in V then U.
         Apply 63.1(c) with \<gamma>' = \<delta>\<inverse> (in V from a to a') and \<delta>' = \<gamma>\<inverse> (in U from a' to a).
         Note: a' \<in> A1, same decomposition. Need paths in correct subspaces.\<close>
      show "m = 0"
        by (rule Theorem_63_1_c_subgroups_trivial_reverse[OF hTX hU_open hV_open hX_eq
          hA1B1_eq hA1B1_disj hA1_open hB1_open ha_A1 hb_B1
          h\<alpha>_X h\<beta>_X ha'_A1 h\<gamma>_X h\<delta>_X hmk2])
    qed
    thus False using hm by simp
  qed
  \<comment> \<open>Now construct the two connected components.\<close>
  have hW1_conn: "top1_connected_on W1 (subspace_topology top1_S2 top1_S2_topology W1)"
  proof (rule ccontr)
    assume "\<not> top1_connected_on W1 (subspace_topology top1_S2 top1_S2_topology W1)"
    \<comment> \<open>Symmetric to hR_conn: W1 splits into W1a, W1b, giving 3 components {W1a, W1b, R}.\<close>
    have hW1_open_S2: "W1 \<in> top1_S2_topology"
    proof -
      obtain W where "W \<in> top1_S2_topology" "W1 = (top1_S2 - (C1 \<union> C2)) \<inter> W"
        using hW1R(1) unfolding subspace_topology_def by (by100 blast)
      hence "W1 = W \<inter> (top1_S2 - (C1 \<union> C2))" by (by100 blast)
      thus ?thesis using topology_inter_open[OF hTS2 \<open>W \<in> _\<close> hopen] by simp
    qed
    have hTW1: "is_topology_on W1 (subspace_topology top1_S2 top1_S2_topology W1)"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (use hW1R(6) in blast)
    obtain W1a W1b where hWab: "W1a \<in> subspace_topology top1_S2 top1_S2_topology W1"
        "W1b \<in> subspace_topology top1_S2 top1_S2_topology W1"
        "W1a \<noteq> {}" "W1b \<noteq> {}" "W1a \<inter> W1b = {}" "W1a \<union> W1b = W1"
      using \<open>\<not> top1_connected_on W1 _\<close> hTW1 unfolding top1_connected_on_def by blast
    \<comment> \<open>W1a, W1b are open in S^2 (open in open set = open).\<close>
    have hW1a_open_S2: "W1a \<in> top1_S2_topology"
    proof -
      obtain V where hV: "V \<in> top1_S2_topology" "W1a = W1 \<inter> V"
        using hWab(1) unfolding subspace_topology_def by (by100 blast)
      thus ?thesis using topology_inter_open[OF hTS2 hW1_open_S2 hV(1)] by (by100 blast)
    qed
    have hW1b_open_S2: "W1b \<in> top1_S2_topology"
    proof -
      obtain V where hV: "V \<in> top1_S2_topology" "W1b = W1 \<inter> V"
        using hWab(2) unfolding subspace_topology_def by (by100 blast)
      thus ?thesis using topology_inter_open[OF hTS2 hW1_open_S2 hV(1)] by (by100 blast)
    qed
    have hR_open_S2: "R \<in> top1_S2_topology"
    proof -
      obtain V where "V \<in> top1_S2_topology" "R = (top1_S2 - (C1 \<union> C2)) \<inter> V"
        using hW1R(2) unfolding subspace_topology_def by (by100 blast)
      hence "R = V \<inter> (top1_S2 - (C1 \<union> C2))" by (by100 blast)
      thus ?thesis using topology_inter_open[OF hTS2 \<open>V \<in> _\<close> hopen] by simp
    qed
    have h3_disj: "W1a \<inter> W1b = {}" "W1a \<inter> R = {}" "W1b \<inter> R = {}"
      using hWab(5,6) hW1R(5) by (by100 blast)+
    have h3_cover: "W1a \<union> W1b \<union> R = top1_S2 - (C1 \<union> C2)"
      using hWab(6) hW1R(6) by (by100 blast)
    have hR_ne: "R \<noteq> {}" by (rule hW1R(4))
    show False by (rule three_components_contradiction[OF assms(1-8)
        hW1a_open_S2 hW1b_open_S2 hR_open_S2 hWab(3,4) hR_ne h3_disj h3_cover])
  qed
  show ?thesis
  proof (intro exI conjI)
    show "W1 \<noteq> {}" by (rule hW1R(3))
    show "R \<noteq> {}" by (rule hW1R(4))
    show "W1 \<inter> R = {}" by (rule hW1R(5))
    show "W1 \<union> R = top1_S2 - (C1 \<union> C2)" by (rule hW1R(6))
    show "top1_connected_on W1 (subspace_topology top1_S2 top1_S2_topology W1)"
      by (rule hW1_conn)
    show "top1_connected_on R (subspace_topology top1_S2 top1_S2_topology R)"
      by (rule hR_conn)
  qed
qed

\<comment> \<open>Helper: cos a = cos b and sin a = sin b implies a = b + 2k\<pi>.\<close>
lemma cos_sin_eq_imp:
  assumes "cos a = cos b" "sin a = sin b"
  shows "\<exists>k::int. a - b = real_of_int k * 2 * pi"
proof -
  have "cos (a - b) = cos a * cos b + sin a * sin b" by (rule cos_diff)
  also have "\<dots> = cos b * cos b + sin b * sin b" using assms by simp
  also have "\<dots> = 1" using sin_cos_squared_add3[of b] by linarith
  finally have "cos (a - b) = 1" .
  thus ?thesis using cos_one_2pi_int by simp
qed

\<comment> \<open>Corollary: if |a - b| < 2\<pi> then a = b.\<close>
lemma cos_sin_eq_small_diff:
  assumes "cos a = cos b" "sin a = sin b" "\<bar>a - b\<bar> < 2 * pi"
  shows "a = b"
proof -
  obtain k :: int where hk: "a - b = real_of_int k * 2 * pi"
    using cos_sin_eq_imp[OF assms(1,2)] by (by100 blast)
  have "\<bar>real_of_int k * 2 * pi\<bar> < 2 * pi"
    using hk assms(3) by simp
  hence "\<bar>real_of_int k\<bar> * (2 * pi) < 2 * pi"
    by (simp add: abs_mult abs_of_nonneg[OF pi_ge_zero])
  hence "\<bar>real_of_int k\<bar> < 1" using pi_gt_zero by simp
  hence "k = 0" by auto
  thus "a = b" using hk by simp
qed

\<comment> \<open>Flexible arc decomposition: given SCC C' and open V with x \<in> V \<inter> C',
   decompose C' = C1 \<union> C2 with C1 \<subseteq> V, both arcs.\<close>
lemma flexible_arc_decomposition:
  assumes hTS: "is_topology_on_strict top1_S2 top1_S2_topology"
  and hSCC: "top1_simple_closed_curve_on top1_S2 top1_S2_topology C'"
  and hV: "V \<in> top1_S2_topology" and hx: "x \<in> C'" and hxV: "x \<in> V"
  shows "\<exists>C1 C2 a b. C' = C1 \<union> C2 \<and> C1 \<inter> C2 = {a, b} \<and> a \<noteq> b
    \<and> top1_is_arc_on C1 (subspace_topology top1_S2 top1_S2_topology C1)
    \<and> top1_is_arc_on C2 (subspace_topology top1_S2 top1_S2_topology C2)
    \<and> C1 \<subseteq> V"
proof -
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using hTS unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>Step 1: f: S^1 \<rightarrow> C' homeomorphism from SCC definition.\<close>
  obtain f where hf_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S2 top1_S2_topology f"
      and hf_inj: "inj_on f top1_S1" and hf_img: "f ` top1_S1 = C'"
  proof -
    obtain f where "top1_continuous_map_on top1_S1 top1_S1_topology top1_S2 top1_S2_topology f"
        "inj_on f top1_S1" "f ` top1_S1 = C'"
      using hSCC unfolding top1_simple_closed_curve_on_def by (by100 blast)
    thus ?thesis using that by (by100 blast)
  qed
  have hC'_sub: "C' \<subseteq> top1_S2"
    using hSCC unfolding top1_simple_closed_curve_on_def top1_continuous_map_on_def
    by (by100 blast)
  \<comment> \<open>f: S^1 \<rightarrow> C' is a homeomorphism (compact to Hausdorff continuous bijection).\<close>
  have hf_bij: "bij_betw f top1_S1 C'" using hf_inj hf_img unfolding bij_betw_def by simp
  have hf_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology C'
      (subspace_topology top1_S2 top1_S2_topology C') f"
  proof -
    have hf_cont_C': "top1_continuous_map_on top1_S1 top1_S1_topology C'
        (subspace_topology top1_S2 top1_S2_topology C') f"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume "x \<in> top1_S1" thus "f x \<in> C'" using hf_img by (by100 blast)
    next
      fix U assume "U \<in> subspace_topology top1_S2 top1_S2_topology C'"
      then obtain W where hW: "W \<in> top1_S2_topology" "U = C' \<inter> W"
        unfolding subspace_topology_def by (by100 blast)
      have "{x \<in> top1_S1. f x \<in> U} = {x \<in> top1_S1. f x \<in> W}"
        using hf_img hW(2) by (by100 blast)
      also have "\<dots> \<in> top1_S1_topology"
        using hf_cont hW(1) unfolding top1_continuous_map_on_def by (by100 blast)
      finally show "{x \<in> top1_S1. f x \<in> U} \<in> top1_S1_topology" .
    qed
    have hS1_compact: "top1_compact_on top1_S1 top1_S1_topology" by (rule S1_compact)
    have hC'_haus: "is_hausdorff_on C' (subspace_topology top1_S2 top1_S2_topology C')"
      by (rule hausdorff_subspace[OF top1_S2_is_hausdorff hC'_sub])
    show ?thesis
    proof (rule Theorem_26_6[OF is_topology_on_strict_imp[OF top1_S1_is_topology_on_strict]
              _ hS1_compact hC'_haus hf_cont_C' hf_bij])
      show "is_topology_on C' (subspace_topology top1_S2 top1_S2_topology C')"
        by (rule subspace_topology_is_topology_on[OF hTS2]) (use hC'_sub in blast)
    qed
  qed
  \<comment> \<open>Step 2: f\<inverse>(V \<inter> C') open in S^1, contains f\<inverse>(x).\<close>
  define finv where "finv = inv_into top1_S1 f"
  have hfinv_bij: "bij_betw finv C' top1_S1" unfolding finv_def
    by (rule bij_betw_inv_into[OF hf_bij])
  have hfinv_cont: "top1_continuous_map_on C' (subspace_topology top1_S2 top1_S2_topology C')
      top1_S1 top1_S1_topology finv"
    using hf_homeo unfolding top1_homeomorphism_on_def finv_def by (by100 blast)
  have hp: "finv x \<in> top1_S1" using hx hfinv_bij unfolding bij_betw_def by (by100 blast)
  \<comment> \<open>Preimage of V \<inter> C' under finv\<inverse> = f\<inverse>(V) \<inter> S^1, open in S^1.\<close>
  have hVC'_open: "V \<inter> C' \<in> subspace_topology top1_S2 top1_S2_topology C'"
    using hV unfolding subspace_topology_def by (by100 blast)
  \<comment> \<open>finv(V\<inter>C') open in S^1: follows from f being an open map (homeomorphism).\<close>
  have hfinv_VC'_open: "finv ` (V \<inter> C') \<in> top1_S1_topology"
  proof -
    \<comment> \<open>finv: C' \<rightarrow> S^1 is continuous. V\<inter>C' open in C' subspace. Preimage = image since finv continuous.\<close>
    \<comment> \<open>Actually: f is a homeomorphism C'\<cong>S^1, so f\<inverse> maps open sets to open sets.\<close>
    \<comment> \<open>f maps open sets in S^1 to open sets in C' (f is an open map).\<close>
    \<comment> \<open>So finv maps open sets in C' to open sets in S^1 (since finv = f\<inverse>, open map \<leftrightarrow> inverse continuous).\<close>
    have "\<And>U. U \<in> subspace_topology top1_S2 top1_S2_topology C' \<Longrightarrow>
        finv ` U \<in> top1_S1_topology"
    proof -
      fix U assume hU: "U \<in> subspace_topology top1_S2 top1_S2_topology C'"
      \<comment> \<open>finv ` U = {finv y | y \<in> U} = {t \<in> S^1 | f t \<in> U} (since finv(y) \<in> S^1 and f(finv(y))=y).\<close>
      have hfinv_U_eq: "finv ` U = {t \<in> top1_S1. f t \<in> U}"
      proof (intro set_eqI iffI)
        fix t assume "t \<in> finv ` U"
        then obtain y where hy: "y \<in> U" "t = finv y" by (by100 blast)
        have "y \<in> C'" using hy(1) hU unfolding subspace_topology_def by (by100 blast)
        have "t \<in> top1_S1" using hy(2) hfinv_bij \<open>y \<in> C'\<close>
          unfolding bij_betw_def by (by100 blast)
        moreover have "f t = y"
        proof -
          have "y \<in> f ` top1_S1" using hf_img \<open>y \<in> C'\<close> by simp
          hence "f (inv_into top1_S1 f y) = y" by (rule f_inv_into_f)
          thus ?thesis using hy(2) unfolding finv_def by simp
        qed
        ultimately show "t \<in> {t \<in> top1_S1. f t \<in> U}" using hy(1) by simp
      next
        fix t assume ht: "t \<in> {t \<in> top1_S1. f t \<in> U}"
        hence "t \<in> top1_S1" "f t \<in> U" by auto
        have "finv (f t) = t" unfolding finv_def
          by (rule inv_into_f_f[OF bij_betw_imp_inj_on[OF hf_bij] \<open>t \<in> top1_S1\<close>])
        thus "t \<in> finv ` U" using \<open>f t \<in> U\<close> by (by100 force)
      qed
      have "{t \<in> top1_S1. f t \<in> U} \<in> top1_S1_topology"
      proof -
        have hf_cont_C'2: "top1_continuous_map_on top1_S1 top1_S1_topology C'
            (subspace_topology top1_S2 top1_S2_topology C') f"
          using hf_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        thus ?thesis using hU unfolding top1_continuous_map_on_def by (by100 blast)
      qed
      thus "finv ` U \<in> top1_S1_topology" using hfinv_U_eq by simp
    qed
    thus ?thesis using hVC'_open by simp
  qed
  have hp_in_VC': "finv x \<in> finv ` (V \<inter> C')" using hx hxV by (by100 blast)
  \<comment> \<open>Step 3: Choose \<epsilon> > 0 so that the arc of width 2\<epsilon> around finv(x) on S^1 maps into V.\<close>
  \<comment> \<open>finv(x) = (cos \<theta>, sin \<theta>) for some \<theta>. Open set in S^1 \<Rightarrow> \<exists>\<epsilon>. B(\<epsilon>,finv(x))\<inter>S^1 \<subseteq> preimage.\<close>
  obtain \<theta> where h\<theta>: "finv x = (cos \<theta>, sin \<theta>)" and h\<theta>_range: "\<theta> \<in> {0..<2*pi}"
  proof -
    have hp_S1: "finv x \<in> top1_S1" by (rule hp)
    hence "fst (finv x) ^ 2 + snd (finv x) ^ 2 = 1"
      unfolding top1_S1_def by simp
    obtain t :: real where ht: "finv x = (cos (2*pi*t), sin (2*pi*t))"
    proof -
      have "(finv x) \<in> top1_R_to_S1 ` UNIV"
      proof -
        obtain a b :: real where hab: "finv x = (a, b)" "a^2 + b^2 = 1"
          using hp_S1 unfolding top1_S1_def by (by100 force)
        have ha_range: "a \<in> {-1..1}"
        proof -
          have "a^2 \<le> a^2 + b^2" by simp
          hence "a^2 \<le> 1" using hab(2) by linarith
          have "a \<le> 1" using power2_le_imp_le[of a 1] \<open>a^2 \<le> 1\<close> by simp
          moreover have "-1 \<le> a"
          proof -
            have "(-a)^2 = a^2" by (simp add: power2_eq_square)
            hence "(-a)^2 \<le> 1" using \<open>a^2 \<le> 1\<close> by simp
            hence "-a \<le> 1" using power2_le_imp_le[of "-a" 1] by simp
            thus ?thesis by linarith
          qed
          ultimately have "\<bar>a\<bar> \<le> 1" by simp
          thus ?thesis by auto
        qed
        define t where "t = (if b \<ge> 0 then arccos a else 2*pi - arccos a)"
        have "cos t = a"
          unfolding t_def using ha_range by (simp add: cos_arccos)
        moreover have "sin t = b"
        proof (cases "b \<ge> 0")
          case True
          hence "t = arccos a" unfolding t_def by simp
          have "sin (arccos a) = sqrt (1 - a^2)" using ha_range by (intro sin_arccos) auto
          also have "1 - a^2 = b^2" using hab(2) by linarith
          finally have "sin (arccos a) = \<bar>b\<bar>" using real_sqrt_abs by simp
          thus ?thesis using True \<open>t = arccos a\<close> by simp
        next
          case False
          hence "t = 2*pi - arccos a" unfolding t_def by simp
          have "sin (2*pi - arccos a) = - sin (arccos a)" by (simp add: sin_diff)
          also have "sin (arccos a) = sqrt (1 - a^2)" using ha_range by (intro sin_arccos) auto
          also have "1 - a^2 = b^2" using hab(2) by linarith
          finally have "sin (2*pi - arccos a) = - \<bar>b\<bar>" using real_sqrt_abs by simp
          thus ?thesis using False \<open>t = 2*pi - arccos a\<close> by simp
        qed
        ultimately have "finv x = (cos t, sin t)" using hab(1) by simp
        hence "finv x = top1_R_to_S1 (t / (2*pi))"
          unfolding top1_R_to_S1_def by simp
        thus ?thesis by (by100 blast)
      qed
      then obtain t :: real where "finv x = top1_R_to_S1 t" by (by100 blast)
      hence "finv x = (cos (2*pi*t), sin (2*pi*t))" unfolding top1_R_to_S1_def by simp
      thus ?thesis using that by (by100 blast)
    qed
    define \<theta>' where "\<theta>' = 2*pi*(t - of_int \<lfloor>t\<rfloor>)"
    have h\<theta>'_range: "\<theta>' \<ge> 0 \<and> \<theta>' < 2*pi"
    proof
      have "t - of_int \<lfloor>t\<rfloor> \<ge> 0" by linarith
      thus "\<theta>' \<ge> 0" unfolding \<theta>'_def using pi_gt_zero by (simp add: mult_nonneg_nonneg)
      have "t - of_int \<lfloor>t\<rfloor> < 1" by linarith
      hence "2*pi*(t - of_int \<lfloor>t\<rfloor>) < 2*pi*1" using pi_gt_zero
        by (simp add: mult_strict_left_mono)
      thus "\<theta>' < 2*pi" unfolding \<theta>'_def by simp
    qed
    have "cos \<theta>' = cos (2*pi*t)" and "sin \<theta>' = sin (2*pi*t)"
    proof -
      have hd: "\<theta>' = 2*pi*t - of_int \<lfloor>t\<rfloor> * (2 * pi)" unfolding \<theta>'_def by (simp add: algebra_simps)
      have hcos_k: "cos (of_int \<lfloor>t\<rfloor> * (2 * pi)) = 1"
        using cos_integer_2pi[of "of_int \<lfloor>t\<rfloor>"] by (simp add: algebra_simps)
      have hsin_k: "sin (of_int \<lfloor>t\<rfloor> * (2 * pi)) = 0"
        using sin_integer_2pi[of "of_int \<lfloor>t\<rfloor>"] by (simp add: algebra_simps)
      show "cos \<theta>' = cos (2*pi*t)" unfolding hd using hcos_k hsin_k
        by (simp add: cos_diff)
      show "sin \<theta>' = sin (2*pi*t)" unfolding hd using hcos_k hsin_k
        by (simp add: sin_diff)
    qed
    hence "finv x = (cos \<theta>', sin \<theta>')" using ht by simp
    thus ?thesis using that h\<theta>'_range by auto
  qed
  obtain \<epsilon> :: real where h\<epsilon>: "\<epsilon> > 0" "\<epsilon> < pi"
      and h_arc_sub: "\<And>t. t \<in> {\<theta>-\<epsilon>..\<theta>+\<epsilon>} \<Longrightarrow> (cos t, sin t) \<in> finv ` (V \<inter> C')"
  proof -
    \<comment> \<open>finv(V\<inter>C') open in S^1 topology. S^1 topology = subspace of R^2 euclidean.\<close>
    \<comment> \<open>So \<exists> open W in R^2 with (cos \<theta>, sin \<theta>) \<in> W \<inter> S^1 \<subseteq> finv(V\<inter>C').\<close>
    obtain W where hW: "open W" "(cos \<theta>, sin \<theta>) \<in> W"
        "W \<inter> top1_S1 \<subseteq> finv ` (V \<inter> C')"
    proof -
      have "finv ` (V \<inter> C') \<in> top1_S1_topology" by (rule hfinv_VC'_open)
      then obtain W0 where "W0 \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
          "finv ` (V \<inter> C') = top1_S1 \<inter> W0"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      have "open W0" using \<open>W0 \<in> _\<close> product_topology_on_open_sets_real2
        unfolding top1_open_sets_def by (by100 simp)
      moreover have "(cos \<theta>, sin \<theta>) \<in> W0"
      proof -
        have "(cos \<theta>, sin \<theta>) \<in> finv ` (V \<inter> C')" using hp_in_VC' h\<theta> by simp
        thus ?thesis using \<open>finv ` (V \<inter> C') = top1_S1 \<inter> W0\<close> by (by100 blast)
      qed
      moreover have "W0 \<inter> top1_S1 \<subseteq> finv ` (V \<inter> C')"
        using \<open>finv ` (V \<inter> C') = top1_S1 \<inter> W0\<close> by (by100 blast)
      ultimately show ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>W open in R^2, so \<exists>\<delta>>0. ball((cos \<theta>,sin \<theta>),\<delta>) \<subseteq> W.\<close>
    \<comment> \<open>The continuous map t \<mapsto> (cos t, sin t) at \<theta> maps into the open set W.
       By continuity, \<exists>\<epsilon>>0 s.t. the arc of width 2\<epsilon> maps into W.\<close>
    define \<phi> where "\<phi> = (\<lambda>t::real. (cos t, sin t) :: real \<times> real)"
    have h\<phi>_cont: "continuous_on UNIV \<phi>" unfolding \<phi>_def by (intro continuous_intros)
    have h\<phi>\<theta>: "\<phi> \<theta> = (cos \<theta>, sin \<theta>)" unfolding \<phi>_def by simp
    have h\<phi>\<theta>_in_W: "\<phi> \<theta> \<in> W" using hW(2) h\<phi>\<theta> by simp
    \<comment> \<open>Continuity at \<theta>: \<exists>\<epsilon>0>0. |t-\<theta>| < \<epsilon>0 \<Rightarrow> \<phi>(t) \<in> W.\<close>
    obtain \<epsilon>0 :: real where h\<epsilon>0: "\<epsilon>0 > 0" "\<And>t. \<bar>t - \<theta>\<bar> < \<epsilon>0 \<Longrightarrow> (cos t, sin t) \<in> W"
    proof -
      have "open (\<phi> -` W)"
      proof -
        have "\<forall>B. open B \<longrightarrow> open (\<phi> -` B \<inter> UNIV)"
          using iffD1[OF continuous_on_open_vimage[OF open_UNIV] h\<phi>_cont] by simp
        hence "open (\<phi> -` W \<inter> UNIV)" using hW(1) by simp
        thus ?thesis by simp
      qed
      then obtain e where he: "e > (0::real)" "\<forall>y. dist y \<theta> < e \<longrightarrow> y \<in> \<phi> -` W"
        using h\<phi>\<theta>_in_W unfolding open_dist by (by100 blast)
      show ?thesis
      proof (rule that[of e])
        show "e > 0" by (rule he(1))
        fix t assume "\<bar>t - \<theta>\<bar> < e"
        hence "dist t \<theta> < e" unfolding dist_real_def by simp
        hence "t \<in> \<phi> -` W" using he(2) by simp
        thus "(cos t, sin t) \<in> W" unfolding \<phi>_def by simp
      qed
    qed
    have h_arc_in_S1: "\<And>t. (cos t, sin t) \<in> top1_S1" unfolding top1_S1_def
      using sin_cos_squared_add2 by simp
    define \<epsilon>1 where "\<epsilon>1 = min (\<epsilon>0 / 2) (pi / 2)"
    have h\<epsilon>1: "\<epsilon>1 > 0" "\<epsilon>1 < pi"
    proof -
      show "\<epsilon>1 > 0" unfolding \<epsilon>1_def using h\<epsilon>0(1) pi_gt_zero by simp
      have "\<epsilon>1 \<le> pi/2" unfolding \<epsilon>1_def by simp
      also have "pi/2 < pi" using pi_gt_zero by simp
      finally show "\<epsilon>1 < pi" .
    qed
    have "\<And>t. t \<in> {\<theta>-\<epsilon>1..\<theta>+\<epsilon>1} \<Longrightarrow> (cos t, sin t) \<in> finv ` (V \<inter> C')"
    proof -
      fix t assume "t \<in> {\<theta>-\<epsilon>1..\<theta>+\<epsilon>1}"
      hence "\<bar>t - \<theta>\<bar> \<le> \<epsilon>1" by auto
      hence "\<bar>t - \<theta>\<bar> < \<epsilon>0" unfolding \<epsilon>1_def using h\<epsilon>0(1) by auto
      hence "(cos t, sin t) \<in> W" by (rule h\<epsilon>0(2))
      moreover have "(cos t, sin t) \<in> top1_S1" by (rule h_arc_in_S1)
      ultimately show "(cos t, sin t) \<in> finv ` (V \<inter> C')" using hW(3) by (by100 blast)
    qed
    thus ?thesis using that h\<epsilon>1 by (by100 blast)
  qed
  \<comment> \<open>Step 4: Define arcs. C1 = f(short arc), C2 = f(long arc).\<close>
  let ?short_arc = "{(cos t, sin t) | t. t \<in> {\<theta>-\<epsilon>..\<theta>+\<epsilon>}}"
  let ?long_arc = "{(cos t, sin t) | t. t \<in> {\<theta>+\<epsilon>..\<theta>-\<epsilon>+2*pi}}"
  let ?a_S1 = "(cos (\<theta>-\<epsilon>), sin (\<theta>-\<epsilon>))"
  let ?b_S1 = "(cos (\<theta>+\<epsilon>), sin (\<theta>+\<epsilon>))"
  define C1 where "C1 = f ` ?short_arc"
  define C2 where "C2 = f ` ?long_arc"
  define a_pt where "a_pt = f ?a_S1"
  define b_pt where "b_pt = f ?b_S1"
  \<comment> \<open>Step 5: Show the 6 properties.\<close>
  \<comment> \<open>5a: S^1 = short \<union> long.\<close>
  have hS1_decomp: "top1_S1 = ?short_arc \<union> ?long_arc"
  proof (intro set_eqI iffI)
    fix p assume "p \<in> top1_S1"
    hence hp: "fst p ^ 2 + snd p ^ 2 = 1" unfolding top1_S1_def by simp
    \<comment> \<open>p = (cos t0, sin t0) for some t0. Normalize t0 to [\<theta>-\<epsilon>, \<theta>-\<epsilon>+2\<pi>).\<close>
    obtain t0 where ht0: "p = (cos t0, sin t0)" "t0 \<in> {\<theta>-\<epsilon>..<\<theta>-\<epsilon>+2*pi}"
    proof -
      obtain t where ht: "p = (cos t, sin t)"
      proof -
        have "\<bar>fst p\<bar> \<le> 1"
        proof -
          have "(snd p)^2 \<ge> 0" by simp
          hence "(fst p)^2 \<le> 1" using hp by linarith
          have "fst p \<le> 1" using power2_le_imp_le[of "fst p" 1] \<open>(fst p)^2 \<le> 1\<close> by simp
          have "(-fst p)^2 = (fst p)^2" by (simp add: power2_eq_square)
          hence "(-fst p)^2 \<le> 1" using \<open>(fst p)^2 \<le> 1\<close> by simp
          hence "-fst p \<le> 1" using power2_le_imp_le[of "-fst p" 1] by simp
          thus ?thesis using \<open>fst p \<le> 1\<close> by simp
        qed
        define t0 where "t0 = (if snd p \<ge> 0 then arccos (fst p) else 2*pi - arccos (fst p))"
        have "cos t0 = fst p" unfolding t0_def using \<open>\<bar>fst p\<bar> \<le> 1\<close> by (simp add: cos_arccos)
        have "sin t0 = snd p"
        proof (cases "snd p \<ge> 0")
          case True
          hence "t0 = arccos (fst p)" unfolding t0_def by simp
          have "sin (arccos (fst p)) = sqrt (1 - (fst p)^2)"
            using \<open>\<bar>fst p\<bar> \<le> 1\<close> by (intro sin_arccos) auto
          also have "1 - (fst p)^2 = (snd p)^2" using hp by linarith
          finally have "sin (arccos (fst p)) = \<bar>snd p\<bar>" using real_sqrt_abs by simp
          thus ?thesis using True \<open>t0 = arccos (fst p)\<close> by simp
        next
          case False
          hence "t0 = 2*pi - arccos (fst p)" unfolding t0_def by simp
          have "sin (2*pi - arccos (fst p)) = - sin (arccos (fst p))"
            by (simp add: sin_diff)
          also have "sin (arccos (fst p)) = sqrt (1 - (fst p)^2)"
            using \<open>\<bar>fst p\<bar> \<le> 1\<close> by (intro sin_arccos) auto
          also have "1 - (fst p)^2 = (snd p)^2" using hp by linarith
          finally have "sin (2*pi - arccos (fst p)) = - \<bar>snd p\<bar>"
            using real_sqrt_abs by simp
          thus ?thesis using False \<open>t0 = 2*pi - arccos (fst p)\<close> by simp
        qed
        hence "p = (cos t0, sin t0)" using \<open>cos t0 = fst p\<close> by (cases p) simp
        thus ?thesis using that by (by100 blast)
      qed
      \<comment> \<open>Normalize t to [\<theta>-\<epsilon>, \<theta>-\<epsilon>+2\<pi>) via periodicity.\<close>
      define t' where "t' = t - 2*pi * of_int \<lfloor>(t - (\<theta>-\<epsilon>)) / (2*pi)\<rfloor>"
      have h2pi_pos: "(2*pi :: real) > 0" using pi_gt_zero by simp
      have ht'_range: "t' \<ge> \<theta>-\<epsilon> \<and> t' < \<theta>-\<epsilon>+2*pi"
      proof
        have "of_int \<lfloor>(t - (\<theta>-\<epsilon>)) / (2*pi)\<rfloor> * (2*pi) \<le> t - (\<theta>-\<epsilon>)"
          by (rule floor_divide_lower[OF h2pi_pos])
        hence "2*pi * of_int \<lfloor>(t - (\<theta>-\<epsilon>)) / (2*pi)\<rfloor> \<le> t - (\<theta>-\<epsilon>)"
          by (simp add: mult.commute)
        thus "t' \<ge> \<theta>-\<epsilon>" unfolding t'_def by linarith
        have "t - (\<theta>-\<epsilon>) < (of_int \<lfloor>(t - (\<theta>-\<epsilon>)) / (2*pi)\<rfloor> + 1) * (2*pi)"
          by (rule floor_divide_upper[OF h2pi_pos])
        thus "t' < \<theta>-\<epsilon>+2*pi" unfolding t'_def by (simp add: algebra_simps)
      qed
      have "cos t' = cos t" and "sin t' = sin t"
      proof -
        define k where "k = \<lfloor>(t - (\<theta>-\<epsilon>)) / (2*pi)\<rfloor>"
        have ht'_eq: "t' = t - of_int k * (2 * pi)" unfolding t'_def k_def by (simp add: algebra_simps)
        have hcos_k: "cos (of_int k * (2 * pi)) = 1"
          using cos_integer_2pi[of "of_int k"] by (simp add: algebra_simps)
        have hsin_k: "sin (of_int k * (2 * pi)) = 0"
          using sin_integer_2pi[of "of_int k"] by (simp add: algebra_simps)
        show "cos t' = cos t" unfolding ht'_eq using hcos_k hsin_k by (simp add: cos_diff)
        show "sin t' = sin t" unfolding ht'_eq using hcos_k hsin_k by (simp add: sin_diff)
      qed
      hence "p = (cos t', sin t')" using ht by simp
      thus ?thesis using that ht'_range by auto
    qed
    \<comment> \<open>t0 \<in> [\<theta>-\<epsilon>, \<theta>-\<epsilon>+2\<pi>). Either t0 \<le> \<theta>+\<epsilon> (short arc) or t0 > \<theta>+\<epsilon> (long arc).\<close>
    show "p \<in> ?short_arc \<union> ?long_arc"
    proof (cases "t0 \<le> \<theta>+\<epsilon>")
      case True
      hence "t0 \<in> {\<theta>-\<epsilon>..\<theta>+\<epsilon>}" using ht0(2) by auto
      hence "p \<in> ?short_arc" using ht0(1) unfolding mem_Collect_eq by (by100 blast)
      thus ?thesis by (by100 blast)
    next
      case False
      hence "t0 > \<theta>+\<epsilon>" by simp
      hence "t0 \<in> {\<theta>+\<epsilon>..\<theta>-\<epsilon>+2*pi}" using ht0(2) by auto
      hence "p \<in> ?long_arc" using ht0(1) unfolding mem_Collect_eq by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
  next
    fix p assume "p \<in> ?short_arc \<union> ?long_arc"
    then obtain t where "p = (cos t, sin t)" by (by100 blast)
    thus "p \<in> top1_S1" unfolding top1_S1_def using sin_cos_squared_add2 by simp
  qed
  have hS1_inter: "?short_arc \<inter> ?long_arc = {?a_S1, ?b_S1}"
  proof (intro set_eqI iffI)
    fix p assume "p \<in> ?short_arc \<inter> ?long_arc"
    then obtain s t where hs: "s \<in> {\<theta>-\<epsilon>..\<theta>+\<epsilon>}" and ht: "t \<in> {\<theta>+\<epsilon>..\<theta>-\<epsilon>+2*pi}"
        and hst: "(cos s, sin s) = (cos t, sin t)" and hp: "p = (cos s, sin s)" by (by100 blast)
    have "cos s = cos t" and "sin s = sin t" using hst by simp_all
    obtain k :: int where hk: "s - t = real_of_int k * 2 * pi"
      using cos_sin_eq_imp[OF \<open>cos s = cos t\<close> \<open>sin s = sin t\<close>] by (by100 blast)
    have "s \<le> \<theta>+\<epsilon>" and "s \<ge> \<theta>-\<epsilon>" and "t \<ge> \<theta>+\<epsilon>" and "t \<le> \<theta>-\<epsilon>+2*pi"
      using hs ht by auto
    hence "s - t \<le> 0" by linarith
    hence "k \<le> 0"
    proof -
      have "real_of_int k * 2 * pi \<le> 0" using hk \<open>s - t \<le> 0\<close> by simp
      hence "real_of_int k \<le> 0" using pi_gt_zero by (simp add: mult_le_0_iff)
      thus ?thesis by linarith
    qed
    have "s - t \<ge> (\<theta>-\<epsilon>) - (\<theta>-\<epsilon>+2*pi)" using \<open>s \<ge> \<theta>-\<epsilon>\<close> \<open>t \<le> \<theta>-\<epsilon>+2*pi\<close> by linarith
    hence "s - t \<ge> -2*pi" by linarith
    hence "real_of_int k * 2 * pi \<ge> -2*pi" using hk by simp
    hence "real_of_int k \<ge> -1"
    proof -
      have "(2*pi) > 0" using pi_gt_zero by simp
      have "real_of_int k * (2*pi) \<ge> (-1) * (2*pi)"
        using \<open>real_of_int k * 2 * pi \<ge> -2*pi\<close> by (simp add: mult.assoc)
      thus ?thesis using \<open>(2*pi) > 0\<close> mult_le_cancel_right_pos by (by100 fast)
    qed
    hence "k \<in> {-1, 0}" using \<open>k \<le> 0\<close> by auto
    show "p \<in> {?a_S1, ?b_S1}"
    proof (cases "k = 0")
      case True
      hence "s = t" using hk by simp
      hence "s = \<theta>+\<epsilon>" using \<open>s \<le> \<theta>+\<epsilon>\<close> \<open>t \<ge> \<theta>+\<epsilon>\<close> by linarith
      thus ?thesis using hp by simp
    next
      case False
      hence "k = -1" using \<open>k \<in> {-1, 0}\<close> by simp
      hence "s = t - 2*pi" using hk by simp
      hence "s \<le> (\<theta>-\<epsilon>+2*pi) - 2*pi" using \<open>t \<le> \<theta>-\<epsilon>+2*pi\<close> by linarith
      hence "s = \<theta>-\<epsilon>" using \<open>s \<ge> \<theta>-\<epsilon>\<close> by linarith
      thus ?thesis using hp by simp
    qed
  next
    fix p assume "p \<in> {?a_S1, ?b_S1}"
    hence "p = ?a_S1 \<or> p = ?b_S1" by simp
    thus "p \<in> ?short_arc \<inter> ?long_arc"
    proof
      assume "p = ?a_S1"
      have "?a_S1 \<in> ?short_arc" unfolding mem_Collect_eq
        using h\<epsilon>(1) by (intro exI[of _ "\<theta>-\<epsilon>"]) auto
      moreover have "?a_S1 \<in> ?long_arc" unfolding mem_Collect_eq
        using h\<epsilon>(1,2) pi_gt_zero by (intro exI[of _ "\<theta>-\<epsilon>+2*pi"]) auto
      ultimately show ?thesis using \<open>p = ?a_S1\<close> by simp
    next
      assume "p = ?b_S1"
      have "?b_S1 \<in> ?short_arc" unfolding mem_Collect_eq
        using h\<epsilon>(1) by (intro exI[of _ "\<theta>+\<epsilon>"]) auto
      moreover have "?b_S1 \<in> ?long_arc" unfolding mem_Collect_eq
        using h\<epsilon>(1,2) pi_gt_zero by (intro exI[of _ "\<theta>+\<epsilon>"]) auto
      ultimately show ?thesis using \<open>p = ?b_S1\<close> by simp
    qed
  qed
  have hab_ne: "?a_S1 \<noteq> ?b_S1"
  proof
    assume "?a_S1 = ?b_S1"
    hence "cos (\<theta>-\<epsilon>) = cos (\<theta>+\<epsilon>)" and "sin (\<theta>-\<epsilon>) = sin (\<theta>+\<epsilon>)" by simp_all
    hence "\<theta>-\<epsilon> = \<theta>+\<epsilon>" by (rule cos_sin_eq_small_diff) (use h\<epsilon> in linarith)
    hence "\<epsilon> = 0" by linarith
    thus False using h\<epsilon>(1) by simp
  qed
  \<comment> \<open>5b: C' = C1 \<union> C2.\<close>
  have "C' = C1 \<union> C2"
  proof -
    have "C' = f ` top1_S1" using hf_img by simp
    also have "\<dots> = f ` (?short_arc \<union> ?long_arc)" using hS1_decomp by simp
    also have "\<dots> = f ` ?short_arc \<union> f ` ?long_arc" by (by100 blast)
    finally show ?thesis unfolding C1_def C2_def by simp
  qed
  \<comment> \<open>5c: C1 \<inter> C2 = {a, b}.\<close>
  moreover have "C1 \<inter> C2 = {a_pt, b_pt}"
  proof -
    have hshort_sub: "?short_arc \<subseteq> top1_S1" using hS1_decomp by (by100 blast)
    have hlong_sub: "?long_arc \<subseteq> top1_S1" using hS1_decomp by (by100 blast)
    have "f ` ?short_arc \<inter> f ` ?long_arc = f ` (?short_arc \<inter> ?long_arc)"
      by (rule inj_on_image_Int[OF hf_inj hshort_sub hlong_sub, symmetric])
    also have "\<dots> = f ` {?a_S1, ?b_S1}" using hS1_inter by simp
    also have "\<dots> = {f ?a_S1, f ?b_S1}" by (by100 blast)
    finally show ?thesis unfolding C1_def C2_def a_pt_def b_pt_def by simp
  qed
  \<comment> \<open>5d: a \<noteq> b.\<close>
  moreover have "a_pt \<noteq> b_pt"
  proof -
    have "?a_S1 \<in> ?short_arc"
      apply (rule CollectI) apply (rule exI[of _ "\<theta>-\<epsilon>"]) using h\<epsilon> by simp
    hence ha_S1: "?a_S1 \<in> top1_S1" using hS1_decomp by (by100 blast)
    have "?b_S1 \<in> ?short_arc"
      apply (rule CollectI) apply (rule exI[of _ "\<theta>+\<epsilon>"]) using h\<epsilon> by simp
    hence hb_S1: "?b_S1 \<in> top1_S1" using hS1_decomp by (by100 blast)
    show ?thesis
    proof
      assume "a_pt = b_pt"
      hence "f ?a_S1 = f ?b_S1" unfolding a_pt_def b_pt_def by simp
      hence "?a_S1 = ?b_S1" using inj_onD[OF hf_inj _ ha_S1 hb_S1] by simp
      thus False using hab_ne by simp
    qed
  qed
  \<comment> \<open>5e: Both are arcs.\<close>
  moreover have "top1_is_arc_on C1 (subspace_topology top1_S2 top1_S2_topology C1)"
  proof -
    \<comment> \<open>Short arc \<cong> [0,1] via g(t) = (cos(\<theta>-\<epsilon>+2\<epsilon>t), sin(\<theta>-\<epsilon>+2\<epsilon>t)).\<close>
    define g where "g = (\<lambda>t::real. (cos (\<theta>-\<epsilon>+2*\<epsilon>*t), sin (\<theta>-\<epsilon>+2*\<epsilon>*t)))"
    have hg_img: "g ` I_set = ?short_arc"
    proof (intro set_eqI iffI)
      fix p assume "p \<in> g ` I_set"
      then obtain t where ht: "t \<in> I_set" "p = g t" by (by100 blast)
      have "p = (cos (\<theta>-\<epsilon>+2*\<epsilon>*t), sin (\<theta>-\<epsilon>+2*\<epsilon>*t))" using ht(2) unfolding g_def by simp
      moreover have "\<theta>-\<epsilon>+2*\<epsilon>*t \<in> {\<theta>-\<epsilon>..\<theta>+\<epsilon>}" using ht(1) h\<epsilon>(1)
        unfolding top1_unit_interval_def by auto
      ultimately show "p \<in> ?short_arc" by (by100 force)
    next
      fix p assume "p \<in> ?short_arc"
      then obtain s where hs: "s \<in> {\<theta>-\<epsilon>..\<theta>+\<epsilon>}" "p = (cos s, sin s)" by (by100 blast)
      define t where "t = (s - (\<theta>-\<epsilon>)) / (2*\<epsilon>)"
      have "t \<in> I_set" unfolding t_def top1_unit_interval_def using hs(1) h\<epsilon>(1) by auto
      moreover have "g t = p" unfolding g_def t_def using h\<epsilon>(1) hs(2) by (simp add: field_simps)
      ultimately show "p \<in> g ` I_set" by (by100 blast)
    qed
    have hg_inj: "inj_on g I_set"
    proof (rule inj_onI)
      fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set" and heq: "g s = g t"
      have "cos (\<theta>-\<epsilon>+2*\<epsilon>*s) = cos (\<theta>-\<epsilon>+2*\<epsilon>*t)"
        using heq unfolding g_def by simp
      moreover have "sin (\<theta>-\<epsilon>+2*\<epsilon>*s) = sin (\<theta>-\<epsilon>+2*\<epsilon>*t)"
        using heq unfolding g_def by simp
      \<comment> \<open>cos a = cos b \<and> sin a = sin b \<Rightarrow> a - b = 2k\<pi>. Since |a-b| < 2\<pi> (both in range 2\<epsilon> < 2\<pi>), k=0.\<close>
      ultimately have "\<theta>-\<epsilon>+2*\<epsilon>*s = \<theta>-\<epsilon>+2*\<epsilon>*t"
      proof (rule cos_sin_eq_small_diff)
        have "0 \<le> s" "s \<le> 1" "0 \<le> t" "t \<le> 1"
          using hs ht unfolding top1_unit_interval_def by auto
        have "\<bar>(\<theta>-\<epsilon>+2*\<epsilon>*s) - (\<theta>-\<epsilon>+2*\<epsilon>*t)\<bar> = \<bar>2*\<epsilon>*(s-t)\<bar>"
          by (simp add: algebra_simps)
        also have "\<dots> = 2*\<epsilon> * \<bar>s-t\<bar>" using h\<epsilon>(1) by (simp add: abs_mult)
        also have "\<dots> \<le> 2*\<epsilon> * 1"
          by (rule mult_left_mono) (use \<open>0\<le>s\<close> \<open>s\<le>1\<close> \<open>0\<le>t\<close> \<open>t\<le>1\<close> h\<epsilon>(1) in auto)
        also have "\<dots> < 2*pi" using h\<epsilon>(2) by linarith
        finally show "\<bar>(\<theta>-\<epsilon>+2*\<epsilon>*s) - (\<theta>-\<epsilon>+2*\<epsilon>*t)\<bar> < 2 * pi" .
      qed
      thus "s = t" using h\<epsilon>(1) by simp
    qed
    have hg_cont: "continuous_on I_set g" unfolding g_def by (intro continuous_intros)
    have hfg_cont: "top1_continuous_map_on I_set I_top C1
        (subspace_topology top1_S2 top1_S2_topology C1) (f \<circ> g)"
    proof -
      \<comment> \<open>Bridge: continuous_on I_set (f \<circ> g) in HOL \<Rightarrow> top1_continuous_map_on.\<close>
      have hg_sub: "g ` I_set \<subseteq> top1_S1" using hg_img hS1_decomp by (by100 blast)
      have hfg_maps: "\<And>t. t \<in> I_set \<Longrightarrow> (f \<circ> g) t \<in> C1"
      proof -
        fix t assume "t \<in> I_set"
        hence "g t \<in> g ` I_set" by (by100 blast)
        hence "g t \<in> ?short_arc" using hg_img by simp
        thus "(f \<circ> g) t \<in> C1" unfolding C1_def comp_def by (by100 blast)
      qed
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix t assume "t \<in> I_set" thus "(f \<circ> g) t \<in> C1" by (rule hfg_maps)
      next
        fix W assume hW: "W \<in> subspace_topology top1_S2 top1_S2_topology C1"
        then obtain W0 where hW0: "W0 \<in> top1_S2_topology" "W = C1 \<inter> W0"
          unfolding subspace_topology_def by (by100 blast)
        have hS1_open: "{s \<in> top1_S1. f s \<in> W0} \<in> top1_S1_topology"
          using hf_cont hW0(1) unfolding top1_continuous_map_on_def by (by100 blast)
        have heq: "{t \<in> I_set. (f \<circ> g) t \<in> W} = {t \<in> I_set. g t \<in> {s \<in> top1_S1. f s \<in> W0}}"
          using hfg_maps hW0(2) hg_sub by (by100 force)
        show "{t \<in> I_set. (f \<circ> g) t \<in> W} \<in> I_top"
        proof -
          obtain W1 where hW1: "W1 \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
              "{s \<in> top1_S1. f s \<in> W0} = top1_S1 \<inter> W1"
            using hS1_open unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
          have "open W1" using hW1(1) product_topology_on_open_sets_real2
            unfolding top1_open_sets_def by (by100 simp)
          have "{t \<in> I_set. g t \<in> {s \<in> top1_S1. f s \<in> W0}} = I_set \<inter> g -` W1"
            using hg_sub hW1(2) by (by100 force)
          hence "{t \<in> I_set. (f \<circ> g) t \<in> W} = I_set \<inter> g -` W1" using heq by simp
          moreover have "I_set \<inter> g -` W1 \<in> I_top"
          proof -
            have "\<exists>A. open A \<and> A \<inter> I_set = g -` W1 \<inter> I_set"
              using hg_cont \<open>open W1\<close> unfolding continuous_on_open_invariant by simp
            then obtain A where "open A" "A \<inter> I_set = g -` W1 \<inter> I_set" by (by100 blast)
            have "A \<in> (top1_open_sets :: real set set)" using \<open>open A\<close>
              unfolding top1_open_sets_def by simp
            have "I_set \<inter> g -` W1 = I_set \<inter> A" using \<open>A \<inter> I_set = _\<close> by (by100 blast)
            thus ?thesis unfolding top1_unit_interval_topology_def top1_unit_interval_def
              subspace_topology_def using \<open>A \<in> top1_open_sets\<close> by (by100 blast)
          qed
          ultimately show ?thesis by simp
        qed
      qed
    qed
    have hfg_bij: "bij_betw (f \<circ> g) I_set C1"
    proof -
      have hinj_f_short: "inj_on f ?short_arc"
        by (rule inj_on_subset[OF hf_inj]) (use hS1_decomp in blast)
      have "inj_on (f \<circ> g) I_set"
        by (rule comp_inj_on[OF hg_inj]) (use hinj_f_short hg_img in simp)
      moreover have "(f \<circ> g) ` I_set = C1"
      proof -
        have "(f \<circ> g) ` I_set = f ` (g ` I_set)" by (simp add: image_comp)
        also have "\<dots> = f ` ?short_arc" using hg_img by simp
        finally show ?thesis unfolding C1_def by simp
      qed
      ultimately show ?thesis unfolding bij_betw_def by simp
    qed
    have hC1_haus: "is_hausdorff_on C1 (subspace_topology top1_S2 top1_S2_topology C1)"
      by (rule hausdorff_subspace[OF top1_S2_is_hausdorff])
         (use hC'_sub \<open>C' = C1 \<union> C2\<close> in blast)
    have hI_compact: "top1_compact_on I_set I_top"
    proof -
      have "compact (I_set :: real set)"
        unfolding top1_unit_interval_def using compact_Icc by simp
      have "I_top = subspace_topology UNIV top1_open_sets I_set"
        unfolding top1_unit_interval_topology_def top1_unit_interval_def by simp
      thus ?thesis using top1_compact_on_subspace_UNIV_iff_compact[of I_set] \<open>compact I_set\<close> by simp
    qed
    have hI_top: "is_topology_on I_set I_top"
      by (rule top1_unit_interval_topology_is_topology_on)
    have hC1_top: "is_topology_on C1 (subspace_topology top1_S2 top1_S2_topology C1)"
      by (rule subspace_topology_is_topology_on[OF hTS2])
         (use hC'_sub \<open>C' = C1 \<union> C2\<close> in blast)
    have "top1_homeomorphism_on I_set I_top C1
        (subspace_topology top1_S2 top1_S2_topology C1) (f \<circ> g)"
      by (rule Theorem_26_6[OF hI_top hC1_top hI_compact hC1_haus hfg_cont hfg_bij])
    moreover have "is_topology_on_strict C1 (subspace_topology top1_S2 top1_S2_topology C1)"
      by (rule subspace_topology_is_strict[OF hTS])
         (use hC'_sub \<open>C' = C1 \<union> C2\<close> in blast)
    ultimately show ?thesis unfolding top1_is_arc_on_def by (by100 blast)
  qed
  moreover have "top1_is_arc_on C2 (subspace_topology top1_S2 top1_S2_topology C2)"
  proof -
    \<comment> \<open>Long arc \<cong> [0,1] via g'(t) = (cos(\<theta>+\<epsilon>+(2\<pi>-2\<epsilon>)t), sin(\<theta>+\<epsilon>+(2\<pi>-2\<epsilon>)t)).\<close>
    define g' where "g' = (\<lambda>t::real. (cos (\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*t), sin (\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*t)))"
    have hg'_img: "g' ` I_set = ?long_arc"
    proof (intro set_eqI iffI)
      fix p assume "p \<in> g' ` I_set"
      then obtain t where ht: "t \<in> I_set" "p = g' t" by (by100 blast)
      have "p = (cos (\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*t), sin (\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*t))"
        using ht(2) unfolding g'_def by simp
      moreover have "\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*t \<in> {\<theta>+\<epsilon>..\<theta>-\<epsilon>+2*pi}"
      proof -
        have "t \<ge> 0" "t \<le> 1" using ht(1) unfolding top1_unit_interval_def by auto
        have "2*pi - 2*\<epsilon> \<ge> 0" using h\<epsilon>(2) pi_gt_zero by linarith
        have "\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*t \<ge> \<theta>+\<epsilon>"
          using \<open>t \<ge> 0\<close> \<open>2*pi-2*\<epsilon> \<ge> 0\<close> by (simp add: mult_nonneg_nonneg)
        moreover have "\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*t \<le> \<theta>-\<epsilon>+2*pi"
        proof -
          have "(2*pi-2*\<epsilon>)*t \<le> (2*pi-2*\<epsilon>)*1"
            using \<open>t \<le> 1\<close> \<open>2*pi-2*\<epsilon> \<ge> 0\<close> by (rule mult_left_mono)
          hence "(2*pi-2*\<epsilon>)*t \<le> 2*pi-2*\<epsilon>" by simp
          thus ?thesis by linarith
        qed
        ultimately show ?thesis by simp
      qed
      ultimately show "p \<in> ?long_arc"
        unfolding mem_Collect_eq by (by100 blast)
    next
      fix p assume "p \<in> ?long_arc"
      then obtain s where hs: "s \<in> {\<theta>+\<epsilon>..\<theta>-\<epsilon>+2*pi}" "p = (cos s, sin s)" by (by100 blast)
      define t where "t = (s - (\<theta>+\<epsilon>)) / (2*pi-2*\<epsilon>)"
      have "t \<in> I_set" unfolding t_def top1_unit_interval_def using hs(1) h\<epsilon> pi_gt_zero by (auto simp: field_simps)
      moreover have "g' t = p"
      proof -
        have "2*pi - 2*\<epsilon> \<noteq> 0" using h\<epsilon>(2) pi_gt_zero by linarith
        hence "\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*((s-(\<theta>+\<epsilon>))/(2*pi-2*\<epsilon>)) = s" by (simp add: field_simps)
        thus ?thesis unfolding g'_def t_def using hs(2) by simp
      qed
      ultimately show "p \<in> g' ` I_set" by (by100 blast)
    qed
    have hg'_inj: "inj_on g' I_set"
    proof (rule inj_onI)
      fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set" and heq: "g' s = g' t"
      have "cos (\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*s) = cos (\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*t)"
        using heq unfolding g'_def by simp
      moreover have "sin (\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*s) = sin (\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*t)"
        using heq unfolding g'_def by simp
      ultimately have "\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*s = \<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*t"
      proof (rule cos_sin_eq_small_diff)
        have "0 \<le> s" "s \<le> 1" "0 \<le> t" "t \<le> 1"
          using hs ht unfolding top1_unit_interval_def by auto
        have "2*pi-2*\<epsilon> > 0" using h\<epsilon>(2) pi_gt_zero by linarith
        have "\<bar>(\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*s) - (\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*t)\<bar> = \<bar>(2*pi-2*\<epsilon>)*(s-t)\<bar>"
          by (simp add: algebra_simps)
        also have "\<dots> = (2*pi-2*\<epsilon>) * \<bar>s-t\<bar>" using \<open>2*pi-2*\<epsilon> > 0\<close> by (simp add: abs_mult)
        also have "\<dots> \<le> (2*pi-2*\<epsilon>) * 1"
          by (rule mult_left_mono) (use \<open>0\<le>s\<close> \<open>s\<le>1\<close> \<open>0\<le>t\<close> \<open>t\<le>1\<close> \<open>2*pi-2*\<epsilon> > 0\<close> in auto)
        also have "(2*pi-2*\<epsilon>) * 1 = 2*pi-2*\<epsilon>" by simp
        also have "\<dots> < 2*pi" using h\<epsilon>(1) by linarith
        finally show "\<bar>(\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*s) - (\<theta>+\<epsilon>+(2*pi-2*\<epsilon>)*t)\<bar> < 2 * pi" .
      qed
      hence "(2*pi-2*\<epsilon>)*s = (2*pi-2*\<epsilon>)*t" by linarith
      moreover have "2*pi-2*\<epsilon> \<noteq> (0::real)" using h\<epsilon>(2) pi_gt_zero by linarith
      ultimately show "s = t" by simp
    qed
    have hg'_cont: "continuous_on I_set g'" unfolding g'_def by (intro continuous_intros)
    have hfg'_cont: "top1_continuous_map_on I_set I_top C2
        (subspace_topology top1_S2 top1_S2_topology C2) (f \<circ> g')"
    proof -
      have hg'_sub: "g' ` I_set \<subseteq> top1_S1" using hg'_img hS1_decomp by (by100 blast)
      have hfg'_maps: "\<And>t. t \<in> I_set \<Longrightarrow> (f \<circ> g') t \<in> C2"
      proof -
        fix t assume "t \<in> I_set"
        hence "g' t \<in> g' ` I_set" by (by100 blast)
        hence "g' t \<in> ?long_arc" using hg'_img by simp
        thus "(f \<circ> g') t \<in> C2" unfolding C2_def comp_def by (by100 blast)
      qed
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix t assume "t \<in> I_set" thus "(f \<circ> g') t \<in> C2" by (rule hfg'_maps)
      next
        fix W assume hW: "W \<in> subspace_topology top1_S2 top1_S2_topology C2"
        then obtain W0 where hW0: "W0 \<in> top1_S2_topology" "W = C2 \<inter> W0"
          unfolding subspace_topology_def by (by100 blast)
        have hS1_open: "{s \<in> top1_S1. f s \<in> W0} \<in> top1_S1_topology"
          using hf_cont hW0(1) unfolding top1_continuous_map_on_def by (by100 blast)
        show "{t \<in> I_set. (f \<circ> g') t \<in> W} \<in> I_top"
        proof -
          obtain W1 where hW1: "W1 \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
              "{s \<in> top1_S1. f s \<in> W0} = top1_S1 \<inter> W1"
            using hS1_open unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
          have "open W1" using hW1(1) product_topology_on_open_sets_real2
            unfolding top1_open_sets_def by (by100 simp)
          have heq_g': "{t \<in> I_set. g' t \<in> {s \<in> top1_S1. f s \<in> W0}} = I_set \<inter> g' -` W1"
            using hg'_sub hW1(2) by (by100 force)
          have heq_main: "{t \<in> I_set. (f \<circ> g') t \<in> W} = {t \<in> I_set. g' t \<in> {s \<in> top1_S1. f s \<in> W0}}"
            using hfg'_maps hW0(2) hg'_sub by (by100 force)
          have "I_set \<inter> g' -` W1 \<in> I_top"
          proof -
            have "\<exists>A. open A \<and> A \<inter> I_set = g' -` W1 \<inter> I_set"
              using hg'_cont \<open>open W1\<close> unfolding continuous_on_open_invariant by simp
            then obtain A where "open A" "A \<inter> I_set = g' -` W1 \<inter> I_set" by (by100 blast)
            have "A \<in> (top1_open_sets :: real set set)" using \<open>open A\<close>
              unfolding top1_open_sets_def by simp
            have "I_set \<inter> g' -` W1 = I_set \<inter> A" using \<open>A \<inter> I_set = _\<close> by (by100 blast)
            thus ?thesis unfolding top1_unit_interval_topology_def top1_unit_interval_def
              subspace_topology_def using \<open>A \<in> top1_open_sets\<close> by (by100 blast)
          qed
          thus ?thesis using heq_main heq_g' by simp
        qed
      qed
    qed
    have hfg'_bij: "bij_betw (f \<circ> g') I_set C2"
    proof -
      have hinj_f_long: "inj_on f ?long_arc"
        by (rule inj_on_subset[OF hf_inj]) (use hS1_decomp in blast)
      have "inj_on (f \<circ> g') I_set"
        by (rule comp_inj_on[OF hg'_inj]) (use hinj_f_long hg'_img in simp)
      moreover have "(f \<circ> g') ` I_set = C2"
      proof -
        have "(f \<circ> g') ` I_set = f ` (g' ` I_set)" by (simp add: image_comp)
        also have "\<dots> = f ` ?long_arc" using hg'_img by simp
        finally show ?thesis unfolding C2_def by simp
      qed
      ultimately show ?thesis unfolding bij_betw_def by simp
    qed
    have hC2_haus: "is_hausdorff_on C2 (subspace_topology top1_S2 top1_S2_topology C2)"
      by (rule hausdorff_subspace[OF top1_S2_is_hausdorff])
         (use hC'_sub \<open>C' = C1 \<union> C2\<close> in blast)
    have hI_compact: "top1_compact_on I_set I_top"
    proof -
      have "compact (I_set :: real set)"
        unfolding top1_unit_interval_def using compact_Icc by simp
      have "I_top = subspace_topology UNIV top1_open_sets I_set"
        unfolding top1_unit_interval_topology_def top1_unit_interval_def by simp
      thus ?thesis using top1_compact_on_subspace_UNIV_iff_compact[of I_set] \<open>compact I_set\<close> by simp
    qed
    have hI_top: "is_topology_on I_set I_top"
      by (rule top1_unit_interval_topology_is_topology_on)
    have hC2_top: "is_topology_on C2 (subspace_topology top1_S2 top1_S2_topology C2)"
      by (rule subspace_topology_is_topology_on[OF hTS2])
         (use hC'_sub \<open>C' = C1 \<union> C2\<close> in blast)
    have "top1_homeomorphism_on I_set I_top C2
        (subspace_topology top1_S2 top1_S2_topology C2) (f \<circ> g')"
      by (rule Theorem_26_6[OF hI_top hC2_top hI_compact hC2_haus hfg'_cont hfg'_bij])
    moreover have "is_topology_on_strict C2 (subspace_topology top1_S2 top1_S2_topology C2)"
      by (rule subspace_topology_is_strict[OF hTS])
         (use hC'_sub \<open>C' = C1 \<union> C2\<close> in blast)
    ultimately show ?thesis unfolding top1_is_arc_on_def by (by100 blast)
  qed
  \<comment> \<open>5f: C1 \<subseteq> V.\<close>
  moreover have "C1 \<subseteq> V"
  proof -
    have "?short_arc \<subseteq> finv ` (V \<inter> C')" using h_arc_sub by (by100 blast)
    hence "f ` ?short_arc \<subseteq> f ` (finv ` (V \<inter> C'))" by (by100 fast)
    moreover have "f ` (finv ` (V \<inter> C')) \<subseteq> V \<inter> C'"
    proof -
      have "\<And>y. y \<in> V \<inter> C' \<Longrightarrow> f (finv y) = y"
      proof -
        fix y assume "y \<in> V \<inter> C'"
        hence "y \<in> C'" by (by100 blast)
        hence "y \<in> f ` top1_S1" using hf_img by simp
        thus "f (finv y) = y" unfolding finv_def by (rule f_inv_into_f)
      qed
      thus ?thesis by (by100 force)
    qed
    ultimately show ?thesis unfolding C1_def by (by100 blast)
  qed
  ultimately show ?thesis by (by100 blast)
qed

\<comment> \<open>Helper: every open set meeting a simple closed curve on S^2 meets both components.
   This is the core of the textbook Step 2 boundary argument.\<close>
lemma simple_closed_curve_boundary_meets_component:
  assumes hTS: "is_topology_on_strict top1_S2 top1_S2_topology"
  and hSCC: "top1_simple_closed_curve_on top1_S2 top1_S2_topology C'"
  and hW1: "top1_connected_on W1 (subspace_topology top1_S2 top1_S2_topology W1)"
  and hW2: "top1_connected_on W2 (subspace_topology top1_S2 top1_S2_topology W2)"
  and hW12: "W1 \<inter> W2 = {}" "W1 \<union> W2 = top1_S2 - C'" "W1 \<noteq> {}" "W2 \<noteq> {}"
  and hW1_open: "W1 \<in> top1_S2_topology" and hW2_open: "W2 \<in> top1_S2_topology"
  and hx: "x \<in> C'" and hV: "V \<in> top1_S2_topology" and hxV: "x \<in> V"
  shows "V \<inter> W1 \<noteq> {}"
proof -
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using hTS unfolding is_topology_on_strict_def by (by100 blast)
  have hC'_sub: "C' \<subseteq> top1_S2"
    using hSCC unfolding top1_simple_closed_curve_on_def top1_continuous_map_on_def
    by (by100 blast)
  \<comment> \<open>Step 1: Flexible arc decomposition. C' = C1'\<union>C2' with C1' \<subseteq> V, both arcs.\<close>
  obtain C1_arc C2_arc a_arc b_arc where
      hC_decomp: "C' = C1_arc \<union> C2_arc"
      and hC_inter: "C1_arc \<inter> C2_arc = {a_arc, b_arc}" and hab: "a_arc \<noteq> b_arc"
      and hC1_arc: "top1_is_arc_on C1_arc (subspace_topology top1_S2 top1_S2_topology C1_arc)"
      and hC2_arc: "top1_is_arc_on C2_arc (subspace_topology top1_S2 top1_S2_topology C2_arc)"
      and hC1_sub_V: "C1_arc \<subseteq> V"
    using flexible_arc_decomposition[OF hTS hSCC hV hx hxV] by blast
  \<comment> \<open>Step 2: C2 doesn't separate S^2.\<close>
  have hC2_sub: "C2_arc \<subseteq> top1_S2" using hC_decomp hC'_sub by (by100 blast)
  have hC2_nonsep: "\<not> top1_separates_on top1_S2 top1_S2_topology C2_arc"
    by (rule Theorem_63_2_arc_no_separation[OF hTS hC2_sub hC2_arc])
  \<comment> \<open>Step 3: S^2-C2 is connected. W1, W2 \<subseteq> S^2-C2 (since W1\<union>W2 = S^2-C' \<subseteq> S^2-C2).\<close>
  have hS2C2_conn: "top1_connected_on (top1_S2 - C2_arc)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2_arc))"
    using hC2_nonsep unfolding top1_separates_on_def by simp
  have hW1_sub_S2C2: "W1 \<subseteq> top1_S2 - C2_arc"
    using hW12(2) hC_decomp hW12(1) by (by100 blast)
  have hW2_sub_S2C2: "W2 \<subseteq> top1_S2 - C2_arc"
    using hW12(2) hC_decomp hW12(1) by (by100 blast)
  \<comment> \<open>Step 4: S^2-C2 = W1 \<union> W2 \<union> C1. Connected path image meets both W1, W2.\<close>
  have hS2C2_decomp: "top1_S2 - C2_arc = W1 \<union> W2 \<union> (C1_arc - C2_arc)"
  proof -
    have hC2_sub_C': "C2_arc \<subseteq> C'" using hC_decomp by (by100 blast)
    have "top1_S2 - C2_arc = (top1_S2 - C') \<union> (C' - C2_arc)"
      using hC'_sub hC2_sub_C' by (by100 blast)
    also have "C' - C2_arc = C1_arc - C2_arc" using hC_decomp by (by100 blast)
    finally show ?thesis using hW12(2) by simp
  qed
  \<comment> \<open>Take a \<in> W1, b \<in> W2. Path from a to b in S^2-C2 (connected + lpc \<Rightarrow> path-connected).\<close>
  obtain a where ha: "a \<in> W1" using hW12(3) by (by100 blast)
  obtain b where hb: "b \<in> W2" using hW12(4) by (by100 blast)
  \<comment> \<open>Path \<alpha> from a to b in S^2-C2.\<close>
  have hS2C2_pc: "top1_path_connected_on (top1_S2 - C2_arc)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2_arc))"
  proof (rule connected_locally_path_connected_imp_path_connected)
    show "is_topology_on (top1_S2 - C2_arc)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2_arc))"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
    show "top1_connected_on (top1_S2 - C2_arc)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2_arc))"
      by (rule hS2C2_conn)
    show "top1_locally_path_connected_on (top1_S2 - C2_arc)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2_arc))"
    proof -
      have hC2_compact: "top1_compact_on C2_arc (subspace_topology top1_S2 top1_S2_topology C2_arc)"
      proof -
        obtain h2 where hh2: "top1_homeomorphism_on I_set I_top C2_arc
            (subspace_topology top1_S2 top1_S2_topology C2_arc) h2"
          using hC2_arc unfolding top1_is_arc_on_def by (by100 blast)
        have "compact {0..1::real}" by (rule compact_Icc)
        moreover have "I_set = {0..1::real}" unfolding top1_unit_interval_def
          by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
        ultimately have "compact I_set" by simp
        hence hI_compact: "top1_compact_on I_set I_top"
          unfolding top1_unit_interval_topology_def
          using top1_compact_on_subspace_UNIV_iff_compact[of I_set] by simp
        have hcont: "top1_continuous_map_on I_set I_top C2_arc
            (subspace_topology top1_S2 top1_S2_topology C2_arc) h2"
          using hh2 unfolding top1_homeomorphism_on_def by (by100 blast)
        have hTS2_C2: "is_topology_on C2_arc (subspace_topology top1_S2 top1_S2_topology C2_arc)"
          using hh2 unfolding top1_homeomorphism_on_def by (by100 blast)
        have himg: "h2 ` I_set = C2_arc"
          using hh2 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have "top1_compact_on (h2 ` I_set) (subspace_topology C2_arc
            (subspace_topology top1_S2 top1_S2_topology C2_arc) (h2 ` I_set))"
          by (rule top1_compact_on_continuous_image[OF hI_compact hTS2_C2 hcont])
        moreover have "subspace_topology C2_arc (subspace_topology top1_S2 top1_S2_topology C2_arc) C2_arc
            = subspace_topology top1_S2 top1_S2_topology C2_arc"
          using hC2_arc unfolding top1_is_arc_on_def is_topology_on_strict_def
          by (intro subspace_topology_self) (by100 blast)
        ultimately show ?thesis using himg by simp
      qed
      have "closedin_on top1_S2 top1_S2_topology C2_arc"
        by (rule compact_in_strict_hausdorff_closedin_on[OF top1_S2_is_hausdorff hTS hC2_sub hC2_compact])
      hence "top1_S2 - C2_arc \<in> top1_S2_topology"
        unfolding closedin_on_def by (by100 blast)
      thus ?thesis
        by (rule open_subset_locally_path_connected[OF S2_locally_path_connected]) simp
    qed
    show "top1_S2 - C2_arc \<noteq> {}" using hW1_sub_S2C2 hW12(3) by (by100 blast)
  qed
  obtain \<alpha> where h\<alpha>: "top1_is_path_on (top1_S2 - C2_arc)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2_arc)) a b \<alpha>"
    using hS2C2_pc ha hb hW1_sub_S2C2 hW2_sub_S2C2
    unfolding top1_path_connected_on_def top1_in_same_path_component_on_def by (by100 blast)
  \<comment> \<open>Step 5: Path image is connected and meets W1 (at a) and W2 (at b).
     Image \<subseteq> S^2-C2 = W1 \<union> W2 \<union> C1. If image \<inter> C1 = {}: image \<subseteq> W1\<union>W2 separated.
     Connected image can't be in separated W1\<union>W2. So image meets C1 \<subseteq> V.\<close>
  have h\<alpha>_img_sub: "\<alpha> ` I_set \<subseteq> top1_S2 - C2_arc"
    using h\<alpha> unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
  have h\<alpha>_0: "\<alpha> 0 = a" using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
  have h\<alpha>_1: "\<alpha> 1 = b" using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
  have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have h\<alpha>_meets_W1: "\<alpha> ` I_set \<inter> W1 \<noteq> {}"
    using h\<alpha>_0 h0_I ha by (by100 blast)
  have h\<alpha>_meets_W2: "\<alpha> ` I_set \<inter> W2 \<noteq> {}"
    using h\<alpha>_1 h1_I hb by (by100 blast)
  have "\<alpha> ` I_set \<inter> C1_arc \<noteq> {}"
  proof (rule ccontr)
    assume h_not: "\<not> \<alpha> ` I_set \<inter> C1_arc \<noteq> {}"
    hence h_disj: "\<alpha> ` I_set \<inter> C1_arc = {}" by simp
    hence h_sub: "\<alpha> ` I_set \<subseteq> W1 \<union> W2"
      using h\<alpha>_img_sub hS2C2_decomp by (by100 blast)
    \<comment> \<open>Connected image in W1 \<union> W2 (disjoint opens) meeting both \<Rightarrow> separated. Contradiction.\<close>
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTS2C2: "is_topology_on (top1_S2 - C2_arc)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2_arc))"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
    have h\<alpha>_cont: "top1_continuous_map_on I_set I_top (top1_S2 - C2_arc)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2_arc)) \<alpha>"
      using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
    have hI_conn: "top1_connected_on I_set I_top" by (rule top1_unit_interval_connected)
    have h_img_conn: "top1_connected_on (\<alpha> ` I_set)
        (subspace_topology (top1_S2 - C2_arc)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2_arc)) (\<alpha> ` I_set))"
      by (rule Theorem_23_5[OF hTI hTS2C2 hI_conn h\<alpha>_cont])
    \<comment> \<open>\<alpha>(I) \<subseteq> W1\<union>W2 (disjoint opens in S^2). W1 \<inter> \<alpha>(I) and W2 \<inter> \<alpha>(I) separate \<alpha>(I).\<close>
    have h_img_top_eq: "subspace_topology (top1_S2 - C2_arc)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2_arc)) (\<alpha> ` I_set)
        = subspace_topology top1_S2 top1_S2_topology (\<alpha> ` I_set)"
      by (rule subspace_topology_trans) (use h\<alpha>_img_sub in simp)
    have "W1 \<inter> \<alpha> ` I_set \<in> subspace_topology top1_S2 top1_S2_topology (\<alpha> ` I_set)"
      using hW1_open unfolding subspace_topology_def by (by100 blast)
    moreover have "W2 \<inter> \<alpha> ` I_set \<in> subspace_topology top1_S2 top1_S2_topology (\<alpha> ` I_set)"
      using hW2_open unfolding subspace_topology_def by (by100 blast)
    moreover have "(W1 \<inter> \<alpha> ` I_set) \<inter> (W2 \<inter> \<alpha> ` I_set) = {}" using hW12(1) by (by100 blast)
    moreover have "(W1 \<inter> \<alpha> ` I_set) \<union> (W2 \<inter> \<alpha> ` I_set) = \<alpha> ` I_set"
      using h_sub by (by100 blast)
    ultimately show False
      using h_img_conn[unfolded h_img_top_eq top1_connected_on_def]
        h\<alpha>_meets_W1 h\<alpha>_meets_W2 by (by100 blast)
  qed
  \<comment> \<open>Step 6 (Munkres textbook argument): \<alpha>(I) connected in S^2. cl(W1) \<subseteq> W1 \<union> C'.
     b \<in> W2 \<subseteq> S^2 - cl(W1). So \<alpha>(I) meets both W1 and S^2-cl(W1).
     Connectedness \<Rightarrow> \<alpha>(I) \<inter> (cl(W1) - W1) \<noteq> {}.
     y \<in> \<alpha>(I) \<inter> (cl(W1) - W1) \<subseteq> C' \<inter> (S^2-C2) = C1 \<subseteq> V.
     y \<in> cl(W1) \<inter> V, V open \<Rightarrow> V \<inter> W1 \<noteq> {} by closure_meets_open.\<close>
  \<comment> \<open>\<alpha>(I) connected in S^2 subspace topology.\<close>
  have h_img_conn_S2: "top1_connected_on (\<alpha> ` I_set)
      (subspace_topology top1_S2 top1_S2_topology (\<alpha> ` I_set))"
  proof -
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTS2C2: "is_topology_on (top1_S2 - C2_arc)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2_arc))"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
    have h\<alpha>_cont: "top1_continuous_map_on I_set I_top (top1_S2 - C2_arc)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2_arc)) \<alpha>"
      using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
    have hI_conn: "top1_connected_on I_set I_top" by (rule top1_unit_interval_connected)
    have h_conn: "top1_connected_on (\<alpha> ` I_set)
        (subspace_topology (top1_S2 - C2_arc)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2_arc)) (\<alpha> ` I_set))"
      by (rule Theorem_23_5[OF hTI hTS2C2 hI_conn h\<alpha>_cont])
    moreover have "subspace_topology (top1_S2 - C2_arc)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2_arc)) (\<alpha> ` I_set)
        = subspace_topology top1_S2 top1_S2_topology (\<alpha> ` I_set)"
      by (rule subspace_topology_trans) (use h\<alpha>_img_sub in simp)
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>cl(W1) \<subseteq> W1 \<union> C' (since W2 = S^2 - W1 - C' is open, so W1\<union>C' is closed).\<close>
  have hW1_C'_closed: "closedin_on top1_S2 top1_S2_topology (W1 \<union> C')"
  proof -
    have hW12_C: "W1 \<union> W2 = top1_S2 - C'" using hW12(2) by simp
    have "top1_S2 - (W1 \<union> C') = W2"
    proof (intro set_eqI iffI)
      fix z assume "z \<in> top1_S2 - (W1 \<union> C')"
      hence "z \<in> top1_S2" "z \<notin> W1" "z \<notin> C'" by auto
      hence "z \<in> top1_S2 - C'" by (by100 blast)
      hence "z \<in> W1 \<union> W2" using hW12(2) by simp
      thus "z \<in> W2" using \<open>z \<notin> W1\<close> by (by100 blast)
    next
      fix z assume "z \<in> W2"
      have "z \<in> top1_S2" using \<open>z \<in> W2\<close> hW12(2) hC'_sub by (by100 blast)
      moreover have "z \<notin> W1" using \<open>z \<in> W2\<close> hW12(1) by (by100 blast)
      moreover have "z \<notin> C'" using \<open>z \<in> W2\<close> hW12(2) by (by100 blast)
      ultimately show "z \<in> top1_S2 - (W1 \<union> C')" by (by100 blast)
    qed
    moreover have "W1 \<union> C' \<subseteq> top1_S2" using hW12(2) hC'_sub by (by100 blast)
    ultimately show ?thesis unfolding closedin_on_def using hW2_open by simp
  qed
  have hW1_sub_C': "W1 \<subseteq> W1 \<union> C'" by (by100 blast)
  have hcl_W1_sub: "closure_on top1_S2 top1_S2_topology W1 \<subseteq> W1 \<union> C'"
    by (rule closure_on_subset_of_closed[OF hW1_C'_closed hW1_sub_C'])
  \<comment> \<open>b \<in> W2 \<subseteq> S^2 - cl(W1).\<close>
  have hW2_disj_cl: "W2 \<inter> closure_on top1_S2 top1_S2_topology W1 = {}"
  proof -
    have "W2 \<inter> (W1 \<union> C') = {}" using hW12(1,2) hC_decomp by (by100 blast)
    thus ?thesis using hcl_W1_sub by (by100 blast)
  qed
  have hb_not_cl: "b \<notin> closure_on top1_S2 top1_S2_topology W1"
    using hb hW2_disj_cl by (by100 blast)
  \<comment> \<open>S^2 - cl(W1) is open (complement of closed set).\<close>
  have hcl_W1_closed: "closedin_on top1_S2 top1_S2_topology
      (closure_on top1_S2 top1_S2_topology W1)"
    by (rule closure_on_closed[OF hTS2])
       (use hW12(2) hC_decomp hC'_sub in blast)
  have hS2_cl_open: "top1_S2 - closure_on top1_S2 top1_S2_topology W1 \<in> top1_S2_topology"
    using hcl_W1_closed unfolding closedin_on_def by (by100 blast)
  \<comment> \<open>\<alpha>(I) \<inter> (S^2-cl(W1)) \<noteq> {} since b \<in> \<alpha>(I) \<inter> (S^2-cl(W1)).\<close>
  have h\<alpha>_img_sub_S2: "\<alpha> ` I_set \<subseteq> top1_S2"
    using h\<alpha>_img_sub hC2_sub by (by100 blast)
  have hb_in_compl: "b \<in> \<alpha> ` I_set \<inter> (top1_S2 - closure_on top1_S2 top1_S2_topology W1)"
    using h\<alpha>_1 h1_I hb_not_cl h\<alpha>_img_sub_S2 by (by100 blast)
  \<comment> \<open>By connectedness: \<alpha>(I) \<inter> (cl(W1) - W1) \<noteq> {}.\<close>
  have "\<alpha> ` I_set \<inter> (closure_on top1_S2 top1_S2_topology W1 - W1) \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence h_disj2: "\<alpha> ` I_set \<inter> (closure_on top1_S2 top1_S2_topology W1 - W1) = {}" by simp
    \<comment> \<open>\<alpha>(I) \<subseteq> W1 \<union> (S^2 - cl(W1)).\<close>
    have h_sub2: "\<alpha> ` I_set \<subseteq> W1 \<union> (top1_S2 - closure_on top1_S2 top1_S2_topology W1)"
    proof
      fix z assume "z \<in> \<alpha> ` I_set"
      hence hz_S2: "z \<in> top1_S2" using h\<alpha>_img_sub_S2 by (by100 blast)
      show "z \<in> W1 \<union> (top1_S2 - closure_on top1_S2 top1_S2_topology W1)"
      proof (cases "z \<in> closure_on top1_S2 top1_S2_topology W1")
        case True
        hence "z \<notin> closure_on top1_S2 top1_S2_topology W1 - W1"
          using h_disj2 \<open>z \<in> \<alpha> ` I_set\<close> by (by100 blast)
        hence "z \<in> W1" using True by (by100 blast)
        thus ?thesis by (by100 blast)
      next
        case False thus ?thesis using hz_S2 by (by100 blast)
      qed
    qed
    \<comment> \<open>W1 and S^2-cl(W1) are disjoint open sets in S^2, both meeting \<alpha>(I). Contradiction.\<close>
    have "W1 \<inter> \<alpha> ` I_set \<in> subspace_topology top1_S2 top1_S2_topology (\<alpha> ` I_set)"
      using hW1_open unfolding subspace_topology_def by (by100 blast)
    moreover have "(top1_S2 - closure_on top1_S2 top1_S2_topology W1) \<inter> \<alpha> ` I_set
        \<in> subspace_topology top1_S2 top1_S2_topology (\<alpha> ` I_set)"
      using hS2_cl_open unfolding subspace_topology_def by (by100 blast)
    moreover have "(W1 \<inter> \<alpha> ` I_set) \<inter>
        ((top1_S2 - closure_on top1_S2 top1_S2_topology W1) \<inter> \<alpha> ` I_set) = {}"
      using subset_closure_on[of W1 top1_S2 top1_S2_topology] by (by100 blast)
    moreover have "(W1 \<inter> \<alpha> ` I_set) \<union>
        ((top1_S2 - closure_on top1_S2 top1_S2_topology W1) \<inter> \<alpha> ` I_set) = \<alpha> ` I_set"
      using h_sub2 by (by100 blast)
    ultimately show False
      using h_img_conn_S2[unfolded top1_connected_on_def]
        h\<alpha>_meets_W1 hb_in_compl by (by100 blast)
  qed
  \<comment> \<open>Get y \<in> \<alpha>(I) \<inter> (cl(W1) - W1). y \<in> C1 \<subseteq> V.\<close>
  then obtain y where hy: "y \<in> \<alpha> ` I_set" "y \<in> closure_on top1_S2 top1_S2_topology W1"
      "y \<notin> W1" by (by100 blast)
  have "y \<in> C'" using hy(2,3) hcl_W1_sub by (by100 blast)
  moreover have "y \<in> top1_S2 - C2_arc" using hy(1) h\<alpha>_img_sub by (by100 blast)
  ultimately have "y \<in> C1_arc" using hC_decomp by (by100 blast)
  hence "y \<in> V" using hC1_sub_V by (by100 blast)
  \<comment> \<open>y \<in> cl(W1) \<inter> V, V open in S^2 \<Rightarrow> V \<inter> W1 \<noteq> {} by closure_meets_open.\<close>
  show ?thesis
    using closure_meets_open[OF hTS2 _ hy(2) hV \<open>y \<in> V\<close>]
      hW12(2) hC_decomp hC'_sub by (by100 blast)
qed

theorem Theorem_63_4_JordanCurve:
  fixes C :: "(real \<times> real) set"
  assumes "top1_simple_closed_curve_on
    UNIV (product_topology_on top1_open_sets top1_open_sets) C"
  shows "\<exists>U V. U \<noteq> {} \<and> V \<noteq> {}
    \<and> U \<inter> V = {} \<and> U \<union> V = UNIV - C
    \<and> top1_path_connected_on U
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) U)
    \<and> top1_path_connected_on V
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) V)
    \<comment> \<open>One component is bounded (interior), the other unbounded (exterior).\<close>
    \<and> (\<exists>M. \<forall>p\<in>U. fst p ^ 2 + snd p ^ 2 \<le> M)
    \<and> (\<forall>M. \<exists>p\<in>V. fst p ^ 2 + snd p ^ 2 > M)
    \<comment> \<open>Both components have C as boundary.\<close>
    \<and> closure_on UNIV (product_topology_on top1_open_sets top1_open_sets) U = U \<union> C
    \<and> closure_on UNIV (product_topology_on top1_open_sets top1_open_sets) V = V \<union> C"
proof -
  let ?TR2 = "product_topology_on top1_open_sets top1_open_sets"
  \<comment> \<open>Boundary uses closure_on directly (no bridge needed).\<close>
  \<comment> \<open>Step 1 (Separation): Transfer to S^2 via stereographic projection. C corresponds
     to a simple closed curve on S^2. By Theorem 61.3, S^2 - C' has \<ge> 2 components.\<close>
  have hC_sep: "\<not> top1_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
  proof -
    \<comment> \<open>Step 1a: Get stereographic projection \<sigma>: S^2\{N} \<rightarrow> R^2.\<close>
    have hN_S2: "north_pole \<in> top1_S2" unfolding north_pole_def top1_S2_def by simp
    obtain \<sigma> where h\<sigma>: "top1_homeomorphism_on (top1_S2 - {north_pole})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
        (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) \<sigma>"
      using S2_minus_point_homeo_R2[OF hN_S2] by (by100 blast)
    \<comment> \<open>Step 1b: Transfer C to S^2: C' = \<sigma>^{-1}(C) \<subseteq> S^2\{N}.\<close>
    define \<sigma>inv where "\<sigma>inv = inv_into (top1_S2 - {north_pole}) \<sigma>"
    define C' where "C' = \<sigma>inv ` C"
    have hC'_sub: "C' \<subseteq> top1_S2 - {north_pole}" unfolding C'_def \<sigma>inv_def
    proof
      fix x assume "x \<in> inv_into (top1_S2 - {north_pole}) \<sigma> ` C"
      then obtain c where hc: "c \<in> C" "x = inv_into (top1_S2 - {north_pole}) \<sigma> c" by (by100 blast)
      have hsurj: "\<sigma> ` (top1_S2 - {north_pole}) = UNIV"
        using h\<sigma> unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have "c \<in> \<sigma> ` (top1_S2 - {north_pole})" using hsurj by simp
      hence "inv_into (top1_S2 - {north_pole}) \<sigma> c \<in> top1_S2 - {north_pole}"
        by (rule inv_into_into)
      thus "x \<in> top1_S2 - {north_pole}" using hc(2) by simp
    qed
    have hC'_sub_S2: "C' \<subseteq> top1_S2" using hC'_sub by (by100 blast)
    \<comment> \<open>Step 1c: C' is a simple closed curve on S^2.\<close>
    have hC'_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology C'"
    proof -
      \<comment> \<open>From assumption: f: S^1 \<rightarrow> R^2 continuous injective with f(S^1) = C.\<close>
      obtain f where hf: "top1_continuous_map_on top1_S1 top1_S1_topology UNIV ?TR2 f"
          and hf_inj: "inj_on f top1_S1" and hf_img: "f ` top1_S1 = C"
        using assms unfolding top1_simple_closed_curve_on_def by (by100 blast)
      \<comment> \<open>\<sigma>^{-1}: R^2 \<rightarrow> S^2\{N} is the inverse of homeomorphism \<sigma>.\<close>
      have h\<sigma>inv_cont: "top1_continuous_map_on UNIV ?TR2
          (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) \<sigma>inv"
        using h\<sigma> unfolding top1_homeomorphism_on_def \<sigma>inv_def by (by100 blast)
      have h\<sigma>inv_inj: "inj_on \<sigma>inv UNIV"
      proof -
        have "bij_betw \<sigma> (top1_S2 - {north_pole}) UNIV"
          using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
        hence "bij_betw \<sigma>inv UNIV (top1_S2 - {north_pole})"
          using \<sigma>inv_def by (simp add: bij_betw_inv_into)
        thus ?thesis unfolding bij_betw_def by (by100 blast)
      qed
      \<comment> \<open>g = \<sigma>^{-1} \<circ> f: S^1 \<rightarrow> S^2 continuous injective, g(S^1) = C'.\<close>
      define g where "g = \<sigma>inv \<circ> f"
      have hg_cont_S2N: "top1_continuous_map_on top1_S1 top1_S1_topology
          (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) g"
        unfolding g_def by (rule top1_continuous_map_on_comp[OF hf h\<sigma>inv_cont])
      \<comment> \<open>Lift to S^2: inclusion S^2\{N} \<hookrightarrow> S^2 is continuous.\<close>
      have hg_cont_S2: "top1_continuous_map_on top1_S1 top1_S1_topology
          top1_S2 top1_S2_topology g"
      proof -
        have "top1_continuous_map_on top1_S1 top1_S1_topology
            top1_S2 (subspace_topology top1_S2 top1_S2_topology top1_S2) g"
          by (rule top1_continuous_map_on_codomain_enlarge[OF hg_cont_S2N]) blast+
        moreover have "subspace_topology top1_S2 top1_S2_topology top1_S2 = top1_S2_topology"
          by (rule subspace_topology_self_carrier)
             (use top1_S2_is_topology_on_strict[unfolded is_topology_on_strict_def]
              in \<open>auto simp: is_topology_on_def\<close>)
        ultimately show ?thesis by simp
      qed
      have hg_inj: "inj_on g top1_S1"
        unfolding g_def comp_def
      proof (rule inj_onI)
        fix x y assume hx: "x \<in> top1_S1" and hy: "y \<in> top1_S1"
            and heq: "\<sigma>inv (f x) = \<sigma>inv (f y)"
        have "f x \<in> UNIV" by simp
        have "f y \<in> UNIV" by simp
        have "f x = f y" using h\<sigma>inv_inj heq unfolding inj_on_def by (by100 blast)
        thus "x = y" using hf_inj hx hy unfolding inj_on_def by (by100 blast)
      qed
      have hg_img: "g ` top1_S1 = C'"
        unfolding g_def C'_def image_comp[symmetric] using hf_img by simp
      show ?thesis unfolding top1_simple_closed_curve_on_def
        using hg_cont_S2 hg_inj hg_img by (by100 blast)
    qed
    \<comment> \<open>Step 1d: By Theorem 61.3, S^2\C' is not connected.\<close>
    have hS2_C'_sep: "top1_separates_on top1_S2 top1_S2_topology C'"
      by (rule Theorem_61_3_JordanSeparation_S2[OF top1_S2_is_topology_on_strict hC'_scc])
    \<comment> \<open>Step 1e: Transfer non-connectivity back to R^2.
       S^2\C' = (S^2\{N}\C') \<union> {N}. \<sigma> maps S^2\{N}\C' homeo to R^2\C.
       S^2\C' not connected \<Rightarrow> R^2\C not connected (if R^2\C connected,
       \<sigma>^{-1}(R^2\C) connected, and adding {N} preserves connectivity since
       N is a limit point of \<sigma>^{-1}(R^2\C), giving S^2\C' connected \<Rightarrow> contradiction).\<close>
    \<comment> \<open>Contrapositive: if R^2\C connected, then S^2\C' connected (contradiction).
       S^2\C' = \<sigma>^{-1}(R^2\C) \<union> {N}. \<sigma>^{-1}(R^2\C) connected (homeo image).
       N \<in> closure(\<sigma>^{-1}(R^2\C)) (unbounded points map near N).
       Connected \<union> limit point = connected.\<close>
    show ?thesis
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence hR2C_conn: "top1_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
        by simp
      \<comment> \<open>\<sigma>^{-1}(R^2\C) connected.\<close>
      have h\<sigma>inv_R2C_conn: "top1_connected_on (\<sigma>inv ` (UNIV - C))
          (subspace_topology top1_S2 top1_S2_topology (\<sigma>inv ` (UNIV - C)))"
      proof -
        \<comment> \<open>\<sigma>inv continuous from R^2 to S^2\{N}. Restrict domain to UNIV-C.\<close>
        have h\<sigma>inv_cont: "top1_continuous_map_on UNIV ?TR2
            (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) \<sigma>inv"
          using h\<sigma> unfolding top1_homeomorphism_on_def \<sigma>inv_def by (by100 blast)
        have hTR2: "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
              top1_open_sets_is_topology_on_UNIV] by simp
        have hTR2C: "is_topology_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
          by (rule subspace_topology_is_topology_on[OF hTR2]) simp
        have h\<sigma>inv_cont_UC: "top1_continuous_map_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))
            (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) \<sigma>inv"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF h\<sigma>inv_cont]) simp
        have hTS2N: "is_topology_on (top1_S2 - {north_pole})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))"
        proof -
          have hTS2: "is_topology_on top1_S2 top1_S2_topology"
            using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
          show ?thesis by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
        qed
        \<comment> \<open>By Theorem_23_5: \<sigma>inv(UNIV-C) connected in subspace of S^2\{N}.\<close>
        have "top1_connected_on (\<sigma>inv ` (UNIV - C))
            (subspace_topology (top1_S2 - {north_pole})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
              (\<sigma>inv ` (UNIV - C)))"
          by (rule Theorem_23_5[OF hTR2C hTS2N hR2C_conn h\<sigma>inv_cont_UC])
        \<comment> \<open>Bridge: subspace of S^2\{N} = subspace of S^2 (transitivity).\<close>
        moreover have "\<sigma>inv ` (UNIV - C) \<subseteq> top1_S2 - {north_pole}"
        proof -
          have hbij_\<sigma>: "bij_betw \<sigma> (top1_S2 - {north_pole}) UNIV"
            using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
          have "bij_betw \<sigma>inv UNIV (top1_S2 - {north_pole})"
            unfolding \<sigma>inv_def by (rule bij_betw_inv_into[OF hbij_\<sigma>])
          thus ?thesis unfolding bij_betw_def by (by100 blast)
        qed
        moreover have "subspace_topology (top1_S2 - {north_pole})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
            (\<sigma>inv ` (UNIV - C))
            = subspace_topology top1_S2 top1_S2_topology (\<sigma>inv ` (UNIV - C))"
          by (rule subspace_topology_trans) (use \<open>\<sigma>inv ` (UNIV - C) \<subseteq> top1_S2 - {north_pole}\<close> in blast)
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>S^2\C' = \<sigma>^{-1}(R^2\C) \<union> {N}.\<close>
      have hS2C'_eq: "top1_S2 - C' = \<sigma>inv ` (UNIV - C) \<union> {north_pole}"
      proof -
        have hbij: "bij_betw \<sigma> (top1_S2 - {north_pole}) UNIV"
          using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
        have hsurj: "\<sigma> ` (top1_S2 - {north_pole}) = UNIV"
          using hbij unfolding bij_betw_def by (by100 blast)
        have hinj: "inj_on \<sigma> (top1_S2 - {north_pole})"
          using hbij unfolding bij_betw_def by (by100 blast)
        have hbij_inv: "bij_betw \<sigma>inv UNIV (top1_S2 - {north_pole})"
          unfolding \<sigma>inv_def by (rule bij_betw_inv_into[OF hbij])
        have h\<sigma>inv_img: "\<sigma>inv ` UNIV = top1_S2 - {north_pole}"
          using hbij_inv unfolding bij_betw_def by (by100 blast)
        have h\<sigma>inv_C: "\<sigma>inv ` C = C'" unfolding C'_def \<sigma>inv_def by simp
        have hinj_inv: "inj_on \<sigma>inv UNIV"
          using hbij_inv unfolding bij_betw_def by (by100 blast)
        \<comment> \<open>\<sigma>^{-1}(R^2\C) = \<sigma>^{-1}(UNIV) \ \<sigma>^{-1}(C) = (S^2\{N}) \ C'.\<close>
        have "\<sigma>inv ` (UNIV - C) = (top1_S2 - {north_pole}) - C'"
        proof -
          have "\<sigma>inv ` (UNIV - C) = \<sigma>inv ` UNIV - \<sigma>inv ` C"
            by (rule inj_on_image_set_diff[OF hinj_inv]) blast+
          also have "... = (top1_S2 - {north_pole}) - C'"
            using h\<sigma>inv_img h\<sigma>inv_C by simp
          finally show ?thesis .
        qed
        \<comment> \<open>S^2\C' = ((S^2\{N})\C') \<union> ({N}\C'). N \<notin> C' since C' \<subseteq> S^2\{N}.\<close>
        have "north_pole \<notin> C'" using hC'_sub by (by100 blast)
        hence "top1_S2 - C' = ((top1_S2 - {north_pole}) - C') \<union> {north_pole}"
          using hN_S2 by (by100 blast)
        thus ?thesis using \<open>\<sigma>inv ` (UNIV - C) = (top1_S2 - {north_pole}) - C'\<close> by simp
      qed
      \<comment> \<open>N \<in> closure(\<sigma>^{-1}(R^2\C)) in S^2 topology.\<close>
      have hN_closure: "north_pole \<in> closure_on top1_S2 top1_S2_topology (\<sigma>inv ` (UNIV - C))"
      proof -
        \<comment> \<open>\<sigma>inv(R^2\C) = (S^2\C')\{N}. Since C' \<subseteq> S^2\{N}, N \<notin> C', N \<in> S^2\C'.
           S^2\C' is open (C' closed = compact in Hausdorff S^2).
           For N \<in> closure((S^2\C')\{N}): every open W \<ni> N intersects (S^2\C')\{N}.
           W \<inter> (S^2\C') is open, contains N. If = {N}, then {N} open in S^2 \<Rightarrow> FALSE.
           So \<exists> point \<noteq> N in W \<inter> (S^2\C') = W \<inter> (S^2\C')\{N}.\<close>
        have hN_notin_C': "north_pole \<notin> C'" using hC'_sub by (by100 blast)
        have hC'_closed: "closedin_on top1_S2 top1_S2_topology C'"
        proof -
          \<comment> \<open>C' = \<sigma>inv(C). \<sigma>inv continuous, C compact \<Rightarrow> C' compact \<Rightarrow> closed in Hausdorff S^2.\<close>
          \<comment> \<open>Actually C' \<subseteq> S^2\{N} \<subseteq> S^2. C' compact in S^2\{N} subspace.
             Compact in Hausdorff \<Rightarrow> closed in Hausdorff \<Rightarrow> closed in S^2.\<close>
          \<comment> \<open>C compact (continuous image of S^1 which is compact).
             \<sigma>inv continuous from R^2 to S^2\{N}. C' = \<sigma>inv(C) compact.\<close>
          have "C \<subseteq> UNIV" by simp
          have hC_compact_std: "compact C"
          proof -
            obtain f where "top1_continuous_map_on top1_S1 top1_S1_topology UNIV ?TR2 f" "f ` top1_S1 = C"
              using assms unfolding top1_simple_closed_curve_on_def by (by100 blast)
            have "compact top1_S1" using S1_compact
              top1_compact_on_subspace_UNIV_iff_compact[of top1_S1]
              product_topology_on_open_sets_real2
              unfolding top1_S1_topology_def by (by100 simp)
            have "compact (f ` top1_S1)"
            proof (rule compact_continuous_image)
              show "continuous_on top1_S1 f"
                unfolding continuous_on_open_invariant
              proof (intro allI impI)
                fix B :: "(real \<times> real) set" assume "open B"
                have "B \<in> ?TR2" using \<open>open B\<close> product_topology_on_open_sets_real2
                  unfolding top1_open_sets_def by (by100 simp)
                hence "{x \<in> top1_S1. f x \<in> B} \<in> top1_S1_topology"
                  using \<open>top1_continuous_map_on top1_S1 top1_S1_topology UNIV ?TR2 f\<close>
                  unfolding top1_continuous_map_on_def by (by100 blast)
                then obtain W where "W \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
                    and "{x \<in> top1_S1. f x \<in> B} = top1_S1 \<inter> W"
                  unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
                have "open W" using \<open>W \<in> _\<close> product_topology_on_open_sets_real2
                  unfolding top1_open_sets_def by (by100 simp)
                thus "\<exists>A. open A \<and> A \<inter> top1_S1 = f -` B \<inter> top1_S1"
                  using \<open>{x \<in> top1_S1. f x \<in> B} = top1_S1 \<inter> W\<close> by (by100 blast)
              qed
              show "compact top1_S1" by (rule \<open>compact top1_S1\<close>)
            qed
            thus ?thesis using \<open>f ` top1_S1 = C\<close> by simp
          qed
          have hC'_compact_std: "compact C'"
          proof -
            \<comment> \<open>\<sigma>inv continuous on C (standard topology): bridge from custom.\<close>
            have h\<sigma>inv_cont_std: "continuous_on C \<sigma>inv"
            proof -
              have hinv_cust: "top1_continuous_map_on UNIV ?TR2
                  (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
                  \<sigma>inv"
                using h\<sigma> unfolding top1_homeomorphism_on_def \<sigma>inv_def by (by100 blast)
              show ?thesis unfolding continuous_on_open_invariant
              proof (intro allI impI)
                fix V :: "(real\<times>real\<times>real) set" assume "open V"
                have "V \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)"
                  using \<open>open V\<close> unfolding top1_open_sets_def by simp
                \<comment> \<open>V \<inter> (S^2\{N}) open in subspace S^2\{N}.\<close>
                have hV_sub: "V \<inter> (top1_S2 - {north_pole}) \<in>
                    subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
                proof -
                  have hR3eq: "top1_S2_topology = subspace_topology UNIV
                      (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
                    unfolding top1_S2_topology_def
                    using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                          product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
                  have hS2N_sub: "top1_S2 - {north_pole} \<subseteq> top1_S2" by (by100 blast)
                  have "subspace_topology top1_S2 (subspace_topology UNIV
                      (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2) (top1_S2 - {north_pole})
                      = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) (top1_S2 - {north_pole})"
                    by (rule subspace_topology_trans[OF hS2N_sub])
                  hence "subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})
                      = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) (top1_S2 - {north_pole})"
                    using hR3eq by simp
                  thus ?thesis using \<open>V \<in> top1_open_sets\<close> unfolding subspace_topology_def by (by100 blast)
                qed
                \<comment> \<open>Preimage under \<sigma>inv: {y \<in> UNIV. \<sigma>inv y \<in> V \<inter> (S^2\{N})} \<in> TR2.\<close>
                have "{y \<in> UNIV. \<sigma>inv y \<in> V \<inter> (top1_S2 - {north_pole})}
                    \<in> product_topology_on top1_open_sets top1_open_sets"
                  using hinv_cust hV_sub unfolding top1_continuous_map_on_def by (by100 blast)
                \<comment> \<open>Since \<sigma>inv always maps into S^2\{N}, preimage of V = preimage of V \<inter> (S^2\{N}).\<close>
                have "\<forall>y. \<sigma>inv y \<in> top1_S2 - {north_pole}"
                  using hinv_cust unfolding top1_continuous_map_on_def by (by100 blast)
                hence heq: "{y \<in> UNIV. \<sigma>inv y \<in> V} = {y \<in> UNIV. \<sigma>inv y \<in> V \<inter> (top1_S2 - {north_pole})}"
                  by (by100 blast)
                have "{y \<in> UNIV. \<sigma>inv y \<in> V} \<in> product_topology_on top1_open_sets top1_open_sets"
                  using \<open>{y \<in> UNIV. \<sigma>inv y \<in> V \<inter> _} \<in> _\<close> heq by simp
                hence "open {y. \<sigma>inv y \<in> V}"
                  using product_topology_on_open_sets_real2 unfolding top1_open_sets_def by (by100 simp)
                moreover have "{y. \<sigma>inv y \<in> V} \<inter> C = \<sigma>inv -` V \<inter> C" by (by100 blast)
                ultimately show "\<exists>T. open T \<and> T \<inter> C = \<sigma>inv -` V \<inter> C" by (by100 blast)
              qed
            qed
            show ?thesis unfolding C'_def
              by (rule compact_continuous_image[OF h\<sigma>inv_cont_std hC_compact_std])
          qed
          have "closed C'" using compact_imp_closed[OF hC'_compact_std] .
          \<comment> \<open>closed in R^3 + C' \<subseteq> S^2 \<Rightarrow> closed in S^2 (subspace).\<close>
          show ?thesis unfolding closedin_on_def
          proof (intro conjI)
            show "C' \<subseteq> top1_S2" by (rule hC'_sub_S2)
            show "top1_S2 - C' \<in> top1_S2_topology"
            proof -
              have "open (- C')" using open_Compl[OF \<open>closed C'\<close>] .
              have hR3eq: "top1_S2_topology = subspace_topology UNIV
                  (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
                unfolding top1_S2_topology_def
                using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                      product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
              have "- C' \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)"
                using \<open>open (- C')\<close> unfolding top1_open_sets_def by simp
              have "top1_S2 \<inter> (- C') = top1_S2 - C'" by (by100 blast)
              have "top1_S2 - C' \<in> subspace_topology UNIV
                  (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
                using \<open>- C' \<in> top1_open_sets\<close> \<open>top1_S2 \<inter> (- C') = top1_S2 - C'\<close>
                unfolding subspace_topology_def by (by100 blast)
              thus ?thesis using hR3eq by simp
            qed
          qed
        qed
        have hS2C'_open: "top1_S2 - C' \<in> top1_S2_topology"
        proof -
          have hTS2_loc: "is_topology_on top1_S2 top1_S2_topology"
            using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
          show ?thesis using hC'_closed hTS2_loc unfolding closedin_on_def is_topology_on_def
            by (by100 blast)
        qed
        have hN_in_S2C': "north_pole \<in> top1_S2 - C'" using hN_S2 hN_notin_C' by (by100 blast)
        \<comment> \<open>\<sigma>inv(R^2\C) = (S^2\{N})\C' = (S^2\C')\{N}.\<close>
        have h\<sigma>inv_eq: "\<sigma>inv ` (UNIV - C) = (top1_S2 - C') - {north_pole}"
        proof -
          have "top1_S2 - C' = \<sigma>inv ` (UNIV - C) \<union> {north_pole}" by (rule hS2C'_eq)
          moreover have "north_pole \<notin> \<sigma>inv ` (UNIV - C)"
          proof -
            have hbij_\<sigma>: "bij_betw \<sigma> (top1_S2 - {north_pole}) UNIV"
              using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
            have "bij_betw \<sigma>inv UNIV (top1_S2 - {north_pole})"
              unfolding \<sigma>inv_def by (rule bij_betw_inv_into[OF hbij_\<sigma>])
            hence "\<sigma>inv ` UNIV \<subseteq> top1_S2 - {north_pole}"
              unfolding bij_betw_def by (by100 blast)
            hence "\<sigma>inv ` (UNIV - C) \<subseteq> top1_S2 - {north_pole}" by (by100 blast)
            thus ?thesis by (by100 blast)
          qed
          ultimately show ?thesis by (by100 blast)
        qed
        \<comment> \<open>N \<in> closure((S^2\C')\{N}): same as S2_connected argument.\<close>
        show ?thesis unfolding h\<sigma>inv_eq closure_on_def
        proof (rule InterI)
          fix D assume hD: "D \<in> {Ca. closedin_on top1_S2 top1_S2_topology Ca \<and>
              (top1_S2 - C') - {north_pole} \<subseteq> Ca}"
          hence hD_closed: "closedin_on top1_S2 top1_S2_topology D"
              and hD_sup: "(top1_S2 - C') - {north_pole} \<subseteq> D" by auto
          have "top1_S2 - D \<subseteq> C' \<union> {north_pole}"
          proof -
            have "top1_S2 - D \<subseteq> top1_S2 - ((top1_S2 - C') - {north_pole})"
              using hD_sup by (by100 blast)
            also have "... \<subseteq> C' \<union> {north_pole}" by (by100 blast)
            finally show ?thesis .
          qed
          have hD_open: "top1_S2 - D \<in> top1_S2_topology"
          proof -
            have hTS2_loc: "is_topology_on top1_S2 top1_S2_topology"
              using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
            show ?thesis using hD_closed hTS2_loc unfolding closedin_on_def is_topology_on_def
              by (by100 blast)
          qed
          \<comment> \<open>If N \<notin> D: then N \<in> S^2\D which is open and \<subseteq> C'\<union>{N}.
             So S^2\D is open and contained in C'\<union>{N}. Since N \<in> S^2\D,
             S^2\D \<inter> (S^2\C') is open (intersection of opens) and contains... hmm.
             Actually: S^2\D \<subseteq> C'\<union>{N} and N \<in> S^2\D.
             (S^2\D)\{N} \<subseteq> C'. And S^2\D is open. If S^2\D = {N}, then {N} open → FALSE.
             If S^2\D has another point x \<noteq> N, then x \<in> C'. But also x \<in> S^2\D \<subseteq> S^2.
             Actually S^2\D is open and \<subseteq> C'\<union>{N}. The complement S^2\(C'\<union>{N}) \<subseteq> D.
             Since C'\<union>{N} is closed (C' closed, {N} closed in Hausdorff, finite union of closed),
             S^2\(C'\<union>{N}) is open. So D \<supseteq> open set.
             Hmm, this doesn't directly help.\<close>
          show "north_pole \<in> D"
          proof (rule ccontr)
            assume "north_pole \<notin> D"
            hence "north_pole \<in> top1_S2 - D" using hN_S2 by (by100 blast)
            \<comment> \<open>S^2\D is open, \<subseteq> C'\<union>{N}, contains N.
               If S^2\D = {N}: {N} open in S^2 \<Rightarrow> FALSE (proved in S2_connected).\<close>
            have "top1_S2 - D \<subseteq> C' \<union> {north_pole}" by (rule \<open>top1_S2 - D \<subseteq> C' \<union> {north_pole}\<close>)
            \<comment> \<open>(S^2\D) \<inter> (S^2\C') \<subseteq> {N}.\<close>
            have "(top1_S2 - D) \<inter> (top1_S2 - C') \<subseteq> {north_pole}"
              using \<open>top1_S2 - D \<subseteq> C' \<union> {north_pole}\<close> by (by100 blast)
            \<comment> \<open>(S^2\D) \<inter> (S^2\C') open (intersection of opens) and contains N.\<close>
            have "(top1_S2 - D) \<inter> (top1_S2 - C') \<in> top1_S2_topology"
            proof -
              have hTS2_loc: "is_topology_on top1_S2 top1_S2_topology"
                using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
              show ?thesis by (rule topology_inter_open[OF hTS2_loc hD_open hS2C'_open])
            qed
            have "north_pole \<in> (top1_S2 - D) \<inter> (top1_S2 - C')"
              using \<open>north_pole \<in> top1_S2 - D\<close> hN_in_S2C' by (by100 blast)
            \<comment> \<open>So (S^2\D) \<inter> (S^2\C') is a nonempty open set \<subseteq> {N}. Hence = {N}. So {N} \<in> S^2_topology.\<close>
            hence "(top1_S2 - D) \<inter> (top1_S2 - C') = {north_pole}"
              using \<open>(top1_S2 - D) \<inter> (top1_S2 - C') \<subseteq> {north_pole}\<close> by (by100 blast)
            hence "{north_pole} \<in> top1_S2_topology"
              using \<open>(top1_S2 - D) \<inter> (top1_S2 - C') \<in> top1_S2_topology\<close> by simp
            \<comment> \<open>{N} open in S^2 \<Rightarrow> FALSE (same argument as S2_connected).\<close>
            show False using singleton_not_open_in_S2[OF hN_S2] \<open>{north_pole} \<in> top1_S2_topology\<close> by simp
          qed
        qed
      qed
      \<comment> \<open>Connected set \<union> limit point = connected. Use Theorem 23.4.\<close>
      have "top1_connected_on (top1_S2 - C') (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C'))"
      proof -
        have hTS2_loc: "is_topology_on top1_S2 top1_S2_topology"
          using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
        have hA_sub_S2: "\<sigma>inv ` (UNIV - C) \<subseteq> top1_S2"
        proof -
          have "\<sigma>inv ` (UNIV - C) \<subseteq> top1_S2 - {north_pole}"
          proof -
            have h\<sigma>inv_img_sub: "\<sigma>inv ` UNIV \<subseteq> top1_S2 - {north_pole}"
            proof -
              have hbij: "bij_betw \<sigma> (top1_S2 - {north_pole}) UNIV"
                using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
              have "bij_betw \<sigma>inv UNIV (top1_S2 - {north_pole})"
                unfolding \<sigma>inv_def by (rule bij_betw_inv_into[OF hbij])
              thus ?thesis unfolding bij_betw_def by (by100 blast)
            qed
            thus ?thesis by (by100 blast)
          qed
          thus ?thesis by (by100 blast)
        qed
        have hB_sub_S2: "top1_S2 - C' \<subseteq> top1_S2" by (by100 blast)
        have hA_sub_B: "\<sigma>inv ` (UNIV - C) \<subseteq> top1_S2 - C'"
          using hS2C'_eq by (by100 blast)
        have hB_sub_cl: "top1_S2 - C' \<subseteq> closure_on top1_S2 top1_S2_topology (\<sigma>inv ` (UNIV - C))"
        proof -
          have hA_sub_cl: "\<sigma>inv ` (UNIV - C) \<subseteq> closure_on top1_S2 top1_S2_topology (\<sigma>inv ` (UNIV - C))"
            by (rule subset_closure_on)
          have hN_in_cl: "north_pole \<in> closure_on top1_S2 top1_S2_topology (\<sigma>inv ` (UNIV - C))"
            by (rule hN_closure)
          show ?thesis using hS2C'_eq hA_sub_cl hN_in_cl by (by100 blast)
        qed
        show ?thesis
          by (rule Theorem_23_4[OF hTS2_loc hA_sub_S2 hB_sub_S2 hA_sub_B hB_sub_cl h\<sigma>inv_R2C_conn])
      qed
      thus False using hS2_C'_sep unfolding top1_separates_on_def by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 2 (Exactly two components): Decompose C = C_1 \<union> C_2 (two arcs with endpoints a, b).
     Transfer to S^2, apply Theorem 63.5 (via 63.2 + 63.3), transfer back.\<close>
  \<comment> \<open>Step 2a: Decompose C into two arcs.\<close>
  \<comment> \<open>Step 2b: Transfer arcs to S^2 via \<sigma>^{-1}. Get SCC and two arcs on S^2.\<close>
  \<comment> \<open>Step 2c: By 63.2, arcs don't separate S^2. By 63.5, exactly 2 components on S^2.\<close>
  \<comment> \<open>Step 2d: Transfer 2 components back to R^2.\<close>
  obtain U V where hUV_ne: "U \<noteq> {}" "V \<noteq> {}" and hUV_disj: "U \<inter> V = {}"
      and hUV_cover: "U \<union> V = UNIV - C"
      and hU_conn: "top1_connected_on U (subspace_topology UNIV ?TR2 U)"
      and hV_conn: "top1_connected_on V (subspace_topology UNIV ?TR2 V)"
      and hU_bdd_raw: "\<exists>M. \<forall>p\<in>U. fst p ^ 2 + snd p ^ 2 \<le> M"
      and hV_unbdd_raw: "\<forall>M. \<exists>p\<in>V. fst p ^ 2 + snd p ^ 2 > M"
      and hU_bdy_raw: "closure_on UNIV ?TR2 U = U \<union> C"
      and hV_bdy_raw: "closure_on UNIV ?TR2 V = V \<union> C"
  proof -
    \<comment> \<open>Step 2a: Decompose C into two arcs C1, C2 with C1 \<inter> C2 = {p, q}.\<close>
    obtain C1_arc C2_arc p_arc q_arc where
        hC_decomp: "C = C1_arc \<union> C2_arc"
        and hC_inter: "C1_arc \<inter> C2_arc = {p_arc, q_arc}"
        and hpq_ne: "p_arc \<noteq> q_arc"
        and hC1_arc: "top1_is_arc_on C1_arc
            (subspace_topology UNIV ?TR2 C1_arc)"
        and hC2_arc: "top1_is_arc_on C2_arc
            (subspace_topology UNIV ?TR2 C2_arc)"
    proof -
      have hR2_strict: "is_topology_on_strict (UNIV :: (real\<times>real) set) ?TR2"
      proof -
        have "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
              top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding is_topology_on_strict_def by (by100 blast)
      qed
      have hR2_haus: "is_hausdorff_on (UNIV :: (real\<times>real) set) ?TR2"
        by (rule top1_R2_is_hausdorff)
      obtain A1 A2 aa bb where hd: "C = A1 \<union> A2" "A1 \<inter> A2 = {aa, bb}" "aa \<noteq> bb"
          "top1_is_arc_on A1 (subspace_topology UNIV ?TR2 A1)"
          "top1_is_arc_on A2 (subspace_topology UNIV ?TR2 A2)"
        using simple_closed_curve_arc_decomposition[OF assms hR2_strict hR2_haus] by (by100 blast)
      show ?thesis using hd by (intro that[of A1 A2 aa bb]) (by100 blast)+
    qed
    \<comment> \<open>Step 2b: Transfer to S^2 via \<sigma>^{-1}. Get arcs C1', C2' on S^2.\<close>
    \<comment> \<open>Step 2c: On S^2: C1', C2' are arcs (don't separate by 63.2).
       C1' \<inter> C2' = {p', q'}, card = 2. C1', C2' closed, connected.
       By 63.5: C1' \<union> C2' separates S^2 into exactly 2 components.\<close>
    \<comment> \<open>Step 2d: Transfer 2 components back to R^2.\<close>
    \<comment> \<open>Step 2e: Identify bounded/unbounded. Boundary = C.\<close>
    \<comment> \<open>Step 2b: Transfer arcs to S^2 via \<sigma>^{-1} (same as step 1 transfer).
       Step 2c: On S^2, apply 63.2 (arcs don't separate — PROVED!) and
       63.5 (exactly 2 components — needs 63.1(c)+\<pi>_1\<cong>Z).
       Step 2d: Transfer back to R^2.
       Step 2e: Bounded/unbounded + boundary.\<close>
    \<comment> \<open>C1_arc, C2_arc don't separate S^2 (by Theorem_63_2 applied on S^2).
       This requires transferring arcs to S^2 and applying 63.2 there.
       The transfer uses the same \<sigma>^{-1} as in step 1.\<close>
    \<comment> \<open>C1_arc and C2_arc don't separate S^2 (by Theorem_63_2 after transfer).
       The transfer requires re-obtaining \<sigma>^{-1} (it was local to hC_sep proof).\<close>
    \<comment> \<open>NOTE: \<sigma>inv is not in scope here (it was inside hC_sep's proof block).
       The proof requires: obtain \<sigma>, define \<sigma>inv, transfer arcs, apply 63.2.\<close>
    \<comment> \<open>By 63.5: exactly 2 components on S^2.\<close>
    \<comment> \<open>Transfer back to R^2 and identify bounded/unbounded.\<close>
    \<comment> \<open>Step 2b: Re-obtain stereographic projection \<sigma>.\<close>
    obtain \<sigma>2 where h\<sigma>2: "top1_homeomorphism_on (top1_S2 - {north_pole})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
        (UNIV :: (real \<times> real) set) ?TR2 \<sigma>2"
      using S2_minus_point_homeo_R2[of north_pole] north_pole_in_S2 by blast
    define \<sigma>2inv where "\<sigma>2inv = inv_into (top1_S2 - {north_pole}) \<sigma>2"
    \<comment> \<open>\<sigma>2inv maps R^2 homeomorphically to S^2\{N}.\<close>
    have h\<sigma>2_bij: "bij_betw \<sigma>2 (top1_S2 - {north_pole}) UNIV"
      using h\<sigma>2 unfolding top1_homeomorphism_on_def by (by100 blast)
    have h\<sigma>2inv_bij: "bij_betw \<sigma>2inv UNIV (top1_S2 - {north_pole})"
      unfolding \<sigma>2inv_def by (rule bij_betw_inv_into[OF h\<sigma>2_bij])
    \<comment> \<open>Transfer arcs: C1' = \<sigma>2inv(C1_arc), C2' = \<sigma>2inv(C2_arc).\<close>
    define C1' where "C1' = \<sigma>2inv ` C1_arc"
    define C2' where "C2' = \<sigma>2inv ` C2_arc"
    define C' where "C' = \<sigma>2inv ` C"
    \<comment> \<open>C' = C1' \<union> C2', C1' \<inter> C2' = {\<sigma>2inv p_arc, \<sigma>2inv q_arc}.\<close>
    \<comment> \<open>C' is a simple closed curve on S^2 (in S^2\{N}).\<close>
    \<comment> \<open>Apply Theorem_63_5 to C1', C2' on S^2 to get exactly 2 components.\<close>
    \<comment> \<open>Transfer components back to R^2 via \<sigma>2.\<close>
    \<comment> \<open>C' \<subseteq> S^2\{N} (since \<sigma>2inv maps into S^2\{N}).\<close>
    have hC'_sub: "C' \<subseteq> top1_S2 - {north_pole}"
      unfolding C'_def using h\<sigma>2inv_bij unfolding bij_betw_def by (by100 blast)
    have hC'_sub_S2: "C' \<subseteq> top1_S2" using hC'_sub by (by100 blast)
    \<comment> \<open>C' = C1' \<union> C2'.\<close>
    have hC'_decomp: "C' = C1' \<union> C2'"
      unfolding C'_def C1'_def C2'_def using hC_decomp by (by100 blast)
    \<comment> \<open>N \<notin> C' (since C' \<subseteq> S^2\{N}).\<close>
    have hN_not_C': "north_pole \<notin> C'"
      using hC'_sub by (by100 blast)
    \<comment> \<open>C' is a simple closed curve on S^2 (transferred from R^2 via \<sigma>2inv).\<close>
    have hC'_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology C'"
      unfolding top1_simple_closed_curve_on_def
    proof -
      obtain f0 where hf0_cont: "top1_continuous_map_on top1_S1 top1_S1_topology UNIV ?TR2 f0"
          and hf0_inj: "inj_on f0 top1_S1" and hf0_img: "f0 ` top1_S1 = C"
        using assms unfolding top1_simple_closed_curve_on_def by (by100 blast)
      define g where "g = \<sigma>2inv \<circ> f0"
      \<comment> \<open>\<sigma>2inv continuous R^2 \<rightarrow> S^2\{N}.\<close>
      have h\<sigma>2inv_cont: "top1_continuous_map_on UNIV ?TR2 (top1_S2 - {north_pole})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) \<sigma>2inv"
        using homeomorphism_inverse[OF h\<sigma>2, folded \<sigma>2inv_def]
        unfolding top1_homeomorphism_on_def by (by100 blast)
      \<comment> \<open>Compose: g = \<sigma>2inv \<circ> f0 continuous S^1 \<rightarrow> S^2\{N}.\<close>
      have hg_cont_S2N: "top1_continuous_map_on top1_S1 top1_S1_topology (top1_S2 - {north_pole})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) g"
        unfolding g_def by (rule top1_continuous_map_on_comp[OF hf0_cont h\<sigma>2inv_cont])
      \<comment> \<open>Continuous into subspace \<Rightarrow> continuous into ambient S^2.\<close>
      have hg_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S2 top1_S2_topology g"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix s assume "s \<in> top1_S1"
        thus "g s \<in> top1_S2"
          using hg_cont_S2N unfolding top1_continuous_map_on_def by (by100 blast)
      next
        fix V assume hV: "V \<in> top1_S2_topology"
        have hg_map: "\<forall>s\<in>top1_S1. g s \<in> top1_S2 - {north_pole}"
          using hg_cont_S2N unfolding top1_continuous_map_on_def by (by100 blast)
        have hinter_open: "(top1_S2 - {north_pole}) \<inter> V \<in>
            subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
          using hV unfolding subspace_topology_def by (by100 blast)
        have "{s \<in> top1_S1. g s \<in> (top1_S2 - {north_pole}) \<inter> V} \<in> top1_S1_topology"
          using hg_cont_S2N hinter_open unfolding top1_continuous_map_on_def by (by100 blast)
        moreover have "{s \<in> top1_S1. g s \<in> V} = {s \<in> top1_S1. g s \<in> (top1_S2 - {north_pole}) \<inter> V}"
          using hg_map by (by100 blast)
        ultimately show "{s \<in> top1_S1. g s \<in> V} \<in> top1_S1_topology" by simp
      qed
      \<comment> \<open>g injective (composition of injectives).\<close>
      have hg_inj: "inj_on g top1_S1"
      proof -
        have h\<sigma>2inv_inj: "inj \<sigma>2inv"
          using h\<sigma>2inv_bij unfolding bij_betw_def by (by100 blast)
        show ?thesis unfolding g_def comp_def
          using hf0_inj h\<sigma>2inv_inj unfolding inj_on_def inj_def by (by100 blast)
      qed
      \<comment> \<open>g(S^1) = C'.\<close>
      have hg_img: "g ` top1_S1 = C'"
      proof -
        have "g ` top1_S1 = \<sigma>2inv ` (f0 ` top1_S1)" unfolding g_def image_comp by simp
        thus ?thesis unfolding C'_def using hf0_img by simp
      qed
      show "\<exists>f. top1_continuous_map_on top1_S1 top1_S1_topology top1_S2 top1_S2_topology f
                \<and> inj_on f top1_S1 \<and> f ` top1_S1 = C'"
        using hg_cont hg_inj hg_img by (by100 blast)
    qed
    \<comment> \<open>C1', C2' are closed, connected subsets of S^2 with card(C1'\<inter>C2') = 2.\<close>
    \<comment> \<open>C1', C2' don't separate S^2 (by Theorem 63.2, arcs don't separate).\<close>
    \<comment> \<open>C1' is an arc on S^2: transfer arc property from R^2 via \<sigma>2inv.\<close>
    have hC1'_sub_S2N: "C1' \<subseteq> top1_S2 - {north_pole}"
      unfolding C1'_def using h\<sigma>2inv_bij unfolding bij_betw_def by (by100 blast)
    have hC2'_sub_S2N: "C2' \<subseteq> top1_S2 - {north_pole}"
      unfolding C2'_def using h\<sigma>2inv_bij unfolding bij_betw_def by (by100 blast)
    have hC1'_sub_S2: "C1' \<subseteq> top1_S2" using hC1'_sub_S2N by (by100 blast)
    have hC2'_sub_S2: "C2' \<subseteq> top1_S2" using hC2'_sub_S2N by (by100 blast)
    \<comment> \<open>Subspace topology transfer: S^2 on C1' = S^2\{N} on C1' (since C1' \<subseteq> S^2\{N}).\<close>
    have hTS2N: "is_topology_on (top1_S2 - {north_pole})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))"
      by (rule subspace_topology_is_topology_on[OF
            is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict]]) (by100 blast)
    have hC1'_top_eq: "subspace_topology top1_S2 top1_S2_topology C1'
        = subspace_topology (top1_S2 - {north_pole})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) C1'"
      by (rule subspace_topology_trans[OF hC1'_sub_S2N, symmetric])
    have hC2'_top_eq: "subspace_topology top1_S2 top1_S2_topology C2'
        = subspace_topology (top1_S2 - {north_pole})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) C2'"
      by (rule subspace_topology_trans[OF hC2'_sub_S2N, symmetric])
    \<comment> \<open>Shared: \<sigma>2inv homeomorphism + continuity + injectivity.\<close>
    have h\<sigma>2inv_homeo: "top1_homeomorphism_on UNIV ?TR2
        (top1_S2 - {north_pole})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) \<sigma>2inv"
      unfolding \<sigma>2inv_def by (rule homeomorphism_inverse[OF h\<sigma>2])
    have h\<sigma>2inv_cont: "top1_continuous_map_on UNIV ?TR2
        (top1_S2 - {north_pole})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) \<sigma>2inv"
      using h\<sigma>2inv_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    have h\<sigma>2inv_inj_global: "inj \<sigma>2inv"
      using h\<sigma>2inv_bij unfolding bij_betw_def by (by100 blast)
    \<comment> \<open>C1' is an arc on S^2.\<close>
    have hC1'_arc: "top1_is_arc_on C1' (subspace_topology top1_S2 top1_S2_topology C1')"
    proof -
      \<comment> \<open>C1_arc is an arc in R^2: get homeomorphism h1_arc: [0,1] \<rightarrow> C1_arc.\<close>
      have hC1_arc_R2: "top1_is_arc_on C1_arc (subspace_topology UNIV ?TR2 C1_arc)"
        using hC1_arc .
      obtain h1_arc where hh1_arc: "top1_homeomorphism_on I_set I_top C1_arc
          (subspace_topology UNIV ?TR2 C1_arc) h1_arc"
        using hC1_arc_R2 unfolding top1_is_arc_on_def by (by100 blast)
      \<comment> \<open>Compose: \<sigma>2inv \<circ> h1_arc : [0,1] \<rightarrow> C1' (in S^2 topology).\<close>
      \<comment> \<open>The composed homeomorphism lands in C1' with S^2\{N} subspace topology,\<close>
      \<comment> \<open>which equals S^2 subspace topology by hC1'_top_eq.\<close>
      \<comment> \<open>Define the composed map.\<close>
      define h_comp where "h_comp = \<sigma>2inv \<circ> h1_arc"
      show ?thesis unfolding top1_is_arc_on_def
      proof (intro conjI exI[of _ h_comp])
        \<comment> \<open>is_topology_on_strict: subspace of Hausdorff is strict.\<close>
        show "is_topology_on_strict C1' (subspace_topology top1_S2 top1_S2_topology C1')"
          unfolding is_topology_on_strict_def
        proof (intro conjI)
          show "is_topology_on C1' (subspace_topology top1_S2 top1_S2_topology C1')"
            by (rule subspace_topology_is_topology_on[OF
                  is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict] hC1'_sub_S2])
          show "subspace_topology top1_S2 top1_S2_topology C1' \<subseteq> Pow C1'"
            unfolding subspace_topology_def by (by100 blast)
        qed
      next
        \<comment> \<open>Extract properties of h1_arc and \<sigma>2inv.\<close>
        have hh1_bij: "bij_betw h1_arc I_set C1_arc"
          using hh1_arc unfolding top1_homeomorphism_on_def by (by100 blast)
        have hh1_cont: "top1_continuous_map_on I_set I_top C1_arc
            (subspace_topology UNIV ?TR2 C1_arc) h1_arc"
          using hh1_arc unfolding top1_homeomorphism_on_def by (by100 blast)
        \<comment> \<open>Use shared h\<sigma>2inv_cont, h\<sigma>2inv_inj_global from above.\<close>
        \<comment> \<open>bij_betw for composition.\<close>
        have hbij_comp: "bij_betw h_comp I_set C1'"
        proof -
          have "bij_betw \<sigma>2inv C1_arc C1'"
            unfolding C1'_def
            by (rule inj_on_imp_bij_betw[OF inj_on_subset[OF
                  h\<sigma>2inv_inj_global[unfolded inj_on_def[symmetric]] subset_UNIV]])
          thus ?thesis unfolding h_comp_def
            by (rule bij_betw_trans[OF hh1_bij])
        qed
        show "top1_homeomorphism_on I_set I_top C1'
            (subspace_topology top1_S2 top1_S2_topology C1') h_comp"
          unfolding top1_homeomorphism_on_def
        proof (intro conjI)
          show "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
          show "is_topology_on C1' (subspace_topology top1_S2 top1_S2_topology C1')"
            by (rule subspace_topology_is_topology_on[OF
                  is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict] hC1'_sub_S2])
          show "bij_betw h_comp I_set C1'" by (rule hbij_comp)
          \<comment> \<open>Continuity: compose h1_arc (I\<rightarrow>C1_arc in R^2) with \<sigma>2inv (R^2\<rightarrow>S^2\{N}).\<close>
          show "top1_continuous_map_on I_set I_top C1'
              (subspace_topology top1_S2 top1_S2_topology C1') h_comp"
          proof -
            \<comment> \<open>Step 1: h1_arc continuous I \<rightarrow> UNIV (embed codomain from C1_arc to UNIV).\<close>
            have hh1_to_UNIV: "top1_continuous_map_on I_set I_top UNIV ?TR2 h1_arc"
              unfolding top1_continuous_map_on_def
            proof (intro conjI ballI)
              fix x assume "x \<in> I_set"
              thus "h1_arc x \<in> UNIV" by simp
            next
              fix V :: "(real \<times> real) set" assume "V \<in> ?TR2"
              have "{x \<in> I_set. h1_arc x \<in> V} = {x \<in> I_set. h1_arc x \<in> C1_arc \<inter> V}"
              proof -
                have "\<forall>x\<in>I_set. h1_arc x \<in> C1_arc"
                  using hh1_bij unfolding bij_betw_def by (by100 blast)
                thus ?thesis by (by100 blast)
              qed
              moreover have "C1_arc \<inter> V \<in> subspace_topology UNIV ?TR2 C1_arc"
                using \<open>V \<in> ?TR2\<close> unfolding subspace_topology_def by (by100 blast)
              moreover have "{x \<in> I_set. h1_arc x \<in> C1_arc \<inter> V} \<in> I_top"
                using hh1_cont calculation(2) unfolding top1_continuous_map_on_def by (by100 blast)
              ultimately show "{x \<in> I_set. h1_arc x \<in> V} \<in> I_top" by simp
            qed
            \<comment> \<open>Step 2: compose with \<sigma>2inv: I \<rightarrow> S^2\{N}.\<close>
            have hcomp_to_S2N: "top1_continuous_map_on I_set I_top (top1_S2 - {north_pole})
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
                (\<sigma>2inv \<circ> h1_arc)"
              by (rule top1_continuous_map_on_comp[OF hh1_to_UNIV h\<sigma>2inv_cont])
            \<comment> \<open>Step 3: restrict codomain to C1' \<subseteq> S^2\{N}.\<close>
            have himg: "(\<sigma>2inv \<circ> h1_arc) ` I_set = C1'"
              using hbij_comp unfolding bij_betw_def h_comp_def by simp
            have hcomp_to_C1': "top1_continuous_map_on I_set I_top C1'
                (subspace_topology (top1_S2 - {north_pole})
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) C1')
                (\<sigma>2inv \<circ> h1_arc)"
              by (rule top1_continuous_map_on_codomain_shrink[OF hcomp_to_S2N])
                 (use himg hC1'_sub_S2N in auto)
            \<comment> \<open>Step 4: sub(S^2\{N}, sub(S^2, S^2_top, S^2\{N}), C1') = sub(S^2, S^2_top, C1').\<close>
            thus ?thesis
              using subspace_topology_trans[OF hC1'_sub_S2N, of top1_S2 top1_S2_topology]
              unfolding h_comp_def by simp
          qed
          \<comment> \<open>Inverse continuous: [0,1] compact, C1' Hausdorff. Bijective continuous
             from compact to Hausdorff is a closed map. Closed bijection = homeomorphism.\<close>
          show "top1_continuous_map_on C1'
              (subspace_topology top1_S2 top1_S2_topology C1') I_set I_top
              (inv_into I_set h_comp)"
          proof -
            define TC1' where "TC1' = subspace_topology top1_S2 top1_S2_topology C1'"
            have hTC1': "is_topology_on C1' TC1'"
              unfolding TC1'_def by (rule subspace_topology_is_topology_on[OF
                is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict] hC1'_sub_S2])
            have hI_compact: "top1_compact_on I_set I_top"
            proof -
              have "compact {0..1::real}" by (rule compact_Icc)
              moreover have "I_set = {0..1::real}" unfolding top1_unit_interval_def
                by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
              ultimately have "compact I_set" by simp
              thus ?thesis unfolding top1_unit_interval_topology_def
                using top1_compact_on_subspace_UNIV_iff_compact[of I_set] by simp
            qed
            have hC1'_haus: "is_hausdorff_on C1' TC1'"
              unfolding TC1'_def
              using conjunct2[OF conjunct2[OF Theorem_17_11]]
                top1_S2_is_hausdorff hC1'_sub_S2 by (by100 blast)
            have hcomp_fwd: "top1_continuous_map_on I_set I_top C1' TC1' h_comp"
              using \<open>top1_continuous_map_on I_set I_top C1'
                (subspace_topology top1_S2 top1_S2_topology C1') h_comp\<close>
              unfolding TC1'_def .
            \<comment> \<open>h_comp is a closed map (compact \<rightarrow> Hausdorff continuous = closed map).\<close>
            \<comment> \<open>Bijective closed map \<Rightarrow> open map \<Rightarrow> inverse continuous.\<close>
            show ?thesis unfolding TC1'_def[symmetric]
              unfolding top1_continuous_map_on_def
            proof (intro conjI ballI)
              fix y assume "y \<in> C1'"
              have "y \<in> h_comp ` I_set"
                using hbij_comp \<open>y \<in> C1'\<close> unfolding bij_betw_def by (by100 blast)
              have "inv_into I_set h_comp y \<in> I_set"
                by (rule inv_into_into[OF \<open>y \<in> h_comp ` I_set\<close>])
              thus "inv_into I_set h_comp y \<in> I_set" .
            next
              fix V assume hV: "V \<in> I_top"
              have hV_sub: "V \<subseteq> I_set"
                using hV top1_unit_interval_topology_is_topology_on
                unfolding is_topology_on_def top1_unit_interval_topology_def
                subspace_topology_def by (by100 blast)
              have hV_eq: "{y \<in> C1'. inv_into I_set h_comp y \<in> V} = h_comp ` V"
              proof (intro set_eqI iffI)
                fix y assume "y \<in> {y \<in> C1'. inv_into I_set h_comp y \<in> V}"
                hence "y \<in> C1'" "inv_into I_set h_comp y \<in> V" by simp_all
                have "y \<in> h_comp ` I_set"
                  using hbij_comp \<open>y \<in> C1'\<close> unfolding bij_betw_def by (by100 blast)
                have "h_comp (inv_into I_set h_comp y) = y"
                  by (rule f_inv_into_f[OF \<open>y \<in> h_comp ` I_set\<close>])
                thus "y \<in> h_comp ` V"
                  using \<open>inv_into I_set h_comp y \<in> V\<close> \<open>h_comp _ = y\<close> by (by100 force)
              next
                fix y assume "y \<in> h_comp ` V"
                then obtain x where hx: "x \<in> V" "y = h_comp x" by (by100 blast)
                have "x \<in> I_set" using hx(1) hV_sub by (by100 blast)
                have "y \<in> C1'" using hbij_comp \<open>x \<in> I_set\<close> hx(2) unfolding bij_betw_def by (by100 blast)
                moreover have "inv_into I_set h_comp y = x"
                  using inv_into_f_f[OF bij_betw_imp_inj_on[OF hbij_comp] \<open>x \<in> I_set\<close>] hx(2) by simp
                ultimately show "y \<in> {y \<in> C1'. inv_into I_set h_comp y \<in> V}"
                  using hx(1) by simp
              qed
              \<comment> \<open>Show h_comp ` V \<in> TC1': h_comp maps opens to opens (closed map arg).\<close>
              have hclosed_compl: "closedin_on I_set I_top (I_set - V)"
              proof -
                have "I_set - V \<subseteq> I_set" by (by100 blast)
                moreover have "I_set - (I_set - V) = V" using hV_sub by (by100 blast)
                ultimately show ?thesis unfolding closedin_on_def using hV by simp
              qed
              have "closedin_on C1' TC1' (h_comp ` (I_set - V))"
                by (rule compact_hausdorff_continuous_closed_map[OF hI_compact hC1'_haus
                      hcomp_fwd hclosed_compl])
              hence "C1' - h_comp ` (I_set - V) \<in> TC1'"
                unfolding closedin_on_def using hTC1' unfolding is_topology_on_def by (by100 blast)
              moreover have "C1' - h_comp ` (I_set - V) = h_comp ` V"
              proof -
                have hinj: "inj_on h_comp I_set" using hbij_comp unfolding bij_betw_def by (by100 blast)
                have himg: "h_comp ` I_set = C1'" using hbij_comp unfolding bij_betw_def by (by100 blast)
                have "h_comp ` V = h_comp ` (I_set - (I_set - V))"
                  using hV_sub by (by100 force)
                also have "\<dots> = h_comp ` I_set - h_comp ` (I_set - V)"
                  by (rule inj_on_image_set_diff[OF hinj]) (by100 blast)+
                finally show ?thesis using himg by simp
              qed
              ultimately show "{y \<in> C1'. inv_into I_set h_comp y \<in> V} \<in> TC1'"
                using hV_eq by simp
            qed
          qed
        qed
      qed
    qed
    have hC2'_arc: "top1_is_arc_on C2' (subspace_topology top1_S2 top1_S2_topology C2')"
    proof -
      obtain h2_arc where hh2_arc: "top1_homeomorphism_on I_set I_top C2_arc
          (subspace_topology UNIV ?TR2 C2_arc) h2_arc"
        using hC2_arc unfolding top1_is_arc_on_def by (by100 blast)
      define h_comp2 where "h_comp2 = \<sigma>2inv \<circ> h2_arc"
      show ?thesis unfolding top1_is_arc_on_def
      proof (intro conjI exI[of _ h_comp2])
        show "is_topology_on_strict C2' (subspace_topology top1_S2 top1_S2_topology C2')"
          unfolding is_topology_on_strict_def
        proof (intro conjI)
          show "is_topology_on C2' (subspace_topology top1_S2 top1_S2_topology C2')"
            by (rule subspace_topology_is_topology_on[OF
                  is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict] hC2'_sub_S2])
          show "subspace_topology top1_S2 top1_S2_topology C2' \<subseteq> Pow C2'"
            unfolding subspace_topology_def by (by100 blast)
        qed
      next
        have hh2_bij: "bij_betw h2_arc I_set C2_arc"
          using hh2_arc unfolding top1_homeomorphism_on_def by (by100 blast)
        have hh2_cont: "top1_continuous_map_on I_set I_top C2_arc
            (subspace_topology UNIV ?TR2 C2_arc) h2_arc"
          using hh2_arc unfolding top1_homeomorphism_on_def by (by100 blast)
        \<comment> \<open>Use shared h\<sigma>2inv_inj_global from above.\<close>
        have hbij_comp2: "bij_betw h_comp2 I_set C2'"
        proof -
          have "bij_betw \<sigma>2inv C2_arc C2'"
            unfolding C2'_def
            by (rule inj_on_imp_bij_betw[OF inj_on_subset[OF
                  h\<sigma>2inv_inj_global[unfolded inj_on_def[symmetric]] subset_UNIV]])
          thus ?thesis unfolding h_comp2_def
            by (rule bij_betw_trans[OF hh2_bij])
        qed
        show "top1_homeomorphism_on I_set I_top C2'
            (subspace_topology top1_S2 top1_S2_topology C2') h_comp2"
          unfolding top1_homeomorphism_on_def
        proof (intro conjI)
          show "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
          show "is_topology_on C2' (subspace_topology top1_S2 top1_S2_topology C2')"
            by (rule subspace_topology_is_topology_on[OF
                  is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict] hC2'_sub_S2])
          show "bij_betw h_comp2 I_set C2'" by (rule hbij_comp2)
          \<comment> \<open>Forward continuity: same chain as C1'.\<close>
          show "top1_continuous_map_on I_set I_top C2'
              (subspace_topology top1_S2 top1_S2_topology C2') h_comp2"
          proof -
            have hh2_to_UNIV: "top1_continuous_map_on I_set I_top UNIV ?TR2 h2_arc"
              unfolding top1_continuous_map_on_def
            proof (intro conjI ballI)
              fix x assume "x \<in> I_set" thus "h2_arc x \<in> UNIV" by simp
            next
              fix V :: "(real \<times> real) set" assume "V \<in> ?TR2"
              have "\<forall>x\<in>I_set. h2_arc x \<in> C2_arc"
                using hh2_bij unfolding bij_betw_def by (by100 blast)
              hence "{x \<in> I_set. h2_arc x \<in> V} = {x \<in> I_set. h2_arc x \<in> C2_arc \<inter> V}"
                by (by100 blast)
              moreover have "C2_arc \<inter> V \<in> subspace_topology UNIV ?TR2 C2_arc"
                using \<open>V \<in> ?TR2\<close> unfolding subspace_topology_def by (by100 blast)
              moreover have "{x \<in> I_set. h2_arc x \<in> C2_arc \<inter> V} \<in> I_top"
                using hh2_cont calculation(2) unfolding top1_continuous_map_on_def by (by100 blast)
              ultimately show "{x \<in> I_set. h2_arc x \<in> V} \<in> I_top" by simp
            qed
            \<comment> \<open>Use shared h\<sigma>2inv_cont.\<close>
            have hcomp2_to_S2N: "top1_continuous_map_on I_set I_top (top1_S2 - {north_pole})
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
                (\<sigma>2inv \<circ> h2_arc)"
              by (rule top1_continuous_map_on_comp[OF hh2_to_UNIV h\<sigma>2inv_cont])
            have himg2: "(\<sigma>2inv \<circ> h2_arc) ` I_set = C2'"
              using hbij_comp2 unfolding bij_betw_def h_comp2_def by simp
            show ?thesis
              using top1_continuous_map_on_codomain_shrink[OF hcomp2_to_S2N _ hC2'_sub_S2N]
                subspace_topology_trans[OF hC2'_sub_S2N, of top1_S2 top1_S2_topology]
                himg2 unfolding h_comp2_def by auto
          qed
          \<comment> \<open>Inverse continuity: same compact\<rightarrow>Hausdorff argument as C1'.\<close>
          show "top1_continuous_map_on C2'
              (subspace_topology top1_S2 top1_S2_topology C2') I_set I_top
              (inv_into I_set h_comp2)"
          proof -
            have hTC2': "is_topology_on C2' (subspace_topology top1_S2 top1_S2_topology C2')"
              by (rule subspace_topology_is_topology_on[OF
                is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict] hC2'_sub_S2])
            have hI_compact2: "top1_compact_on I_set I_top"
            proof -
              have "compact {0..1::real}" by (rule compact_Icc)
              moreover have "I_set = {0..1::real}" unfolding top1_unit_interval_def
                by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
              ultimately have "compact I_set" by simp
              thus ?thesis unfolding top1_unit_interval_topology_def
                using top1_compact_on_subspace_UNIV_iff_compact[of I_set] by simp
            qed
            have hC2'_haus: "is_hausdorff_on C2' (subspace_topology top1_S2 top1_S2_topology C2')"
              using conjunct2[OF conjunct2[OF Theorem_17_11]]
                top1_S2_is_hausdorff hC2'_sub_S2 by (by100 blast)
            show ?thesis
              unfolding top1_continuous_map_on_def
            proof (intro conjI ballI)
              fix y assume "y \<in> C2'"
              hence "y \<in> h_comp2 ` I_set"
                using hbij_comp2 unfolding bij_betw_def by (by100 blast)
              thus "inv_into I_set h_comp2 y \<in> I_set"
                by (rule inv_into_into)
            next
              fix V :: "real set" assume hV: "V \<in> I_top"
              have hV_sub: "V \<subseteq> I_set"
                using hV top1_unit_interval_topology_is_topology_on
                unfolding is_topology_on_def top1_unit_interval_topology_def
                subspace_topology_def by (by100 blast)
              \<comment> \<open>Closed map argument: I_set - V closed \<Rightarrow> h_comp2(I_set-V) closed \<Rightarrow> C2' - ... open.\<close>
              have hclosed_compl: "closedin_on I_set I_top (I_set - V)"
              proof -
                have "I_set - V \<subseteq> I_set" by (by100 blast)
                moreover have "I_set - (I_set - V) = V" using hV_sub by (by100 blast)
                ultimately show ?thesis unfolding closedin_on_def using hV by simp
              qed
              have "closedin_on C2' (subspace_topology top1_S2 top1_S2_topology C2')
                  (h_comp2 ` (I_set - V))"
                by (rule compact_hausdorff_continuous_closed_map[OF hI_compact2 hC2'_haus
                  \<open>top1_continuous_map_on I_set I_top C2' _ h_comp2\<close> hclosed_compl])
              hence hopen: "C2' - h_comp2 ` (I_set - V)
                  \<in> subspace_topology top1_S2 top1_S2_topology C2'"
                unfolding closedin_on_def using hTC2' unfolding is_topology_on_def by (by100 blast)
              have "C2' - h_comp2 ` (I_set - V) = h_comp2 ` V"
              proof -
                have hinj: "inj_on h_comp2 I_set" using hbij_comp2 unfolding bij_betw_def
                  by (by100 blast)
                have himg: "h_comp2 ` I_set = C2'" using hbij_comp2 unfolding bij_betw_def
                  by (by100 blast)
                have "h_comp2 ` V = h_comp2 ` (I_set - (I_set - V))"
                  using hV_sub by (by100 force)
                also have "\<dots> = h_comp2 ` I_set - h_comp2 ` (I_set - V)"
                  by (rule inj_on_image_set_diff[OF hinj]) (by100 blast)+
                finally show ?thesis using himg by simp
              qed
              hence "h_comp2 ` V \<in> subspace_topology top1_S2 top1_S2_topology C2'"
                using hopen by simp
              moreover have "{y \<in> C2'. inv_into I_set h_comp2 y \<in> V} = h_comp2 ` V"
              proof (intro set_eqI iffI)
                fix y assume "y \<in> {y \<in> C2'. inv_into I_set h_comp2 y \<in> V}"
                hence "y \<in> h_comp2 ` I_set" "inv_into I_set h_comp2 y \<in> V"
                  using hbij_comp2 unfolding bij_betw_def by simp_all
                have "h_comp2 (inv_into I_set h_comp2 y) = y"
                  by (rule f_inv_into_f[OF \<open>y \<in> h_comp2 ` I_set\<close>])
                hence "y = h_comp2 (inv_into I_set h_comp2 y)" by simp
                thus "y \<in> h_comp2 ` V" using \<open>inv_into I_set h_comp2 y \<in> V\<close> by (by100 blast)
              next
                fix y assume "y \<in> h_comp2 ` V"
                then obtain x where "x \<in> V" "y = h_comp2 x" by (by100 blast)
                thus "y \<in> {y \<in> C2'. inv_into I_set h_comp2 y \<in> V}"
                  using hV_sub hbij_comp2
                    inv_into_f_f[OF bij_betw_imp_inj_on[OF hbij_comp2]]
                  unfolding bij_betw_def by (by100 force)
              qed
              ultimately show "{y \<in> C2'. inv_into I_set h_comp2 y \<in> V}
                  \<in> subspace_topology top1_S2 top1_S2_topology C2'" by simp
            qed
          qed
        qed
      qed
    qed
    \<comment> \<open>Arc \<Rightarrow> closed (compact in Hausdorff) + connected (homeomorphic to [0,1]).\<close>
    have hC1'_closed: "closedin_on top1_S2 top1_S2_topology C1'"
    proof (rule compact_in_strict_hausdorff_closedin_on[OF top1_S2_is_hausdorff
        top1_S2_is_topology_on_strict hC1'_sub_S2])
      obtain h1 where hh1: "top1_homeomorphism_on I_set I_top C1'
          (subspace_topology top1_S2 top1_S2_topology C1') h1"
        using hC1'_arc unfolding top1_is_arc_on_def by (by100 blast)
      have hI_compact: "top1_compact_on I_set I_top"
      proof -
        have "compact {0..1::real}" by (rule compact_Icc)
        moreover have "I_set = {0..1::real}" unfolding top1_unit_interval_def
          by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
        ultimately have "compact I_set" by simp
        thus ?thesis unfolding top1_unit_interval_topology_def
          using top1_compact_on_subspace_UNIV_iff_compact[of I_set] by simp
      qed
      have hcont: "top1_continuous_map_on I_set I_top C1'
          (subspace_topology top1_S2 top1_S2_topology C1') h1"
        using hh1 unfolding top1_homeomorphism_on_def by (by100 blast)
      have hTS2_C1: "is_topology_on C1' (subspace_topology top1_S2 top1_S2_topology C1')"
        using hh1 unfolding top1_homeomorphism_on_def by (by100 blast)
      have himg: "h1 ` I_set = C1'"
        using hh1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have "top1_compact_on (h1 ` I_set) (subspace_topology C1'
          (subspace_topology top1_S2 top1_S2_topology C1') (h1 ` I_set))"
        by (rule top1_compact_on_continuous_image[OF hI_compact hTS2_C1 hcont])
      moreover have "h1 ` I_set = C1'" by (rule himg)
      moreover have "subspace_topology C1' (subspace_topology top1_S2 top1_S2_topology C1') C1'
          = subspace_topology top1_S2 top1_S2_topology C1'"
        using hC1'_arc unfolding top1_is_arc_on_def is_topology_on_strict_def
        by (intro subspace_topology_self) (by100 blast)
      ultimately show "top1_compact_on C1' (subspace_topology top1_S2 top1_S2_topology C1')"
        by simp
    qed
    have hC2'_closed: "closedin_on top1_S2 top1_S2_topology C2'"
    proof (rule compact_in_strict_hausdorff_closedin_on[OF top1_S2_is_hausdorff
        top1_S2_is_topology_on_strict hC2'_sub_S2])
      obtain h2 where hh2: "top1_homeomorphism_on I_set I_top C2'
          (subspace_topology top1_S2 top1_S2_topology C2') h2"
        using hC2'_arc unfolding top1_is_arc_on_def by (by100 blast)
      have "compact {0..1::real}" by (rule compact_Icc)
      moreover have "I_set = {0..1::real}" unfolding top1_unit_interval_def
        by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
      ultimately have "compact I_set" by simp
      hence hI_compact: "top1_compact_on I_set I_top"
        unfolding top1_unit_interval_topology_def
        using top1_compact_on_subspace_UNIV_iff_compact[of I_set] by simp
      have hcont: "top1_continuous_map_on I_set I_top C2'
          (subspace_topology top1_S2 top1_S2_topology C2') h2"
        using hh2 unfolding top1_homeomorphism_on_def by (by100 blast)
      have hTS2_C2: "is_topology_on C2' (subspace_topology top1_S2 top1_S2_topology C2')"
        using hh2 unfolding top1_homeomorphism_on_def by (by100 blast)
      have himg: "h2 ` I_set = C2'"
        using hh2 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have "top1_compact_on (h2 ` I_set) (subspace_topology C2'
          (subspace_topology top1_S2 top1_S2_topology C2') (h2 ` I_set))"
        by (rule top1_compact_on_continuous_image[OF hI_compact hTS2_C2 hcont])
      moreover have "h2 ` I_set = C2'" by (rule himg)
      moreover have "subspace_topology C2' (subspace_topology top1_S2 top1_S2_topology C2') C2'
          = subspace_topology top1_S2 top1_S2_topology C2'"
        using hC2'_arc unfolding top1_is_arc_on_def is_topology_on_strict_def
        by (intro subspace_topology_self) (by100 blast)
      ultimately show "top1_compact_on C2' (subspace_topology top1_S2 top1_S2_topology C2')"
        by simp
    qed
    have hC1'_conn: "top1_connected_on C1' (subspace_topology top1_S2 top1_S2_topology C1')"
    proof -
      obtain h1 where hh1: "top1_homeomorphism_on I_set I_top C1'
          (subspace_topology top1_S2 top1_S2_topology C1') h1"
        using hC1'_arc unfolding top1_is_arc_on_def by (by100 blast)
      have hcont: "top1_continuous_map_on I_set I_top C1'
          (subspace_topology top1_S2 top1_S2_topology C1') h1"
        using hh1 unfolding top1_homeomorphism_on_def by (by100 blast)
      have himg: "h1 ` I_set = C1'"
        using hh1 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have hTS2_C1: "is_topology_on C1' (subspace_topology top1_S2 top1_S2_topology C1')"
        using hh1 unfolding top1_homeomorphism_on_def by (by100 blast)
      have "top1_connected_on (h1 ` I_set) (subspace_topology C1'
          (subspace_topology top1_S2 top1_S2_topology C1') (h1 ` I_set))"
        by (rule Theorem_23_5[OF top1_unit_interval_topology_is_topology_on hTS2_C1
              top1_unit_interval_connected hcont])
      moreover have "subspace_topology C1' (subspace_topology top1_S2 top1_S2_topology C1') C1'
          = subspace_topology top1_S2 top1_S2_topology C1'"
        using hC1'_arc unfolding top1_is_arc_on_def is_topology_on_strict_def
        by (intro subspace_topology_self) (by100 blast)
      ultimately show ?thesis using himg by simp
    qed
    have hC2'_conn: "top1_connected_on C2' (subspace_topology top1_S2 top1_S2_topology C2')"
    proof -
      obtain h2 where hh2: "top1_homeomorphism_on I_set I_top C2'
          (subspace_topology top1_S2 top1_S2_topology C2') h2"
        using hC2'_arc unfolding top1_is_arc_on_def by (by100 blast)
      have hcont: "top1_continuous_map_on I_set I_top C2'
          (subspace_topology top1_S2 top1_S2_topology C2') h2"
        using hh2 unfolding top1_homeomorphism_on_def by (by100 blast)
      have himg: "h2 ` I_set = C2'"
        using hh2 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have hTS2_C2: "is_topology_on C2' (subspace_topology top1_S2 top1_S2_topology C2')"
        using hh2 unfolding top1_homeomorphism_on_def by (by100 blast)
      have "top1_connected_on (h2 ` I_set) (subspace_topology C2'
          (subspace_topology top1_S2 top1_S2_topology C2') (h2 ` I_set))"
        by (rule Theorem_23_5[OF top1_unit_interval_topology_is_topology_on hTS2_C2
              top1_unit_interval_connected hcont])
      moreover have "subspace_topology C2' (subspace_topology top1_S2 top1_S2_topology C2') C2'
          = subspace_topology top1_S2 top1_S2_topology C2'"
        using hC2'_arc unfolding top1_is_arc_on_def is_topology_on_strict_def
        by (intro subspace_topology_self) (by100 blast)
      ultimately show ?thesis using himg by simp
    qed
    have hC12'_card: "card (C1' \<inter> C2') = 2"
    proof -
      have h\<sigma>2inv_inj: "inj \<sigma>2inv"
        using h\<sigma>2inv_bij unfolding bij_betw_def by (by100 blast)
      have "C1' \<inter> C2' = \<sigma>2inv ` (C1_arc \<inter> C2_arc)"
        unfolding C1'_def C2'_def using image_Int[OF h\<sigma>2inv_inj, of C1_arc C2_arc]
        by simp
      also have "\<dots> = \<sigma>2inv ` {p_arc, q_arc}" using hC_inter by simp
      also have "card \<dots> = 2"
      proof -
        have "\<sigma>2inv p_arc \<noteq> \<sigma>2inv q_arc"
          using hpq_ne h\<sigma>2inv_inj unfolding inj_def by (by100 blast)
        thus ?thesis by simp
      qed
      finally show ?thesis .
    qed
    have hC1'_nonsep: "\<not> top1_separates_on top1_S2 top1_S2_topology C1'"
      by (rule Theorem_63_2_arc_no_separation[OF top1_S2_is_topology_on_strict hC1'_sub_S2 hC1'_arc])
    have hC2'_nonsep: "\<not> top1_separates_on top1_S2 top1_S2_topology C2'"
      by (rule Theorem_63_2_arc_no_separation[OF top1_S2_is_topology_on_strict hC2'_sub_S2 hC2'_arc])
    \<comment> \<open>Apply Theorem_63_5: S^2-(C1'\<union>C2') has exactly 2 components.\<close>
    obtain U_S2 V_S2 where
        hUS2_ne: "U_S2 \<noteq> {}" and hVS2_ne: "V_S2 \<noteq> {}"
        and hUVS2_disj: "U_S2 \<inter> V_S2 = {}"
        and hUVS2_cover: "U_S2 \<union> V_S2 = top1_S2 - (C1' \<union> C2')"
        and hUS2_conn: "top1_connected_on U_S2 (subspace_topology top1_S2 top1_S2_topology U_S2)"
        and hVS2_conn: "top1_connected_on V_S2 (subspace_topology top1_S2 top1_S2_topology V_S2)"
    proof -
      have "\<exists>U V. U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = top1_S2 - (C1' \<union> C2') \<and>
          top1_connected_on U (subspace_topology top1_S2 top1_S2_topology U) \<and>
          top1_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
        by (rule Theorem_63_5_two_closed_connected[OF top1_S2_is_topology_on_strict
              hC1'_closed hC2'_closed hC1'_conn hC2'_conn hC12'_card hC1'_nonsep hC2'_nonsep])
      then obtain U0 V0 where "U0 \<noteq> {}" "V0 \<noteq> {}" "U0 \<inter> V0 = {}"
          "U0 \<union> V0 = top1_S2 - (C1' \<union> C2')"
          "top1_connected_on U0 (subspace_topology top1_S2 top1_S2_topology U0)"
          "top1_connected_on V0 (subspace_topology top1_S2 top1_S2_topology V0)"
        by blast
      show ?thesis
        apply (intro that[of U0 V0])
        using \<open>U0 \<noteq> {}\<close> \<open>V0 \<noteq> {}\<close> \<open>U0 \<inter> V0 = {}\<close> \<open>U0 \<union> V0 = _\<close>
          \<open>top1_connected_on U0 _\<close> \<open>top1_connected_on V0 _\<close>
        by simp_all
    qed
    \<comment> \<open>N \<in> one of U_S2, V_S2. WLOG N \<in> V_S2 (swap if needed).\<close>
    have hN_in_comp: "north_pole \<in> U_S2 \<or> north_pole \<in> V_S2"
      using hUVS2_cover hN_not_C' north_pole_in_S2 hC'_decomp by (by100 blast)
    \<comment> \<open>Transfer to R^2: \<sigma>2 maps S^2\{N} homeomorphically to R^2.\<close>
    \<comment> \<open>Define R^2 components from S^2 components.\<close>
    \<comment> \<open>U = \<sigma>2(U_S2), or U = \<sigma>2(U_S2) and V = \<sigma>2(V_S2 - {N}).\<close>
    \<comment> \<open>The component containing N maps to the unbounded component in R^2.\<close>
    \<comment> \<open>WLOG: ensure N \<in> V_S2 (swap if needed).\<close>
    obtain W1_S2 W2_S2 where hW1_ne: "W1_S2 \<noteq> {}" and hW2_ne: "W2_S2 \<noteq> {}"
        and hW12_disj: "W1_S2 \<inter> W2_S2 = {}"
        and hW12_cover: "W1_S2 \<union> W2_S2 = top1_S2 - (C1' \<union> C2')"
        and hW1_conn: "top1_connected_on W1_S2 (subspace_topology top1_S2 top1_S2_topology W1_S2)"
        and hW2_conn: "top1_connected_on W2_S2 (subspace_topology top1_S2 top1_S2_topology W2_S2)"
        and hN_in_W2: "north_pole \<in> W2_S2"
    proof -
      show ?thesis using hN_in_comp hUS2_ne hVS2_ne hUVS2_disj hUVS2_cover hUS2_conn hVS2_conn
      proof (cases "north_pole \<in> V_S2")
        case True
        thus ?thesis by (intro that[of U_S2 V_S2])
           (use hUS2_ne hVS2_ne hUVS2_disj hUVS2_cover hUS2_conn hVS2_conn in simp)+
      next
        case False
        hence "north_pole \<in> U_S2" using hN_in_comp by simp
        thus ?thesis by (intro that[of V_S2 U_S2])
           (use hUS2_ne hVS2_ne hUVS2_disj hUVS2_cover hUS2_conn hVS2_conn in auto)+
      qed
    qed
    \<comment> \<open>N \<notin> W1_S2 (disjoint from W2_S2 which contains N).\<close>
    have hN_not_W1: "north_pole \<notin> W1_S2" using hW12_disj hN_in_W2 by (by100 blast)
    \<comment> \<open>W1_S2 \<subseteq> S^2\{N} (doesn't contain N).\<close>
    have hW1_sub_S2N: "W1_S2 \<subseteq> top1_S2 - {north_pole}"
      using hW12_cover hN_not_W1 by (by100 blast)
    \<comment> \<open>Define R^2 components.\<close>
    define U_R2 where "U_R2 = \<sigma>2 ` W1_S2"
    define V_R2 where "V_R2 = \<sigma>2 ` (W2_S2 - {north_pole})"
    \<comment> \<open>Show all 8 properties.\<close>
    have hUR2_ne: "U_R2 \<noteq> {}" using hW1_ne unfolding U_R2_def by (by100 blast)
    have hVR2_ne: "V_R2 \<noteq> {}"
    proof -
      \<comment> \<open>W2_S2 \<noteq> {N}: if W2_S2 = {N}, then {N} is open in S^2 (it's a component,
         hence open since S^2 is locally connected). But singletons aren't open in S^2.\<close>
      have "W2_S2 \<noteq> {north_pole}"
      proof
        assume heq: "W2_S2 = {north_pole}"
        \<comment> \<open>W2_S2 is open in S^2 (component of open set in locally connected S^2).\<close>
        have hTS2: "is_topology_on top1_S2 top1_S2_topology"
          using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
        have hC12'_closed: "closedin_on top1_S2 top1_S2_topology (C1' \<union> C2')"
        proof -
          have "top1_S2 - (C1' \<union> C2') = (top1_S2 - C1') \<inter> (top1_S2 - C2')" by (by100 blast)
          moreover have "(top1_S2 - C1') \<in> top1_S2_topology"
            using hC1'_closed unfolding closedin_on_def by (by100 blast)
          moreover have "(top1_S2 - C2') \<in> top1_S2_topology"
            using hC2'_closed unfolding closedin_on_def by (by100 blast)
          ultimately have "top1_S2 - (C1' \<union> C2') \<in> top1_S2_topology"
            using topology_inter_open[OF hTS2] by (by100 simp)
          thus ?thesis unfolding closedin_on_def
            using hC1'_sub_S2 hC2'_sub_S2 by (by100 blast)
        qed
        have hS2C12_open: "top1_S2 - (C1' \<union> C2') \<in> top1_S2_topology"
          using hC12'_closed unfolding closedin_on_def by (by100 blast)
        \<comment> \<open>W2_S2 \<subseteq> S^2-(C1'\<union>C2') and it's a component, hence open in S^2.\<close>
        have "W2_S2 \<in> top1_S2_topology"
        proof -
          \<comment> \<open>S^2-(C1'\<union>C2') is open and locally path-connected.\<close>
          define S2C where "S2C = top1_S2 - (C1' \<union> C2')"
          define TS2C where "TS2C = subspace_topology top1_S2 top1_S2_topology S2C"
          have "S2C \<subseteq> top1_S2" unfolding S2C_def by (by100 blast)
          have hTS2C: "is_topology_on S2C TS2C"
            unfolding TS2C_def by (rule subspace_topology_is_topology_on[OF hTS2 \<open>S2C \<subseteq> top1_S2\<close>])
          have hS2C_lpc: "top1_locally_path_connected_on S2C TS2C"
            unfolding TS2C_def S2C_def
            by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hS2C12_open]) simp
          \<comment> \<open>Path component of N in S^2-(C1'\<union>C2') is open.\<close>
          have hN_S2C: "north_pole \<in> S2C"
            unfolding S2C_def using hN_in_W2 hW12_cover hC'_decomp by (by100 blast)
          define PC_N where "PC_N = top1_path_component_of_on S2C TS2C north_pole"
          have hPC_N_open: "PC_N \<in> TS2C"
            unfolding PC_N_def
            by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTS2C hS2C_lpc hN_S2C])
          \<comment> \<open>PC_N = W2_S2 (both are the maximal connected set containing N in S2C).\<close>
          \<comment> \<open>PC_N = W2_S2: path component = connected component in lpc space.\<close>
          have hN_in_PC: "north_pole \<in> PC_N"
            unfolding PC_N_def top1_path_component_of_on_def
            top1_in_same_path_component_on_def
            using top1_constant_path_is_path[OF hTS2C hN_S2C] by (by100 blast)
          have hPC_sub: "PC_N \<subseteq> S2C"
          proof
            fix y assume "y \<in> PC_N"
            then obtain f where "top1_is_path_on S2C TS2C north_pole y f"
              unfolding PC_N_def top1_path_component_of_on_def
              top1_in_same_path_component_on_def by (by100 blast)
            hence "f 1 = y" and "\<forall>s\<in>I_set. f s \<in> S2C"
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)+
            moreover have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
            ultimately show "y \<in> S2C" by (by100 blast)
          qed
          have hW2_sub_S2C: "W2_S2 \<subseteq> S2C"
            using hW12_cover hC'_decomp unfolding S2C_def by (by100 blast)
          \<comment> \<open>Complement of PC_N is open (union of other path components).\<close>
          have hCompl_open: "S2C - PC_N \<in> TS2C"
            unfolding PC_N_def
            by (rule top1_path_component_of_on_complement_open_if_locally_path_connected[OF
                  hTS2C hS2C_lpc hN_S2C])
          have "PC_N = W2_S2"
          proof (intro set_eqI iffI)
            fix x assume hx: "x \<in> PC_N"
            \<comment> \<open>PC_N \<subseteq> W2_S2: if x \<in> PC_N but x \<notin> W2_S2, then x \<in> W1_S2.
               But PC_N is connected (path-connected) and meets both W1 and W2.
               W1 \<inter> W2 = {}, W1 \<union> W2 = S2C, so PC_N \<inter> W1 and PC_N \<inter> W2 separate PC_N.\<close>
            show "x \<in> W2_S2"
            proof (rule ccontr)
              assume "x \<notin> W2_S2"
              hence "x \<in> W1_S2" using hx hPC_sub hW12_cover hC'_decomp
                unfolding S2C_def by (by100 blast)
              \<comment> \<open>Both W1 \<inter> S2C and W2 \<inter> S2C are open in S2C (W1, W2 \<subseteq> S2C, so trivially open).\<close>
              \<comment> \<open>Actually W1 and W2 cover S2C and are disjoint. PC_N meets both. Contradiction.\<close>
              \<comment> \<open>W1_S2 \<subseteq> PC_N: W1 connected, PC_N and S2C-PC_N partition S2C openly.\<close>
              have hW1_sub_S2C: "W1_S2 \<subseteq> S2C"
                using hW12_cover hC'_decomp unfolding S2C_def by (by100 blast)
              have hW1_top_eq: "subspace_topology top1_S2 top1_S2_topology W1_S2
                  = subspace_topology S2C TS2C W1_S2"
              proof -
                have "subspace_topology S2C (subspace_topology top1_S2 top1_S2_topology S2C) W1_S2
                    = subspace_topology top1_S2 top1_S2_topology W1_S2"
                  by (rule subspace_topology_trans[OF hW1_sub_S2C])
                thus ?thesis unfolding TS2C_def by simp
              qed
              \<comment> \<open>W1 connected. PC_N, S2C-PC_N open in TS2C. Their restrictions separate W1.\<close>
              have "(S2C - PC_N) \<inter> W1_S2 = {}"
              proof (rule ccontr)
                assume hne: "(S2C - PC_N) \<inter> W1_S2 \<noteq> {}"
                have "PC_N \<inter> W1_S2 \<in> subspace_topology S2C TS2C W1_S2"
                  using hPC_N_open unfolding subspace_topology_def by (by100 blast)
                moreover have "(S2C - PC_N) \<inter> W1_S2 \<in> subspace_topology S2C TS2C W1_S2"
                  using hCompl_open unfolding subspace_topology_def by (by100 blast)
                moreover have "PC_N \<inter> W1_S2 \<noteq> {}" using \<open>x \<in> W1_S2\<close> hx by (by100 blast)
                moreover have "(PC_N \<inter> W1_S2) \<inter> ((S2C - PC_N) \<inter> W1_S2) = {}" by (by100 blast)
                moreover have "(PC_N \<inter> W1_S2) \<union> ((S2C - PC_N) \<inter> W1_S2) = W1_S2"
                  using hW1_sub_S2C by (by100 blast)
                ultimately show False
                  using hW1_conn[unfolded hW1_top_eq top1_connected_on_def] hne
                  by (by100 blast)
              qed
              hence hW1_sub_PC: "W1_S2 \<subseteq> PC_N" using hW1_sub_S2C by (by100 blast)
              \<comment> \<open>W1 \<subseteq> PC_N and W2 \<subseteq> PC_N \<Rightarrow> S2C = PC_N \<Rightarrow> S2C path-connected \<Rightarrow> connected.
                 But S2C = W1\<union>W2 separated (by Theorem_61_4). S2C not connected.
                 Contradiction: S2C both connected and not connected.\<close>
              \<comment> \<open>W1 \<subseteq> PC_N contradicts the assumption x \<in> W1 \<inter> PC_N: no, that's consistent.
                 The contradiction is: x \<in> W1 but we want x \<in> W2. Since W1 \<subseteq> PC_N doesn't help.
                 Actually the real issue: we assumed x \<notin> W2 and derived W1 \<subseteq> PC_N. This doesn't
                 contradict anything directly. We need: S2C = PC_N \<Rightarrow> connected \<Rightarrow> but S2C separated.
                 S2C separated means W1, W2 open. W1 open in TS2C \<Rightarrow> need W1 path-component (lpc).
                 For now, contradiction proof omitted.\<close>
              \<comment> \<open>S2C = PC_N (path-connected). But S2C is NOT connected (separated by C1'\<union>C2').\<close>
              \<comment> \<open>W2_S2 \<subseteq> PC_N (same separation argument as for W2\<subseteq>PC_N direction below).\<close>
              have hW2_sub_PC_local: "W2_S2 \<subseteq> PC_N"
              proof -
                have "\<And>y. y \<in> W2_S2 \<Longrightarrow> y \<in> PC_N"
                proof (rule ccontr)
                  fix y assume hyW2: "y \<in> W2_S2" and "y \<notin> PC_N"
                  have "y \<in> S2C" using hyW2 hW2_sub_S2C by (by100 blast)
                  have hW2_top_eq: "subspace_topology top1_S2 top1_S2_topology W2_S2
                      = subspace_topology S2C TS2C W2_S2"
                  proof -
                    have "subspace_topology S2C (subspace_topology top1_S2 top1_S2_topology S2C) W2_S2
                        = subspace_topology top1_S2 top1_S2_topology W2_S2"
                      by (rule subspace_topology_trans[OF hW2_sub_S2C])
                    thus ?thesis unfolding TS2C_def by simp
                  qed
                  have "PC_N \<inter> W2_S2 \<in> subspace_topology S2C TS2C W2_S2"
                    using hPC_N_open unfolding subspace_topology_def by (by100 blast)
                  moreover have "(S2C - PC_N) \<inter> W2_S2 \<in> subspace_topology S2C TS2C W2_S2"
                    using hCompl_open unfolding subspace_topology_def by (by100 blast)
                  moreover have "PC_N \<inter> W2_S2 \<noteq> {}" using hN_in_PC hN_in_W2 by (by100 blast)
                  moreover have "(S2C - PC_N) \<inter> W2_S2 \<noteq> {}" using \<open>y \<in> S2C\<close> \<open>y \<notin> PC_N\<close> hyW2 by (by100 blast)
                  moreover have "(PC_N \<inter> W2_S2) \<inter> ((S2C - PC_N) \<inter> W2_S2) = {}" by (by100 blast)
                  moreover have "(PC_N \<inter> W2_S2) \<union> ((S2C - PC_N) \<inter> W2_S2) = W2_S2"
                    using hW2_sub_S2C by (by100 blast)
                  ultimately show False
                    using hW2_conn[unfolded hW2_top_eq top1_connected_on_def] by (by100 blast)
                qed
                thus ?thesis by (by100 blast)
              qed
              have "S2C \<subseteq> PC_N" using hW1_sub_PC hW2_sub_PC_local hW12_cover hC'_decomp
                unfolding S2C_def by (by100 blast)
              hence "S2C = PC_N" using hPC_sub by (by100 blast)
              \<comment> \<open>S2C path-connected (= PC_N). PC_N path-connected by definition.\<close>
              have "top1_path_connected_on S2C TS2C"
              proof -
                have "top1_path_connected_on PC_N (subspace_topology S2C TS2C PC_N)"
                  unfolding PC_N_def
                  by (rule top1_path_component_of_on_path_connected[OF hTS2C hN_S2C])
                moreover have "subspace_topology S2C TS2C PC_N = TS2C"
                proof -
                  have "\<forall>U\<in>TS2C. U \<subseteq> S2C"
                    unfolding TS2C_def subspace_topology_def by (by100 blast)
                  hence "subspace_topology S2C TS2C S2C = TS2C" by (rule subspace_topology_self)
                  thus ?thesis using \<open>S2C = PC_N\<close> by simp
                qed
                ultimately have "top1_path_connected_on PC_N TS2C" by simp
                thus ?thesis using \<open>S2C = PC_N\<close> by simp
              qed
              hence hS2C_conn: "top1_connected_on S2C TS2C"
                by (rule top1_path_connected_imp_connected)
              \<comment> \<open>But S2C is NOT connected (C1'\<union>C2' separates S^2).\<close>
              have "\<not> top1_connected_on S2C TS2C"
                unfolding S2C_def TS2C_def
                using Theorem_61_4_general_separation[OF top1_S2_is_topology_on_strict
                      hC1'_sub_S2 hC2'_sub_S2 hC1'_closed hC2'_closed
                      hC1'_conn hC2'_conn hC12'_card]
                unfolding top1_separates_on_def by simp
              show False using hS2C_conn \<open>\<not> top1_connected_on S2C TS2C\<close> by simp
            qed
          next
            fix x assume hx: "x \<in> W2_S2"
            \<comment> \<open>W2_S2 \<subseteq> PC_N: if x \<in> W2_S2 but x \<notin> PC_N, then x \<in> S2C-PC_N which is open.
               W2_S2 meets PC_N (at N) and S2C-PC_N (at x). Both open in S2C.
               This separates W2_S2 (connected). Contradiction.\<close>
            show "x \<in> PC_N"
            proof (rule ccontr)
              assume "x \<notin> PC_N"
              have "x \<in> S2C" using hx hW2_sub_S2C by (by100 blast)
              hence "x \<in> S2C - PC_N" using \<open>x \<notin> PC_N\<close> by (by100 blast)
              \<comment> \<open>W2_S2 meets PC_N (at N) and S2C-PC_N (at x). Both open.\<close>
              have hW2_meet_PC: "W2_S2 \<inter> PC_N \<noteq> {}" using hN_in_PC hN_in_W2 by (by100 blast)
              have hW2_meet_compl: "W2_S2 \<inter> (S2C - PC_N) \<noteq> {}" using \<open>x \<in> S2C - PC_N\<close> hx by (by100 blast)
              have hW2_sub_union: "W2_S2 \<subseteq> PC_N \<union> (S2C - PC_N)" using hW2_sub_S2C by (by100 blast)
              have hPC_compl_disj: "PC_N \<inter> (S2C - PC_N) = {}" by (by100 blast)
              \<comment> \<open>PC_N and S2C-PC_N are both in TS2C: separation of W2_S2.\<close>
              \<comment> \<open>Convert to TS2C subspace: sub(S2, S2_top, W2) = sub(S2C, TS2C, W2).\<close>
              have hW2_top_eq: "subspace_topology top1_S2 top1_S2_topology W2_S2
                  = subspace_topology S2C TS2C W2_S2"
              proof -
                have "subspace_topology S2C (subspace_topology top1_S2 top1_S2_topology S2C) W2_S2
                    = subspace_topology top1_S2 top1_S2_topology W2_S2"
                  by (rule subspace_topology_trans[OF hW2_sub_S2C])
                thus ?thesis unfolding TS2C_def by simp
              qed
              \<comment> \<open>PC_N \<inter> W2_S2 and (S2C-PC_N) \<inter> W2_S2 open in sub(S2C, TS2C, W2).\<close>
              have hA_open: "PC_N \<inter> W2_S2 \<in> subspace_topology S2C TS2C W2_S2"
                using hPC_N_open unfolding subspace_topology_def by (by100 blast)
              have hB_open: "(S2C - PC_N) \<inter> W2_S2 \<in> subspace_topology S2C TS2C W2_S2"
                using hCompl_open unfolding subspace_topology_def by (by100 blast)
              \<comment> \<open>They cover W2_S2, are disjoint, and each nonempty.\<close>
              have hcover: "PC_N \<inter> W2_S2 \<union> ((S2C - PC_N) \<inter> W2_S2) = W2_S2"
                using hW2_sub_S2C by (by100 blast)
              have hdisj_AB: "(PC_N \<inter> W2_S2) \<inter> ((S2C - PC_N) \<inter> W2_S2) = {}" by (by100 blast)
              \<comment> \<open>This is a separation of W2_S2, contradicting connectedness.\<close>
              show False
                using hW2_conn[unfolded hW2_top_eq top1_connected_on_def]
                hA_open hB_open hW2_meet_PC hW2_meet_compl
                hcover hdisj_AB
                by (by100 blast)
            qed
          qed
          hence "W2_S2 \<in> TS2C" using hPC_N_open by simp
          \<comment> \<open>Open in S^2-(C1'\<union>C2') (which is open in S^2) \<Rightarrow> open in S^2.\<close>
          then obtain W where hW: "W \<in> top1_S2_topology" "W2_S2 = S2C \<inter> W"
            unfolding TS2C_def subspace_topology_def by (by100 blast)
          have "S2C \<inter> W \<in> top1_S2_topology"
            by (rule topology_inter_open[OF hTS2 hS2C12_open[folded S2C_def] hW(1)])
          thus ?thesis using hW(2) by simp
        qed
        hence "{north_pole} \<in> top1_S2_topology" using heq by simp
        thus False using singleton_not_open_in_S2[OF north_pole_in_S2] by simp
      qed
      hence "\<exists>x. x \<in> W2_S2 \<and> x \<noteq> north_pole" using hW2_ne hN_in_W2 by (by100 blast)
      then obtain x where "x \<in> W2_S2" "x \<noteq> north_pole" by (by100 blast)
      hence "x \<in> W2_S2 - {north_pole}" by (by100 blast)
      hence "\<sigma>2 x \<in> V_R2" unfolding V_R2_def by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    have h\<sigma>2_inj: "inj_on \<sigma>2 (top1_S2 - {north_pole})"
      using h\<sigma>2_bij unfolding bij_betw_def by (by100 blast)
    have hW2_sub: "W2_S2 - {north_pole} \<subseteq> top1_S2 - {north_pole}"
      using hW12_cover by (by100 blast)
    have hUR2VR2_disj: "U_R2 \<inter> V_R2 = {}"
    proof -
      have "W1_S2 \<inter> (W2_S2 - {north_pole}) = {}"
        using hW12_disj by (by100 blast)
      moreover have "W1_S2 \<union> (W2_S2 - {north_pole}) \<subseteq> top1_S2 - {north_pole}"
        using hW1_sub_S2N hW2_sub by (by100 blast)
      ultimately show ?thesis unfolding U_R2_def V_R2_def
      proof (intro set_eqI iffI)
        fix x assume hx: "x \<in> \<sigma>2 ` W1_S2 \<inter> \<sigma>2 ` (W2_S2 - {north_pole})"
        have "x \<in> \<sigma>2 ` W1_S2" using hx by (by100 blast)
        then obtain a where ha: "a \<in> W1_S2" "x = \<sigma>2 a" by (by100 blast)
        have "x \<in> \<sigma>2 ` (W2_S2 - {north_pole})" using hx by (by100 blast)
        then obtain b where hb: "b \<in> W2_S2 - {north_pole}" "\<sigma>2 b = x" by (by100 blast)
        have "a \<in> top1_S2 - {north_pole}" using ha(1) hW1_sub_S2N by (by100 blast)
        have "b \<in> top1_S2 - {north_pole}" using hb(1) hW2_sub by (by100 blast)
        have "a = b" using h\<sigma>2_inj \<open>a \<in> top1_S2 - _\<close> \<open>b \<in> top1_S2 - _\<close>
            ha(2) hb(2) unfolding inj_on_def by (by100 blast)
        hence "a \<in> W1_S2 \<inter> (W2_S2 - {north_pole})" using ha(1) hb(1) by simp
        thus "x \<in> {}" using \<open>W1_S2 \<inter> (W2_S2 - {north_pole}) = {}\<close> by (by100 blast)
      qed simp
    qed
    have hUR2VR2_cover: "U_R2 \<union> V_R2 = UNIV - C"
    proof -
      have hW12_minus_N: "W1_S2 \<union> (W2_S2 - {north_pole}) = (top1_S2 - {north_pole}) - C'"
        using hW12_cover hN_not_W1 hC'_decomp by (by100 blast)
      have "\<sigma>2 ` ((top1_S2 - {north_pole}) - C') = UNIV - C"
      proof -
        have "\<sigma>2 ` (top1_S2 - {north_pole}) = UNIV"
          using h\<sigma>2_bij unfolding bij_betw_def by (by100 blast)
        moreover have "\<sigma>2 ` C' = C"
        proof -
          have "C' = \<sigma>2inv ` C" unfolding C'_def by simp
          hence "\<sigma>2 ` C' = \<sigma>2 ` (\<sigma>2inv ` C)" by simp
          also have "\<dots> = C"
          proof (intro set_eqI iffI)
            fix x assume "x \<in> \<sigma>2 ` (\<sigma>2inv ` C)"
            then obtain y where "y \<in> C" "x = \<sigma>2 (\<sigma>2inv y)" by (by100 blast)
            have "\<sigma>2inv y \<in> top1_S2 - {north_pole}"
              using h\<sigma>2inv_bij \<open>y \<in> C\<close> unfolding bij_betw_def by (by100 blast)
            have "y \<in> \<sigma>2 ` (top1_S2 - {north_pole})"
              using h\<sigma>2_bij \<open>y \<in> C\<close> unfolding bij_betw_def by simp
            hence "\<sigma>2 (\<sigma>2inv y) = y"
              unfolding \<sigma>2inv_def by (rule f_inv_into_f)
            thus "x \<in> C" using \<open>x = _\<close> \<open>y \<in> C\<close> by simp
          next
            fix x assume "x \<in> C"
            have "x \<in> \<sigma>2 ` (top1_S2 - {north_pole})"
              using h\<sigma>2_bij \<open>x \<in> C\<close> unfolding bij_betw_def by simp
            hence "\<sigma>2inv x \<in> top1_S2 - {north_pole}"
              using h\<sigma>2inv_bij unfolding bij_betw_def by (by100 blast)
            have "\<sigma>2 (\<sigma>2inv x) = x"
              unfolding \<sigma>2inv_def using \<open>x \<in> \<sigma>2 ` _\<close> by (rule f_inv_into_f)
            have "\<sigma>2inv x \<in> \<sigma>2inv ` C" using \<open>x \<in> C\<close> by (by100 blast)
            thus "x \<in> \<sigma>2 ` (\<sigma>2inv ` C)" using \<open>\<sigma>2 (\<sigma>2inv x) = x\<close> by (by100 force)
          qed
          finally show ?thesis .
        qed
        moreover have "C' \<subseteq> top1_S2 - {north_pole}" using hC'_sub by simp
        have hAB_sub: "(top1_S2 - {north_pole}) - C' \<subseteq> top1_S2 - {north_pole}" by (by100 blast)
        have "\<sigma>2 ` ((top1_S2 - {north_pole}) - C') = \<sigma>2 ` (top1_S2 - {north_pole}) - \<sigma>2 ` C'"
          by (rule inj_on_image_set_diff[OF h\<sigma>2_inj hAB_sub hC'_sub])
        hence "\<sigma>2 ` ((top1_S2 - {north_pole}) - C') = UNIV - C"
          using \<open>\<sigma>2 ` (top1_S2 - {north_pole}) = UNIV\<close> \<open>\<sigma>2 ` C' = C\<close> by simp
        thus ?thesis .
      qed
      have "\<sigma>2 ` (W1_S2 \<union> (W2_S2 - {north_pole})) = UNIV - C"
        using \<open>\<sigma>2 ` ((top1_S2 - {north_pole}) - C') = UNIV - C\<close> hW12_minus_N by simp
      hence "\<sigma>2 ` W1_S2 \<union> \<sigma>2 ` (W2_S2 - {north_pole}) = UNIV - C"
        by (simp add: image_Un)
      thus ?thesis unfolding U_R2_def V_R2_def by simp
    qed
    have hUR2_conn: "top1_connected_on U_R2 (subspace_topology UNIV ?TR2 U_R2)"
    proof -
      \<comment> \<open>W1_S2 connected + \<sigma>2 continuous \<Rightarrow> \<sigma>2(W1_S2) connected.\<close>
      have hTS2N: "is_topology_on (top1_S2 - {north_pole})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))"
        by (rule subspace_topology_is_topology_on[OF
              is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict]]) (by100 blast)
      have h\<sigma>2_cont: "top1_continuous_map_on (top1_S2 - {north_pole})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) UNIV ?TR2 \<sigma>2"
        using h\<sigma>2 unfolding top1_homeomorphism_on_def by (by100 blast)
      have hTR2: "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
          top1_open_sets_is_topology_on_UNIV] by simp
      \<comment> \<open>W1_S2 connected in S^2\{N} subspace = S^2 subspace (by trans, since W1_S2 \<subseteq> S^2\{N}).\<close>
      have hW1_conn_S2N: "top1_connected_on W1_S2
          (subspace_topology (top1_S2 - {north_pole})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) W1_S2)"
        using hW1_conn subspace_topology_trans[OF hW1_sub_S2N, of top1_S2 top1_S2_topology]
        by simp
      have "\<sigma>2 ` W1_S2 = U_R2" unfolding U_R2_def by simp
      moreover have "top1_connected_on (\<sigma>2 ` W1_S2)
          (subspace_topology UNIV ?TR2 (\<sigma>2 ` W1_S2))"
      proof -
        have h\<sigma>2_rest: "top1_continuous_map_on W1_S2
            (subspace_topology (top1_S2 - {north_pole})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) W1_S2)
            UNIV ?TR2 \<sigma>2"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF h\<sigma>2_cont hW1_sub_S2N])
        show ?thesis by (rule Theorem_23_5[OF _ hTR2 hW1_conn_S2N h\<sigma>2_rest])
            (rule subspace_topology_is_topology_on[OF hTS2N hW1_sub_S2N])
      qed
      ultimately show ?thesis by simp
    qed
    \<comment> \<open>Bounded/unbounded: via Lemma_61_1_components_correspond.\<close>
    \<comment> \<open>Bounded/unbounded via Lemma_61_1. Need: C' compact, W1/W2 \<in> components.\<close>
    have hC'_compact: "top1_compact_on C' (subspace_topology top1_S2 top1_S2_topology C')"
    proof -
      \<comment> \<open>C' closed in S^2 (C1' \<union> C2' both closed, union of closed is closed).\<close>
      have hC'_closed: "closedin_on top1_S2 top1_S2_topology C'"
      proof -
        have "top1_S2 - C' = (top1_S2 - C1') \<inter> (top1_S2 - C2')" using hC'_decomp by (by100 blast)
        moreover have "(top1_S2 - C1') \<in> top1_S2_topology"
          using hC1'_closed unfolding closedin_on_def by (by100 blast)
        moreover have "(top1_S2 - C2') \<in> top1_S2_topology"
          using hC2'_closed unfolding closedin_on_def by (by100 blast)
        ultimately have "top1_S2 - C' \<in> top1_S2_topology"
          using topology_inter_open[OF
            is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict]] by (by100 simp)
        thus ?thesis unfolding closedin_on_def using hC'_sub_S2 by (by100 blast)
      qed
      \<comment> \<open>S^2 compact.\<close>
      have hS2_compact: "top1_compact_on top1_S2 top1_S2_topology"
      proof -
        have "top1_S2_topology = subspace_topology UNIV
            (top1_open_sets :: (real \<times> real \<times> real) set set) top1_S2"
          unfolding top1_S2_topology_def
          using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
        hence "top1_compact_on top1_S2 top1_S2_topology = compact top1_S2"
          using top1_compact_on_subspace_UNIV_iff_compact[of top1_S2] by simp
        thus ?thesis using S2_compact_standard by simp
      qed
      show ?thesis
        using conjunct1[OF Theorem_26_2_strict[OF hS2_compact
              top1_S2_is_topology_on_strict hC'_closed]] .
    qed
    \<comment> \<open>Boundary: closure(U) = U \<union> C and closure(V) = V \<union> C.
       Direction \<supseteq>: U \<subseteq> closure(U) trivially. C \<subseteq> closure(U) by textbook Step 2.
       Direction \<subseteq>: closure(U) \<inter> V = {} since V open and U \<inter> V = {}.
       Hence closure(U) \<subseteq> UNIV - V = U \<union> C.\<close>
    have hTR2: "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
      using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
          top1_open_sets_is_topology_on_UNIV] by simp
    \<comment> \<open>W1, W2 open in S^2 (path components of lpc S2C = S^2 - C').\<close>
    \<comment> \<open>W1, W2 open in S^2: path components of lpc S2C.\<close>
    have hTS2_here: "is_topology_on top1_S2 top1_S2_topology"
      using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
    have hS2C_open_here: "top1_S2 - (C1' \<union> C2') \<in> top1_S2_topology"
    proof -
      have "top1_S2 - (C1' \<union> C2') = (top1_S2 - C1') \<inter> (top1_S2 - C2')" by (by100 blast)
      moreover have "(top1_S2 - C1') \<in> top1_S2_topology"
        using hC1'_closed unfolding closedin_on_def by (by100 blast)
      moreover have "(top1_S2 - C2') \<in> top1_S2_topology"
        using hC2'_closed unfolding closedin_on_def by (by100 blast)
      ultimately show ?thesis using topology_inter_open[OF hTS2_here] by (by100 simp)
    qed
    define S2C_here where "S2C_here = top1_S2 - (C1' \<union> C2')"
    define TS2C_here where "TS2C_here = subspace_topology top1_S2 top1_S2_topology S2C_here"
    have "S2C_here \<subseteq> top1_S2" unfolding S2C_here_def by (by100 blast)
    have hTS2C_here: "is_topology_on S2C_here TS2C_here"
      unfolding TS2C_here_def
      by (rule subspace_topology_is_topology_on[OF hTS2_here \<open>S2C_here \<subseteq> top1_S2\<close>])
    have hS2C_lpc_here: "top1_locally_path_connected_on S2C_here TS2C_here"
      unfolding TS2C_here_def S2C_here_def
      by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hS2C_open_here]) simp
    have hW1_sub_S2C_here: "W1_S2 \<subseteq> S2C_here" and hW2_sub_S2C_here: "W2_S2 \<subseteq> S2C_here"
      using hW12_cover hC'_decomp unfolding S2C_here_def by (by100 blast)+
    \<comment> \<open>W1 is a path component of S2C_here.\<close>
    \<comment> \<open>W1 = path component of any w \<in> W1 (hence open).\<close>
    have hS2C_not_conn: "\<not> top1_connected_on S2C_here TS2C_here"
      unfolding S2C_here_def TS2C_here_def
      using Theorem_61_4_general_separation[OF top1_S2_is_topology_on_strict
            hC1'_sub_S2 hC2'_sub_S2 hC1'_closed hC2'_closed
            hC1'_conn hC2'_conn hC12'_card]
      unfolding top1_separates_on_def by simp
    have hW1_open_S2C: "W1_S2 \<in> TS2C_here"
    proof -
      obtain w where hw: "w \<in> W1_S2" using hW1_ne by (by100 blast)
      hence hw_S2C: "w \<in> S2C_here" using hW1_sub_S2C_here by (by100 blast)
      define PC_w where "PC_w = top1_path_component_of_on S2C_here TS2C_here w"
      have hPCw_open: "PC_w \<in> TS2C_here" unfolding PC_w_def
        by (rule top1_path_component_of_on_open_if_locally_path_connected[OF
              hTS2C_here hS2C_lpc_here hw_S2C])
      have hPCw_compl_open: "S2C_here - PC_w \<in> TS2C_here" unfolding PC_w_def
        by (rule top1_path_component_of_on_complement_open_if_locally_path_connected[OF
              hTS2C_here hS2C_lpc_here hw_S2C])
      have hw_PC: "w \<in> PC_w" unfolding PC_w_def top1_path_component_of_on_def
        top1_in_same_path_component_on_def
        using top1_constant_path_is_path[OF hTS2C_here hw_S2C] by (by100 blast)
      \<comment> \<open>W1 \<subseteq> PC_w: W1 connected, PC_w and S2C-PC_w open, W1 meets PC_w.\<close>
      have "W1_S2 \<subseteq> PC_w"
      proof -
        have hW1_top_eq: "subspace_topology top1_S2 top1_S2_topology W1_S2
            = subspace_topology S2C_here TS2C_here W1_S2"
        proof -
          have "subspace_topology S2C_here (subspace_topology top1_S2 top1_S2_topology S2C_here) W1_S2
              = subspace_topology top1_S2 top1_S2_topology W1_S2"
            by (rule subspace_topology_trans[OF hW1_sub_S2C_here])
          thus ?thesis unfolding TS2C_here_def by simp
        qed
        have "(S2C_here - PC_w) \<inter> W1_S2 = {}"
        proof (rule ccontr)
          assume hne: "(S2C_here - PC_w) \<inter> W1_S2 \<noteq> {}"
          have "PC_w \<inter> W1_S2 \<in> subspace_topology S2C_here TS2C_here W1_S2"
            using hPCw_open unfolding subspace_topology_def by (by100 blast)
          moreover have "(S2C_here - PC_w) \<inter> W1_S2 \<in> subspace_topology S2C_here TS2C_here W1_S2"
            using hPCw_compl_open unfolding subspace_topology_def by (by100 blast)
          moreover have "PC_w \<inter> W1_S2 \<noteq> {}" using hw hw_PC by (by100 blast)
          moreover have "(PC_w \<inter> W1_S2) \<inter> ((S2C_here - PC_w) \<inter> W1_S2) = {}" by (by100 blast)
          moreover have "(PC_w \<inter> W1_S2) \<union> ((S2C_here - PC_w) \<inter> W1_S2) = W1_S2"
            using hW1_sub_S2C_here by (by100 blast)
          ultimately show False
            using hW1_conn[unfolded hW1_top_eq top1_connected_on_def] hne by (by100 blast)
        qed
        thus ?thesis using hW1_sub_S2C_here by (by100 blast)
      qed
      \<comment> \<open>PC_w \<subseteq> W1: if PC_w meets W2, then S2C connected (contradiction).\<close>
      moreover have "PC_w \<subseteq> W1_S2"
      proof (rule ccontr)
        assume "\<not> PC_w \<subseteq> W1_S2"
        then obtain y where hy: "y \<in> PC_w" "y \<notin> W1_S2" by (by100 blast)
        have hPC_sub: "PC_w \<subseteq> S2C_here"
        proof
          fix z assume "z \<in> PC_w"
          then obtain f where "top1_is_path_on S2C_here TS2C_here w z f"
            unfolding PC_w_def top1_path_component_of_on_def
            top1_in_same_path_component_on_def by (by100 blast)
          hence "f 1 = z" and "\<forall>s\<in>I_set. f s \<in> S2C_here"
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)+
          moreover have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
          ultimately show "z \<in> S2C_here" by (by100 blast)
        qed
        hence "y \<in> W2_S2" using hy hW12_cover hC'_decomp hPC_sub
          unfolding S2C_here_def by (by100 blast)
        \<comment> \<open>PC_w path-connected (connected). W2 connected. They meet at y. Union connected.\<close>
        have hPCw_conn: "top1_connected_on PC_w (subspace_topology S2C_here TS2C_here PC_w)"
        proof -
          have "top1_path_connected_on PC_w (subspace_topology S2C_here TS2C_here PC_w)"
            unfolding PC_w_def
            using top1_path_component_of_on_path_connected[OF hTS2C_here hw_S2C]
            by simp
          thus ?thesis by (rule top1_path_connected_imp_connected)
        qed
        have hW2_top_eq: "subspace_topology top1_S2 top1_S2_topology W2_S2
            = subspace_topology S2C_here TS2C_here W2_S2"
        proof -
          have "subspace_topology S2C_here (subspace_topology top1_S2 top1_S2_topology S2C_here) W2_S2
              = subspace_topology top1_S2 top1_S2_topology W2_S2"
            by (rule subspace_topology_trans[OF hW2_sub_S2C_here])
          thus ?thesis unfolding TS2C_here_def by simp
        qed
        \<comment> \<open>PC_w \<union> W2 connected (Theorem_23_3 with common point y).\<close>
        \<comment> \<open>PC_w \<union> W2 connected (Theorem_23_3: two connected sets sharing point y).\<close>
        have hPCw_union_W2_conn: "top1_connected_on (PC_w \<union> W2_S2)
            (subspace_topology S2C_here TS2C_here (PC_w \<union> W2_S2))"
        proof -
          define I2 :: "nat set" where "I2 = {0, 1}"
          define A2 :: "nat \<Rightarrow> (real\<times>real\<times>real) set" where
            "A2 = (\<lambda>i. if i = 0 then PC_w else W2_S2)"
          have "I2 \<noteq> {}" unfolding I2_def by simp
          have "\<forall>i\<in>I2. A2 i \<subseteq> S2C_here"
            unfolding I2_def A2_def using hPC_sub hW2_sub_S2C_here by simp
          have "\<forall>i\<in>I2. top1_connected_on (A2 i) (subspace_topology S2C_here TS2C_here (A2 i))"
            unfolding I2_def A2_def
            using hPCw_conn hW2_conn[unfolded hW2_top_eq] by simp
          have "y \<in> \<Inter>(A2 ` I2)" unfolding I2_def A2_def using hy(1) \<open>y \<in> W2_S2\<close> by simp
          have "PC_w \<union> W2_S2 = (\<Union>i\<in>I2. A2 i)" unfolding I2_def A2_def by (by100 force)
          show ?thesis using Theorem_23_3[OF hTS2C_here \<open>I2 \<noteq> {}\<close> \<open>\<forall>i\<in>I2. A2 i \<subseteq> S2C_here\<close>
            \<open>\<forall>i\<in>I2. top1_connected_on _ _\<close> \<open>y \<in> \<Inter>(A2 ` I2)\<close>]
            unfolding \<open>PC_w \<union> W2_S2 = _\<close>[symmetric] by simp
        qed
        \<comment> \<open>PC_w \<union> W2 \<supseteq> W1 \<union> W2 = S2C (since PC_w \<supseteq> W1).\<close>
        have "S2C_here = PC_w \<union> W2_S2"
          using \<open>W1_S2 \<subseteq> PC_w\<close> hW12_cover hC'_decomp hPC_sub hW2_sub_S2C_here
          unfolding S2C_here_def by (by100 blast)
        hence "top1_connected_on S2C_here TS2C_here"
        proof -
          have "subspace_topology S2C_here TS2C_here (PC_w \<union> W2_S2) = TS2C_here"
          proof -
            have "\<forall>U\<in>TS2C_here. U \<subseteq> S2C_here"
              unfolding TS2C_here_def subspace_topology_def by (by100 blast)
            hence "subspace_topology S2C_here TS2C_here S2C_here = TS2C_here"
              by (rule subspace_topology_self)
            thus ?thesis using \<open>S2C_here = PC_w \<union> W2_S2\<close> by simp
          qed
          thus ?thesis using hPCw_union_W2_conn \<open>S2C_here = PC_w \<union> W2_S2\<close> by simp
        qed
        thus False using hS2C_not_conn by simp
      qed
      ultimately have "W1_S2 = PC_w" by (by100 blast)
      thus ?thesis using hPCw_open by simp
    qed
    have hW2_open_S2C: "W2_S2 \<in> TS2C_here"
    proof -
      \<comment> \<open>Same argument as W1: W2 is a path component of S2C, hence open.\<close>
      obtain w2 where hw2: "w2 \<in> W2_S2" using hW2_ne by (by100 blast)
      hence hw2_S2C: "w2 \<in> S2C_here" using hW2_sub_S2C_here by (by100 blast)
      define PC_w2 where "PC_w2 = top1_path_component_of_on S2C_here TS2C_here w2"
      have hPCw2_open: "PC_w2 \<in> TS2C_here" unfolding PC_w2_def
        by (rule top1_path_component_of_on_open_if_locally_path_connected[OF
              hTS2C_here hS2C_lpc_here hw2_S2C])
      \<comment> \<open>W2 = PC_w2 by same separation argument (skip details, same as W1).\<close>
      have hPCw2_compl_open: "S2C_here - PC_w2 \<in> TS2C_here" unfolding PC_w2_def
        by (rule top1_path_component_of_on_complement_open_if_locally_path_connected[OF
              hTS2C_here hS2C_lpc_here hw2_S2C])
      have hw2_PC: "w2 \<in> PC_w2" unfolding PC_w2_def top1_path_component_of_on_def
        top1_in_same_path_component_on_def
        using top1_constant_path_is_path[OF hTS2C_here hw2_S2C] by (by100 blast)
      \<comment> \<open>W2 \<subseteq> PC_w2: separation argument.\<close>
      have hW2_sub_PCw2: "W2_S2 \<subseteq> PC_w2"
      proof -
        have hW2_top_eq: "subspace_topology top1_S2 top1_S2_topology W2_S2
            = subspace_topology S2C_here TS2C_here W2_S2"
        proof -
          have "subspace_topology S2C_here (subspace_topology top1_S2 top1_S2_topology S2C_here) W2_S2
              = subspace_topology top1_S2 top1_S2_topology W2_S2"
            by (rule subspace_topology_trans[OF hW2_sub_S2C_here])
          thus ?thesis unfolding TS2C_here_def by simp
        qed
        have "(S2C_here - PC_w2) \<inter> W2_S2 = {}"
        proof (rule ccontr)
          assume hne: "(S2C_here - PC_w2) \<inter> W2_S2 \<noteq> {}"
          have "PC_w2 \<inter> W2_S2 \<in> subspace_topology S2C_here TS2C_here W2_S2"
            using hPCw2_open unfolding subspace_topology_def by (by100 blast)
          moreover have "(S2C_here - PC_w2) \<inter> W2_S2 \<in> subspace_topology S2C_here TS2C_here W2_S2"
            using hPCw2_compl_open unfolding subspace_topology_def by (by100 blast)
          moreover have "PC_w2 \<inter> W2_S2 \<noteq> {}" using hw2 hw2_PC by (by100 blast)
          moreover have "(PC_w2 \<inter> W2_S2) \<inter> ((S2C_here - PC_w2) \<inter> W2_S2) = {}" by (by100 blast)
          moreover have "(PC_w2 \<inter> W2_S2) \<union> ((S2C_here - PC_w2) \<inter> W2_S2) = W2_S2"
            using hW2_sub_S2C_here by (by100 blast)
          ultimately show False
            using hW2_conn[unfolded hW2_top_eq top1_connected_on_def] hne by (by100 blast)
        qed
        thus ?thesis using hW2_sub_S2C_here by (by100 blast)
      qed
      \<comment> \<open>PC_w2 \<subseteq> W2: if PC_w2 meets W1, S2C connected contradiction.\<close>
      have hPCw2_sub_W2: "PC_w2 \<subseteq> W2_S2"
      proof (rule ccontr)
        assume "\<not> PC_w2 \<subseteq> W2_S2"
        then obtain y where hy: "y \<in> PC_w2" "y \<notin> W2_S2" by (by100 blast)
        have hPC2_sub: "PC_w2 \<subseteq> S2C_here"
        proof
          fix z assume "z \<in> PC_w2"
          then obtain f where "top1_is_path_on S2C_here TS2C_here w2 z f"
            unfolding PC_w2_def top1_path_component_of_on_def
            top1_in_same_path_component_on_def by (by100 blast)
          hence "f 1 = z" and "\<forall>s\<in>I_set. f s \<in> S2C_here"
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)+
          moreover have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
          ultimately show "z \<in> S2C_here" by (by100 blast)
        qed
        hence "y \<in> W1_S2" using hy hW12_cover hC'_decomp hPC2_sub
          unfolding S2C_here_def by (by100 blast)
        have hPCw2_conn: "top1_connected_on PC_w2 (subspace_topology S2C_here TS2C_here PC_w2)"
        proof -
          have "top1_path_connected_on PC_w2 (subspace_topology S2C_here TS2C_here PC_w2)"
            unfolding PC_w2_def
            using top1_path_component_of_on_path_connected[OF hTS2C_here hw2_S2C] by simp
          thus ?thesis by (rule top1_path_connected_imp_connected)
        qed
        have hW1_top_eq2: "subspace_topology top1_S2 top1_S2_topology W1_S2
            = subspace_topology S2C_here TS2C_here W1_S2"
        proof -
          have "subspace_topology S2C_here (subspace_topology top1_S2 top1_S2_topology S2C_here) W1_S2
              = subspace_topology top1_S2 top1_S2_topology W1_S2"
            by (rule subspace_topology_trans[OF hW1_sub_S2C_here])
          thus ?thesis unfolding TS2C_here_def by simp
        qed
        \<comment> \<open>PC_w2 \<union> W1 connected, covers S2C, S2C not connected. Contradiction.\<close>
        define I2 :: "nat set" where "I2 = {0, 1}"
        define A2 :: "nat \<Rightarrow> (real\<times>real\<times>real) set" where
          "A2 = (\<lambda>i. if i = 0 then PC_w2 else W1_S2)"
        have "I2 \<noteq> {}" unfolding I2_def by simp
        have "\<forall>i\<in>I2. A2 i \<subseteq> S2C_here"
          unfolding I2_def A2_def using hPC2_sub hW1_sub_S2C_here by simp
        have "\<forall>i\<in>I2. top1_connected_on (A2 i) (subspace_topology S2C_here TS2C_here (A2 i))"
          unfolding I2_def A2_def using hPCw2_conn hW1_conn[unfolded hW1_top_eq2] by simp
        have "y \<in> \<Inter>(A2 ` I2)" unfolding I2_def A2_def using hy(1) \<open>y \<in> W1_S2\<close> by simp
        have "PC_w2 \<union> W1_S2 = (\<Union>i\<in>I2. A2 i)" unfolding I2_def A2_def by (by100 force)
        have "top1_connected_on (PC_w2 \<union> W1_S2)
            (subspace_topology S2C_here TS2C_here (PC_w2 \<union> W1_S2))"
          using Theorem_23_3[OF hTS2C_here \<open>I2 \<noteq> {}\<close> \<open>\<forall>i\<in>I2. A2 i \<subseteq> S2C_here\<close>
            \<open>\<forall>i\<in>I2. top1_connected_on _ _\<close> \<open>y \<in> \<Inter>(A2 ` I2)\<close>]
          unfolding \<open>PC_w2 \<union> W1_S2 = _\<close>[symmetric] by simp
        have "S2C_here = PC_w2 \<union> W1_S2"
          using hW2_sub_PCw2 hW12_cover hC'_decomp hPC2_sub hW1_sub_S2C_here
          unfolding S2C_here_def by (by100 blast)
        have "\<forall>U\<in>TS2C_here. U \<subseteq> S2C_here"
          unfolding TS2C_here_def subspace_topology_def by (by100 blast)
        hence "subspace_topology S2C_here TS2C_here S2C_here = TS2C_here"
          by (rule subspace_topology_self)
        hence "top1_connected_on S2C_here TS2C_here"
          using \<open>top1_connected_on (PC_w2 \<union> W1_S2) _\<close> \<open>S2C_here = PC_w2 \<union> W1_S2\<close> by simp
        thus False using hS2C_not_conn by simp
      qed
      have "W2_S2 = PC_w2" using hW2_sub_PCw2 hPCw2_sub_W2 by (by100 blast)
      thus ?thesis using hPCw2_open by simp
    qed
    \<comment> \<open>Open in S2C (which is open in S^2) = open in S^2.\<close>
    have hW1_open_S2: "W1_S2 \<in> top1_S2_topology"
    proof -
      obtain U1 where hU1: "U1 \<in> top1_S2_topology" "W1_S2 = S2C_here \<inter> U1"
        using hW1_open_S2C unfolding TS2C_here_def subspace_topology_def by (by100 blast)
      have "S2C_here \<inter> U1 \<in> top1_S2_topology"
        by (rule topology_inter_open[OF hTS2_here hS2C_open_here[folded S2C_here_def] hU1(1)])
      thus ?thesis using hU1(2) by simp
    qed
    have hW2_open_S2: "W2_S2 \<in> top1_S2_topology"
    proof -
      obtain U2 where hU2: "U2 \<in> top1_S2_topology" "W2_S2 = S2C_here \<inter> U2"
        using hW2_open_S2C unfolding TS2C_here_def subspace_topology_def by (by100 blast)
      have "S2C_here \<inter> U2 \<in> top1_S2_topology"
        by (rule topology_inter_open[OF hTS2_here hS2C_open_here[folded S2C_here_def] hU2(1)])
      thus ?thesis using hU2(2) by simp
    qed
    \<comment> \<open>V_R2 connected: W2_S2 - {N} connected (connected_open_delete_S2), transfer via \<sigma>2.\<close>
    have hVR2_conn: "top1_connected_on V_R2 (subspace_topology UNIV ?TR2 V_R2)"
    proof -
      have hW2_sub_S2: "W2_S2 \<subseteq> top1_S2"
        using hW2_sub_S2C_here unfolding S2C_here_def by (by100 blast)
      \<comment> \<open>Step 1: W2_S2 - {N} connected via connected_open_delete_S2.\<close>
      have hW2N_conn_hol: "connected (W2_S2 - {north_pole})"
      proof (rule connected_open_delete_S2[OF hW2_open_S2 hW2_conn hN_in_W2])
        obtain c where hc: "c \<in> W1_S2" using hW1_ne by (by100 blast)
        have "c \<in> top1_S2 - (C1' \<union> C2')" using hc hW12_cover by (by100 blast)
        hence hc_S2: "c \<in> top1_S2" by (by100 blast)
        have hc_not: "c \<notin> W2_S2" using hc hW12_disj by (by100 blast)
        thus "\<exists>c. c \<in> top1_S2 \<and> c \<notin> W2_S2" using hc_S2 by (by100 blast)
      qed
      \<comment> \<open>Step 2: \<sigma>2 continuous_on S^2\{N} in HOL sense.\<close>
      have h\<sigma>2_cont_on_S2N: "continuous_on (top1_S2 - {north_pole}) \<sigma>2"
      proof -
        have h\<sigma>2_cont_cust: "top1_continuous_map_on (top1_S2 - {north_pole})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) UNIV ?TR2 \<sigma>2"
          using h\<sigma>2 unfolding top1_homeomorphism_on_def by (by100 blast)
        show ?thesis unfolding continuous_on_open_invariant
        proof (intro allI impI)
          fix V :: "(real \<times> real) set" assume "open V"
          have "V \<in> (top1_open_sets :: (real \<times> real) set set)"
            using \<open>open V\<close> unfolding top1_open_sets_def by simp
          hence hV_TR2: "V \<in> ?TR2"
            using product_topology_on_open_sets_real2 by (by100 metis)
          have hpre: "{x \<in> top1_S2 - {north_pole}. \<sigma>2 x \<in> V}
              \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
            using h\<sigma>2_cont_cust hV_TR2 unfolding top1_continuous_map_on_def by (by100 blast)
          then obtain W where hW: "W \<in> top1_S2_topology"
              "{x \<in> top1_S2 - {north_pole}. \<sigma>2 x \<in> V} = (top1_S2 - {north_pole}) \<inter> W"
            unfolding subspace_topology_def by (by100 blast)
          have hTS2eq: "top1_S2_topology = subspace_topology UNIV
              (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
            unfolding top1_S2_topology_def
            using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                  product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
          then obtain W' where hW': "W' \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)"
              "W = top1_S2 \<inter> W'"
            using hW(1) unfolding subspace_topology_def by (by100 blast)
          have "open W'" using hW'(1) unfolding top1_open_sets_def by simp
          have "W' \<inter> (top1_S2 - {north_pole}) = \<sigma>2 -` V \<inter> (top1_S2 - {north_pole})"
          proof (intro set_eqI iffI)
            fix x assume "x \<in> W' \<inter> (top1_S2 - {north_pole})"
            hence hx1: "x \<in> top1_S2 - {north_pole}" and hx2: "x \<in> W'" by auto
            hence "x \<in> top1_S2 \<inter> W'" by (by100 blast)
            hence "x \<in> W" using hW'(2) by simp
            hence "x \<in> {x \<in> top1_S2 - {north_pole}. \<sigma>2 x \<in> V}"
              using hx1 hW(2) by (by100 blast)
            thus "x \<in> \<sigma>2 -` V \<inter> (top1_S2 - {north_pole})" by (by100 blast)
          next
            fix x assume "x \<in> \<sigma>2 -` V \<inter> (top1_S2 - {north_pole})"
            hence hx1: "x \<in> top1_S2 - {north_pole}" and hx2: "\<sigma>2 x \<in> V" by auto
            hence "x \<in> (top1_S2 - {north_pole}) \<inter> W" using hW(2) by (by100 blast)
            thus "x \<in> W' \<inter> (top1_S2 - {north_pole})" using hW'(2) hx1 by (by100 blast)
          qed
          thus "\<exists>A. open A \<and> A \<inter> (top1_S2 - {north_pole}) = \<sigma>2 -` V \<inter> (top1_S2 - {north_pole})"
            using \<open>open W'\<close> by (by100 blast)
        qed
      qed
      have h\<sigma>2_cont_on_W2N: "continuous_on (W2_S2 - {north_pole}) \<sigma>2"
        by (rule continuous_on_subset[OF h\<sigma>2_cont_on_S2N]) (use hW2_sub_S2 in blast)
      \<comment> \<open>Step 3: V_R2 connected in HOL sense.\<close>
      have "connected V_R2"
      proof -
        have "connected (\<sigma>2 ` (W2_S2 - {north_pole}))"
          by (rule connected_continuous_image[OF h\<sigma>2_cont_on_W2N hW2N_conn_hol])
        thus ?thesis unfolding V_R2_def by simp
      qed
      \<comment> \<open>Step 4: Bridge to top1_connected_on.\<close>
      thus ?thesis
        using top1_connected_on_subspace_open_iff_connected[of V_R2]
              product_topology_on_open_sets_real2
        by (by100 simp)
    qed
    \<comment> \<open>\<sigma>2 homeomorphism maps open subsets of S^2\{N} to open subsets of R^2.\<close>
    have h\<sigma>2_open_map: "\<And>V. V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})
        \<Longrightarrow> \<sigma>2 ` V \<in> ?TR2"
    proof -
      fix V assume hV: "V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
      \<comment> \<open>\<sigma>2\<inverse> continuous: preimage of V under \<sigma>2\<inverse> = \<sigma>2(V).\<close>
      have hinv_cont: "top1_continuous_map_on UNIV ?TR2 (top1_S2 - {north_pole})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
          (inv_into (top1_S2 - {north_pole}) \<sigma>2)"
        using h\<sigma>2 unfolding top1_homeomorphism_on_def by (by100 blast)
      hence "{x \<in> UNIV. inv_into (top1_S2 - {north_pole}) \<sigma>2 x \<in> V} \<in> ?TR2"
        using hV unfolding top1_continuous_map_on_def by (by100 blast)
      moreover have "{x \<in> UNIV. inv_into (top1_S2 - {north_pole}) \<sigma>2 x \<in> V} = \<sigma>2 ` V"
      proof (intro set_eqI iffI)
        fix x assume "x \<in> {x \<in> UNIV. inv_into (top1_S2 - {north_pole}) \<sigma>2 x \<in> V}"
        hence hinv_in: "inv_into (top1_S2 - {north_pole}) \<sigma>2 x \<in> V" by simp
        have hV_sub: "V \<subseteq> top1_S2 - {north_pole}"
          using hV unfolding subspace_topology_def by (by100 blast)
        hence "inv_into (top1_S2 - {north_pole}) \<sigma>2 x \<in> top1_S2 - {north_pole}"
          using hinv_in by (by100 blast)
        have "x \<in> \<sigma>2 ` (top1_S2 - {north_pole})"
          using h\<sigma>2_bij unfolding bij_betw_def by simp
        hence "\<sigma>2 (inv_into (top1_S2 - {north_pole}) \<sigma>2 x) = x"
          by (rule f_inv_into_f)
        thus "x \<in> \<sigma>2 ` V" using hinv_in by (by100 force)
      next
        fix x assume "x \<in> \<sigma>2 ` V"
        then obtain y where hy: "y \<in> V" "x = \<sigma>2 y" by (by100 blast)
        have hV_sub: "V \<subseteq> top1_S2 - {north_pole}"
          using hV unfolding subspace_topology_def by (by100 blast)
        hence "y \<in> top1_S2 - {north_pole}" using hy(1) by (by100 blast)
        hence "inv_into (top1_S2 - {north_pole}) \<sigma>2 x = y"
          using hy(2) inv_into_f_f[OF bij_betw_imp_inj_on[OF h\<sigma>2_bij]] by simp
        thus "x \<in> {x \<in> UNIV. inv_into (top1_S2 - {north_pole}) \<sigma>2 x \<in> V}"
          using hy(1) by simp
      qed
      ultimately show "\<sigma>2 ` V \<in> ?TR2" by simp
    qed
    have hUR2_in_TR2: "U_R2 \<in> ?TR2"
    proof -
      have "W1_S2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
        using hW1_open_S2 hW1_sub_S2N unfolding subspace_topology_def by (by100 blast)
      thus ?thesis unfolding U_R2_def using h\<sigma>2_open_map by simp
    qed
    have hVR2_in_TR2: "V_R2 \<in> ?TR2"
    proof -
      \<comment> \<open>W2 - {N} open in S^2: W2 open, {N} closed (Hausdorff), intersection of opens.\<close>
      have "W2_S2 - {north_pole} \<in> top1_S2_topology"
      proof -
        have "{north_pole} \<in> top1_S2_topology \<longrightarrow> False"
          using singleton_not_open_in_S2[OF north_pole_in_S2] by simp
        have "top1_S2 - {north_pole} \<in> top1_S2_topology"
          using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff north_pole_in_S2]
            hTS2_here unfolding closedin_on_def is_topology_on_def by (by100 blast)
        hence "W2_S2 \<inter> (top1_S2 - {north_pole}) \<in> top1_S2_topology"
          by (rule topology_inter_open[OF hTS2_here hW2_open_S2])
        moreover have "W2_S2 \<inter> (top1_S2 - {north_pole}) = W2_S2 - {north_pole}"
          using hW2_sub_S2C_here unfolding S2C_here_def by (by100 blast)
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>W2 - {N} \<subseteq> S^2 \{N}, so it's in the subspace topology.\<close>
      hence "W2_S2 - {north_pole} \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
      proof -
        have "W2_S2 \<subseteq> top1_S2" using hW2_sub_S2C_here unfolding S2C_here_def by (by100 blast)
        have "W2_S2 - {north_pole} \<subseteq> top1_S2 - {north_pole}" using \<open>W2_S2 \<subseteq> top1_S2\<close> by (by100 blast)
        hence "W2_S2 - {north_pole} = (top1_S2 - {north_pole}) \<inter> (W2_S2 - {north_pole})"
          by (by100 blast)
        thus ?thesis using \<open>W2_S2 - {north_pole} \<in> top1_S2_topology\<close>
          unfolding subspace_topology_def by (by100 blast)
      qed
      thus ?thesis unfolding V_R2_def using h\<sigma>2_open_map by simp
    qed
    have hUR2_sub: "U_R2 \<subseteq> UNIV" by simp
    have hVR2_sub: "V_R2 \<subseteq> UNIV" by simp
    have hW1_sub_C': "W1_S2 \<subseteq> top1_S2 - C'" using hW12_cover hC'_decomp by (by100 blast)
    have hW2_sub_C': "W2_S2 \<subseteq> top1_S2 - C'" using hW12_cover hC'_decomp by (by100 blast)
    have hW1_comp: "W1_S2 \<in> top1_components_on (top1_S2 - C')
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C'))"
    proof -
      obtain w where hw: "w \<in> W1_S2" using hW1_ne by (by100 blast)
      have "W1_S2 = top1_component_of_on (top1_S2 - C')
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')) w"
      proof (intro set_eqI iffI)
        \<comment> \<open>\<supseteq>: W1 connected, w \<in> W1, \<subseteq> S^2-C'.\<close>
        fix z assume "z \<in> W1_S2"
        show "z \<in> top1_component_of_on (top1_S2 - C')
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')) w"
          unfolding top1_component_of_on_mem_iff
          using hw \<open>z \<in> W1_S2\<close> hW1_sub_C' hW1_conn
            subspace_topology_trans[OF hW1_sub_C']
          by (intro exI[of _ W1_S2]) simp
      next
        \<comment> \<open>\<subseteq>: any connected C \<ni> w in S^2-C' must be \<subseteq> W1 (else C meets W2, separation).\<close>
        fix z assume "z \<in> top1_component_of_on (top1_S2 - C')
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')) w"
        then obtain Ca where hCa: "Ca \<subseteq> top1_S2 - C'" "w \<in> Ca" "z \<in> Ca"
            "top1_connected_on Ca (subspace_topology (top1_S2 - C')
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')) Ca)"
          unfolding top1_component_of_on_mem_iff by (by100 blast)
        \<comment> \<open>Ca \<subseteq> W1: if Ca meets W2, separation via W1/W2 both open.\<close>
        have "Ca \<subseteq> W1_S2"
        proof (rule ccontr)
          assume "\<not> Ca \<subseteq> W1_S2"
          then obtain y where "y \<in> Ca" "y \<notin> W1_S2" by (by100 blast)
          hence "y \<in> W2_S2" using hCa(1) hW12_cover hC'_decomp by (by100 blast)
          \<comment> \<open>W1\<inter>Ca and W2\<inter>Ca separate Ca. W1, W2 open in S^2 hence in subspace.\<close>
          have "W1_S2 \<inter> Ca \<in> subspace_topology (top1_S2 - C')
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')) Ca"
          proof -
            have "W1_S2 \<inter> (top1_S2 - C') \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')"
              using hW1_open_S2 unfolding subspace_topology_def by (by100 blast)
            moreover have "W1_S2 \<inter> (top1_S2 - C') = W1_S2" using hW1_sub_C' by (by100 blast)
            ultimately have "W1_S2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')"
              by simp
            thus ?thesis unfolding subspace_topology_def by (by100 blast)
          qed
          moreover have "W2_S2 \<inter> Ca \<in> subspace_topology (top1_S2 - C')
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')) Ca"
          proof -
            have "W2_S2 \<inter> (top1_S2 - C') \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')"
              using hW2_open_S2 unfolding subspace_topology_def by (by100 blast)
            moreover have "W2_S2 \<inter> (top1_S2 - C') = W2_S2" using hW2_sub_C' by (by100 blast)
            ultimately have "W2_S2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')"
              by simp
            thus ?thesis unfolding subspace_topology_def by (by100 blast)
          qed
          moreover have "W1_S2 \<inter> Ca \<noteq> {}" using hw hCa(2) by (by100 blast)
          moreover have "W2_S2 \<inter> Ca \<noteq> {}" using \<open>y \<in> W2_S2\<close> \<open>y \<in> Ca\<close> by (by100 blast)
          moreover have "(W1_S2 \<inter> Ca) \<inter> (W2_S2 \<inter> Ca) = {}" using hW12_disj by (by100 blast)
          moreover have "(W1_S2 \<inter> Ca) \<union> (W2_S2 \<inter> Ca) = Ca"
            using hCa(1) hW12_cover hC'_decomp by (by100 blast)
          ultimately show False
            using hCa(4)[unfolded top1_connected_on_def] by (by100 blast)
        qed
        thus "z \<in> W1_S2" using hCa(3) by (by100 blast)
      qed
      thus ?thesis unfolding top1_components_on_def
        using hw hW1_sub_C' by (by100 blast)
    qed
    have hN_S2C': "north_pole \<in> top1_S2 - C'"
      using north_pole_in_S2 hN_not_C' by (by100 blast)
    have hW1_sub_C': "W1_S2 \<subseteq> top1_S2 - C'"
      using hW12_cover hC'_decomp by (by100 blast)
    have h61_1_W1: "(north_pole \<notin> W1_S2 \<longrightarrow>
        (\<exists>M. \<forall>x\<in>W1_S2. fst (\<sigma>2 x) ^ 2 + snd (\<sigma>2 x) ^ 2 \<le> M))
      \<and> (north_pole \<in> W1_S2 \<longrightarrow>
        (\<forall>M. \<exists>x\<in>W1_S2 - {north_pole}. fst (\<sigma>2 x) ^ 2 + snd (\<sigma>2 x) ^ 2 > M))"
      by (rule Lemma_61_1_components_correspond[OF top1_S2_is_topology_on_strict
            hC'_sub_S2 hC'_compact hN_S2C' h\<sigma>2 hW1_conn hW1_sub_C' hW1_comp])
    have hUR2_bdd: "\<exists>M. \<forall>p\<in>U_R2. fst p ^ 2 + snd p ^ 2 \<le> M"
    proof -
      have "north_pole \<notin> W1_S2" using hW12_disj hN_in_W2 by (by100 blast)
      hence "\<exists>M. \<forall>x\<in>W1_S2. fst (\<sigma>2 x) ^ 2 + snd (\<sigma>2 x) ^ 2 \<le> M"
        using h61_1_W1 by simp
      thus ?thesis unfolding U_R2_def by (by100 blast)
    qed
    have hW2_comp: "W2_S2 \<in> top1_components_on (top1_S2 - C')
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C'))"
    proof -
      obtain w2 where hw2: "w2 \<in> W2_S2" using hW2_ne by (by100 blast)
      have "W2_S2 = top1_component_of_on (top1_S2 - C')
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')) w2"
      proof (intro set_eqI iffI)
        fix z assume "z \<in> W2_S2"
        show "z \<in> top1_component_of_on (top1_S2 - C')
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')) w2"
          unfolding top1_component_of_on_mem_iff
          using hw2 \<open>z \<in> W2_S2\<close> hW2_sub_C' hW2_conn
            subspace_topology_trans[OF hW2_sub_C']
          by (intro exI[of _ W2_S2]) simp
      next
        fix z assume "z \<in> top1_component_of_on (top1_S2 - C')
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')) w2"
        then obtain Ca where hCa: "Ca \<subseteq> top1_S2 - C'" "w2 \<in> Ca" "z \<in> Ca"
            "top1_connected_on Ca (subspace_topology (top1_S2 - C')
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')) Ca)"
          unfolding top1_component_of_on_mem_iff by (by100 blast)
        have "Ca \<subseteq> W2_S2"
        proof (rule ccontr)
          assume "\<not> Ca \<subseteq> W2_S2"
          then obtain y where "y \<in> Ca" "y \<notin> W2_S2" by (by100 blast)
          hence "y \<in> W1_S2" using hCa(1) hW12_cover hC'_decomp by (by100 blast)
          have "W1_S2 \<inter> Ca \<in> subspace_topology (top1_S2 - C')
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')) Ca"
          proof -
            have "W1_S2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')"
              using hW1_open_S2 hW1_sub_C' unfolding subspace_topology_def by (by100 blast)
            thus ?thesis unfolding subspace_topology_def by (by100 blast)
          qed
          moreover have "W2_S2 \<inter> Ca \<in> subspace_topology (top1_S2 - C')
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')) Ca"
          proof -
            have "W2_S2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - C')"
              using hW2_open_S2 hW2_sub_C' unfolding subspace_topology_def by (by100 blast)
            thus ?thesis unfolding subspace_topology_def by (by100 blast)
          qed
          moreover have "W1_S2 \<inter> Ca \<noteq> {}" using \<open>y \<in> W1_S2\<close> \<open>y \<in> Ca\<close> by (by100 blast)
          moreover have "W2_S2 \<inter> Ca \<noteq> {}" using hw2 hCa(2) by (by100 blast)
          moreover have "(W1_S2 \<inter> Ca) \<inter> (W2_S2 \<inter> Ca) = {}" using hW12_disj by (by100 blast)
          moreover have "(W1_S2 \<inter> Ca) \<union> (W2_S2 \<inter> Ca) = Ca"
            using hCa(1) hW12_cover hC'_decomp by (by100 blast)
          ultimately show False
            using hCa(4)[unfolded top1_connected_on_def] by (by100 blast)
        qed
        thus "z \<in> W2_S2" using hCa(3) by (by100 blast)
      qed
      thus ?thesis unfolding top1_components_on_def
        using hw2 hW2_sub_C' by (by100 blast)
    qed
    have hW2_sub_C': "W2_S2 \<subseteq> top1_S2 - C'"
      using hW12_cover hC'_decomp by (by100 blast)
    have h61_1_W2: "(north_pole \<notin> W2_S2 \<longrightarrow>
        (\<exists>M. \<forall>x\<in>W2_S2. fst (\<sigma>2 x) ^ 2 + snd (\<sigma>2 x) ^ 2 \<le> M))
      \<and> (north_pole \<in> W2_S2 \<longrightarrow>
        (\<forall>M. \<exists>x\<in>W2_S2 - {north_pole}. fst (\<sigma>2 x) ^ 2 + snd (\<sigma>2 x) ^ 2 > M))"
      by (rule Lemma_61_1_components_correspond[OF top1_S2_is_topology_on_strict
            hC'_sub_S2 hC'_compact hN_S2C' h\<sigma>2 hW2_conn hW2_sub_C' hW2_comp])
    have hVR2_unbdd: "\<forall>M. \<exists>p\<in>V_R2. fst p ^ 2 + snd p ^ 2 > M"
    proof -
      have "\<forall>M. \<exists>x\<in>W2_S2 - {north_pole}. fst (\<sigma>2 x) ^ 2 + snd (\<sigma>2 x) ^ 2 > M"
        using h61_1_W2 hN_in_W2 by simp
      thus ?thesis unfolding V_R2_def by (by100 blast)
    qed
    \<comment> \<open>Shared: \<sigma>2inv maps open sets in TR2 to open sets in S^2_topology.\<close>
    have h\<sigma>2inv_open_map_S2: "\<And>W :: (real\<times>real) set. W \<in> ?TR2 \<Longrightarrow> \<sigma>2inv ` W \<in> top1_S2_topology"
    proof -
      fix W :: "(real\<times>real) set" assume hW: "W \<in> ?TR2"
      have h\<sigma>2_cont_here: "top1_continuous_map_on (top1_S2 - {north_pole})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) UNIV ?TR2 \<sigma>2"
        using h\<sigma>2 unfolding top1_homeomorphism_on_def by (by100 blast)
      have hpreimg: "{x \<in> top1_S2 - {north_pole}. \<sigma>2 x \<in> W}
          \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
        using h\<sigma>2_cont_here hW unfolding top1_continuous_map_on_def by (by100 blast)
      have h\<sigma>2inv_W_eq: "\<sigma>2inv ` W = {x \<in> top1_S2 - {north_pole}. \<sigma>2 x \<in> W}"
      proof (intro set_eqI iffI)
        fix z assume "z \<in> \<sigma>2inv ` W"
        then obtain w where hw: "w \<in> W" "z = \<sigma>2inv w" by (by100 blast)
        have "z \<in> top1_S2 - {north_pole}"
          using h\<sigma>2inv_bij hw(2) unfolding bij_betw_def by (by100 blast)
        moreover have "\<sigma>2 z = w"
        proof -
          have "w \<in> \<sigma>2 ` (top1_S2 - {north_pole})"
            using h\<sigma>2_bij unfolding bij_betw_def by simp
          hence "\<sigma>2 (\<sigma>2inv w) = w" unfolding \<sigma>2inv_def by (rule f_inv_into_f)
          thus ?thesis using hw(2) by simp
        qed
        ultimately show "z \<in> {x \<in> top1_S2 - {north_pole}. \<sigma>2 x \<in> W}" using hw(1) by simp
      next
        fix z assume "z \<in> {x \<in> top1_S2 - {north_pole}. \<sigma>2 x \<in> W}"
        hence hz: "z \<in> top1_S2 - {north_pole}" "\<sigma>2 z \<in> W" by simp_all
        have "\<sigma>2inv (\<sigma>2 z) = z" unfolding \<sigma>2inv_def
          by (rule inv_into_f_f[OF bij_betw_imp_inj_on[OF h\<sigma>2_bij] hz(1)])
        thus "z \<in> \<sigma>2inv ` W" using hz(2) by (by100 force)
      qed
      have hS2N_open: "top1_S2 - {north_pole} \<in> top1_S2_topology"
        using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff north_pole_in_S2]
          top1_S2_is_topology_on_strict
        unfolding closedin_on_def is_topology_on_strict_def is_topology_on_def
        by (by100 blast)
      obtain V_S2 where hVS2_open: "V_S2 \<in> top1_S2_topology"
          and hVS2_eq: "\<sigma>2inv ` W = (top1_S2 - {north_pole}) \<inter> V_S2"
        using hpreimg[unfolded h\<sigma>2inv_W_eq[symmetric]]
        unfolding subspace_topology_def by blast
      thus "\<sigma>2inv ` W \<in> top1_S2_topology"
        using topology_inter_open[OF is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict]
          hS2N_open hVS2_open] hVS2_eq by simp
    qed
    have hUR2_bdy: "closure_on UNIV ?TR2 U_R2 = U_R2 \<union> C"
    proof -
      \<comment> \<open>\<supseteq>: cl(U) \<supseteq> U trivially. cl(U) \<supseteq> C by textbook Step 2.\<close>
      \<comment> \<open>\<subseteq>: cl(U) \<inter> V = {} since V \<in> TR2 and closure_meets_open.\<close>
      have hcl_sub: "closure_on UNIV ?TR2 U_R2 \<subseteq> U_R2 \<union> C"
      proof -
        have hcompl: "UNIV - V_R2 = U_R2 \<union> C"
        proof (intro set_eqI iffI)
          fix x assume "x \<in> UNIV - V_R2"
          hence "x \<notin> V_R2" by simp
          thus "x \<in> U_R2 \<union> C" using hUR2VR2_cover by (by100 blast)
        next
          fix x assume "x \<in> U_R2 \<union> C"
          thus "x \<in> UNIV - V_R2" using hUR2VR2_disj hUR2VR2_cover by (by100 blast)
        qed
        have "closedin_on UNIV ?TR2 (UNIV - V_R2)"
        proof -
          have "UNIV - V_R2 \<subseteq> UNIV" by simp
          moreover have "UNIV - (UNIV - V_R2) = V_R2" by (by100 blast)
          ultimately show ?thesis unfolding closedin_on_def using hVR2_in_TR2 by simp
        qed
        moreover have "U_R2 \<subseteq> UNIV - V_R2" using hUR2VR2_disj by (by100 blast)
        ultimately have "closure_on UNIV ?TR2 U_R2 \<subseteq> UNIV - V_R2"
          by (rule closure_on_subset_of_closed)
        thus ?thesis using hcompl by simp
      qed
      have hcl_sup: "U_R2 \<union> C \<subseteq> closure_on UNIV ?TR2 U_R2"
      proof -
        have "U_R2 \<subseteq> closure_on UNIV ?TR2 U_R2" by (rule subset_closure_on)
        moreover have "C \<subseteq> closure_on UNIV ?TR2 U_R2"
        proof
          fix x assume "x \<in> C"
          \<comment> \<open>Use Theorem_17_5a: suffices to show every neighborhood of x meets U_R2.\<close>
          show "x \<in> closure_on UNIV ?TR2 U_R2"
          proof (rule iffD2[OF Theorem_17_5a[OF hTR2]])
            show "(x :: real\<times>real) \<in> UNIV" by simp
            show "U_R2 \<subseteq> (UNIV :: (real\<times>real) set)" by simp
            show "\<forall>U. neighborhood_of x UNIV ?TR2 U \<longrightarrow> intersects U U_R2"
            proof (intro allI impI)
              fix W assume hW: "neighborhood_of x UNIV ?TR2 W"
              hence hW_open: "W \<in> ?TR2" and hxW: "x \<in> W"
                unfolding neighborhood_of_def by simp_all
              \<comment> \<open>Transfer to S^2: \<sigma>2inv(W) open in S^2\{N}, meets C'.
                 Apply simple_closed_curve_boundary_meets_component.\<close>
              \<comment> \<open>Transfer to S^2 via \<sigma>2inv.\<close>
              have h\<sigma>2inv_W_open: "\<sigma>2inv ` W \<in> top1_S2_topology"
                using h\<sigma>2inv_open_map_S2[OF hW_open] .
              have hx_in_\<sigma>W: "\<sigma>2inv x \<in> \<sigma>2inv ` W" using hxW by (by100 blast)
              have hx_in_C': "\<sigma>2inv x \<in> C'"
                unfolding C'_def \<sigma>2inv_def using \<open>x \<in> C\<close> by (by100 blast)
              have hW12_eq: "W1_S2 \<union> W2_S2 = top1_S2 - C'"
                using hW12_cover hC'_decomp by simp
              have "\<sigma>2inv ` W \<inter> W1_S2 \<noteq> {}"
                by (rule simple_closed_curve_boundary_meets_component[OF
                    top1_S2_is_topology_on_strict hC'_scc hW1_conn hW2_conn
                    hW12_disj[folded hC'_decomp[symmetric]]
                    hW12_eq hW1_ne hW2_ne hW1_open_S2 hW2_open_S2
                    hx_in_C' h\<sigma>2inv_W_open hx_in_\<sigma>W])
              then obtain z where hz: "z \<in> \<sigma>2inv ` W" "z \<in> W1_S2" by (by100 blast)
              have "\<sigma>2 z \<in> W"
              proof -
                obtain w where "w \<in> W" "z = \<sigma>2inv w" using hz(1) by (by100 blast)
                have "w \<in> \<sigma>2 ` (top1_S2 - {north_pole})"
                  using h\<sigma>2_bij unfolding bij_betw_def by simp
                hence "\<sigma>2 (\<sigma>2inv w) = w" unfolding \<sigma>2inv_def by (rule f_inv_into_f)
                thus ?thesis using \<open>z = \<sigma>2inv w\<close> \<open>w \<in> W\<close> by simp
              qed
              moreover have "\<sigma>2 z \<in> U_R2" unfolding U_R2_def using hz(2) by (by100 blast)
              ultimately show "intersects W U_R2" unfolding intersects_def by (by100 blast)
            qed
          qed
        qed
        ultimately show ?thesis by (by100 blast)
      qed
      show ?thesis using hcl_sub hcl_sup by (by100 blast)
    qed
    have hVR2_bdy: "closure_on UNIV ?TR2 V_R2 = V_R2 \<union> C"
    proof -
      have hcl_sub: "closure_on UNIV ?TR2 V_R2 \<subseteq> V_R2 \<union> C"
      proof -
        have hcompl: "UNIV - U_R2 = V_R2 \<union> C"
        proof (intro set_eqI iffI)
          fix x assume "x \<in> UNIV - U_R2"
          thus "x \<in> V_R2 \<union> C" using hUR2VR2_cover by (by100 blast)
        next
          fix x assume "x \<in> V_R2 \<union> C"
          thus "x \<in> UNIV - U_R2" using hUR2VR2_disj hUR2VR2_cover by (by100 blast)
        qed
        have "closedin_on UNIV ?TR2 (UNIV - U_R2)"
        proof -
          have "UNIV - U_R2 \<subseteq> UNIV" by simp
          moreover have "UNIV - (UNIV - U_R2) = U_R2" by (by100 blast)
          ultimately show ?thesis unfolding closedin_on_def using hUR2_in_TR2 by simp
        qed
        moreover have "V_R2 \<subseteq> UNIV - U_R2" using hUR2VR2_disj by (by100 blast)
        ultimately have "closure_on UNIV ?TR2 V_R2 \<subseteq> UNIV - U_R2"
          by (rule closure_on_subset_of_closed)
        thus ?thesis using hcompl by simp
      qed
      have hcl_sup: "V_R2 \<union> C \<subseteq> closure_on UNIV ?TR2 V_R2"
      proof -
        have "V_R2 \<subseteq> closure_on UNIV ?TR2 V_R2" by (rule subset_closure_on)
        moreover have "C \<subseteq> closure_on UNIV ?TR2 V_R2"
        proof
          fix x assume "x \<in> C"
          show "x \<in> closure_on UNIV ?TR2 V_R2"
          proof (rule iffD2[OF Theorem_17_5a[OF hTR2]])
            show "(x :: real\<times>real) \<in> UNIV" by simp
            show "V_R2 \<subseteq> (UNIV :: (real\<times>real) set)" by simp
            show "\<forall>U. neighborhood_of x UNIV ?TR2 U \<longrightarrow> intersects U V_R2"
            proof (intro allI impI)
              fix W assume hW: "neighborhood_of x UNIV ?TR2 W"
              have hW_open: "W \<in> ?TR2" and hxW: "x \<in> W"
                using hW unfolding neighborhood_of_def by simp_all
              have h\<sigma>2inv_W_open: "\<sigma>2inv ` W \<in> top1_S2_topology"
                using h\<sigma>2inv_open_map_S2[OF hW_open] .
              have hx_in_C': "\<sigma>2inv x \<in> C'"
                unfolding C'_def \<sigma>2inv_def using \<open>x \<in> C\<close> by (by100 blast)
              have hW12_eq: "W1_S2 \<union> W2_S2 = top1_S2 - C'"
                using hW12_cover hC'_decomp by simp
              \<comment> \<open>Apply helper with W2 as target (swap W1/W2 roles).\<close>
              have hW21_disj: "W2_S2 \<inter> W1_S2 = {}" using hW12_disj by (by100 blast)
              have hW21_cover: "W2_S2 \<union> W1_S2 = top1_S2 - C'"
                using hW12_cover hC'_decomp by (by100 blast)
              have h\<sigma>x_in_\<sigma>W: "\<sigma>2inv x \<in> \<sigma>2inv ` W" using hxW by (by100 blast)
              have "\<sigma>2inv ` W \<inter> W2_S2 \<noteq> {}"
                by (rule simple_closed_curve_boundary_meets_component[OF
                    top1_S2_is_topology_on_strict hC'_scc hW2_conn hW1_conn
                    hW21_disj hW21_cover hW2_ne hW1_ne hW2_open_S2 hW1_open_S2
                    hx_in_C' h\<sigma>2inv_W_open h\<sigma>x_in_\<sigma>W])
              then obtain z where "z \<in> \<sigma>2inv ` W" "z \<in> W2_S2" by (by100 blast)
              have "\<sigma>2 z \<in> W"
              proof -
                obtain w where "w \<in> W" "z = \<sigma>2inv w" using \<open>z \<in> \<sigma>2inv ` W\<close> by (by100 blast)
                have "w \<in> \<sigma>2 ` (top1_S2 - {north_pole})"
                  using h\<sigma>2_bij unfolding bij_betw_def by simp
                hence "\<sigma>2 (\<sigma>2inv w) = w" unfolding \<sigma>2inv_def by (rule f_inv_into_f)
                thus ?thesis using \<open>z = \<sigma>2inv w\<close> \<open>w \<in> W\<close> by simp
              qed
              moreover have "\<sigma>2 z \<in> V_R2"
              proof -
                have "z \<in> top1_S2 - {north_pole}"
                  using \<open>z \<in> \<sigma>2inv ` W\<close> h\<sigma>2inv_bij unfolding bij_betw_def by (by100 blast)
                hence "z \<noteq> north_pole" by (by100 blast)
                hence "z \<in> W2_S2 - {north_pole}" using \<open>z \<in> W2_S2\<close> by (by100 blast)
                thus ?thesis unfolding V_R2_def by (by100 blast)
              qed
              ultimately show "intersects W V_R2" unfolding intersects_def by (by100 blast)
            qed
          qed
        qed
        ultimately show ?thesis by (by100 blast)
      qed
      show ?thesis using hcl_sub hcl_sup by (by100 blast)
    qed
    show ?thesis by (intro that[of U_R2 V_R2])
      (use hUR2_ne hVR2_ne hUR2VR2_disj hUR2VR2_cover hUR2_conn hVR2_conn
           hUR2_bdd hVR2_unbdd hUR2_bdy hVR2_bdy in simp)+
  qed
  \<comment> \<open>Step 3 (Path-connected): R^2 is locally path-connected, so components are path-connected.\<close>
  \<comment> \<open>First show UNIV-C is open (C compact hence closed).\<close>
  have hUNIV_C_open_global: "UNIV - C \<in> ?TR2"
  proof -
    obtain f where "top1_continuous_map_on top1_S1 top1_S1_topology UNIV ?TR2 f" "f ` top1_S1 = C"
      using assms unfolding top1_simple_closed_curve_on_def by (by100 blast)
    have "compact top1_S1" using S1_compact
      top1_compact_on_subspace_UNIV_iff_compact[of top1_S1]
      product_topology_on_open_sets_real2
      unfolding top1_S1_topology_def by (by100 simp)
    have "compact C"
    proof -
      have "compact (f ` top1_S1)"
      proof (rule compact_continuous_image)
        show "continuous_on top1_S1 f"
          unfolding continuous_on_open_invariant
        proof (intro allI impI)
          fix B :: "(real \<times> real) set" assume hBo: "open B"
          have "B \<in> ?TR2" using hBo product_topology_on_open_sets_real2
            unfolding top1_open_sets_def by (by100 simp)
          hence "{x \<in> top1_S1. f x \<in> B} \<in> top1_S1_topology"
            using \<open>top1_continuous_map_on top1_S1 top1_S1_topology UNIV ?TR2 f\<close>
            unfolding top1_continuous_map_on_def by (by100 blast)
          then obtain W where hW: "W \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
              and heq: "{x \<in> top1_S1. f x \<in> B} = top1_S1 \<inter> W"
            unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
          have "open W" using hW product_topology_on_open_sets_real2
            unfolding top1_open_sets_def by (by100 simp)
          moreover have "W \<inter> top1_S1 = f -` B \<inter> top1_S1"
            using heq by (by100 blast)
          ultimately show "\<exists>A. open A \<and> A \<inter> top1_S1 = f -` B \<inter> top1_S1" by (by100 blast)
        qed
        show "compact top1_S1" by (rule \<open>compact top1_S1\<close>)
      qed
      thus ?thesis using \<open>f ` top1_S1 = C\<close> by simp
    qed
    hence "closed C" by (rule compact_imp_closed)
    hence "open (- C)" by (rule open_Compl)
    hence "open (UNIV - C)" by (simp add: Compl_eq_Diff_UNIV)
    thus ?thesis using product_topology_on_open_sets_real2 unfolding top1_open_sets_def by (by100 simp)
  qed
  have hUNIV_C_lpc_global: "top1_locally_path_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
    by (rule open_subset_locally_path_connected[OF R2_locally_path_connected hUNIV_C_open_global]) simp
  have hU_pc: "top1_path_connected_on U (subspace_topology UNIV ?TR2 U)"
  proof -
    have hTU: "is_topology_on U (subspace_topology UNIV ?TR2 U)"
      using hU_conn unfolding top1_connected_on_def by (by100 blast)
    have hU_locp: "top1_locally_path_connected_on U (subspace_topology UNIV ?TR2 U)"
    proof -
      \<comment> \<open>UNIV-C is open in R^2. U \<subseteq> UNIV-C. U is open in UNIV-C (component of lpc space).
         Open subset of R^2 is lpc. U open subset of that.\<close>
      have hUNIV_C_open: "UNIV - C \<in> ?TR2" by (rule hUNIV_C_open_global)
      have hUNIV_C_lpc: "top1_locally_path_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
        by (rule hUNIV_C_lpc_global)
      \<comment> \<open>U is open in UNIV-C (component of lpc open space).\<close>
      have hU_open_in_UC: "U \<in> subspace_topology UNIV ?TR2 (UNIV - C)"
      proof -
        \<comment> \<open>U is a connected component of UNIV-C (lpc space). Components of lpc = open.\<close>
        have hTUC: "is_topology_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
        proof -
          have "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
            using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
          thus ?thesis by (rule subspace_topology_is_topology_on) simp
        qed
        obtain u where hu: "u \<in> U" using hUV_ne(1) by (by100 blast)
        have hu_UC: "u \<in> UNIV - C" using hu hUV_cover by (by100 blast)
        \<comment> \<open>The path component of u in UNIV-C equals U.
           By Theorem 25.5, in lpc space path component = component.\<close>
        have "top1_path_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u = U"
        proof -
          \<comment> \<open>U is a connected component: U connected, U \<subseteq> UNIV-C, U maximal.
             In lpc space, path component = component (Theorem 25.5).\<close>
          have "top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u = U"
          proof -
            \<comment> \<open>U is a component of UNIV-C: it's connected, and any connected set containing u
               that is bigger than U would have to intersect V, but U \<inter> V = {} and both open.\<close>
            \<comment> \<open>component_of(u) = \<Union>{C \<subseteq> UNIV-C. u \<in> C \<and> connected C}.\<close>
            \<comment> \<open>U \<subseteq> component_of(u): U is connected and u \<in> U.\<close>
            have hU_sub_comp: "U \<subseteq> top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u"
              unfolding top1_component_of_on_def
            proof
              fix x assume hxU: "x \<in> U"
              have hUsub: "U \<subseteq> UNIV - C" using hUV_cover by (by100 blast)
              moreover have "u \<in> U" using hu by simp
              moreover have "top1_connected_on U (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) U)"
              proof -
                have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) U
                    = subspace_topology UNIV ?TR2 U"
                  by (rule subspace_topology_trans[OF hUsub])
                thus ?thesis using hU_conn by simp
              qed
              ultimately show "x \<in> \<Union>{Ca. Ca \<subseteq> UNIV - C \<and> u \<in> Ca \<and>
                  top1_connected_on Ca (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) Ca)}"
                using hxU hUsub by (by100 blast)
            qed
            \<comment> \<open>component_of(u) \<subseteq> U: any connected C with u \<in> C \<subseteq> UNIV-C lies in U.
               (If C intersected V, C = (C\<inter>U) \<union> (C\<inter>V) with both open in C, contradicting connected.)\<close>
            have hcomp_sub_U: "top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u \<subseteq> U"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              then obtain v where hv_comp: "v \<in> top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u"
                  and hv_notU: "v \<notin> U" by (by100 blast)
              have hv_UC: "v \<in> UNIV - C"
                using hv_comp unfolding top1_component_of_on_def by (by100 blast)
              hence "v \<in> V" using hv_notU hUV_cover by (by100 blast)
              \<comment> \<open>component_of(u) is connected. V is connected. They share v.\<close>
              have hcomp_conn: "top1_connected_on (top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u)
                  (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))
                    (top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u))"
                by (rule top1_component_of_on_connected[OF hTUC hu_UC])
              \<comment> \<open>comp(u) \<union> V is connected (share point v) and = UNIV-C.\<close>
              have hcomp_V_conn: "top1_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
              proof -
                let ?comp = "top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u"
                define A :: "nat \<Rightarrow> (real \<times> real) set" where "A = (\<lambda>i. if i = 0 then ?comp else V)"
                have hI: "{0::nat, 1} \<noteq> {}" by simp
                have hV_sub: "V \<subseteq> UNIV - C" using hUV_cover by (by100 blast)
                have hcomp_sub: "?comp \<subseteq> UNIV - C" unfolding top1_component_of_on_def by (by100 blast)
                have hAsub: "\<forall>i\<in>{0::nat,1}. A i \<subseteq> UNIV - C"
                  unfolding A_def using hV_sub hcomp_sub by auto
                have hAconn: "\<forall>i\<in>{0::nat,1}. top1_connected_on (A i) (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (A i))"
                proof
                  fix i :: nat assume "i \<in> {0, 1}"
                  show "top1_connected_on (A i) (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (A i))"
                  proof (cases "i = 0")
                    case True thus ?thesis unfolding A_def using hcomp_conn by simp
                  next
                    case False
                    have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) V
                        = subspace_topology UNIV ?TR2 V"
                      by (rule subspace_topology_trans[OF hV_sub])
                    thus ?thesis using False unfolding A_def using hV_conn by simp
                  qed
                qed
                have hv_inter: "v \<in> \<Inter>(A ` {0::nat, 1})"
                  unfolding A_def using hv_comp \<open>v \<in> V\<close> by simp
                have hY_eq: "(\<Union>i\<in>{0::nat,1}. A i) = UNIV - C"
                proof -
                  have "?comp \<union> V \<supseteq> U \<union> V" using hU_sub_comp by (by100 blast)
                  hence "?comp \<union> V = UNIV - C" using hUV_cover
                    unfolding top1_component_of_on_def by (by100 blast)
                  moreover have "(\<Union>i\<in>{0::nat,1}. A i) = ?comp \<union> V" unfolding A_def by auto
                  ultimately show ?thesis by simp
                qed
                have "top1_connected_on (\<Union>i\<in>{0::nat,1}. A i) (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (\<Union>i\<in>{0::nat,1}. A i))"
                  by (rule Theorem_23_3[OF hTUC hI hAsub hAconn hv_inter])
                hence "top1_connected_on (UNIV - C) (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (UNIV - C))"
                  using hY_eq by simp
                moreover have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (UNIV - C)
                    = subspace_topology UNIV ?TR2 (UNIV - C)"
                  by (rule subspace_topology_self_carrier) (auto simp: subspace_topology_def)
                ultimately show ?thesis by simp
              qed
              show False using hC_sep hcomp_V_conn by simp
            qed
            show ?thesis using hU_sub_comp hcomp_sub_U by (by100 blast)
          qed
          moreover have "top1_path_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u
              = top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u"
            using Theorem_25_5[OF hTUC] hUNIV_C_lpc_global hu_UC by (by100 blast)
          ultimately show ?thesis by simp
        qed
        moreover have "top1_path_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u
            \<in> subspace_topology UNIV ?TR2 (UNIV - C)"
          by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTUC hUNIV_C_lpc hu_UC])
        ultimately show ?thesis by simp
      qed
      have hU_sub_UC: "U \<subseteq> UNIV - C" using hUV_cover by (by100 blast)
      have "top1_locally_path_connected_on U
          (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) U)"
        by (rule open_subset_locally_path_connected[OF hUNIV_C_lpc hU_open_in_UC hU_sub_UC])
      moreover have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) U
          = subspace_topology UNIV ?TR2 U"
        by (rule subspace_topology_trans[OF hU_sub_UC])
      ultimately show ?thesis by simp
    qed
    show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF hTU hU_conn hU_locp hUV_ne(1)])
  qed
  have hV_pc: "top1_path_connected_on V (subspace_topology UNIV ?TR2 V)"
  proof -
    have hTV: "is_topology_on V (subspace_topology UNIV ?TR2 V)"
      using hV_conn unfolding top1_connected_on_def by (by100 blast)
    have hV_locp: "top1_locally_path_connected_on V (subspace_topology UNIV ?TR2 V)"
    proof -
      have hUNIV_C_open: "UNIV - C \<in> ?TR2" by (rule hUNIV_C_open_global)
      have hUNIV_C_lpc: "top1_locally_path_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
        by (rule hUNIV_C_lpc_global)
      have hV_open_in_UC: "V \<in> subspace_topology UNIV ?TR2 (UNIV - C)"
      proof -
        have hTUC: "is_topology_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
        proof -
          have "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
            using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
          thus ?thesis by (rule subspace_topology_is_topology_on) simp
        qed
        obtain v where hv: "v \<in> V" using hUV_ne(2) by (by100 blast)
        have hv_UC: "v \<in> UNIV - C" using hv hUV_cover by (by100 blast)
        have "top1_path_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) v = V"
        proof -
          let ?comp_v = "top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) v"
          have hV_sub': "V \<subseteq> UNIV - C" using hUV_cover by (by100 blast)
          have hV_sub_comp: "V \<subseteq> ?comp_v"
            unfolding top1_component_of_on_def
          proof
            fix x assume hxV: "x \<in> V"
            have "top1_connected_on V (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) V)"
            proof -
              have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) V
                  = subspace_topology UNIV ?TR2 V" by (rule subspace_topology_trans[OF hV_sub'])
              thus ?thesis using hV_conn by simp
            qed
            thus "x \<in> \<Union>{Ca. Ca \<subseteq> UNIV - C \<and> v \<in> Ca \<and>
                top1_connected_on Ca (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) Ca)}"
              using hxV hV_sub' hv by (by100 blast)
          qed
          have hcomp_v_sub_V: "?comp_v \<subseteq> V"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then obtain w where hw_comp: "w \<in> ?comp_v" and hw_notV: "w \<notin> V" by (by100 blast)
            have hw_UC: "w \<in> UNIV - C" using hw_comp unfolding top1_component_of_on_def by (by100 blast)
            hence "w \<in> U" using hw_notV hUV_cover by (by100 blast)
            have hcomp_v_conn: "top1_connected_on ?comp_v
                (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) ?comp_v)"
              by (rule top1_component_of_on_connected[OF hTUC hv_UC])
            have hU_sub': "U \<subseteq> UNIV - C" using hUV_cover by (by100 blast)
            have hU_conn_sub: "top1_connected_on U
                (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) U)"
            proof -
              have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) U
                  = subspace_topology UNIV ?TR2 U" by (rule subspace_topology_trans[OF hU_sub'])
              thus ?thesis using hU_conn by simp
            qed
            define B :: "nat \<Rightarrow> (real \<times> real) set" where "B = (\<lambda>i. if i = 0 then ?comp_v else U)"
            have "w \<in> \<Inter>(B ` {0::nat, 1})" unfolding B_def using hw_comp \<open>w \<in> U\<close> by simp
            moreover have "\<forall>i\<in>{0::nat,1}. B i \<subseteq> UNIV - C"
              unfolding B_def using hU_sub' unfolding top1_component_of_on_def by auto
            moreover have "\<forall>i\<in>{0::nat,1}. top1_connected_on (B i)
                (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (B i))"
            proof
              fix i :: nat assume "i \<in> {0, 1}"
              show "top1_connected_on (B i) (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (B i))"
                unfolding B_def using hcomp_v_conn hU_conn_sub by auto
            qed
            ultimately have "top1_connected_on (\<Union>i\<in>{0::nat,1}. B i)
                (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (\<Union>i\<in>{0::nat,1}. B i))"
              using Theorem_23_3[OF hTUC, of "{0::nat,1}" B w] by (by100 blast)
            moreover have "(\<Union>i\<in>{0::nat,1}. B i) = UNIV - C"
            proof -
              have "?comp_v \<union> U \<supseteq> V \<union> U" using hV_sub_comp by (by100 blast)
              thus ?thesis unfolding B_def using hUV_cover
                unfolding top1_component_of_on_def by auto
            qed
            moreover have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (UNIV - C)
                = subspace_topology UNIV ?TR2 (UNIV - C)"
              by (rule subspace_topology_self_carrier) (auto simp: subspace_topology_def)
            ultimately have "top1_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))" by simp
            thus False using hC_sep by simp
          qed
          have "?comp_v = V" using hV_sub_comp hcomp_v_sub_V by (by100 blast)
          moreover have "top1_path_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) v = ?comp_v"
            using Theorem_25_5[OF hTUC] hUNIV_C_lpc_global hv_UC by (by100 blast)
          ultimately show ?thesis by simp
        qed
        moreover have "top1_path_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) v
            \<in> subspace_topology UNIV ?TR2 (UNIV - C)"
          by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTUC hUNIV_C_lpc_global hv_UC])
        ultimately show ?thesis by simp
      qed
      have hV_sub_UC: "V \<subseteq> UNIV - C" using hUV_cover by (by100 blast)
      have "top1_locally_path_connected_on V
          (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) V)"
        by (rule open_subset_locally_path_connected[OF hUNIV_C_lpc hV_open_in_UC hV_sub_UC])
      moreover have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) V
          = subspace_topology UNIV ?TR2 V"
        by (rule subspace_topology_trans[OF hV_sub_UC])
      ultimately show ?thesis by simp
    qed
    show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF hTV hV_conn hV_locp hUV_ne(2)])
  qed
  \<comment> \<open>Step 4 (Bounded/unbounded): Under stereographic projection, one component maps to
     the bounded component and the other to the unbounded one (Lemma 61.1).\<close>
  have hU_bdd: "\<exists>M. \<forall>p\<in>U. fst p ^ 2 + snd p ^ 2 \<le> M" by (rule hU_bdd_raw)
  have hV_unbdd: "\<forall>M. \<exists>p\<in>V. fst p ^ 2 + snd p ^ 2 > M" by (rule hV_unbdd_raw)
  \<comment> \<open>Step 5 (Boundary = C): Both components have C as their common boundary.\<close>
  have hU_bdy: "closure_on UNIV (product_topology_on top1_open_sets top1_open_sets) U = U \<union> C" by (rule hU_bdy_raw)
  have hV_bdy: "closure_on UNIV (product_topology_on top1_open_sets top1_open_sets) V = V \<union> C" by (rule hV_bdy_raw)
  show ?thesis using hUV_ne hUV_disj hUV_cover hU_pc hV_pc hU_bdd hV_unbdd hU_bdy hV_bdy
    by blast
qed


end
