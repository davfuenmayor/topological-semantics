theory boolean_algebra_infinitary
  imports boolean_algebra function_algebra
begin

subsection \<open>Encoding infinitary Boolean operations\<close>

(**Our aim is to encode complete Boolean algebras (of sets) which we can later be used to
interpret quantified formulas (somewhat in the spirit of Boolean-valued models for set theory).*)

(**We start by defining infinite meet (infimum) and infinite join (supremum) operations,*)
definition infimum:: "('p \<sigma>)\<sigma> \<Rightarrow> 'p \<sigma>" ("\<^bold>\<And>_") 
  where "\<^bold>\<And>S \<equiv> \<lambda>w. \<forall>X. S X \<longrightarrow> X w"
definition supremum::"('p \<sigma>)\<sigma> \<Rightarrow> 'p \<sigma>" ("\<^bold>\<Or>_") 
  where "\<^bold>\<Or>S \<equiv> \<lambda>w. \<exists>X. S X  \<and>  X w"

(*add infimum and supremum to definition set of algebra connectives*)
declare infimum_def[conn] supremum_def[conn]

(**Infimum and supremum satisfy an infinite variant of the De Morgan laws*)
lemma iDM_a: "\<^bold>\<midarrow>(\<^bold>\<And>S) \<^bold>\<approx> \<^bold>\<Or>(S\<^sup>-)" unfolding order conn op_conn by force
lemma iDM_b:" \<^bold>\<midarrow>(\<^bold>\<Or>S) \<^bold>\<approx> \<^bold>\<And>(S\<^sup>-)" unfolding order conn op_conn by force

(**We show that the our encoded Boolean algebras are lattice-complete.*)

(**The functions below return the set of upper-/lower-bounds of a set of sets S wrt. domain D*)
definition upper_bounds::"('p \<sigma>)\<sigma> \<Rightarrow> ('p \<sigma>)\<sigma> \<Rightarrow> ('p \<sigma>)\<sigma>" ("ub\<^sup>_")
  where "ub\<^sup>D S \<equiv> \<lambda>U. D U \<and> (\<forall>X. S X \<longrightarrow> X \<^bold>\<preceq> U)" 
definition lower_bounds::"('p \<sigma>)\<sigma> \<Rightarrow> ('p \<sigma>)\<sigma> \<Rightarrow> ('p \<sigma>)\<sigma>" ("lb\<^sup>_")
  where "lb\<^sup>D S \<equiv> \<lambda>L. D L \<and> (\<forall>X. S X \<longrightarrow> L \<^bold>\<preceq> X)"

(**Similarly, the functions below return the set of least/greatest upper-/lower-bounds for S wrt. D*)
definition lub::"('p \<sigma>)\<sigma> \<Rightarrow> ('p \<sigma>)\<sigma> \<Rightarrow> ('p \<sigma>)\<sigma>" ("lub\<^sup>_") 
  where "lub\<^sup>D S \<equiv> \<lambda>U. ub\<^sup>D S U \<and> (\<forall>X. ub\<^sup>D S X \<longrightarrow> U \<^bold>\<preceq> X)"
definition glb::"('p \<sigma>)\<sigma> \<Rightarrow> ('p \<sigma>)\<sigma> \<Rightarrow> ('p \<sigma>)\<sigma>" ("glb\<^sup>_")
  where "glb\<^sup>D S \<equiv> \<lambda>L. lb\<^sup>D S L \<and> (\<forall>X. lb\<^sup>D S X \<longrightarrow> X \<^bold>\<preceq> L)"

(**Note that the term \<^bold>\<top> below denotes the top element in the algebra of sets of sets (i.e. the powerset)*)
lemma sup_lub: "let D=\<^bold>\<top> in lub\<^sup>D S \<^bold>\<Or>S" unfolding lub_def upper_bounds_def conn order by auto
lemma sup_exist_unique: "let D=\<^bold>\<top> in \<forall>S. \<exists>!X. lub\<^sup>D S X" by (metis lub_def setequ_char setequ_ext sup_lub)
lemma inf_glb: "let D=\<^bold>\<top> in glb\<^sup>D S \<^bold>\<And>S" unfolding glb_def lower_bounds_def conn order by auto
lemma inf_exist_unique: "let D=\<^bold>\<top> in \<forall>S. \<exists>!X. glb\<^sup>D S X" by (metis glb_def inf_glb setequ_char setequ_ext)

abbreviation "isEmpty S \<equiv> \<forall>x. \<not>S x"
abbreviation "nonEmpty S \<equiv> \<exists>x. S x"

lemma "isEmpty S \<Longrightarrow> \<^bold>\<And>S \<^bold>\<approx> \<^bold>\<top>" unfolding order conn by simp
lemma "isEmpty S \<Longrightarrow> \<^bold>\<Or>S \<^bold>\<approx> \<^bold>\<bottom>" unfolding order conn by simp

(**The property of being closed under arbitrary (resp. nonempty) supremum/infimum.*)
definition infimum_closed :: "('p \<sigma>)\<sigma> \<Rightarrow> bool"
  where "infimum_closed S  \<equiv> \<forall>D. D \<^bold>\<preceq> S \<longrightarrow> S(\<^bold>\<And>D)" (*observe that D can be empty*)
definition supremum_closed :: "('p \<sigma>)\<sigma> \<Rightarrow> bool" 
  where "supremum_closed S \<equiv> \<forall>D. D \<^bold>\<preceq> S \<longrightarrow> S(\<^bold>\<Or>D)" (*observe that D can be empty*)
definition infimum_closed' :: "('p \<sigma>)\<sigma> \<Rightarrow> bool" 
  where"infimum_closed' S  \<equiv> \<forall>D. nonEmpty D \<and> D \<^bold>\<preceq> S \<longrightarrow> S(\<^bold>\<And>D)"
definition supremum_closed' :: "('p \<sigma>)\<sigma> \<Rightarrow> bool" 
  where "supremum_closed' S \<equiv> \<forall>D. nonEmpty D \<and> D \<^bold>\<preceq> S \<longrightarrow> S(\<^bold>\<Or>D)"

(**Note that arbitrary infimum- (resp. supremum-) closed sets include the top (resp. bottom) element.*)
lemma "infimum_closed S \<Longrightarrow> S \<^bold>\<top>" unfolding infimum_closed_def conn order by force
lemma "supremum_closed S \<Longrightarrow> S \<^bold>\<bottom>" unfolding supremum_closed_def conn order by force
(**However, the above does not hold for non-empty infimum- (resp. supremum-) closed sets.*)
lemma "infimum_closed' S \<Longrightarrow> S \<^bold>\<top>" nitpick oops
lemma "supremum_closed' S \<Longrightarrow> S \<^bold>\<bottom>" nitpick oops

(**We have in fact the following characterizations for the notions above:*)
lemma inf_closed_char: "infimum_closed S = (infimum_closed' S \<and> S \<^bold>\<top>)" 
  unfolding infimum_closed'_def infimum_closed_def by (metis bottom_def infimum_closed_def infimum_def setequ_char setequ_ext subset_def top_def)
lemma sup_closed_char: "supremum_closed S = (supremum_closed' S \<and> S \<^bold>\<bottom>)"
  unfolding supremum_closed'_def supremum_closed_def by (metis (no_types, opaque_lifting) L14 L9 bottom_def setequ_ext subset_def supremum_def)

lemma inf_sup_closed_dc: "infimum_closed S = supremum_closed S\<^sup>-" by (smt (verit) BA_dn iDM_a iDM_b infimum_closed_def setequ_ext sfun_dualcompl_def subset_def supremum_closed_def)
lemma inf_sup_closed_dc': "infimum_closed' S = supremum_closed' S\<^sup>-" by (smt (verit, best) dualcompl_invol iDM_b infimum_closed'_def setequ_ext sfun_dualcompl_def subset_def supremum_closed'_def)

(**We check some further properties:*)
lemma fp_inf_sup_closed_dual: "infimum_closed (fp \<phi>) \<Longrightarrow> supremum_closed (fp \<phi>\<^sup>d)" 
  by (simp add: fp_dual inf_sup_closed_dc)
lemma fp_inf_sup_closed_dual': "infimum_closed' (fp \<phi>) \<Longrightarrow> supremum_closed' (fp \<phi>\<^sup>d)" 
  by (simp add: fp_dual inf_sup_closed_dc')
lemma fp_sup_inf_closed_dual: "supremum_closed (fp \<phi>) \<Longrightarrow> infimum_closed (fp \<phi>\<^sup>d)" 
  by (simp add: dualcompl_invol fp_dual inf_sup_closed_dc)
lemma fp_sup_inf_closed_dual': "supremum_closed' (fp \<phi>) \<Longrightarrow> infimum_closed' (fp \<phi>\<^sup>d)"
  by (simp add: dualcompl_invol fp_dual inf_sup_closed_dc')

(**We verify that being infimum-closed' (resp. supremum-closed') entails being meet-closed (resp. join-closed).*)
lemma inf_meet_closed: "\<forall>S. infimum_closed' S \<longrightarrow> meet_closed S" proof -
  { fix S::"'w \<sigma> \<Rightarrow> bool"
    { assume inf_closed: "infimum_closed' S"
      hence "meet_closed S" proof -
        { fix X::"'w \<sigma>" and Y::"'w \<sigma>"
          let ?D="\<lambda>Z. Z=X \<or> Z=Y"
          { assume "S X \<and> S Y"
            hence "?D \<^bold>\<preceq> S" using subset_def by blast
            moreover have "nonEmpty ?D" by auto
            ultimately have "S(\<^bold>\<And>?D)" using inf_closed infimum_closed'_def by (smt (z3))
            hence "S(\<lambda>w. \<forall>Z. (Z=X \<or> Z=Y) \<longrightarrow> Z w)" unfolding infimum_def by simp
            moreover have "(\<lambda>w. \<forall>Z. (Z=X \<or> Z=Y) \<longrightarrow> Z w) = (\<lambda>w. X w \<and> Y w)" by auto
            ultimately have "S(\<lambda>w. X w \<and> Y w)" by simp
          } hence "(S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<and> Y)" unfolding conn by (rule impI)
        } thus ?thesis unfolding meet_closed_def by simp  qed
    } hence "infimum_closed' S \<longrightarrow> meet_closed S" by simp
  } thus ?thesis by (rule allI)
qed
lemma sup_join_closed: "\<forall>P. supremum_closed' P \<longrightarrow> join_closed P" proof -
  { fix S::"'w \<sigma> \<Rightarrow> bool"
    { assume sup_closed: "supremum_closed' S"
      hence "join_closed S" proof -
        { fix X::"'w \<sigma>" and Y::"'w \<sigma>"
          let ?D="\<lambda>Z. Z=X \<or> Z=Y"
          { assume "S X \<and> S Y"
            hence "?D \<^bold>\<preceq> S" using subset_def by blast
            moreover have "nonEmpty ?D" by auto
            ultimately have "S(\<^bold>\<Or>?D)" using sup_closed supremum_closed'_def by (smt (z3))
            hence "S(\<lambda>w. \<exists>Z. (Z=X \<or> Z=Y) \<and> Z w)" unfolding supremum_def by simp
            moreover have "(\<lambda>w. \<exists>Z. (Z=X \<or> Z=Y) \<and> Z w) = (\<lambda>w. X w \<or> Y w)" by auto
            ultimately have "S(\<lambda>w. X w \<or> Y w)" by simp
          } hence "(S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<or> Y)" unfolding conn by (rule impI)
        } thus ?thesis unfolding join_closed_def by simp qed
    } hence "supremum_closed' S \<longrightarrow> join_closed S" by simp
  } thus ?thesis by (rule allI)
qed

end