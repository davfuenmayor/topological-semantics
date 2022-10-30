theory conditions_kuratowski_infinitary
  imports conditions_kuratowski "../boolean_algebra/boolean_algebra_infinitary"
begin

(**We define and interrelate infinitary variants for some previously introduced
 axiomatic conditions on operators.*)

(**Distribution over infinite joins (suprema) or infinite additivity (iADDI).*)
definition iADDI::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iADDI")
  where "iADDI \<phi>   \<equiv> \<forall>S. \<phi>(\<^bold>\<Or>S) \<approx> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" 
definition iADDI_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iADDI\<^sup>a")
  where "iADDI\<^sup>a \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<Or>S) \<preceq> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" 
definition iADDI_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iADDI\<^sup>b")
  where "iADDI\<^sup>b \<phi> \<equiv> \<forall>S. \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk> \<preceq> \<phi>(\<^bold>\<Or>S)"
(**Distribution over infinite meets (infima) or infinite multiplicativity (iMULT).*)
definition iMULT::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iMULT")
  where "iMULT \<phi>   \<equiv> \<forall>S. \<phi>(\<^bold>\<And>S) \<approx> \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>" 
definition iMULT_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iMULT\<^sup>a")
  where "iMULT\<^sup>a \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<And>S) \<preceq> \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>"
definition iMULT_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iMULT\<^sup>b")
  where "iMULT\<^sup>b \<phi> \<equiv> \<forall>S. \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<preceq> \<phi>(\<^bold>\<And>S)"

declare iADDI_def[cond] iADDI_a_def[cond] iADDI_b_def[cond]
        iMULT_def[cond] iMULT_a_def[cond] iMULT_b_def[cond]

lemma iADDI_char: "iADDI \<phi> = (iADDI\<^sup>a \<phi> \<and> iADDI\<^sup>b \<phi>)" unfolding cond using setequ_char by blast
lemma iMULT_char: "iMULT \<phi> = (iMULT\<^sup>a \<phi> \<and> iMULT\<^sup>b \<phi>)" unfolding cond using setequ_char by blast

(**ADDI-b and iADDI-b are in fact equivalent.*)
lemma iADDIb_equ: "iADDI\<^sup>b \<phi> = ADDI\<^sup>b \<phi>" proof -
  have lr: "iADDI\<^sup>b \<phi> \<Longrightarrow> ADDI\<^sup>b \<phi>" proof - (*prove as a one-liner by instantiating iADDI_b_def with S=(\<lambda>Z. Z=A \<or> Z=B)*)
  assume iaddib: "iADDI\<^sup>b \<phi>"
  { fix A::"'a \<sigma>" and B::"'a \<sigma>" (* for some reason Isabelle doesn't like other letters as type variable. Why?*)
    let ?S="\<lambda>Z. Z=A \<or> Z=B"
    have "\<^bold>\<Or>?S = A \<^bold>\<or> B" unfolding supremum_def join_def by blast
    hence p1: "\<phi>(\<^bold>\<Or>?S) = \<phi>(A \<^bold>\<or> B)" by simp
    have "\<lbrakk>\<phi> ?S\<rbrakk> = (\<lambda>Z. Z=(\<phi> A) \<or> Z=(\<phi> B))" unfolding image_def by metis
    hence p2: "\<^bold>\<Or>\<lbrakk>\<phi> ?S\<rbrakk> = (\<phi> A) \<^bold>\<or> (\<phi> B)" unfolding supremum_def join_def by auto
    have " \<^bold>\<Or>\<lbrakk>\<phi> ?S\<rbrakk> \<preceq> \<phi>(\<^bold>\<Or>?S)" using iaddib iADDI_b_def by blast    
    hence "(\<phi> A) \<^bold>\<or> (\<phi> B) \<preceq> \<phi>(A \<^bold>\<or> B)" using p1 p2 by simp
  } thus ?thesis by (simp add: ADDI_b_def) qed
  have rl: "ADDI\<^sup>b \<phi> \<Longrightarrow> iADDI\<^sup>b \<phi>" unfolding iADDI_b_def by (smt (verit) MONO_ADDIb MONO_def lub_def image_def sup_lub upper_bounds_def) 
  from lr rl show ?thesis by auto
qed
(**MULT-a and iMULT-a are also equivalent.*)
lemma iMULTa_equ: "iMULT\<^sup>a \<phi> = MULT\<^sup>a \<phi>" proof -
  have lr: "iMULT\<^sup>a \<phi> \<Longrightarrow> MULT\<^sup>a \<phi>" proof - (*prove as a one-liner by instantiating iMULT_a_def with S=(\<lambda>Z. Z=A \<or> Z=B)*)
  assume imulta: "iMULT\<^sup>a \<phi>"
  { fix A::"'a \<sigma>" and B::"'a \<sigma>"
    let ?S="\<lambda>Z. Z=A \<or> Z=B"
    have "\<^bold>\<And>?S = A \<^bold>\<and> B" unfolding infimum_def meet_def by blast
    hence p1: "\<phi>(\<^bold>\<And>?S) = \<phi>(A \<^bold>\<and> B)" by simp
    have "\<lbrakk>\<phi> ?S\<rbrakk> = (\<lambda>Z. Z=(\<phi> A) \<or> Z=(\<phi> B))" unfolding image_def by metis
    hence p2: "\<^bold>\<And>\<lbrakk>\<phi> ?S\<rbrakk> = (\<phi> A) \<^bold>\<and> (\<phi> B)" unfolding infimum_def meet_def by auto
    have "\<phi>(\<^bold>\<And>?S) \<preceq> \<^bold>\<And>\<lbrakk>\<phi> ?S\<rbrakk>" using imulta iMULT_a_def by blast    
    hence "\<phi>(A \<^bold>\<and> B) \<preceq> (\<phi> A) \<^bold>\<and> (\<phi> B)" using p1 p2 by simp
  } thus ?thesis by (simp add: MULT_a_def) qed
  have rl: "MULT\<^sup>a \<phi> \<Longrightarrow> iMULT\<^sup>a \<phi>" by (smt (verit) MONO_MULTa MONO_def glb_def iMULT_a_def inf_glb lower_bounds_def image_def)
  from lr rl show ?thesis by blast
qed

(**Thus we have that MONO, ADDI-b/iADDI-b and MULT-a/iMULT-a are all equivalent.*)
lemma MONO_iADDIb: "iADDI\<^sup>b \<phi> = MONO \<phi>" unfolding MONO_ADDIb iADDIb_equ by simp
lemma MONO_iMULTa: "iMULT\<^sup>a \<phi> = MONO \<phi>" unfolding MONO_MULTa iMULTa_equ by simp


(**Below we prove several duality relationships between iADDI(a/b) and iMULT(a/b).*)

(**Duality between iMULT-a and iADDI-b (an easy corollary from the previous equivalence).*)
lemma iMULTa_iADDIb_dual1: "iMULT\<^sup>a \<phi> = iADDI\<^sup>b \<phi>\<^sup>d" by (simp add: MULTa_ADDIb_dual1 iADDIb_equ iMULTa_equ)
lemma iMULTa_iADDIb_dual2: "iADDI\<^sup>b \<phi> = iMULT\<^sup>a \<phi>\<^sup>d" by (simp add: MULTa_ADDIb_dual2 iADDIb_equ iMULTa_equ)
(**Duality between iADDI-a and iMULT-b.*)
lemma iADDIa_iMULTb_dual1: "iADDI\<^sup>a \<phi> = iMULT\<^sup>b \<phi>\<^sup>d" by (smt (z3) BA_cmpl_equ BA_cp dualcompl_invol iADDI_a_def iDM_a iMULT_b_def im_prop1 op_dual_def setequ_ext)
lemma iADDIa_iMULTb_dual2: "iMULT\<^sup>b \<phi> = iADDI\<^sup>a \<phi>\<^sup>d" by (simp add: dual_invol iADDIa_iMULTb_dual1)
(**Duality between iADDI and iMULT.*)
lemma iADDI_iMULT_dual1: "iADDI \<phi> = iMULT \<phi>\<^sup>d" using iADDI_char iADDIa_iMULTb_dual1 iMULT_char iMULTa_iADDIb_dual2 by blast
lemma iADDI_iMULT_dual2: "iMULT \<phi> = iADDI \<phi>\<^sup>d" by (simp add: dual_invol iADDI_iMULT_dual1)

(**In fact, infinite additivity (multiplicativity) entails (dual) normality:*)
lemma iADDI_NORM: "iADDI \<phi> \<longrightarrow> NORM \<phi>" unfolding cond by (metis bottom_def image_def setequ_ext sup_empty)
lemma iMULT_DNRM: "iMULT \<phi> \<longrightarrow> DNRM \<phi>" by (simp add: NOR_dual2 iADDI_NORM iADDI_iMULT_dual2)

(**Suitable conditions on an operation can make the set of its fixed-points closed under infinite meets/joins.*)

lemma fp_sup_closed_cond1: "iADDI \<phi> \<longrightarrow> supremum_closed (fp \<phi>)" unfolding cond order supremum_closed_def fixpoints_def image_def by (smt (verit) supremum_def)
lemma fp_sup_closed_cond2: "iADDI\<^sup>a \<phi> \<and> EXPN \<phi> \<longrightarrow> supremum_closed (fp \<phi>)" unfolding cond by (smt (z3) fixpoints_def image_def setequ_char subset_def supremum_closed_def supremum_def)
lemma fp_sup_closed_cond3: "MONO \<phi> \<and> CNTR \<phi> \<longrightarrow> supremum_closed (fp \<phi>)" unfolding cond by (smt (verit, del_insts) fixpoints_def lub_def setequ_char setequ_ext subset_def sup_lub supremum_closed_def upper_bounds_def)

lemma fp_inf_closed_cond1: "iMULT \<phi> \<longrightarrow> infimum_closed (fp \<phi>)" by (metis fp_dual fp_sup_closed_cond1 iADDI_iMULT_dual2 inf_sup_closed_dc)
lemma fp_inf_closed_cond2: "iMULT\<^sup>b \<phi> \<and> CNTR \<phi> \<longrightarrow> infimum_closed (fp \<phi>)" by (metis EXPN_CNTR_dual2 fp_dual fp_sup_closed_cond2 iADDIa_iMULTb_dual2 inf_sup_closed_dc)
lemma fp_inf_closed_cond3: "MONO \<phi> \<and> EXPN \<phi> \<longrightarrow> infimum_closed (fp \<phi>)" by (metis EXPN_CNTR_dual1 MONO_dual fp_dual fp_sup_closed_cond3 inf_sup_closed_dc)

(**OTOH, the converse conjectures have (finite) countermodels. They need additional assumptions.*)
lemma "infimum_closed (fp \<phi>) \<longrightarrow> iMULT \<phi>" nitpick oops (*countermodel found: needs further assumptions*)
lemma "supremum_closed (fp \<phi>) \<longrightarrow> iADDI \<phi>" nitpick oops (*countermodel found: needs further assumptions*)
lemma fp_inf_closed_iMULT: "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi> \<Longrightarrow> infimum_closed (fp \<phi>) \<longrightarrow> iMULT \<phi>"
proof -
assume mono: "MONO \<phi>" and cntr: "CNTR \<phi>" and idem:"IDEM\<^sup>b \<phi>" {
  assume ic:"infimum_closed (fp \<phi>)" {
    fix S
    from ic have "\<forall>D. D \<preceq> (fp \<phi>) \<longrightarrow> (fp \<phi>)(\<^bold>\<And>D)" unfolding infimum_closed_def by simp
    hence "let D=\<lbrakk>\<phi> S\<rbrakk> in (\<forall>X. D X \<longrightarrow> (X \<approx> \<phi> X)) \<longrightarrow> \<^bold>\<And>D \<approx> \<phi> \<^bold>\<And>D" by (simp add: fixpoints_def setequ_ext subset_def) 
    moreover from idem have "(\<forall>X. \<lbrakk>\<phi> S\<rbrakk> X \<longrightarrow> (X \<approx> \<phi> X))" by (metis (mono_tags, lifting) CNTR_def IDEM_b_def cntr image_def setequ_char)
    ultimately have aux: "\<^bold>\<And>(\<lbrakk>\<phi> S\<rbrakk>) \<approx> \<phi>(\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>)" by meson
    from cntr have "\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<preceq> \<^bold>\<And>S" by (smt (verit, best) CNTR_def image_def infimum_def subset_def)
    hence "\<phi>(\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>) \<preceq> \<phi>(\<^bold>\<And>S)" using mono by (simp add: MONO_def) 
    from this aux have "\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<preceq> \<phi>(\<^bold>\<And>S)" by (simp add: setequ_ext)
  } hence "infimum_closed (fp \<phi>) \<longrightarrow> iMULT \<phi>" by (simp add: MONO_iMULTa iMULT_b_def iMULT_char mono)
} thus ?thesis by simp 
qed
lemma fp_sup_closed_iADDI: "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> IDEM\<^sup>a \<phi> \<Longrightarrow> supremum_closed (fp \<phi>) \<longrightarrow> iADDI \<phi>" by (metis EXPN_CNTR_dual1 IDEM_dual2 MONO_dual dual_invol fp_inf_closed_iMULT fp_inf_sup_closed_dual iADDI_iMULT_dual1)
(*
proof -
assume mono: "MONO \<phi>" and expn: "EXPN \<phi>" and idem:"IDEM\<^sup>a \<phi>" {
  assume sc:"supremum_closed (fp \<phi>)" {
    fix S
    from sc have "\<forall>D. D \<preceq> (fp \<phi>) \<longrightarrow> (fp \<phi>)(\<^bold>\<Or>D)" unfolding supremum_closed_def by simp
    hence "let D=\<lbrakk>\<phi> S\<rbrakk> in (\<forall>X. D X \<longrightarrow> (X \<approx> \<phi> X)) \<longrightarrow> \<^bold>\<Or>D \<approx> \<phi> \<^bold>\<Or>D" by (simp add: fixpoints_def setequ_ext subset_def)
    moreover have "(\<forall>X. \<lbrakk>\<phi> S\<rbrakk> X \<longrightarrow> (X \<approx> \<phi> X))" by (metis (mono_tags, lifting) EXPN_def IDEM_a_def expn idem image_def setequ_char)
    ultimately have aux: "\<^bold>\<Or>(\<lbrakk>\<phi> S\<rbrakk>) \<approx> \<phi>(\<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)" by meson
    have "\<^bold>\<Or>S \<preceq> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" by (metis EXPN_CNTR_dual1 EXPN_def IDEM_dual1 MONO_dual dual_invol expn fp_inf_closed_iMULT fp_inf_sup_closed_dual iADDI_def iADDI_iMULT_dual1 idem mono sc setequ_ext)
    hence "\<phi>(\<^bold>\<Or>S) \<preceq> \<phi>(\<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)" using mono by (simp add: MONO_def) 
    from this aux have "\<phi>(\<^bold>\<Or>S) \<preceq> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>" by (metis setequ_ext)
  } hence "supremum_closed (fp \<phi>) \<longrightarrow> iADDI \<phi>" by (simp add: MONO_ADDIb iADDI_a_def iADDI_char iADDIb_equ mono)
} thus ?thesis by simp
qed
*)

end