theory conditions_positive
  imports "../boolean_algebra/boolean_algebra_functional"
begin

(** We define and interrelate some useful axiomatic conditions on unary operations (operators) 
having a 'w-parametric type @{type "'w \<sigma> \<Rightarrow> 'w \<sigma>"}.
Boolean algebras extended with such operators give us different sorts of topological Boolean algebras.*)


(**Monotonicity (MONO).*)
definition MONO::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MONO")
  where "MONO \<phi> \<equiv> \<forall>A B. A \<preceq> B \<longrightarrow> \<phi> A \<preceq> \<phi> B"

named_theorems cond (*(*to group together axiomatic conditions*)*)
declare MONO_def[cond]

(**MONO is self-dual*)
lemma MONO_dual: "MONO \<phi> = MONO \<phi>\<^sup>d" by (smt (verit) BA_cp MONO_def dual_invol op_dual_def)


(**Expansive/extensive (EXPN) and its dual contractive (CNTR).*)
definition EXPN::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("EXPN")
  where "EXPN \<phi>  \<equiv> \<forall>A. A \<preceq> \<phi> A"
definition CNTR::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("CNTR")
  where "CNTR \<phi> \<equiv> \<forall>A. \<phi> A \<preceq> A"

declare EXPN_def[cond] CNTR_def[cond]

(**EXPN and CNTR are dual to each other *)
lemma EXPN_CNTR_dual1: "EXPN \<phi> = CNTR \<phi>\<^sup>d" unfolding cond by (metis BA_cp BA_dn op_dual_def setequ_ext)
lemma EXPN_CNTR_dual2: "CNTR \<phi> = EXPN \<phi>\<^sup>d" by (simp add: EXPN_CNTR_dual1 dual_invol)


(**Normality (NORM) and its dual (DNRM).*)
definition NORM::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("NORM")
  where "NORM \<phi>  \<equiv> (\<phi> \<^bold>\<bottom>) \<approx> \<^bold>\<bottom>"
definition DNRM::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("DNRM")
  where "DNRM \<phi> \<equiv> (\<phi> \<^bold>\<top>) \<approx> \<^bold>\<top>" 

declare NORM_def[cond] DNRM_def[cond]

(**NORM and DNRM are dual to each other *)
lemma NOR_dual1: "NORM \<phi> = DNRM \<phi>\<^sup>d" unfolding cond by (simp add: bottom_def compl_def op_dual_def setequ_def top_def)
lemma NOR_dual2: "DNRM \<phi> = NORM \<phi>\<^sup>d" by (simp add: NOR_dual1 dual_invol) 

(**EXPN (CNTR) entail DNRM (NORM).*)
lemma EXPN_impl_DNRM: "EXPN \<phi> \<longrightarrow> DNRM \<phi>" unfolding cond by (simp add: setequ_def subset_def top_def)
lemma CNTR_impl_NORM: "CNTR \<phi> \<longrightarrow> NORM \<phi>" by (simp add: EXPN_CNTR_dual2 EXPN_impl_DNRM NOR_dual1 dual_invol)


(**Idempotence (IDEM).*)
definition IDEM::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("IDEM") 
  where "IDEM \<phi>  \<equiv> \<forall>A. \<phi>(\<phi> A) \<approx> (\<phi> A)"
definition IDEM_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("IDEM\<^sup>a") 
  where "IDEM\<^sup>a \<phi> \<equiv> \<forall>A. \<phi>(\<phi> A) \<preceq> (\<phi> A)"
definition IDEM_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("IDEM\<^sup>b") 
  where "IDEM\<^sup>b \<phi> \<equiv> \<forall>A.  (\<phi> A) \<preceq> \<phi>(\<phi> A)"

declare IDEM_def[cond] IDEM_a_def[cond] IDEM_b_def[cond]

(**IDEM-a and IDEM-b are dual to each other *)
lemma IDEM_dual1: "IDEM\<^sup>a \<phi> = IDEM\<^sup>b \<phi>\<^sup>d" unfolding cond by (metis (mono_tags, opaque_lifting) BA_cp BA_dn op_dual_def setequ_ext)
lemma IDEM_dual2: "IDEM\<^sup>b \<phi> = IDEM\<^sup>a \<phi>\<^sup>d" by (simp add: IDEM_dual1 dual_invol)

lemma IDEM_char: "IDEM \<phi> = (IDEM\<^sup>a \<phi> \<and> IDEM\<^sup>b \<phi>)" unfolding cond setequ_char by blast
lemma IDEM_dual: "IDEM \<phi> = IDEM \<phi>\<^sup>d" using IDEM_char IDEM_dual1 IDEM_dual2 by blast


(**EXPN (CNTR) entail IDEM-b (IDEM-a).*)
lemma EXPN_impl_IDEM_b: "EXPN \<phi> \<longrightarrow> IDEM\<^sup>b \<phi>" by (simp add: EXPN_def IDEM_b_def)
lemma CNTR_impl_IDEM_a: "CNTR \<phi> \<longrightarrow> IDEM\<^sup>a \<phi>" by (simp add: CNTR_def IDEM_a_def)

(**Moreover, IDEM has some other interesting characterizations. For instance, *)
(**as having the property of collapsing the range and the set of fixed-points of an operator*)
lemma IDEM_range_fp_char: "IDEM \<phi> = (\<lbrakk>\<phi> _\<rbrakk> = fp \<phi>)" unfolding cond range_def fixpoints_def by (metis setequ_ext)
(**and via function composition*)
lemma IDEM_fun_comp_char: "IDEM \<phi> = (\<phi> = \<phi> \<circ> \<phi>)" unfolding cond fun_comp_def by (metis setequ_ext)

(**Distribution over joins or additivity (ADDI) and its dual...*)
definition ADDI::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ADDI")
  where "ADDI \<phi>   \<equiv> \<forall>A B. \<phi>(A \<^bold>\<or> B) \<approx> (\<phi> A) \<^bold>\<or> (\<phi> B)" 
definition ADDI_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ADDI\<^sup>a")
  where "ADDI\<^sup>a \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<or> B) \<preceq> (\<phi> A) \<^bold>\<or> (\<phi> B)"
definition ADDI_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ADDI\<^sup>b")
  where "ADDI\<^sup>b \<phi> \<equiv> \<forall>A B.  (\<phi> A) \<^bold>\<or> (\<phi> B) \<preceq> \<phi>(A \<^bold>\<or> B)" 

(**... distribution over meets or multiplicativity (MULT).*)
definition MULT::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MULT") 
  where "MULT \<phi>   \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<approx> (\<phi> A) \<^bold>\<and> (\<phi> B)" 
definition MULT_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MULT\<^sup>a")
  where "MULT\<^sup>a \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<preceq> (\<phi> A) \<^bold>\<and> (\<phi> B)" 
definition MULT_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MULT\<^sup>b")
  where "MULT\<^sup>b \<phi> \<equiv> \<forall>A B. (\<phi> A) \<^bold>\<and> (\<phi> B) \<preceq> \<phi>(A \<^bold>\<and> B)"

declare ADDI_def[cond] ADDI_a_def[cond] ADDI_b_def[cond]
        MULT_def[cond] MULT_a_def[cond] MULT_b_def[cond]

lemma ADDI_char: "ADDI \<phi> = (ADDI\<^sup>a \<phi> \<and> ADDI\<^sup>b \<phi>)" unfolding cond using setequ_char by blast
lemma MULT_char: "MULT \<phi> = (MULT\<^sup>a \<phi> \<and> MULT\<^sup>b \<phi>)" unfolding cond using setequ_char by blast

(**MONO, MULT-a and ADDI-b are equivalent.*)
lemma MONO_MULTa: "MULT\<^sup>a \<phi> = MONO \<phi>" unfolding cond by (metis L10 L3 L4 L5 L8 setequ_char setequ_ext)
lemma MONO_ADDIb: "ADDI\<^sup>b \<phi> = MONO \<phi>" unfolding cond by (metis (mono_tags, lifting) L7 L9 join_def setequ_ext subset_def)

(**Below we prove several duality relationships between ADDI(a/b) and MULT(a/b).*)

(**Duality between MULT-a and ADDI-b (an easy corollary from the self-duality of MONO).*)
lemma MULTa_ADDIb_dual1: "MULT\<^sup>a \<phi> = ADDI\<^sup>b \<phi>\<^sup>d" by (metis MONO_ADDIb MONO_MULTa MONO_dual)
lemma MULTa_ADDIb_dual2: "ADDI\<^sup>b \<phi> = MULT\<^sup>a \<phi>\<^sup>d" by (simp add: MULTa_ADDIb_dual1 dual_invol)
(**Duality between ADDI-a and MULT-b.*)
lemma ADDIa_MULTb_dual1: "ADDI\<^sup>a \<phi> = MULT\<^sup>b \<phi>\<^sup>d" unfolding cond op_dual_def by (metis BA_cp BA_deMorgan1 BA_dn setequ_ext)
lemma ADDIa_MULTb_dual2: "MULT\<^sup>b \<phi> = ADDI\<^sup>a \<phi>\<^sup>d" by (simp add: ADDIa_MULTb_dual1 dual_invol)
(**Duality between ADDI and MULT.*)
lemma ADDI_MULT_dual1: "ADDI \<phi> = MULT \<phi>\<^sup>d" using ADDI_char ADDIa_MULTb_dual1 MULT_char MULTa_ADDIb_dual2 by blast
lemma ADDI_MULT_dual2: "MULT \<phi> = ADDI \<phi>\<^sup>d" by (simp add: ADDI_MULT_dual1 dual_invol)


(**We verify properties regarding closure over meets/joins for fixed-points.*)

(**MULT implies meet-closedness of the set of fixed-points (the converse requires additional assumptions)*)
lemma MULT_meetclosed: "MULT \<phi> \<Longrightarrow> meet_closed (fp \<phi>)" by (simp add: MULT_def fixpoints_def meet_closed_def setequ_ext)
lemma "meet_closed (fp \<phi>) \<Longrightarrow> MULT \<phi>" nitpick oops (*countermodel found: needs further assumptions*)
lemma meetclosed_MULT: "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi> \<Longrightarrow> meet_closed (fp \<phi>) \<Longrightarrow> MULT \<phi>" by (smt (z3) CNTR_def IDEM_b_def MONO_MULTa MONO_def MULT_a_def MULT_def fixpoints_def meet_closed_def meet_def setequ_char setequ_ext subset_def)

(**ADDI implies join-closedness of the set of fixed-points (the converse requires additional assumptions)*)
lemma ADDI_joinclosed: "ADDI \<phi> \<Longrightarrow> join_closed (fp \<phi>)" by (simp add: ADDI_def fixpoints_def join_closed_def setequ_ext)
lemma "join_closed (fp \<phi>) \<Longrightarrow> ADDI \<phi>" nitpick oops (*countermodel found: needs further assumptions*)
lemma joinclosed_ADDI: "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> IDEM\<^sup>a \<phi> \<Longrightarrow> join_closed (fp \<phi>) \<Longrightarrow> ADDI \<phi>" by (smt (verit, ccfv_threshold) ADDI_MULT_dual1 BA_deMorgan2 EXPN_CNTR_dual1 IDEM_dual1 MONO_dual fp_dual join_closed_def meet_closed_def meetclosed_MULT sdfun_dcompl_def setequ_ext)

(**Assuming MONO, we have that EXPN (CNTR) implies meet-closed (join-closed) for the set of fixed-points.*)
lemma EXPN_meetclosed: "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> meet_closed (fp \<phi>)" by (smt (verit) EXPN_def MONO_MULTa MULT_a_def fixpoints_def meet_closed_def setequ_char setequ_ext)
lemma CNTR_joinclosed: "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> join_closed (fp \<phi>)" by (smt (verit, best) ADDI_b_def CNTR_def MONO_ADDIb fixpoints_def join_closed_def setequ_char setequ_ext)

(**Further assuming IDEM the above results can be stated to the whole range of an operator.*)
lemma "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow> meet_closed (\<lbrakk>\<phi> _\<rbrakk>)" by (simp add: EXPN_meetclosed IDEM_range_fp_char)
lemma "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow> join_closed (\<lbrakk>\<phi> _\<rbrakk>)" by (simp add: CNTR_joinclosed IDEM_range_fp_char) 

end