theory conditions_relativized
  imports conditions_negative
begin

(****************** Relativized order and equality relations ****************)
definition subset_in::\<open>'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> bool\<close> ("_\<preceq>\<^sub>__") 
  where \<open>A \<preceq>\<^sub>U B \<equiv> \<forall>x. U x \<longrightarrow> (A x \<longrightarrow> B x)\<close>
definition subset_out::\<open>'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> bool\<close> ("_\<preceq>\<^sup>__") 
  where \<open>A \<preceq>\<^sup>U B \<equiv> \<forall>x. \<not>U x \<longrightarrow> (A x \<longrightarrow> B x)\<close>

definition setequ_in::\<open>'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> bool\<close> ("_\<approx>\<^sub>__") 
  where \<open>A \<approx>\<^sub>U B \<equiv> \<forall>x. U x \<longrightarrow> (A x \<longleftrightarrow> B x)\<close>
definition setequ_out::\<open>'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> bool\<close> ("_\<approx>\<^sup>__") 
  where \<open>A \<approx>\<^sup>U B \<equiv> \<forall>x. \<not>U x \<longrightarrow> (A x \<longleftrightarrow> B x)\<close>

declare subset_in_def[order] subset_out_def[order] setequ_in_def[order] setequ_out_def[order]

lemma subset_in_out: "(let U=C in (A \<preceq>\<^sub>U B)) = (let U=\<^bold>\<midarrow>C in (A \<preceq>\<^sup>U B))" by (simp add: compl_def subset_in_def subset_out_def)
lemma setequ_in_out: "(let U=C in (A \<approx>\<^sub>U B)) = (let U=\<^bold>\<midarrow>C in (A \<approx>\<^sup>U B))" by (simp add: compl_def setequ_in_def setequ_out_def)

lemma subset_in_char: "(A \<preceq>\<^sub>U B) = (U \<^bold>\<and> A \<preceq> U \<^bold>\<and> B)" unfolding order conn by blast
lemma subset_out_char: "(A \<preceq>\<^sup>U B) = (U \<^bold>\<or> A \<preceq> U \<^bold>\<or> B)" unfolding order conn by blast
lemma setequ_in_char: "(A \<approx>\<^sub>U B) = (U \<^bold>\<and> A \<approx> U \<^bold>\<and> B)" unfolding order conn by blast
lemma setequ_out_char: "(A \<approx>\<^sup>U B) = (U \<^bold>\<or> A \<approx> U \<^bold>\<or> B)" unfolding order conn by blast

(**Relativization cannot be meaningfully applied to conditions (n)NORM or (n)DNRM.*)
lemma "NORM \<phi>  = (let U = \<^bold>\<top> in ((\<phi> \<^bold>\<bottom>) \<approx>\<^sub>U \<^bold>\<bottom>))" by (simp add: NORM_def setequ_def setequ_in_def top_def)
lemma "(let U = \<^bold>\<bottom> in ((\<phi> \<^bold>\<bottom>) \<approx>\<^sub>U \<^bold>\<bottom>))" by (simp add: bottom_def setequ_in_def)

(*Relativization ('in' resp. 'out') leaves (n)EXPN/(n)CNTR unchanged or trivializes them.*)
lemma "EXPN \<phi>  = (\<forall>A. A \<preceq>\<^sub>A \<phi> A)" by (simp add: EXPN_def subset_def subset_in_def)
lemma "CNTR \<phi>  = (\<forall>A. (\<phi> A) \<preceq>\<^sup>A A)" by (metis (mono_tags, lifting) CNTR_def subset_def subset_out_def)
lemma "\<forall>A. A \<preceq>\<^sup>A \<phi> A" by (simp add: subset_out_def)
lemma "\<forall>A. (\<phi> A) \<preceq>\<^sub>A A" by (simp add: subset_in_def)


(****************** Relativized ADDI variants ****************)

definition ADDIr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ADDIr")
  where "ADDIr \<phi>  \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in      (\<phi>(A \<^bold>\<or> B) \<approx>\<^sup>U (\<phi> A) \<^bold>\<or> (\<phi> B))"
definition ADDIr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ADDIr\<^sup>a")
  where "ADDIr\<^sup>a \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in      (\<phi>(A \<^bold>\<or> B) \<preceq>\<^sup>U (\<phi> A) \<^bold>\<or> (\<phi> B))" 
definition ADDIr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ADDIr\<^sup>b")
  where "ADDIr\<^sup>b \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in ((\<phi> A) \<^bold>\<or> (\<phi> B) \<preceq>\<^sup>U \<phi>(A \<^bold>\<or> B))"
 
declare ADDIr_def[cond] ADDIr_a_def[cond] ADDIr_b_def[cond]

lemma ADDIr_char: "ADDIr \<phi> = (ADDIr\<^sup>a \<phi> \<and> ADDIr\<^sup>b \<phi>)" unfolding cond by (meson setequ_char setequ_out_char subset_out_char)

lemma ADDIr_a_impl: "ADDI\<^sup>a \<phi> \<longrightarrow> ADDIr\<^sup>a \<phi>" by (simp add: ADDI_a_def ADDIr_a_def subset_def subset_out_def)
lemma ADDIr_a_equ:  "EXPN \<phi> \<Longrightarrow> ADDIr\<^sup>a \<phi> = ADDI\<^sup>a \<phi>" unfolding cond by (smt (verit, del_insts) join_def subset_def subset_out_def)
lemma ADDIr_a_equ':"nEXPN \<phi> \<Longrightarrow> ADDIr\<^sup>a \<phi> = ADDI\<^sup>a \<phi>" unfolding cond by (smt (verit, ccfv_threshold) compl_def subset_def subset_out_def)

lemma ADDIr_b_impl: "ADDI\<^sup>b \<phi> \<longrightarrow> ADDIr\<^sup>b \<phi>" by (simp add: ADDI_b_def ADDIr_b_def subset_def subset_out_def)
lemma "nEXPN \<phi> \<Longrightarrow> ADDIr\<^sup>b \<phi> \<longrightarrow> ADDI\<^sup>b \<phi>" nitpick oops
lemma ADDIr_b_equ: "EXPN \<phi> \<Longrightarrow> ADDIr\<^sup>b \<phi> = ADDI\<^sup>b \<phi>" unfolding cond by (smt (z3) subset_def subset_out_def)


(****************** Relativized MULT variants ****************)

definition MULTr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MULTr")
  where "MULTr \<phi>  \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in      (\<phi>(A \<^bold>\<and> B) \<approx>\<^sub>U (\<phi> A) \<^bold>\<and> (\<phi> B))"
definition MULTr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MULTr\<^sup>a")
  where "MULTr\<^sup>a \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in      (\<phi>(A \<^bold>\<and> B) \<preceq>\<^sub>U (\<phi> A) \<^bold>\<and> (\<phi> B))"
definition MULTr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MULTr\<^sup>b")
  where "MULTr\<^sup>b \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in ((\<phi> A) \<^bold>\<and> (\<phi> B) \<preceq>\<^sub>U \<phi>(A \<^bold>\<and> B))"

declare MULTr_def[cond] MULTr_a_def[cond] MULTr_b_def[cond]

lemma MULTr_char: "MULTr \<phi> = (MULTr\<^sup>a \<phi> \<and> MULTr\<^sup>b \<phi>)" unfolding cond by (meson setequ_char setequ_in_char subset_in_char)

lemma MULTr_a_impl: "MULT\<^sup>a \<phi> \<longrightarrow> MULTr\<^sup>a \<phi>" by (simp add: MULT_a_def MULTr_a_def subset_def subset_in_def)
lemma "nCNTR \<phi> \<Longrightarrow> MULTr\<^sup>a \<phi> \<longrightarrow> MULT\<^sup>a \<phi>" nitpick oops
lemma MULTr_a_equ: "CNTR \<phi> \<Longrightarrow> MULTr\<^sup>a \<phi> = MULT\<^sup>a \<phi>" unfolding cond by (smt (verit, del_insts) subset_def subset_in_def)

lemma MULTr_b_impl: "MULT\<^sup>b \<phi> \<longrightarrow> MULTr\<^sup>b \<phi>" by (simp add: MULT_b_def MULTr_b_def subset_def subset_in_def)
lemma "MULTr\<^sup>b \<phi> \<longrightarrow> MULT\<^sup>b \<phi>" nitpick oops
lemma MULTr_b_equ:  "CNTR \<phi> \<Longrightarrow> MULTr\<^sup>b \<phi> = MULT\<^sup>b \<phi>" unfolding cond by (smt (verit, del_insts) meet_def subset_def subset_in_def)
lemma MULTr_b_equ':"nCNTR \<phi> \<Longrightarrow> MULTr\<^sup>b \<phi> = MULT\<^sup>b \<phi>" unfolding cond by (smt (z3) compl_def subset_def subset_in_def)

(**** Weak variants of monotonicity ***)
definition MONOw1::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MONOw\<^sup>1") 
  where "MONOw\<^sup>1 \<phi> \<equiv> \<forall>A B. A \<preceq> B \<longrightarrow> (\<phi> A) \<preceq> B \<^bold>\<or> (\<phi> B)"
definition MONOw2::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MONOw\<^sup>2")
  where "MONOw\<^sup>2 \<phi> \<equiv> \<forall>A B. A \<preceq> B \<longrightarrow> A \<^bold>\<and> (\<phi> A) \<preceq> (\<phi> B)"

declare MONOw1_def[cond] MONOw2_def[cond]

lemma MONOw1_ADDIr_b: "MONOw\<^sup>1 \<phi> = ADDIr\<^sup>b \<phi>" proof -
  have l2r: "MONOw\<^sup>1 \<phi> \<longrightarrow> ADDIr\<^sup>b \<phi>"  unfolding cond subset_out_char by (metis (mono_tags, opaque_lifting) L7 join_def subset_def) 
  have r2l: "ADDIr\<^sup>b \<phi> \<longrightarrow> MONOw\<^sup>1 \<phi>" unfolding cond subset_out_char by (metis (full_types) L9 join_def setequ_ext subset_def)
  show ?thesis using l2r r2l by blast
qed
lemma MONOw2_MULTr_a: "MONOw\<^sup>2 \<phi> = MULTr\<^sup>a \<phi>" proof -
  have l2r: "MONOw\<^sup>2 \<phi> \<longrightarrow> MULTr\<^sup>a \<phi>" unfolding cond subset_in_char by (meson L4 L5 L8 L9)
  have r2l:"MULTr\<^sup>a \<phi> \<longrightarrow> MONOw\<^sup>2 \<phi>" unfolding cond subset_in_char by (metis BA_distr1 L2 L5 L6 L9 setequ_ext)
  show ?thesis using l2r r2l by blast
qed

lemma "MONO \<phi> \<longrightarrow> MONOw\<^sup>1 \<phi>" by (simp add: ADDIr_b_impl MONO_ADDIb MONOw1_ADDIr_b)
lemma "MONOw\<^sup>1 \<phi> \<longrightarrow> MONO \<phi>" nitpick oops
lemma "MONO \<phi> \<longrightarrow> MONOw\<^sup>2 \<phi>" by (simp add: MONO_MULTa MONOw2_MULTr_a MULTr_a_impl)
lemma "MONOw\<^sup>2 \<phi> \<longrightarrow> MONO \<phi>" nitpick oops

(****************** Relativized nADDI variants ****************)

definition nADDIr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nADDIr")
  where "nADDIr \<phi>  \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in      (\<phi>(A \<^bold>\<or> B) \<approx>\<^sup>U (\<phi> A) \<^bold>\<and> (\<phi> B))"
definition nADDIr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nADDIr\<^sup>a")
  where "nADDIr\<^sup>a \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in ((\<phi> A) \<^bold>\<and> (\<phi> B) \<preceq>\<^sup>U \<phi>(A \<^bold>\<or> B))" 
definition nADDIr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nADDIr\<^sup>b")
  where "nADDIr\<^sup>b \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in      (\<phi>(A \<^bold>\<or> B) \<preceq>\<^sup>U (\<phi> A) \<^bold>\<and> (\<phi> B))"
 
declare nADDIr_def[cond] nADDIr_a_def[cond] nADDIr_b_def[cond]

lemma nADDIr_char: "nADDIr \<phi> = (nADDIr\<^sup>a \<phi> \<and> nADDIr\<^sup>b \<phi>)" unfolding cond by (meson setequ_char setequ_out_char subset_out_char)

lemma nADDIr_a_impl: "nADDI\<^sup>a \<phi> \<longrightarrow> nADDIr\<^sup>a \<phi>" unfolding cond by (simp add: subset_def subset_out_def)
lemma "nADDIr\<^sup>a \<phi> \<longrightarrow> nADDI\<^sup>a \<phi>" nitpick oops
lemma nADDIr_a_equ:  "EXPN \<phi> \<Longrightarrow> nADDIr\<^sup>a \<phi> = nADDI\<^sup>a \<phi>" unfolding cond by (smt (z3) subset_def subset_out_def)
lemma nADDIr_a_equ':"nEXPN \<phi> \<Longrightarrow> nADDIr\<^sup>a \<phi> = nADDI\<^sup>a \<phi>" unfolding cond by (smt (z3) compl_def join_def meet_def subset_def subset_out_def)

lemma nADDIr_b_impl: "nADDI\<^sup>b \<phi> \<longrightarrow> nADDIr\<^sup>b \<phi>" by (simp add: nADDI_b_def nADDIr_b_def subset_def subset_out_def)
lemma "EXPN \<phi> \<Longrightarrow> nADDIr\<^sup>b \<phi> \<longrightarrow> nADDI\<^sup>b \<phi>" nitpick oops
lemma nADDIr_b_equ: "nEXPN \<phi> \<Longrightarrow> nADDIr\<^sup>b \<phi> = nADDI\<^sup>b \<phi>" unfolding cond by (smt (z3) compl_def subset_def subset_out_def)


(****************** Relativized nMULT variants ****************)

definition nMULTr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nMULTr")
  where "nMULTr \<phi>  \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in      (\<phi>(A \<^bold>\<and> B) \<approx>\<^sub>U (\<phi> A) \<^bold>\<or> (\<phi> B))"
definition nMULTr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nMULTr\<^sup>a")
  where "nMULTr\<^sup>a \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in ((\<phi> A) \<^bold>\<or> (\<phi> B) \<preceq>\<^sub>U \<phi>(A \<^bold>\<and> B))"
definition nMULTr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nMULTr\<^sup>b")
  where "nMULTr\<^sup>b \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in      (\<phi>(A \<^bold>\<and> B) \<preceq>\<^sub>U (\<phi> A) \<^bold>\<or> (\<phi> B))"

declare nMULTr_def[cond] nMULTr_a_def[cond] nMULTr_b_def[cond]

lemma nMULTr_char: "nMULTr \<phi> = (nMULTr\<^sup>a \<phi> \<and> nMULTr\<^sup>b \<phi>)" unfolding cond by (meson setequ_char setequ_in_char subset_in_char)

lemma nMULTr_a_impl: "nMULT\<^sup>a \<phi> \<longrightarrow> nMULTr\<^sup>a \<phi>" by (simp add: nMULT_a_def nMULTr_a_def subset_def subset_in_def)
lemma "CNTR \<phi> \<Longrightarrow> nMULTr\<^sup>a \<phi> \<longrightarrow> nMULT\<^sup>a \<phi>" nitpick oops
lemma nMULTr_a_equ: "nCNTR \<phi> \<Longrightarrow> nMULTr\<^sup>a \<phi> = nMULT\<^sup>a \<phi>" unfolding cond by (smt (z3) compl_def subset_def subset_in_def)

lemma nMULTr_b_impl: "nMULT\<^sup>b \<phi> \<longrightarrow> nMULTr\<^sup>b \<phi>" by (simp add: nMULT_b_def nMULTr_b_def subset_def subset_in_def)
lemma "nMULTr\<^sup>b \<phi> \<longrightarrow> nMULT\<^sup>b \<phi>" nitpick oops
lemma nMULTr_b_equ:  "CNTR \<phi> \<Longrightarrow> nMULTr\<^sup>b \<phi> = nMULT\<^sup>b \<phi>" unfolding cond by (smt (z3) compl_def join_def meet_def subset_def subset_in_def)
lemma nMULTr_b_equ':"nCNTR \<phi> \<Longrightarrow> nMULTr\<^sup>b \<phi> = nMULT\<^sup>b \<phi>" unfolding cond by (smt (z3) compl_def join_def meet_def subset_def subset_in_def)


(**** Weak variants of antitonicity ***)
definition ANTIw1::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ANTIw\<^sup>1") 
  where "ANTIw\<^sup>1 \<phi> \<equiv> \<forall>A B. A \<preceq> B \<longrightarrow> (\<phi> B) \<preceq> B \<^bold>\<or> (\<phi> A)"
definition ANTIw2::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ANTIw\<^sup>2")
  where "ANTIw\<^sup>2 \<phi> \<equiv> \<forall>A B. A \<preceq> B \<longrightarrow> A \<^bold>\<and> (\<phi> B) \<preceq> (\<phi> A)"

declare ANTIw1_def[cond] ANTIw2_def[cond]

lemma ANTIw1_nADDIr_b: "ANTIw\<^sup>1 \<phi> = nADDIr\<^sup>b \<phi>" proof -
  have l2r: "ANTIw\<^sup>1 \<phi> \<longrightarrow> nADDIr\<^sup>b \<phi>" unfolding cond subset_out_char by (smt (verit, ccfv_SIG) BA_distr2 L8 join_def setequ_ext subset_def)
  have r2l: "nADDIr\<^sup>b \<phi> \<longrightarrow> ANTIw\<^sup>1 \<phi>" unfolding cond subset_out_def by (metis (full_types) L9 join_def meet_def setequ_ext subset_def)
  show ?thesis using l2r r2l by blast
qed
lemma ANTIw2_nMULTr_a: "ANTIw\<^sup>2 \<phi> = nMULTr\<^sup>a \<phi>" proof -
  have l2r: "ANTIw\<^sup>2 \<phi> \<longrightarrow> nMULTr\<^sup>a \<phi>" unfolding cond subset_in_char by (metis BA_distr1 L3 L4 L5 L7 L8 setequ_ext)
  have r2l: "nMULTr\<^sup>a \<phi> \<longrightarrow> ANTIw\<^sup>2 \<phi>" unfolding cond subset_in_def by (metis (full_types) L10 join_def meet_def setequ_ext subset_def)
  show ?thesis using l2r r2l by blast
qed

lemma "ANTI \<phi> \<longrightarrow> ANTIw\<^sup>1 \<phi>" by (simp add: ANTI_nADDIb ANTIw1_nADDIr_b nADDIr_b_impl)
lemma "ANTIw\<^sup>1 \<phi> \<longrightarrow> ANTI \<phi>" nitpick oops
lemma "ANTI \<phi> \<longrightarrow> ANTIw\<^sup>2 \<phi>" by (simp add: ANTI_nMULTa ANTIw2_nMULTr_a nMULTr_a_impl)
lemma "ANTIw\<^sup>2 \<phi> \<longrightarrow> ANTI \<phi>" nitpick oops

(****************** Dual interrelations ****************)

lemma ADDIr_dual1: "ADDIr\<^sup>a \<phi> = MULTr\<^sup>b \<phi>\<^sup>d" unfolding cond subset_in_char subset_out_char by (smt (z3) BA_cp BA_deMorgan1 BA_dn op_dual_def setequ_ext)
lemma ADDIr_dual2: "ADDIr\<^sup>b \<phi> = MULTr\<^sup>a \<phi>\<^sup>d" unfolding cond subset_in_char subset_out_char by (smt (verit, ccfv_threshold) BA_cp BA_deMorgan1 BA_dn op_dual_def setequ_ext)
lemma ADDIr_dual:  "ADDIr \<phi> = MULTr \<phi>\<^sup>d" using ADDIr_char ADDIr_dual1 ADDIr_dual2 MULTr_char by blast

lemma nADDIr_dual1: "nADDIr\<^sup>a \<phi> = nMULTr\<^sup>b \<phi>\<^sup>d" unfolding cond subset_in_char subset_out_char by (smt (verit, del_insts) BA_cp BA_deMorgan1 BA_dn op_dual_def setequ_ext)
lemma nADDIr_dual2: "nADDIr\<^sup>b \<phi> = nMULTr\<^sup>a \<phi>\<^sup>d" by (smt (z3) BA_deMorgan1 BA_dn compl_def nADDIr_b_def nMULTr_a_def op_dual_def setequ_ext subset_in_def subset_out_def)
lemma nADDIr_dual: "nADDIr \<phi> = nMULTr \<phi>\<^sup>d" using nADDIr_char nADDIr_dual1 nADDIr_dual2 nMULTr_char by blast


(****************** Complement interrelations ****************)

lemma ADDIr_a_cmpl: "ADDIr\<^sup>a \<phi> = nADDIr\<^sup>a \<phi>\<^sup>c" unfolding cond by (smt (verit, del_insts) BA_deMorgan1 compl_def setequ_ext subset_out_def svfun_compl_def)
lemma ADDIr_b_cmpl: "ADDIr\<^sup>b \<phi> = nADDIr\<^sup>b \<phi>\<^sup>c" unfolding cond by (smt (verit, del_insts) BA_deMorgan1 compl_def setequ_ext subset_out_def svfun_compl_def)
lemma ADDIr_cmpl: "ADDIr \<phi> = nADDIr \<phi>\<^sup>c" by (simp add: ADDIr_a_cmpl ADDIr_b_cmpl ADDIr_char nADDIr_char)
lemma MULTr_a_cmpl: "MULTr\<^sup>a \<phi> = nMULTr\<^sup>a \<phi>\<^sup>c" unfolding cond by (smt (verit, del_insts) BA_deMorgan2 compl_def setequ_ext subset_in_def svfun_compl_def)
lemma MULTr_b_cmpl: "MULTr\<^sup>b \<phi> = nMULTr\<^sup>b \<phi>\<^sup>c" unfolding cond by (smt (verit, ccfv_threshold) BA_deMorgan2 compl_def setequ_ext subset_in_def svfun_compl_def)
lemma MULTr_cmpl: "MULTr \<phi> = nMULTr \<phi>\<^sup>c" by (simp add: MULTr_a_cmpl MULTr_b_cmpl MULTr_char nMULTr_char)


(****************** Fixed-point interrelations ****************)

lemma EXPN_fp:  "EXPN \<phi> = EXPN \<phi>\<^sup>f\<^sup>p" by (simp add: EXPN_def dimpl_def op_fixpoint_def subset_def)
lemma EXPN_fpc: "EXPN \<phi> = nEXPN \<phi>\<^sup>f\<^sup>p\<^sup>c" using EXPN_fp nEXPN_CNTR_compl by blast
lemma CNTR_fp:  "CNTR \<phi> = nCNTR \<phi>\<^sup>f\<^sup>p" by (metis EXPN_CNTR_dual1 EXPN_fp dual_compl_char2 dual_invol nCNTR_EXPN_compl ofp_comm_dc1 sfun_compl_invol)
lemma CNTR_fpc: "CNTR \<phi> = CNTR \<phi>\<^sup>f\<^sup>p\<^sup>c" by (metis CNTR_fp nCNTR_EXPN_compl ofp_comm_compl ofp_invol)

lemma nNORM_fp: "NORM \<phi> = nNORM \<phi>\<^sup>f\<^sup>p" by (metis NORM_def fixpoints_def fp_rel nNORM_def)
lemma NORM_fpc: "NORM \<phi> = NORM \<phi>\<^sup>f\<^sup>p\<^sup>c" by (simp add: NORM_def bottom_def ofp_fixpoint_compl_def sdiff_def)
lemma DNRM_fp:  "DNRM \<phi> = DNRM \<phi>\<^sup>f\<^sup>p" by (simp add: DNRM_def dimpl_def op_fixpoint_def top_def)
lemma DNRM_fpc: "DNRM \<phi> = nDNRM \<phi>\<^sup>f\<^sup>p\<^sup>c" using DNRM_fp nDNRM_DNRM_compl by blast

lemma ADDIr_a_fpc: "ADDIr\<^sup>a \<phi> = ADDIr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>c" unfolding cond subset_out_def by (simp add: join_def ofp_fixpoint_compl_def sdiff_def)
lemma ADDIr_a_fp: "ADDIr\<^sup>a \<phi> = nADDIr\<^sup>a \<phi>\<^sup>f\<^sup>p" by (metis ADDIr_a_cmpl ADDIr_a_fpc sfun_compl_invol)
lemma ADDIr_b_fpc: "ADDIr\<^sup>b \<phi> = ADDIr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>c" unfolding cond subset_out_def by (simp add: join_def ofp_fixpoint_compl_def sdiff_def)
lemma ADDIr_b_fp: "ADDIr\<^sup>b \<phi> = nADDIr\<^sup>b \<phi>\<^sup>f\<^sup>p" by (metis ADDIr_b_cmpl ADDIr_b_fpc sfun_compl_invol)

lemma MULTr_a_fp: "MULTr\<^sup>a \<phi> = MULTr\<^sup>a \<phi>\<^sup>f\<^sup>p" unfolding cond subset_in_def by (simp add: dimpl_def meet_def op_fixpoint_def)
lemma MULTr_a_fpc: "MULTr\<^sup>a \<phi> = nMULTr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>c" using MULTr_a_cmpl MULTr_a_fp by blast
lemma MULTr_b_fp: "MULTr\<^sup>b \<phi> = MULTr\<^sup>b \<phi>\<^sup>f\<^sup>p" unfolding cond subset_in_def by (simp add: dimpl_def meet_def op_fixpoint_def)
lemma MULTr_b_fpc: "MULTr\<^sup>b \<phi> = nMULTr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>c" using MULTr_b_cmpl MULTr_b_fp by blast


(****************** Relativized IDEM variants ****************)

definition IDEMr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("IDEMr\<^sup>a")
  where "IDEMr\<^sup>a \<phi> \<equiv> \<forall>A. \<phi>(A \<^bold>\<or> \<phi> A) \<preceq>\<^sup>A (\<phi> A)"
definition IDEMr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("IDEMr\<^sup>b") 
  where "IDEMr\<^sup>b \<phi> \<equiv> \<forall>A. (\<phi> A) \<preceq>\<^sub>A \<phi>(A \<^bold>\<and> \<phi> A)"
declare IDEMr_a_def[cond] IDEMr_b_def[cond]

(****************** Relativized nIDEM variants ****************)
definition nIDEMr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nIDEMr\<^sup>a") 
  where "nIDEMr\<^sup>a \<phi> \<equiv> \<forall>A. (\<phi> A) \<preceq>\<^sup>A \<phi>(A \<^bold>\<or> \<^bold>\<midarrow>(\<phi> A))"
definition nIDEMr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nIDEMr\<^sup>b") 
  where "nIDEMr\<^sup>b \<phi> \<equiv> \<forall>A. \<phi>(A \<^bold>\<and> \<^bold>\<midarrow>(\<phi> A)) \<preceq>\<^sub>A (\<phi> A)"

declare nIDEMr_a_def[cond] nIDEMr_b_def[cond]

lemma IDEMr_dual: "IDEMr\<^sup>a \<phi> = IDEMr\<^sup>b \<phi>\<^sup>d" unfolding cond subset_in_def subset_out_def op_dual_def by (metis (mono_tags, opaque_lifting) BA_dn compl_def diff_char1 diff_char2 impl_char setequ_ext)
lemma IDEMr_a_cmpl: "IDEMr\<^sup>a \<phi> = nIDEMr\<^sup>a \<phi>\<^sup>c" unfolding cond subset_in_def subset_out_def by (metis compl_def sfun_compl_invol svfun_compl_def)
lemma IDEMr_b_cmpl: "IDEMr\<^sup>b \<phi> = nIDEMr\<^sup>b \<phi>\<^sup>c" unfolding cond subset_in_def subset_out_def by (metis compl_def sfun_compl_invol svfun_compl_def)
lemma nIDEMr_dual: "nIDEMr\<^sup>a \<phi> = nIDEMr\<^sup>b \<phi>\<^sup>d" by (metis IDEMr_dual IDEMr_a_cmpl IDEMr_b_cmpl dual_compl_char1 dual_compl_char2 sfun_compl_invol)




lemma IDEMr_a_fp: "IDEMr\<^sup>a \<phi> = nIDEMr\<^sup>a \<phi>\<^sup>f\<^sup>p" proof -
  have l2r: "IDEMr\<^sup>a \<phi> \<longrightarrow> nIDEMr\<^sup>a \<phi>\<^sup>f\<^sup>p" 
    unfolding cond subset_out_char op_fixpoint_def conn order apply simp (*by metis*) sorry (*fix*)
  have r2l: "nIDEMr\<^sup>a \<phi>\<^sup>f\<^sup>p \<longrightarrow> IDEMr\<^sup>a \<phi>" 
    unfolding cond subset_out_def op_fixpoint_def conn order apply simp (*by metis*) sorry (*fix*) 
  from l2r r2l show ?thesis by blast
qed
lemma IDEMr_a_fpc: "IDEMr\<^sup>a \<phi> = IDEMr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>c" using IDEMr_a_fp by (smt (verit, del_insts) IDEMr_a_def compl_def nIDEMr_a_def subset_out_def svfun_compl_def)

lemma IDEMr_b_fp: "IDEMr\<^sup>b \<phi> = IDEMr\<^sup>b \<phi>\<^sup>f\<^sup>p" proof -
  have l2r: "IDEMr\<^sup>b \<phi> \<longrightarrow> IDEMr\<^sup>b \<phi>\<^sup>f\<^sup>p" 
    unfolding cond subset_in_def op_fixpoint_def conn order apply simp (*by metis*) sorry (*fix*)
  have r2l: "IDEMr\<^sup>b \<phi>\<^sup>f\<^sup>p \<longrightarrow> IDEMr\<^sup>b \<phi>" 
    unfolding cond subset_in_def op_fixpoint_def conn order apply simp (*by metis*) sorry (*fix*)
  from l2r r2l show ?thesis by blast
qed
lemma IDEMr_b_fpc: "IDEMr\<^sup>b \<phi> = nIDEMr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>c" using IDEMr_b_fp  sorry (* TODO*)

end