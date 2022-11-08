theory conditions_fixedpoint
  imports conditions_complement
begin

(**In the world of fixed-points EXPN and CNTR play an essential role: *)
lemma EXPN_fp:  "EXPN \<phi> = EXPN \<phi>\<^sup>f\<^sup>p" by (simp add: EXPN_def dimpl_def op_fixpoint_def subset_def)
lemma EXPN_fpc: "EXPN \<phi> = nEXPN \<phi>\<^sup>f\<^sup>p\<^sup>c" using EXPN_fp nEXPN_CNTR_compl by blast
lemma CNTR_fp:  "CNTR \<phi> = nCNTR \<phi>\<^sup>f\<^sup>p" by (metis EXPN_CNTR_dual1 EXPN_fp dual_compl_char2 dual_invol nCNTR_EXPN_compl ofp_comm_dc1 sfun_compl_invol)
lemma CNTR_fpc: "CNTR \<phi> = CNTR \<phi>\<^sup>f\<^sup>p\<^sup>c" by (metis CNTR_fp nCNTR_EXPN_compl ofp_comm_compl ofp_invol)

definition subset_in::\<open>'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> bool\<close> ("_\<preceq>\<^sub>__") 
  where \<open>A \<preceq>\<^sub>U B \<equiv> \<forall>x. U x \<longrightarrow> (A x \<longrightarrow> B x)\<close>
definition subset_out::\<open>'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> bool\<close> ("_\<preceq>\<^sup>__") 
  where \<open>A \<preceq>\<^sup>U B \<equiv> \<forall>x. \<not>U x \<longrightarrow> (A x \<longrightarrow> B x)\<close>

definition setequ_in::\<open>'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> bool\<close> ("_\<approx>\<^sub>__") 
  where \<open>A \<approx>\<^sub>U B \<equiv> \<forall>x. U x \<longrightarrow> (A x \<longleftrightarrow> B x)\<close>
definition setequ_out::\<open>'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> bool\<close> ("_\<approx>\<^sup>__") 
  where \<open>A \<approx>\<^sup>U B \<equiv> \<forall>x. \<not>U x \<longrightarrow> (A x \<longleftrightarrow> B x)\<close>

declare subset_in_def[order] subset_out_def[order] setequ_in_def[order] setequ_out_def[order]

lemma subset_in_char: "(A \<preceq>\<^sub>U B) = (U \<^bold>\<and> A \<preceq> U \<^bold>\<and> B)" unfolding order conn by blast
lemma subset_out_char: "(A \<preceq>\<^sup>U B) = (U \<^bold>\<or> A \<preceq> U \<^bold>\<or> B)" unfolding order conn by blast
lemma setequ_in_char: "(A \<approx>\<^sub>U B) = (U \<^bold>\<and> A \<approx> U \<^bold>\<and> B)" unfolding order conn by blast
lemma setequ_out_char: "(A \<approx>\<^sup>U B) = (U \<^bold>\<or> A \<approx> U \<^bold>\<or> B)" unfolding order conn by blast

definition ADDIr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ADDIr")
  where "ADDIr \<phi>  \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in ( \<phi>(A \<^bold>\<or> B) \<approx>\<^sup>U (\<phi> A) \<^bold>\<or> (\<phi> B) )"
definition ADDIr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ADDIr\<^sup>a")
  where "ADDIr\<^sup>a \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in ( \<phi>(A \<^bold>\<or> B) \<preceq>\<^sup>U (\<phi> A) \<^bold>\<or> (\<phi> B) )" 
definition ADDIr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("ADDIr\<^sup>b")
  where "ADDIr\<^sup>b \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in ( (\<phi> A) \<^bold>\<or> (\<phi> B) \<preceq>\<^sup>U \<phi>(A \<^bold>\<or> B) )"
 
declare ADDIr_def[cond] ADDIr_a_def[cond] ADDIr_b_def[cond]

lemma ADDIr_char: "ADDIr \<phi> = (ADDIr\<^sup>a \<phi> \<and> ADDIr\<^sup>b \<phi>)" unfolding cond by (meson setequ_char setequ_out_char subset_out_char)

lemma ADDIr_a_rel: "ADDI\<^sup>a \<phi> \<longrightarrow> ADDIr\<^sup>a \<phi>" by (simp add: ADDI_a_def ADDIr_a_def subset_def subset_out_def)
lemma "ADDIr\<^sup>a \<phi> \<longrightarrow> ADDI\<^sup>a \<phi>" nitpick oops
lemma ADDIr_a_rel': "EXPN \<phi> \<Longrightarrow> ADDIr\<^sup>a \<phi> = ADDI\<^sup>a \<phi>" unfolding cond by (smt (verit, del_insts) join_def subset_def subset_out_def)

lemma ADDIr_b_rel: "ADDI\<^sup>b \<phi> \<longrightarrow> ADDIr\<^sup>b \<phi>" by (simp add: ADDI_b_def ADDIr_b_def subset_def subset_out_def)
lemma "ADDIr\<^sup>b \<phi> \<longrightarrow> ADDI\<^sup>b \<phi>" nitpick oops
lemma ADDIr_b_rel': "EXPN \<phi> \<Longrightarrow> ADDIr\<^sup>b \<phi> = ADDI\<^sup>b \<phi>" unfolding cond by (smt (z3) subset_def subset_out_def)


definition MULTr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MULTr")
  where "MULTr \<phi>  \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in ( \<phi>(A \<^bold>\<and> B) \<approx>\<^sub>U (\<phi> A) \<^bold>\<and> (\<phi> B))"
definition MULTr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MULTr\<^sup>a")
  where "MULTr\<^sup>a \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in ( \<phi>(A \<^bold>\<and> B) \<preceq>\<^sub>U (\<phi> A) \<^bold>\<and> (\<phi> B))"
definition MULTr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("MULTr\<^sup>b")
  where "MULTr\<^sup>b \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in ( (\<phi> A) \<^bold>\<and> (\<phi> B) \<preceq>\<^sub>U \<phi>(A \<^bold>\<and> B))"

declare MULTr_def[cond] MULTr_a_def[cond] MULTr_b_def[cond]

lemma MULTr_char: "MULTr \<phi> = (MULTr\<^sup>a \<phi> \<and> MULTr\<^sup>b \<phi>)" unfolding cond by (meson setequ_char setequ_in_char subset_in_char)

lemma MULTr_a_rel: "MULT\<^sup>a \<phi> \<longrightarrow> MULTr\<^sup>a \<phi>" by (simp add: MULT_a_def MULTr_a_def subset_def subset_in_def)
lemma "MULTr\<^sup>a \<phi> \<longrightarrow> MULT\<^sup>a \<phi>" nitpick oops
lemma MULTr_a_rel': "CNTR \<phi> \<Longrightarrow> MULTr\<^sup>a \<phi> = MULT\<^sup>a \<phi>" unfolding cond by (smt (verit, del_insts) subset_def subset_in_def)

lemma MULTr_b_rel: "MULT\<^sup>b \<phi> \<longrightarrow> MULTr\<^sup>b \<phi>" by (simp add: MULT_b_def MULTr_b_def subset_def subset_in_def)
lemma "MULTr\<^sup>b \<phi> \<longrightarrow> MULT\<^sup>b \<phi>" nitpick oops
lemma MULTr_b_rel': "CNTR \<phi> \<Longrightarrow> MULTr\<^sup>b \<phi> = MULT\<^sup>b \<phi>" unfolding cond by (smt (verit, del_insts) meet_def subset_def subset_in_def)


definition nADDIr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nADDIr")
  where "nADDIr \<phi>  \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in ( \<phi>(A \<^bold>\<or> B) \<approx>\<^sup>U (\<phi> A) \<^bold>\<and> (\<phi> B) )"
definition nADDIr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nADDIr\<^sup>a")
  where "nADDIr\<^sup>a \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in ( (\<phi> A) \<^bold>\<and> (\<phi> B) \<preceq>\<^sup>U \<phi>(A \<^bold>\<or> B) )"
definition nADDIr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nADDIr\<^sup>b")
  where "nADDIr\<^sup>b \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<or> B) in ( \<phi>(A \<^bold>\<or> B) \<preceq>\<^sup>U (\<phi> A) \<^bold>\<and> (\<phi> B) )" 
 
declare nADDIr_def[cond] nADDIr_a_def[cond] nADDIr_b_def[cond]

lemma nADDIr_char: "nADDIr \<phi> = (nADDIr\<^sup>a \<phi> \<and> nADDIr\<^sup>b \<phi>)" unfolding cond by (meson setequ_char setequ_out_char subset_out_char)

lemma nADDIr_a_rel: "nADDI\<^sup>a \<phi> \<longrightarrow> nADDIr\<^sup>a \<phi>" by (simp add: nADDI_a_def nADDIr_a_def subset_def subset_out_def)
lemma "nADDIr\<^sup>a \<phi> \<longrightarrow> nADDI\<^sup>a \<phi>" nitpick oops
lemma nADDIr_a_rel': "nEXPN \<phi> \<Longrightarrow> nADDIr\<^sup>a \<phi> = nADDI\<^sup>a \<phi>" unfolding cond by (smt (z3) compl_def join_def meet_def subset_def subset_out_def)
lemma "EXPN \<phi> \<Longrightarrow> nADDIr\<^sup>a \<phi> = nADDI\<^sup>a \<phi>" unfolding cond by (smt (z3) compl_def join_def meet_def subset_def subset_out_def)

lemma nADDIr_b_rel: "nADDI\<^sup>b \<phi> \<longrightarrow> nADDIr\<^sup>b \<phi>" by (simp add: nADDI_b_def nADDIr_b_def subset_def subset_out_def)
lemma "nADDIr\<^sup>b \<phi> \<longrightarrow> nADDI\<^sup>b \<phi>" nitpick oops
lemma nADDIr_b_rel': "nEXPN \<phi> \<Longrightarrow> nADDIr\<^sup>b \<phi> = nADDI\<^sup>b \<phi>" unfolding cond by (smt (verit, del_insts) compl_def subset_def subset_out_def)


definition nMULTr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nMULTr")
  where "nMULTr \<phi>  \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in ( \<phi>(A \<^bold>\<and> B) \<approx>\<^sub>U (\<phi> A) \<^bold>\<or> (\<phi> B))"
definition nMULTr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nMULTr\<^sup>a")
  where "nMULTr\<^sup>a \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in ( (\<phi> A) \<^bold>\<or> (\<phi> B) \<preceq>\<^sub>U \<phi>(A \<^bold>\<and> B))"
definition nMULTr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nMULTr\<^sup>b")
  where "nMULTr\<^sup>b \<phi> \<equiv> \<forall>A B. let U = (A \<^bold>\<and> B) in ( \<phi>(A \<^bold>\<and> B) \<preceq>\<^sub>U (\<phi> A) \<^bold>\<or> (\<phi> B))"

declare nMULTr_def[cond] nMULTr_a_def[cond] nMULTr_b_def[cond]

lemma nMULTr_char: "nMULTr \<phi> = (nMULTr\<^sup>a \<phi> \<and> nMULTr\<^sup>b \<phi>)" unfolding cond by (meson setequ_char setequ_in_char subset_in_char)

lemma nMULTr_a_rel: "nMULT\<^sup>a \<phi> \<longrightarrow> nMULTr\<^sup>a \<phi>" by (simp add: nMULT_a_def nMULTr_a_def subset_def subset_in_def)
lemma "nMULTr\<^sup>a \<phi> \<longrightarrow> nMULT\<^sup>a \<phi>" nitpick oops
lemma nMULTr_a_rel': "nCNTR \<phi> \<Longrightarrow> nMULTr\<^sup>a \<phi> = nMULT\<^sup>a \<phi>" unfolding cond by (smt (z3) compl_def subset_def subset_in_def)

lemma nMULTr_b_rel: "nMULT\<^sup>b \<phi> \<longrightarrow> nMULTr\<^sup>b \<phi>" by (simp add: nMULT_b_def nMULTr_b_def subset_def subset_in_def)
lemma "nMULTr\<^sup>b \<phi> \<longrightarrow> nMULT\<^sup>b \<phi>" nitpick oops
lemma nMULTr_b_rel': "nCNTR \<phi> \<Longrightarrow> nMULTr\<^sup>b \<phi> = nMULT\<^sup>b \<phi>" unfolding cond by (smt (z3) compl_def join_def meet_def subset_def subset_in_def)
lemma "CNTR \<phi> \<Longrightarrow> nMULTr\<^sup>b \<phi> = nMULT\<^sup>b \<phi>" unfolding cond by (smt (verit, del_insts) subset_def subset_in_def)


lemma fp_nADDI_nMULT_dual1: "nADDIr\<^sup>a \<phi> = nMULTr\<^sup>b \<phi>\<^sup>d" unfolding cond subset_in_char subset_out_char by (smt (verit, del_insts) BA_cp BA_deMorgan1 BA_dn op_dual_def setequ_ext)
lemma fp_nADDI_nMULT_dual2: "nADDIr\<^sup>b \<phi> = nMULTr\<^sup>a \<phi>\<^sup>d" by (smt (z3) BA_deMorgan1 BA_dn compl_def nADDIr_b_def nMULTr_a_def op_dual_def setequ_ext subset_in_def subset_out_def)
lemma fp_nADDI_nMULT_dual: "nADDIr \<phi> = nMULTr \<phi>\<^sup>d" using fp_nADDI_nMULT_dual1 fp_nADDI_nMULT_dual2 nADDIr_char nMULTr_char by blast

(*Assuming EXPN, nADDIr is the 'fixedpoint condition' for ADDI*)
lemma ADDIa_fp1: "ADDI\<^sup>a \<phi> \<longrightarrow> nADDIr\<^sup>a \<phi>\<^sup>f\<^sup>p" unfolding cond subset_in_char subset_out_char by (smt (verit, ccfv_SIG) dimpl_def join_def meet_def op_fixpoint_def subset_def)
lemma ADDIa_fp2: "(EXPN \<phi> \<or> nEXPN \<phi>) \<longrightarrow> (nADDIr\<^sup>a \<phi> \<longrightarrow> ADDI\<^sup>a \<phi>\<^sup>f\<^sup>p)" unfolding cond subset_in_char subset_out_char by (smt (verit, ccfv_threshold) compl_def dimpl_def join_def meet_def op_fixpoint_def subset_def)
lemma ADDIa_fp: "EXPN \<phi> \<longrightarrow> (ADDI\<^sup>a \<phi> = nADDIr\<^sup>a \<phi>\<^sup>f\<^sup>p)" by (metis ADDIa_fp1 ADDIa_fp2 EXPN_fp ofp_invol)
lemma ADDIb_fp1: "ADDI\<^sup>b \<phi> \<longrightarrow> nADDIr\<^sup>b \<phi>\<^sup>f\<^sup>p" unfolding cond subset_in_char subset_out_char by (smt (verit, ccfv_SIG) dimpl_def join_def meet_def op_fixpoint_def subset_def)
lemma ADDIb_fp2: "EXPN \<phi> \<longrightarrow> (nADDIr\<^sup>b \<phi> \<longrightarrow> ADDI\<^sup>b \<phi>\<^sup>f\<^sup>p)" unfolding cond subset_in_char subset_out_char by (smt (verit, ccfv_threshold) dimpl_def join_def meet_def op_fixpoint_def subset_def)
lemma ADDIb_fp: "EXPN \<phi> \<longrightarrow> (ADDI\<^sup>b \<phi> = nADDIr\<^sup>b \<phi>\<^sup>f\<^sup>p)" by (metis ADDIb_fp1 ADDIb_fp2 EXPN_fp ofp_invol)
lemma ADDI_fp: "EXPN \<phi> \<longrightarrow> (ADDI \<phi> = nADDIr \<phi>\<^sup>f\<^sup>p)" by (simp add: ADDI_char ADDIa_fp ADDIb_fp nADDIr_char)

(*Assuming EXPN, ADDIr is the 'fixedpoint-complement condition' for ADDI*)
lemma ADDIa_fpc1: "ADDI\<^sup>a \<phi> \<longrightarrow> ADDIr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>c" by (simp add: ADDI_a_def ADDIr_a_def join_def ofp_fixpoint_compl_def sdiff_def subset_def subset_out_def)
lemma ADDIa_fpc2: "(EXPN \<phi> \<or> nEXPN \<phi>) \<longrightarrow> (ADDIr\<^sup>a \<phi> \<longrightarrow> ADDI\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>c)" by (smt (z3) ADDI_a_def ADDIr_a_def EXPN_def EXPN_fp join_def nEXPN_CNTR_compl ofp_comm_compl ofp_fixpoint_compl_def sdiff_def sfun_compl_invol subset_def subset_out_def)
lemma ADDIa_fpc: "EXPN \<phi> \<longrightarrow> (ADDI\<^sup>a \<phi> = ADDIr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>c)" by (smt (z3) ADDI_a_def ADDIr_a_def EXPN_def join_def ofp_fixpoint_compl_def sdiff_def subset_def subset_out_def)
lemma ADDIb_fpc1: "ADDI\<^sup>b \<phi> \<longrightarrow> ADDIr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>c" by (smt (z3) ADDIr_b_def compl_def join_def meet_def ADDIb_fp1 nADDIr_b_def subset_out_def svfun_compl_def)
lemma ADDIb_fpc2: "nEXPN \<phi> \<longrightarrow> (ADDIr\<^sup>b \<phi> \<longrightarrow> ADDI\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>c)" by (smt (verit, del_insts) ADDIr_b_def EXPN_fpc compl_def join_def meet_def ADDIb_fp nADDIr_b_def ofp_comm_compl ofp_invol sfun_compl_invol subset_out_def svfun_compl_def)
lemma ADDIb_fpc: "EXPN \<phi> \<longrightarrow> (ADDI\<^sup>b \<phi> = ADDIr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>c)" by (smt (z3) ADDIr_b_def compl_def join_def meet_def ADDIb_fp nADDIr_b_def subset_out_def svfun_compl_def)
lemma ADDI_fpc: "EXPN \<phi> \<longrightarrow> (ADDI \<phi> = ADDIr \<phi>\<^sup>f\<^sup>p\<^sup>c)" by (simp add: ADDI_char ADDIa_fpc ADDIb_fpc ADDIr_char)

(*Assuming CNTR, MULTr is the 'fixedpoint condition' for MULT*)
lemma MULTa_fp1: "MULT\<^sup>a \<phi> \<longrightarrow> MULTr\<^sup>a \<phi>\<^sup>f\<^sup>p" by (smt (z3) MULT_a_def MULTr_a_def dimpl_def meet_def op_fixpoint_def subset_def subset_in_char)
lemma MULTa_fp2: "nCNTR \<phi> \<longrightarrow> (MULTr\<^sup>a \<phi> \<longrightarrow> MULT\<^sup>a \<phi>\<^sup>f\<^sup>p)" unfolding cond subset_in_char subset_out_char by (smt (verit, ccfv_threshold) op_fixpoint_def compl_def dimpl_def meet_def subset_def)
lemma MULTa_fp: "CNTR \<phi> \<longrightarrow> (MULT\<^sup>a \<phi> = MULTr\<^sup>a \<phi>\<^sup>f\<^sup>p)" by (metis CNTR_fp MULTa_fp1 MULTa_fp2 ofp_invol)
lemma MULTb_fp1: "MULT\<^sup>b \<phi> \<longrightarrow> MULTr\<^sup>b \<phi>\<^sup>f\<^sup>p" by (simp add: MULT_b_def MULTr_b_def dimpl_def meet_def op_fixpoint_def subset_def subset_in_char)
lemma MULTb_fp2: "(CNTR \<phi> \<or> nCNTR \<phi>) \<longrightarrow> (MULTr\<^sup>b \<phi> \<longrightarrow> MULT\<^sup>b \<phi>\<^sup>f\<^sup>p)" unfolding cond subset_in_char subset_out_char op_fixpoint_def by (smt (z3) compl_def dimpl_def meet_def op_fixpoint_def subset_def)
lemma MULTb_fp: "CNTR \<phi> \<longrightarrow> (MULT\<^sup>b \<phi> = MULTr\<^sup>b \<phi>\<^sup>f\<^sup>p)" by (metis CNTR_fp MULTb_fp1 MULTb_fp2 ofp_invol)
lemma MULT_fp: "CNTR \<phi> \<longrightarrow> (MULT \<phi> = MULTr \<phi>\<^sup>f\<^sup>p)" by (simp add: MULT_char MULTa_fp MULTb_fp MULTr_char)

(*Assuming CNTR, nMULTr is the 'fixedpoint-complement condition' for MULT*)
lemma MULTa_fpc1: "MULT\<^sup>a \<phi> \<longrightarrow> nMULTr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>c" by (metis MULTa_ADDIb_dual1 dual_compl_char2 dual_invol fp_nADDI_nMULT_dual2 ADDIb_fp1 ofp_comm_dc1)
lemma MULTa_fpc2: "CNTR \<phi> \<longrightarrow> (nMULTr\<^sup>a \<phi> \<longrightarrow> MULT\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>c)" by (metis CNTR_fpc EXPN_CNTR_dual2 MULTa_ADDIb_dual1 dual_compl_char2 dual_invol fp_nADDI_nMULT_dual2 ADDIb_fp ofp_comm_dc2 ofp_invol)
lemma MULTa_fpc: "CNTR \<phi> \<longrightarrow> (MULT\<^sup>a \<phi> = nMULTr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>c)" by (metis CNTR_fpc MULTa_fpc1 MULTa_fpc2 ofp_comm_compl ofp_invol sfun_compl_invol)
lemma MULTb_fpc1: "MULT\<^sup>b \<phi> \<longrightarrow> nMULTr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>c" by (metis ADDIa_MULTb_dual2 ADDIa_fp1 dual_compl_char2 dual_invol fp_nADDI_nMULT_dual1 ofp_comm_dc1)
lemma MULTb_fpc2: "(CNTR \<phi> \<or> nCNTR \<phi>) \<longrightarrow> (nMULTr\<^sup>b \<phi> \<longrightarrow> MULT\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>c)" unfolding cond subset_in_char subset_out_char op_fixpoint_def svfun_compl_def by (smt (z3) compl_def dimpl_def join_def meet_def subset_def)
lemma MULTb_fpc: "CNTR \<phi> \<longrightarrow> (MULT\<^sup>b \<phi> = nMULTr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>c)" by (metis CNTR_fpc MULTb_fpc1 MULTb_fpc2 ofp_comm_compl ofp_invol sfun_compl_invol)
lemma MULT_fpc: "CNTR \<phi> \<longrightarrow> (MULT \<phi> = nMULTr \<phi>\<^sup>f\<^sup>p\<^sup>c)" by (simp add: MULT_char MULTa_fpc MULTb_fpc nMULTr_char)

lemma nNORM_fp: "NORM \<phi> = nNORM \<phi>\<^sup>f\<^sup>p" by (metis NORM_def fixpoints_def fp_rel nNORM_def)
lemma DNRM_fp: "DNRM \<phi> = DNRM \<phi>\<^sup>f\<^sup>p" by (simp add: DNRM_def dimpl_def op_fixpoint_def top_def)
lemma NORM_fpc: "NORM \<phi> = NORM \<phi>\<^sup>f\<^sup>p\<^sup>c" by (simp add: NORM_def bottom_def ofp_fixpoint_compl_def sdiff_def)
lemma DNRM_fpc: "DNRM \<phi> = nDNRM \<phi>\<^sup>f\<^sup>p\<^sup>c" using DNRM_fp nDNRM_DNRM_compl by blast


definition IDEMr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("IDEMr\<^sup>a")
  where "IDEMr\<^sup>a \<phi> \<equiv> \<forall>A. \<phi>(A \<^bold>\<or> \<phi> A) \<preceq>\<^sup>A (\<phi> A)"
definition IDEMr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("IDEMr\<^sup>b") 
  where "IDEMr\<^sup>b \<phi> \<equiv> \<forall>A. (\<phi> A) \<preceq>\<^sub>A \<phi>(A \<^bold>\<and> \<phi> A)"

definition nIDEMr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nIDEMr\<^sup>a") 
  where "nIDEMr_a \<phi> \<equiv> \<forall>A. (\<phi> A) \<preceq>\<^sup>A \<phi>(A \<^bold>\<or> \<^bold>\<midarrow>(\<phi> A))"
definition nIDEMr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("nIDEMr\<^sup>b") 
  where "nIDEMr_b \<phi> \<equiv> \<forall>A. \<phi>(A \<^bold>\<and> \<^bold>\<midarrow>(\<phi> A)) \<preceq>\<^sub>A A \<^bold>\<and> (\<phi> A)"


declare IDEMr_a_def[cond] IDEMr_b_def[cond]
        nIDEMr_a_def[cond] nIDEMr_b_def[cond]

lemma nIDEMr_dual: "nIDEMr\<^sup>a \<phi> = nIDEMr\<^sup>b \<phi>\<^sup>d" unfolding cond subset_in_char subset_out_char by (smt (z3) BA_cmpl_equ BA_cp BA_deMorgan2 L5 L6 op_dual_def setequ_ext)
lemma nIDEMr_a_compl: "IDEMr\<^sup>a \<phi> = nIDEMr\<^sup>a \<phi>\<^sup>c" unfolding cond subset_out_char svfun_compl_def conn setequ_ext subset_def by auto
lemma nIDEMr_b_compl: "IDEMr\<^sup>b \<phi> = nIDEMr\<^sup>b \<phi>\<^sup>c" unfolding cond subset_in_char svfun_compl_def conn setequ_ext subset_def by auto

lemma aux1: "EXPN \<phi> \<Longrightarrow> IDEM\<^sup>a \<phi> \<longrightarrow> nIDEMr\<^sup>a \<phi>\<^sup>f\<^sup>p" unfolding cond op_fixpoint_def subset_out_char conn by (smt (verit, best) setequ_char setequ_ext subset_def)
lemma aux2: "EXPN \<phi> \<Longrightarrow> nIDEMr\<^sup>a \<phi> \<longrightarrow> IDEM\<^sup>a \<phi>\<^sup>f\<^sup>p" sorry (*TODO: kernel reconstruction fails*) (* unfolding cond subset_out_char op_fixpoint_def conn *) (* apply auto sledgehammer(setequ_def setequ_ext subset_def) *)

(*Assuming EXPN, nIDEMr\<^sup>a is the 'fixedpoint condition' for IDEM\<^sup>a *)
lemma IDEM_a_fp: "EXPN \<phi> \<longrightarrow> IDEM\<^sup>a \<phi> = nIDEMr\<^sup>a \<phi>\<^sup>f\<^sup>p" by (metis EXPN_fp aux1 aux2 ofp_invol)
(*Assuming EXPN, IDEMr\<^sup>a is the 'fixedpoint-complement condition' for IDEM\<^sup>a*)
lemma IDEM_a_fpc: "EXPN \<phi> \<longrightarrow> IDEM\<^sup>a \<phi> = IDEMr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>c" by (simp add: IDEM_a_fp nIDEMr_a_compl sfun_compl_invol)
(*Assuming CNTR, IDEMr\<^sup>b is the 'fixedpoint condition' for IDEM\<^sup>b*)
lemma IDEM_b_fp:  "CNTR \<phi> \<longrightarrow> IDEM\<^sup>b \<phi> = IDEMr\<^sup>b \<phi>\<^sup>f\<^sup>p" by (simp add: EXPN_CNTR_dual2 IDEM_a_fp IDEM_dual2 dual_compl_char2 dual_invol nIDEMr_b_compl nIDEMr_dual ofp_comm_dc1)
(*Assuming CNTR, nIDEMr\<^sup>b is the 'fixedpoint-complement condition' for IDEM\<^sup>b*)
lemma IDEM_b_fpc: "CNTR \<phi> \<longrightarrow> IDEM\<^sup>b \<phi> = nIDEMr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>c" by (simp add: IDEM_b_fp nIDEMr_b_compl)

end