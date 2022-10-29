theory conditions_fp
  imports conditions_complement
begin

(**In the world of fixed-points these two properties play an essential role: *)
lemma EXPN_fp: "EXPN \<phi> = EXPN \<phi>\<^sup>f\<^sup>p" by (simp add: EXPN_def dimpl_def op_fixpoint_def subset_def)
lemma CNTR_fp: "CNTR \<phi> = nCNTR \<phi>\<^sup>f\<^sup>p" by (metis EXPN_CNTR_dual2 EXPN_fp dual_compl_char1 nEXPN_CNTR_compl nEXPN_nCNTR_dual2 ofp_comm_dc1)

definition fpMONO::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("fpMONO")
  where "fpMONO \<phi> \<equiv> \<forall>A B. A \<preceq> B \<longrightarrow> (\<phi> B) \<preceq> B \<^bold>\<or> (\<phi> A)"
definition fpMONOd::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("fpMONOd")
  where "fpMONOd \<phi> \<equiv> \<forall>A B. A \<preceq> B \<longrightarrow> A \<^bold>\<and> (\<phi> B) \<preceq> \<phi> A"
declare fpMONO_def[cond] fpMONOd_def[cond]

lemma p1: "fpMONO \<phi> = fpMONOd \<phi>\<^sup>d" by (smt (verit, best) BA_cp BA_deMorgan1 BA_deMorgan2 dual_compl_char1 dual_invol fpMONO_def fpMONOd_def sdfun_dcompl_def setequ_ext svfun_compl_def)
lemma p1': "fpMONOd \<phi> = fpMONO \<phi>\<^sup>d" by (simp add: dual_invol p1)

lemma "EXPN \<phi> \<Longrightarrow> MONO \<phi> = fpMONO \<phi>\<^sup>f\<^sup>p" oops

lemma weak1: "CNTR \<phi> \<Longrightarrow> fpMONO \<phi>" by (metis (mono_tags, lifting) CNTR_def fpMONO_def join_def subset_def)
lemma weak2: "CNTR \<phi> \<Longrightarrow> fpMONO \<phi>\<^sup>c" by (smt (verit, del_insts) CNTR_def compl_def fpMONO_def join_def subset_def svfun_compl_def)
lemma weak3: "EXPN \<phi> \<Longrightarrow> fpMONOd \<phi>" by (simp add: EXPN_def fpMONOd_def meet_def subset_def)
lemma weak4: "EXPN \<phi> \<Longrightarrow> fpMONOd \<phi>\<^sup>c" by (simp add: EXPN_def compl_def fpMONOd_def meet_def subset_def svfun_compl_def)

lemma t5: "EXPN \<phi> \<Longrightarrow> fpMONO \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi>" by (metis EXPN_def IDEM_b_def L1 fpMONO_def setequ_ext)

definition XYZ::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("XYZ")
  where "XYZ \<phi>  \<equiv> \<forall>A B. (A \<^bold>\<or> B) \<^bold>\<or> \<phi>(A \<^bold>\<or> B) \<approx> (A \<^bold>\<or> B) \<^bold>\<or> ((\<phi> A) \<^bold>\<and> (\<phi> B))"
definition XYZ_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("XYZ\<^sup>a")
  where "XYZ\<^sup>a \<phi> \<equiv> \<forall>A B. (A \<^bold>\<or> B) \<^bold>\<or> ((\<phi> A) \<^bold>\<and> (\<phi> B)) \<preceq> (A \<^bold>\<or> B) \<^bold>\<or> \<phi>(A \<^bold>\<or> B)"
definition XYZ_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("XYZ\<^sup>b")
  where "XYZ\<^sup>b \<phi> \<equiv> \<forall>A B. (A \<^bold>\<or> B) \<^bold>\<or> \<phi>(A \<^bold>\<or> B) \<preceq> (A \<^bold>\<or> B) \<^bold>\<or> ((\<phi> A) \<^bold>\<and> (\<phi> B))" 
 
declare XYZ_def[cond] XYZ_a_def[cond] XYZ_b_def[cond]

definition XYZd::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("XYZd")
  where "XYZd \<phi>   \<equiv> \<forall>A B. (A \<^bold>\<and> B) \<^bold>\<and> \<phi>(A \<^bold>\<and> B) \<approx> (A \<^bold>\<and> B) \<^bold>\<and> ((\<phi> A) \<^bold>\<or> (\<phi> B))"
definition XYZd_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("XYZd\<^sup>a")
  where "XYZd\<^sup>a \<phi>   \<equiv> \<forall>A B. (A \<^bold>\<and> B) \<^bold>\<and> ((\<phi> A) \<^bold>\<or> (\<phi> B)) \<preceq> (A \<^bold>\<and> B) \<^bold>\<and> \<phi>(A \<^bold>\<and> B)"
definition XYZd_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("XYZd\<^sup>b")
  where "XYZd\<^sup>b \<phi>   \<equiv> \<forall>A B. (A \<^bold>\<and> B) \<^bold>\<and> \<phi>(A \<^bold>\<and> B) \<preceq> (A \<^bold>\<and> B) \<^bold>\<and> ((\<phi> A) \<^bold>\<or> (\<phi> B))"

declare XYZd_def[cond] XYZd_a_def[cond] XYZd_b_def[cond]

lemma XYZ_duala: "XYZ\<^sup>a \<phi> = XYZd\<^sup>b \<phi>\<^sup>d" by (smt (verit, del_insts) BA_cp BA_deMorgan1 BA_dn XYZ_a_def XYZd_b_def op_dual_def setequ_ext)
lemma XYZ_dualb: "XYZ\<^sup>b \<phi> = XYZd\<^sup>a \<phi>\<^sup>d" by (smt (verit, del_insts) BA_cp BA_deMorgan1 BA_dn XYZ_b_def XYZd_a_def op_dual_def setequ_ext)
lemma t6: "XYZ \<phi> \<Longrightarrow> fpMONO \<phi>"  by (smt (verit, ccfv_threshold) L9 XYZ_def fpMONO_def join_def meet_def setequ_ext subset_def)
lemma t7: "XYZd \<phi> \<Longrightarrow> fpMONOd \<phi>" by (smt (verit) L10 L5 XYZd_def fpMONOd_def join_def meet_def setequ_ext subset_def)
lemma "XYZ\<^sup>a \<phi> = fpMONO \<phi>" nitpick oops
lemma "XYZd\<^sup>b \<phi> = fpMONOd \<phi>" nitpick oops
lemma t8: "XYZ\<^sup>b \<phi> = fpMONO \<phi>" proof
  show l2r: "XYZ\<^sup>b \<phi> \<Longrightarrow> fpMONO \<phi>" unfolding cond by (smt (z3) BA_distr2 L10 L5 L6 L9 join_def setequ_ext subset_def)
  show r2l: "fpMONO \<phi> \<Longrightarrow> XYZ\<^sup>b \<phi>" unfolding cond by (smt (verit, best) BA_distr2 L8 join_def setequ_ext subset_def)
qed
lemma t9: "XYZd\<^sup>a \<phi> = fpMONOd \<phi>" proof
  show l2r: "XYZd\<^sup>a \<phi> \<Longrightarrow> fpMONOd \<phi>" unfolding cond by (metis (full_types) L10 L6 meet_def setequ_ext subset_def)
  show r2l: "fpMONOd \<phi> \<Longrightarrow> XYZd\<^sup>a \<phi>" unfolding cond by (metis BA_distr1 L3 L4 L5 L7 L8 setequ_ext) 
qed

lemma conv1:  "ADDI\<^sup>a \<phi> \<longrightarrow> XYZ\<^sup>a \<phi>\<^sup>f\<^sup>p"  unfolding cond by (smt (z3) dimpl_def join_def meet_def op_fixpoint_def subset_def)
lemma conv2: "EXPN \<phi> \<Longrightarrow> XYZ\<^sup>a \<phi>\<^sup>f\<^sup>p \<longrightarrow> ADDI\<^sup>a \<phi>" unfolding cond op_fixpoint_def conn by (smt (verit) subset_def)
lemma conv3: "ADDI\<^sup>b \<phi> \<longrightarrow> XYZ\<^sup>b \<phi>\<^sup>f\<^sup>p" unfolding cond op_fixpoint_def conn by (smt (verit) subset_def)
lemma conv4: "EXPN \<phi> \<Longrightarrow> XYZ\<^sup>b \<phi>\<^sup>f\<^sup>p \<longrightarrow> ADDI\<^sup>b \<phi>" unfolding cond op_fixpoint_def conn by (smt (verit) subset_def)

lemma "NORM \<phi> = nNORM \<phi>\<^sup>f\<^sup>p" by (metis NORM_def fixpoints_def fp_rel nNORM_def)


(**fp-Idempotence (fpIDEM).*)
definition fpIDEM::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("fpIDEM") 
  where "fpIDEM \<phi> \<equiv> \<forall>A. (\<phi>\<^sup>- A) \<preceq> \<phi>\<^sup>-(\<phi> A)"
definition fpIDEMd::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("fpIDEMd") 
  where "fpIDEMd \<phi> \<equiv> \<forall>A. \<phi>(\<phi>\<^sup>d A) \<preceq> (\<phi> A)"

declare fpIDEM_def[cond] fpIDEMd_def[cond]

lemma "fpIDEM \<phi> = fpIDEMd \<phi>\<^sup>d" by (metis BA_cp dual_compl_char1 dual_invol fpIDEM_def fpIDEMd_def svfun_compl_def)
lemma "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi> \<Longrightarrow> fpIDEM \<phi>\<^sup>f\<^sup>p" unfolding cond conn2 conn order by (smt (z3))



(****************************************************)
(*
definition XYZ2::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("XYZ2")
  where "XYZ2 \<phi>   \<equiv> \<forall>A B. \<phi>(A \<^bold>\<or> B) \<approx> (A \<^bold>\<or> B) \<^bold>\<or> ((\<phi> A) \<^bold>\<and> (\<phi> B))"
definition XYZ2_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("XYZ2\<^sup>a")
  where "XYZ2\<^sup>a \<phi>   \<equiv> \<forall>A B. \<phi>(A \<^bold>\<or> B) \<preceq> (A \<^bold>\<or> B) \<^bold>\<or> ((\<phi> A) \<^bold>\<and> (\<phi> B))" 
definition XYZ2_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("XYZ2\<^sup>b")
  where "XYZ2\<^sup>b \<phi>   \<equiv> \<forall>A B. (A \<^bold>\<or> B) \<^bold>\<or> ((\<phi> A) \<^bold>\<and> (\<phi> B)) \<preceq> \<phi>(A \<^bold>\<or> B)" 

declare XYZ2_def[cond] XYZ2_a_def[cond] XYZ2_b_def[cond]

definition XYZ2d::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("XYZ2d")
  where "XYZ2d \<phi>   \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<approx> (A \<^bold>\<and> B) \<^bold>\<and> ((\<phi> A) \<^bold>\<or> (\<phi> B))"
definition XYZ2d_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("XYZ2d\<^sup>a")
  where "XYZ2d\<^sup>a \<phi>   \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<preceq> (A \<^bold>\<and> B) \<^bold>\<and> ((\<phi> A) \<^bold>\<or> (\<phi> B))"
definition XYZ2d_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("XYZ2d\<^sup>b")
  where "XYZ2d\<^sup>b \<phi>   \<equiv> \<forall>A B. (A \<^bold>\<and> B) \<^bold>\<and> ((\<phi> A) \<^bold>\<or> (\<phi> B)) \<preceq> \<phi>(A \<^bold>\<and> B)"

declare XYZ2d_def[cond] XYZ2d_a_def[cond] XYZ2d_b_def[cond]

lemma XYZ2_duala: "XYZ2\<^sup>a \<phi> = XYZ2d\<^sup>b \<phi>\<^sup>d" 
  using BA_cmpl_equ BA_cp BA_deMorgan1 BA_deMorgan2 
  unfolding cond   oops
  (* by (smt (verit) BA_cmpl_equ BA_cp BA_deMorgan1 BA_deMorgan2 L5 L6 XYZ2_a_def XYZ2d_b_def op_dual_def setequ_ext) *)
lemma "XYZ\<^sup>b \<phi> \<longrightarrow> XYZ2\<^sup>b \<phi>" nitpick oops
lemma "XYZ2\<^sup>b \<phi> \<longrightarrow> XYZ\<^sup>b \<phi>" by (simp add: XYZ2_b_def XYZ_b_def join_def subset_def)

lemma conv1:  "EXPN \<phi> \<Longrightarrow> ADDI \<phi> \<longrightarrow> XYZ2 \<phi>\<^sup>f\<^sup>p" oops
  (* unfolding cond by (smt (z3) dimpl_def join_def meet_def op_fixpoint_def subset_def) *)
(*
lemma conv2: "EXPN \<phi> \<Longrightarrow> XYZ\<^sup>b \<phi>\<^sup>f\<^sup>p \<longrightarrow> ADDI\<^sup>a \<phi>" unfolding cond op_fixpoint_def conn by (smt (verit) subset_def)
lemma conv3: "ADDI\<^sup>b \<phi> \<longrightarrow> XYZ\<^sup>a \<phi>\<^sup>f\<^sup>p" unfolding cond op_fixpoint_def conn by (smt (verit) subset_def)
lemma conv4: "EXPN \<phi> \<Longrightarrow> XYZ\<^sup>a \<phi>\<^sup>f\<^sup>p \<longrightarrow> ADDI\<^sup>b \<phi>" unfolding cond op_fixpoint_def conn by (smt (verit) subset_def)
*)

*)



end