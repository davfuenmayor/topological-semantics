theory conditions_fixedpoint_backup
  imports conditions_complement
begin

(**In the world of fixed-points these two properties play an essential role: *)
lemma EXPN_fp: "EXPN \<phi> = EXPN \<phi>\<^sup>f\<^sup>p" by (simp add: EXPN_def dimpl_def op_fixpoint_def subset_def)
lemma CNTR_fp: "CNTR \<phi> = CNTR \<phi>\<^sup>c\<^sup>f\<^sup>p" by (simp add: EXPN_CNTR_dual2 EXPN_def compl_def dimpl_def op_dual_def op_fixpoint_def subset_def svfun_compl_def)

definition wMONO::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("wMONO") 
  where "wMONO \<phi> \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> (\<phi> A) \<^bold>\<preceq> B \<^bold>\<or> (\<phi> B)"
definition wMONOd::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("wMONOd")
  where "wMONOd \<phi> \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> A \<^bold>\<and> (\<phi> A) \<^bold>\<preceq> (\<phi> B)"

declare wMONO_def[cond] wMONOd_def[cond]

lemma g1: "wMONO \<phi> = wMONOd \<phi>\<^sup>d" by (smt (z3) BA_cmpl_equ BA_cp BA_deMorgan1 BA_deMorgan2 dual_compl_char2 dual_invol ofp_comm_dc1 ofp_invol sdfun_dcompl_def setequ_ext svfun_compl_def wMONO_def wMONOd_def)
lemma g2: "MONO \<phi> \<Longrightarrow> wMONO \<phi>" by (simp add: MONO_def wMONO_def join_def subset_def)
lemma g3: "MONO \<phi> \<Longrightarrow> wMONOd \<phi>" by (simp add: MONO_def wMONOd_def meet_def subset_def)
lemma g4: "CNTR \<phi> \<Longrightarrow> wMONO \<phi>" by (smt (verit) CNTR_def wMONO_def join_def subset_def)
lemma g5: "EXPN \<phi> \<Longrightarrow> wMONOd \<phi>" by (metis EXPN_CNTR_dual1 dual_invol g1 g4)

lemma g6: "EXPN \<phi> \<Longrightarrow> wMONO \<phi> \<Longrightarrow> MONO \<phi>" by (simp add: EXPN_def L9 MONO_def setequ_ext wMONO_def)
lemma g7: "CNTR \<phi> \<Longrightarrow> wMONOd \<phi> \<Longrightarrow> MONO \<phi>" by (simp add: CNTR_def L10 MONO_def setequ_ext wMONOd_def)

lemma g8: "CNTR \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> (\<forall>A. \<phi> A \<^bold>\<approx> A)" by (simp add: CNTR_def EXPN_def setequ_char)
lemma "EXPN \<phi> \<Longrightarrow> wMONO \<phi> \<Longrightarrow> (\<forall>A. \<phi> A \<^bold>\<approx> A)" nitpick oops
lemma "CNTR \<phi> \<Longrightarrow> wMONOd \<phi> \<Longrightarrow> (\<forall>A. \<phi> A \<^bold>\<approx> A)" nitpick oops

definition fpMONO::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("fpMONO")
  where "fpMONO \<phi> \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> (\<phi> B) \<^bold>\<preceq> B \<^bold>\<or> (\<phi> A)"
definition fpMONOd::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("fpMONOd")
  where "fpMONOd \<phi> \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> A \<^bold>\<and> (\<phi> B) \<^bold>\<preceq> \<phi> A"
  (* where "fpMONO \<phi> \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> A \<^bold>\<and> (\<phi> B) \<^bold>\<preceq> B \<^bold>\<and> (\<phi> A)" *)
declare fpMONO_def[cond] fpMONOd_def[cond]

lemma "EXPN \<phi> \<Longrightarrow> fpMONO \<phi> \<Longrightarrow> (\<forall>A. \<phi> A \<^bold>\<approx> A)" nitpick oops
lemma "CNTR \<phi> \<Longrightarrow> fpMONOd \<phi> \<Longrightarrow> (\<forall>A. \<phi> A \<^bold>\<approx> A)" nitpick oops
lemma "MONO \<phi> \<Longrightarrow> fpMONO \<phi> \<Longrightarrow> (\<forall>A. \<phi> A \<^bold>\<approx> A)" nitpick oops
lemma "MONO \<phi> \<Longrightarrow> fpMONOd \<phi> \<Longrightarrow> (\<forall>A. \<phi> A \<^bold>\<approx> A)" nitpick oops

lemma t1: "CNTR \<phi> \<Longrightarrow> fpMONO \<phi>" by (metis (mono_tags, lifting) CNTR_def fpMONO_def join_def subset_def)
lemma t2: "CNTR \<phi> \<Longrightarrow> fpMONO \<phi>\<^sup>c" by (smt (verit, del_insts) CNTR_def compl_def fpMONO_def join_def subset_def svfun_compl_def)
lemma t3: "EXPN \<phi> \<Longrightarrow> fpMONOd \<phi>" by (simp add: EXPN_def fpMONOd_def meet_def subset_def)
lemma t4: "EXPN \<phi> \<Longrightarrow> fpMONOd \<phi>\<^sup>c" by (simp add: EXPN_def compl_def fpMONOd_def meet_def subset_def svfun_compl_def)

(**IDEM\<^sup>b is another weakening of CNTR (alongside with wMONO and fpMONO) *)
lemma "CNTR \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi>" by (simp add: CNTR_impl_IDEM_b)
(* all 3 weakenings are independent*)
lemma "EXPN \<phi> \<Longrightarrow> wMONO \<phi> \<Longrightarrow> fpMONO \<phi>" nitpick oops
lemma "EXPN \<phi> \<Longrightarrow> fpMONO \<phi> \<Longrightarrow> wMONO \<phi>" nitpick oops
lemma "EXPN \<phi> \<Longrightarrow> wMONO \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi>" nitpick oops
lemma "fpMONO \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi>" nitpick oops

lemma "IDEM\<^sup>b \<phi> \<Longrightarrow> fpMONO \<phi>" nitpick oops
lemma "IDEM\<^sup>b \<phi> \<Longrightarrow> wMONO \<phi>" nitpick oops
(* IDEM\<^sup>b is not strong enough to recover wMONO nor fpMONO*)
lemma "EXPN \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi> \<Longrightarrow> wMONO \<phi>" nitpick oops
lemma "EXPN \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi> \<Longrightarrow> fpMONO \<phi>" nitpick oops
lemma "MONO \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi> \<Longrightarrow> fpMONO \<phi>" nitpick oops

lemma "MONO \<phi> \<Longrightarrow> fpMONO \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi> " oops
lemma t5: "EXPN \<phi> \<Longrightarrow> fpMONO \<phi> \<Longrightarrow> IDEM\<^sup>b \<phi>" by (metis EXPN_def IDEM_b_def L1 fpMONO_def setequ_ext)


lemma p1: "fpMONO \<phi> = fpMONOd \<phi>\<^sup>d" by (smt (verit, best) BA_cp BA_deMorgan1 BA_deMorgan2 dual_compl_char1 dual_invol fpMONO_def fpMONOd_def sdfun_dcompl_def setequ_ext svfun_compl_def)
lemma p1': "fpMONOd \<phi> = fpMONO \<phi>\<^sup>d" by (simp add: dual_invol p1)
lemma p2: "wMONO \<phi> = fpMONO \<phi>\<^sup>f\<^sup>p" unfolding cond op_fixpoint_def  conn order by auto
lemma p3: "wMONOd \<phi> = fpMONOd \<phi>\<^sup>c\<^sup>f\<^sup>p" by (metis dual_compl_char2 dual_invol g1 ofp_comm_compl ofp_comm_dc1 p1' p2)

definition XYZ::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("XYZ")
  (* where "XYZ \<phi>   \<equiv> \<forall>A B. (A \<^bold>\<and> B) \<^bold>\<and> \<phi>(A \<^bold>\<or> B) \<^bold>\<approx> (A \<^bold>\<and> B) \<^bold>\<and> ((\<phi> A) \<^bold>\<and> (\<phi> B))"  *)
  (* where "XYZ \<phi>   \<equiv> \<forall>A B. (A \<^bold>\<or> B) \<^bold>\<and> \<phi>(A \<^bold>\<or> B) \<^bold>\<approx> (A \<^bold>\<or> B) \<^bold>\<and> ((\<phi> A) \<^bold>\<and> (\<phi> B))"  *)
  where "XYZ \<phi>   \<equiv> \<forall>A B. (A \<^bold>\<or> B) \<^bold>\<or> \<phi>(A \<^bold>\<or> B) \<^bold>\<approx> (A \<^bold>\<or> B) \<^bold>\<or> ((\<phi> A) \<^bold>\<and> (\<phi> B))" 

definition XYZd::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("XYZd")
  where "XYZd \<phi>   \<equiv> \<forall>A B. (A \<^bold>\<and> B) \<^bold>\<and> \<phi>(A \<^bold>\<or> B) \<^bold>\<approx> (A \<^bold>\<and> B) \<^bold>\<and> ((\<phi> A) \<^bold>\<and> (\<phi> B))"

lemma "XYZ \<phi> \<Longrightarrow> fpMONO \<phi>"  by (smt (verit, ccfv_threshold) L9 XYZ_def fpMONO_def join_def meet_def setequ_ext subset_def)
lemma "XYZd \<phi> \<Longrightarrow> fpMONOd \<phi>" by (smt (z3) L6 L9 XYZd_def fpMONOd_def meet_def setequ_ext subset_def)
lemma "XYZ \<phi> \<Longrightarrow> wMONO \<phi>"  nitpick oops
lemma "XYZ \<phi> \<Longrightarrow> wMONOd \<phi>"  nitpick oops
lemma "XYZd \<phi> \<Longrightarrow> wMONO \<phi>"  nitpick oops
lemma "XYZd \<phi> \<Longrightarrow> wMONOd \<phi>"  nitpick oops

lemma "XYZ \<phi> \<Longrightarrow> CNTR \<phi>"  nitpick oops
lemma "XYZ \<phi> \<Longrightarrow> EXPN \<phi>"  nitpick oops
lemma "XYZd \<phi> \<Longrightarrow> CNTR \<phi>"  nitpick oops
lemma "XYZd \<phi> \<Longrightarrow> EXPN \<phi>"  nitpick oops

lemma "fpMONO \<phi> \<Longrightarrow> XYZ \<phi> " nitpick oops
lemma "fpMONOd \<phi> \<Longrightarrow> XYZ \<phi> " nitpick oops
lemma "fpMONO \<phi> \<Longrightarrow> XYZd \<phi> " nitpick oops
lemma "fpMONOd \<phi> \<Longrightarrow> XYZd \<phi> " nitpick oops

lemma "wMONO \<phi> \<Longrightarrow> fpMONO \<phi> \<Longrightarrow> XYZ \<phi> " nitpick oops
lemma "wMONOd \<phi> \<Longrightarrow> fpMONOd \<phi> \<Longrightarrow> XYZd \<phi> " nitpick oops
lemma "EXPN \<phi> \<Longrightarrow> fpMONO \<phi> \<Longrightarrow> XYZ \<phi> " nitpick oops

(*
lemma "ADDI \<phi> \<longrightarrow> XYZ \<phi>\<^sup>f\<^sup>p" by (smt (verit, ccfv_threshold) ADDI_def XYZ_def dimpl_def join_def meet_def op_fixpoint_def setequ_def)
lemma "EXPN \<phi> \<Longrightarrow> XYZ \<phi>\<^sup>f\<^sup>p \<longrightarrow> ADDI \<phi>" unfolding cond XYZ_def oops
lemma "XYZ \<phi>\<^sup>f\<^sup>p \<longrightarrow> ADDI\<^sup>a \<phi>" nitpick oops
lemma "XYZ \<phi>\<^sup>f\<^sup>p \<longrightarrow> ADDI\<^sup>b \<phi>" nitpick oops
lemma "XYZ \<phi>\<^sup>f\<^sup>p \<longrightarrow> MONO \<phi>" nitpick oops

lemma "EXPN \<phi> \<Longrightarrow> ADDI \<phi> \<longrightarrow> ADDI\<^sup>a \<phi>\<^sup>f\<^sup>p" nitpick oops
lemma "EXPN \<phi> \<Longrightarrow> ADDI \<phi> \<longrightarrow> MULT\<^sup>b \<phi>\<^sup>f\<^sup>p" nitpick oops

definition ABC::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("ABC")
  where "ABC \<phi>   \<equiv> \<forall>A B. \<phi>(A \<^bold>\<or> B) \<^bold>\<approx> (A \<^bold>\<or> \<phi> B) \<^bold>\<and> ((\<phi> A) \<^bold>\<or> B)" 

lemma "ADDI \<phi> \<longrightarrow> ABC \<phi>\<^sup>f\<^sup>p" nitpick oops
lemma "ABC \<phi> \<longrightarrow> ADDI \<phi>\<^sup>f\<^sup>p " unfolding ABC_def ADDI_def 
  (* sledgehammer *)
  (* by (smt (verit) BA_distr1 BA_distr2 L1 L5 L6 dimpl_def join_def meet_def op_fixpoint_def setequ_def setequ_ext) *)

*)
end