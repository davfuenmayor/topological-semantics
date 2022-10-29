theory conditions_negative
  imports conditions_positive
begin

(** We define and interrelate some useful axiomatic conditions on unary operations (operators) 
having a 'p-parametric type @{type "'p \<sigma> \<Rightarrow> 'p \<sigma>"}.
Boolean algebras extended with such operators give us different sorts of topological Boolean algebras.*)


(**Anti-tonicity (ANTI).*)
definition ANTI::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("ANTI")
  where "ANTI \<phi> \<equiv> \<forall>A B. A \<preceq> B \<longrightarrow> \<phi> B \<preceq> \<phi> A"

declare ANTI_def[cond]

(**ANTI is self-dual*)
lemma ANTI_dual: "ANTI \<phi> = ANTI \<phi>\<^sup>d" by (smt (verit) BA_cp ANTI_def dual_invol op_dual_def)
(**ANTI is the 'complement' of MONO*)
lemma ANTI_MONO: "ANTI \<phi> = MONO \<phi>\<^sup>c" by (metis ANTI_def BA_cp MONO_def svfun_compl_def)


(**anti-Expansive/extensive (EXPN) and its dual contractive (CNTR).*)
definition nEXPN::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("nEXPN")
  where "nEXPN \<phi>  \<equiv> \<forall>A. \<phi> A \<preceq> \<^bold>\<midarrow>A"
definition nCNTR::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("nCNTR")
  where "nCNTR \<phi> \<equiv> \<forall>A. \<^bold>\<midarrow>A \<preceq> \<phi> A"

declare nEXPN_def[cond] nCNTR_def[cond]

(**nEXPN and nCNTR are dual to each other *)
lemma nEXPN_nCNTR_dual1: "nEXPN \<phi> = nCNTR \<phi>\<^sup>d" unfolding cond by (metis BA_cp BA_dn op_dual_def setequ_ext)
lemma nEXPN_nCNTR_dual2: "nCNTR \<phi> = nEXPN \<phi>\<^sup>d" by (simp add: dual_invol nEXPN_nCNTR_dual1)

(**nEXPN and nCNTR are the 'complements' of EXPN and CNTR respectively*)
lemma nEXPN_CNTR_compl: "nEXPN \<phi> = EXPN \<phi>\<^sup>c" by (metis BA_cp EXPN_def nEXPN_def sfun_compl_invol svfun_compl_def)
lemma nCNTR_EXPN_compl: "nCNTR \<phi> = CNTR \<phi>\<^sup>c" by (metis EXPN_CNTR_dual1 dual_compl_char1 dual_compl_char2 dual_invol nEXPN_CNTR_compl nEXPN_nCNTR_dual2)

(**anti-Normality (nNORM) and its dual (nDNRM).*)
definition nNORM::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("nNORM")
  where "nNORM \<phi>  \<equiv> (\<phi> \<^bold>\<bottom>) \<approx> \<^bold>\<top>"
definition nDNRM::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("nDNRM")
  where "nDNRM \<phi> \<equiv> (\<phi> \<^bold>\<top>) \<approx> \<^bold>\<bottom>" 

declare nNORM_def[cond] nDNRM_def[cond]

(**nNORM and nDNRM are dual to each other *)
lemma nNOR_dual1: "nNORM \<phi> = nDNRM \<phi>\<^sup>d" unfolding cond by (simp add: bottom_def compl_def op_dual_def setequ_def top_def)
lemma nNOR_dual2: "nDNRM \<phi> = nNORM \<phi>\<^sup>d" by (simp add: dual_invol nNOR_dual1) 

(**nNORM and nDNRM are the 'complements' of NORM and DNRM respectively*)
lemma nNORM_NORM_compl: "nNORM \<phi> = NORM \<phi>\<^sup>c" unfolding cond by (simp add: NORM_def bottom_def compl_def setequ_def svfun_compl_def top_def)
lemma nDNRM_DNRM_compl: "nDNRM \<phi> = DNRM \<phi>\<^sup>c" by (simp add: DNRM_def bottom_def compl_def nDNRM_def setequ_def svfun_compl_def top_def)

(**nEXPN (nCNTR) entail nDNRM (nNORM).*)
lemma nEXPN_impl_nDNRM: "nEXPN \<phi> \<longrightarrow> nDNRM \<phi>" unfolding cond by (metis bottom_def compl_def setequ_def subset_def top_def)
lemma nCNTR_impl_nNORM: "nCNTR \<phi> \<longrightarrow> nNORM \<phi>" by (simp add: nEXPN_impl_nDNRM nEXPN_nCNTR_dual2 nNOR_dual1)


(**anti-Idempotence (nIDEM).*)
definition nIDEM::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("nIDEM") 
  where "nIDEM \<phi>  \<equiv> \<forall>A. (\<phi> A) \<approx> \<phi>(\<^bold>\<midarrow>(\<phi> A))"
definition nIDEM_a::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("nIDEM\<^sup>a") 
  where "nIDEM_a \<phi> \<equiv> \<forall>A. \<phi>(\<^bold>\<midarrow>(\<phi> A)) \<preceq> (\<phi> A)"
definition nIDEM_b::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("nIDEM\<^sup>b") 
  where "nIDEM_b \<phi> \<equiv> \<forall>A. (\<phi> A) \<preceq> \<phi>(\<^bold>\<midarrow>(\<phi> A))"

declare nIDEM_def[cond] nIDEM_a_def[cond] nIDEM_b_def[cond]

(**nIDEM-a and nIDEM-b are dual to each other *)
lemma nIDEM_dual1: "nIDEM\<^sup>a \<phi> = nIDEM\<^sup>b \<phi>\<^sup>d" unfolding cond by (metis BA_cp BA_dn op_dual_def setequ_ext)
lemma nIDEM_dual2: "nIDEM\<^sup>b \<phi> = nIDEM\<^sup>a \<phi>\<^sup>d" by (simp add: dual_invol nIDEM_dual1)

lemma nIDEM_char: "nIDEM \<phi> = (nIDEM\<^sup>a \<phi> \<and> nIDEM\<^sup>b \<phi>)" unfolding cond setequ_char by blast
lemma nIDEM_dual: "nIDEM \<phi> = nIDEM \<phi>\<^sup>d" using nIDEM_char nIDEM_dual1 nIDEM_dual2 by blast

(**nIDEM(a/b) and IDEM(a/b) are the 'complements' each other*)
lemma nIDEM_a_compl: "nIDEM\<^sup>a \<phi> = IDEM\<^sup>a \<phi>\<^sup>c" unfolding cond by (metis (no_types, opaque_lifting) BA_cp IDEM_a_def svfun_compl_def)
lemma nIDEM_b_compl: "nIDEM\<^sup>b \<phi> = IDEM\<^sup>b \<phi>\<^sup>c" by (metis IDEM_dual1 dual_compl_char1 dual_compl_char2 dual_invol nIDEM_a_compl nIDEM_dual2)
lemma nIDEM_compl: "nIDEM \<phi> = IDEM \<phi>\<^sup>c" by (simp add: IDEM_char nIDEM_a_compl nIDEM_b_compl nIDEM_char)

(**nEXPN (nCNTR) entail nIDEM-a (nIDEM-b).*)
lemma nEXPN_impl_nIDEM_a: "nEXPN \<phi> \<longrightarrow> nIDEM\<^sup>a \<phi>" by (simp add: EXPN_impl_IDEM_a nEXPN_CNTR_compl nIDEM_a_compl)
lemma nCNTR_impl_nIDEM_b: "nCNTR \<phi> \<longrightarrow> nIDEM\<^sup>b \<phi>" by (simp add: nEXPN_impl_nIDEM_a nEXPN_nCNTR_dual2 nIDEM_dual2)


(**anti-Distribution over joins or anti-additivity (nADDI) and its dual...*)
definition nADDI::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("nADDI")
  where "nADDI \<phi>   \<equiv> \<forall>A B. (\<phi> A) \<^bold>\<and> (\<phi> B) \<approx> \<phi>(A \<^bold>\<or> B)" 
definition nADDI_a::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("nADDI\<^sup>a")
  where "nADDI\<^sup>a \<phi> \<equiv> \<forall>A B.  (\<phi> A) \<^bold>\<and> (\<phi> B) \<preceq> \<phi>(A \<^bold>\<or> B)" 
definition nADDI_b::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("nADDI\<^sup>b")
  where "nADDI\<^sup>b \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<or> B) \<preceq> (\<phi> A) \<^bold>\<and> (\<phi> B)"

(**... anti-distribution over meets or anti-multiplicativity (nMULT).*)
definition nMULT::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("nMULT") 
  where "nMULT \<phi>   \<equiv> \<forall>A B. (\<phi> A) \<^bold>\<or> (\<phi> B) \<approx> \<phi>(A \<^bold>\<and> B)" 
definition nMULT_a::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("nMULT\<^sup>a")
  where "nMULT\<^sup>a \<phi> \<equiv> \<forall>A B. (\<phi> A) \<^bold>\<or> (\<phi> B) \<preceq> \<phi>(A \<^bold>\<and> B)"
definition nMULT_b::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("nMULT\<^sup>b")
  where "nMULT\<^sup>b \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<preceq> (\<phi> A) \<^bold>\<or> (\<phi> B)" 

declare nADDI_def[cond] nADDI_a_def[cond] nADDI_b_def[cond]
        nMULT_def[cond] nMULT_a_def[cond] nMULT_b_def[cond]

lemma nADDI_char: "nADDI \<phi> = (nADDI\<^sup>a \<phi> \<and> nADDI\<^sup>b \<phi>)" unfolding cond using setequ_char by blast
lemma nMULT_char: "nMULT \<phi> = (nMULT\<^sup>a \<phi> \<and> nMULT\<^sup>b \<phi>)" unfolding cond using setequ_char by blast

(**ANTI, nMULT-a and nADDI-b are equivalent.*)
lemma ANTI_nMULTa: "nMULT\<^sup>a \<phi> = ANTI \<phi>" unfolding cond by (smt (z3) L10 L7 join_def meet_def setequ_ext subset_def)
lemma ANTI_nADDIb: "nADDI\<^sup>b \<phi> = ANTI \<phi>" unfolding cond by (smt (verit) BA_cp BA_deMorgan1 L10 L3 L5 L8 L9 setequ_char setequ_ext)

(**Below we prove several duality relationships between nADDI(a/b) and nMULT(a/b).*)

(**Duality between nMULT-a and nADDI-b (an easy corollary from the self-duality of ANTI).*)
lemma nMULTa_nADDIb_dual1: "nMULT\<^sup>a \<phi> = nADDI\<^sup>b \<phi>\<^sup>d" using ANTI_nADDIb ANTI_nMULTa ANTI_dual by blast
lemma nMULTa_nADDIb_dual2: "nADDI\<^sup>b \<phi> = nMULT\<^sup>a \<phi>\<^sup>d" by (simp add: dual_invol nMULTa_nADDIb_dual1)
(**Duality between nADDI-a and nMULT-b.*)
lemma nADDIa_nMULTb_dual1: "nADDI\<^sup>a \<phi> = nMULT\<^sup>b \<phi>\<^sup>d" unfolding cond by (metis (no_types, lifting) BA_cp BA_deMorgan1 BA_dn op_dual_def setequ_ext)
lemma nADDIa_nMULTb_dual2: "nMULT\<^sup>b \<phi> = nADDI\<^sup>a \<phi>\<^sup>d" by (simp add: dual_invol nADDIa_nMULTb_dual1)
(**Duality between ADDI and MULT.*)
lemma nADDI_nMULT_dual1: "nADDI \<phi> = nMULT \<phi>\<^sup>d" using nADDI_char nADDIa_nMULTb_dual1 nMULT_char nMULTa_nADDIb_dual2 by blast
lemma nADDI_nMULT_dual2: "nMULT \<phi> = nADDI \<phi>\<^sup>d" by (simp add: dual_invol nADDI_nMULT_dual1)

lemma "ADDI\<^sup>a \<phi> = nADDI\<^sup>a \<phi>\<^sup>c" by (metis ADDI_a_def BA_cp BA_deMorgan1 nADDI_a_def setequ_ext svfun_compl_def)
lemma "ADDI\<^sup>b \<phi> = nADDI\<^sup>b \<phi>\<^sup>c" by (simp add: ANTI_nADDIb ANTI_MONO MONO_ADDIb sfun_compl_invol)
lemma "MULT\<^sup>a \<phi> = nMULT\<^sup>a \<phi>\<^sup>c" by (simp add: ANTI_MONO ANTI_nMULTa MONO_MULTa sfun_compl_invol)
lemma "MULT\<^sup>b \<phi> = nMULT\<^sup>b \<phi>\<^sup>c" by (metis BA_cp BA_deMorgan2 MULT_b_def nMULT_b_def setequ_ext svfun_compl_def)


(**We verify properties regarding closure over meets/joins for fixed-points.*)

(**nMULT for an operator implies join-closedness of the set of fixed-points of its dual-complement*)
lemma nMULT_joinclosed: "nMULT \<phi> \<Longrightarrow> join_closed (fp (\<phi>\<^sup>-))" by (smt (verit, del_insts) ADDI_MULT_dual2 ADDI_joinclosed BA_deMorgan1 MULT_def dual_compl_char2 nMULT_def setequ_ext svfun_compl_def)
lemma "join_closed (fp (\<phi>\<^sup>-)) \<Longrightarrow> nMULT \<phi>" nitpick oops (*countermodel found: needs further assumptions*)
lemma joinclosed_nMULT: "ANTI \<phi> \<Longrightarrow> nCNTR \<phi> \<Longrightarrow> nIDEM\<^sup>a \<phi> \<Longrightarrow> join_closed (fp (\<phi>\<^sup>-)) \<Longrightarrow> nMULT \<phi>" by (smt (verit) ADDI_def ANTI_MONO BA_deMorgan2 MONO_dual dual_compl_char1 dual_compl_char2 dual_invol joinclosed_ADDI nEXPN_CNTR_compl nEXPN_nCNTR_dual2 nIDEM_b_compl nIDEM_dual1 nMULT_def op_dual_def setequ_ext svfun_compl_def)

(**nADDI for an operator implies meet-closedness of the set of fixed-points of its dual-complement*)
lemma nADDI_meetclosed: "nADDI \<phi> \<Longrightarrow> meet_closed (fp (\<phi>\<^sup>-))" by (smt (verit, ccfv_threshold) ADDI_MULT_dual1 ADDI_def BA_deMorgan2 MULT_meetclosed dual_compl_char2 nADDI_def setequ_ext svfun_compl_def)
lemma "meet_closed (fp (\<phi>\<^sup>-)) \<Longrightarrow> nADDI \<phi>" nitpick oops (*countermodel found: needs further assumptions*)
lemma meetclosed_nADDI: "ANTI \<phi> \<Longrightarrow> nEXPN \<phi> \<Longrightarrow> nIDEM\<^sup>b \<phi> \<Longrightarrow> meet_closed (fp (\<phi>\<^sup>-)) \<Longrightarrow> nADDI \<phi>" by (metis ADDI_MULT_dual1 ADDI_joinclosed ANTI_MONO EXPN_CNTR_dual1 MONO_dual dual_compl_char1 dual_compl_char2 fp_compl fp_dcompl joinclosed_nMULT meetclosed_MULT nADDI_nMULT_dual1 nEXPN_CNTR_compl nEXPN_nCNTR_dual1 nIDEM_a_compl nIDEM_dual2)

(**Assuming ANTI, we have that nEXPN (nCNTR) implies meet-closed (join-closed) for the set of fixed-points.*)
lemma nEXPN_meetclosed: "ANTI \<phi> \<Longrightarrow> nEXPN \<phi> \<Longrightarrow> meet_closed (fp \<phi>)" by (metis (full_types) L10 compl_def fixpoints_def meet_closed_def nEXPN_def setequ_ext subset_def)
lemma nCNTR_joinclosed: "ANTI \<phi> \<Longrightarrow> nCNTR \<phi> \<Longrightarrow> join_closed (fp \<phi>)" by (smt (verit, ccfv_threshold) BA_impl L9 fixpoints_def impl_char join_closed_def nCNTR_def setequ_char setequ_ext)

(*TODO:*)

lemma "nEXPN \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow> \<not>nonEmpty (fp \<phi>)" nitpick oops(*TODO: explain*)

(*

(**Further assuming IDEM the above results can be stated to the whole range of an operator.*)
lemma "ANTI \<phi> \<Longrightarrow> nEXPN \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow> meet_closed (\<lbrakk>\<phi> _\<rbrakk>)"  unfolding cond oops
lemma "nCNTR \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow> join_closed (\<lbrakk>\<phi> _\<rbrakk>)" by (smt (verit) BA_impl IDEM_range_fp L9 fixpoints_def impl_char join_closed_def nCNTR_def setequ_char setequ_ext)
lemma "ANTI \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow> join_closed (\<lbrakk>\<phi> _\<rbrakk>)" oops 

lemma "ANTI \<phi> \<Longrightarrow> nCNTR \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow> join_closed (\<lbrakk>\<phi> _\<rbrakk>)"  unfolding cond oops
lemma "nEXPN \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow> meet_closed (\<lbrakk>\<phi> _\<rbrakk>)" oops 
lemma "ANTI \<phi> \<Longrightarrow> IDEM \<phi> \<Longrightarrow> meet_closed (\<lbrakk>\<phi> _\<rbrakk>)" oops 

(**And assuming nIDEM the results are dualized*)
lemma "ANTI \<phi> \<Longrightarrow> nEXPN \<phi> \<Longrightarrow> nIDEM \<phi> \<Longrightarrow> join_closed (\<lbrakk>\<phi> _\<rbrakk>)" unfolding cond oops
lemma "ANTI \<phi> \<Longrightarrow> nCNTR \<phi> \<Longrightarrow> nIDEM \<phi> \<Longrightarrow> meet_closed (\<lbrakk>\<phi> _\<rbrakk>)" unfolding cond oops
*)
end