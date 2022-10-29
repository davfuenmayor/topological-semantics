theory conditions_more
  imports conditions_kuratowski
begin


lemma MONO_ant: "MONO \<phi> \<Longrightarrow> \<forall>A B C. A \<^bold>\<preceq> B \<longrightarrow> \<phi>(B \<^bold>\<rightarrow> C) \<^bold>\<preceq> \<phi>(A \<^bold>\<rightarrow> C)" by (metis (full_types) MONO_def impl_def subset_def)
lemma MONO_cons: "MONO \<phi> \<Longrightarrow> \<forall>A B C. A \<^bold>\<preceq> B \<longrightarrow> \<phi>(C \<^bold>\<rightarrow> A) \<^bold>\<preceq> \<phi>(C \<^bold>\<rightarrow> B)" by (metis (full_types) MONO_def impl_def subset_def)


(**Properties regarding distribution over implication/difference.*)
definition DISTR_impl_inc::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("DISTR\<^sub>\<rightarrow>\<^sup>i")
  where "DISTR\<^sub>\<rightarrow>\<^sup>i \<phi> \<equiv> \<forall>A B. \<phi> (A \<^bold>\<rightarrow> B) \<^bold>\<preceq> (\<phi> A) \<^bold>\<rightarrow> (\<phi> B)" 
definition DISTR_impl_dec::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("DISTR\<^sub>\<rightarrow>\<^sup>d")
  where "DISTR\<^sub>\<rightarrow>\<^sup>d \<phi> \<equiv> \<forall>A B. (\<phi> A) \<^bold>\<rightarrow> (\<phi> B) \<^bold>\<preceq> \<phi> (A \<^bold>\<rightarrow> B)"

definition DISTR_diff_inc::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("DISTR\<^sub>\<leftharpoonup>\<^sup>i")
  where "DISTR\<^sub>\<leftharpoonup>\<^sup>i \<phi> \<equiv> \<forall>A B. \<phi> (A \<^bold>\<leftharpoonup> B) \<^bold>\<preceq> (\<phi> A) \<^bold>\<leftharpoonup> (\<phi> B)" 
definition DISTR_diff_dec::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("DISTR\<^sub>\<leftharpoonup>\<^sup>d")
  where "DISTR\<^sub>\<leftharpoonup>\<^sup>d \<phi> \<equiv> \<forall>A B. (\<phi> A) \<^bold>\<leftharpoonup> (\<phi> B) \<^bold>\<preceq> \<phi> (A \<^bold>\<leftharpoonup> B)" 

declare DISTR_impl_inc_def[cond] DISTR_impl_dec_def[cond]
        DISTR_diff_inc_def[cond] DISTR_diff_dec_def[cond]

(* lemma "DISTR\<^sub>\<leftharpoonup>\<^sup>i \<phi> \<longrightarrow> DISTR\<^sub>\<rightarrow>\<^sup>d \<phi>\<^sup>d" *)

lemma DISTR_diff_inc_prop: "MONO \<phi> \<Longrightarrow> CNTR \<phi> \<Longrightarrow> DISTR\<^sub>\<leftharpoonup>\<^sup>i \<phi>" unfolding cond by (smt (z3) diff_def subset_def)
lemma DISTR_impl_inc_prop: "MULT \<phi> \<Longrightarrow> DISTR\<^sub>\<rightarrow>\<^sup>i \<phi>" proof -
  assume mult: "MULT \<phi>"
  { fix a::"'a \<sigma>" and b::"'a \<sigma>"
    have "a \<^bold>\<and> b = a \<^bold>\<and> (a \<^bold>\<rightarrow> b)" unfolding conn by blast
    hence "\<phi>(a \<^bold>\<and> b) = \<phi>(a \<^bold>\<and> (a \<^bold>\<rightarrow> b))" by simp
    moreover from mult have "\<phi>(a \<^bold>\<and> b) \<^bold>\<approx> \<phi> a \<^bold>\<and> \<phi> b" by (simp add: MULT_def)
    moreover from mult have "\<phi>(a \<^bold>\<and> (a \<^bold>\<rightarrow> b)) \<^bold>\<approx> \<phi> a \<^bold>\<and> \<phi> (a \<^bold>\<rightarrow> b)" by (simp add: MULT_def)
    ultimately have "\<phi> a \<^bold>\<and> \<phi> (a \<^bold>\<rightarrow> b) \<^bold>\<approx> \<phi> a \<^bold>\<and> \<phi> b" by (simp add: setequ_ext)
    hence "\<phi> a \<^bold>\<and> \<phi> (a \<^bold>\<rightarrow> b) \<^bold>\<approx> \<phi> a \<^bold>\<and> (\<phi> a \<^bold>\<rightarrow> \<phi> b)" unfolding conn order by blast
    hence "\<phi>(a \<^bold>\<rightarrow> b) \<^bold>\<preceq> \<phi> a \<^bold>\<rightarrow> \<phi> b" unfolding conn order by blast
  } thus ?thesis by (simp add: DISTR_impl_inc_def)
qed
lemma DISTR_impl_dec_prop: "MONO \<phi> \<Longrightarrow> EXPN \<phi> \<Longrightarrow> DISTR\<^sub>\<rightarrow>\<^sup>d \<phi>" by (smt (verit, best) DISTR_impl_dec_def EXPN_def MONO_def impl_def subset_def)
lemma DISTR_diff_dec_prop: "ADDI \<phi> \<Longrightarrow> DISTR\<^sub>\<leftharpoonup>\<^sup>d \<phi>" proof -
  assume addi: "ADDI \<phi>"
  { fix a::"'a \<sigma>" and b::"'a \<sigma>"
    have "a \<^bold>\<or> b = (a \<^bold>\<leftharpoonup> b) \<^bold>\<or> b" unfolding conn by blast
    hence "\<phi>(a \<^bold>\<or> b) = \<phi>((a \<^bold>\<leftharpoonup> b) \<^bold>\<or> b)" by simp
    moreover from addi have "\<phi>(a \<^bold>\<or> b) \<^bold>\<approx> \<phi> a \<^bold>\<or> \<phi> b" by (simp add: ADDI_def)
    moreover from addi have "\<phi>((a \<^bold>\<leftharpoonup> b) \<^bold>\<or> b) \<^bold>\<approx> \<phi> (a \<^bold>\<leftharpoonup> b) \<^bold>\<or> (\<phi> b)" by (simp add: ADDI_def)
    ultimately have "\<phi> a \<^bold>\<or> \<phi> b \<^bold>\<approx> \<phi>(a \<^bold>\<leftharpoonup> b) \<^bold>\<or> \<phi> b" unfolding order by metis
    hence "(\<phi> a \<^bold>\<leftharpoonup> \<phi> b) \<^bold>\<or> \<phi> b \<^bold>\<approx> \<phi>(a \<^bold>\<leftharpoonup> b) \<^bold>\<or> \<phi> b" unfolding conn order by blast
    hence "\<phi> a \<^bold>\<leftharpoonup> \<phi> b \<^bold>\<preceq> \<phi> (a \<^bold>\<leftharpoonup> b)" unfolding conn order by blast
  } thus ?thesis by (simp add: DISTR_diff_dec_def)
qed

lemma ADDI_distr_impl_dual: "ADDI \<phi> \<Longrightarrow> \<forall>A B. \<phi>\<^sup>d(A \<^bold>\<rightarrow> B) \<^bold>\<preceq> \<phi> A \<^bold>\<rightarrow> \<phi> B" by (smt (verit) BA_cp BA_dn DISTR_diff_dec_def DISTR_diff_dec_prop diff_char op_dual_def setequ_ext)
lemma MULT_distr_diff_dual: "MULT \<phi> \<Longrightarrow> \<forall>A B. \<phi> A \<^bold>\<leftharpoonup> \<phi> B \<^bold>\<preceq> \<phi>\<^sup>d(A \<^bold>\<leftharpoonup> B)" by (smt (verit) BA_cp BA_dn DISTR_impl_inc_def DISTR_impl_inc_prop diff_char op_dual_def setequ_ext)
lemma ADDI_distr_diff_dual: "ADDI \<phi> \<Longrightarrow> \<forall>A B. \<phi>\<^sup>d A \<^bold>\<leftharpoonup> \<phi>\<^sup>d B \<^bold>\<preceq> \<phi>(A \<^bold>\<leftharpoonup> B)" by (smt (verit, ccfv_SIG) ADDI_MULT_dual1 BA_cp BA_dn DISTR_impl_inc_def DISTR_impl_inc_prop diff_char op_dual_def setequ_ext)
lemma MULT_distr_impl_dual: "MULT \<phi> \<Longrightarrow> \<forall>A B. \<phi>(A \<^bold>\<rightarrow> B) \<^bold>\<preceq> \<phi>\<^sup>d A \<^bold>\<rightarrow> \<phi>\<^sup>d B" by (metis ADDI_MULT_dual2 ADDI_distr_impl_dual dual_invol)

end