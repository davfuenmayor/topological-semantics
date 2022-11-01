theory conditions_fixedpoint_infinitary
  imports conditions_fixedpoint conditions_complement_infinitary
begin                        

(**We define and interrelate infinitary variants for some previously introduced
 axiomatic conditions on operators.*)

definition iADDIr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iADDIr")
  where "iADDIr \<phi>  \<equiv> \<forall>S. let U=\<^bold>\<Or>S in (\<phi>(\<^bold>\<Or>S) \<approx>\<^sup>U \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)"
definition iADDIr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iADDIr\<^sup>a")
  where "iADDIr\<^sup>a \<phi> \<equiv> \<forall>S. let U=\<^bold>\<Or>S in (\<phi>(\<^bold>\<Or>S) \<preceq>\<^sup>U \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)" 
definition iADDIr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iADDIr\<^sup>b")
  where "iADDIr\<^sup>b \<phi> \<equiv> \<forall>S. let U=\<^bold>\<Or>S in (\<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk> \<preceq>\<^sup>U \<phi>(\<^bold>\<Or>S))" 

definition inADDIr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("inADDIr")
  where "inADDIr \<phi>  \<equiv> \<forall>S. let U=\<^bold>\<Or>S in (\<phi>(\<^bold>\<Or>S) \<approx>\<^sup>U \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>)"
definition inADDIr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("inADDIr\<^sup>a")
  where "inADDIr\<^sup>a \<phi> \<equiv> \<forall>S. let U=\<^bold>\<Or>S in (\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<preceq>\<^sup>U \<phi>(\<^bold>\<Or>S))"  
definition inADDIr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("inADDIr\<^sup>b")
  where "inADDIr\<^sup>b \<phi> \<equiv> \<forall>S. let U=\<^bold>\<Or>S in (\<phi>(\<^bold>\<Or>S) \<preceq>\<^sup>U \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>)" 

declare iADDIr_def[cond] iADDIr_a_def[cond] iADDIr_b_def[cond]
        inADDIr_def[cond] inADDIr_a_def[cond] inADDIr_b_def[cond]

definition iMULTr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iMULTr")
  where "iMULTr \<phi>  \<equiv> \<forall>S. let U=\<^bold>\<And>S in (\<phi>(\<^bold>\<And>S) \<approx>\<^sub>U \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>)"
definition iMULTr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iMULTr\<^sup>a")
  where "iMULTr\<^sup>a \<phi> \<equiv> \<forall>S. let U=\<^bold>\<And>S in (\<phi>(\<^bold>\<And>S) \<preceq>\<^sub>U \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>)"
definition iMULTr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("iMULTr\<^sup>b")
  where "iMULTr\<^sup>b \<phi> \<equiv> \<forall>S. let U=\<^bold>\<And>S in (\<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<preceq>\<^sub>U \<phi>(\<^bold>\<And>S))"

definition inMULTr::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("inMULTr")
  where "inMULTr \<phi>  \<equiv> \<forall>S. let U=\<^bold>\<And>S in (\<phi>(\<^bold>\<And>S) \<approx>\<^sub>U \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)"
definition inMULTr_a::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("inMULTr\<^sup>a")
  where "inMULTr\<^sup>a \<phi> \<equiv> \<forall>S. let U=\<^bold>\<And>S in (\<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk> \<preceq>\<^sub>U \<phi>(\<^bold>\<And>S))"
definition inMULTr_b::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" ("inMULTr\<^sup>b")
  where "inMULTr\<^sup>b \<phi> \<equiv> \<forall>S. let U=\<^bold>\<And>S in (\<phi>(\<^bold>\<And>S) \<preceq>\<^sub>U \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>)"

declare iMULTr_def[cond] iMULTr_a_def[cond] iMULTr_b_def[cond]
        inMULTr_def[cond] inMULTr_a_def[cond] inMULTr_b_def[cond]

lemma iADDI_MULT_dual1: "iADDIr\<^sup>a \<phi> = iMULTr\<^sup>b \<phi>\<^sup>d" unfolding cond by (smt (z3) BA_cmpl_equ BA_cp BA_deMorgan2 dual_invol iDM_a iDM_b im_prop1 op_dual_def setequ_ext subset_in_char subset_out_char)
lemma iADDI_MULT_dual2: "iADDIr\<^sup>b \<phi> = iMULTr\<^sup>a \<phi>\<^sup>d" unfolding cond by (smt (z3) BA_cmpl_equ BA_cp BA_deMorgan2 dual_invol iDM_a iDM_b im_prop1 op_dual_def setequ_ext subset_in_char subset_out_char)

(*TODO: fix kernel reconstruction for the following:*)
lemma "iADDI\<^sup>a \<phi> \<longrightarrow> inADDIr\<^sup>a \<phi>\<^sup>f\<^sup>p" oops
lemma "EXPN \<phi> \<longrightarrow> (iADDI\<^sup>a \<phi> = inADDIr\<^sup>a \<phi>\<^sup>f\<^sup>p)" oops
lemma "iADDI\<^sup>a \<phi> \<longrightarrow> iADDIr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>c" oops
lemma "EXPN \<phi> \<longrightarrow> (iADDI\<^sup>a \<phi> = iADDIr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>c)" oops

lemma "iADDI\<^sup>b \<phi> \<longrightarrow> inADDIr\<^sup>b \<phi>\<^sup>f\<^sup>p" oops
lemma "EXPN \<phi> \<longrightarrow> (iADDI\<^sup>b \<phi> = inADDIr\<^sup>b \<phi>\<^sup>f\<^sup>p)" oops
lemma "iADDI\<^sup>b \<phi> \<longrightarrow> iADDIr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>c" oops
lemma "EXPN \<phi> \<longrightarrow> (iADDI\<^sup>b \<phi> = iADDIr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>c)" oops

lemma "iMULT\<^sup>a \<phi> \<longrightarrow> iMULTr\<^sup>a \<phi>\<^sup>f\<^sup>p" oops 
lemma "CNTR \<phi> \<longrightarrow> (iMULT\<^sup>a \<phi> = iMULTr\<^sup>a \<phi>\<^sup>f\<^sup>p)"  oops
lemma "iMULT\<^sup>a \<phi> \<longrightarrow> inMULTr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>c" oops
lemma "CNTR \<phi> \<longrightarrow> (iMULT\<^sup>a \<phi> = inMULTr\<^sup>a \<phi>\<^sup>f\<^sup>p\<^sup>c)" oops

lemma "iMULT\<^sup>b \<phi> \<longrightarrow> iMULTr\<^sup>b \<phi>\<^sup>f\<^sup>p" oops 
lemma "CNTR \<phi> \<longrightarrow> (iMULT\<^sup>b \<phi> = iMULTr\<^sup>b \<phi>\<^sup>f\<^sup>p)"  oops
lemma "iMULT\<^sup>b \<phi> \<longrightarrow> inMULTr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>c" oops
lemma "CNTR \<phi> \<longrightarrow> (iMULT\<^sup>b \<phi> = inMULTr\<^sup>b \<phi>\<^sup>f\<^sup>p\<^sup>c)" oops

end