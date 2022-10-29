theory conditions_fixedpoint_infinitary
  imports conditions_fixedpoint_simple conditions_positive_infinitary conditions_negative_infinitary
begin                        

(**We define and interrelate infinitary variants for some previously introduced
 axiomatic conditions on operators.*)
definition iXYZ::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("iXYZ")
  where "iXYZ \<phi>   \<equiv> \<forall>S. \<^bold>\<Or>S \<^bold>\<or> \<phi>(\<^bold>\<Or>S) \<approx> \<^bold>\<Or>S \<^bold>\<or> \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>"
definition iXYZ_a::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("iXYZ\<^sup>a")
  where "iXYZ\<^sup>a \<phi>  \<equiv> \<forall>S. \<^bold>\<Or>S \<^bold>\<or> \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<preceq> \<^bold>\<Or>S \<^bold>\<or> \<phi>(\<^bold>\<Or>S)"  
definition iXYZ_b::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("iXYZ\<^sup>b")
  where "iXYZ\<^sup>b \<phi>  \<equiv> \<forall>S. \<^bold>\<Or>S \<^bold>\<or> \<phi>(\<^bold>\<Or>S) \<preceq> \<^bold>\<Or>S \<^bold>\<or> \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>" 

declare iXYZ_def[cond] iXYZ_a_def[cond] iXYZ_b_def[cond]

definition iXYZd::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("iXYZd")
  where "iXYZd \<phi>  \<equiv> \<forall>S. \<^bold>\<And>S \<^bold>\<and> \<phi>(\<^bold>\<And>S) \<approx> \<^bold>\<And>S \<^bold>\<and> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>"
definition iXYZd_a::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("iXYZd\<^sup>a")
  where "iXYZd\<^sup>a \<phi> \<equiv> \<forall>S. \<^bold>\<And>S \<^bold>\<and> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk> \<preceq> \<^bold>\<And>S \<^bold>\<and> \<phi>(\<^bold>\<And>S)"
definition iXYZd_b::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("iXYZd\<^sup>b")
  where "iXYZd\<^sup>b \<phi> \<equiv> \<forall>S. \<^bold>\<And>S \<^bold>\<and> \<phi>(\<^bold>\<And>S) \<preceq> \<^bold>\<And>S \<^bold>\<and> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>"

declare iXYZd_def[cond] iXYZd_a_def[cond] iXYZd_b_def[cond]

lemma iXYZ_duala: "iXYZ\<^sup>a \<phi> \<longrightarrow> iXYZd\<^sup>b \<phi>\<^sup>d" unfolding cond 
  by (metis BA_cmpl_equ BA_cp BA_deMorgan2 L5 iDM_a iDM_b im_prop3 op_dual_def setequ_ext)

lemma iXYZ_dualb: "iXYZd\<^sup>b \<phi> \<longrightarrow> iXYZ\<^sup>a \<phi>\<^sup>d" unfolding cond 
  by (metis BA_cp BA_deMorgan1 BA_dn iDM_a iDM_b im_prop3 op_dual_def setequ_ext)

lemma iconv1:  "iADDI\<^sup>a \<phi> \<longrightarrow> iXYZ\<^sup>a \<phi>\<^sup>f\<^sup>p" unfolding cond by (smt (z3) dimpl_def infimum_def join_def image_def op_fixpoint_def subset_def supremum_def)
lemma iconv2: "EXPN \<phi> \<Longrightarrow> iXYZ\<^sup>a \<phi>\<^sup>f\<^sup>p \<longrightarrow> iADDI\<^sup>a \<phi>" unfolding cond image_def conn2 conn order by (smt (verit))

lemma iconv3:  "iADDI\<^sup>b \<phi> \<longrightarrow> iXYZ\<^sup>b \<phi>\<^sup>f\<^sup>p" by (smt (verit, del_insts) dimpl_def iADDI_b_def iXYZ_b_def infimum_def join_def misc.image_def op_fixpoint_def subset_def supremum_def)
lemma iconv4: "EXPN \<phi> \<Longrightarrow> iXYZ\<^sup>b \<phi>\<^sup>f\<^sup>p \<longrightarrow> iADDI\<^sup>b \<phi>" unfolding cond by (smt (z3) dimpl_def infimum_def join_def image_def ofp_invol op_fixpoint_def subset_def supremum_def)

end