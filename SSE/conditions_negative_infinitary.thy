theory conditions_negative_infinitary
  imports conditions_negative boolean_algebra_infinitary
begin

(**We define and interrelate infinitary variants for some previously introduced
 axiomatic conditions on operators.*)

(**anti-distribution over infinite joins (suprema) or infinite anti-additivity (inADDI).*)
definition inADDI::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("inADDI")
  where "inADDI \<phi>  \<equiv> \<forall>S. \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<approx> \<phi>(\<^bold>\<Or>S)" 
definition inADDI_a::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("inADDI\<^sup>a")
  where "inADDI\<^sup>a \<phi> \<equiv> \<forall>S. \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk> \<preceq> \<phi>(\<^bold>\<Or>S)  " 
definition inADDI_b::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("inADDI\<^sup>b")
  where "inADDI\<^sup>b \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<Or>S) \<preceq> \<^bold>\<And>\<lbrakk>\<phi> S\<rbrakk>"
(**anti-Distribution over infinite meets (infima) or infinite anti-multiplicativity (inMULT).*)
definition inMULT::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("inMULT")
  where "inMULT \<phi>  \<equiv> \<forall>S. \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk> \<approx> \<phi>(\<^bold>\<And>S)" 
definition inMULT_a::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("inMULT\<^sup>a")
  where "inMULT\<^sup>a \<phi> \<equiv> \<forall>S. \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk> \<preceq> \<phi>(\<^bold>\<And>S)"
definition inMULT_b::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" ("inMULT\<^sup>b")
  where "inMULT\<^sup>b \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<And>S) \<preceq> \<^bold>\<Or>\<lbrakk>\<phi> S\<rbrakk>"

declare inADDI_def[cond] inADDI_a_def[cond] inADDI_b_def[cond]
        inMULT_def[cond] inMULT_a_def[cond] inMULT_b_def[cond]

lemma inADDI_char: "inADDI \<phi> = (inADDI\<^sup>a \<phi> \<and> inADDI\<^sup>b \<phi>)" unfolding cond using setequ_char by blast
lemma inMULT_char: "inMULT \<phi> = (inMULT\<^sup>a \<phi> \<and> inMULT\<^sup>b \<phi>)" unfolding cond using setequ_char by blast

(**nADDI-b and inADDI-b are in fact equivalent.*)
lemma inADDIb_equ: "inADDI\<^sup>b \<phi> = nADDI\<^sup>b \<phi>" proof -
  have lr: "inADDI\<^sup>b \<phi> \<Longrightarrow> nADDI\<^sup>b \<phi>" proof - (*prove as a one-liner by instantiating inADDI_b_def with S=(\<lambda>Z. Z=A \<or> Z=B)*)
  assume inaddib: "inADDI\<^sup>b \<phi>"
  { fix A::"'a \<sigma>" and B::"'a \<sigma>" (* for some reason Isabelle doesn't like other letters as type variable. Why?*)
    let ?S="\<lambda>Z. Z=A \<or> Z=B"
    have "\<^bold>\<Or>?S = A \<^bold>\<or> B" unfolding supremum_def join_def by blast
    hence p1: "\<phi>(\<^bold>\<Or>?S) = \<phi>(A \<^bold>\<or> B)" by simp
    have "\<lbrakk>\<phi> ?S\<rbrakk> = (\<lambda>Z. Z=(\<phi> A) \<or> Z=(\<phi> B))" unfolding image_def by metis
    hence p2: "\<^bold>\<And>\<lbrakk>\<phi> ?S\<rbrakk> = (\<phi> A) \<^bold>\<and> (\<phi> B)" unfolding infimum_def meet_def by auto
    have "\<phi>(\<^bold>\<Or>?S) \<preceq> \<^bold>\<And>\<lbrakk>\<phi> ?S\<rbrakk>" using inaddib inADDI_b_def by blast
    hence "\<phi>(A \<^bold>\<or> B) \<preceq> (\<phi> A) \<^bold>\<and> (\<phi> B)" using p1 p2 by simp
  } thus ?thesis by (simp add: nADDI_b_def) qed
  have rl: "nADDI\<^sup>b \<phi> \<Longrightarrow> inADDI\<^sup>b \<phi>" unfolding inADDI_b_def ANTI_nADDIb ANTI_def image_def
    by (smt (verit) glb_def inf_glb lower_bounds_def lub_def sup_lub upper_bounds_def)
  from lr rl show ?thesis by auto
qed
(**nMULT-a and inMULT-a are also equivalent.*)
lemma inMULTa_equ: "inMULT\<^sup>a \<phi> = nMULT\<^sup>a \<phi>" proof -
  have lr: "inMULT\<^sup>a \<phi> \<Longrightarrow> nMULT\<^sup>a \<phi>" proof - (*prove as a one-liner by instantiating inMULT_a_def with S=(\<lambda>Z. Z=A \<or> Z=B)*)
  assume inmulta: "inMULT\<^sup>a \<phi>"
  { fix A::"'a \<sigma>" and B::"'a \<sigma>"
    let ?S="\<lambda>Z. Z=A \<or> Z=B"
    have "\<^bold>\<And>?S = A \<^bold>\<and> B" unfolding infimum_def meet_def by blast
    hence p1: "\<phi>(\<^bold>\<And>?S) = \<phi>(A \<^bold>\<and> B)" by simp
    have "\<lbrakk>\<phi> ?S\<rbrakk> = (\<lambda>Z. Z=(\<phi> A) \<or> Z=(\<phi> B))" unfolding image_def by metis
    hence p2: "\<^bold>\<Or>\<lbrakk>\<phi> ?S\<rbrakk> = (\<phi> A) \<^bold>\<or> (\<phi> B)" unfolding supremum_def join_def by auto
    have "\<^bold>\<Or>\<lbrakk>\<phi> ?S\<rbrakk> \<preceq> \<phi>(\<^bold>\<And>?S)" using inmulta inMULT_a_def by blast    
    hence "(\<phi> A) \<^bold>\<or> (\<phi> B) \<preceq> \<phi>(A \<^bold>\<and> B)" using p1 p2 by simp
  } thus ?thesis by (simp add: nMULT_a_def) qed
  have rl: "nMULT\<^sup>a \<phi> \<Longrightarrow> inMULT\<^sup>a \<phi>" unfolding inMULT_a_def ANTI_nMULTa ANTI_def image_def
    by (smt (verit) glb_def inf_glb lower_bounds_def lub_def sup_lub upper_bounds_def)
  from lr rl show ?thesis by blast
qed

(**Thus we have that ANTI, nADDI-b/inADDI-b and nMULT-a/inMULT-a are all equivalent.*)
lemma ANTI_inADDIb: "inADDI\<^sup>b \<phi> = ANTI \<phi>" unfolding ANTI_nADDIb inADDIb_equ by simp
lemma ANTI_inMULTa: "inMULT\<^sup>a \<phi> = ANTI \<phi>" unfolding ANTI_nMULTa inMULTa_equ by simp


(**Below we prove several duality relationships between inADDI(a/b) and inMULT(a/b).*)

(**Duality between inMULT-a and inADDI-b (an easy corollary from the previous equivalence).*)
lemma inMULTa_inADDIb_dual1: "inMULT\<^sup>a \<phi> = inADDI\<^sup>b \<phi>\<^sup>d" by (simp add: nMULTa_nADDIb_dual1 inADDIb_equ inMULTa_equ)
lemma inMULTa_inADDIb_dual2: "inADDI\<^sup>b \<phi> = inMULT\<^sup>a \<phi>\<^sup>d" by (simp add: nMULTa_nADDIb_dual2 inADDIb_equ inMULTa_equ)
(**Duality between inADDI-a and inMULT-b.*)
lemma inADDIa_inMULTb_dual1: "inADDI\<^sup>a \<phi> = inMULT\<^sup>b \<phi>\<^sup>d" by (smt (z3) BA_cmpl_equ BA_cp dualcompl_invol inADDI_a_def iDM_a inMULT_b_def im_prop1 op_dual_def setequ_ext)
lemma inADDIa_inMULTb_dual2: "inMULT\<^sup>b \<phi> = inADDI\<^sup>a \<phi>\<^sup>d" by (simp add: dual_invol inADDIa_inMULTb_dual1)
(**Duality between inADDI and inMULT.*)
lemma inADDI_inMULT_dual1: "inADDI \<phi> = inMULT \<phi>\<^sup>d" using inADDI_char inADDIa_inMULTb_dual1 inMULT_char inMULTa_inADDIb_dual2 by blast
lemma inADDI_inMULT_dual2: "inMULT \<phi> = inADDI \<phi>\<^sup>d" by (simp add: dual_invol inADDI_inMULT_dual1)

(**In fact, infinite anti-additivity (anti-multiplicativity) entails (dual) anti-normality:*)
lemma inADDI_nNORM: "inADDI \<phi> \<longrightarrow> nNORM \<phi>" by (metis bottom_def inADDI_def inf_empty misc.image_def nNORM_def setequ_ext sup_empty)
lemma inMULT_nDNRM: "inMULT \<phi> \<longrightarrow> nDNRM \<phi>" by (simp add: inADDI_inMULT_dual2 inADDI_nNORM nNOR_dual2)

end