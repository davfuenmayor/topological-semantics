theory negation_fixedpoints
  imports frontier_algebra "../SSE/operation_negative_quantification"
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

section \<open>Frontier-based negation - Fixed-points\<close>

(**We define a paracomplete and a paraconsistent negation employing the interior and the closure operation
respectively. We explore the use of fixed-point predicates to recover some relevant properties of negation,
many of which cannot be readily recovered by just adding semantic conditions.
We take the frontier operator as primitive and explore which semantic conditions are minimally required.*)

definition neg_I::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>\<^sup>I")  where  "\<^bold>\<not>\<^sup>I \<phi> \<equiv> \<I>(\<^bold>\<midarrow>\<phi>)"
definition neg_C::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>\<^sup>C")  where  "\<^bold>\<not>\<^sup>C \<phi> \<equiv> \<C>(\<^bold>\<midarrow>\<phi>)"
declare neg_I_def[conn] neg_C_def[conn]

(**First, observe that all results obtained for fixed-point predicates extend to their associated operators.*)
lemma "\<forall>A. \<gamma>\<^sup>f\<^sup>p(A) \<^bold>\<and> \<phi>(A) \<^bold>\<preceq> \<psi>(A) \<Longrightarrow> \<forall>A. (fp \<gamma>)(A) \<longrightarrow> \<phi>(A) \<^bold>\<preceq> \<psi>(A)" unfolding conn by simp
lemma "\<forall>A B. \<gamma>\<^sup>f\<^sup>p(A) \<^bold>\<and> \<gamma>\<^sup>f\<^sup>p(B) \<^bold>\<and> (\<phi> A B) \<^bold>\<preceq> (\<psi> A B) \<Longrightarrow> \<forall>A B. (fp \<gamma>)(A) \<and> (fp \<gamma>)(B) \<longrightarrow> (\<phi> A B) \<^bold>\<preceq> (\<psi> A B)" unfolding conn by simp

(**Note: recall from previous results that if we have Fr(A) then we also have both Cl(A) and Br(A).
With this understanding we will tacitly assume the corresponding results for Fr(-) below.
Moreover, we obtained countermodels (using Nitpick) for all formulas featuring other combinations (not shown).*)


subsection \<open>'Explosion' (ECQ) and excluded middle (TND)\<close>

(**TND-I*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A. Cl(A) \<longrightarrow> TND\<^sup>A \<^bold>\<not>\<^sup>I" by (simp add: OpCldual conn)
(**ECQ_C*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A. Op(A) \<longrightarrow> ECQ\<^sup>A \<^bold>\<not>\<^sup>C" using Cl_fr_def Int_fr_def pF2 unfolding conn by fastforce


subsection \<open>Contraposition rules\<close>

(**CoPw-I*)
lemma "\<forall>A B. Br(\<^bold>\<midarrow>B) \<longrightarrow> CoPw\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" using Int_fr_def pB1 conn by auto
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Cl(A)  \<longrightarrow> CoPw\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" using Int_fr_def OpCldual conn by auto
(**CoPw-C*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Br(A) \<longrightarrow> CoPw\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" using pA2 pB2 pF2 unfolding conn by metis
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Op(B) \<longrightarrow> CoPw\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" using ClOpdual Cl_fr_def unfolding conn by auto

(**CoP1-I*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Cl(A) \<longrightarrow>  CoP1\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" using Int_fr_def OpCldual conn by auto
lemma "Fr_1b \<F> \<Longrightarrow> \<forall>A B. Op(B) \<longrightarrow>  CoP1\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" by (smt IF2 dEXP_def MONO_def monI conn)
lemma CoP1_I_rec: "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>A B. Br (\<^bold>\<midarrow>B) \<longrightarrow> CoP1\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" using IF3 dNOR_def Br_boundary unfolding conn by auto 
(**CoP1-C*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Op(B) \<longrightarrow> CoP1\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" using Int_fr_def pC2 pF2 unfolding conn by metis
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Br(A) \<longrightarrow> CoP1\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" using Br_fr_def Cl_fr_def pF2 unfolding conn by fastforce

(**CoP2-I*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Cl(A) \<longrightarrow> CoP2\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" using Int_fr_def OpCldual unfolding conn by auto
lemma "\<forall>A B. Br (\<^bold>\<midarrow>B) \<longrightarrow> CoP2\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" by (simp add: pI1 conn)
(**CoP2-C*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Op(B) \<longrightarrow>  CoP2\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" using Cl_fr_def Int_fr_def pF2 unfolding conn by fastforce
lemma "Fr_6 \<F> \<Longrightarrow> \<forall>A B. Cl(A) \<longrightarrow>  CoP2\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" by (smt Cl_fr_def MONO_def monC conn)
lemma "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>A B. Br(A) \<longrightarrow> CoP2\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" using CoP1_I_rec Disj_IF pA2 pF2 pF3 unfolding conn by smt

(**CoP3-I*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Cl(A) \<longrightarrow> CoP3\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" by (metis Disj_I ICdual' compl_def dual_def eq_ext' meet_def neg_I_def)
(**CoP3-C*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Op(B) \<longrightarrow> CoP3\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" by (metis Disj_I ICdual compl_def dual_def eq_ext' meet_def neg_C_def)

(**XCoP-I*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Cl(A) \<longrightarrow>  XCoP\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" using Fr_2_def pA1 pA2 pF1 unfolding conn by metis
lemma "\<forall>A B. Br(\<^bold>\<midarrow>B) \<longrightarrow>  XCoP\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" using IB_rel Int_br_def diff_def eq_ext' conn by fastforce
(**XCoP-C*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Op(B) \<longrightarrow> XCoP\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" by (metis ClOpdual compl_def diff_def meet_def neg_C_def pA2)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B.  \<forall>A B. Br(A) \<longrightarrow> XCoP\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" using Cl_fr_def compl_def join_def neg_C_def pF3 by fastforce


subsection \<open>Double negation introduction/elimination\<close>

(**DNI-I*)
lemma "Fr_1b \<F> \<Longrightarrow> \<forall>A. Op(A) \<longrightarrow> DNI\<^sup>A \<^bold>\<not>\<^sup>I" using MONO_def monI pA1 unfolding conn by smt
lemma "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>A. Br (\<^bold>\<midarrow>A) \<longrightarrow> DNI\<^sup>A \<^bold>\<not>\<^sup>I" using CoP1_I_rec by simp
(**DNI-C*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A. Op(A) \<longrightarrow> DNI\<^sup>A \<^bold>\<not>\<^sup>C" using Cl_fr_def Int_fr_def pF2 unfolding conn by fastforce

(**DNE-I*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A. Cl(A) \<longrightarrow> DNE\<^sup>A \<^bold>\<not>\<^sup>I" by (simp add: Cl_fr_def Fr_2_def Int_fr_def conn)
(**DNE-C*)
lemma "Fr_6 \<F> \<Longrightarrow> \<forall>A. Cl(A) \<longrightarrow> DNE\<^sup>A \<^bold>\<not>\<^sup>C" by (smt MONO_def monC pC2 conn)
lemma "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>A. Br(A) \<longrightarrow> DNE\<^sup>A \<^bold>\<not>\<^sup>C" using CoP1_I_rec Disj_IF pA2 pF2 pF3 unfolding conn by smt


subsection \<open>De Morgan laws\<close>

(**DM1-I*)
lemma "Fr_1b \<F> \<Longrightarrow> \<forall>A B. DM1\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" by (smt MONO_def monI conn)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Cl(A) \<and> Cl(B) \<longrightarrow> DM1\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" using pF2 pI2 conn by fastforce
(**DM1-C*)
lemma "Fr_6 \<F> \<Longrightarrow> \<forall>A B. DM1\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" by (smt MONO_def monC conn)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Br(A) \<and> Br(B) \<longrightarrow> DM1\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" using CF2 EXP_def pF2 pF3 unfolding conn by metis

(**DM2-I*)
lemma "Fr_1b \<F> \<Longrightarrow> \<forall>A B. DM2\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" by (smt MONO_def monI conn)
lemma "\<forall>A B. Br(\<^bold>\<midarrow>A) \<and> Br(\<^bold>\<midarrow>B) \<longrightarrow> DM2\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" using Int_fr_def pB1 conn by auto
(**DM2-C*)
lemma "Fr_6 \<F> \<Longrightarrow> \<forall>A B. DM2\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" by (smt MONO_def monC conn)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Op(A) \<and> Op(B) \<longrightarrow> DM2\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" using CF2 ClOpdual EXP_def unfolding conn by auto

(**DM3-I*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Cl(A) \<and> Cl(B) \<longrightarrow> DM3\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" using Int_fr_def pF2 unfolding conn by fastforce 
(**DM3-C*)
lemma "Fr_1a \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> \<forall>A B. DM3\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" using Cl_fr_def Fr_1a_def pF2 unfolding conn by metis
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Br(A) \<and> Br(B) \<longrightarrow> DM3\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" using Cl_fr_def pF3 unfolding conn by fastforce

(**DM4-I*)
lemma "Fr_1a \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> \<forall>A B. DM4\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" using ADDI_a_def Br_fr_def CF1a Int_fr_def pC1 unfolding conn by (metis (full_types))
lemma "\<forall>A B. Br(\<^bold>\<midarrow>A) \<and> Br(\<^bold>\<midarrow>B) \<longrightarrow> DM4\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>I" using Int_fr_def pB1 conn by auto
(**DM4-C*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Op(A) \<and> Op(B) \<longrightarrow> DM4\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" using Cl_fr_def Int_fr_def pF2 unfolding conn by (metis (full_types))
lemma "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>A B. Fr(A) \<and> Fr(B) \<longrightarrow> DM4\<^sup>A\<^sup>B \<^bold>\<not>\<^sup>C" using Cl_fr_def Fr_join_closed Fr_2_def compl_def join_def neg_C_def by auto


subsection \<open>Local contraposition axioms\<close>

(**lCoPw-I*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Cl(A) \<longrightarrow> lCoPw\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" using Int_fr_def OpCldual unfolding conn by auto
lemma "\<forall>A B. Br(\<^bold>\<midarrow>B) \<longrightarrow> lCoPw\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" by (simp add: pI1 conn)
(**lCoPw-C*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Op(B) \<longrightarrow> lCoPw\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C" using Cl_fr_def Int_fr_def pF2 unfolding conn by fastforce
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Br(A) \<longrightarrow> lCoPw\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C" by (simp add: pC1 conn)

(**lCoP1-I*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Cl(A) \<longrightarrow> lCoP1\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" using Int_fr_def OpCldual unfolding conn by auto
(**lCoP1-C*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Op(B) \<longrightarrow> lCoP1\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C" using Cl_fr_def Int_fr_def pF2 unfolding conn by fastforce
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Br(A) \<longrightarrow> lCoP1\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C" by (simp add: pC1 conn)

(**lCoP2-I*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Cl(A) \<longrightarrow> lCoP2\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" using Int_fr_def OpCldual unfolding conn by auto
lemma "\<forall>A B. Br(\<^bold>\<midarrow>B) \<longrightarrow> lCoP2\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" by (simp add: pI1 conn)
(**lCoP2-C*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Op(B) \<longrightarrow> lCoP2\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C" using Cl_fr_def Int_fr_def pF2 unfolding conn by fastforce

(**lCoP3-I*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Cl(A) \<longrightarrow> lCoP3\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" using Int_fr_def OpCldual unfolding conn by auto
(**lCoP3-C*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Op(B) \<longrightarrow> lCoP3\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C" using Cl_fr_def Int_fr_def pF2 unfolding conn by fastforce


subsection \<open>Disjunctive syllogism\<close>

(**DS1-I*)
lemma "\<forall>A B. DS1\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" by (simp add: Int_fr_def conn)
(**DS1-C*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B.  Op(A) \<longrightarrow> DS1\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C" using Cl_fr_def Int_fr_def pF2 unfolding conn by fastforce

(**DS2-I*)
lemma "Fr_2 \<F> \<Longrightarrow> \<forall>A B. Cl(A) \<longrightarrow> DS2\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" using OpCldual unfolding conn by auto
(**DS2-C*)
lemma "\<forall>A B. DS2\<^sup>A\<^sup>B(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C"  using Cl_fr_def unfolding conn by auto

end