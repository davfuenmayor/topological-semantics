theory negation_conditions
  imports frontier_algebra "../SSE/operation_negative_quantification"
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3] (*default settings*)
(*(We rename (classical) meta-logical negation to avoid terminological confusion)*)
abbreviation cneg::"bool\<Rightarrow>bool" ("\<sim>_" [40]40) where "\<sim>\<phi> \<equiv> \<not>\<phi>" 

section \<open>Frontier-based negation - Semantic conditions\<close>

(**We define a paracomplete and a paraconsistent negation employing the interior and closure operation resp.
We take the frontier operator as primitive and explore which semantic conditions are minimally required
to obtain some relevant properties of negation.*)

definition neg_I::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>\<^sup>I")  where  "\<^bold>\<not>\<^sup>I \<phi> \<equiv> \<I>(\<^bold>\<midarrow>\<phi>)"
definition neg_C::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>\<^sup>C")  where  "\<^bold>\<not>\<^sup>C \<phi> \<equiv> \<C>(\<^bold>\<midarrow>\<phi>)"
declare neg_I_def[conn] neg_C_def[conn]


subsection \<open>'Explosion' (ECQ) and excluded middle (TND)\<close>

(**TND*)
lemma "\<FF> \<F> \<Longrightarrow> TNDm \<^bold>\<not>\<^sup>I" nitpick oops (*still not recovering minimally weak TND*)
lemma TND_C: "TND \<^bold>\<not>\<^sup>C" by (simp add: pC2 Defs conn) (*TND valid in general*)

(**ECQ*)
lemma ECQ_I: "ECQ \<^bold>\<not>\<^sup>I" by (simp add: pI2 Defs conn) (*ECQ valid in general*)
lemma "\<FF> \<F> \<Longrightarrow> ECQm \<^bold>\<not>\<^sup>C" nitpick oops (*still not recovering minimally weak ECQ*)

(**Relations between LNC and different ECQ variants.*)
lemma "ECQ \<^bold>\<not>\<^sup>C \<longrightarrow>  LNC \<^bold>\<not>\<^sup>C" by (simp add: pC2 Defs conn)
lemma ECQw_LNC: "ECQw \<^bold>\<not>\<^sup>C \<longrightarrow>  LNC \<^bold>\<not>\<^sup>C" by (smt ECQw_def LNC_def pC2 conn)
lemma ECQm_LNC: "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> ECQm \<^bold>\<not>\<^sup>C \<longrightarrow> LNC \<^bold>\<not>\<^sup>C" using Cl_fr_def Fr_1_def pF2 unfolding Defs conn by metis
lemma "\<FF> \<F> \<Longrightarrow> LNC \<^bold>\<not>\<^sup>C \<longrightarrow>  ECQm \<^bold>\<not>\<^sup>C" nitpick oops
lemma "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow>  LNC \<^bold>\<not>\<^sup>I" using ECQ_I ECQ_def IF3 LNC_def dNOR_def unfolding conn by auto

(**Below we show that enforcing all conditions on the frontier operator still leaves room
for both boldly paraconsistent and paracomplete models. We use Nitpick to generate a non-trivial 
model (here a set algebra with 8 elements).*)
lemma "\<FF> \<F> \<and> \<sim>ECQm \<^bold>\<not>\<^sup>C" nitpick[satisfy,card w=3] oops (*boldly paraconsistent model found*)
lemma "\<FF> \<F> \<and> \<sim>TNDm \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops (*boldly paracomplete model found*)


subsection \<open>Modus tollens (MT)\<close>

(**MT-I*)
lemma MT0_I: "Fr_1b \<F> \<Longrightarrow> MT0 \<^bold>\<not>\<^sup>I"  unfolding Defs by (smt MONO_def compl_def monI neg_I_def top_def)
lemma MT1_I: "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> MT1 \<^bold>\<not>\<^sup>I" unfolding Defs by (metis MONO_def monI IF3 Int_fr_def compl_def dNOR_def diff_def neg_I_def top_def)
lemma "\<FF> \<F> \<Longrightarrow> MT2 \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> MT2 \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "\<sim>TNDm \<^bold>\<not>\<^sup>I \<and> Fr_1a \<F> \<and> Fr_2 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> MT2 \<^bold>\<not>\<^sup>I" nitpick[satisfy] oops
lemma "\<sim>TNDm \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> MT2 \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "\<sim>TNDm \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> MT2 \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "\<FF> \<F> \<Longrightarrow> MT3 \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma "\<sim>TNDm \<^bold>\<not>\<^sup>I \<and> Fr_1a \<F> \<and> Fr_2 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> MT3 \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "\<sim>TNDm \<^bold>\<not>\<^sup>I \<and> MT0 \<^bold>\<not>\<^sup>I \<and> MT1 \<^bold>\<not>\<^sup>I \<and> MT2 \<^bold>\<not>\<^sup>I \<and> MT3 \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
(**MT-C*)
lemma "Fr_2 \<F> \<Longrightarrow> MT0 \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma MT0_C: "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> MT0 \<^bold>\<not>\<^sup>C" unfolding Defs by (smt ICdual MONO_def PF6 compl_def monC neg_C_def top_def)
lemma MT1_C: "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> MT1 \<^bold>\<not>\<^sup>C" unfolding Defs by (smt Cl_fr_def Fr_6_def PF6 conn)
lemma "\<FF> \<F> \<Longrightarrow> MT2 \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma "\<sim>ECQm \<^bold>\<not>\<^sup>C \<and> \<FF> \<F> \<and> MT2 \<^bold>\<not>\<^sup>C" nitpick[satisfy,card w=3] oops (*model found*)
lemma MT3_C: "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> MT3 \<^bold>\<not>\<^sup>C" unfolding Defs using MONO_def monI by (metis ClOpdual IF3 compl_def dNOR_def diff_def neg_C_def pA2 top_def)
lemma "\<sim>ECQm \<^bold>\<not>\<^sup>C \<and> MT0 \<^bold>\<not>\<^sup>C \<and> MT1 \<^bold>\<not>\<^sup>C \<and> MT2 \<^bold>\<not>\<^sup>C \<and> MT3 \<^bold>\<not>\<^sup>C" nitpick[satisfy,card w=3] oops


subsection \<open>Contraposition rules (CoP)\<close>

(**CoPw-I*)
lemma "CoPw \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma CoPw_I: "Fr_1b \<F> \<Longrightarrow> CoPw \<^bold>\<not>\<^sup>I" unfolding Defs conn by (metis (no_types, lifting) MONO_def monI)
(**CoPw-C*)
lemma "CoPw \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma CoPw_C: "Fr_6 \<F> \<Longrightarrow> CoPw \<^bold>\<not>\<^sup>C" by (smt CoPw_def MONO_def monC conn)

(**We can indeed prove that XCoP is entailed by CoP1 (CoP2) in the particular case of a closure- (interior-)based negation.*)
lemma CoP1_XCoP: "CoP1 \<^bold>\<not>\<^sup>C \<longrightarrow>  XCoP \<^bold>\<not>\<^sup>C" by (metis XCoP_def2 CoP1_def CoP1_def2 DM2_CoPw DM2_def ECQw_def TND_C TND_def TNDw_def top_def)
lemma CoP2_XCoP: "CoP2 \<^bold>\<not>\<^sup>I \<longrightarrow>  XCoP \<^bold>\<not>\<^sup>I" by (smt XCoP_def2 CoP2_DM3 CoP2_def2 CoPw_def DM3_def DNE_def ECQ_I ECQ_def ECQw_def TNDw_def bottom_def join_def)

(**CoP1-I*)
lemma "\<FF> \<F> \<Longrightarrow> CoP1 \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma "\<sim>TNDm \<^bold>\<not>\<^sup>I \<and> \<FF> \<F> \<and> CoP1 \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
(**CoP1-C*)
lemma "\<FF> \<F> \<Longrightarrow> CoP1 \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma "\<sim>ECQ \<^bold>\<not>\<^sup>C \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> CoP1 \<^bold>\<not>\<^sup>C" nitpick[satisfy,card w=3] oops
lemma "CoP1 \<^bold>\<not>\<^sup>C \<longrightarrow> ECQm \<^bold>\<not>\<^sup>C" using XCoP_def2 CoP1_XCoP ECQm_def ECQw_def by blast

(**CoP2-I*)
lemma "\<FF> \<F> \<Longrightarrow> CoP2 \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> CoP2 \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> CoP2 \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "CoP2 \<^bold>\<not>\<^sup>I \<longrightarrow> TNDm \<^bold>\<not>\<^sup>I" using XCoP_def2 CoP2_XCoP TNDm_def TNDw_def by auto
(**CoP2-C*)
lemma "\<FF> \<F> \<Longrightarrow> CoP2 \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma "\<sim>ECQm \<^bold>\<not>\<^sup>C \<and> \<FF> \<F> \<and> CoP2 \<^bold>\<not>\<^sup>C" nitpick[satisfy,card w=3] oops

(**CoP3-I*)
lemma "\<FF> \<F> \<Longrightarrow> CoP3 \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> CoP3 \<^bold>\<not>\<^sup>I" (*nitpick[satisfy]*) oops (*cannot find (finite) models*)
(**CoP3-C*)
lemma "\<FF> \<F> \<Longrightarrow> CoP3 \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma "\<sim>ECQ \<^bold>\<not>\<^sup>C \<and> CoP3 \<^bold>\<not>\<^sup>C" (*nitpick[satisfy]*) oops (*cannot find (finite) models*)

(**XCoP-I*)
lemma "\<FF> \<F> \<Longrightarrow> XCoP \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> XCoP \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> XCoP \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "XCoP \<^bold>\<not>\<^sup>I \<longrightarrow> TNDm \<^bold>\<not>\<^sup>I" by (simp add: XCoP_def2 TNDm_def TNDw_def)
(**XCoP-C*)
lemma "\<FF> \<F> \<Longrightarrow> XCoP \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma "\<sim>ECQ \<^bold>\<not>\<^sup>C \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> XCoP \<^bold>\<not>\<^sup>C" nitpick[satisfy,card w=3] oops
lemma "XCoP \<^bold>\<not>\<^sup>C \<longrightarrow> ECQm \<^bold>\<not>\<^sup>C" by (simp add: XCoP_def2 ECQm_def ECQw_def)


subsection \<open>Double negation introduction/elimination (DNI/DNE)\<close>

(**DNI-I*)
lemma "\<FF> \<F> \<Longrightarrow> DNI \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma "\<sim>TNDm \<^bold>\<not>\<^sup>I \<and> \<FF> \<F> \<and> DNI \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
(**DNI-C*)
lemma "\<FF> \<F> \<Longrightarrow> DNI \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma "\<sim>ECQ \<^bold>\<not>\<^sup>C \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> DNI \<^bold>\<not>\<^sup>C" nitpick[satisfy,card w=3] oops
lemma "\<sim>ECQm \<^bold>\<not>\<^sup>C \<and> Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> DNI \<^bold>\<not>\<^sup>C" nitpick[satisfy,card w=3] oops
lemma "\<sim>ECQm \<^bold>\<not>\<^sup>C \<and> Fr_2 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> DNI \<^bold>\<not>\<^sup>C" nitpick[satisfy,card w=3] oops

(**DNE-I*)
lemma "\<FF> \<F> \<Longrightarrow> DNE \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> DNE \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> DNE \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "\<sim>TNDm \<^bold>\<not>\<^sup>I \<and> Fr_2 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> DNE \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "\<sim>TND \<^bold>\<not>\<^sup>I  \<and> DNE \<^bold>\<not>\<^sup>I \<and> DNI \<^bold>\<not>\<^sup>I" (*nitpick[satisfy]*) oops (*cannot find (finite) models*)
(**DNE-C*)
lemma "\<FF> \<F> \<Longrightarrow> DNE \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma "\<sim>ECQm \<^bold>\<not>\<^sup>C \<and> \<FF> \<F> \<and> DNE \<^bold>\<not>\<^sup>C" nitpick[satisfy,card w=3] oops
lemma "\<sim>ECQ \<^bold>\<not>\<^sup>C  \<and> DNE \<^bold>\<not>\<^sup>C \<and> DNI \<^bold>\<not>\<^sup>C" (*nitpick[satisfy]*) oops (*cannot find (finite) models*)


subsection \<open>Normality (negative) and its dual (nNor/nDNor)\<close>

(**nNor-I*) 
lemma "nNor \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma nNor_I: "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> nNor \<^bold>\<not>\<^sup>I"  using IF3 dNOR_def unfolding Defs conn by auto
lemma "\<sim>TNDm \<^bold>\<not>\<^sup>I \<and> \<FF> \<F> \<and> nNor \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
(**nNor-C*) 
lemma nNor_C: "nNor \<^bold>\<not>\<^sup>C" unfolding Cl_fr_def Defs conn by simp

(**nDNor-I*) 
lemma nDNor_I: "nDNor \<^bold>\<not>\<^sup>I" unfolding Int_fr_def Defs conn by simp
(**nDNor-C*) 
lemma "nDNor \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma nDNor_C: "Fr_3 \<F> \<Longrightarrow> nDNor \<^bold>\<not>\<^sup>C" using pC2 NOR_def unfolding Defs conn by simp
lemma "\<sim>ECQm \<^bold>\<not>\<^sup>C \<and> \<FF> \<F> \<and> nDNor \<^bold>\<not>\<^sup>C" nitpick[satisfy,card w=3] oops


subsection \<open>De Morgan laws\<close>

(**DM1/2 (see CoPw)*)

(**DM3-I*)
lemma "\<FF> \<F> \<Longrightarrow> DM3 \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> DM3 \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> DM3 \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "\<sim>TNDm \<^bold>\<not>\<^sup>I \<and> DM3 \<^bold>\<not>\<^sup>I" (*nitpick[satisfy]*) oops (*cannot find (finite) models*)
(**DM3-C*)
lemma "DM3 \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma DM3_C: "Fr_1a \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> DM3 \<^bold>\<not>\<^sup>C" using  DM3_def Fr_1a_def pA2 pF2 unfolding conn by smt
lemma "\<sim>ECQm \<^bold>\<not>\<^sup>C \<and> \<FF> \<F> \<and> DM3 \<^bold>\<not>\<^sup>C" nitpick[satisfy,card w=3] oops

(**DM4-I*)
lemma "DM4 \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma DM4_I: "Fr_1a \<F> \<Longrightarrow> DM4 \<^bold>\<not>\<^sup>I" using ADDI_a_def Cl_fr_def DM4_def IC1b IF1b dual_def unfolding conn by smt
lemma "\<sim>TNDm \<^bold>\<not>\<^sup>I \<and> \<FF> \<F> \<and> DM4 \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
(**DM4-C*)
lemma "\<FF> \<F> \<Longrightarrow> DM4 \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma "\<sim>ECQ \<^bold>\<not>\<^sup>C \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> DM4 \<^bold>\<not>\<^sup>C" nitpick[satisfy,card w=3] oops
lemma "\<sim>ECQm \<^bold>\<not>\<^sup>C \<and> DM4 \<^bold>\<not>\<^sup>C" (*nitpick[satisfy]*) oops (*cannot find (finite) models*)

(**iDM1/2 (see CoPw)*)

(**iDM3-I*)
lemma "\<FF> \<F> \<Longrightarrow> Fr_inf \<F> \<Longrightarrow> iDM3 \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> iDM3 \<^bold>\<not>\<^sup>I" nitpick[satisfy] oops
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> iDM3 \<^bold>\<not>\<^sup>I" nitpick[satisfy] oops
lemma "\<sim>TNDm \<^bold>\<not>\<^sup>I \<and> iDM3 \<^bold>\<not>\<^sup>I" (*nitpick[satisfy]*) oops (*cannot find (finite) models*)
lemma "iDM3 \<^bold>\<not>\<^sup>I \<longrightarrow> TNDm \<^bold>\<not>\<^sup>I" unfolding Defs oops (*TODO*)
(**iDM3-C*)
lemma "iDM3 \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma iDM3_C: "Fr_2 \<F> \<Longrightarrow> Fr_inf \<F> \<Longrightarrow> iDM3 \<^bold>\<not>\<^sup>C" unfolding Defs by (metis (full_types) CF_inf Ra_restr_ex dom_compl_def iADDI_a_def iDM_a neg_C_def)
(**iDM4-I*)
lemma "iDM4 \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma iDM4_I: "Fr_inf \<F> \<Longrightarrow> iDM4 \<^bold>\<not>\<^sup>I" unfolding Defs by (metis IF_inf Ra_restr_all dom_compl_def iDM_b iMULT_b_def neg_I_def)
(**iDM4-C*)
lemma "\<FF> \<F> \<Longrightarrow> Fr_inf \<F> \<Longrightarrow> iDM4 \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma "\<sim>ECQ \<^bold>\<not>\<^sup>C \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> iDM4 \<^bold>\<not>\<^sup>C" nitpick[satisfy] oops
lemma "\<sim>ECQm \<^bold>\<not>\<^sup>C \<and> iDM4 \<^bold>\<not>\<^sup>C" (*nitpick[satisfy]*) oops (*cannot find (finite) models*)
lemma "iDM4 \<^bold>\<not>\<^sup>C \<longrightarrow> ECQm \<^bold>\<not>\<^sup>C" unfolding Defs oops (*TODO*)


subsection \<open>Contraposition (local) axioms (lCoP)\<close>

(**lCoPw-I*)
lemma "\<FF> \<F> \<Longrightarrow> lCoPw(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> lCoPw(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> lCoPw(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "lCoPw(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I \<longrightarrow> TNDm \<^bold>\<not>\<^sup>I" by (simp add: XCoP_def2 TNDm_def TNDw_def lCoPw_XCoP)
(**lCoPw-C*)
lemma "\<FF> \<F> \<Longrightarrow> lCoPw(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma "\<sim>ECQ \<^bold>\<not>\<^sup>C \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> lCoPw(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C" nitpick[satisfy,card w=3] oops
lemma "lCoPw(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C \<longrightarrow> ECQm \<^bold>\<not>\<^sup>C" by (simp add: XCoP_def2 ECQm_def ECQw_def lCoPw_XCoP)

(**lCoP1-I*)
lemma "\<FF> \<F> \<Longrightarrow> lCoP1(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma "lCoP1(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I \<longrightarrow> TND \<^bold>\<not>\<^sup>I" by (simp add: lCoP1_TND)
(**lCoP1-C*)
lemma "\<FF> \<F> \<Longrightarrow> lCoP1(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma "\<sim>ECQ \<^bold>\<not>\<^sup>C \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> lCoP1(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C" nitpick[satisfy,card w=3] oops
lemma "lCoP1(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C \<longrightarrow> ECQm \<^bold>\<not>\<^sup>C" by (simp add: XCoP_def2 ECQm_def ECQw_def lCoP1_def2 lCoPw_XCoP)

(**lCoP2-I*)
lemma "\<FF> \<F> \<Longrightarrow> lCoP2(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> lCoP2(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "\<sim>TND \<^bold>\<not>\<^sup>I \<and> Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> lCoP2(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" nitpick[satisfy,card w=3] oops
lemma "lCoP2(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I \<longrightarrow> TNDm \<^bold>\<not>\<^sup>I" by (simp add: XCoP_def2 TNDm_def TNDw_def lCoP2_def2 lCoPw_XCoP)
(**lCoP2-C*)
lemma "\<FF> \<F> \<Longrightarrow> lCoP2(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma "lCoP2(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C \<longrightarrow> ECQ \<^bold>\<not>\<^sup>C" by (simp add: lCoP2_ECQ)

(**lCoP3-I*)
lemma "\<FF> \<F> \<Longrightarrow> lCoP3(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma "lCoP3(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I \<longrightarrow> TND \<^bold>\<not>\<^sup>I" unfolding Defs conn by metis
(**lCoP3-C*)
lemma "\<FF> \<F> \<Longrightarrow> lCoP3(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma "lCoP3(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C \<longrightarrow> ECQ \<^bold>\<not>\<^sup>C" unfolding Defs conn by metis


subsection \<open>Disjunctive syllogism\<close>

(**DS1-I*)
lemma "DS1(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" using DS1_def ECQ_I ECQ_def unfolding conn by auto
(**DS1-C*)
lemma "\<FF> \<F> \<Longrightarrow> DS1(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C" nitpick oops (*countermodel*)
lemma "DS1(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C \<longrightarrow> ECQ \<^bold>\<not>\<^sup>C" unfolding Defs conn by metis

(**DS2-I*)
lemma "\<FF> \<F> \<Longrightarrow> DS2(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I" nitpick oops (*countermodel*)
lemma "DS2(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>I \<longrightarrow> TND \<^bold>\<not>\<^sup>I" by (simp add: Defs conn)
(**DS2-C*)
lemma "DS2(\<^bold>\<rightarrow>) \<^bold>\<not>\<^sup>C" using TND_C unfolding Defs conn by auto

end