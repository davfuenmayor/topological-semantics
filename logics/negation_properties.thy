theory negation_properties
  imports "../conditions/conditions_relativized"
begin

section \<open>Properties of negation(-like) operators\<close>

(*Introduces convenient notation for type for properties of operators (to avoid clutter)*)
type_synonym 'w \<Omega> = "('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool"
type_synonym 'w \<Delta> = "('w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool"

named_theorems neg (*to group together definitions for properties of negations*)

subsection \<open>Principles of excluded middle, contradiction and explosion\<close>

(**TND: tertium non datur, aka. law of excluded middle (resp. strong, weak, minimal).*)
abbreviation pTND  ("TND\<^sup>_  _") where "TND\<^sup>a  \<eta> \<equiv>       \<^bold>\<top>  \<^bold>= a \<^bold>\<or> (\<eta> a)"
abbreviation pTNDw ("TNDw\<^sup>_ _") where "TNDw\<^sup>a \<eta> \<equiv> \<forall>b. (\<eta> b) \<^bold>\<le> a \<^bold>\<or> (\<eta> a)"
abbreviation pTNDm ("TNDm\<^sup>_ _") where "TNDm\<^sup>a \<eta> \<equiv>     (\<eta> \<^bold>\<bottom>) \<^bold>\<le> a \<^bold>\<or> (\<eta> a)"
definition TND ::"'w \<Omega>" where "TND  \<eta> \<equiv> \<forall>\<phi>. TND\<^sup>\<phi>  \<eta>"
definition TNDw::"'w \<Omega>" where "TNDw \<eta> \<equiv> \<forall>\<phi>. TNDw\<^sup>\<phi> \<eta>"
definition TNDm::"'w \<Omega>" where "TNDm \<eta> \<equiv> \<forall>\<phi>. TNDm\<^sup>\<phi> \<eta>"
declare TND_def[neg] TNDw_def[neg] TNDm_def[neg]

(**Explore some (non)entailment relations:*)
lemma "TND  \<eta> \<Longrightarrow> TNDw \<eta>" unfolding neg conn order by simp
lemma "TNDw \<eta> \<Longrightarrow> TND  \<eta>" nitpick oops
lemma "TNDw \<eta> \<Longrightarrow> TNDm \<eta>" unfolding neg by simp
lemma "TNDm \<eta> \<Longrightarrow> TNDw \<eta>" nitpick oops

(**ECQ: ex contradictione (sequitur) quodlibet (resp: strong, weak, minimal).*)
abbreviation pECQ  ("ECQ\<^sup>_ _")  where "ECQ\<^sup>a  \<eta> \<equiv>     a \<^bold>\<and> (\<eta> a) \<^bold>= \<^bold>\<bottom>"
abbreviation pECQw ("ECQw\<^sup>_ _") where "ECQw\<^sup>a \<eta> \<equiv> \<forall>b. a \<^bold>\<and> (\<eta> a) \<^bold>\<le> (\<eta> b)"
abbreviation pECQm ("ECQm\<^sup>_ _") where "ECQm\<^sup>a \<eta> \<equiv>     a \<^bold>\<and> (\<eta> a) \<^bold>\<le> (\<eta> \<^bold>\<top>)"
definition ECQ ::"'w \<Omega>" where  "ECQ \<eta> \<equiv> \<forall>a. ECQ\<^sup>a  \<eta>"
definition ECQw::"'w \<Omega>" where "ECQw \<eta> \<equiv> \<forall>a. ECQw\<^sup>a \<eta>"
definition ECQm::"'w \<Omega>" where "ECQm \<eta> \<equiv> \<forall>a. ECQm\<^sup>a \<eta>"
declare ECQ_def[neg] ECQw_def[neg] ECQm_def[neg]

(**Explore some (non)entailment relations:*)
lemma "ECQ  \<eta> \<Longrightarrow> ECQw \<eta>" unfolding neg conn order by blast
lemma "ECQw \<eta> \<Longrightarrow> ECQ  \<eta>" nitpick oops
lemma "ECQw \<eta> \<Longrightarrow> ECQm \<eta>" unfolding neg by simp
lemma "ECQm \<eta> \<Longrightarrow> ECQw \<eta>" nitpick oops

(**LNC: law of non-contradiction.*)
abbreviation pLNC  ("LNC\<^sup>_ _")  where "LNC\<^sup>a \<eta> \<equiv> \<eta>(a \<^bold>\<and> \<eta> a) \<^bold>= \<^bold>\<top>"
definition LNC::"'w \<Omega>" where "LNC \<eta> \<equiv> \<forall>a. LNC\<^sup>a \<eta>"
declare LNC_def[neg]

(**ECQ and LNC are in general independent.*)
lemma "ECQ \<eta> \<Longrightarrow> LNC \<eta>" nitpick oops
lemma "LNC \<eta> \<Longrightarrow> ECQm \<eta>" nitpick oops


subsection \<open>Contraposition rules\<close>

(**CoP: contraposition (global/rule variants).
Variant 0 is antitonicity (ANTI). Variants 1-3 are stronger.*)
abbreviation pCoP1 ("CoP1\<^sup>_\<^sup>_ _") where "CoP1\<^sup>a\<^sup>b \<eta> \<equiv> a \<^bold>\<le> (\<eta> b) \<longrightarrow> b \<^bold>\<le> (\<eta> a)"
abbreviation pCoP2 ("CoP2\<^sup>_\<^sup>_ _") where "CoP2\<^sup>a\<^sup>b \<eta> \<equiv> (\<eta> a) \<^bold>\<le> b \<longrightarrow> (\<eta> b) \<^bold>\<le> a"
abbreviation pCoP3 ("CoP3\<^sup>_\<^sup>_ _") where "CoP3\<^sup>a\<^sup>b \<eta> \<equiv> (\<eta> a) \<^bold>\<le> (\<eta> b) \<longrightarrow> b \<^bold>\<le> a"

abbreviation CoP0 ::"'w \<Omega>" where "CoP0  \<eta> \<equiv> ANTI \<eta>"
definition   CoP1 ::"'w \<Omega>" where "CoP1  \<eta> \<equiv> \<forall>a b. CoP1\<^sup>a\<^sup>b \<eta>"
definition   CoP1'::"'w \<Omega>" where "CoP1' \<eta> \<equiv> \<forall>a b. a \<^bold>\<le> (\<eta> b) \<longleftrightarrow> b \<^bold>\<le> (\<eta> a)"
definition   CoP2 ::"'w \<Omega>" where "CoP2  \<eta> \<equiv> \<forall>a b. CoP2\<^sup>a\<^sup>b \<eta>"
definition   CoP2'::"'w \<Omega>" where "CoP2' \<eta> \<equiv> \<forall>a b. (\<eta> a) \<^bold>\<le> b \<longleftrightarrow> (\<eta> b) \<^bold>\<le> a"
definition   CoP3 ::"'w \<Omega>" where "CoP3  \<eta> \<equiv> \<forall>a b. CoP3\<^sup>a\<^sup>b \<eta>"

lemma CoP1_defs_rel: "CoP1 \<eta> = CoP1' \<eta>" unfolding neg CoP1_def CoP1'_def by blast
lemma CoP2_defs_rel: "CoP2 \<eta> = CoP2' \<eta>" unfolding neg CoP2_def CoP2'_def by blast

declare CoP1_def[neg] CoP2_def[neg] CoP3_def[neg]

(**Explore some (non)entailment relations:*)
lemma "CoP1 \<eta> \<Longrightarrow> CoP0 \<eta>" by (metis (mono_tags) ANTI_def CoP1_def subset_char1)
lemma "CoP0 \<eta> \<Longrightarrow> CoP1 \<eta>" nitpick oops
lemma "CoP2 \<eta> \<Longrightarrow> CoP0 \<eta>" by (metis ANTI_def CoP2_def subset_char1)
lemma "CoP0 \<eta> \<Longrightarrow> CoP2 \<eta>" nitpick oops
lemma "CoP3 \<eta> \<Longrightarrow> CoP0 \<eta>" unfolding neg (*nitpick*) oops (**no countermodel found so far. TODO: verify*)
lemma "CoP0 \<eta> \<Longrightarrow> CoP3 \<eta>" nitpick oops

(**All three strong variants are pairwise independent. However, CoP3 follows from CoP1 plus CoP2.*)
lemma CoP123: "CoP1 \<eta> \<Longrightarrow> CoP2 \<eta> \<Longrightarrow> CoP3 \<eta>" unfolding neg order by smt
(**Taking all CoP together still leaves room for a boldly paraconsistent resp. paracomplete logic.*)
lemma "CoP1 \<eta> \<Longrightarrow> CoP2 \<eta> \<Longrightarrow> ECQm \<eta>" nitpick oops 
lemma "CoP1 \<eta> \<Longrightarrow> CoP2 \<eta> \<Longrightarrow> TNDm \<eta>" nitpick oops 


subsection \<open>Modus tollens rules\<close>

(**MT: modus (tollendo) tollens (global/rule variants).*)
abbreviation pMT0 ("MT0\<^sup>_\<^sup>_ _") where "MT0\<^sup>a\<^sup>b \<eta> \<equiv> a \<^bold>\<le> b \<and> (\<eta> b) \<^bold>= \<^bold>\<top> \<longrightarrow> (\<eta> a) \<^bold>= \<^bold>\<top>"
abbreviation pMT1 ("MT1\<^sup>_\<^sup>_ _") where "MT1\<^sup>a\<^sup>b \<eta> \<equiv> a \<^bold>\<le> (\<eta> b) \<and> b \<^bold>= \<^bold>\<top> \<longrightarrow> (\<eta> a) \<^bold>= \<^bold>\<top>"
abbreviation pMT2 ("MT2\<^sup>_\<^sup>_ _") where "MT2\<^sup>a\<^sup>b \<eta> \<equiv> (\<eta> a) \<^bold>\<le> b \<and> (\<eta> b) \<^bold>= \<^bold>\<top> \<longrightarrow> a \<^bold>= \<^bold>\<top>"
abbreviation pMT3 ("MT3\<^sup>_\<^sup>_ _") where "MT3\<^sup>a\<^sup>b \<eta> \<equiv> (\<eta> a) \<^bold>\<le> (\<eta> b) \<and> b \<^bold>= \<^bold>\<top> \<longrightarrow> a \<^bold>= \<^bold>\<top>"
definition MT0::"'w \<Omega>" where "MT0 \<eta> \<equiv> \<forall>a b. MT0\<^sup>a\<^sup>b \<eta>"
definition MT1::"'w \<Omega>" where "MT1 \<eta> \<equiv> \<forall>a b. MT1\<^sup>a\<^sup>b \<eta>"
definition MT2::"'w \<Omega>" where "MT2 \<eta> \<equiv> \<forall>a b. MT2\<^sup>a\<^sup>b \<eta>"
definition MT3::"'w \<Omega>" where "MT3 \<eta> \<equiv> \<forall>a b. MT3\<^sup>a\<^sup>b \<eta>"

declare MT0_def[neg] MT1_def[neg] MT2_def[neg] MT3_def[neg]

(**Again, all MT variants are pairwise independent. We explore some (non)entailment relations:*)
lemma "CoP0 \<eta> \<Longrightarrow> MT0 \<eta>" unfolding neg order cond conn by blast
lemma "CoP1 \<eta> \<Longrightarrow> MT1 \<eta>" unfolding neg order conn by blast
lemma "CoP2 \<eta> \<Longrightarrow> MT2 \<eta>" unfolding neg order conn by blast
lemma "CoP3 \<eta> \<Longrightarrow> MT3 \<eta>" unfolding neg order conn by blast
lemma "MT0 \<eta> \<Longrightarrow> MT1 \<eta> \<Longrightarrow> MT2 \<eta> \<Longrightarrow> MT3 \<eta> \<Longrightarrow> CoP0 \<eta>" nitpick oops
lemma "MT0 \<eta> \<Longrightarrow> MT1 \<eta> \<Longrightarrow> MT2 \<eta> \<Longrightarrow> MT3 \<eta> \<Longrightarrow> ECQm \<eta>" nitpick oops
lemma "MT0 \<eta> \<Longrightarrow> MT1 \<eta> \<Longrightarrow> MT2 \<eta> \<Longrightarrow> MT3 \<eta> \<Longrightarrow> TNDm \<eta>" nitpick oops
lemma MT123: "MT1 \<eta> \<Longrightarrow> MT2 \<eta> \<Longrightarrow> MT3 \<eta>"  unfolding neg order conn by metis


subsection \<open>Double negation introduction and elimination\<close>

(**DNI/DNE: double negation introduction/elimination (as axioms).*)
abbreviation pDNI ("DNI\<^sup>_ _") where "DNI\<^sup>a \<eta> \<equiv> a \<^bold>\<le> \<eta> (\<eta> a)"
abbreviation pDNE ("DNE\<^sup>_ _") where "DNE\<^sup>a \<eta> \<equiv> \<eta> (\<eta> a) \<^bold>\<le> a"
definition DNI::"'w \<Omega>" where "DNI \<eta> \<equiv> \<forall>a. DNI\<^sup>a \<eta>"
definition DNE::"'w \<Omega>" where "DNE \<eta> \<equiv> \<forall>a. DNE\<^sup>a \<eta>"
declare DNI_def[neg] DNE_def[neg]

(**CoP1 (resp. CoP2) can alternatively be defined as CoPw plus DNI (resp. DNE).*)
lemma "DNI \<eta> \<Longrightarrow> CoP1 \<eta>" nitpick oops
lemma CoP1_def2: "CoP1 \<eta> = (CoP0 \<eta> \<and> DNI \<eta>)" unfolding neg cond using subset_char2 by blast
lemma "DNE \<eta> \<Longrightarrow>  CoP2 \<eta>" nitpick oops
lemma CoP2_def2: "CoP2 \<eta> = (CoP0 \<eta> \<and> DNE \<eta>)" unfolding neg cond using subset_char1 by blast

(**Explore some non-entailment relations:*)
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> CoP0 \<eta>" nitpick oops 
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> TNDm \<eta>" nitpick oops 
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> ECQm \<eta>" nitpick oops 
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> MT0 \<eta>" nitpick oops
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> MT1 \<eta>" nitpick oops
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> MT2 \<eta>" nitpick oops
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> MT3 \<eta>" nitpick oops

(**DNI/DNE: double negation introduction/elimination (as rules).*)
abbreviation prDNI ("rDNI\<^sup>_ _") where "rDNI\<^sup>a \<eta> \<equiv> a \<^bold>= \<^bold>\<top> \<longrightarrow> \<eta> (\<eta> a) \<^bold>= \<^bold>\<top>"
abbreviation prDNE ("rDNE\<^sup>_ _") where "rDNE\<^sup>a \<eta> \<equiv> \<eta> (\<eta> a) \<^bold>= \<^bold>\<top> \<longrightarrow> a \<^bold>= \<^bold>\<top>"
definition rDNI::"'w \<Omega>" where "rDNI \<eta> \<equiv> \<forall>a. rDNI\<^sup>a \<eta>"
definition rDNE::"'w \<Omega>" where "rDNE \<eta> \<equiv> \<forall>a. rDNE\<^sup>a \<eta>"
declare rDNI_def[neg] rDNE_def[neg]

(**The rule variants are strictly weaker than the axiom variants,*)
lemma "DNI \<eta> \<Longrightarrow> rDNI \<eta>" unfolding neg order conn by simp
lemma "rDNI \<eta> \<Longrightarrow> DNI \<eta>" nitpick oops
lemma "DNE \<eta> \<Longrightarrow> rDNE \<eta>" unfolding neg order conn by blast
lemma "rDNE \<eta> \<Longrightarrow> DNE \<eta>" nitpick oops
(**and follow already from modus tollens.*)
lemma MT1_rDNI: "MT1 \<eta> \<Longrightarrow> rDNI \<eta>" unfolding neg order by blast
lemma MT2_rDNE: "MT2 \<eta> \<Longrightarrow> rDNE \<eta>" unfolding neg order by blast


subsection \<open>(anti)normality and its dual\<close>

(**nNORM (resp. nDNRM) is entailed by CoP1 (resp. CoP2). *)
lemma CoP1_NORM: "CoP1 \<eta> \<Longrightarrow> nNORM \<eta>" unfolding neg cond conn order by simp
lemma CoP2_DNRM: "CoP2 \<eta> \<Longrightarrow> nDNRM \<eta>" unfolding neg cond conn by (smt (verit) setequ_char subset_def)
lemma "DNI \<eta> \<Longrightarrow> nNORM \<eta>" nitpick oops 
lemma "DNE \<eta> \<Longrightarrow> nDNRM \<eta>" nitpick oops 
(**nNORM and nDNRM together entail the rule variant of DNI (rDNI).*)
lemma nDNRM_rDNI: "nNORM \<eta> \<Longrightarrow> nDNRM \<eta> \<Longrightarrow> rDNI \<eta>" unfolding neg cond by (simp add: setequ_ext)
lemma "nNORM \<eta> \<Longrightarrow> nDNRM \<eta> \<Longrightarrow> rDNE \<eta>" nitpick oops


subsection \<open>De Morgan laws\<close>

(**De Morgan laws correspond to anti-additivity and anti-multiplicativity)*)

(**DM3 (resp. DM4) are entailed by CoP0/ANTI together with DNE (resp. DNI).*)
lemma CoP0_DNE_nMULTb: "CoP0 \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> nMULT\<^sup>b \<eta>" unfolding neg cond by (metis ANTI_def ANTI_nADDIb L12 nADDI_b_def subset_char1)
lemma CoP0_DNI_nADDIa: "CoP0 \<eta> \<Longrightarrow> DNI \<eta> \<Longrightarrow> nADDI\<^sup>a \<eta>" unfolding neg cond by (metis ANTI_def ANTI_nMULTa L11 nMULT_a_def subset_char2)

(**From this follows that DM3 (resp. DM4) is entailed by CoP2 (resp. CoP1).*)
lemma CoP2_nMULTb: "CoP2 \<eta> \<Longrightarrow> nMULT\<^sup>b \<eta>" by (simp add: CoP0_DNE_nMULTb CoP2_def2)
lemma CoP1_nADDIa: "CoP1 \<eta> \<Longrightarrow> nADDI\<^sup>a \<eta>" by (simp add: CoP0_DNI_nADDIa CoP1_def2)
   
(**Explore some non-entailment relations:*)
lemma "CoP0 \<eta> \<Longrightarrow> nADDI\<^sup>a \<eta> \<Longrightarrow> nMULT\<^sup>b \<eta> \<Longrightarrow> nNORM \<eta> \<Longrightarrow> nDNRM \<eta> \<Longrightarrow> DNI \<eta>" nitpick oops 
lemma "CoP0 \<eta> \<Longrightarrow> nADDI\<^sup>a \<eta> \<Longrightarrow> nMULT\<^sup>b \<eta> \<Longrightarrow> nNORM \<eta> \<Longrightarrow> nDNRM \<eta> \<Longrightarrow> DNE \<eta>" nitpick oops 
lemma "CoP0 \<eta> \<Longrightarrow> nADDI\<^sup>a \<eta> \<Longrightarrow> nMULT\<^sup>b \<eta> \<Longrightarrow> DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> ECQm \<eta>" nitpick oops 
lemma "CoP0 \<eta> \<Longrightarrow> nADDI\<^sup>a \<eta> \<Longrightarrow> nMULT\<^sup>b \<eta> \<Longrightarrow> DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> TNDm \<eta>" nitpick oops 


subsection \<open>Contextual (strong) contraposition rule\<close>

(**XCoP: contextual contraposition (global/rule variant).*)
abbreviation pXCoP ("XCoP\<^sup>_\<^sup>_ _") where "XCoP\<^sup>a\<^sup>b \<eta> \<equiv> \<forall>c. c \<^bold>\<and> a \<^bold>\<le> b \<longrightarrow> c \<^bold>\<and> (\<eta> b) \<^bold>\<le> (\<eta> a)"
definition XCoP::"'w \<Omega>" where "XCoP \<eta> \<equiv> \<forall>a b. XCoP\<^sup>a\<^sup>b \<eta>"
declare XCoP_def[neg]

(**XCoP can alternatively be defined as ECQw plus TNDw.*)
lemma XCoP_def2: "XCoP \<eta> = (ECQw \<eta> \<and> TNDw \<eta>)" proof -
  have LtoR1: "XCoP \<eta> \<Longrightarrow> ECQw \<eta>" unfolding neg conn order by blast
  have LtoR2: "XCoP \<eta> \<Longrightarrow> TNDw \<eta>" sorry (*this holds. TODO reconstruct (use atomicity)*)
  have RtoL: "ECQw \<eta> \<and> TNDw \<eta> \<Longrightarrow> XCoP \<eta>" unfolding neg by (smt (verit, del_insts) join_def meet_def subset_def)
  from LtoR1 LtoR2 RtoL show ?thesis by blast
qed

(**Explore some (non)entailment relations:*)
lemma "XCoP \<eta> \<Longrightarrow> ECQ \<eta>" nitpick oops 
lemma "XCoP \<eta> \<Longrightarrow> TND \<eta>" nitpick oops 
lemma XCoP_CoPw: "XCoP \<eta> \<Longrightarrow> CoP0 \<eta>" unfolding neg cond by (metis (full_types) meet_def subset_def)
lemma "XCoP \<eta> \<Longrightarrow> CoP1 \<eta>" nitpick oops 
lemma "XCoP \<eta> \<Longrightarrow> CoP2 \<eta>" nitpick oops 
lemma "XCoP \<eta> \<Longrightarrow> CoP3 \<eta>" nitpick oops 
lemma "CoP1 \<eta> \<and> CoP2 \<eta> \<Longrightarrow> XCoP \<eta>" nitpick oops 
lemma "XCoP \<eta> \<Longrightarrow> nNORM \<eta>" nitpick oops 
lemma "XCoP \<eta> \<Longrightarrow> nDNRM \<eta>" nitpick oops 
lemma "XCoP \<eta> \<Longrightarrow> rDNI \<eta>" nitpick oops 
lemma "XCoP \<eta> \<Longrightarrow> rDNE \<eta>" nitpick oops 
lemma XCoP_nMULTb: "XCoP \<eta> \<Longrightarrow> nMULT\<^sup>b \<eta>" sorry (*this holds. TODO reconstruct (use atomicity)*)
lemma XCoP_nADDIa: "XCoP \<eta> \<Longrightarrow> nADDI\<^sup>a \<eta>" sorry (*this holds. TODO reconstruct (use atomicity)*)


subsection \<open>Local contraposition axioms\<close>
(**Observe that the definitions below take implication as an additional parameter: @{text "\<iota>"}.*)

(**lCoP: contraposition (local/axiom variants).*)
abbreviation plCoP0 ("lCoP0\<^sup>_\<^sup>_ _ _") where "lCoP0\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> a b) \<^bold>\<le> (\<iota> (\<eta> b) (\<eta> a))"
abbreviation plCoP1 ("lCoP1\<^sup>_\<^sup>_ _ _") where "lCoP1\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> a (\<eta> b)) \<^bold>\<le> (\<iota> b (\<eta> a))"
abbreviation plCoP2 ("lCoP2\<^sup>_\<^sup>_ _ _") where "lCoP2\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> (\<eta> a) b) \<^bold>\<le> (\<iota> (\<eta> b) a)"
abbreviation plCoP3 ("lCoP3\<^sup>_\<^sup>_ _ _") where "lCoP3\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> (\<eta> a) (\<eta> b)) \<^bold>\<le> (\<iota> b a)"
definition lCoP0::"'w \<Delta>"  where "lCoP0  \<iota> \<eta> \<equiv> \<forall>a b. lCoP0\<^sup>a\<^sup>b \<iota> \<eta>"
definition lCoP1::"'w \<Delta>"  where "lCoP1  \<iota> \<eta> \<equiv> \<forall>a b. lCoP1\<^sup>a\<^sup>b \<iota> \<eta>"
definition lCoP1'::"'w \<Delta>" where "lCoP1' \<iota> \<eta> \<equiv> \<forall>a b. (\<iota> a (\<eta> b)) \<^bold>= (\<iota> b (\<eta> a))"
definition lCoP2::"'w \<Delta>"  where "lCoP2  \<iota> \<eta> \<equiv> \<forall>a b. lCoP2\<^sup>a\<^sup>b \<iota> \<eta>"
definition lCoP2'::"'w \<Delta>" where "lCoP2' \<iota> \<eta> \<equiv> \<forall>a b. (\<iota> (\<eta> a) b) \<^bold>= (\<iota> (\<eta> b) a)"
definition lCoP3::"'w \<Delta>"  where "lCoP3  \<iota> \<eta> \<equiv> \<forall>a b. lCoP3\<^sup>a\<^sup>b \<iota> \<eta>"

lemma lCoP1_defs_rel: "lCoP1 \<iota> \<eta> = lCoP1' \<iota> \<eta>" by (metis (mono_tags) lCoP1'_def lCoP1_def setequ_char)
lemma lCoP2_defs_rel: "lCoP2 \<iota> \<eta> = lCoP2' \<iota> \<eta>" using lCoP2'_def lCoP2_def setequ_char by blast

declare lCoP0_def[neg] lCoP1_def[neg] lCoP2_def[neg] lCoP3_def[neg]

(**All local contraposition variants are in general independent from each other.
However if we take classical implication we can verify some relationships.*)

lemma lCoP1_def2: "lCoP1(\<^bold>\<rightarrow>) \<eta> = (lCoP0(\<^bold>\<rightarrow>) \<eta> \<and> DNI \<eta>)" unfolding neg conn order by metis
lemma lCoP2_def2: "lCoP2(\<^bold>\<rightarrow>) \<eta> = (lCoP0(\<^bold>\<rightarrow>) \<eta> \<and> DNE \<eta>)" unfolding neg conn order by blast
lemma "lCoP1(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP0(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "lCoP0(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP1(\<^bold>\<rightarrow>) \<eta>" nitpick oops
lemma "lCoP2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP0(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "lCoP0(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP2(\<^bold>\<rightarrow>) \<eta>" nitpick oops
lemma "lCoP3(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP0(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "lCoP0(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP3(\<^bold>\<rightarrow>) \<eta>" nitpick oops
lemma lCoP123: "lCoP1(\<^bold>\<rightarrow>) \<eta> \<and> lCoP2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP3(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by metis

(**Local variants imply global ones as expected.*)
lemma "lCoP0(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> CoP0 \<eta>" unfolding neg cond conn order by blast
lemma "lCoP1(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> CoP1 \<eta>" unfolding neg conn order by blast
lemma "lCoP2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> CoP2 \<eta>" unfolding neg conn order by blast
lemma "lCoP3(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> CoP3 \<eta>" unfolding neg conn order by blast

(**Explore some (non)entailment relations.*)
lemma lCoPw_XCoP: "lCoP0(\<^bold>\<rightarrow>) \<eta> = XCoP \<eta>" unfolding XCoP_def2 neg conn order by metis
lemma lCoP1_TND: "lCoP1(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> TND \<eta>" unfolding neg conn by (smt (verit, best) setequ_char subset_def)
lemma "TND \<eta> \<Longrightarrow> lCoP1(\<^bold>\<rightarrow>) \<eta>" nitpick oops
lemma lCoP2_ECQ: "lCoP2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> ECQ \<eta>" unfolding neg conn by (smt (verit) setequ_def subset_def)
lemma "ECQ \<eta> \<Longrightarrow> lCoP2(\<^bold>\<rightarrow>) \<eta>" nitpick oops


subsection \<open>Local modus tollens axioms\<close>

(**lMT: Modus tollens (local/axiom variants).*)
abbreviation plMT0 ("lMT0\<^sup>_\<^sup>_ _ _") where "lMT0\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> a b) \<^bold>\<and> (\<eta> b) \<^bold>\<le> (\<eta> a)"
abbreviation plMT1 ("lMT1\<^sup>_\<^sup>_ _ _") where "lMT1\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> a (\<eta> b)) \<^bold>\<and> b \<^bold>\<le> (\<eta> a)"
abbreviation plMT2 ("lMT2\<^sup>_\<^sup>_ _ _") where "lMT2\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> (\<eta> a) b) \<^bold>\<and> (\<eta> b) \<^bold>\<le> a"
abbreviation plMT3 ("lMT3\<^sup>_\<^sup>_ _ _") where "lMT3\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> (\<eta> a) (\<eta> b)) \<^bold>\<and> b \<^bold>\<le> a"
definition lMT0::"'w \<Delta>" where "lMT0 \<iota> \<eta> \<equiv> \<forall>a b. lMT0\<^sup>a\<^sup>b \<iota> \<eta>"
definition lMT1::"'w \<Delta>" where "lMT1 \<iota> \<eta> \<equiv> \<forall>a b. lMT1\<^sup>a\<^sup>b \<iota> \<eta>"
definition lMT2::"'w \<Delta>" where "lMT2 \<iota> \<eta> \<equiv> \<forall>a b. lMT2\<^sup>a\<^sup>b \<iota> \<eta>"
definition lMT3::"'w \<Delta>" where "lMT3 \<iota> \<eta> \<equiv> \<forall>a b. lMT3\<^sup>a\<^sup>b \<iota> \<eta>"
  
declare lMT0_def[neg] lMT1_def[neg] lMT2_def[neg] lMT3_def[neg]

(**All local MT variants are in general independent from each other and also from local CoP instances.
However if we take classical implication we can verify that local MT and CoP are indeed equivalent.*)
lemma "lMT0(\<^bold>\<rightarrow>) \<eta> = lCoP0(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "lMT1(\<^bold>\<rightarrow>) \<eta> = lCoP1(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "lMT2(\<^bold>\<rightarrow>) \<eta> = lCoP2(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "lMT3(\<^bold>\<rightarrow>) \<eta> = lCoP3(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast


subsection \<open>Disjunctive syllogism\<close>

(**DS: disjunctive syllogism.*)
abbreviation pDS1 ("DS1\<^sup>_\<^sup>_ _ _") where "DS1\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (a \<^bold>\<or> b) \<^bold>\<le> (\<iota> (\<eta> a) b)"
abbreviation pDS2 ("DS2\<^sup>_\<^sup>_ _ _") where "DS2\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> (\<eta> a) b) \<^bold>\<le> (a \<^bold>\<or> b)"
abbreviation pDS3 ("DS3\<^sup>_\<^sup>_ _ _") where "DS3\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> ((\<eta> a) \<^bold>\<or> b) \<^bold>\<le> (\<iota> a b)"
abbreviation pDS4 ("DS4\<^sup>_\<^sup>_ _ _") where "DS4\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> a b) \<^bold>\<le> ((\<eta> a) \<^bold>\<or> b)"
definition DS1::"'w \<Delta>" where "DS1 \<iota> \<eta> \<equiv> \<forall>a b. DS1\<^sup>a\<^sup>b \<iota> \<eta>"
definition DS2::"'w \<Delta>" where "DS2 \<iota> \<eta> \<equiv> \<forall>a b. DS2\<^sup>a\<^sup>b \<iota> \<eta>"
definition DS3::"'w \<Delta>" where "DS3 \<iota> \<eta> \<equiv> \<forall>a b. DS3\<^sup>a\<^sup>b \<iota> \<eta>"
definition DS4::"'w \<Delta>" where "DS4 \<iota> \<eta> \<equiv> \<forall>a b. DS4\<^sup>a\<^sup>b \<iota> \<eta>"

declare DS1_def[neg] DS2_def[neg] DS3_def[neg] DS4_def[neg]

(**All DS variants are in general independent from each other. However if we take classical implication
we can verify that the pairs DS1-DS3 and DS2-DS4 are indeed equivalent. *)
lemma "DS1(\<^bold>\<rightarrow>) \<eta> = DS3(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "DS2(\<^bold>\<rightarrow>) \<eta> = DS4(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast

(**Explore some (non)entailment relations.*)
lemma DS1_nDNor: "DS1(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> nDNRM \<eta>" unfolding neg cond conn order by metis
lemma DS2_nNor:  "DS2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> nNORM \<eta>" unfolding neg cond conn order by metis
lemma lCoP2_DS1: "lCoP2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> DS1(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma lCoP1_DS2: "lCoP1(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> DS2(\<^bold>\<rightarrow>) \<eta>" unfolding neg conn order by blast
lemma "CoP2 \<eta> \<Longrightarrow> DS1(\<^bold>\<rightarrow>) \<eta>" nitpick oops
lemma "CoP1 \<eta> \<Longrightarrow> DS2(\<^bold>\<rightarrow>) \<eta>" nitpick oops

end