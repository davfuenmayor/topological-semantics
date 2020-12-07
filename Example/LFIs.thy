theory LFIs
  imports "../topological-semantics/negation_conditions"
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3] (*default settings*)

section \<open>Logics of Formal Inconsistency (LFIs)\<close>
(**The LFIs @{cite LFI} are a family of paraconsistent logics featuring a "consistency" operator @{text "\<^bold>\<circ>"}
that can be used to recover some classical properties of negation (in particular ECQ).
We show how to semantically embed LFIs as extensions of Boolean algebras (here as frontier algebras).*)

(**Logical validity can be defined as truth in all worlds/points (i.e. as denoting the top element)*)
abbreviation gtrue::"\<sigma>\<Rightarrow>bool" ("[\<^bold>\<turnstile> _]") where  "[\<^bold>\<turnstile>  A] \<equiv> \<forall>w. A w"   
lemma gtrue_def: "[\<^bold>\<turnstile> A] \<equiv> A \<^bold>\<approx> \<^bold>\<top>"  by (simp add: top_def)

(**When defining a logic over an existing algebra we have two choices: a global (truth preserving)
and a local (truth-degree preserving) notion of logical consequence. For LFIs we use the latter.*)
abbreviation conseq_global1::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_ \<^bold>\<turnstile>\<^sub>g _]") where "[A \<^bold>\<turnstile>\<^sub>g B] \<equiv> [\<^bold>\<turnstile> A] \<longrightarrow> [\<^bold>\<turnstile> B]"
abbreviation conseq_global2::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_,_ \<^bold>\<turnstile>\<^sub>g _]") where "[A\<^sub>1, A\<^sub>2 \<^bold>\<turnstile>\<^sub>g B] \<equiv> [\<^bold>\<turnstile> A\<^sub>1] \<and> [\<^bold>\<turnstile> A\<^sub>2] \<longrightarrow> [\<^bold>\<turnstile> B]"
abbreviation conseq_local1::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_ \<^bold>\<turnstile> _]") where "[A \<^bold>\<turnstile> B] \<equiv> A \<^bold>\<preceq> B"
abbreviation conseq_local2::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_,_ \<^bold>\<turnstile> _]") where "[A\<^sub>1, A\<^sub>2 \<^bold>\<turnstile> B] \<equiv> A\<^sub>1 \<^bold>\<and> A\<^sub>2 \<^bold>\<preceq> B"
(*add more as the need arises...*)

(**For LFIs we use the closure-based negation previously defined (taking frontier as primitive). *)
abbreviation pneg::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_" [57]58) where "\<^bold>\<not>A \<equiv> \<^bold>\<not>\<^sup>C A"

(**In terms of the frontier operator the negation looks as follows:*)
lemma "\<^bold>\<not>A \<^bold>\<approx> \<^bold>\<midarrow>A \<^bold>\<or> \<F>(\<^bold>\<midarrow>A)" by (simp add: neg_C_def pC2)
lemma pneg_prop: "Fr_2 \<F> \<Longrightarrow> \<^bold>\<not>A \<^bold>\<approx> \<^bold>\<midarrow>A \<^bold>\<or> \<F>(A)" using pC2 pF2 unfolding conn by blast

(**We define two pairs of in/consistency operators and show how they relate to each other.
Using LFIs terminology, the minimal logic so encoded corresponds to "RmbC-ciw" (cf. @{cite RLFI}).*)
abbreviation pinca :: "\<sigma>\<Rightarrow>\<sigma>" ("\<bullet>\<^sup>A_" [57]58) where "\<bullet>\<^sup>AA  \<equiv> A \<^bold>\<and> \<^bold>\<not>A"
abbreviation pcona :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circ>\<^sup>A_" [57]58) where "\<^bold>\<circ>\<^sup>AA  \<equiv> \<^bold>\<midarrow>\<bullet>\<^sup>AA"
abbreviation pincb :: "\<sigma>\<Rightarrow>\<sigma>" ("\<bullet>\<^sup>B_" [57]58) where "\<bullet>\<^sup>BA  \<equiv> \<B> A"
abbreviation pconb :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circ>\<^sup>B_" [57]58) where "\<^bold>\<circ>\<^sup>BA  \<equiv> \<^bold>\<midarrow>\<bullet>\<^sup>BA"

(**Observe that assumming condition Fr-2 are we allowed to exchange A and B variants*)
lemma pincAB: "Fr_2 \<F> \<Longrightarrow> \<bullet>\<^sup>AA \<^bold>\<approx> \<bullet>\<^sup>BA" using Br_fr_def Cl_fr_def pF2 conn by auto
lemma pconAB: "Fr_2 \<F> \<Longrightarrow> \<^bold>\<circ>\<^sup>AA \<^bold>\<approx> \<^bold>\<circ>\<^sup>BA" using pincAB unfolding conn by simp

(**Observe that without assuming Fr-2 we obtain slightly different properties.*)
lemma "\<^bold>\<circ>\<^sup>AA \<^bold>\<approx> A \<^bold>\<rightarrow> \<I> A" nitpick oops (*countermodel*)
lemma Prop1: "\<^bold>\<circ>\<^sup>BA \<^bold>\<approx> A \<^bold>\<leftrightarrow> \<I> A" using fp1 unfolding conn equal_op_def by metis
lemma "Cl A \<longleftrightarrow> \<^bold>\<circ>\<^sup>B\<^bold>\<midarrow>A \<^bold>\<approx> \<^bold>\<top>" nitpick oops (*countermodel*)
lemma Prop2: "Cl A \<longleftrightarrow> \<^bold>\<circ>\<^sup>A\<^bold>\<midarrow>A \<^bold>\<approx> \<^bold>\<top>" using pC2 unfolding conn by auto
lemma Prop3: "Cl A \<longleftrightarrow> \<bullet>\<^sup>A\<^bold>\<midarrow>A \<^bold>\<approx> \<^bold>\<bottom>" using Cl_fr_def unfolding conn by auto
lemma "Op A \<longleftrightarrow> \<^bold>\<circ>\<^sup>AA \<^bold>\<approx> \<^bold>\<top>" nitpick oops (*countermodel*)
lemma Prop4: "Op A \<longleftrightarrow> \<^bold>\<circ>\<^sup>BA \<^bold>\<approx> \<^bold>\<top>" using Op_Bzero unfolding conn by simp
lemma Prop5: "Op A \<longleftrightarrow> \<bullet>\<^sup>BA \<^bold>\<approx> \<^bold>\<bottom>" using Op_Bzero by simp

(**In what follows we employ the (minimal) A-variant and verify some well-known properties (cf. @{cite LFI}).*)
abbreviation pinc :: "\<sigma>\<Rightarrow>\<sigma>" ("\<bullet>_" [57]58) where "\<bullet>A  \<equiv> \<bullet>\<^sup>AA"
abbreviation pcon :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circ>_" [57]58) where "\<^bold>\<circ>A  \<equiv> \<^bold>\<midarrow>\<bullet>A"

(* (1) *)
lemma "[a \<^bold>\<and> \<^bold>\<not>a \<^bold>\<turnstile> \<^bold>\<not>\<^bold>\<circ>a]" by (simp add: pC2 conn)
lemma "\<FF> \<F> \<Longrightarrow> [\<^bold>\<not>\<^bold>\<circ>a \<^bold>\<turnstile> a \<^bold>\<and> \<^bold>\<not>a]" nitpick oops (* countermodel found *)
(* (2) *)
lemma "[\<^bold>\<circ>a \<^bold>\<turnstile> \<^bold>\<not>(a \<^bold>\<and> \<^bold>\<not>a)]" by (simp add: pC2 conn)
lemma "\<FF> \<F> \<Longrightarrow> [\<^bold>\<not>(a \<^bold>\<and> \<^bold>\<not>a) \<^bold>\<turnstile> \<^bold>\<circ>a]" nitpick oops (* countermodel found *)
(* (3) *)
lemma "[\<^bold>\<not>a \<^bold>\<rightarrow> b \<^bold>\<turnstile> a \<^bold>\<or> b]" using pC2 conn by auto
lemma "\<FF> \<F> \<Longrightarrow> [a \<^bold>\<or> b \<^bold>\<turnstile> \<^bold>\<not>a \<^bold>\<rightarrow> b]" nitpick oops (* countermodel found *)
(* (4) *)
lemma "[\<^bold>\<circ>a, a \<^bold>\<or> b  \<^bold>\<turnstile> \<^bold>\<not>a \<^bold>\<rightarrow> b]" using conn by auto
(* (5) *)
lemma "\<FF> \<F> \<Longrightarrow> [a \<^bold>\<rightarrow> b \<^bold>\<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" nitpick oops (* countermodel found *)
lemma cop1: "[\<^bold>\<circ>b, a \<^bold>\<rightarrow> b \<^bold>\<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" using CF2 EXP_def neg_C_def conn by auto
(* (6) *)
lemma "\<FF> \<F> \<Longrightarrow> [a \<^bold>\<rightarrow> \<^bold>\<not>b \<^bold>\<turnstile> b \<^bold>\<rightarrow> \<^bold>\<not>a]" nitpick oops (* countermodel found *)
lemma cop2: "[\<^bold>\<circ>b, a \<^bold>\<rightarrow> \<^bold>\<not>b \<^bold>\<turnstile> b \<^bold>\<rightarrow> \<^bold>\<not>a]" using CF2 EXP_def neg_C_def conn by auto
(* (7) *)
lemma "\<FF> \<F> \<Longrightarrow> [\<^bold>\<not>a \<^bold>\<rightarrow> b \<^bold>\<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> a]" nitpick oops (* countermodel found *)
lemma cop3: "[\<^bold>\<circ>b, \<^bold>\<not>a \<^bold>\<rightarrow> b \<^bold>\<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> a]" using CF2 EXP_def neg_C_def using conn by fastforce
(* (8) *)
lemma "\<FF> \<F> \<Longrightarrow> [\<^bold>\<not>a \<^bold>\<rightarrow> \<^bold>\<not>b \<^bold>\<turnstile> b \<^bold>\<rightarrow> a]" nitpick oops (* countermodel found *)
lemma cop4: "[\<^bold>\<circ>b, \<^bold>\<not>a \<^bold>\<rightarrow> \<^bold>\<not>b \<^bold>\<turnstile> b \<^bold>\<rightarrow> a]" using CF2 EXP_def neg_C_def conn by fastforce

(**The following axioms are commonly employed in the literature on LFIs to obtain stronger logics.
We explore under which conditions they can be assumed while keeping the logic boldly paraconsistent.*)
abbreviation cf where "cf \<equiv> DNE pneg"
abbreviation ce where "ce \<equiv> DNI pneg"
abbreviation ciw where "ciw \<equiv> \<forall>P. [\<^bold>\<turnstile> \<^bold>\<circ>P \<^bold>\<or> \<bullet>P]"
abbreviation ci  where  "ci \<equiv> \<forall>P.  [\<^bold>\<not>\<^bold>\<circ>P \<^bold>\<turnstile> \<bullet>P]"
abbreviation cl  where  "cl \<equiv> \<forall>P.  [\<^bold>\<not>\<bullet>P \<^bold>\<turnstile> \<^bold>\<circ>P]"
abbreviation ca_conj where "ca_conj \<equiv> \<forall>P Q. [\<^bold>\<circ>P,\<^bold>\<circ>Q \<^bold>\<turnstile> \<^bold>\<circ>(P \<^bold>\<and> Q)]"
abbreviation ca_disj where "ca_disj \<equiv> \<forall>P Q. [\<^bold>\<circ>P,\<^bold>\<circ>Q \<^bold>\<turnstile> \<^bold>\<circ>(P \<^bold>\<or> Q)]"
abbreviation ca_impl where "ca_impl \<equiv> \<forall>P Q. [\<^bold>\<circ>P,\<^bold>\<circ>Q \<^bold>\<turnstile> \<^bold>\<circ>(P \<^bold>\<rightarrow> Q)]"
abbreviation ca where "ca \<equiv> ca_conj \<and> ca_disj \<and> ca_impl"

(**cf*)
lemma "\<FF> \<F> \<Longrightarrow> cf" nitpick oops
lemma "\<FF> \<F> \<and> cf \<and> \<sim>ECQm pneg" nitpick[satisfy] oops (*model found*)
(**ce*)
lemma "\<FF> \<F> \<Longrightarrow> ce" nitpick oops
lemma "Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> ce \<and> \<sim>ECQ pneg" nitpick[satisfy] oops (*model found*)  
lemma "Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> ce \<and> \<sim>ECQm pneg" nitpick[satisfy] oops (*model found*)  
lemma "Fr_1a \<F> \<and> Fr_2 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> ce \<and> \<sim>ECQm pneg" nitpick[satisfy] oops (*model found*)  
lemma "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> ce \<longrightarrow> ECQm pneg" unfolding Defs  using CoP1_XCoP CoP1_def2 CoPw_C DNI_def ECQw_def PF6 XCoP_def2 by auto
(**ciw*)
lemma ciw by (simp add:conn)
(**ci*)
lemma "\<FF> \<F> \<Longrightarrow> ci" nitpick oops
lemma "\<FF> \<F> \<and> ci \<and> \<sim>ECQm pneg" nitpick[satisfy] oops (*model found*)
(**cl*)
lemma "\<FF> \<F> \<Longrightarrow> cl" nitpick oops
lemma "Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> cl \<and> \<sim>ECQm pneg" nitpick[satisfy] oops (*model found*) 
lemma "Fr_1a \<F> \<and> Fr_2 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> cl \<and> \<sim>ECQm pneg" nitpick[satisfy] oops (*model found*)
lemma "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> cl \<longrightarrow> ECQ pneg" unfolding Defs  by (metis BC_rel Br_Border Br_cl_def bottom_def compl_def eq_ext' meet_def neg_C_def) 
(**ca-conj/disj*)
lemma "Fr_1a \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> ca_conj" using DM3_C DM3_def conn by auto
lemma "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> ca_disj" using ADDI_b_def MONO_ADDIb monI pB1 pincAB unfolding conn by metis
lemma "\<FF> \<F> \<Longrightarrow> ca_impl" nitpick oops
(**ca-impl*)
lemma "ca_impl \<and> \<sim>ECQ pneg" (*nitpick[satisfy]*) oops (*cannot find finite model*)
lemma "ca_impl \<longrightarrow> ECQm pneg" oops (*nor proof yet*)
(**cf \& ci*)
lemma "Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> cf \<and> ci \<and> \<sim>ECQm pneg" nitpick[satisfy] oops (*model found*)  
lemma "Fr_2 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> cf \<and> ci \<and> \<sim>ECQm pneg" nitpick[satisfy] oops (*model found*)
lemma "Fr_1b \<F> \<and> Fr_2 \<F> \<and> cf \<and> ci \<and> \<sim>ECQ pneg" (*nitpick[satisfy]*) oops (*cannot find finite model*) 
lemma "\<FF> \<F> \<and> cf \<and> ci \<longrightarrow> ECQm pneg" oops (*nor proof yet*) 
(**cf \& cl*)
lemma "Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> cf \<and> cl \<and> \<sim>ECQm pneg" nitpick[satisfy] oops (*model found*) 
lemma "Fr_2 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> cf \<and> cl \<and> \<sim>ECQm pneg" nitpick[satisfy] oops (*model found*)
lemma "Fr_1b \<F> \<and> Fr_2 \<F> \<and> cf \<and> cl \<longrightarrow> ECQ pneg" unfolding Defs by (smt Br_fr_def Fr_1b_def Prop2 Prop3 pF3 pneg_prop conn) 

end