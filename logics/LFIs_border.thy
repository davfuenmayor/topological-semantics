theory LFIs_border
  imports "logical_consequence" "../conditions/conditions_relativized_infinitary"
begin

section \<open>Logics of Formal Inconsistency (LFIs)\<close>

(**The LFIs are a family of paraconsistent logics featuring a 'consistency' operator @{text "\<^bold>\<circ>"}
that can be used to recover some classical properties of negation (in particular ECQ).
We show a shallow semantical embedding of logics at least as strong as the LFI RmbC-ciw*)

(*Let us assume a concrete type w (for 'worlds' or 'points')*)
typedecl w
(*Let us assume the following primitive unary operation \<B> (intended as a border operator)*)
consts \<B>::"w \<sigma> \<Rightarrow> w \<sigma>"

(*From the topological cube of opposition:*)
abbreviation "\<C> \<equiv> (\<B>\<^sup>f\<^sup>p)\<^sup>-" 
abbreviation "\<I> \<equiv> \<B>\<^sup>f\<^sup>p\<^sup>c" 
lemma "\<C>\<^sup>- = \<B>\<^sup>f\<^sup>p" by (simp add: dualcompl_invol)

(*let us recall that: *)
lemma expn_cntr: "EXPN \<C> = CNTR \<B>" by (metis EXPN_CNTR_dual2 EXPN_fp ofp_comm_dc1)

(**For LFIs we use the negation previously defined as \<C>\<^sup>- = \<B>\<^sup>f\<^sup>p *)
abbreviation cneg ("\<^bold>\<not>_"[70]71) where "cneg \<equiv> \<B>\<^sup>f\<^sup>p"

(**In terms of the border operator the negation looks as follows:*)
lemma cneg_char: "CNTR \<B> \<longrightarrow> \<^bold>\<not>A \<^bold>= \<^bold>\<midarrow>A \<^bold>\<or> (\<B> A)" by (smt (verit, ccfv_threshold) CNTR_def compl_def dimpl_def join_def op_fixpoint_def setequ_def subset_def)

(**This negation is of course boldly paraconsistent (for both local and global consequence).*)
lemma "[a, \<^bold>\<not>a \<turnstile> b]" nitpick oops (*countermodel*)
lemma "[a, \<^bold>\<not>a \<turnstile> \<^bold>\<not>b]" nitpick oops (*countermodel*)
lemma "[a, \<^bold>\<not>a \<turnstile>\<^sub>g b]" nitpick oops (*countermodel*) 
lemma "[a, \<^bold>\<not>a \<turnstile>\<^sub>g \<^bold>\<not>b]" nitpick oops (*countermodel*)

(**We define two pairs of in/consistency operators and show how they relate to each other.
Using LFIs terminology, the minimal logic so encoded corresponds to 'RmbC-ciw' (cf. @{cite RLFI}).*)
abbreviation op_inc_a::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<bullet>\<^sup>A_" [57]58) (* \<bullet> as truth-glut *)
  where "\<bullet>\<^sup>AA \<equiv> A \<^bold>\<and> \<^bold>\<not>A"
abbreviation op_con_a::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<^bold>\<circ>\<^sup>A_" [57]58) 
  where "\<^bold>\<circ>\<^sup>AA \<equiv> \<^bold>\<midarrow>\<bullet>\<^sup>AA"
abbreviation op_inc_b::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<bullet>\<^sup>B_" [57]58) (* \<bullet> as border *)
  where "\<bullet>\<^sup>BA \<equiv> \<B> A"
abbreviation op_con_b::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<^bold>\<circ>\<^sup>B_" [57]58) 
  where "\<^bold>\<circ>\<^sup>BA \<equiv> \<B>\<^sup>c A"

(**Observe that assumming CNTR \<B> are we allowed to exchange A and B variants.*)
lemma pincAB: "CNTR \<B> \<longrightarrow> \<bullet>\<^sup>AA \<^bold>= \<bullet>\<^sup>BA" by (smt (verit, ccfv_SIG) cneg_char dimpl_def join_def meet_def op_fixpoint_def setequ_def)
lemma pconAB: "CNTR \<B> \<longrightarrow> \<^bold>\<circ>\<^sup>AA \<^bold>= \<^bold>\<circ>\<^sup>BA" by (metis pincAB setequ_ext svfun_compl_def) 

(**Variants A and B give us slightly different properties (there are countermodels for those not shown).*)
lemma Prop1: "\<^bold>\<circ>\<^sup>BA \<^bold>= \<I>\<^sup>f\<^sup>p A" by (simp add: ofp_comm_compl ofp_invol setequ_ext)
lemma Prop2: "\<^bold>\<circ>\<^sup>AA \<^bold>= A \<^bold>\<rightarrow> \<I> A" by (simp add: BA_deMorgan2 impl_char svfun_compl_def)
lemma Prop3: "fp \<C> A \<longleftrightarrow> \<^bold>\<circ>\<^sup>B\<^bold>\<midarrow>A \<^bold>= \<^bold>\<top>" by (metis Prop1 dual_compl_char2 fp_d_rel setequ_ext)
lemma Prop4a: "fp \<I> A \<longleftrightarrow> \<^bold>\<circ>\<^sup>BA \<^bold>= \<^bold>\<top>" by (simp add: fp_rel ofp_comm_compl ofp_invol)
lemma Prop4b: "fp \<I> A  \<longrightarrow> \<^bold>\<circ>\<^sup>AA \<^bold>= \<^bold>\<top>" by (metis BA_impl Prop2 fixpoints_def setequ_char setequ_ext)

(**The 'principle of gentle explosion' works for both variants (both locally and globally)*)
lemma "[\<^bold>\<circ>\<^sup>Aa, a, \<^bold>\<not>a \<turnstile> b]" by (metis (mono_tags, lifting) compl_def meet_def subset_def) 
lemma "[\<^bold>\<circ>\<^sup>Aa, a, \<^bold>\<not>a \<turnstile>\<^sub>g b]" by (metis compl_def meet_def)
lemma "[\<^bold>\<circ>\<^sup>Ba, a, \<^bold>\<not>a \<turnstile> b]" by (smt (z3) meet_def ofp_fixpoint_compl_def ofp_invol sdiff_def subset_def)
lemma "[\<^bold>\<circ>\<^sup>Ba, a, \<^bold>\<not>a \<turnstile>\<^sub>g b]" by (metis compl_def fixpoints_def fp_rel gtrue_def setequ_ext svfun_compl_def)

abbreviation "BORDER \<phi> \<equiv> nMULTr \<phi> \<and> CNTR \<phi> \<and> nDNRM \<phi> \<and> nIDEMr\<^sup>b \<phi>"

(**We show how all (local) contraposition variants (among others) can be recovered using the
 consistency operators.*)

lemma "[\<^bold>\<circ>\<^sup>Ab, a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" nitpick oops
lemma cons_lcop1: "CNTR \<B> \<longrightarrow> [\<^bold>\<circ>\<^sup>Ab, a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" by (smt (verit, del_insts) cneg_char compl_def impl_char join_def meet_def setequ_ext subset_def)
lemma "[\<^bold>\<circ>\<^sup>Bb, a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" nitpick oops
lemma cons_lcop2: "CNTR \<B> \<longrightarrow> [\<^bold>\<circ>\<^sup>Bb, a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" by (metis cons_lcop1 pconAB setequ_ext)
(*.....*)

(**The following axioms are commonly employed in the literature on LFIs to obtain stronger logics.
We explore under which conditions they can be assumed while keeping the logic boldly paraconsistent.*)
abbreviation cf where "cf \<equiv> \<forall>P. [\<^bold>\<not>\<^bold>\<not>P \<turnstile> P]"
abbreviation ce where "ce \<equiv> \<forall>P. [P \<turnstile> \<^bold>\<not>\<^bold>\<not>P]"
abbreviation ciw_a where "ciw_a \<equiv> \<forall>P. [\<turnstile> \<^bold>\<circ>\<^sup>AP \<^bold>\<or> \<bullet>\<^sup>AP]"
abbreviation ciw_b where "ciw_b \<equiv> \<forall>P. [\<turnstile> \<^bold>\<circ>\<^sup>BP \<^bold>\<or> \<bullet>\<^sup>BP]"
abbreviation ci_a  where  "ci_a \<equiv> \<forall>P. [\<^bold>\<not>(\<^bold>\<circ>\<^sup>AP) \<turnstile> \<bullet>\<^sup>AP]"
abbreviation ci_b  where  "ci_b \<equiv> \<forall>P. [\<^bold>\<not>(\<^bold>\<circ>\<^sup>BP) \<turnstile> \<bullet>\<^sup>BP]"
abbreviation cl_a  where  "cl_a \<equiv> \<forall>P.  [\<^bold>\<not>(\<bullet>\<^sup>AP) \<turnstile> \<^bold>\<circ>\<^sup>AP]"
abbreviation cl_b  where  "cl_b \<equiv> \<forall>P.  [\<^bold>\<not>(\<bullet>\<^sup>BP) \<turnstile> \<^bold>\<circ>\<^sup>BP]"
abbreviation ca_conj_a where "ca_conj_a \<equiv> \<forall>P Q. [\<^bold>\<circ>\<^sup>AP,\<^bold>\<circ>\<^sup>AQ \<turnstile> \<^bold>\<circ>\<^sup>A(P \<^bold>\<and> Q)]"
abbreviation ca_conj_b where "ca_conj_b \<equiv> \<forall>P Q. [\<^bold>\<circ>\<^sup>BP,\<^bold>\<circ>\<^sup>BQ \<turnstile> \<^bold>\<circ>\<^sup>B(P \<^bold>\<and> Q)]"
abbreviation ca_disj_a where "ca_disj_a \<equiv> \<forall>P Q. [\<^bold>\<circ>\<^sup>AP,\<^bold>\<circ>\<^sup>AQ \<turnstile> \<^bold>\<circ>\<^sup>A(P \<^bold>\<or> Q)]"
abbreviation ca_disj_b where "ca_disj_b \<equiv> \<forall>P Q. [\<^bold>\<circ>\<^sup>BP,\<^bold>\<circ>\<^sup>BQ \<turnstile> \<^bold>\<circ>\<^sup>B(P \<^bold>\<or> Q)]"
abbreviation ca_impl_a where "ca_impl_a \<equiv> \<forall>P Q. [\<^bold>\<circ>\<^sup>AP,\<^bold>\<circ>\<^sup>AQ \<turnstile> \<^bold>\<circ>\<^sup>A(P \<^bold>\<rightarrow> Q)]"
abbreviation ca_impl_b where "ca_impl_b \<equiv> \<forall>P Q. [\<^bold>\<circ>\<^sup>BP,\<^bold>\<circ>\<^sup>BQ \<turnstile> \<^bold>\<circ>\<^sup>B(P \<^bold>\<rightarrow> Q)]"
abbreviation ca_a where "ca_a \<equiv> ca_conj_a \<and> ca_disj_a \<and> ca_impl_a"
abbreviation ca_b where "ca_b \<equiv> ca_conj_b \<and> ca_disj_b \<and> ca_impl_b"

(**cf*)
lemma "BORDER \<B> \<Longrightarrow> cf" nitpick oops (*countermodel*)

(**ce*)
lemma "BORDER \<B> \<Longrightarrow> ce" nitpick oops (*countermodel*)

(**ciw*)
lemma prop_ciw_a: "ciw_a" by (simp add: conn)
lemma prop_ciw_b: "ciw_b" by (simp add: conn svfun_compl_def)

(**ci*)
lemma "BORDER \<B> \<Longrightarrow> ci_a" nitpick oops (*countermodel*)
lemma "BORDER \<B> \<Longrightarrow> ci_b" nitpick oops (*countermodel*)

(**cl*)
lemma "BORDER \<B> \<Longrightarrow> cl_a" nitpick oops (*countermodel*)
lemma "BORDER \<B> \<Longrightarrow> cl_b" nitpick oops (*countermodel*)

(**ca_conj*)
lemma prop_ca_conj_b: "nMULT\<^sup>b \<B> = ca_conj_b" by (metis MULT_b_def nMULTb_compl sfun_compl_invol)
lemma prop_ca_conj_a: "nMULTr\<^sup>b \<B> = ca_conj_a" unfolding cond op_fixpoint_def by (smt (z3) compl_def dimpl_def join_def meet_def op_fixpoint_def subset_def subset_in_def)

(**ca_disj*)
lemma prop_ca_disj_b: "ADDI\<^sup>a \<B> = ca_disj_b" by (simp add: nADDI_a_def nADDIa_compl)
lemma prop_ca_disj_a: "nMULTr\<^sup>a \<B> = ca_disj_a" (*nitpick*) oops (*TODO: verify*)

(**ca_impl*)
lemma "BORDER \<B> \<Longrightarrow> ca_impl_a" nitpick oops (*countermodel*)
lemma "BORDER \<B> \<Longrightarrow> ca_impl_b" nitpick oops (*countermodel*)

end