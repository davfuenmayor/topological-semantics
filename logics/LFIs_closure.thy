theory LFIs_closure
  imports "logical_consequence" "../conditions/conditions_relativized_infinitary"
begin

section \<open>Logics of Formal Inconsistency (LFIs)\<close>

(**The LFIs are a family of paraconsistent logics featuring a 'consistency' operator @{text "\<^bold>\<circ>"}
that can be used to recover some classical properties of negation (in particular ECQ).
We show a shallow semantical embedding of logics at least as strong as the LFI RmbC-ciw*)

(*Let us assume a concrete type w (for 'worlds' or 'points')*)
typedecl w
(*Let us assume the following primitive unary operation \<C> (intended as a closure operator)*)
consts \<C>::"w \<sigma> \<Rightarrow> w \<sigma>"

(*From the topological cube of opposition:*)
abbreviation "\<I> \<equiv> \<C>\<^sup>d" 
abbreviation "\<B> \<equiv> (\<C>\<^sup>f\<^sup>p)\<^sup>d" 
lemma "\<C>\<^sup>d\<^sup>- = \<B>\<^sup>f\<^sup>p" by (simp add: ofp_comm_dc1 ofp_invol)

(*let us recall that: *)
lemma "EXPN \<C> = CNTR \<B>" using EXPN_CNTR_dual1 EXPN_fp by blast

(**For LFIs we use the negation previously defined as \<C>\<^sup>d\<^sup>- = \<B>\<^sup>f\<^sup>p *)
abbreviation cneg ("\<^bold>\<not>_"[70]71) where "cneg \<equiv> \<C>\<^sup>d\<^sup>-"

(**In terms of the border operator the negation looks as follows:*)
lemma cneg_char: "EXPN \<C> \<longrightarrow> \<^bold>\<not>A \<^bold>= \<^bold>\<midarrow>A \<^bold>\<or> (\<B> A)" by (smt (verit, ccfv_SIG) EXPN_def compl_def dimpl_def join_def ofp_comm_dc2 op_fixpoint_def sdfun_dcompl_def setequ_def subset_def)

abbreviation "CLOSURE \<phi> \<equiv> ADDI \<phi> \<and> EXPN \<phi> \<and> NORM \<phi> \<and> IDEM \<phi>"

(**This negation is of course boldly paraconsistent for local consequence.*)
lemma "CLOSURE \<C> \<longrightarrow> [a, \<^bold>\<not>a \<turnstile> b]" nitpick oops (*countermodel*)
lemma "CLOSURE \<C> \<longrightarrow> [a, \<^bold>\<not>a \<turnstile> \<^bold>\<not>b]" nitpick oops (*countermodel*)

(**This negation is boldly paraconsistent for global consequence unless NORM \<C> holds.*)
lemma "[a, \<^bold>\<not>a \<turnstile>\<^sub>g b]" nitpick oops (*countermodel*)
lemma "[a, \<^bold>\<not>a \<turnstile>\<^sub>g \<^bold>\<not>b]" nitpick oops (*countermodel*)
lemma "NORM \<C> \<longrightarrow> [a, \<^bold>\<not>a \<turnstile>\<^sub>g b]" by (metis (mono_tags, opaque_lifting) NORM_def bottom_def compl_def sdfun_dcompl_def setequ_def setequ_ext)
lemma "NORM \<C> \<longrightarrow> [a, \<^bold>\<not>a \<turnstile>\<^sub>g \<^bold>\<not>b]" by (metis (no_types, opaque_lifting) NORM_def bottom_def compl_def dual_compl_char2 op_dual_def setequ_def setequ_ext svfun_compl_def)

(**We define two pairs of in/consistency operators and show how they relate to each other.
Using LFIs terminology, the minimal logic so encoded corresponds to 'RmbC-ciw' (cf. @{cite RLFI}).*)
abbreviation op_inc_a::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<bullet>\<^sup>A_" [57]58) (* \<bullet> as truth-glut *)
  where "\<bullet>\<^sup>AA \<equiv> A \<^bold>\<and> \<^bold>\<not>A"
abbreviation op_con_a::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<^bold>\<circ>\<^sup>A_" [57]58) 
  where "\<^bold>\<circ>\<^sup>AA \<equiv> \<^bold>\<midarrow>\<bullet>\<^sup>AA"
abbreviation op_inc_b::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<bullet>\<^sup>B_" [57]58) (* \<bullet> as border *)
  where "\<bullet>\<^sup>BA \<equiv> \<B> A"
abbreviation op_con_b::"w \<sigma> \<Rightarrow> w \<sigma>" ("\<^bold>\<circ>\<^sup>B_" [57]58) 
  where "\<^bold>\<circ>\<^sup>BA \<equiv> \<B>\<^sup>- A"

(**Observe that assumming EXPN \<C> are we allowed to exchange A and B variants.*)
lemma pincAB: "EXPN \<C> \<longrightarrow> \<bullet>\<^sup>AA \<^bold>= \<bullet>\<^sup>BA" by (smt (verit, ccfv_threshold) cneg_char compl_def dimpl_def join_def meet_def op_dual_def op_fixpoint_def sdfun_dcompl_def setequ_def)
lemma pconAB: "EXPN \<C> \<longrightarrow> \<^bold>\<circ>\<^sup>AA \<^bold>= \<^bold>\<circ>\<^sup>BA" by (metis pincAB setequ_ext svfun_compl_def)

(**Variants A and B give us slightly different properties (there are countermodels for those not shown).*)
lemma Prop1: "\<^bold>\<circ>\<^sup>BA \<^bold>= \<I>\<^sup>f\<^sup>p A" by (simp add: dual_compl_char1 ofp_comm_dc1 setequ_ext)
lemma Prop2: "\<^bold>\<circ>\<^sup>AA \<^bold>= A \<^bold>\<rightarrow> \<I> A" by (simp add: BA_deMorgan2 impl_char op_dual_def sdfun_dcompl_def)
lemma Prop3: "fp \<C> A \<longleftrightarrow> \<^bold>\<circ>\<^sup>B\<^bold>\<midarrow>A \<^bold>= \<^bold>\<top>" by (metis Prop1 dual_invol fp_d_rel setequ_ext)
lemma Prop4a: "fp \<I> A \<longleftrightarrow> \<^bold>\<circ>\<^sup>BA \<^bold>= \<^bold>\<top>" by (simp add: dual_compl_char1 fp_rel ofp_comm_dc1)
lemma Prop4b: "fp \<I> A  \<longrightarrow> \<^bold>\<circ>\<^sup>AA \<^bold>= \<^bold>\<top>" by (metis BA_impl L13 L4 Prop2 fixpoints_def setequ_ext)

(**The 'principle of gentle explosion' works for both variants (both locally and globally)*)
lemma "[\<^bold>\<circ>\<^sup>Aa, a, \<^bold>\<not>a \<turnstile> b]" by (metis (mono_tags, lifting) compl_def meet_def subset_def) 
lemma "[\<^bold>\<circ>\<^sup>Aa, a, \<^bold>\<not>a \<turnstile>\<^sub>g b]" by (metis compl_def meet_def)
lemma "[\<^bold>\<circ>\<^sup>Ba, a, \<^bold>\<not>a \<turnstile> b]" by (smt (verit) compl_def dimpl_def dual_compl_char1 meet_def op_fixpoint_def sdfun_dcompl_def subset_def)
lemma "[\<^bold>\<circ>\<^sup>Ba, a, \<^bold>\<not>a \<turnstile>\<^sub>g b]" by (metis ofp_comm_dc2 ofp_fixpoint_compl_def sdiff_def)


(**We show how all (local) contraposition variants (among others) can be recovered using the
 consistency operators.*)

lemma cons_lcop1: "EXPN \<C> \<longrightarrow> [\<^bold>\<circ>\<^sup>Ab, a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" by (smt (verit) cneg_char compl_def impl_def join_def meet_def setequ_ext subset_def)
lemma "[\<^bold>\<circ>\<^sup>Bb, a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" nitpick oops
lemma cons_lcop2: "EXPN \<C> \<longrightarrow> [\<^bold>\<circ>\<^sup>Bb, a \<^bold>\<rightarrow> b \<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" by (metis cons_lcop1 pconAB setequ_ext)
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
lemma "CLOSURE \<C> \<Longrightarrow> cf" nitpick oops (*countermodel*)

(**ce*)
lemma "CLOSURE \<C> \<Longrightarrow> ce" nitpick oops (*countermodel*)

(**ciw*)
lemma prop_ciw_a: "ciw_a" by (simp add: conn)
lemma prop_ciw_b: "ciw_b" by (simp add: conn svfun_compl_def)

(**ci*)
lemma "CLOSURE \<C> \<Longrightarrow> ci_a" nitpick oops (*countermodel*)
lemma "CLOSURE \<C> \<Longrightarrow> ci_b" nitpick oops (*countermodel*)

(**cl*)
lemma "CLOSURE \<C> \<Longrightarrow> cl_a" nitpick oops (*countermodel*)
lemma "CLOSURE \<C> \<Longrightarrow> cl_b" nitpick oops (*countermodel*)

(**ca_conj*)
lemma prop_ca_conj_b: "EXPN \<C> \<Longrightarrow> ADDI\<^sup>a \<C> = ca_conj_b" by (metis ADDIa_MULTb_dual2 ADDIr_a_cmpl ADDIr_a_equ' ADDIr_a_fpc EXPN_fpc MULT_b_def dual_compl_char1 dual_compl_char2 dual_invol nADDIa_compl nADDIr_a_equ' nEXPN_CNTR_compl)
lemma prop_ca_conj_a: "ADDIr\<^sup>a \<C> = ca_conj_a" (*nitpick*) oops (*TODO: verify*)

(**ca_disj*)
lemma prop_ca_disj_b: "EXPN \<C> \<Longrightarrow> ADDI\<^sup>b \<C> = ca_disj_b" (*nitpick*) oops (*TODO: verify*)
lemma prop_ca_disj_a: "ADDIr\<^sup>b \<C> = ca_disj_a" (*nitpick*) oops (*TODO: verify*)

(**ca_impl*)
lemma "CLOSURE \<C> \<Longrightarrow> ca_impl_a" nitpick oops (*countermodel*)
lemma "CLOSURE \<C> \<Longrightarrow> ca_impl_b" nitpick oops (*countermodel*)

end