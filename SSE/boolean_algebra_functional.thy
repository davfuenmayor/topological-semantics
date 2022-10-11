theory boolean_algebra_functional
  imports boolean_algebra
begin

subsection \<open>Algebraic connectives on set-valued functions\<close>

(**Functions with sets in their codomain will be called here 'set-valued functions'.
  We conveniently define some (2nd-order) Boolean operations on them.*)

(**The 'meet' and 'join' of two set-valued functions: *)
definition svfun_meet::"('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>)" (infixr "\<sqinter>" 62) 
  where "\<phi> \<sqinter> \<psi> \<equiv> \<lambda>X. (\<phi> X) \<^bold>\<and> (\<psi> X)"
definition svfun_join::"('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>)" (infixr "\<squnion>" 61) 
  where "\<phi> \<squnion> \<psi> \<equiv> \<lambda>X. (\<phi> X) \<^bold>\<or> (\<psi> X)"
(**analogously, we can define an 'implication' and a 'complement'*)
definition svfun_impl::"('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>)" (infixr "\<sqsupset>" 61) 
  where "\<psi> \<sqsupset> \<phi> \<equiv> \<lambda>X. (\<psi> X) \<^bold>\<rightarrow> (\<phi> X)"
definition svfun_compl::"('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>)" ("(_\<^sup>c)") 
  where "\<phi>\<^sup>c \<equiv> \<lambda>X. \<^bold>\<midarrow>(\<phi> X)"
(**There are two natural 0-ary set-valued functions (aka. constants) *)
definition svfun_top::"'i \<Rightarrow> 'p \<sigma>" ("\<top>") 
  where "\<top>A \<equiv> \<^bold>\<top>"
definition svfun_bot::"'i \<Rightarrow> 'p \<sigma>" ("\<bottom>") 
  where "\<bottom>A \<equiv> \<^bold>\<bottom>"

named_theorems conn2 (*to group together definitions for 2nd-order algebraic connectives*)
declare svfun_meet_def[conn2] svfun_join_def[conn2] svfun_impl_def[conn2]
        svfun_compl_def[conn2] svfun_top_def[conn2] svfun_bot_def[conn2]

(**And, of course, set-valued functions are naturally ordered in the expected way*)
definition svfun_sub::"('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" (infixr "\<sqsubseteq>" 55) 
  where "\<psi> \<sqsubseteq> \<phi> \<equiv> \<forall>X. (\<psi> X) \<^bold>\<preceq> (\<phi> X)"
definition svfun_equ::"('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> bool" (infixr "\<cong>" 55) 
  where "\<psi> \<cong> \<phi> \<equiv> \<forall>X. (\<psi> X) \<^bold>\<approx> (\<phi> X)"

named_theorems order2 (*to group together definitions for 2nd-order algebraic connectives*)
declare svfun_sub_def[order2] svfun_equ_def[order2]

lemma svfun_sub_char: "(\<psi> \<sqsubseteq> \<phi>) = (\<psi> \<sqsupset> \<phi> \<cong> \<top>)" by (simp add: BA_impl svfun_equ_def svfun_impl_def svfun_sub_def svfun_top_def)
lemma svfun_equ_char: "(\<psi> \<cong> \<phi>) = (\<psi> \<sqsubseteq> \<phi> \<and> \<phi> \<sqsubseteq> \<psi>)" unfolding order2 setequ_char by blast
lemma svfun_equ_ext: "(\<psi> \<cong> \<phi>) = (\<psi> = \<phi>)" by (meson ext setequ_ext svfun_equ_def)

(**Clearly, set-valued functions form a Boolean algebra. We can prove some interesting relationships*)
lemma svfun_deMorgan1: "(\<psi> \<sqinter> \<phi>)\<^sup>c = (\<psi>\<^sup>c) \<squnion> (\<phi>\<^sup>c)" unfolding conn conn2 by simp
lemma svfun_deMorgan2: "(\<psi> \<squnion> \<phi>)\<^sup>c = (\<psi>\<^sup>c) \<sqinter> (\<phi>\<^sup>c)" unfolding conn conn2 by simp
lemma svfun_impl_char: "\<psi> \<sqsupset> \<phi> = \<psi>\<^sup>c \<squnion> \<phi>" unfolding conn conn2 by simp


subsection \<open>Further algebraic connectives on operators\<close>

(**Dual to set-valued functions we can have set-domain functions. For them we can define the 'dual-complement'*)
definition sdfun_dcompl::"('p \<sigma> \<Rightarrow> 'i) \<Rightarrow> ('p \<sigma> \<Rightarrow> 'i)" ("(_\<^sup>-)") 
  where "\<phi>\<^sup>- \<equiv> \<lambda>X. \<phi>(\<^bold>\<midarrow>X)"
lemma sdfun_dcompl_char: "\<phi>\<^sup>- = (\<lambda>X. \<exists>Y. (\<phi> Y) \<and> (X = \<^bold>\<midarrow>Y))" by (metis BA_dn setequ_ext sdfun_dcompl_def)

(**Operators are a particularly important kind of functions. They are both set-valued and set-domain.
Thus our algebra of operators inherits the connectives defined above plus some idiosyncratic ones. *)

(**We conveniently define the 'dual' of an operator*)
definition op_dual::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('p \<sigma> \<Rightarrow> 'p \<sigma>)" ("(_\<^sup>d)") 
  where "\<phi>\<^sup>d \<equiv> \<lambda>X. \<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>X))"

(**The following two 0-ary connectives (i.e operator 'constants') exist already (but somehow implicitly).
  We just make them explicit by introducing some convenient notation.*)
definition id_op::"'p \<sigma> \<Rightarrow> 'p \<sigma>" ("+") 
  where "+A \<equiv> A" (*introduces notation (+) to refer to 'identity' operator*)
abbreviation compl_op::"'p \<sigma> \<Rightarrow> 'p \<sigma>" ("-") 
  where "-A \<equiv> \<^bold>\<midarrow>A" (*to refer to 'complement' operator as (-)*)

declare sdfun_dcompl_def[conn2] op_dual_def[conn2] id_op_def[conn2]

(**We now prove some lemmas (some of them might help provers in their hard work).*)
lemma dual_compl_char1: "\<phi>\<^sup>- = (\<phi>\<^sup>d)\<^sup>c" unfolding conn2 conn order by simp
lemma dual_compl_char2: "\<phi>\<^sup>- = (\<phi>\<^sup>c)\<^sup>d" unfolding conn2 conn order by simp
lemma sfun_compl_invol: "\<phi>\<^sup>c\<^sup>c = \<phi>" unfolding conn2 conn order by simp
lemma dual_invol: "\<phi>\<^sup>d\<^sup>d = \<phi>" unfolding conn2 conn order by simp
lemma dualcompl_invol: "(\<phi>\<^sup>-)\<^sup>- = \<phi>" unfolding conn2 conn order by simp

lemma "(+)\<^sup>d = (+)" unfolding conn2 conn by simp
lemma "(+)\<^sup>c = (-)" unfolding conn2 conn by simp
lemma "(\<phi> \<squnion> \<psi>)\<^sup>d = (\<phi>\<^sup>d) \<sqinter> (\<psi>\<^sup>d)" unfolding conn2 conn by simp
lemma "(\<phi> \<squnion> \<psi>)\<^sup>c = (\<phi>\<^sup>c) \<sqinter> (\<psi>\<^sup>c)" unfolding conn2 conn by simp
lemma "(\<phi> \<sqinter> \<psi>)\<^sup>d = (\<phi>\<^sup>d) \<squnion> (\<psi>\<^sup>d)" unfolding conn2 conn by simp
lemma "(\<phi> \<sqinter> \<psi>)\<^sup>c = (\<phi>\<^sup>c) \<squnion> (\<psi>\<^sup>c)" unfolding conn2 conn by simp

(**The notion of a fixed-point is fundamental. We speak of sets being fixed-points of operators.
We define a function that given an operator returns the set of all its fixed-points.*)
definition fixpoints::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('p \<sigma>)\<sigma>" ("fp") 
  where "fp \<phi> \<equiv> \<lambda>X. (\<phi> X) \<^bold>\<approx> X"
(**We can in fact 'operationalize' the function above thus obtaining a (2nd-order) 'fixed-point' connective*)
definition op_fixpoint::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('p \<sigma> \<Rightarrow> 'p \<sigma>)" ("(_\<^sup>f\<^sup>p)") 
  where "\<phi>\<^sup>f\<^sup>p \<equiv> \<lambda>X. (\<phi> X) \<^bold>\<leftrightarrow> X"

declare fixpoints_def[conn2] op_fixpoint_def[conn2]

(**Interestingly, the fixed-point connective is definable in terms of the others*)
lemma op_fixpoint_char: "\<phi>\<^sup>f\<^sup>p = (\<phi> \<sqinter> (+)) \<squnion> (\<phi>\<^sup>c \<sqinter> (-))" unfolding conn2 order conn by blast

(**The set of fixed-points of the dual of an operator coincides with the set of complements of its fixed-points*)
lemma fp_dual: "(fp \<phi>\<^sup>d) = (fp \<phi>)\<^sup>-" unfolding order conn conn2 by blast

(**The fixed-points function and the fixed-point connective are essentially related.*)
lemma fp_rel: "fp \<phi> A \<longleftrightarrow> (\<phi>\<^sup>f\<^sup>p A) \<^bold>\<approx> \<^bold>\<top>" unfolding conn2 order conn by simp
lemma fp_d_rel:  "fp \<phi>\<^sup>d A \<longleftrightarrow> \<phi>\<^sup>f\<^sup>p(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<top>" unfolding conn2 order conn by blast
lemma fp_c_rel: "fp \<phi>\<^sup>c A \<longleftrightarrow> \<phi>\<^sup>f\<^sup>p A \<^bold>\<approx> \<^bold>\<bottom>" unfolding conn2 order conn by blast
lemma fp_dc_rel: "fp (\<phi>\<^sup>-) A \<longleftrightarrow> \<phi>\<^sup>f\<^sup>p(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<bottom>" unfolding conn2 order conn by simp

lemma ofp_invol: "(\<phi>\<^sup>f\<^sup>p)\<^sup>f\<^sup>p = \<phi>" unfolding conn2 order conn by blast
lemma ofp_comm_compl: "(\<phi>\<^sup>c)\<^sup>f\<^sup>p = (\<phi>\<^sup>f\<^sup>p)\<^sup>c" unfolding conn2 order conn by blast
lemma ofp_comm_dc1: "(\<phi>\<^sup>d)\<^sup>f\<^sup>p = (\<phi>\<^sup>f\<^sup>p)\<^sup>-" unfolding conn2 order conn by blast
lemma ofp_comm_dc2:"(\<phi>\<^sup>-)\<^sup>f\<^sup>p = (\<phi>\<^sup>f\<^sup>p)\<^sup>d" unfolding conn2 order conn by simp



(**In fact, function composition can be seen as an additional binary connective for operators.
  We show below some interesting relationships that hold: *)
lemma "X\<^sup>c = ((-) \<circ> X)" by (simp add: fun_comp_def svfun_compl_def)
lemma "X\<^sup>- = (X \<circ> (-))" by (simp add: fun_comp_def sdfun_dcompl_def)
lemma "X\<^sup>d = ((-) \<circ> X \<circ> (-))" by (simp add: fun_comp_def op_dual_def)
(*TODO: do more*)

(**There are also some useful dualities regarding the images of operators*)
lemma im_compl: "\<lbrakk>\<phi>\<^sup>c D\<rbrakk>  = \<lbrakk>\<phi> D\<rbrakk>\<^sup>-" unfolding image_def svfun_compl_def sdfun_dcompl_def using BA_cmpl_equ setequ_ext by blast
lemma im_dual1: "\<lbrakk>\<phi>\<^sup>d D\<rbrakk>  = \<lbrakk>\<phi> D\<^sup>-\<rbrakk>\<^sup>-" unfolding image_def op_dual_def sdfun_dcompl_def by (metis (no_types, opaque_lifting) BA_dn setequ_ext)
lemma im_dual2: "\<lbrakk>\<phi>\<^sup>d D\<rbrakk>  = \<lbrakk>\<phi>\<^sup>c D\<^sup>-\<rbrakk>" by (simp add: im_compl im_dual1)
lemma im_dual3: "\<lbrakk>\<phi>\<^sup>d D\<^sup>-\<rbrakk> = \<lbrakk>\<phi> D\<rbrakk>\<^sup>-" by (simp add: dualcompl_invol im_compl im_dual2)
(*TODO: do more*)


end