theory boolean_algebra_functional
  imports boolean_algebra
begin

subsection \<open>Algebraic connectives on set-valued functions\<close>

(**Functions with sets in their codomain will be called here 'set-valued functions'.
  We conveniently define some (2nd-order) Boolean operations on them.*)

(**The 'meet' and 'join' of two set-valued functions: *)
definition svfun_meet::"('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'w \<sigma>)" (infixr "\<^bold>\<and>''" 62) 
  where "\<phi> \<^bold>\<and>' \<psi> \<equiv> \<lambda>x. (\<phi> x) \<^bold>\<and> (\<psi> x)"
definition svfun_join::"('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'w \<sigma>)" (infixr "\<^bold>\<or>''" 61) 
  where "\<phi> \<^bold>\<or>' \<psi> \<equiv> \<lambda>x. (\<phi> x) \<^bold>\<or> (\<psi> x)"
(**analogously, we can define an 'implication' and a 'complement'*)
definition svfun_impl::"('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'w \<sigma>)" (infixr "\<^bold>\<rightarrow>''" 61) 
  where "\<psi> \<^bold>\<rightarrow>' \<phi> \<equiv> \<lambda>x. (\<psi> x) \<^bold>\<rightarrow> (\<phi> x)"
definition svfun_compl::"('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'w \<sigma>)" ("(_\<^sup>c)") 
  where "\<phi>\<^sup>c \<equiv> \<lambda>x. \<^bold>\<midarrow>(\<phi> x)"
(**There are two natural 0-ary connectives (aka. constants) *)
definition svfun_top::"'i \<Rightarrow> 'w \<sigma>" ("\<^bold>\<top>''") 
  where "\<^bold>\<top>' \<equiv> \<lambda>x. \<^bold>\<top>"
definition svfun_bot::"'i \<Rightarrow> 'w \<sigma>" ("\<^bold>\<bottom>''") 
  where "\<^bold>\<bottom>' \<equiv> \<lambda>x. \<^bold>\<bottom>"

named_theorems conn2 (*to group together definitions for 2nd-order algebraic connectives*)
declare svfun_meet_def[conn2] svfun_join_def[conn2] svfun_impl_def[conn2]
        svfun_compl_def[conn2] svfun_top_def[conn2] svfun_bot_def[conn2]

(**And, of course, set-valued functions are naturally ordered in the expected way*)
definition svfun_sub::"('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" (infixr "\<^bold>\<le>''" 55) 
  where "\<psi> \<^bold>\<le>' \<phi> \<equiv> \<forall>x. (\<psi> x) \<^bold>\<le> (\<phi> x)"
definition svfun_equ::"('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" (infixr "\<^bold>=''" 55) 
  where "\<psi> \<^bold>=' \<phi> \<equiv> \<forall>x. (\<psi> x) \<^bold>= (\<phi> x)"

named_theorems order2 (*to group together definitions for 2nd-order algebraic connectives*)
declare svfun_sub_def[order2] svfun_equ_def[order2]

lemma svfun_sub_char: "(\<psi> \<^bold>\<le>' \<phi>) = (\<psi> \<^bold>\<rightarrow>' \<phi> \<^bold>=' \<^bold>\<top>')" by (simp add: BA_impl svfun_equ_def svfun_impl_def svfun_sub_def svfun_top_def)
lemma svfun_equ_char: "(\<psi> \<^bold>=' \<phi>) = (\<psi> \<^bold>\<le>' \<phi> \<and> \<phi> \<^bold>\<le>' \<psi>)" unfolding order2 setequ_char by blast
lemma svfun_equ_ext: "(\<psi> \<^bold>=' \<phi>) = (\<psi> = \<phi>)" by (meson ext setequ_ext svfun_equ_def)

(**Clearly, set-valued functions form a Boolean algebra. We can prove some interesting relationships*)
lemma svfun_compl_char: "\<phi>\<^sup>c = (\<phi> \<^bold>\<rightarrow>' \<^bold>\<bottom>')" unfolding conn conn2 by simp
lemma svfun_impl_char1: "(\<psi> \<^bold>\<rightarrow>' \<phi>) = (\<psi>\<^sup>c \<^bold>\<or>' \<phi>)" unfolding conn conn2 by simp
lemma svfun_impl_char2: "(\<psi> \<^bold>\<rightarrow>' \<phi>) = (\<psi> \<^bold>\<and>' (\<phi>\<^sup>c))\<^sup>c" unfolding conn conn2 by simp
lemma svfun_deMorgan1: "(\<psi> \<^bold>\<and>' \<phi>)\<^sup>c = (\<psi>\<^sup>c) \<^bold>\<or>' (\<phi>\<^sup>c)" unfolding conn conn2 by simp
lemma svfun_deMorgan2: "(\<psi> \<^bold>\<or>' \<phi>)\<^sup>c = (\<psi>\<^sup>c) \<^bold>\<and>' (\<phi>\<^sup>c)" unfolding conn conn2 by simp


subsection \<open>Further algebraic connectives on operators\<close>

(**Dual to set-valued functions we can have set-domain functions. For them we can define the 'dual-complement'*)
definition sdfun_dcompl::"('w \<sigma> \<Rightarrow> 'i) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'i)" ("(_\<^sup>-)") 
  where "\<phi>\<^sup>- \<equiv> \<lambda>X. \<phi>(\<^bold>\<midarrow>X)"
lemma sdfun_dcompl_char: "\<phi>\<^sup>- = (\<lambda>X. \<exists>Y. (\<phi> Y) \<and> (X = \<^bold>\<midarrow>Y))" by (metis BA_dn setequ_ext sdfun_dcompl_def)

(**Operators are a particularly important kind of functions. They are both set-valued and set-domain.
Thus our algebra of operators inherits the connectives defined above plus some idiosyncratic ones. *)

(**We conveniently define the 'dual' of an operator*)
definition op_dual::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("(_\<^sup>d)") 
  where "\<phi>\<^sup>d \<equiv> \<lambda>X. \<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>X))"

(**The following two 0-ary connectives (i.e operator 'constants') exist already (but somehow implicitly).
  We just make them explicit by introducing some convenient notation.*)
definition id_op::"'w \<sigma> \<Rightarrow> 'w \<sigma>" ("\<^bold>e") 
  where "\<^bold>e \<equiv> \<lambda>X. X" (*introduces notation to refer to 'identity' operator*)
definition compl_op::"'w \<sigma> \<Rightarrow> 'w \<sigma>" ("\<^bold>n") 
  where "\<^bold>n \<equiv> \<lambda>X. \<^bold>\<midarrow>X" (*to refer to 'complement' operator*)

declare sdfun_dcompl_def[conn2] op_dual_def[conn2] id_op_def[conn2] compl_op_def[conn2]

(**We now prove some lemmas (some of them might help provers in their hard work).*)
lemma dual_compl_char1: "\<phi>\<^sup>- = (\<phi>\<^sup>d)\<^sup>c" unfolding conn2 conn order by simp
lemma dual_compl_char2: "\<phi>\<^sup>- = (\<phi>\<^sup>c)\<^sup>d" unfolding conn2 conn order by simp
lemma sfun_compl_invol: "\<phi>\<^sup>c\<^sup>c = \<phi>" unfolding conn2 conn order by simp
lemma dual_invol: "\<phi>\<^sup>d\<^sup>d = \<phi>" unfolding conn2 conn order by simp
lemma dualcompl_invol: "(\<phi>\<^sup>-)\<^sup>- = \<phi>" unfolding conn2 conn order by simp

lemma op_prop1: "\<^bold>e\<^sup>d = \<^bold>e" unfolding conn2 conn by simp
lemma op_prop2: "\<^bold>n\<^sup>d = \<^bold>n" unfolding conn2 conn by simp
lemma op_prop3: "\<^bold>e\<^sup>c = \<^bold>n" unfolding conn2 conn by simp
lemma op_prop4: "(\<phi> \<^bold>\<or>' \<psi>)\<^sup>d = (\<phi>\<^sup>d) \<^bold>\<and>' (\<psi>\<^sup>d)" unfolding conn2 conn by simp
lemma op_prop5: "(\<phi> \<^bold>\<or>' \<psi>)\<^sup>c = (\<phi>\<^sup>c) \<^bold>\<and>' (\<psi>\<^sup>c)" unfolding conn2 conn by simp
lemma op_prop6: "(\<phi> \<^bold>\<and>' \<psi>)\<^sup>d = (\<phi>\<^sup>d) \<^bold>\<or>' (\<psi>\<^sup>d)" unfolding conn2 conn by simp
lemma op_prop7: "(\<phi> \<^bold>\<and>' \<psi>)\<^sup>c = (\<phi>\<^sup>c) \<^bold>\<or>' (\<psi>\<^sup>c)" unfolding conn2 conn by simp
lemma op_prop8: "\<^bold>\<top>' = \<^bold>n \<^bold>\<or>' \<^bold>e" unfolding conn2 conn by simp
lemma op_prop9: "\<^bold>\<bottom>' = \<^bold>n \<^bold>\<and>' \<^bold>e" unfolding conn2 conn by simp

(**The notion of a fixed-point is fundamental. We speak of sets being fixed-points of operators.
We define a function that given an operator returns the set of all its fixed-points.*)
definition fixpoints::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma>)\<sigma>" ("fp") 
  where "fp \<phi> \<equiv> \<lambda>X. (\<phi> X) \<^bold>= X"
(**We can in fact 'operationalize' the function above thus obtaining a (2nd-order) 'fixed-point' connective*)
definition op_fixpoint::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("(_\<^sup>f\<^sup>p)")
(* definition op_fixpoint ("(_\<^sup>f\<^sup>p)")  *)
  where "\<phi>\<^sup>f\<^sup>p \<equiv> \<lambda>X. (\<phi> X) \<^bold>\<leftrightarrow> X"

declare fixpoints_def[conn2] op_fixpoint_def[conn2]

(**Interestingly, the fixed-point connective is definable in terms of the others*)
lemma op_fixpoint_char: "\<phi>\<^sup>f\<^sup>p = (\<phi> \<^bold>\<and>' \<^bold>e) \<^bold>\<or>' (\<phi>\<^sup>c \<^bold>\<and>' \<^bold>n)" unfolding conn2 order conn by blast

(**Given an operator \<phi>: the fixed-points of \<phi>'s dual is the set of complements of \<phi>' fixed-points*)
lemma fp_dual: "fp \<phi>\<^sup>d = (fp \<phi>)\<^sup>-" unfolding order conn conn2 by blast
(**the fixed-points of \<phi>'s complement is the set of complements of the fixed-points of \<phi>'s dual-complement*)
lemma fp_compl: "fp \<phi>\<^sup>c = (fp (\<phi>\<^sup>-))\<^sup>-" by (simp add: dual_compl_char2 dualcompl_invol fp_dual)
(**the fixed-points of \<phi>'s dual-complement is the set of complements of the fixed-points of \<phi>'s complement*)
lemma fp_dcompl: "fp (\<phi>\<^sup>-) = (fp \<phi>\<^sup>c)\<^sup>-" by (simp add: dualcompl_invol fp_compl)

(**The fixed-points function and the fixed-point connective are essentially related.*)
lemma fp_rel: "fp \<phi> A \<longleftrightarrow> (\<phi>\<^sup>f\<^sup>p A) \<^bold>= \<^bold>\<top>" unfolding conn2 order conn by simp
lemma fp_d_rel:  "fp \<phi>\<^sup>d A \<longleftrightarrow> \<phi>\<^sup>f\<^sup>p(\<^bold>\<midarrow>A) \<^bold>= \<^bold>\<top>" unfolding conn2 order conn by blast
lemma fp_c_rel: "fp \<phi>\<^sup>c A \<longleftrightarrow> \<phi>\<^sup>f\<^sup>p A \<^bold>= \<^bold>\<bottom>" unfolding conn2 order conn by blast
lemma fp_dc_rel: "fp (\<phi>\<^sup>-) A \<longleftrightarrow> \<phi>\<^sup>f\<^sup>p(\<^bold>\<midarrow>A) \<^bold>= \<^bold>\<bottom>" unfolding conn2 order conn by simp

(**The fixed-point operation is involutive*)
lemma ofp_invol: "(\<phi>\<^sup>f\<^sup>p)\<^sup>f\<^sup>p = \<phi>" unfolding conn2 order conn by blast
(**and commutes the dual with the dual-complement operations*)
lemma ofp_comm_dc1: "(\<phi>\<^sup>d)\<^sup>f\<^sup>p = (\<phi>\<^sup>f\<^sup>p)\<^sup>-" unfolding conn2 order conn by blast
lemma ofp_comm_dc2:"(\<phi>\<^sup>-)\<^sup>f\<^sup>p = (\<phi>\<^sup>f\<^sup>p)\<^sup>d" unfolding conn2 order conn by simp

(**The fixed-point operation commutes with the complement*)
lemma ofp_comm_compl: "(\<phi>\<^sup>c)\<^sup>f\<^sup>p = (\<phi>\<^sup>f\<^sup>p)\<^sup>c" unfolding conn2 order conn by blast
(**The above motivates the following alternative definition for a 'complemented-fixed-point' operation*)
lemma ofp_fixpoint_compl_def: "\<phi>\<^sup>f\<^sup>p\<^sup>c = (\<lambda>X. (\<phi> X) \<^bold>\<triangle> X)" unfolding conn2 conn by simp
(**Analogously, the complemented fixed-point connective is also definable in terms of the others*)
lemma op_fixpoint_compl_char: "\<phi>\<^sup>f\<^sup>p\<^sup>c = (\<phi> \<^bold>\<or>' \<^bold>e) \<^bold>\<and>' (\<phi>\<^sup>c \<^bold>\<or>' \<^bold>n)" unfolding conn2 conn by blast

(**In fact, function composition can be seen as an additional binary connective for operators.
  We show below some interesting relationships that hold: *)
lemma op_prop10: "\<phi> = (\<^bold>e \<circ> \<phi>)" unfolding conn2 fun_comp_def by simp
lemma op_prop11: "\<phi> = (\<phi> \<circ> \<^bold>e)" unfolding conn2 fun_comp_def by simp
lemma op_prop12: "\<^bold>e = (\<^bold>n \<circ> \<^bold>n)" unfolding conn2 conn fun_comp_def by simp
lemma op_prop13: "\<phi>\<^sup>c = (\<^bold>n \<circ> \<phi>)" unfolding conn2 fun_comp_def by simp
lemma op_prop14: "\<phi>\<^sup>- = (\<phi> \<circ> \<^bold>n)" unfolding conn2 fun_comp_def by simp
lemma op_prop15: "\<phi>\<^sup>d = (\<^bold>n \<circ> \<phi> \<circ> \<^bold>n)" unfolding conn2 fun_comp_def by simp

(**There are also some useful properties regarding the images of operators*)
lemma im_prop1: "\<lbrakk>\<phi> D\<rbrakk>\<^sup>-  = \<lbrakk>\<phi>\<^sup>d D\<^sup>-\<rbrakk>" unfolding image_def op_dual_def sdfun_dcompl_def by (metis BA_dn setequ_ext)
lemma im_prop2: "\<lbrakk>\<phi>\<^sup>c D\<rbrakk>\<^sup>- = \<lbrakk>\<phi> D\<rbrakk>" unfolding image_def svfun_compl_def sdfun_dcompl_def by (metis BA_dn setequ_ext)
lemma im_prop3: "\<lbrakk>\<phi>\<^sup>d D\<rbrakk>\<^sup>- = \<lbrakk>\<phi> D\<^sup>-\<rbrakk>" unfolding image_def op_dual_def sdfun_dcompl_def by (metis BA_dn setequ_ext)
lemma im_prop4: "\<lbrakk>\<phi>\<^sup>- D\<rbrakk>\<^sup>- = \<lbrakk>\<phi>\<^sup>d D\<rbrakk>" unfolding image_def op_dual_def sdfun_dcompl_def by (metis BA_dn setequ_ext)
lemma im_prop5: "\<lbrakk>\<phi>\<^sup>c D\<^sup>-\<rbrakk>  = \<lbrakk>\<phi>\<^sup>- D\<rbrakk>\<^sup>-" unfolding image_def svfun_compl_def sdfun_dcompl_def by (metis (no_types, opaque_lifting) BA_dn setequ_ext)
lemma im_prop6: "\<lbrakk>\<phi>\<^sup>- D\<^sup>-\<rbrakk>  = \<lbrakk>\<phi> D\<rbrakk>" unfolding image_def sdfun_dcompl_def by (metis BA_dn setequ_ext)


(**Observe that all results obtained by assuming fixed-point predicates extend to their associated operators.*)
lemma "\<phi>\<^sup>f\<^sup>p(A) \<^bold>\<and> \<Gamma>(A) \<^bold>\<le> \<Delta>(A) \<longrightarrow> (fp \<phi>)(A) \<longrightarrow> \<Gamma>(A) \<^bold>\<le> \<Delta>(A)"
  by (simp add: fp_rel meet_def setequ_ext subset_def top_def)
lemma "\<phi>\<^sup>f\<^sup>p(A) \<^bold>\<and> \<phi>\<^sup>f\<^sup>p(B) \<^bold>\<and> (\<Gamma> A B) \<^bold>\<le> (\<Delta> A B) \<longrightarrow> (fp \<phi>)(A) \<and> (fp \<phi>)(B) \<longrightarrow> (\<Gamma> A B) \<^bold>\<le> (\<Delta> A B)"
  by (simp add: fp_rel meet_def setequ_ext subset_def top_def)

end