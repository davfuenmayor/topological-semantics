theory misc
  imports Main
begin
(*----------- Technicalities--------*)
declare[[smt_timeout=30]]
declare[[show_types]]
(* declare[[syntax_ambiguity_warning=false]] *)
sledgehammer_params[isar_proof=false]
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3, atoms=a b c d] (*default Nitpick settings*)
(*we hide some Isabelle/HOL notation from the libraries (which we don't use) to avoid overloading*)
hide_const(open) List.list.Nil no_notation List.list.Nil ("[]")  (*We have no use for lists... *)
hide_const(open) Relation.converse no_notation Relation.converse ("(_\<inverse>)" [1000] 999) (*..nor for relations in this work*)
hide_const(open) Fun.comp no_notation Fun.comp (infixl "\<circ>" 55) (*we redefine function composition below*)
hide_const(open) Groups.plus_class.plus no_notation Groups.plus_class.plus (infixl "+" 65) (*we don't use this*)
hide_const(open) Groups.times_class.times no_notation Groups.times_class.times (infixl "*" 70) (*we don't use this*)
hide_const(open) Groups.minus_class.minus no_notation Groups.minus_class.minus (infixl "-" 65) (*we don't use this*)
hide_const(open) Groups.uminus_class.uminus no_notation Groups.uminus_class.uminus ("- _" [81] 80) (*we don't use this*)
(*---------------------------------*)

abbreviation "isEmpty S \<equiv> \<forall>x. \<not>S x"
abbreviation "nonEmpty S \<equiv> \<exists>x. S x"

(**Function composition.*)
definition fun_comp :: "('b \<Rightarrow> 'c) \<Rightarrow> ( 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" (infixl "\<circ>" 75) 
  where "\<phi> \<circ> \<psi> \<equiv> \<lambda>x. \<phi> (\<psi> x)"

(**Inverse projection maps a unary function to a 'projected' binary function wrt. its 1st argument.*)
abbreviation inv_proj::\<open>('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c)\<close> ("(_)\<up>")
  where "D\<up> \<equiv> \<lambda>A B. D A"

(**Image of a mapping  @{text "\<phi>"}, with range as an special case.*)
definition image::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)" ("\<lbrakk>_ _\<rbrakk>") 
  where "\<lbrakk>\<phi> S\<rbrakk> \<equiv> \<lambda>y. \<exists>x. (S x) \<and> (\<phi> x) = y"
definition range::"('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool)" ("\<lbrakk>_'_\<rbrakk>") 
  where "\<lbrakk>\<phi> _\<rbrakk> \<equiv> \<lambda>Y. \<exists>x. (\<phi> x) = Y"
lemma range_char1: "\<lbrakk>\<phi> _\<rbrakk> = \<lbrakk>\<phi> (\<lambda>x. True)\<rbrakk>" by (simp add: image_def range_def)
lemma range_char2: "\<lbrakk>\<phi> _\<rbrakk> = (\<lambda>X. \<exists>S. \<lbrakk>\<phi> S\<rbrakk> X)" unfolding range_def image_def by blast

end