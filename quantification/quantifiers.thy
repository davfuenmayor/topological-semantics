theory quantifiers
  imports "../boolean_algebra/boolean_algebra_infinitary"
begin

subsection \<open>Encoding quantifiers (restricted and unrestricted)\<close>

(*Introduce pedagogically convenient notation*)
notation HOL.All ("\<Pi>_") notation HOL.Ex ("\<Sigma>_")

(**Let us recall that in HOL we have: *)
lemma "(\<forall>x. \<phi>) = \<Pi>(\<lambda>x. \<phi>)" by simp
lemma "(\<exists>x. \<phi>) = \<Sigma>(\<lambda>x. \<phi>)" by simp

(**We can introduce their respective 'w-type-lifted variants as follows: *)
definition mforall::"('i\<Rightarrow>'w \<sigma>)\<Rightarrow>'w \<sigma>" ("\<^bold>\<Pi>_")
  where "\<^bold>\<Pi>\<phi> \<equiv> \<lambda>w. \<forall>X. \<phi> X w"
definition mexists::"('i\<Rightarrow>'w \<sigma>)\<Rightarrow>'w \<sigma>" ("\<^bold>\<Sigma>_") 
  where "\<^bold>\<Sigma>\<phi> \<equiv> \<lambda>w. \<exists>X. \<phi> X w"

(**To improve readability, we introduce for them standard binder notation.*)
notation mforall (binder "\<^bold>\<forall>" [48]49)  notation mexists (binder "\<^bold>\<exists>" [48]49) 

(**And thus we obtain the 'w-type-lifted variant of the standard (variable-binding) quantifiers*)
lemma "(\<^bold>\<forall>X. \<phi>) = \<^bold>\<Pi>(\<lambda>X. \<phi>)" by (simp add: mforall_def)
lemma "(\<^bold>\<exists>X. \<phi>) = \<^bold>\<Sigma>(\<lambda>X. \<phi>)" by (simp add: mexists_def)

(**Quantifiers are dual to each other in the expected way*)
lemma "\<^bold>\<Pi>\<phi> = \<^bold>\<midarrow>(\<^bold>\<Sigma>\<phi>\<^sup>c)" by (simp add: compl_def mexists_def mforall_def svfun_compl_def)
lemma "(\<^bold>\<forall>X. \<phi> X) = \<^bold>\<midarrow>(\<^bold>\<exists>X. \<^bold>\<midarrow>(\<phi> X))" by (simp add: compl_def mexists_def mforall_def)

(**Relationship between quantifiers and the infinitary supremum and infimum operations*)
lemma mforall_char: "\<^bold>\<Pi>\<phi> = \<^bold>\<And>\<lbrakk>\<phi> _\<rbrakk>" unfolding infimum_def mforall_def range_def by metis
lemma mexists_char:  "\<^bold>\<Sigma>\<phi> = \<^bold>\<Or>\<lbrakk>\<phi> _\<rbrakk>" unfolding supremum_def mexists_def range_def by metis

(*or, in other words*)
lemma mforallb_char: "(\<^bold>\<forall>X. \<phi>) = \<^bold>\<And>\<lbrakk>(\<lambda>X. \<phi>) _\<rbrakk>" unfolding infimum_def mforall_def range_def by simp
lemma mexistsb_char: "(\<^bold>\<exists>X. \<phi>) = \<^bold>\<Or>\<lbrakk>(\<lambda>X. \<phi>) _\<rbrakk>" unfolding supremum_def mexists_def range_def by simp


(**Restricted quantification*)

(**Constant domains: first generalization of quantifiers above (e.g. free logic)*)
definition mforall_const::"'i \<sigma> \<Rightarrow> ('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> 'w \<sigma>" ("\<^bold>\<Pi>[_]_") 
  where "\<^bold>\<Pi>[D]\<phi> \<equiv> \<lambda>w. \<forall>X. (D X) \<longrightarrow> (\<phi> X) w" 
definition mexists_const::"'i \<sigma> \<Rightarrow> ('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> 'w \<sigma>" ("\<^bold>\<Sigma>[_]_") 
  where "\<^bold>\<Sigma>[D]\<phi> \<equiv> \<lambda>w. \<exists>X. (D X)  \<and>  (\<phi> X) w"

(**Alas! the convenient binder notation cannot be easily introduced for restricted quantifiers*)

(**Constant-domain quantification generalises its unrestricted counterpart*)
lemma "\<^bold>\<Pi>\<phi> = \<^bold>\<Pi>[\<^bold>\<top>]\<phi>" by (simp add: mforall_const_def mforall_def top_def)
lemma "\<^bold>\<Sigma>\<phi> = \<^bold>\<Sigma>[\<^bold>\<top>]\<phi>" by (simp add: mexists_const_def mexists_def top_def)

(**Constant-domain quantification can also be characterised using infimum and supremum*)
lemma mforall_const_char: "\<^bold>\<Pi>[D]\<phi> = \<^bold>\<And>\<lbrakk>\<phi> D\<rbrakk>" unfolding image_def infimum_def mforall_const_def by metis
lemma mexists_const_char: "\<^bold>\<Sigma>[D]\<phi> = \<^bold>\<Or>\<lbrakk>\<phi> D\<rbrakk>" unfolding image_def supremum_def mexists_const_def by metis

(**Constant-domain quantifiers also  allow us to nicely characterize the interaction between
 function composition and (restricted) quantification:*)
lemma mforall_comp: "\<^bold>\<Pi>(\<phi>\<circ>\<psi>) = \<^bold>\<Pi>[\<lbrakk>\<psi> _\<rbrakk>] \<phi>" unfolding fun_comp_def mforall_const_def mforall_def range_def by metis
lemma mexists_comp: "\<^bold>\<Sigma>(\<phi>\<circ>\<psi>) = \<^bold>\<Sigma>[\<lbrakk>\<psi> _\<rbrakk>] \<phi>" unfolding fun_comp_def mexists_const_def mexists_def range_def by metis


(**Varying domains: we can also restrict quantifiers by taking a 'functional domain' as additional parameter.
The latter is a set-valued mapping each element 'i to a set of points (e.g. where it 'exists').*)
definition mforall_var::"('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> 'w \<sigma>" ("\<^bold>\<Pi>{_}_") 
  where "\<^bold>\<Pi>{\<psi>}\<phi> \<equiv> \<lambda>w. \<forall>X. (\<psi> X) w \<longrightarrow> (\<phi> X) w" 
definition mexists_var::"('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'w \<sigma>) \<Rightarrow> 'w \<sigma>" ("\<^bold>\<Sigma>{_}_") 
  where "\<^bold>\<Sigma>{\<psi>}\<phi> \<equiv> \<lambda>w. \<exists>X. (\<psi> X) w  \<and>  (\<phi> X) w"

(**Varying-domain quantification generalises its constant-domain counterpart*)

lemma "\<^bold>\<Pi>[D]\<phi> = \<^bold>\<Pi>{D\<up>}\<phi>" by (simp add: mforall_const_def mforall_var_def)
lemma "\<^bold>\<Sigma>[D]\<phi> = \<^bold>\<Sigma>{D\<up>}\<phi>" by (simp add: mexists_const_def mexists_var_def)

(**Restricted quantifiers are dual to each other in the expected way*)
lemma "\<^bold>\<Pi>[D]\<phi> = \<^bold>\<midarrow>(\<^bold>\<Sigma>[D]\<phi>\<^sup>c)" by (metis iDM_b im_prop2 mexists_const_char mforall_const_char setequ_ext)
lemma "\<^bold>\<Pi>{\<psi>}\<phi> = \<^bold>\<midarrow>(\<^bold>\<Sigma>{\<psi>}\<phi>\<^sup>c)" by (simp add: compl_def mexists_var_def mforall_var_def svfun_compl_def)


(**We can use 2nd-order connectives on set-valued functions to encode restricted quantifiers as unrestricted*)
lemma "\<^bold>\<Pi>{\<psi>}\<phi> = \<^bold>\<Pi>(\<psi> \<^bold>\<sqsupset> \<phi>)" by (simp add: impl_def mforall_def mforall_var_def svfun_impl_def)
lemma "\<^bold>\<Sigma>{\<psi>}\<phi> = \<^bold>\<Sigma>(\<psi> \<^bold>\<sqinter> \<phi>)" by (simp add: meet_def mexists_def mexists_var_def svfun_meet_def)

(**Observe that using these operators has the advantage of allowing for binder notation,*)
lemma "\<^bold>\<Pi>{\<psi>}\<phi> = (\<^bold>\<forall>X. (\<psi> \<^bold>\<sqsupset> \<phi>) X)" by (simp add: impl_def mforall_def mforall_var_def svfun_impl_def)
lemma "\<^bold>\<Sigma>{\<psi>}\<phi> = (\<^bold>\<exists>X. (\<psi> \<^bold>\<sqinter> \<phi>) X)" by (simp add: meet_def mexists_def mexists_var_def svfun_meet_def)

(**So to sumarize: different sorts of restricted quantification can be emulated 
  by employing 2nd-order operations to adequately relativise predicates: *)

lemma "\<^bold>\<Pi>[D]\<phi> = (\<^bold>\<forall>X. (D\<up> \<^bold>\<sqsupset> \<phi>) X)" by (simp add: impl_def mforall_const_def mforall_def svfun_impl_def)
lemma "\<^bold>\<Pi>{\<^bold>\<top>'}\<phi> = (\<^bold>\<forall>X. (\<^bold>\<top>' \<^bold>\<sqsupset> \<phi>) X)" by (simp add: impl_def mforall_def mforall_var_def svfun_impl_def)
lemma "\<^bold>\<Pi>\<phi> = \<^bold>\<Pi>{\<^bold>\<top>'}\<phi>" by (simp add: mforall_def mforall_var_def svfun_top_def top_def)
lemma "(\<^bold>\<forall>X. \<phi> X) = \<^bold>\<Pi>{\<^bold>\<top>'}\<phi>" by (simp add: mforall_def mforall_var_def svfun_top_def top_def)

named_theorems quant (*to group together definitions related to quantification*)
declare mforall_def[quant] mexists_def[quant]
        mforall_const_def[quant] mexists_const_def[quant]
        mforall_var_def[quant] mexists_var_def[quant]

end