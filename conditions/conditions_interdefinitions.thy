theory conditions_interdefinitions
  imports conditions_positive
begin

(**Interior operator as derived from border.*)
definition Int_br::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<I>\<^sub>B") 
  where "\<I>\<^sub>B \<B> \<equiv> \<lambda>A. A \<^bold>\<leftharpoonup> (\<B> A)"
(**Interior operator as derived from frontier.*)
definition Int_fr::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<I>\<^sub>F") 
  where "\<I>\<^sub>F \<F> \<equiv> \<lambda>A. A \<^bold>\<leftharpoonup> (\<F> A)"
(**Closure operator as derived from border.*)
definition Cl_br::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<C>\<^sub>B") 
  where "\<C>\<^sub>B \<B> \<equiv> \<lambda>A. A \<^bold>\<or> \<B>(\<^bold>\<midarrow>A)"
(**Closure operator as derived from frontier.*)
definition Cl_fr::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<C>\<^sub>F") 
  where "\<C>\<^sub>F \<F> \<equiv> \<lambda>A. A \<^bold>\<or> (\<F> A)"
(**Frontier operator as derived from interior.*)
definition Fr_int::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<F>\<^sub>I") 
  where "\<F>\<^sub>I \<I> \<equiv> \<lambda>A. \<^bold>\<midarrow>(\<I> A \<^bold>\<or> \<I>(\<^bold>\<midarrow>A))"
(**Frontier operator as derived from closure.*)
definition Fr_cl::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<F>\<^sub>C") 
  where "\<F>\<^sub>C \<C> \<equiv> \<lambda>A. (\<C> A) \<^bold>\<and> \<C>(\<^bold>\<midarrow>A)"
(**Frontier operator as derived from border.*)
definition Fr_br::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<F>\<^sub>B") 
  where "\<F>\<^sub>B \<B> \<equiv> \<lambda>A. \<B> A \<^bold>\<or> \<B>(\<^bold>\<midarrow>A)"
(**Border operator as derived from interior.*)
definition Br_int::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<B>\<^sub>I") 
  where "\<B>\<^sub>I \<I> \<equiv> \<lambda>A. A \<^bold>\<leftharpoonup> (\<I> A)"
(**Border operator as derived from closure.*)
definition Br_cl::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<B>\<^sub>C")  
  where "\<B>\<^sub>C \<C> \<equiv> \<lambda>A. A \<^bold>\<and> \<C>(\<^bold>\<midarrow>A)"
(**Border operator as derived from frontier.*)
definition Br_fr::"('w \<sigma>\<Rightarrow>'w \<sigma>)\<Rightarrow>('w \<sigma>\<Rightarrow>'w \<sigma>)" ("\<B>\<^sub>F") 
  where "\<B>\<^sub>F \<F> \<equiv> \<lambda>A. A \<^bold>\<and> (\<F> A)"

lemma "\<B> = \<B>\<^sub>C (\<C>\<^sub>B \<B>)" nitpick oops
lemma "\<B> = \<B>\<^sub>I (\<I>\<^sub>B \<B>)" nitpick oops
lemma "\<B> = \<B>\<^sub>F (\<F>\<^sub>B \<B>)" nitpick oops
lemma "\<F> = \<F>\<^sub>C (\<C>\<^sub>F \<F>)" nitpick oops
lemma "\<F> = \<F>\<^sub>I (\<I>\<^sub>F \<F>)" nitpick oops
lemma "\<F> = \<F>\<^sub>B (\<B>\<^sub>F \<F>)" nitpick oops

abbreviation "SYMM \<phi> \<equiv> \<forall>A. \<phi>(\<^bold>\<midarrow>A) \<approx> \<phi> A"

lemma "CNTR \<B> \<Longrightarrow> \<B> = \<B>\<^sub>C (\<C>\<^sub>B \<B>)" unfolding CNTR_def Br_cl_def Cl_br_def compl_def join_def meet_def subset_def by metis
lemma "CNTR \<B> \<Longrightarrow> \<B> = \<B>\<^sub>I (\<I>\<^sub>B \<B>)" unfolding CNTR_def Br_int_def Int_br_def diff_def subset_def by metis
lemma "CNTR \<B> \<Longrightarrow> \<B> = \<B>\<^sub>F (\<F>\<^sub>B \<B>)" unfolding CNTR_def Br_fr_def Fr_br_def subset_def compl_def join_def meet_def by metis
lemma "SYMM \<F> \<Longrightarrow> \<F> = \<F>\<^sub>C (\<C>\<^sub>F \<F>)" unfolding Cl_fr_def Fr_cl_def compl_def join_def meet_def setequ_ext by metis
lemma "SYMM \<F> \<Longrightarrow> \<F> = \<F>\<^sub>I (\<I>\<^sub>F \<F>)" unfolding Int_fr_def Fr_int_def compl_def diff_def join_def setequ_ext by metis
lemma "SYMM \<F> \<Longrightarrow> \<F> = \<F>\<^sub>B (\<B>\<^sub>F \<F>)" unfolding Br_fr_def Fr_br_def compl_def join_def meet_def setequ_ext by metis

lemma "EXPN \<C> \<Longrightarrow> \<C> = \<C>\<^sub>B (\<B>\<^sub>C \<C>)" oops
  (* unfolding CNTR_def Br_cl_def Cl_br_def compl_def join_def meet_def subset_def by metis *)

lemma "\<C> = (\<C>\<^sup>d)\<^sup>d" sledgehammer

end
