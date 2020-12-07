theory border_algebra
  imports operators_basic
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3] (*default settings*)

section \<open>Border algebra\<close>
(**We define a border algebra in an analogous fashion as the well-known closure/interior algebras.
We also verify a few interesting properties.*)

(**Declares a primitive (unconstrained) border operation and defines others from it.*)
consts \<B>::"\<sigma>\<Rightarrow>\<sigma>"
abbreviation "\<I> \<equiv> \<I>\<^sub>B \<B>" (**interior*)
abbreviation "\<C> \<equiv> \<C>\<^sub>B \<B>" (**closure*)
abbreviation "\<F> \<equiv> \<F>\<^sub>B \<B>" (**frontier*)

(**Verifies minimal conditions under which operators resulting from conversion functions coincide.*)
lemma ICdual:  "\<I> \<^bold>\<equiv> \<C>\<^sup>d" by (simp add: Cl_br_def Int_br_def dual_def equal_op_def conn)
lemma ICdual': "\<C> \<^bold>\<equiv> \<I>\<^sup>d"  by (simp add: Cl_br_def Int_br_def dual_def equal_op_def conn)
lemma FI_rel: "Br_1 \<B> \<Longrightarrow> \<F> \<^bold>\<equiv> \<F>\<^sub>I \<I>" using Fr_br_def Fr_int_def Int_br_def equal_op_def by (smt Br_5b_def PB5b dual_def conn)
lemma IF_rel: "Br_1 \<B> \<Longrightarrow> \<I> \<^bold>\<equiv> \<I>\<^sub>F \<F>" using Br_5b_def Fr_br_def Int_br_def Int_fr_def PB5b unfolding equal_op_def conn by fastforce
lemma FC_rel: "Br_1 \<B> \<Longrightarrow> \<F> \<^bold>\<equiv> \<F>\<^sub>C \<C>" using Br_5b_def Cl_br_def Fr_br_def Fr_cl_def PB5b unfolding equal_op_def conn by fastforce
lemma CF_rel: "Br_1 \<B> \<Longrightarrow> \<C> \<^bold>\<equiv> \<C>\<^sub>F \<F>" using Br_5b_def Cl_br_def Cl_fr_def Fr_br_def PB5b unfolding equal_op_def conn by fastforce
lemma BI_rel: "Br_1 \<B> \<Longrightarrow> \<B> \<^bold>\<equiv> \<B>\<^sub>I \<I>" using Br_5b_def Br_int_def Int_br_def PB5b diff_def equal_op_def by fastforce
lemma BC_rel: "Br_1 \<B> \<Longrightarrow> \<B> \<^bold>\<equiv> \<B>\<^sub>C \<C>" using BI_BC_rel BI_rel ICdual' eq_ext' by fastforce
lemma BF_rel: "Br_1 \<B> \<Longrightarrow> \<B> \<^bold>\<equiv> \<B>\<^sub>F \<F>" by (smt BI_rel Br_fr_def Br_int_def IF_rel Int_fr_def diff_def equal_op_def meet_def) 

(**Fixed-point and other operators are interestingly related.*)
lemma fp1: "Br_1 \<B> \<Longrightarrow> \<I>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B>\<^sup>c" using Br_5b_def Int_br_def PB5b unfolding equal_op_def conn by fastforce
lemma fp2: "Br_1 \<B> \<Longrightarrow> \<B>\<^sup>f\<^sup>p \<^bold>\<equiv> \<I>\<^sup>c" using Br_5b_def Int_br_def PB5b conn equal_op_def by fastforce 
lemma fp3: "Br_1 \<B> \<Longrightarrow> \<C>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B>\<^sup>d" using Br_5c_def Cl_br_def PB5c dual_def unfolding equal_op_def conn by fastforce
lemma fp4: "Br_1 \<B> \<Longrightarrow> (\<B>\<^sup>d)\<^sup>f\<^sup>p \<^bold>\<equiv> \<C>" by (smt dimp_def equal_op_def fp3)
lemma fp5: "Br_1 \<B> \<Longrightarrow> \<F>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B> \<^bold>\<squnion> (\<C>\<^sup>c)" by (smt Br_5b_def Cl_br_def Fr_br_def PB5b equal_op_def conn)

(*
(**Different inter-relations (some redundant ones are kept to help the provers).*)
lemma monI: "Br_1(\<B>) \<Longrightarrow> MONO(\<I>)" using IB1 PI1 MONO_MULTa by auto
lemma monC: "Br_1(\<B>) \<Longrightarrow> MONO(\<C>)" using CB1 PC1 MONO_ADDIb by auto
lemma pB1: "Br_1(\<B>) \<Longrightarrow> \<forall>A. \<B> A \<^bold>\<approx> A \<^bold>\<leftharpoonup> \<I> A" using Br_5b_def Int_br_def PB5b conn by fastforce
lemma pB2: "Br_1(\<B>) \<Longrightarrow> \<forall>A. \<B> A \<^bold>\<approx> A \<^bold>\<and> \<F> A" using Br_5b_def Fr_br_def PB5b conn by fastforce
lemma pB3: "Br_1(\<B>) \<Longrightarrow> \<forall>A. \<B>(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<midarrow>A \<^bold>\<and> \<F> A" using FB2 Fr_2_def pB2 unfolding conn by metis
lemma pB4: "Br_1(\<B>) \<Longrightarrow> \<forall>A. \<B>(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<midarrow>A \<^bold>\<and> \<C> A" using Cl_br_def pB3 conn by auto
lemma pB5: "Br_1(\<B>) \<Longrightarrow> \<forall>A. \<B>(\<C> A) \<^bold>\<preceq> (\<B> A) \<^bold>\<or> \<B>(\<^bold>\<midarrow>A)" by (smt ADDI_a_def Br_5b_def Cl_br_def PB5b PB7 conn)
lemma pF1: "Br_1(\<B>) \<Longrightarrow> \<forall>A. \<F> A \<^bold>\<approx> \<C> A \<^bold>\<leftharpoonup> \<I> A" using CF_rel Cl_fr_def IF_rel Int_fr_def unfolding equal_op_def conn by auto
lemma pF2: "Br_1(\<B>) \<Longrightarrow> \<forall>A. \<F> A \<^bold>\<approx> \<C> A \<^bold>\<and> \<C>(\<^bold>\<midarrow>A)" using FC_rel Fr_cl_def eq_ext' by fastforce
lemma pF3: "\<forall>A. \<F> A \<^bold>\<approx> \<B> A \<^bold>\<or> \<B>(\<^bold>\<midarrow>A)" by (simp add: Fr_br_def)
lemma pF4: "Br_1 \<B> \<Longrightarrow> Br_3 \<B> \<Longrightarrow> \<forall>A. \<F>(\<I> A) \<^bold>\<preceq> \<F> A" by (smt IB4 IDEM_def IF_rel Int_fr_def MONO_def diff_def eq_ext' monC pF1)
lemma pF5: "Br_1 \<B> \<Longrightarrow> Br_3 \<B> \<Longrightarrow> \<forall>A. \<F>(\<C> A) \<^bold>\<preceq> \<F> A" by (metis FB2 Fr_2_def ICdual' dual_def eq_ext' pF4)
lemma pA1: "Br_1(\<B>) \<Longrightarrow> \<forall>A. A \<^bold>\<approx> \<I> A \<^bold>\<or> \<B> A" using Int_br_def pB2 conn by auto
lemma pA2: "Br_1(\<B>) \<Longrightarrow> \<forall>A. A \<^bold>\<approx> \<C> A \<^bold>\<leftharpoonup> \<B>(\<^bold>\<midarrow>A)" using Cl_br_def pA1 unfolding conn by metis
lemma pC1: "\<forall>A. \<C> A \<^bold>\<approx> A \<^bold>\<or> \<B>(\<^bold>\<midarrow>A)" by (simp add: Cl_br_def)
lemma pC2: "Br_1(\<B>) \<Longrightarrow> \<forall>A. \<C> A \<^bold>\<approx> A \<^bold>\<or> \<F> A" using CF_rel Cl_fr_def eq_ext' by fastforce
lemma pI1: "\<forall>A. \<I> A \<^bold>\<approx> A \<^bold>\<leftharpoonup> \<B> A" by (simp add: Int_br_def)
lemma pI2: "Br_1(\<B>) \<Longrightarrow> \<forall>A. \<I> A \<^bold>\<approx> A \<^bold>\<leftharpoonup> \<F> A" using IF_rel Int_fr_def eq_ext' by fastforce

lemma IC_imp: "Br_1 \<B> \<Longrightarrow> Br_2 \<B> \<Longrightarrow> \<forall>A B. \<I>(A \<^bold>\<rightarrow> B) \<^bold>\<preceq> \<C> A \<^bold>\<rightarrow> \<C> B" proof -
  assume br1: "Br_1 \<B>" and br2: "Br_2 \<B>"
  { fix a b
    have "(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b \<^bold>\<rightarrow> \<^bold>\<midarrow>a = \<^bold>\<top>" unfolding conn by auto
    hence "\<I>((a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b \<^bold>\<rightarrow> \<^bold>\<midarrow>a) \<^bold>\<approx> \<I>(\<^bold>\<top>)" by simp
    hence "\<I>((a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b \<^bold>\<rightarrow> \<^bold>\<midarrow>a) \<^bold>\<approx> \<^bold>\<top>" using br1 IB3 br2 dNOR_def by auto
    moreover have "let A=(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b; B=\<^bold>\<midarrow>a in \<I>(A \<^bold>\<rightarrow> B) \<^bold>\<preceq> \<I>(A) \<^bold>\<rightarrow> \<I>(B)" using IB1 Int_7_def PI7 br1 by auto 
    ultimately have "\<I>((a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b) \<^bold>\<rightarrow> \<I>(\<^bold>\<midarrow>a) \<^bold>\<approx> \<^bold>\<top>" unfolding conn by simp
    moreover have "let A=a \<^bold>\<rightarrow> b; B=\<^bold>\<midarrow>b in \<I>(A \<^bold>\<and> B) \<^bold>\<approx> \<I>(A) \<^bold>\<and> \<I>(B)" using IB1 MULT_def br1 by auto
    ultimately have "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<I>(\<^bold>\<midarrow>b) \<^bold>\<rightarrow> \<I>(\<^bold>\<midarrow>a) \<^bold>\<approx> \<^bold>\<top>" unfolding conn by simp
    moreover have "\<forall>A. \<I>(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<midarrow>\<C>(A)" using ICdual' compl_def dual_def eq_ext' by fastforce
    ultimately have "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>\<C>(b) \<^bold>\<rightarrow> \<^bold>\<midarrow>\<C>(a) \<^bold>\<approx> \<^bold>\<top>" unfolding conn by simp
    hence "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>\<C>(b) \<^bold>\<preceq> \<^bold>\<midarrow>\<C>(a)" unfolding conn by simp
    hence "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<C> a \<^bold>\<preceq> \<C> b" unfolding conn by metis
  } thus ?thesis unfolding conn by simp
qed*)

(**Define some fixed-point predicates and prove some properties.*)
abbreviation openset ("Op") where "Op A \<equiv> fp \<I> A"
abbreviation closedset ("Cl") where "Cl A \<equiv> fp \<C> A"
abbreviation borderset ("Br") where "Br A \<equiv> fp \<B> A"
abbreviation frontierset ("Fr") where "Fr A \<equiv> fp \<F> A"

lemma Int_Open: "Br_1 \<B> \<Longrightarrow> Br_3 \<B> \<Longrightarrow> \<forall>A. Op(\<I> A)" using IB4 IDEM_def by blast
lemma Cl_Closed: "Br_1 \<B> \<Longrightarrow> Br_3 \<B> \<Longrightarrow> \<forall>A. Cl(\<C> A)" using CB4 IDEM_def by blast
lemma Br_Border: "Br_1 \<B> \<Longrightarrow> \<forall>A. Br(\<B> A)" using IDEM_def PB6 by blast
(**In contrast, there is no analogous fixed-point result for frontier:*)
lemma "\<BB> \<B> \<Longrightarrow> \<forall>A. Fr(\<F> A)" nitpick oops (*counterexample even if assuming all border conditions*)

lemma OpCldual: "\<forall>A. Cl A \<longleftrightarrow> Op(\<^bold>\<midarrow>A)" using Cl_br_def Int_br_def conn by auto 
lemma ClOpdual: "\<forall>A. Op A \<longleftrightarrow> Cl(\<^bold>\<midarrow>A)" using Cl_br_def Int_br_def conn by auto
lemma Fr_ClBr: "Br_1 \<B> \<Longrightarrow> \<forall>A. Fr(A) = (Cl(A) \<and> Br(A))" by (metis BF_rel Br_fr_def CF_rel Cl_fr_def eq_ext' join_def meet_def)
lemma Cl_F: "Br_1 \<B> \<Longrightarrow> Br_3 \<B> \<Longrightarrow> \<forall>A. Cl(\<F> A)" by (metis CF_rel Cl_fr_def FB4 Fr_4_def eq_ext' join_def)

end