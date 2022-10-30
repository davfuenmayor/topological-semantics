theory boolean_algebra
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

lemma image_comp: "\<lbrakk>(f \<circ> g) S\<rbrakk> = \<lbrakk>f \<lbrakk>g S\<rbrakk>\<rbrakk>" unfolding fun_comp_def image_def by metis


section \<open>Shallow semantical embedding of (a logic of) Boolean algebras\<close>

(**We encode Boolean algebras via their (Stone) representation as algebras of sets ('fields of sets').
This means that each element of (the carrier of) the algebra will be a set of `points'.
Inspired by the 'propositions as sets of worlds' paradigm from modal logic, we can sometimes refer
to points as 'worlds', and thus to the elements of our Boolean algebras as 'propositions'.
However, this is only one possibility, since points can themselves be taken as sets (e.g. of `worlds')
and thus as 'propositions'. In such a case the elements of our Boolean algebras might correspond
to 'theories' (i.e. sets of 'propositions').*)

(**We utilize a particular naming convention: The type parameter @{type "'w"} is employed for the
domain/universe of `points'. We conveniently introduce the (parametric) type-alias @{type "'w \<sigma>"} 
as shorthand for @{type "'w\<Rightarrow>bool"}. Hence, the elements of our algebra are objects of type @{type "'w \<sigma>"},
and thus correspond to (characteristic functions of) sets of `points'. Observe that the type parameter
'w can itself correspond to a 'set type', and so elements of our algebras can have type @{type "('w \<sigma>)\<sigma>"}.
Set-valued (set-domain) functions are thus functions that have sets (of points) as their codomain (domain),
they are basically anything with a (parametric) type @{type "'i\<Rightarrow>'w \<sigma>"} (@{type "'w \<sigma>\<Rightarrow>'i"}).*)

type_synonym 'w \<sigma> = \<open>'w \<Rightarrow> bool\<close> (*type for (characteristic functions of) sets (of points)*)

(**In the sequel, we will (try to) enforce the following naming convention:

(i) Upper-case latin letters (A, B, D, M, P, S, X, etc.) denote arbitrary sets (type @{type "'w \<sigma>"}).
We will employ lower-case letters (p, q, x, w, etc.) to denote variables playing the role of 'points'.
In some contexts, the letters S and D will be employed to denote sets/domains of sets (of 'points').

(ii) Greek letters denote arbitrary set-valued functions (type @{type "'i\<Rightarrow>'w \<sigma>"} aliased @{type "('i \<Rightarrow> 'w \<sigma>)"}).
We employ the letters @{text "\<phi>"}, @{text "\<psi>"} and @{text "\<eta>"} to denote arbitrary unary operations
(with type @{type "'w \<sigma> \<Rightarrow> 'w \<sigma>"}); and the letters @{text "\<xi>"} and @{text "\<delta>"} to denote 
arbitrary binary operations (with type @{type "'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>"}).

(iii) Upper-case calligraphic letters (\<B>, \<I>, \<C>, \<P>, etc.) are reserved for unary operations that are
intended to act as so-called 'topological operators' in the given context.
*)

subsection \<open>Encoding Boolean operations\<close>

(**Standard inclusion-based order structure on sets.*)
definition subset::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" (infixr "\<preceq>" 45) 
  where "A \<preceq> B \<equiv> \<forall>p. A p \<longrightarrow> B p"
definition setequ::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" (infixr "\<approx>" 45) 
  where "A \<approx> B \<equiv> \<forall>p. A p \<longleftrightarrow> B p"

named_theorems order (*to group together order-related definitions*)
declare setequ_def[order] subset_def[order]

(**These (trivial) lemmas are intended to help automated tools with equational reasoning.*)
lemma setequ_char: "(A \<approx> B) = (A \<preceq> B \<and> B \<preceq> A)" unfolding order by blast
lemma setequ_ext: "(A \<approx> B) = (A = B)" unfolding order by blast

(**We now encode connectives for (distributive and complemented) bounded lattices, mostly 
by reusing their counterpart meta-logical HOL connectives,*)
definition meet::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<and>" 54) 
  where "A \<^bold>\<and> B \<equiv> \<lambda>p. (A p) \<and> (B p)" (**intersection*)
definition join::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<or>" 53) 
  where "A \<^bold>\<or> B \<equiv> \<lambda>p. (A p) \<or> (B p)" (**union*)
definition top::"'w \<sigma>" ("\<^bold>\<top>")    
  where "\<^bold>\<top> \<equiv> \<lambda>w. True"   (**universe*)
definition bottom::"'w \<sigma>" ("\<^bold>\<bottom>") 
  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"  (**empty-set*)

(**and introduce further operations to obtain a Boolean algebra (of sets).*)
definition compl::"'w \<sigma> \<Rightarrow> 'w \<sigma>" ("\<^bold>\<midarrow>_"[57]58)
  where "\<^bold>\<midarrow>A  \<equiv> \<lambda>p. \<not>(A p)" (** (set-)complement*)
definition impl::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<rightarrow>" 51)
  where "A \<^bold>\<rightarrow> B \<equiv> \<lambda>p. (A p) \<longrightarrow> (B p)" (** (set-)implication*)
definition diff::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<leftharpoonup>" 51) 
  where "A \<^bold>\<leftharpoonup> B \<equiv> \<lambda>p. (A p) \<and> \<not>(B p)" (** (set-)difference*)
definition dimpl::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<leftrightarrow>" 51)
(* definition dimpl (infixr "\<^bold>\<leftrightarrow>" 51)  *)
  where "A \<^bold>\<leftrightarrow> B \<equiv> \<lambda>p. (A p) = (B p)" (** double implication*)
definition sdiff::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<triangle>" 51)
(* definition sdiff (infixr "\<^bold>\<triangle>" 51)  *)
  where "A \<^bold>\<triangle> B \<equiv> \<lambda>p. (A p) \<noteq> (B p)" (** symmetric difference (aka. xor) *)

named_theorems conn (*to group together definitions for algebraic connectives*)
declare meet_def[conn] join_def[conn] top_def[conn] bottom_def[conn]
        impl_def[conn] dimpl_def[conn] diff_def[conn] sdiff_def[conn] compl_def[conn]

(**Verify characterization for some connectives.*)
lemma compl_char: "\<^bold>\<midarrow>A = A \<^bold>\<rightarrow> \<^bold>\<bottom>" unfolding conn by simp
lemma impl_char: "A \<^bold>\<rightarrow> B = \<^bold>\<midarrow>A \<^bold>\<or> B" unfolding conn by simp
lemma dimpl_char: "A \<^bold>\<leftrightarrow> B = (A \<^bold>\<rightarrow> B) \<^bold>\<and> (B \<^bold>\<rightarrow> A)" unfolding conn by blast
lemma diff_char1: "A \<^bold>\<leftharpoonup> B = A \<^bold>\<and> \<^bold>\<midarrow>B" unfolding conn by simp
lemma diff_char2: "A \<^bold>\<leftharpoonup> B = \<^bold>\<midarrow>(A \<^bold>\<rightarrow> B)" unfolding conn by simp
lemma sdiff_char1: "A \<^bold>\<triangle> B = (A \<^bold>\<leftharpoonup> B) \<^bold>\<or> (B \<^bold>\<leftharpoonup> A)" unfolding conn by blast
lemma sdiff_char2: "A \<^bold>\<triangle> B = \<^bold>\<midarrow>(A \<^bold>\<leftrightarrow> B)" unfolding conn by simp

(**We can verify that (quite trivially) this algebra satisfies some properties of lattices.*)
lemma L1: "A \<approx> A \<^bold>\<or> A" unfolding conn order by simp
lemma L2: "A \<approx> A \<^bold>\<and> A" unfolding conn order by simp
lemma L3: "A \<preceq> A \<^bold>\<or> B" unfolding conn order by simp
lemma L4: "A \<^bold>\<and> B \<preceq> A" unfolding conn order by simp
lemma L5: "(A \<^bold>\<and> B) \<^bold>\<or> B \<approx> B" unfolding setequ_char conn order by simp 
lemma L6: "A \<^bold>\<and> (A \<^bold>\<or> B) \<approx> A" unfolding setequ_char conn order by simp
lemma L7: "A \<preceq> C \<and> B \<preceq> C \<longrightarrow> A \<^bold>\<or> B \<preceq> C" unfolding conn order by simp 
lemma L8: "C \<preceq> A \<and> C \<preceq> B \<longrightarrow> C \<preceq> A \<^bold>\<and> B" unfolding conn order by simp
lemma L9: "A \<preceq> B \<longleftrightarrow> (A \<^bold>\<or> B) \<approx> B" unfolding setequ_char conn order by simp
lemma L10: "B \<preceq> A \<longleftrightarrow> (A \<^bold>\<and> B) \<approx> B" unfolding setequ_char conn order by simp
lemma L11: "A \<preceq> B \<and> C \<preceq> D \<longrightarrow> A \<^bold>\<or> C \<preceq> B \<^bold>\<or> D" unfolding conn order by simp
lemma L12: "A \<preceq> B \<and> C \<preceq> D \<longrightarrow> A \<^bold>\<and> C \<preceq> B \<^bold>\<and> D" unfolding conn order by simp
lemma L13: "A \<^bold>\<and> \<^bold>\<top> \<approx> A" unfolding conn order by simp
lemma L14: "A \<^bold>\<or> \<^bold>\<bottom> \<approx> A" unfolding conn order by simp

(**These properties below hold in particular also for Boolean algebras.*)
lemma BA_impl: "A \<preceq> B \<longleftrightarrow> A \<^bold>\<rightarrow> B \<approx> \<^bold>\<top>" unfolding conn order by simp
lemma BA_distr1: "(A \<^bold>\<and> (B \<^bold>\<or> C)) \<approx> ((A \<^bold>\<and> B) \<^bold>\<or> (A \<^bold>\<and> C))" unfolding setequ_char conn order by simp
lemma BA_distr2: "(A \<^bold>\<or> (B \<^bold>\<and> C)) \<approx> ((A \<^bold>\<or> B) \<^bold>\<and> (A \<^bold>\<or> C))" unfolding conn order by blast
lemma BA_cp: "A \<preceq> B \<longleftrightarrow> \<^bold>\<midarrow>B \<preceq> \<^bold>\<midarrow>A" unfolding conn order by blast 
lemma BA_deMorgan1: "\<^bold>\<midarrow>(A \<^bold>\<or> B) \<approx> (\<^bold>\<midarrow>A \<^bold>\<and> \<^bold>\<midarrow>B)" unfolding conn order by simp
lemma BA_deMorgan2: "\<^bold>\<midarrow>(A \<^bold>\<and> B) \<approx> (\<^bold>\<midarrow>A \<^bold>\<or> \<^bold>\<midarrow>B)" unfolding conn order by simp
lemma BA_dn: "\<^bold>\<midarrow>\<^bold>\<midarrow>A \<approx> A" unfolding conn order by simp
lemma BA_cmpl_equ: "(\<^bold>\<midarrow>A \<approx> B) = (A \<approx> \<^bold>\<midarrow>B)" unfolding conn order by blast


(**We conveniently introduce these properties of sets of sets (of points).*)
definition meet_closed::"('w \<sigma>)\<sigma> \<Rightarrow> bool"
  where "meet_closed S \<equiv>  \<forall>X Y. (S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<and> Y)"
definition join_closed::"('w \<sigma>)\<sigma> \<Rightarrow> bool"
  where "join_closed S \<equiv>  \<forall>X Y. (S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<or> Y)"

definition upwards_closed::"('w \<sigma>)\<sigma> \<Rightarrow> bool"
  where "upwards_closed S \<equiv> \<forall>X Y. S X \<and> X \<preceq> Y \<longrightarrow> S Y"
definition downwards_closed::"('w \<sigma>)\<sigma> \<Rightarrow> bool" 
where "downwards_closed S \<equiv> \<forall>X Y. S X \<and> Y \<preceq> X \<longrightarrow> S Y"


subsection \<open>Atomicity and primitive equality\<close>

(**We can verify indeed that the algebra is atomic (in three different ways) by relying on the
presence of primitive equality in HOL.*)

lemma atomic1: "\<forall>w. \<exists>Q. Q w \<and> (\<forall>P. P w \<longrightarrow> Q \<preceq> P)" unfolding order using the_sym_eq_trivial by metis

definition "atom A \<equiv> \<not>(A \<approx> \<^bold>\<bottom>) \<and> (\<forall>P. A \<preceq> P \<or> A \<preceq> \<^bold>\<midarrow>P)"

lemma atomic2: "\<forall>w. \<exists>Q. Q w \<and> atom Q" unfolding atom_def order conn using the_sym_eq_trivial by metis
lemma atomic3: "\<forall>P. \<not>(P \<approx> \<^bold>\<bottom>) \<longrightarrow> (\<exists>Q. atom Q \<and> Q \<preceq> P)" unfolding atom_def order conn by fastforce

(*and now with interactive proof*)
lemma "\<forall>P. \<not>(P \<approx> \<^bold>\<bottom>) \<longrightarrow> (\<exists>Q. atom Q \<and> Q \<preceq> P)"
proof -
  { fix P::"'w \<sigma>"
    { assume "\<not>(P \<approx> \<^bold>\<bottom>)"
      hence "\<exists>v. P v" unfolding conn order by simp
      then obtain w where 1:"P w" by (rule exE)
      let ?Q="\<lambda>v. v = w" (*using HOL primitive equality*)
      have 2: "atom ?Q" unfolding atom_def unfolding conn order by simp
      have "\<forall>v. ?Q v \<longrightarrow> P v" using 1 by simp
      hence 3: "?Q \<preceq> P" unfolding order by simp
      from 2 3 have "\<exists>Q. atom Q \<and> Q \<preceq> P" by blast
    } hence "\<not>(P \<approx> \<^bold>\<bottom>) \<longrightarrow> (\<exists>Q. atom Q \<and> Q \<preceq> P)" by (rule impI)
  } thus ?thesis by (rule allI)
qed

end