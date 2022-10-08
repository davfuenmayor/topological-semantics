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
hide_const(open) Groups.minus_class.minus no_notation Groups.minus_class.minus (infixl "-" 65) (*we don't use this*)
(*---------------------------------*)

section \<open>Shallow semantical embedding of (a logic of) Boolean algebras\<close>

(**We encode Boolean algebras via their (Stone) representation as algebras of sets ('fields of sets').
This means that each element of (the carrier of) the algebra will be a set of `points'.
Inspired by the 'propositions as sets of worlds' paradigm from modal logic, we can sometimes refer
to points as 'worlds', and thus to the elements of our Boolean algebras as 'propositions'.
However, this is only one possibility, since points can themselves be taken as sets (e.g. of `worlds')
and thus as 'propositions'. In such a case the elements of our Boolean algebras might correspond
to 'theories' (i.e. sets of 'propositions').*)

(**We utilize a particular naming convention: The type parameter @{type "'p"} is employed for the
domain/universe of `points'. We conveniently introduce the (parametric) type-alias @{type "'p \<sigma>"} 
as shorthand for @{type "'p\<Rightarrow>bool"}. Hence, the elements of our algebra are objects of type @{type "'p \<sigma>"},
and thus correspond to (characteristic functions of) sets of `points'. Observe that the type parameter
'p can itself correspond to a 'set type', and so elements of our algebras can have type @{type "('p \<sigma>)\<sigma>"}.
Set-valued (set-domain) functions are thus functions that have sets (of points) as their codomain (domain),
they are basically anything with a (parametric) type @{type "'i\<Rightarrow>'p \<sigma>"} (@{type "'p \<sigma>\<Rightarrow>'i"}).*)

type_synonym 'p \<sigma> = \<open>'p \<Rightarrow> bool\<close> (*type for (characteristic functions of) sets (of points)*)

(**In the sequel, we will (try to) enforce the following naming convention:

(i) Upper-case latin letters (A, B, D, M, P, S, X, etc.) denote arbitrary sets (type @{type "'p \<sigma>"}).
We will employ lower-case letters (p, q, x, w, etc.) to denote variables playing the role of 'points'.
In some contexts, the letters S and D will be employed to denote sets/domains of sets (of 'points').

(ii) Greek letters denote arbitrary set-valued functions (type @{type "'i\<Rightarrow>'p \<sigma>"} aliased @{type "('i \<Rightarrow> 'p \<sigma>)"}).
We employ the letters @{text "\<phi>"}, @{text "\<psi>"} and @{text "\<eta>"} to denote arbitrary unary operations
(with type @{type "'p \<sigma> \<Rightarrow> 'p \<sigma>"}); and the letters @{text "\<xi>"} and @{text "\<delta>"} to denote 
arbitrary binary operations (with type @{type "'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma>"}).

(iii) Upper-case calligraphic letters (\<B>, \<I>, \<C>, \<P>, etc.) are reserved for unary operations that are
intended to act as so-called 'topological operators' in the given context.
*)

subsection \<open>Encoding Boolean operations\<close>

(**Standard inclusion-based order structure on sets.*)
definition subset::"'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> bool" (infixr "\<^bold>\<preceq>" 45) 
  where "A \<^bold>\<preceq> B \<equiv> \<forall>p. A p \<longrightarrow> B p"
definition setequ::"'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> bool" (infixr "\<^bold>\<approx>" 45) 
  where "A \<^bold>\<approx> B \<equiv> \<forall>p. A p \<longleftrightarrow> B p"

named_theorems order (*to group together order-related definitions*)
declare setequ_def[order] subset_def[order]

(**These (trivial) lemmas are intended to help automated tools with equational reasoning.*)
lemma setequ_char: "(A \<^bold>\<approx> B) = (A \<^bold>\<preceq> B \<and> B \<^bold>\<preceq> A)" unfolding order by blast
lemma setequ_ext: "(A \<^bold>\<approx> B) = (A = B)" unfolding order by blast

(**We now encode connectives for (distributive and complemented) bounded lattices, mostly 
by reusing their counterpart meta-logical HOL connectives,*)
definition meet::"'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma>" (infixr "\<^bold>\<and>" 54) 
  where "A \<^bold>\<and> B \<equiv> \<lambda>p. (A p) \<and> (B p)" (**intersection*)
definition join::"'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma>" (infixr "\<^bold>\<or>" 53) 
  where "A \<^bold>\<or> B \<equiv> \<lambda>p. (A p) \<or> (B p)" (**union*)
definition top::"'p \<sigma>" ("\<^bold>\<top>")    
  where "\<^bold>\<top> \<equiv> \<lambda>w. True"   (**universe*)
definition bottom::"'p \<sigma>" ("\<^bold>\<bottom>") 
  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"  (**empty-set*)

(**and introduce further operations to obtain a Boolean algebra (of sets).*)
definition compl::"'p \<sigma> \<Rightarrow> 'p \<sigma>" ("\<^bold>\<midarrow>_"[57]58)
  where "\<^bold>\<midarrow>A  \<equiv> \<lambda>p. \<not>(A p)" (** (set-)complement*)
definition impl::"'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma>" (infixr "\<^bold>\<rightarrow>" 51)
  where "A \<^bold>\<rightarrow> B \<equiv> \<lambda>p. (A p) \<longrightarrow> (B p)" (** (set-)implication*)
definition diff::"'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma>" (infixr "\<^bold>\<leftharpoonup>" 51) 
  where "A \<^bold>\<leftharpoonup> B \<equiv> \<lambda>p. (A p) \<and> \<not>(B p)" (** (set-)difference*)
definition dimpl::"'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma>" (infixr "\<^bold>\<leftrightarrow>" 51) 
  where "A \<^bold>\<leftrightarrow> B \<equiv> \<lambda>p. (A p) = (B p)" (** double implication*)
definition sdiff::"'p \<sigma> \<Rightarrow> 'p \<sigma> \<Rightarrow> 'p \<sigma>" (infixr "\<^bold>\<triangle>" 51) 
  where "A \<^bold>\<triangle> B \<equiv> \<lambda>p. (A p) \<noteq> (B p)" (** symmetric difference (aka. xor) *)

named_theorems conn (*to group together definitions for algebraic connectives*)
declare meet_def[conn] join_def[conn] top_def[conn] bottom_def[conn]
        impl_def[conn] dimpl_def[conn] diff_def[conn] sdiff_def[conn] compl_def[conn]

(**Verify characterization for some connectives.*)
lemma compl_char: "\<^bold>\<midarrow>A = A \<^bold>\<rightarrow> \<^bold>\<bottom>" unfolding conn by simp
lemma impl_char: "A \<^bold>\<rightarrow> B = \<^bold>\<midarrow>A \<^bold>\<or> B" unfolding conn by simp
lemma diff_char: "A \<^bold>\<leftharpoonup> B = \<^bold>\<midarrow>(A \<^bold>\<rightarrow> B)" unfolding conn by simp
lemma dimpl_char: "A \<^bold>\<leftrightarrow> B = (A \<^bold>\<rightarrow> B) \<^bold>\<and> (B \<^bold>\<rightarrow> A)" unfolding conn by blast
lemma sdiff_char: "A \<^bold>\<triangle> B = (A \<^bold>\<leftharpoonup> B) \<^bold>\<or> (B \<^bold>\<leftharpoonup> A)" unfolding conn by blast

(**We can verify that (quite trivially) this algebra satisfies some properties of lattices.*)
lemma L1: "A \<^bold>\<approx> A \<^bold>\<or> A" unfolding conn order by simp
lemma L2: "A \<^bold>\<approx> A \<^bold>\<and> A" unfolding conn order by simp
lemma L3: "A \<^bold>\<preceq> A \<^bold>\<or> B" unfolding conn order by simp
lemma L4: "A \<^bold>\<and> B \<^bold>\<preceq> A" unfolding conn order by simp
lemma L5: "(A \<^bold>\<and> B) \<^bold>\<or> B \<^bold>\<approx> B" unfolding setequ_char conn order by simp 
lemma L6: "A \<^bold>\<and> (A \<^bold>\<or> B) \<^bold>\<approx> A" unfolding setequ_char conn order by simp
lemma L7: "A \<^bold>\<preceq> C \<and> B \<^bold>\<preceq> C \<longrightarrow> A \<^bold>\<or> B \<^bold>\<preceq> C" unfolding conn order by simp 
lemma L8: "C \<^bold>\<preceq> A \<and> C \<^bold>\<preceq> B \<longrightarrow> C \<^bold>\<preceq> A \<^bold>\<and> B" unfolding conn order by simp
lemma L9: "A \<^bold>\<preceq> B \<longleftrightarrow> (A \<^bold>\<or> B) \<^bold>\<approx> B" unfolding setequ_char conn order by simp
lemma L10: "B \<^bold>\<preceq> A \<longleftrightarrow> (A \<^bold>\<and> B) \<^bold>\<approx> B" unfolding setequ_char conn order by simp
lemma L11: "A \<^bold>\<preceq> B \<and> C \<^bold>\<preceq> D \<longrightarrow> A \<^bold>\<or> C \<^bold>\<preceq> B \<^bold>\<or> D" unfolding conn order by simp
lemma L12: "A \<^bold>\<preceq> B \<and> C \<^bold>\<preceq> D \<longrightarrow> A \<^bold>\<and> C \<^bold>\<preceq> B \<^bold>\<and> D" unfolding conn order by simp
lemma L13: "A \<^bold>\<and> \<^bold>\<top> \<^bold>\<approx> A" unfolding conn order by simp
lemma L14: "A \<^bold>\<or> \<^bold>\<bottom> \<^bold>\<approx> A" unfolding conn order by simp

(**These properties below hold in particular for Boolean algebras.*)
lemma BA_distr1: "(A \<^bold>\<and> (B \<^bold>\<or> C)) \<^bold>\<approx> ((A \<^bold>\<and> B) \<^bold>\<or> (A \<^bold>\<and> C))" unfolding setequ_char conn order by simp
lemma BA_distr2: "(A \<^bold>\<or> (B \<^bold>\<and> C)) \<^bold>\<approx> ((A \<^bold>\<or> B) \<^bold>\<and> (A \<^bold>\<or> C))" unfolding conn order by blast
lemma BA_cp: "A \<^bold>\<preceq> B \<longleftrightarrow> \<^bold>\<midarrow>B \<^bold>\<preceq> \<^bold>\<midarrow>A" unfolding conn order by blast 
lemma BA_deMorgan1: "\<^bold>\<midarrow>(A \<^bold>\<or> B) \<^bold>\<approx> (\<^bold>\<midarrow>A \<^bold>\<and> \<^bold>\<midarrow>B)" unfolding conn order by simp
lemma BA_deMorgan2: "\<^bold>\<midarrow>(A \<^bold>\<and> B) \<^bold>\<approx> (\<^bold>\<midarrow>A \<^bold>\<or> \<^bold>\<midarrow>B)" unfolding conn order by simp
lemma BA_dn: "\<^bold>\<midarrow>\<^bold>\<midarrow>A \<^bold>\<approx> A" unfolding conn order by simp
lemma BA_cmpl_equ: "(\<^bold>\<midarrow>A \<^bold>\<approx> B) = (A \<^bold>\<approx> \<^bold>\<midarrow>B)" unfolding conn order by blast


(**We conveniently introduce these properties of sets of sets (of points).*)
definition meet_closed::"('p \<sigma>)\<sigma> \<Rightarrow> bool"
  where "meet_closed S \<equiv>  \<forall>X Y. (S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<and> Y)"
definition join_closed::"('p \<sigma>)\<sigma> \<Rightarrow> bool"
  where "join_closed S \<equiv>  \<forall>X Y. (S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<or> Y)"

definition upwards_closed::"('p \<sigma>)\<sigma> \<Rightarrow> bool"
  where "upwards_closed S \<equiv> \<forall>X Y. S X \<and> X \<^bold>\<preceq> Y \<longrightarrow> S Y"
definition downwards_closed::"('p \<sigma>)\<sigma> \<Rightarrow> bool" 
where "downwards_closed S \<equiv> \<forall>X Y. S X \<and> Y \<^bold>\<preceq> X \<longrightarrow> S Y"


subsection \<open>Atomicity and primitive equality\<close>

(**We can verify indeed that the algebra is atomic (in three different ways) by relying on the
presence of primitive equality in HOL.*)

lemma atomic1: "\<forall>w. \<exists>Q. Q w \<and> (\<forall>P. P w \<longrightarrow> Q \<^bold>\<preceq> P)" unfolding order using the_sym_eq_trivial by metis

definition "atom A \<equiv> \<not>(A \<^bold>\<approx> \<^bold>\<bottom>) \<and> (\<forall>P. A \<^bold>\<preceq> P \<or> A \<^bold>\<preceq> \<^bold>\<midarrow>P)"

lemma atomic2: "\<forall>w. \<exists>Q. Q w \<and> atom Q" unfolding atom_def order conn using the_sym_eq_trivial by metis
lemma atomic3: "\<forall>P. \<not>(P \<^bold>\<approx> \<^bold>\<bottom>) \<longrightarrow> (\<exists>Q. atom Q \<and> Q \<^bold>\<preceq> P)" unfolding atom_def order conn by fastforce

(*and now with interactive proof*)
lemma "\<forall>P. \<not>(P \<^bold>\<approx> \<^bold>\<bottom>) \<longrightarrow> (\<exists>Q. atom Q \<and> Q \<^bold>\<preceq> P)"
proof -
  { fix P
    { assume "\<not>(P \<^bold>\<approx> \<^bold>\<bottom>)"
      hence "\<exists>v. P v" unfolding conn order by simp
      then obtain w where 1:"P w" by (rule exE)
      let ?Q="\<lambda>v. v = w" (*using HOL primitive equality*)
      have 2: "atom ?Q" unfolding atom_def unfolding conn order by simp
      have "\<forall>v. ?Q v \<longrightarrow> P v" using 1 by simp
      hence 3: "?Q \<^bold>\<preceq> P" unfolding order by simp
      from 2 3 have "\<exists>Q. atom Q \<and> Q \<^bold>\<preceq> P" by blast
    } hence "\<not>(P \<^bold>\<approx> \<^bold>\<bottom>) \<longrightarrow> (\<exists>Q. atom Q \<and> Q \<^bold>\<preceq> P)" by (rule impI)
  } thus ?thesis by (rule allI)
qed

end