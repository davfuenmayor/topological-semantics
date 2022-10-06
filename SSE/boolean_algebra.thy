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

section \<open>Shallow semantical embedding of (a logic of) Boolean algebras (of propositions)\<close>

(**We encode Boolean algebras via their (Stone) representation as algebras of sets ('fields of sets').
This means that each element of (the carrier of) the algebra will be a set (of points).
Inspired by the 'propositions as sets of worlds' paradigm from modal logic, we will often refer
to points as 'worlds', and thus to the elements of our Boolean algebras as 'propositions'.*)

(**We utilize a particular naming convention:
The type parameter @{type "'w"} is employed for the domain/universe of points (aka. 'worlds').
We conveniently introduce the (parametric) type-alias @{type "'w \<sigma>"} as shorthand for @{type "'w\<Rightarrow>bool"}.
Hence, the elements of our algebra (propositions) are objects of type @{type "'w \<sigma>"},
and thus correspond to (characteristic functions of) sets of points.
Propositional functions, as the name suggests, are functions that have propositions as their codomain,
they are basically anything with a (parametric) type @{type "'e\<Rightarrow>'w \<sigma>"} (aliased @{type "('e,'w)\<pi>"}.*)

type_synonym 'w \<sigma> = \<open>'w \<Rightarrow> bool\<close> (*type for propositions as (characteristic functions of) sets*)
type_synonym ('e,'w)\<pi> = \<open>'e \<Rightarrow> 'w \<sigma>\<close> (*type for propositional functions*)

(**In the sequel, we will (try to) enforce the following naming convention:

(i) Latin letters (A, b, M, P, q, X, y, etc.) denote in general propositions (type @{type "'w \<sigma>"}),
excepting the letters S and D which we use to denote sets/domains of propositions, 
and the letters u, v and w which we use to denote worlds/points.

(ii) Greek letters denote propositional functions in general (type @{type "'e \<Rightarrow> 'w \<sigma>"}).
We employ the letters @{text "\<phi>"}, @{text "\<psi>"} and @{text "\<eta>"} to denote unary operations
(with type @{type "'w \<sigma> \<Rightarrow> 'w \<sigma>"}); and the letters @{text "\<xi>"} and @{text "\<delta>"} to denote 
binary operations (with type @{type "'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>"}).*)

subsection \<open>Encoding Boolean operations\<close>

(**Standard inclusion-based order structure on sets.*)
definition subset::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" (infixr "\<^bold>\<preceq>" 45) 
  where "A \<^bold>\<preceq> B \<equiv> \<forall>w. A w \<longrightarrow> B w"
definition setequ::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" (infixr "\<^bold>\<approx>" 45) 
  where "A \<^bold>\<approx> B \<equiv> \<forall>w. A w \<longleftrightarrow> B w"

named_theorems order (*to group together order-related definitions*)
declare setequ_def[order] subset_def[order]

(**These (trivial) lemmas are intended to help automated tools with equational reasoning.*)
lemma setequ_char: "(A \<^bold>\<approx> B) = (A \<^bold>\<preceq> B \<and> B \<^bold>\<preceq> A)" unfolding order by blast
lemma setequ_ext: "(A \<^bold>\<approx> B) = (A = B)" unfolding order by blast

(**We now encode connectives for (distributive and complemented) bounded lattices, mostly 
by reusing their counterpart meta-logical HOL connectives,*)
definition meet::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<and>" 54) 
  where "A \<^bold>\<and> B \<equiv> \<lambda>w. (A w) \<and> (B w)"
definition join::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<or>" 53) 
  where "A \<^bold>\<or> B \<equiv> \<lambda>w. (A w) \<or> (B w)"
definition top::"'w \<sigma>" ("\<^bold>\<top>")    
  where "\<^bold>\<top> \<equiv> \<lambda>w. True"
definition bottom::"'w \<sigma>" ("\<^bold>\<bottom>") 
  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"

(**and introduce further operations to obtain a Boolean 'algebra of propositions'.*)
definition compl::"'w \<sigma> \<Rightarrow> 'w \<sigma>" ("\<^bold>\<midarrow>_"[57]58)
  where "\<^bold>\<midarrow>A  \<equiv> \<lambda>w. \<not>(A w)" (** (set-)complement*)
definition impl::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<rightarrow>" 51)
  where "A \<^bold>\<rightarrow> B \<equiv> \<lambda>w. (A w) \<longrightarrow> (B w)" (** (set-)implication*)
definition diff::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<leftharpoonup>" 51) 
  where "A \<^bold>\<leftharpoonup> B \<equiv> \<lambda>w. (A w) \<and> \<not>(B w)" (** (set-)difference*)
definition dimpl::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<leftrightarrow>" 51) 
  where "A \<^bold>\<leftrightarrow> B \<equiv> \<lambda>w. (A w) = (B w)" (** double implication*)
definition sdiff::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<triangle>" 51) 
  where "A \<^bold>\<triangle> B \<equiv> \<lambda>w. (A w) \<noteq> (B w)" (** symmetric difference (aka. xor) *)

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
lemma L1: "a \<^bold>\<approx> a \<^bold>\<or> a" unfolding conn order by simp
lemma L2: "a \<^bold>\<approx> a \<^bold>\<and> a" unfolding conn order by simp
lemma L3: "a \<^bold>\<preceq> a \<^bold>\<or> b" unfolding conn order by simp
lemma L4: "a \<^bold>\<and> b \<^bold>\<preceq> a" unfolding conn order by simp
lemma L5: "(a \<^bold>\<and> b) \<^bold>\<or> b \<^bold>\<approx> b" unfolding setequ_char conn order by simp 
lemma L6: "a \<^bold>\<and> (a \<^bold>\<or> b) \<^bold>\<approx> a" unfolding setequ_char conn order by simp
lemma L7: "a \<^bold>\<preceq> c \<and> b \<^bold>\<preceq> c \<longrightarrow> a \<^bold>\<or> b \<^bold>\<preceq> c" unfolding conn order by simp 
lemma L8: "c \<^bold>\<preceq> a \<and> c \<^bold>\<preceq> b \<longrightarrow> c \<^bold>\<preceq> a \<^bold>\<and> b" unfolding conn order by simp
lemma L9: "a \<^bold>\<preceq> b \<longleftrightarrow> (a \<^bold>\<or> b) \<^bold>\<approx> b" unfolding setequ_char conn order by simp
lemma L10: "b \<^bold>\<preceq> a \<longleftrightarrow> (a \<^bold>\<and> b) \<^bold>\<approx> b" unfolding setequ_char conn order by simp
lemma L11: "a \<^bold>\<preceq> b \<and> c \<^bold>\<preceq> d \<longrightarrow> a \<^bold>\<or> c \<^bold>\<preceq> b \<^bold>\<or> d" unfolding conn order by simp
lemma L12: "a \<^bold>\<preceq> b \<and> c \<^bold>\<preceq> d \<longrightarrow> a \<^bold>\<and> c \<^bold>\<preceq> b \<^bold>\<and> d" unfolding conn order by simp
lemma L13: "X \<^bold>\<and> \<^bold>\<top> \<^bold>\<approx> X" unfolding conn order by simp
lemma L14: "X \<^bold>\<or> \<^bold>\<bottom> \<^bold>\<approx> X" unfolding conn order by simp

(**These properties below hold in particular for Boolean algebras.*)
lemma BA_distr1: "(a \<^bold>\<and> (b \<^bold>\<or> c)) \<^bold>\<approx> ((a \<^bold>\<and> b) \<^bold>\<or> (a \<^bold>\<and> c))" unfolding setequ_char conn order by simp
lemma BA_distr2: "(a \<^bold>\<or> (b \<^bold>\<and> c)) \<^bold>\<approx> ((a \<^bold>\<or> b) \<^bold>\<and> (a \<^bold>\<or> c))" unfolding conn order by blast
lemma BA_cp: "a \<^bold>\<preceq> b \<longleftrightarrow> \<^bold>\<midarrow>b \<^bold>\<preceq> \<^bold>\<midarrow>a" unfolding conn order by blast 
lemma BA_deMorgan1: "\<^bold>\<midarrow>(X \<^bold>\<or> Y) \<^bold>\<approx> (\<^bold>\<midarrow>X \<^bold>\<and> \<^bold>\<midarrow>Y)" unfolding conn order by simp
lemma BA_deMorgan2: "\<^bold>\<midarrow>(X \<^bold>\<and> Y) \<^bold>\<approx> (\<^bold>\<midarrow>X \<^bold>\<or> \<^bold>\<midarrow>Y)" unfolding conn order by simp
lemma BA_dn: "\<^bold>\<midarrow>\<^bold>\<midarrow>X \<^bold>\<approx> X" unfolding conn order by simp


(**Some additional relevant definitions and properties*)

definition meet_closed::"('w \<sigma>) \<sigma> \<Rightarrow> bool"
  where "meet_closed S \<equiv>  \<forall>X Y. (S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<and> Y)"
definition join_closed::"('w \<sigma>) \<sigma> \<Rightarrow> bool"
  where "join_closed S \<equiv>  \<forall>X Y. (S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<or> Y)"

definition upwards_closed::"('w \<sigma>) \<sigma> \<Rightarrow> bool"
  where "upwards_closed S \<equiv> \<forall>X Y. S X \<and> X \<^bold>\<preceq> Y \<longrightarrow> S Y"
definition downwards_closed::"('w \<sigma>) \<sigma> \<Rightarrow> bool" 
where "downwards_closed S \<equiv> \<forall>X Y. S X \<and> Y \<^bold>\<preceq> X \<longrightarrow> S Y"


subsection \<open>Transformations and relations on propositional functions\<close>

(**We define equality for propositional functions as follows.*)
definition pfun_equal::"('e,'w)\<pi> \<Rightarrow> ('e,'w)\<pi> \<Rightarrow> bool" (infix "\<^bold>\<equiv>" 60) 
  where "\<phi> \<^bold>\<equiv> \<psi> \<equiv> \<forall>X. \<phi> X \<^bold>\<approx> \<psi> X"

(**We conveniently define some (2nd-order) Boolean operations on propositional functions*)
(**Binary: meet and join*)
definition pfun_meet::"('e,'w)\<pi> \<Rightarrow> ('e,'w)\<pi> \<Rightarrow> ('e,'w)\<pi>" (infixr "\<^bold>\<sqinter>" 62) 
  where "\<phi> \<^bold>\<sqinter> \<psi> \<equiv> \<lambda>X. \<phi> X \<^bold>\<and> \<psi> X"
definition pfun_join::"('e,'w)\<pi> \<Rightarrow> ('e,'w)\<pi> \<Rightarrow> ('e,'w)\<pi>" (infixr "\<^bold>\<squnion>" 61) 
  where "\<phi> \<^bold>\<squnion> \<psi> \<equiv> \<lambda>X. \<phi> X \<^bold>\<or> \<psi> X"
(**Unary: complement*)
definition pfun_compl::"('e,'w)\<pi> \<Rightarrow> ('e,'w)\<pi>" ("(_\<^sup>c)") 
  where "\<phi>\<^sup>c \<equiv> \<lambda>X. \<^bold>\<midarrow>(\<phi> X)"

(*Unary operations are particularly important propositional functions, we conveniently define:*)

(*Unary: dual and dual-complement*)
definition op_dual::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("(_\<^sup>d)") 
  where "\<phi>\<^sup>d \<equiv> \<lambda>X. \<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>X))"
definition op_dualcompl::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("(_\<^sup>d\<^sup>c)") 
  where "\<phi>\<^sup>d\<^sup>c \<equiv> \<lambda>X. \<phi>(\<^bold>\<midarrow>X)"
(**The constants denoted by (+) and (-) already exist. We just introduce them as convenient notation.*)
definition id::"'w \<sigma> \<Rightarrow> 'w \<sigma>" ("+") where "+A \<equiv> A" (*introduces dummy identity operator (+)*)
notation compl ("-") (*adds notation to refer to the set-complement as (-)*)

named_theorems op_conn (*to group together definitions for connectives on operations*)
declare pfun_equal_def[op_conn] pfun_compl_def[op_conn] pfun_join_def[op_conn] pfun_meet_def[op_conn]
        op_dual_def[op_conn] op_dualcompl_def[op_conn] id_def[op_conn]

(**We now prove some lemmas (some of them might help provers in their hard work).*)
lemma pfun_equal_ext: "(\<phi> \<^bold>\<equiv> \<psi>) = (\<phi> = \<psi>)" using pfun_equal_def setequ_ext by auto  
lemma dual_compl_char1: "\<phi>\<^sup>d\<^sup>c \<^bold>\<equiv> (\<phi>\<^sup>d)\<^sup>c" unfolding op_conn conn order by simp
lemma dual_compl_char2: "\<phi>\<^sup>d\<^sup>c \<^bold>\<equiv> (\<phi>\<^sup>c)\<^sup>d" unfolding op_conn conn order by simp
lemma pfun_compl_invol: "\<phi>\<^sup>c\<^sup>c \<^bold>\<equiv> \<phi>" unfolding op_conn conn order by simp
lemma dual_invol: "\<phi>\<^sup>d\<^sup>d \<^bold>\<equiv> \<phi>" unfolding op_conn conn order by simp
lemma dualcompl_invol: "(\<phi>\<^sup>d\<^sup>c)\<^sup>d\<^sup>c \<^bold>\<equiv> \<phi>" unfolding op_conn conn order by simp

lemma "(+)\<^sup>d \<^bold>\<equiv> (+)" by (simp add: BA_dn id_def op_dual_def pfun_equal_def)
lemma "(+)\<^sup>c \<^bold>\<equiv> (-)" by (simp add: id_def pfun_compl_def pfun_equal_def setequ_ext)
lemma "(A \<^bold>\<squnion> B)\<^sup>d \<^bold>\<equiv> (A\<^sup>d) \<^bold>\<sqinter> (B\<^sup>d)" by (simp add: BA_deMorgan1 op_dual_def pfun_equal_def pfun_join_def pfun_meet_def)
lemma "(A \<^bold>\<squnion> B)\<^sup>c \<^bold>\<equiv> (A\<^sup>c) \<^bold>\<sqinter> (B\<^sup>c)" by (simp add: BA_deMorgan1 pfun_compl_def pfun_equal_def pfun_join_def pfun_meet_def)
lemma "(A \<^bold>\<sqinter> B)\<^sup>d \<^bold>\<equiv> (A\<^sup>d) \<^bold>\<squnion> (B\<^sup>d)" by (simp add: BA_deMorgan2 op_dual_def pfun_equal_def pfun_join_def pfun_meet_def)
lemma "(A \<^bold>\<sqinter> B)\<^sup>c \<^bold>\<equiv> (A\<^sup>c) \<^bold>\<squnion> (B\<^sup>c)" by (simp add: BA_deMorgan2 pfun_compl_def pfun_equal_def pfun_join_def pfun_meet_def)

(**The notion of a fixed point is a fundamental one. We speak of propositions being fixed points of
operations. For a given operation we define in the usual way a fixed-point predicate for propositions.*)
definition fixpoint_pred::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" ("fp") 
  where "fp \<phi> \<equiv> \<lambda>X. \<phi> X \<^bold>\<approx> X"
(**We can 'operationalize' this fixed-point predicate by defining a fixed-point (2nd-order) operator:*)
(* definition fixpoint_op::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("(_\<^sup>f\<^sup>p)" [70]71)  *)
definition fixpoint_op::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("(_\<^sup>f\<^sup>p)") 
  where "\<phi>\<^sup>f\<^sup>p \<equiv> \<lambda>X. (\<phi> X) \<^bold>\<leftrightarrow> X"

declare fixpoint_pred_def[op_conn] fixpoint_op_def[op_conn]

lemma fp_d: "(fp \<phi>\<^sup>d) A \<longleftrightarrow> (fp \<phi>)(\<^bold>\<midarrow>A)" unfolding op_conn order conn by blast
lemma fp_c: "(fp \<phi>\<^sup>c) A \<longleftrightarrow> (A \<^bold>\<approx> \<^bold>\<midarrow>(\<phi> A))" unfolding op_conn order conn by blast
lemma fp_dc:"(fp \<phi>\<^sup>d\<^sup>c) A \<longleftrightarrow> (A \<^bold>\<approx> \<phi>(\<^bold>\<midarrow>A))" unfolding op_conn order conn by blast
lemma ofp_invol: "(\<phi>\<^sup>f\<^sup>p)\<^sup>f\<^sup>p \<^bold>\<equiv> \<phi>" unfolding op_conn order conn by blast
lemma ofp_c: "(\<phi>\<^sup>c)\<^sup>f\<^sup>p \<^bold>\<equiv> (\<phi>\<^sup>f\<^sup>p)\<^sup>c" unfolding op_conn order conn by blast
lemma ofp_d: "(\<phi>\<^sup>d)\<^sup>f\<^sup>p \<^bold>\<equiv> (\<phi>\<^sup>f\<^sup>p)\<^sup>d\<^sup>c" unfolding op_conn order conn by blast
lemma ofp_dc:"(\<phi>\<^sup>d\<^sup>c)\<^sup>f\<^sup>p \<^bold>\<equiv> (\<phi>\<^sup>f\<^sup>p)\<^sup>d" unfolding op_conn order conn by simp
lemma ofp_decomp: "\<phi>\<^sup>f\<^sup>p \<^bold>\<equiv> (\<phi> \<^bold>\<sqinter> (+)) \<^bold>\<squnion> (\<phi>\<^sup>c \<^bold>\<sqinter> (-))" unfolding op_conn order conn by blast

(**Fixed-point predicate and fixed-point operator are closely related.*)
lemma fp_rel: "(fp \<phi>) X \<longleftrightarrow> (\<phi>\<^sup>f\<^sup>p X) \<^bold>\<approx> \<^bold>\<top>" unfolding op_conn order conn by simp
lemma fp_d_rel:  "(fp \<phi>\<^sup>d) X \<longleftrightarrow> \<phi>\<^sup>f\<^sup>p(\<^bold>\<midarrow>X) \<^bold>\<approx> \<^bold>\<top>" using fp_d fp_rel by blast
lemma fp_c_rel: "(fp \<phi>\<^sup>c) X \<longleftrightarrow> \<phi>\<^sup>f\<^sup>p X \<^bold>\<approx> \<^bold>\<bottom>" unfolding op_conn order conn by blast
lemma fp_dc_rel: "(fp \<phi>\<^sup>d\<^sup>c) X \<longleftrightarrow> \<phi>\<^sup>f\<^sup>p(\<^bold>\<midarrow>X) \<^bold>\<approx> \<^bold>\<bottom>" unfolding op_conn order conn by simp

subsection \<open>Atomicity and primitive equality\<close>

(**We can verify indeed that the algebra is atomic (in three different ways) by relying on the
presence of primitive equality in HOL.*)
lemma atomic1: "\<forall>w. \<exists>q. q w \<and> (\<forall>p. p w \<longrightarrow> q \<^bold>\<preceq> p)" unfolding order using the_sym_eq_trivial by metis

definition "atom a \<equiv> \<not>(a \<^bold>\<approx> \<^bold>\<bottom>) \<and> (\<forall>p. a \<^bold>\<preceq> p \<or> a \<^bold>\<preceq> \<^bold>\<midarrow>p)"
lemma atomic2: "\<forall>w. \<exists>q. q w \<and> atom(q)" unfolding atom_def order conn using the_sym_eq_trivial by metis
lemma atomic3: "\<forall>p. \<not>(p \<^bold>\<approx> \<^bold>\<bottom>) \<longrightarrow> (\<exists>q. atom(q) \<and> q \<^bold>\<preceq> p)" unfolding atom_def order conn by fastforce

(*and now with interactive proof*)
lemma "\<forall>p. \<not>(p \<^bold>\<approx> \<^bold>\<bottom>) \<longrightarrow> (\<exists>q. atom(q) \<and> q \<^bold>\<preceq> p)"
proof -
  { fix p
    { assume "\<not>(p \<^bold>\<approx> \<^bold>\<bottom>)"
      hence "\<exists>v. p v" unfolding conn order by simp
      then obtain w where 1:"p w" by (rule exE)
      let ?q="\<lambda>v. v = w" (*using HOL primitive equality*)
      have 2: "atom ?q" unfolding atom_def unfolding conn order by simp
      have "\<forall>v. ?q v \<longrightarrow> p v" using 1 by simp
      hence 3: "?q \<^bold>\<preceq> p" unfolding order by simp
      from 2 3 have "\<exists>q. atom(q) \<and> q \<^bold>\<preceq> p" by blast
    } hence "\<not>(p \<^bold>\<approx> \<^bold>\<bottom>) \<longrightarrow> (\<exists>q. atom(q) \<and> q \<^bold>\<preceq> p)" by (rule impI)
  } thus ?thesis by (rule allI)
qed

end