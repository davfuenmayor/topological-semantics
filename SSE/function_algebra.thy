theory function_algebra
  imports boolean_algebra
begin

subsection \<open>Operations on set-valued functions\<close>

(**We conveniently define some (2nd-order) Boolean operations on set-valued functions*)
(**The 'meet' and 'join' of two set-valued functions: *)
definition sfun_meet::"('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>)" (infixr "\<^bold>\<sqinter>" 62) 
  where "\<phi> \<^bold>\<sqinter> \<psi> \<equiv> \<lambda>X. \<phi> X \<^bold>\<and> \<psi> X"
definition sfun_join::"('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>)" (infixr "\<^bold>\<squnion>" 61) 
  where "\<phi> \<^bold>\<squnion> \<psi> \<equiv> \<lambda>X. \<phi> X \<^bold>\<or> \<psi> X"
(**analogously, we can define an implication: *)
definition sfun_impl::"('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>)" (infixr "\<^bold>\<sqsupset>" 61) 
  where "\<psi> \<^bold>\<sqsupset> \<phi> \<equiv> \<lambda>X. (\<psi> X) \<^bold>\<rightarrow> (\<phi> X)"

(**The 'complement' of a set-valued function: *)
definition sfun_compl::"('i \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('i \<Rightarrow> 'p \<sigma>)" ("(_\<^sup>c)") 
  where "\<phi>\<^sup>c \<equiv> \<lambda>X. \<^bold>\<midarrow>(\<phi> X)"

lemma sfun_impl_char: "\<psi> \<^bold>\<sqsupset> \<phi> = \<psi>\<^sup>c \<^bold>\<squnion> \<phi>" by (simp add: compl_def impl_def join_def sfun_compl_def sfun_impl_def sfun_join_def)
lemma sfun_deMorgan1: "(\<psi> \<^bold>\<sqinter> \<phi>)\<^sup>c = (\<psi>\<^sup>c) \<^bold>\<squnion> (\<phi>\<^sup>c)" by (simp add: compl_def join_def meet_def sfun_compl_def sfun_join_def sfun_meet_def)
lemma sfun_deMorgan2: "(\<psi> \<^bold>\<squnion> \<phi>)\<^sup>c = (\<psi>\<^sup>c) \<^bold>\<sqinter> (\<phi>\<^sup>c)" by (simp add: compl_def join_def meet_def sfun_compl_def sfun_join_def sfun_meet_def)


(**Dual to set-valued functions we can have set-domain functions. For them we can define the 'dual-complement'*)
definition sfun_dualcompl::"('p \<sigma> \<Rightarrow> 'i) \<Rightarrow> ('p \<sigma> \<Rightarrow> 'i)" ("(_\<^sup>-)") 
  where "\<phi>\<^sup>- \<equiv> \<lambda>X. \<phi>(\<^bold>\<midarrow>X)"
(**alternative definition of dual-complement*)
lemma sfun_dualcompl_char: "\<phi>\<^sup>- = (\<lambda>X. \<exists>Y. (\<phi> Y) \<and> (X = \<^bold>\<midarrow>Y))" by (metis BA_dn setequ_ext sfun_dualcompl_def)

(**Unary operations (on sets) are a particularly important kind of functions which are set-valued 
and set-domain functions at the same time. For them we can conveniently define the 'dual'*)
definition op_dual::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('p \<sigma> \<Rightarrow> 'p \<sigma>)" ("(_\<^sup>d)") 
  where "\<phi>\<^sup>d \<equiv> \<lambda>X. \<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>X))"

(**The operations to be denoted by (+) and (-) already exist. We just introduce convenient notation.*)
definition id::"'p \<sigma> \<Rightarrow> 'p \<sigma>" ("+") where "+A \<equiv> A" (*introduces (+) notation for identity operation*)
notation compl ("-") (*introduces notation to refer to the set-complement operation as (-)*)

named_theorems op_conn (*to group together definitions for 2nd-order relation and operations*)
declare sfun_compl_def[op_conn] sfun_join_def[op_conn] sfun_meet_def[op_conn]
        op_dual_def[op_conn] sfun_dualcompl_def[op_conn] id_def[op_conn]

(**We now prove some lemmas (some of them might help provers in their hard work).*)
lemma dual_compl_char1: "\<phi>\<^sup>- = (\<phi>\<^sup>d)\<^sup>c" unfolding op_conn conn order by simp
lemma dual_compl_char2: "\<phi>\<^sup>- = (\<phi>\<^sup>c)\<^sup>d" unfolding op_conn conn order by simp
lemma sfun_compl_invol: "\<phi>\<^sup>c\<^sup>c = \<phi>" unfolding op_conn conn order by simp
lemma dual_invol: "\<phi>\<^sup>d\<^sup>d = \<phi>" unfolding op_conn conn order by simp
lemma dualcompl_invol: "(\<phi>\<^sup>-)\<^sup>- = \<phi>" unfolding op_conn conn order by simp

lemma "(+)\<^sup>d = (+)" unfolding op_conn conn by simp
lemma "(+)\<^sup>c = (-)" unfolding op_conn conn by simp
lemma "(\<phi> \<^bold>\<squnion> \<psi>)\<^sup>d = (\<phi>\<^sup>d) \<^bold>\<sqinter> (\<psi>\<^sup>d)" unfolding op_conn conn by simp
lemma "(\<phi> \<^bold>\<squnion> \<psi>)\<^sup>c = (\<phi>\<^sup>c) \<^bold>\<sqinter> (\<psi>\<^sup>c)" unfolding op_conn conn by simp
lemma "(\<phi> \<^bold>\<sqinter> \<psi>)\<^sup>d = (\<phi>\<^sup>d) \<^bold>\<squnion> (\<psi>\<^sup>d)" unfolding op_conn conn by simp
lemma "(\<phi> \<^bold>\<sqinter> \<psi>)\<^sup>c = (\<phi>\<^sup>c) \<^bold>\<squnion> (\<psi>\<^sup>c)" unfolding op_conn conn by simp

(**The notion of a fixed-point is fundamental. We speak of sets being fixed-points of operations.
We define a function that given an operation returns the set of all its fixed-points.*)
definition fixpoints::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('p \<sigma>)\<sigma>" ("fp") 
  where "fp \<phi> \<equiv> \<lambda>X. \<phi> X \<^bold>\<approx> X"
(**We can 'operationalize' the function above by defining a (2nd-order) 'fixed-point operator':*)
definition fixpoint_op::"('p \<sigma> \<Rightarrow> 'p \<sigma>) \<Rightarrow> ('p \<sigma> \<Rightarrow> 'p \<sigma>)" ("(_\<^sup>f\<^sup>p)") 
  where "\<phi>\<^sup>f\<^sup>p \<equiv> \<lambda>X. (\<phi> X) \<^bold>\<leftrightarrow> X"

declare fixpoints_def[op_conn] fixpoint_op_def[op_conn]

lemma fp_dual: "(fp \<phi>\<^sup>d) = (fp \<phi>)\<^sup>-" unfolding order conn op_conn by auto

(**The fixed-points function and the fixed-point operator are essentially related.*)
lemma fp_rel: "fp \<phi> A \<longleftrightarrow> (\<phi>\<^sup>f\<^sup>p A) \<^bold>\<approx> \<^bold>\<top>" unfolding op_conn order conn by simp
lemma fp_d_rel:  "fp \<phi>\<^sup>d A \<longleftrightarrow> \<phi>\<^sup>f\<^sup>p(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<top>" unfolding op_conn order conn by blast
lemma fp_c_rel: "fp \<phi>\<^sup>c A \<longleftrightarrow> \<phi>\<^sup>f\<^sup>p A \<^bold>\<approx> \<^bold>\<bottom>" unfolding op_conn order conn by blast
lemma fp_dc_rel: "fp (\<phi>\<^sup>-) A \<longleftrightarrow> \<phi>\<^sup>f\<^sup>p(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<bottom>" unfolding op_conn order conn by simp

lemma ofp_invol: "(\<phi>\<^sup>f\<^sup>p)\<^sup>f\<^sup>p = \<phi>" unfolding op_conn order conn by blast
lemma ofp_comm_compl: "(\<phi>\<^sup>c)\<^sup>f\<^sup>p = (\<phi>\<^sup>f\<^sup>p)\<^sup>c" unfolding op_conn order conn by blast
lemma ofp_comm_dc1: "(\<phi>\<^sup>d)\<^sup>f\<^sup>p = (\<phi>\<^sup>f\<^sup>p)\<^sup>-" unfolding op_conn order conn by blast
lemma ofp_comm_dc2:"(\<phi>\<^sup>-)\<^sup>f\<^sup>p = (\<phi>\<^sup>f\<^sup>p)\<^sup>d" unfolding op_conn order conn by simp
lemma ofp_decomp: "\<phi>\<^sup>f\<^sup>p = (\<phi> \<^bold>\<sqinter> (+)) \<^bold>\<squnion> (\<phi>\<^sup>c \<^bold>\<sqinter> (-))" unfolding op_conn order conn by blast


end