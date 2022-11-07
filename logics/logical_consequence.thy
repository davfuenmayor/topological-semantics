theory logical_consequence
  imports "../boolean_algebra/boolean_algebra"
begin

(**Logical validity can be defined as truth in all points (i.e. as denoting the top element)*)
abbreviation gtrue::"'w \<sigma> \<Rightarrow> bool" ("[\<turnstile> _]") 
  where  "[\<turnstile> A] \<equiv> \<forall>w. A w"   
lemma gtrue_def: "[\<turnstile> A] \<equiv> A \<approx> \<^bold>\<top>" by (simp add: setequ_def top_def)

(**When defining a logic over an existing algebra we have two choices: a global (truth preserving)
and a local (degree preserving) notion of logical consequence. For LFIs we prefer the latter.*)
abbreviation conseq_global1::"'w \<sigma> \<Rightarrow> 'w \<sigma>\<Rightarrow>bool" ("[_ \<turnstile>\<^sub>g _]") 
  where "[A \<turnstile>\<^sub>g B] \<equiv> [\<turnstile> A] \<longrightarrow> [\<turnstile> B]"
abbreviation conseq_global2::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" ("[_,_ \<turnstile>\<^sub>g _]") 
  where "[A\<^sub>1, A\<^sub>2 \<turnstile>\<^sub>g B] \<equiv> [\<turnstile> A\<^sub>1] \<and> [\<turnstile> A\<^sub>2] \<longrightarrow> [\<turnstile> B]"
abbreviation conseq_global3::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" ("[_,_,_ \<turnstile>\<^sub>g _]") 
  where "[A\<^sub>1, A\<^sub>2, A\<^sub>3 \<turnstile>\<^sub>g B] \<equiv> [\<turnstile> A\<^sub>1] \<and> [\<turnstile> A\<^sub>2] \<and> [\<turnstile> A\<^sub>3] \<longrightarrow> [\<turnstile> B]"

abbreviation conseq_local1::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" ("[_ \<turnstile> _]") 
  where "[A \<turnstile> B] \<equiv> A \<preceq> B"
abbreviation conseq_local2::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" ("[_,_ \<turnstile> _]") 
  where "[A\<^sub>1, A\<^sub>2 \<turnstile> B] \<equiv> A\<^sub>1 \<^bold>\<and> A\<^sub>2 \<preceq> B"
abbreviation conseq_local3::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" ("[_,_,_ \<turnstile> _]") 
  where "[A\<^sub>1, A\<^sub>2, A\<^sub>3 \<turnstile> B] \<equiv> A\<^sub>1 \<^bold>\<and> A\<^sub>2 \<^bold>\<and> A\<^sub>3 \<preceq> B"
(*add more as the need arises...*)

end