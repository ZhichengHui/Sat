theory Sat_CDCL
  imports Sat_Proof.Sat_Minimize
begin

text \<open>The contract of the CDCL search of \<^verbatim>\<open>core/src/lib.rs\<close>, \<^verbatim>\<open>cdcl\<close>. The functions it calls
  (\<^verbatim>\<open>Sat_Search\<close>) only need to terminate without a panic. Its answers rest on the checks of
  \<^verbatim>\<open>Sat_Certify\<close>.\<close>

section \<open>The clause database of the search\<close>

text \<open>The facts about the clause database and the answers that the main loop of \<^verbatim>\<open>cdcl\<close> uses.\<close>

lemma learned_ok_Nil:
  \<open>learned_ok f []\<close>
  unfolding learned_ok_def by simp

lemma f_small:
  assumes \<open>sat_repr_ok f\<close> \<open>\<not> 0x4000000000000000 \<le> word64_of_nat (length (Formula_clauses f))\<close>
  shows \<open>length (Formula_clauses f) < 4611686018427387904\<close>
proof -
  have lf: \<open>length (Formula_clauses f) < 2 ^ 64\<close>
    using assms(1) unfolding sat_repr_ok_def by simp
  then have \<open>unat (word64_of_nat (length (Formula_clauses f))) = length (Formula_clauses f)\<close>
    by (simp add: unat_of_nat_eq)
  then show ?thesis
    using assms(2) by (simp add: word_le_nat_alt not_le)
qed

lemma db_small_of:
  assumes \<open>sat_repr_ok f\<close> \<open>length (Formula_clauses f) < 4611686018427387904\<close> \<open>learned_ok f L\<close>
  shows \<open>db_small f L\<close>
  using assms unfolding db_small_def db_def sat_repr_ok_def learned_ok_def by fastforce

lemma db_index_add:
  assumes \<open>length (Formula_clauses f) < 4611686018427387904\<close> \<open>length L < 4611686018427387904\<close>
  shows \<open>unat (word64_of_nat (length (Formula_clauses f))) + unat (word64_of_nat (length L))
    < 18446744073709551616\<close>
  using assms by (simp add: unat_of_nat_eq)

lemma learned_small:
  assumes \<open>learned_ok f L\<close> \<open>\<not> 0x4000000000000000 \<le> word64_of_nat (length L)\<close>
  shows \<open>length L < 4611686018427387904\<close>
proof -
  have \<open>length L < 2 ^ 64\<close>
    using assms(1) unfolding learned_ok_def by simp
  then have \<open>unat (word64_of_nat (length L)) = length L\<close>
    by (simp add: unat_of_nat_eq)
  then show ?thesis
    using assms(2) by (simp add: word_le_nat_alt not_le)
qed

lemma cdcl_post_None:
  \<open>cdcl_post f None\<close>
  unfolding cdcl_post_def by simp

lemma cdcl_post_Sat:
  \<open>length m = unat (Formula_num_vars f) \<Longrightarrow> formula_sat m f \<Longrightarrow>
    cdcl_post f (Some (Answer_Sat (make_Assignments m)))\<close>
  unfolding cdcl_post_def by simp

lemma cdcl_post_Unsat:
  \<open>learned_ok f L \<Longrightarrow> \<forall>a. \<exists>c \<in> set (db f L). \<not> clause_sat a c \<Longrightarrow>
    cdcl_post f (Some Answer_Unsat)\<close>
  unfolding cdcl_post_def using db_sat by fastforce

lemma half_add:
  assumes \<open>x < (0x4000000000000000 :: 64 word)\<close>
  shows \<open>unat x + unat (x div 2) < 18446744073709551616\<close>
proof -
  have \<open>unat (x div 2) \<le> unat x\<close>
    by (simp add: unat_div)
  then show ?thesis
    using big_c(1)[OF assms] by linarith
qed

lemma f_len64:
  \<open>sat_repr_ok f \<Longrightarrow> length (Formula_clauses f) < 18446744073709551616\<close>
  unfolding sat_repr_ok_def by simp

lemma learned_push':
  \<open>learned_ok f L \<Longrightarrow> \<not> 0x4000000000000000 \<le> word64_of_nat (length L) \<Longrightarrow>
    length x \<le> 4611686018427387904 \<Longrightarrow>
    \<forall>a. (\<forall>c \<in> set (db f L). clause_sat a c) \<longrightarrow> (\<exists>l \<in> set x. lit_sat a l) \<Longrightarrow>
    learned_ok f (L @ [make_Clause x])\<close>
  using learned_ok_push[of f L x] learned_small[of f L] by simp

section \<open>Bounds of the main loop\<close>

method cdcl_bound =
  (search_bound | rule cdcl_post_None learned_ok_Nil |
    (rule cdcl_post_Sat cdcl_post_Unsat half_add f_small f_len64 learned_push'; assumption) |
    (rule db_small_of db_index_add;
      (assumption | rule learned_ok_Nil | (rule f_small learned_small learned_push'; assumption))))

context Sat_ctx
begin

section \<open>The search with certified answers\<close>

text \<open>A conflict adds a certified learned clause to the database; \<^verbatim>\<open>cdcl\<close> answers only what the
  checks show.\<close>

definition on_conflict_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> ('addr, 'gv, Clause list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>on_conflict_contract r g s f lref gl L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> lref \<mapsto>\<langle>\<top>\<rangle> gl\<down>L \<star>
        \<langle>sat_repr_ok f \<and> length (Formula_clauses f) < 4611686018427387904 \<and> learned_ok f L\<rangle> in
     let post = \<lambda>res. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') \<star>
        (\<Squnion>gl' L'. lref \<mapsto>\<langle>\<top>\<rangle> gl'\<down>L' \<star>
           \<langle>learned_ok f L' \<and> (res = 1 \<longrightarrow> \<not> (\<exists>a. \<forall>c \<in> set (db f L'). clause_sat a c))\<rangle>) in
     make_function_contract pre post\<close>

lemma on_conflict_spec:
  shows \<open>\<Gamma>; on_conflict r f lref c \<Turnstile>\<^sub>F on_conflict_contract r g s f lref gl L c\<close>
  apply (crush_boot f: on_conflict_def contract: on_conflict_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def vec_push_def Clause_mk_def
      specs add: certify_spec Search_analyze_spec Search_backtrack_spec Search_attach_spec
        Search_enqueue_spec Search_learnt_lbd_spec
      contracts add: certify_contract_def Search_analyze_contract_def Search_backtrack_contract_def
        Search_attach_contract_def Search_enqueue_contract_def Search_learnt_lbd_contract_def
      simp add: true_def false_def)
  apply (all \<open>cdcl_bound?\<close>)
  done

definition cdcl_contract :: \<open>Formula \<Rightarrow> ('s, Answer option, 'abort) function_contract\<close> where
  \<open>cdcl_contract f \<equiv>
     let pre = can_alloc_reference \<star> \<langle>sat_repr_ok f\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>cdcl_post f r\<rangle> in
     make_function_contract pre post\<close>

lemma cdcl_spec:
  shows \<open>\<Gamma>; cdcl f \<Turnstile>\<^sub>F cdcl_contract f\<close>
  apply (crush_boot f: cdcl_def contract: cdcl_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def
      specs add: new_search_spec init_spec
      contracts add: new_search_contract_def init_contract_def
      simp add: true_def false_def)
  subgoal for _ s_ref l_ref _ _ _ confl_ref sr_ref ra_ref st_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gl L gc c gsr sr gra ra gt t. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>L \<star>
               confl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star>
               sr_ref \<mapsto>\<langle>\<top>\<rangle> gsr\<down>sr \<star> ra_ref \<mapsto>\<langle>\<top>\<rangle> gra\<down>ra \<star>
               st_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t \<star> can_alloc_reference \<star> \<langle>learned_ok f L\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gl L gc c gsr sr gra ra gt t. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>L \<star>
               confl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star>
               sr_ref \<mapsto>\<langle>\<top>\<rangle> gsr\<down>sr \<star> ra_ref \<mapsto>\<langle>\<top>\<rangle> gra\<down>ra \<star>
               st_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t \<star> can_alloc_reference \<star>
               \<langle>learned_ok f L \<and> t < 0xFFFFFFFFFFFFFFFF\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>cdcl_post f r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def NONE_def BIG_def vec_push_def Answer_Sat_mk_def Assignments_mk_def
        specs add: Search_propagate_spec on_conflict_spec Search_backtrack_spec Search_enqueue_spec
          Search_pick_spec model_spec satisfies_spec Search_reduce_spec Search_restart_due_spec
        contracts add: Search_propagate_contract_def on_conflict_contract_def Search_backtrack_contract_def
          Search_enqueue_contract_def Search_pick_contract_def model_contract_def satisfies_contract_def
          Search_reduce_contract_def Search_restart_due_contract_def
        simp add: true_def false_def)
    apply (all \<open>cdcl_bound?\<close>)
    done
  apply (all \<open>cdcl_bound?\<close>)
  done

end

end
