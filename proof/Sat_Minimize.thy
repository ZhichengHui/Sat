theory Sat_Minimize
  imports Sat_Proof.Sat_Search
begin

text \<open>The contracts of the conflict analysis of the CDCL search of \<^verbatim>\<open>core/src/lib.rs\<close> and of its
  recursive minimisation of the learned clause. As in \<^verbatim>\<open>Sat_Search\<close>, they only need to return
  without a panic: the learned clause is checked by \<^verbatim>\<open>certify\<close>.\<close>

context Sat_ctx
begin

section \<open>Recursive minimisation\<close>

definition Search_push_frame_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_push_frame_contract r g s v \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_push_frame_spec:
  shows \<open>\<Gamma>; Search_push_frame r v \<Turnstile>\<^sub>F Search_push_frame_contract r g s v\<close>
  apply (crush_boot f: Search_push_frame_def contract: Search_push_frame_contract_def)
  apply (crush_base inline: BIG_def ACT_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition Search_redundant_step_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_redundant_step_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_redundant_step_spec:
  shows \<open>\<Gamma>; Search_redundant_step r \<Turnstile>\<^sub>F Search_redundant_step_contract r g s\<close>
  apply (crush_boot f: Search_redundant_step_def contract: Search_redundant_step_contract_def)
  apply (crush_base inline: BIG_def ACT_def NONE_def
      specs add: Search_push_frame_spec contracts add: Search_push_frame_contract_def
      simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition Search_unwind_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_unwind_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_unwind_spec:
  shows \<open>\<Gamma>; Search_unwind r \<Turnstile>\<^sub>F Search_unwind_contract r g s\<close>
  apply (crush_boot f: Search_unwind_def contract: Search_unwind_contract_def)
  apply (crush_base inline: BIG_def ACT_def NONE_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  subgoal for k_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gk kk. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> \<langle>sok_in s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gk kk. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star>
               \<langle>sok_in s' \<and> kk < word64_of_nat (rvec_length (Search_stack s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: BIG_def ACT_def NONE_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_lit_redundant_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>Search_lit_redundant_contract r g s v \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_lit_redundant_spec:
  shows \<open>\<Gamma>; Search_lit_redundant r v \<Turnstile>\<^sub>F Search_lit_redundant_contract r g s v\<close>
  apply (crush_boot f: Search_lit_redundant_def contract: Search_lit_redundant_contract_def)
  apply (crush_base inline: BIG_def ACT_def NONE_def
      specs add: Search_push_frame_spec contracts add: Search_push_frame_contract_def
      simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>(erule word64_not_le_of_nat)?\<close>)
  apply (ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>k. can_alloc_reference \<star> (\<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> \<langle>sok_in s'\<rangle>)\<close> and
      INV'=\<open>\<lambda>k. can_alloc_reference \<star> (\<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> \<langle>sok_in s'\<rangle>)\<close> and
      \<tau>=\<open>\<lambda>_. can_alloc_reference \<star> (\<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> \<langle>sok s'\<rangle>)\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>)
  apply (crush_base inline: BIG_def ACT_def NONE_def
      specs add: Search_redundant_step_spec Search_unwind_spec
      contracts add: Search_redundant_step_contract_def Search_unwind_contract_def
      simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition Search_compact_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_compact_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_compact_spec:
  shows \<open>\<Gamma>; Search_compact r \<Turnstile>\<^sub>F Search_compact_contract r g s\<close>
  apply (crush_boot f: Search_compact_def contract: Search_compact_contract_def)
  apply (crush_base inline: BIG_def ACT_def slice_swap_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  subgoal for i_ref j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gi i gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star> \<langle>sok_in s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gi i gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>sok_in s' \<and> j < word64_of_nat (rvec_length (Search_learnt s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: BIG_def ACT_def slice_swap_def specs add: Search_lit_redundant_spec
        contracts add: Search_lit_redundant_contract_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    apply (all \<open>(rule FalseE, rule swap_ok2; assumption)?\<close>)
    done
  done

definition Search_clear_marks_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_clear_marks_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_clear_marks_spec:
  shows \<open>\<Gamma>; Search_clear_marks r \<Turnstile>\<^sub>F Search_clear_marks_contract r g s\<close>
  apply (crush_boot f: Search_clear_marks_def contract: Search_clear_marks_contract_def)
  apply (crush_base inline: BIG_def ACT_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  subgoal for k_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gk kk. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> \<langle>sok_in s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gk kk. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star>
               \<langle>sok_in s' \<and> kk < word64_of_nat (rvec_length (Search_toclear s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: BIG_def ACT_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_minimize_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_minimize_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_minimize_spec:
  shows \<open>\<Gamma>; Search_minimize r \<Turnstile>\<^sub>F Search_minimize_contract r g s\<close>
  apply (crush_boot f: Search_minimize_def contract: Search_minimize_contract_def)
  apply (crush_base inline: BIG_def ACT_def specs add: Search_learnt_lbd_spec Search_compact_spec Search_clear_marks_spec
        Search_unmark_from_spec
      contracts add: Search_learnt_lbd_contract_def Search_compact_contract_def
        Search_clear_marks_contract_def Search_unmark_from_contract_def
      simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

section \<open>Conflict analysis\<close>

text \<open>\<^verbatim>\<open>analyze\<close> clears \<^verbatim>\<open>learnt\<close> and pushes one literal.\<close>
lemma vok_clear_push:
  assumes \<open>vok l v\<close> \<open>288230376151711760 \<le> rvec_cap_max l\<close>
  shows \<open>\<exists>y. rvec_append_val (update_rvec_elems (\<lambda>_. []) v) [x] = Some y\<close>
    \<open>vok l (the (rvec_append_val (update_rvec_elems (\<lambda>_. []) v) [x]))\<close>
proof -
  have c: \<open>vok l (update_rvec_elems (\<lambda>_. []) v)\<close>
    using assms(1) by (rule vok_update) simp
  show \<open>\<exists>y. rvec_append_val (update_rvec_elems (\<lambda>_. []) v) [x] = Some y\<close>
    \<open>vok l (the (rvec_append_val (update_rvec_elems (\<lambda>_. []) v) [x]))\<close>
    using push_ok(1,2)[OF c _ assms(2), of \<open>[x]\<close>] by simp_all
qed

lemma sok_learnt_reset:
  assumes \<open>sok_in s\<close>
  shows \<open>sok_in (update_Search_learnt
    (\<lambda>a. the (rvec_append_val (update_rvec_elems (\<lambda>_. []) (Search_learnt s)) [x]))
    (update_Search_hint (\<lambda>_. update_rvec_elems (\<lambda>_. []) (Search_hint s)) s))\<close>
proof -
  have l: \<open>vok L16 (Search_learnt s)\<close> and h: \<open>vok L8 (Search_hint s)\<close>
    using assms unfolding sok_in_def sok_def by simp_all
  have \<open>vok L16 (the (rvec_append_val (update_rvec_elems (\<lambda>_. []) (Search_learnt s)) [x]))\<close>
    using l by (rule vok_clear_push(2)[OF _ cap_max_big(3)])
  moreover have \<open>vok L8 (update_rvec_elems (\<lambda>_. []) (Search_hint s))\<close>
    using h by (rule vok_update) simp
  ultimately show ?thesis
    using assms unfolding sok_in_def sok_def by simp
qed



definition Search_analyze_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause rvec \<Rightarrow> 64 word \<Rightarrow> ('s, Lit rvec, 'abort) function_contract\<close> where
  \<open>Search_analyze_contract r g s f L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s \<and> db_small f L\<rangle> in
     let post = \<lambda>res. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) \<star>
        \<langle>rvec_length res \<le> 4611686018427387904\<rangle> in
     make_function_contract pre post\<close>

lemma Search_analyze_spec:
  shows \<open>\<Gamma>; Search_analyze r f L c \<Turnstile>\<^sub>F Search_analyze_contract r g s f L c\<close>
  apply (crush_boot f: Search_analyze_def contract: Search_analyze_contract_def)
  apply (crush_base inline: ACT_def NONE_def BIG_def Lit_mk_def
      simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  apply (all \<open>(erule sok_learnt_reset; fail)?\<close>)
  apply (all \<open>(auto simp add: sok_def sok_in_def vok_clear_push cap_max_big; fail)?\<close>)
  subgoal for counter_ref p_ref idx_ref c_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gc cn gp p gi i gcc cc. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               counter_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> idx_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               c_ref \<mapsto>\<langle>\<top>\<rangle> gcc\<down>cc \<star> can_alloc_reference \<star> \<langle>sok_in s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gc cn gp p gi i gcc cc. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               counter_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> idx_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               c_ref \<mapsto>\<langle>\<top>\<rangle> gcc\<down>cc \<star> can_alloc_reference \<star> \<langle>sok_in s'\<rangle>\<close> and
        BRK=\<open>\<lambda>k. \<Squnion>gs s' gc cn gp p gi i gcc cc. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               counter_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> idx_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               c_ref \<mapsto>\<langle>\<top>\<rangle> gcc\<down>cc \<star> can_alloc_reference \<star> \<langle>sok_in s'\<rangle>\<close> and
        \<tau>=\<open>\<lambda>res. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) \<star>
               \<langle>rvec_length res \<le> 4611686018427387904\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: ACT_def NONE_def BIG_def Lit_mk_def
        specs add: Search_analyze_clause_spec Search_prev_seen_spec Search_finish_learnt_spec
          Search_copy_learnt_spec Search_minimize_spec
        contracts add: Search_analyze_clause_contract_def Search_prev_seen_contract_def
          Search_finish_learnt_contract_def Search_copy_learnt_contract_def Search_minimize_contract_def
        simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    apply (all \<open>(erule sok_learnt_reset)?\<close>)
    done
  done

end

end
