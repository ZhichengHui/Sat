theory Sat_Minimize
  imports Sat_Proof.Sat_Search
begin

text \<open>The contracts of the conflict analysis of the CDCL search of \<^verbatim>\<open>core/src/lib.rs\<close> and of its
  recursive minimisation of the learned clause. As in \<^verbatim>\<open>Sat_Search\<close>, they only need to return
  without a panic: the learned clause is checked by \<^verbatim>\<open>certify\<close>.\<close>

section \<open>Words of the minimisation\<close>

text \<open>The frames of the search stack are three words; the top frame is read below its length.\<close>
lemma len_minus:
  assumes \<open>\<not> word64_of_nat n < (3 :: 64 word)\<close> \<open>(1 :: 64 word) \<le> k\<close> \<open>k \<le> 3\<close>
  shows \<open>unat (word64_of_nat n - k) < n\<close>
proof -
  have le: \<open>k \<le> word64_of_nat n\<close>
    using assms by simp
  then have \<open>unat k \<le> unat (word64_of_nat n :: 64 word)\<close>
    by (simp add: word_le_nat_alt)
  moreover have \<open>unat (word64_of_nat n :: 64 word) \<le> n\<close>
    by (simp add: unat_of_nat)
  moreover have \<open>0 < unat k\<close>
    using assms(2) by (simp add: word_le_nat_alt)
  moreover have \<open>unat (word64_of_nat n - k) = unat (word64_of_nat n :: 64 word) - unat k\<close>
    using le by (rule unat_sub)
  ultimately show ?thesis
    by linarith
qed

lemma succ_less:
  \<open>(j :: 64 word) < x \<Longrightarrow> unat (j + 1) = Suc (unat j)\<close>
  using word64_less_max[of j x] unat_word_Suc_simp[of j] by simp

method minimize_bound =
  ((rule len_minus; simp) | (rule succ_less; assumption) | (erule succ_less) | erule not_le_max |
    search_bound | arena_bound)

context Sat_ctx
begin

section \<open>Recursive minimisation\<close>

definition Search_push_frame_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_push_frame_contract r g s v \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_push_frame_spec:
  shows \<open>\<Gamma>; Search_push_frame r v \<Turnstile>\<^sub>F Search_push_frame_contract r g s v\<close>
  apply (crush_boot f: Search_push_frame_def contract: Search_push_frame_contract_def)
  apply (crush_base inline: len_def BIG_def vec_push_def simp add: true_def false_def)
  apply (all \<open>minimize_bound?\<close>)
  done

definition Search_redundant_step_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_redundant_step_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_redundant_step_spec:
  shows \<open>\<Gamma>; Search_redundant_step r \<Turnstile>\<^sub>F Search_redundant_step_contract r g s\<close>
  apply (crush_boot f: Search_redundant_step_def contract: Search_redundant_step_contract_def)
  apply (crush_base inline: len_def NONE_def vec_push_def vec_truncate_def
      specs add: Search_push_frame_spec contracts add: Search_push_frame_contract_def
      simp add: true_def false_def)
  apply (all \<open>minimize_bound?\<close>)
  done

definition Search_unwind_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_unwind_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_unwind_spec:
  shows \<open>\<Gamma>; Search_unwind r \<Turnstile>\<^sub>F Search_unwind_contract r g s\<close>
  apply (crush_boot f: Search_unwind_def contract: Search_unwind_contract_def)
  apply (crush_base inline: len_def NONE_def vec_clear_def simp add: true_def false_def)
  subgoal for k_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gk kk. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gk kk. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star>
               \<langle>kk < word64_of_nat (length (Search_stack s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def NONE_def vec_clear_def simp add: true_def false_def)
    apply (all \<open>minimize_bound?\<close>)
    done
  done

definition Search_lit_redundant_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>Search_lit_redundant_contract r g s v \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_lit_redundant_spec:
  shows \<open>\<Gamma>; Search_lit_redundant r v \<Turnstile>\<^sub>F Search_lit_redundant_contract r g s v\<close>
  apply (crush_boot f: Search_lit_redundant_def contract: Search_lit_redundant_contract_def)
  apply (crush_base inline: len_def NONE_def vec_clear_def
      specs add: Search_push_frame_spec contracts add: Search_push_frame_contract_def
      simp add: true_def false_def)
  apply (all \<open>(erule word64_not_le_of_nat)?\<close>)
  apply (ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>k. can_alloc_reference \<star> (\<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s')\<close> and
      INV'=\<open>\<lambda>k. can_alloc_reference \<star> (\<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s')\<close> and
      \<tau>=\<open>\<lambda>_. can_alloc_reference \<star> (\<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s')\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>)
  apply (crush_base inline: len_def NONE_def
      specs add: Search_redundant_step_spec Search_unwind_spec
      contracts add: Search_redundant_step_contract_def Search_unwind_contract_def
      simp add: true_def false_def)
  apply (all \<open>minimize_bound?\<close>)
  done

definition Search_compact_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_compact_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_compact_spec:
  shows \<open>\<Gamma>; Search_compact r \<Turnstile>\<^sub>F Search_compact_contract r g s\<close>
  apply (crush_boot f: Search_compact_def contract: Search_compact_contract_def)
  apply (crush_base inline: len_def slice_swap_def simp add: true_def false_def)
  subgoal for i_ref j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gi i gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gi i gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>j < word64_of_nat (length (Search_learnt s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def slice_swap_def specs add: Search_lit_redundant_spec
        contracts add: Search_lit_redundant_contract_def simp add: true_def false_def)
    apply (all \<open>minimize_bound?\<close>)
    apply (all \<open>(rule FalseE, rule swap_ok2; assumption)?\<close>)
    done
  done

definition Search_clear_marks_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_clear_marks_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_clear_marks_spec:
  shows \<open>\<Gamma>; Search_clear_marks r \<Turnstile>\<^sub>F Search_clear_marks_contract r g s\<close>
  apply (crush_boot f: Search_clear_marks_def contract: Search_clear_marks_contract_def)
  apply (crush_base inline: len_def vec_clear_def simp add: true_def false_def)
  subgoal for k_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gk kk. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gk kk. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star>
               \<langle>kk < word64_of_nat (length (Search_toclear s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def vec_clear_def simp add: true_def false_def)
    apply (all \<open>minimize_bound?\<close>)
    done
  done

definition Search_minimize_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_minimize_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_minimize_spec:
  shows \<open>\<Gamma>; Search_minimize r \<Turnstile>\<^sub>F Search_minimize_contract r g s\<close>
  apply (crush_boot f: Search_minimize_def contract: Search_minimize_contract_def)
  apply (crush_base inline: vec_truncate_def
      specs add: Search_learnt_lbd_spec Search_compact_spec Search_clear_marks_spec
        Search_unmark_from_spec
      contracts add: Search_learnt_lbd_contract_def Search_compact_contract_def
        Search_clear_marks_contract_def Search_unmark_from_contract_def
      simp add: true_def false_def)
  done

section \<open>Conflict analysis\<close>

definition Search_analyze_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> ('s, Lit list, 'abort) function_contract\<close> where
  \<open>Search_analyze_contract r g s f L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>res. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') \<star>
        \<langle>length res \<le> 4611686018427387904\<rangle> in
     make_function_contract pre post\<close>

lemma Search_analyze_spec:
  shows \<open>\<Gamma>; Search_analyze r f L c \<Turnstile>\<^sub>F Search_analyze_contract r g s f L c\<close>
  apply (crush_boot f: Search_analyze_def contract: Search_analyze_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def vec_push_def vec_clear_def Lit_mk_def
      simp add: true_def false_def)
  subgoal for counter_ref p_ref idx_ref c_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gc cn gp p gi i gcc cc. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               counter_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> idx_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               c_ref \<mapsto>\<langle>\<top>\<rangle> gcc\<down>cc \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gc cn gp p gi i gcc cc. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               counter_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> idx_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               c_ref \<mapsto>\<langle>\<top>\<rangle> gcc\<down>cc \<star> can_alloc_reference\<close> and
        BRK=\<open>\<lambda>k. \<Squnion>gs s' gc cn gp p gi i gcc cc. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               counter_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cn \<star> p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> idx_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
               c_ref \<mapsto>\<langle>\<top>\<rangle> gcc\<down>cc \<star> can_alloc_reference\<close> and
        \<tau>=\<open>\<lambda>res. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') \<star>
               \<langle>length res \<le> 4611686018427387904\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def NONE_def BIG_def Lit_mk_def
        specs add: Search_analyze_clause_spec Search_prev_seen_spec Search_finish_learnt_spec
          Search_copy_learnt_spec Search_minimize_spec
        contracts add: Search_analyze_clause_contract_def Search_prev_seen_contract_def
          Search_finish_learnt_contract_def Search_copy_learnt_contract_def Search_minimize_contract_def
        simp add: true_def false_def)
    apply (all \<open>search_bound?\<close>)
    done
  done

end

end
