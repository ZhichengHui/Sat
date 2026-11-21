theory Sat_Reduce
  imports Sat_Proof.Sat_Minimize
begin

text \<open>The contracts of the functions of the CDCL search of \<^verbatim>\<open>core/src/lib.rs\<close> that delete learned
  clauses and decide restarts. Like the rest of the search (\<^verbatim>\<open>Sat_Search\<close>), they only need to
  return without a panic.\<close>

context Sat_ctx
begin

section \<open>Deletion of learned clauses\<close>

definition Search_count_live_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_count_live_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_count_live_spec:
  shows \<open>\<Gamma>; Search_count_live r \<Turnstile>\<^sub>F Search_count_live_contract r g s\<close>
  apply (crush_boot f: Search_count_live_def contract: Search_count_live_contract_def)
  apply (crush_base inline: NONE_def BIG_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  subgoal for live_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gl l gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               live_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star> \<langle>sok_in s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gl l gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               live_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>sok_in s' \<and> i < word64_of_nat (rvec_length (Search_lbd s')) \<and> i < word64_of_nat (rvec_length (Search_dead s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: BIG_def ACT_def NONE_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_cut_contract :: \<open>Search \<Rightarrow> 64 word \<Rightarrow> ('s, Cut, 'abort) function_contract\<close> where
  \<open>Search_cut_contract s live \<equiv> make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma Search_cut_spec:
  shows \<open>\<Gamma>; Search_cut s live \<Turnstile>\<^sub>F Search_cut_contract s live\<close>
  apply (crush_boot f: Search_cut_def contract: Search_cut_contract_def)
  apply (crush_base inline: BIG_def ACT_def Cut_mk_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  subgoal for left_ref t_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gl l gt t. left_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gl l gt t. left_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t \<star> can_alloc_reference \<star>
               \<langle>3 < t \<and> t - 1 < word64_of_nat (rvec_length (Search_hist s)) \<and>
                rvec_elems (Search_hist s) ! unat (t - 1) \<le> l\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. can_alloc_reference\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: BIG_def ACT_def Cut_mk_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_unwatch_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_unwatch_contract r g s m i \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_unwatch_spec:
  shows \<open>\<Gamma>; Search_unwatch r m i \<Turnstile>\<^sub>F Search_unwatch_contract r g s m i\<close>
  apply (crush_boot f: Search_unwatch_def contract: Search_unwatch_contract_def)
  apply (crush_base inline: NONE_def BIG_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition Search_kill_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_kill_contract r g s m t left \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_kill_spec:
  shows \<open>\<Gamma>; Search_kill r m t left \<Turnstile>\<^sub>F Search_kill_contract r g s m t left\<close>
  apply (crush_boot f: Search_kill_def contract: Search_kill_contract_def)
  apply (crush_base inline: BIG_def ACT_def specs add: Search_unwatch_spec
      contracts add: Search_unwatch_contract_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  subgoal for left_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gl l gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               left_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star> \<langle>sok_in s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gl l gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               left_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>sok_in s' \<and> i < word64_of_nat (rvec_length (Search_lbd s')) \<and> i < word64_of_nat (rvec_length (Search_dead s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: BIG_def ACT_def specs add: Search_unwatch_spec
        contracts add: Search_unwatch_contract_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_reduce_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_reduce_contract r g s m \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_reduce_spec:
  shows \<open>\<Gamma>; Search_reduce r m \<Turnstile>\<^sub>F Search_reduce_contract r g s m\<close>
  apply (crush_boot f: Search_reduce_def contract: Search_reduce_contract_def)
  apply (crush_base inline: BIG_def ACT_def specs add: Search_count_live_spec Search_cut_spec Search_kill_spec
      contracts add: Search_count_live_contract_def Search_cut_contract_def Search_kill_contract_def
      simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

section \<open>Restarts\<close>

text \<open>The moving averages of the literal block distances, scaled by \<open>2^16\<close>, stay below \<open>2^64\<close>
  because \<^verbatim>\<open>restart_due\<close> checks the range of every operand; the word lemmas below are the
  bounds that \<open>crush_base inline: BIG_def ACT_def\<close> leaves.\<close>

lemma restart_avg:
  assumes \<open>\<not> 0x20000000000 \<le> (a :: 64 word)\<close>
  shows \<open>unat (a * 0x10000 div n) * 5 < 18446744073709551616\<close>
  using assms div_le_dividend[of \<open>unat a * 65536\<close> \<open>unat n\<close>]
  by (simp add: word_le_nat_alt unat_div unat_word_ariths, linarith)

lemma restart_avg2:
  \<open>\<not> 0x20000000000 \<le> (a :: 64 word) + l \<Longrightarrow>
    unat ((a * 0x10000 + l * 0x10000) div n) * 5 < 18446744073709551616\<close>
  using restart_avg[of \<open>a + l\<close> n] by (simp add: distrib_right)

lemma restart_lt:
  \<open>unat (x :: 64 word) < 18446744073709551616\<close>
  using unat_lt2p[of x] by simp

lemma restart_div_le:
  \<open>(x :: 64 word) div 0x20 \<le> x\<close>
  by (simp add: word_le_nat_alt unat_div)

lemma restart_add:
  assumes \<open>(f :: 64 word) < 0x1000000000\<close> and \<open>(l :: 64 word) < 0x100000\<close>
  shows \<open>unat (f - f div 0x20) + unat (l * 0x800) < 18446744073709551616\<close>
  using assms by (simp add: word_less_nat_alt word_le_nat_alt unat_sub unat_div unat_word_ariths)

text \<open>The other bounds of \<^verbatim>\<open>restart_due\<close> close by the simplifier in \<open>search_bound\<close>.\<close>
method restart_bound =
  (rule restart_div_le restart_lt | (rule restart_avg restart_avg2 restart_add; assumption))

definition Search_restart_due_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, bool, 'abort) function_contract\<close> where
  \<open>Search_restart_due_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_restart_due_spec:
  shows \<open>\<Gamma>; Search_restart_due r \<Turnstile>\<^sub>F Search_restart_due_contract r g s\<close>
  apply (crush_boot f: Search_restart_due_def contract: Search_restart_due_contract_def)
  apply (crush_base inline: BIG_def ACT_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>restart_bound?\<close>)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

end

end
