theory Sat_Level0
  imports Sat_Proof.Sat_Reduce
begin

text \<open>The contracts of the hint of level 0 of \<^verbatim>\<open>core/src/lib.rs\<close> (\<^verbatim>\<open>level0_hint\<close>): the
  variables of level 0 whose reasons \<^verbatim>\<open>certify\<close> checks. As in \<^verbatim>\<open>Sat_Search\<close>, they only need to
  return without a panic: the hint is untrusted, and \<^verbatim>\<open>certify\<close> checks every reason it uses.\<close>

context Sat_ctx
begin

text \<open>The invariant after an update of \<open>hint0\<close>, as \<open>sok_elems\<close> and \<open>sok_push\<close> of
  \<^verbatim>\<open>Sat_Minimize\<close> for the other lists.\<close>
lemma sok_hint0:
  assumes \<open>sok s\<close>
  shows \<open>length (g1 (rvec_elems (Search_hint0 s))) \<le> rvec_length (Search_hint0 s) \<Longrightarrow>
      sok (update_Search_hint0 (update_rvec_elems g1) s)\<close>
    \<open>Search_hint0 s = v2 \<Longrightarrow> length (g2 (rvec_elems v2)) \<le> rvec_length v2 \<Longrightarrow>
      sok (update_Search_hint0 (\<lambda>_. update_rvec_elems g2 v2) s)\<close>
    \<open>Search_hint0 s = v \<Longrightarrow> word64_of_nat (rvec_length v) < (0x100000000000000 :: 64 word) \<Longrightarrow>
      length xs \<le> 8 \<Longrightarrow> sok (update_Search_hint0 (\<lambda>_. the (rvec_append_val v xs)) s)\<close>
    \<open>word64_of_nat (rvec_length (Search_hint0 s)) < (0x100000000000000 :: 64 word) \<Longrightarrow>
      length xs \<le> 8 \<Longrightarrow> \<exists>y. rvec_append_val (Search_hint0 s) xs = Some y\<close>
  using assms by (auto simp add: sok_def cap_max_big push_ok intro!: vok_update)

text \<open>\<open>sok_fast\<close> with the rules of \<open>hint0\<close>.\<close>
method sok0 =
  ((match conclusion in \<open>sok_in _\<close> \<Rightarrow> succeed \<bar> \<open>sok _\<close> \<Rightarrow> succeed \<bar>
     \<open>\<exists>y. rvec_append_val _ _ = Some y\<close> \<Rightarrow> succeed),
   (unfold sok_in_def)?, ((rule sok_frame sok_elems sok_push sok_hint0)+)?,
   (sok_asm | (simp (no_asm); fail) | (simp add: not_le; fail))+)

definition Search_frame0_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_frame0_contract r g s v c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_frame0_spec:
  shows \<open>\<Gamma>; Search_frame0 r v c \<Turnstile>\<^sub>F Search_frame0_contract r g s v c\<close>
  apply (crush_boot f: Search_frame0_def contract: Search_frame0_contract_def)
  apply (crush_base inline: BIG_def simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>(sok0; fail)?\<close>)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition Search_step0_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_step0_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_step0_spec:
  shows \<open>\<Gamma>; Search_step0 r \<Turnstile>\<^sub>F Search_step0_contract r g s\<close>
  apply (crush_boot f: Search_step0_def contract: Search_step0_contract_def)
  apply (crush_base inline: BIG_def NONE_def
      specs add: Search_frame0_spec contracts add: Search_frame0_contract_def
      simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>(sok0; fail)?\<close>)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition Search_close0_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_close0_contract r g s c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_close0_spec:
  shows \<open>\<Gamma>; Search_close0 r c \<Turnstile>\<^sub>F Search_close0_contract r g s c\<close>
  apply (crush_boot f: Search_close0_def contract: Search_close0_contract_def)
  apply (crush_base inline: BIG_def NONE_def
      specs add: Search_frame0_spec contracts add: Search_frame0_contract_def
      simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>(sok0; fail)?\<close>)
  apply (ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>k. can_alloc_reference \<star> (\<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> \<langle>sok_in s'\<rangle>)\<close> and
      INV'=\<open>\<lambda>k. can_alloc_reference \<star> (\<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> \<langle>sok_in s'\<rangle>)\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>)
  apply (crush_base inline: BIG_def NONE_def
      specs add: Search_step0_spec contracts add: Search_step0_contract_def
      simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>(sok0; fail)?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition Search_unmark0_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_unmark0_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_unmark0_spec:
  shows \<open>\<Gamma>; Search_unmark0 r \<Turnstile>\<^sub>F Search_unmark0_contract r g s\<close>
  apply (crush_boot f: Search_unmark0_def contract: Search_unmark0_contract_def)
  apply (crush_base simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>(sok0; fail)?\<close>)
  subgoal for k_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gk kk. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> \<langle>sok_in s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gk kk. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star>
               \<langle>sok_in s' \<and> kk < word64_of_nat (rvec_length (Search_hint0 s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
    apply (all \<open>(sok0; fail)?\<close>)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_close_hint_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_close_hint_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_close_hint_spec:
  shows \<open>\<Gamma>; Search_close_hint r \<Turnstile>\<^sub>F Search_close_hint_contract r g s\<close>
  apply (crush_boot f: Search_close_hint_def contract: Search_close_hint_contract_def)
  apply (crush_base simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>(sok0; fail)?\<close>)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star> \<langle>sok_in s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>sok_in s' \<and> i < word64_of_nat (rvec_length (Search_hint s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base specs add: Search_close0_spec contracts add: Search_close0_contract_def
        simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
    apply (all \<open>(sok0; fail)?\<close>)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_level0_hint_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_level0_hint_contract r g s c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_level0_hint_spec:
  shows \<open>\<Gamma>; Search_level0_hint r c \<Turnstile>\<^sub>F Search_level0_hint_contract r g s c\<close>
  apply (crush_boot f: Search_level0_hint_def contract: Search_level0_hint_contract_def)
  apply (crush_base specs add: Search_close0_spec Search_close_hint_spec Search_unmark0_spec
      contracts add: Search_close0_contract_def Search_close_hint_contract_def Search_unmark0_contract_def
      simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>(sok0; fail)?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

end

end
