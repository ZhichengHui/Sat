theory Trial_Rvec
  imports Sat.Sat_Funs
begin

context Sat_ctx
begin

text \<open>Missing in AutoCorrode: modify through the focus on the elements.\<close>
lemma rvec_elems_focus_modify [simp]:
  shows \<open>\<nabla>{rvec_elems_focus} f v = update_rvec_elems f v\<close>
  by (simp add: focus_modify_def' focus_components rvec.expand)

definition updated_contract :: \<open>bool rvec \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> ('s, bool rvec, 'abort) function_contract\<close> where
  \<open>updated_contract xs i x \<equiv>
     let pre = can_alloc_reference \<star> \<langle>unat i < rvec_length xs\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = update_rvec_elems (\<lambda>ys. ys[unat i := x]) xs\<rangle> in
     make_function_contract pre post\<close>

lemma updated_spec:
  shows \<open>\<Gamma>; updated xs i x \<Turnstile>\<^sub>F updated_contract xs i x\<close>
  apply (crush_boot f: updated_def contract: updated_contract_def)
  apply (crush_base simp add: true_def false_def focus_components)
  done

definition copy_contract :: \<open>Pasn \<Rightarrow> ('s, Pasn, 'abort) function_contract\<close> where
  \<open>copy_contract pa \<equiv>
     let pre = can_alloc_reference in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>rvec_elems (Assignments_v0 (Pasn_assign r)) = rvec_elems (Assignments_v0 (Pasn_assign pa)) \<and>
         rvec_elems (Pasn_set r) = rvec_elems (Pasn_set pa)\<rangle> in
     make_function_contract pre post\<close>

lemma copy_spec:
  shows \<open>\<Gamma>; copy pa \<Turnstile>\<^sub>F copy_contract pa\<close>
  apply (crush_boot f: copy_def contract: copy_contract_def)
  apply (crush_base inline: Pasn_mk_def Assignments_mk_def simp add: rvec_clone_val_def)
  done

definition key_contract :: \<open>64 word \<Rightarrow> bool \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>key_contract v b \<equiv>
     let pre = can_alloc_reference in
     let post = \<lambda>r. can_alloc_reference in
     make_function_contract pre post\<close>

lemma key_spec:
  shows \<open>\<Gamma>; key v b \<Turnstile>\<^sub>F key_contract v b\<close>
  apply (crush_boot f: key_def contract: key_contract_def)
  apply (crush_base inline: BIG_def NONE_def simp add: true_def false_def)
  apply (auto simp add: word_less_nat_alt unat_word_ariths)
  done

text \<open>The old weak contract of enqueue (no invariant on the state).\<close>
definition Search_enqueue_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_enqueue_contract r g s v b c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_enqueue_spec:
  shows \<open>\<Gamma>; Search_enqueue r v b c \<Turnstile>\<^sub>F Search_enqueue_contract r g s v b c\<close>
  apply (crush_boot f: Search_enqueue_def contract: Search_enqueue_contract_def)
  apply (crush_base inline: NONE_def BIG_def Lit_mk_def
      specs add: key_spec contracts add: key_contract_def simp add: true_def false_def)
  \<comment> \<open>leaves \<open>\<exists>y. rvec_append_val (Search_trail s) [v] = Some y\<close>: unprovable without an invariant\<close>
  oops

text \<open>With a capacity invariant on the trail.\<close>
definition Search_enqueue_contract2 :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_enqueue_contract2 r g s v b c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star>
        \<langle>rvec_wf (Search_trail s) \<and> 2 * rvec_length (Search_trail s) + 8 \<le> rvec_cap_max (rvec_layout (Search_trail s))\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma push_ok:
  assumes \<open>rvec_wf v\<close> and \<open>2 * rvec_length v + 8 \<le> rvec_cap_max (rvec_layout v)\<close>
  shows \<open>rvec_append_val v [x] \<noteq> None\<close>
  using assms rvec_reserve_val_not_None[of v 1]
  by (cases \<open>rvec_length v + 1 \<le> rvec_cap v\<close>)
     (auto simp add: rvec_append_val_def rvec_min_non_zero_cap_def)

lemma push_ok':
  assumes \<open>rvec_wf v\<close> and \<open>2 * rvec_length v + 8 \<le> rvec_cap_max (rvec_layout v)\<close>
  shows \<open>\<exists>y. rvec_append_val v [x] = Some y\<close>
  using push_ok[OF assms] by auto

lemma word64_less_of_nat:
  \<open>(x :: 64 word) < word64_of_nat n \<Longrightarrow> unat x < n\<close>
  by (metis le_unat_uoi linorder_not_le nat_less_le order_le_less_trans unat_mono word_less_nat_alt)

lemma Search_enqueue_spec2:
  shows \<open>\<Gamma>; Search_enqueue r v b c \<Turnstile>\<^sub>F Search_enqueue_contract2 r g s v b c\<close>
  apply (crush_boot f: Search_enqueue_def contract: Search_enqueue_contract2_def)
  apply (crush_base inline: NONE_def BIG_def Lit_mk_def
      specs add: key_spec contracts add: key_contract_def simp add: true_def false_def push_ok)
  apply (auto intro!: push_ok' word64_less_of_nat)
  done

end

end
