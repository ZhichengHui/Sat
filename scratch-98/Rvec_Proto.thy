(* Scratch prototype for #98 (session 67db04ed), not for merge: the capacity invariant `sok` of the
   search under the rvec model. Checked by `isabelle build` of scratch-98/ROOT on top of the
   regenerated urust/ (session Sat): everything up to Search_attach_spec builds; attach ends in a
   sorry (see there). *)
theory Rvec_Proto
  imports Sat.Sat_Funs
begin

section \<open>Vectors that may grow\<close>

text \<open>A vector of the layout \<open>l\<close> that is well-formed. Its length is then below \<open>2^64\<close>,
  so \<^verbatim>\<open>len()\<close> is exact, and a vector shorter than \<open>2^57\<close> of a layout whose largest
  capacity is at least \<open>2^58 + 16\<close> grows by up to eight elements without a capacity overflow.\<close>
definition vok :: \<open>elem_layout \<Rightarrow> 'v rvec \<Rightarrow> bool\<close> where
  \<open>vok l v \<equiv> rvec_wf v \<and> rvec_layout v = l\<close>

abbreviation L1 :: elem_layout where \<open>L1 \<equiv> make_elem_layout 1 1\<close>
abbreviation L8 :: elem_layout where \<open>L8 \<equiv> make_elem_layout 8 8\<close>
abbreviation L16 :: elem_layout where \<open>L16 \<equiv> make_elem_layout 16 8\<close>
abbreviation L24 :: elem_layout where \<open>L24 \<equiv> make_elem_layout 24 8\<close>

lemma cap_max_big:
  \<open>288230376151711760 \<le> rvec_cap_max L1\<close> \<open>288230376151711760 \<le> rvec_cap_max L8\<close>
  \<open>288230376151711760 \<le> rvec_cap_max L16\<close> \<open>288230376151711760 \<le> rvec_cap_max L24\<close>
  by (simp_all add: rvec_cap_max_def isize_max_def)

lemma vok_len:
  assumes \<open>vok l v\<close>
  shows \<open>unat (word64_of_nat (rvec_length v)) = rvec_length v\<close>
  using assms rvec_len_unat(1)[of v] by (simp add: vok_def)

lemma vok_append:
  assumes \<open>vok l v\<close> \<open>rvec_length v < 144115188075855872\<close> \<open>length xs \<le> 8\<close>
    \<open>288230376151711760 \<le> rvec_cap_max l\<close>
  shows \<open>rvec_append_val v xs \<noteq> None\<close>
    \<open>vok l (the (rvec_append_val v xs))\<close>
    \<open>rvec_elems (the (rvec_append_val v xs)) = rvec_elems v @ xs\<close>
proof -
  have wf: \<open>rvec_wf v\<close> and lay: \<open>rvec_layout v = l\<close>
    using assms(1) by (auto simp add: vok_def)
  have \<open>rvec_reserve_val v (length xs) \<noteq> None\<close>
  proof (cases \<open>rvec_length v + length xs \<le> rvec_cap v\<close>)
    case True
    then show ?thesis using rvec_reserve_val_not_None[OF wf] by blast
  next
    case False
    then have \<open>rvec_cap v < rvec_length v + 8\<close> using assms(3) by linarith
    then show ?thesis
      using rvec_reserve_val_not_None[OF wf] assms(2,3,4) lay
      by (auto simp add: rvec_min_non_zero_cap_def)
  qed
  then show ne: \<open>rvec_append_val v xs \<noteq> None\<close>
    by (simp add: rvec_append_val_None_iff)
  then obtain w where w: \<open>rvec_append_val v xs = Some w\<close> by blast
  show \<open>vok l (the (rvec_append_val v xs))\<close> \<open>rvec_elems (the (rvec_append_val v xs)) = rvec_elems v @ xs\<close>
    using rvec_append_val_Some[OF w wf] lay w by (auto simp add: vok_def)
qed

lemma vok_update:
  assumes \<open>vok l v\<close> \<open>length (f (rvec_elems v)) \<le> rvec_length v\<close>
  shows \<open>vok l (update_rvec_elems f v)\<close>
  using assms rvec_wf_update_elems by (auto simp add: vok_def)

lemma word64_less_of_nat:
  \<open>(x :: 64 word) < word64_of_nat n \<Longrightarrow> unat x < n\<close>
  by (metis le_unat_uoi linorder_not_le nat_less_le order_le_less_trans unat_mono word_less_nat_alt)

lemma vok_bound:
  assumes \<open>vok l v\<close> \<open>word64_of_nat (rvec_length v) < (0x100000000000000 :: 64 word)\<close>
  shows \<open>rvec_length v < 144115188075855872\<close>
  using assms vok_len[OF assms(1)] by (simp add: word_less_nat_alt)

lemma push_ok:
  assumes \<open>vok l v\<close> \<open>word64_of_nat (rvec_length v) < (0x100000000000000 :: 64 word)\<close>
    \<open>288230376151711760 \<le> rvec_cap_max l\<close> \<open>length xs \<le> 8\<close>
  shows \<open>\<exists>y. rvec_append_val v xs = Some y\<close> \<open>vok l (the (rvec_append_val v xs))\<close>
    \<open>rvec_elems (the (rvec_append_val v xs)) = rvec_elems v @ xs\<close>
  using vok_append[OF assms(1) vok_bound[OF assms(1,2)] assms(4,3)] by auto

lemma sub_less:
  assumes \<open>m < 2 ^ 64\<close> \<open>m \<le> unat c\<close> \<open>c - word64_of_nat m < word64_of_nat n\<close>
  shows \<open>unat c - m < n\<close>
proof -
  have \<open>word64_of_nat m \<le> c\<close>
    using assms(1,2) by (simp add: word_le_nat_alt unat_of_nat_eq)
  then have \<open>unat (c - word64_of_nat m) = unat c - m\<close>
    using assms(1) by (simp add: unat_sub unat_of_nat_eq)
  then show ?thesis
    using word64_less_of_nat[OF assms(3)] by simp
qed

lemma watch_push:
  assumes \<open>\<forall>w \<in> set ws. vok L8 w\<close> \<open>k < length ws\<close>
    \<open>word64_of_nat (rvec_length (ws ! k)) < (0x100000000000000 :: 64 word)\<close>
  shows \<open>\<exists>y. rvec_append_val (ws ! k) [x] = Some y\<close>
    \<open>\<forall>w \<in> set (ws[k := the (rvec_append_val (ws ! k) [x])]). vok L8 w\<close>
proof -
  have v: \<open>vok L8 (ws ! k)\<close> using assms(1,2) by simp
  show \<open>\<exists>y. rvec_append_val (ws ! k) [x] = Some y\<close>
    using push_ok(1)[OF v assms(3) cap_max_big(2)] by simp
  have \<open>vok L8 (the (rvec_append_val (ws ! k) [x]))\<close>
    using push_ok(2)[OF v assms(3) cap_max_big(2)] by simp
  then show \<open>\<forall>w \<in> set (ws[k := the (rvec_append_val (ws ! k) [x])]). vok L8 w\<close>
    using assms(1) set_update_subset_insert by fastforce
qed

lemma watch_push_mem:
  assumes \<open>\<forall>w \<in> set ws. vok L8 w\<close> \<open>k < word64_of_nat (length ws)\<close>
    \<open>word64_of_nat (rvec_length (ws ! unat k)) < (0x100000000000000 :: 64 word)\<close>
    \<open>x \<in> set (ws[unat k := the (rvec_append_val (ws ! unat k) [y])])\<close>
  shows \<open>vok L8 x\<close>
  using watch_push(2)[OF assms(1) word64_less_of_nat[OF assms(2)] assms(3)] assms(4) by blast

lemma arena_lt:
  assumes \<open>(a :: 64 word) < 0x100000000000000\<close> \<open>a + c < word64_of_nat m\<close> \<open>b \<le> c\<close> \<open>c \<le> 8\<close>
  shows \<open>unat (a + b) < m\<close>
proof -
  have \<open>unat (a + b) = unat a + unat b\<close> \<open>unat (a + c) = unat a + unat c\<close>
    using assms by (simp_all add: word_le_nat_alt word_less_nat_alt unat_add_lem[symmetric])
  moreover have \<open>unat b \<le> unat c\<close>
    using assms(3) by (simp add: word_le_nat_alt)
  moreover have \<open>unat (a + c) < m\<close>
    using assms(2) by (rule word64_less_of_nat)
  ultimately show ?thesis
    by simp
qed

lemma rvec_elems_focus_modify:
  shows \<open>\<nabla>{rvec_elems_focus} f v = update_rvec_elems f v\<close>
  by (simp add: focus_modify_def' focus_components rvec.expand)

context Sat_ctx
begin

text \<open>The invariant of the search state: the vectors it grows are well-formed and have the
  layouts of their element types.\<close>
definition sok :: \<open>Search \<Rightarrow> bool\<close> where
  \<open>sok s \<equiv> vok L8 (Search_trail s) \<and> vok L8 (Search_start s) \<and> vok L8 (Search_arena s) \<and>
     (\<forall>w \<in> set (rvec_elems (Search_watches s)). vok L8 w) \<and> vok L16 (Search_learnt s) \<and>
     vok L8 (Search_stack s) \<and> vok L8 (Search_toclear s) \<and> vok L8 (Search_lim s) \<and>
     vok L8 (Search_lbd s) \<and> vok L1 (Search_dead s)\<close>

definition key_contract :: \<open>64 word \<Rightarrow> bool \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>key_contract v b \<equiv> make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma key_spec:
  shows \<open>\<Gamma>; key v b \<Turnstile>\<^sub>F key_contract v b\<close>
  apply (crush_boot f: key_def contract: key_contract_def)
  apply (crush_base inline: BIG_def NONE_def simp add: true_def false_def)
  apply (auto simp add: word_less_nat_alt unat_word_ariths)
  done

definition Search_enqueue_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> bool \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_enqueue_contract r g s v b c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_enqueue_spec:
  shows \<open>\<Gamma>; Search_enqueue r v b c \<Turnstile>\<^sub>F Search_enqueue_contract r g s v b c\<close>
  apply (crush_boot f: Search_enqueue_def contract: Search_enqueue_contract_def)
  apply (crush_base inline: NONE_def BIG_def
      specs add: key_spec contracts add: key_contract_def simp add: true_def false_def)
  apply (auto simp add: sok_def cap_max_big push_ok intro: word64_less_of_nat)
  done

definition clause_len_contract :: \<open>Formula \<Rightarrow> Clause rvec \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>clause_len_contract f L c \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>rvec_length (Formula_clauses f) < 2 ^ 64\<rangle>) (\<lambda>_. can_alloc_reference)\<close>

lemma clause_len_spec:
  shows \<open>\<Gamma>; clause_len f L c \<Turnstile>\<^sub>F clause_len_contract f L c\<close>
  apply (crush_boot f: clause_len_def contract: clause_len_contract_def)
  apply (crush_base simp add: true_def false_def)
  apply (auto intro: word64_less_of_nat sub_less simp add: word_le_nat_alt not_less unat_sub unat_of_nat_eq)
  done

definition lit_at_contract :: \<open>Formula \<Rightarrow> Clause rvec \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, Lit, 'abort) function_contract\<close> where
  \<open>lit_at_contract f L c j \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>rvec_length (Formula_clauses f) < 2 ^ 64\<rangle>) (\<lambda>_. can_alloc_reference)\<close>

lemma lit_at_spec:
  shows \<open>\<Gamma>; lit_at f L c j \<Turnstile>\<^sub>F lit_at_contract f L c j\<close>
  apply (crush_boot f: lit_at_def contract: lit_at_contract_def)
  apply (crush_base inline: Lit_mk_def NONE_def simp add: true_def false_def)
  apply (auto intro: word64_less_of_nat sub_less simp add: word_le_nat_alt not_less unat_sub unat_of_nat_eq)
  done

definition Search_push_clause_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause rvec \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_push_clause_contract r g s f L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star>
        \<langle>sok s \<and> rvec_length (Formula_clauses f) < 2 ^ 64\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_push_clause_spec:
  shows \<open>\<Gamma>; Search_push_clause r f L c \<Turnstile>\<^sub>F Search_push_clause_contract r g s f L c\<close>
  apply (crush_boot f: Search_push_clause_def contract: Search_push_clause_contract_def)
  apply (crush_base inline: NONE_def BIG_def Lit_mk_def
      specs add: clause_len_spec lit_at_spec key_spec
      contracts add: clause_len_contract_def lit_at_contract_def key_contract_def
      simp add: true_def false_def)
  apply (all \<open>(auto simp add: sok_def cap_max_big push_ok word_less_nat_alt unat_word_ariths; fail)?\<close>)
  apply (rename_tac len j_ref)
  apply (ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>_. \<Squnion>gs s' gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>sok s'\<rangle>\<close> and
      INV'=\<open>\<lambda>_. \<Squnion>gs s' gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>sok s' \<and> j < len\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>)
  apply (crush_base inline: NONE_def BIG_def Lit_mk_def
      specs add: clause_len_spec lit_at_spec key_spec
      contracts add: clause_len_contract_def lit_at_contract_def key_contract_def
      simp add: true_def false_def)
  apply (auto simp add: sok_def cap_max_big push_ok word_less_nat_alt)
  done

lemma all_set_update:
  \<open>(\<forall>w \<in> set xs. P w) \<Longrightarrow> P y \<Longrightarrow> \<forall>w \<in> set (xs[k := y]). P w\<close>
  using set_update_subset_insert by fastforce

definition sok_in :: \<open>Search \<Rightarrow> bool\<close> where \<open>sok_in \<equiv> sok\<close>

definition Search_watch_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_watch_contract r g s k nd \<equiv>
     let pre = r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. \<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle> in
     make_function_contract pre post\<close>

lemma Search_watch_spec:
  shows \<open>\<Gamma>; Search_watch r k nd \<Turnstile>\<^sub>F Search_watch_contract r g s k nd\<close>
  apply (crush_boot f: Search_watch_def contract: Search_watch_contract_def)
  apply (crush_base inline: BIG_def simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>(simp add: sok_in_def)?\<close>)
  apply (auto simp add: sok_def watch_push word64_less_of_nat)
  apply (rule watch_push_mem; assumption)
  done

definition Search_attach_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause rvec \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_attach_contract r g s f L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star>
        \<langle>sok_in s \<and> rvec_length (Formula_clauses f) < 2 ^ 64\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_attach_spec:
  shows \<open>\<Gamma>; Search_attach r f L c \<Turnstile>\<^sub>F Search_attach_contract r g s f L c\<close>
  apply (crush_boot f: Search_attach_def contract: Search_attach_contract_def)
  apply (crush_base inline: NONE_def BIG_def
      specs add: Search_push_clause_spec Search_watch_spec
      contracts add: Search_push_clause_contract_def Search_watch_contract_def
      simp add: true_def false_def)
  apply (all \<open>(simp add: sok_in_def; fail)?\<close>)
  apply (auto simp add: sok_def sok_in_def rvec_elems_focus_modify word_less_nat_alt unat_word_ariths
      intro: vok_update arena_lt)
  \<comment> \<open>16 goals left: arena offsets after push_clause (\<open>unat (len + 5) < length\<close>) and \<open>sok\<close>
     of the updated state. \<open>auto simp add: vok_def rvec_len_unat rvec_wf_def\<close> did not terminate
     (> 10 min); close them one by one with arena_lt and rvec_len_unat.\<close>
  sorry
  done

end

end
