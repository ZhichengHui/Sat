theory Sat_Search
  imports Sat_Proof.Sat_Certify
begin

text \<open>The contracts of the functions of the CDCL search of \<^verbatim>\<open>core/src/lib.rs\<close> that \<^verbatim>\<open>cdcl\<close>
  calls (\<^verbatim>\<open>Sat_CDCL\<close>). The search is not trusted: its functions only need to terminate without a
  panic, which they do because every index is checked before use and every loop is bounded by the
  fuel.\<close>

section \<open>Words of the search\<close>

lemma nz_len:
  \<open>word64_of_nat n \<noteq> 0 \<Longrightarrow> 0 < n\<close>
  by (cases n) auto

lemma push_len:
  assumes \<open>length xs \<le> 4611686018427387904\<close>
    \<open>word64_of_nat (length xs) < (0x4000000000000000 :: 64 word)\<close>
  shows \<open>Suc (length xs) \<le> 4611686018427387904\<close>
proof -
  have \<open>unat (word64_of_nat (length xs)) = length xs\<close>
    using assms(1) by (simp add: unat_of_nat_eq)
  then show ?thesis
    using assms(2) by (simp add: word_less_nat_alt)
qed

lemma swap_ok:
  assumes \<open>(ra :: 64 word) < word64_of_nat n\<close> \<open>(2 :: 64 word) < word64_of_nat n\<close>
    \<open>Suc 0 < n \<longrightarrow> \<not> unat ra < n\<close>
  shows False
proof -
  have \<open>unat ra < n\<close>
    using assms(1) by (rule word64_less_of_nat)
  moreover have \<open>unat (2 :: 64 word) < n\<close>
    using assms(2) by (rule word64_less_of_nat)
  ultimately show False
    using assms(3) by simp
qed

lemma swap_ok2:
  assumes \<open>(a :: 64 word) < word64_of_nat n\<close> \<open>(b :: 64 word) < word64_of_nat n\<close>
    \<open>unat a < n \<longrightarrow> \<not> unat b < n\<close>
  shows False
  using assms word64_less_of_nat by blast

lemma push_len':
  assumes \<open>length xs \<le> 4611686018427387904\<close>
    \<open>word64_of_nat (length xs) < (0x4000000000000000 :: 64 word)\<close>
  shows \<open>length xs \<le> 4611686018427387903\<close>
  using push_len[OF assms] by simp

lemma counter_add:
  assumes \<open>\<not> 0xFFFFFFFFFFFFFFFF - c < (a :: 64 word)\<close>
  shows \<open>unat c + unat a < 18446744073709551616\<close>
proof -
  have \<open>unat a \<le> unat (0xFFFFFFFFFFFFFFFF - c)\<close>
    using assms by (simp add: word_le_nat_alt not_less)
  moreover have le: \<open>c \<le> 0xFFFFFFFFFFFFFFFF\<close>
    using unat_lt2p[of c] by (simp add: word_le_nat_alt)
  moreover have \<open>unat (0xFFFFFFFFFFFFFFFF - c) = unat (0xFFFFFFFFFFFFFFFF :: 64 word) - unat c\<close>
    using le by (rule unat_sub)
  moreover have \<open>unat c < 18446744073709551616\<close>
    using unat_lt2p[of c] by simp
  ultimately show ?thesis
    by simp
qed


lemma one_le:
  \<open>(w :: 64 word) \<noteq> 0 \<Longrightarrow> 1 \<le> w\<close>
  by (simp add: word_le_nat_alt unat_gt_0 Suc_le_eq)

lemma le_max:
  \<open>(w :: 64 word) \<le> 0xFFFFFFFFFFFFFFFF\<close>
  using unat_lt2p[of w] by (simp add: word_le_nat_alt)

lemma not_le_max:
  \<open>\<not> (y :: 64 word) \<le> x \<Longrightarrow> unat x < 18446744073709551615\<close>
  using word64_less_max not_le by blast

lemma big_succ:
  \<open>(c :: 64 word) < 0x4000000000000000 \<Longrightarrow> unat (c + 1) = Suc (unat c)\<close>
  using big_c(1)[of c] unat_word_Suc_simp[of c] by simp

lemma big_succ_le:
  \<open>(c :: 64 word) < 0x4000000000000000 \<Longrightarrow> unat (c + 1) \<le> 4611686018427387904\<close>
  using big_c(1)[of c] big_succ[of c] by simp

lemma inc_div:
  \<open>(x :: 64 word) < 0x4000000000000000 \<Longrightarrow> unat (x div 0x20) < 18446744073709551615\<close>
  using big_c(1)[of x] by (simp add: unat_div)

lemma inc_add:
  assumes \<open>(x :: 64 word) < 0x4000000000000000\<close>
  shows \<open>unat x + unat (x div 0x20 + 1) < 18446744073709551616\<close>
proof -
  have d: \<open>unat (x div 0x20) \<le> unat x\<close>
    by (simp add: unat_div)
  have \<open>unat (x div 0x20 + 1) = Suc (unat (x div 0x20))\<close>
    using big_c(1)[OF assms] d unat_word_Suc_simp[of \<open>x div 0x20\<close>] by simp
  then show ?thesis
    using big_c(1)[OF assms] d by simp
qed

lemma one_lt:
  \<open>1 < word64_of_nat n \<Longrightarrow> Suc 0 < n\<close>
  using word64_less_of_nat[of 1 n] by simp

section \<open>Bounds\<close>

text \<open>The goals that \<open>crush_base\<close> leaves in the search are bounds of words and indices. Each
  closes in one step: by the simplifier or by one of the word lemmas.\<close>

method search_bound =
  ((simp only: word64_less_of_nat; fail) | erule word64_less_max | erule len_minus_one | rule drop30 |
    (simp add: word_le_nat_alt word_less_nat_alt; fail) |
    (rule add_big; assumption) | (frule big_c(1), linarith) |
    erule nz_len | (rule push_len; assumption) | erule counter_add | (rule push_len'; assumption) |
    (rule one_le; assumption) | rule le_max | (rule big_succ; assumption) |
    (rule big_succ[symmetric]; assumption) | (rule big_succ_le; assumption) |
    (rule inc_div; assumption) | (rule inc_add; assumption) | (rule one_lt; assumption))

context Sat_ctx
begin

section \<open>The search\<close>

text \<open>The functions of the search only need to return without a panic. Those that read the state
  have the trivial postcondition; those that change it leave the reference pointing to some
  state.\<close>

definition Search_key_false_contract :: \<open>Search \<Rightarrow> 64 word \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>Search_key_false_contract s k \<equiv>
     make_function_contract (can_alloc_reference) (\<lambda>_. can_alloc_reference)\<close>

lemma Search_key_false_spec:
  shows \<open>\<Gamma>; Search_key_false s k \<Turnstile>\<^sub>F Search_key_false_contract s k\<close>
  apply (crush_boot f: Search_key_false_def contract: Search_key_false_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  apply (all \<open>search_bound\<close>)
  done

definition Search_lit_true_contract :: \<open>Search \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>Search_lit_true_contract s v b \<equiv>
     make_function_contract (can_alloc_reference) (\<lambda>_. can_alloc_reference)\<close>

lemma Search_lit_true_spec:
  shows \<open>\<Gamma>; Search_lit_true s v b \<Turnstile>\<^sub>F Search_lit_true_contract s v b\<close>
  apply (crush_boot f: Search_lit_true_def contract: Search_lit_true_contract_def)
  apply (crush_base specs add: key_spec Search_key_false_spec
      contracts add: key_contract_def Search_key_false_contract_def simp add: true_def false_def)
  done

definition Search_lit_false_contract :: \<open>Search \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>Search_lit_false_contract s v b \<equiv>
     make_function_contract (can_alloc_reference) (\<lambda>_. can_alloc_reference)\<close>

lemma Search_lit_false_spec:
  shows \<open>\<Gamma>; Search_lit_false s v b \<Turnstile>\<^sub>F Search_lit_false_contract s v b\<close>
  apply (crush_boot f: Search_lit_false_def contract: Search_lit_false_contract_def)
  apply (crush_base specs add: key_spec Search_key_false_spec
      contracts add: key_contract_def Search_key_false_contract_def simp add: true_def false_def)
  done

definition Search_key_true_contract :: \<open>Search \<Rightarrow> 64 word \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>Search_key_true_contract s k \<equiv>
     make_function_contract (can_alloc_reference) (\<lambda>_. can_alloc_reference)\<close>

lemma Search_key_true_spec:
  shows \<open>\<Gamma>; Search_key_true s k \<Turnstile>\<^sub>F Search_key_true_contract s k\<close>
  apply (crush_boot f: Search_key_true_def contract: Search_key_true_contract_def)
  apply (crush_base specs add: Search_key_false_spec
      contracts add: Search_key_false_contract_def simp add: true_def false_def)
  done

definition Search_enqueue_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_enqueue_contract r g s v b c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_enqueue_spec:
  shows \<open>\<Gamma>; Search_enqueue r v b c \<Turnstile>\<^sub>F Search_enqueue_contract r g s v b c\<close>
  apply (crush_boot f: Search_enqueue_def contract: Search_enqueue_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def Lit_mk_def vec_push_def vec_pop_def vec_truncate_def slice_swap_def
      specs add: key_spec contracts add: key_contract_def simp add: true_def false_def)
  apply (auto simp add: word64_less_of_nat intro: word64_less_max)
  done

definition Search_attach_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow> Formula \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_attach_contract r g s f L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_attach_spec:
  shows \<open>\<Gamma>; Search_attach r f L c \<Turnstile>\<^sub>F Search_attach_contract r g s f L c\<close>
  apply (crush_boot f: Search_attach_def contract: Search_attach_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def Lit_mk_def vec_push_def vec_pop_def vec_truncate_def slice_swap_def specs add: clause_len_spec lit_at_spec key_spec contracts add: clause_len_contract_def lit_at_contract_def key_contract_def
      simp add: true_def false_def)
  apply (all \<open>((drule word64_less_of_nat_2)+)?\<close>)
  apply (simp_all only: word64_less_of_nat big_c)
  apply (all \<open>(frule big_c(1))?, linarith\<close>)
  done


definition Search_free_lit_contract :: \<open>Search \<Rightarrow> Clause \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_free_lit_contract s cl op my \<equiv>
     make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma Search_free_lit_spec:
  shows \<open>\<Gamma>; Search_free_lit s cl op my \<Turnstile>\<^sub>F Search_free_lit_contract s cl op my\<close>
  apply (crush_boot f: Search_free_lit_def contract: Search_free_lit_contract_def)
  apply (crush_base inline: len_def specs add: Search_lit_false_spec
      contracts add: Search_lit_false_contract_def simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>rename_tac j_ref n_ref\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>k. \<Squnion>gj j gn n. j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> can_alloc_reference\<close> and
      INV'=\<open>\<lambda>k. \<Squnion>gj j gn n. j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> can_alloc_reference \<star>
             \<langle>n < word64_of_nat (length (Clause_v0 cl))\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. can_alloc_reference\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>\<close>)
  apply (crush_base specs add: Search_lit_false_spec
      contracts add: Search_lit_false_contract_def simp add: true_def false_def)
  apply (all \<open>((rule word64_less_max, assumption) | (simp add: not_le word64_less_of_nat; fail) |
    (simp add: nz_len; fail) | (rule not_le_max, assumption) | search_bound)\<close>)
  done

definition Search_find_watch_contract :: \<open>Search \<Rightarrow> Formula \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_find_watch_contract s f L c op my \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>db_small f L\<rangle>) (\<lambda>_. can_alloc_reference)\<close>

lemma Search_find_watch_spec:
  shows \<open>\<Gamma>; Search_find_watch s f L c op my \<Turnstile>\<^sub>F Search_find_watch_contract s f L c op my\<close>
  apply (crush_boot f: Search_find_watch_def contract: Search_find_watch_contract_def)
  apply (crush_base inline: len_def specs add: Search_free_lit_spec
      contracts add: Search_free_lit_contract_def simp add: true_def false_def)
  apply (all \<open>search_bound\<close>)
  done


definition close_gap_contract :: \<open>64 word list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word list, 'abort) function_contract\<close> where
  \<open>close_gap_contract xs i j \<equiv>
     make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma close_gap_spec:
  shows \<open>\<Gamma>; close_gap xs i j \<Turnstile>\<^sub>F close_gap_contract xs i j\<close>
  apply (crush_boot f: close_gap_def contract: close_gap_contract_def)
  apply (crush_base inline: len_def vec_truncate_def simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>rename_tac ys_ref i_ref j_ref\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>_. \<Squnion>gy y gi i gj j. ys_ref \<mapsto>\<langle>\<top>\<rangle> gy\<down>y \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
             j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference\<close> and
      INV'=\<open>\<lambda>_. \<Squnion>gy y gi i gj j. ys_ref \<mapsto>\<langle>\<top>\<rangle> gy\<down>y \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
             j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>i < word64_of_nat (length y) \<and> j < i\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>\<close>)
  apply (crush_base inline: len_def vec_truncate_def simp add: true_def false_def)
  apply (all \<open>search_bound\<close>)
  done

definition Search_propagate_lit_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_propagate_lit_contract r g s f L k \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_propagate_lit_spec:
  shows \<open>\<Gamma>; Search_propagate_lit r f L k \<Turnstile>\<^sub>F Search_propagate_lit_contract r g s f L k\<close>
  apply (crush_boot f: Search_propagate_lit_def contract: Search_propagate_lit_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def Lit_mk_def mem_replace_def vec_push_def
      specs add: clause_len_spec lit_at_spec key_spec Search_lit_false_spec
        Search_find_watch_spec Search_enqueue_spec Search_key_true_spec close_gap_spec
      contracts add: clause_len_contract_def lit_at_contract_def key_contract_def
        Search_lit_false_contract_def Search_find_watch_contract_def
        Search_enqueue_contract_def Search_key_true_contract_def close_gap_contract_def
      simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>rename_tac ws_ref confl_ref i_ref j_ref\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>_. \<Squnion>gs s' gw w gc c gi i gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> ws_ref \<mapsto>\<langle>\<top>\<rangle> gw\<down>w \<star>
             confl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference\<close> and
      INV'=\<open>\<lambda>_. \<Squnion>gs s' gw w gc c gi i gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> ws_ref \<mapsto>\<langle>\<top>\<rangle> gw\<down>w \<star>
             confl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>i < word64_of_nat (length w)\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>\<close>)
  apply (crush_base inline: len_def NONE_def BIG_def Lit_mk_def mem_replace_def vec_push_def
      specs add: clause_len_spec lit_at_spec key_spec Search_lit_false_spec
        Search_find_watch_spec Search_enqueue_spec Search_key_true_spec close_gap_spec
      contracts add: clause_len_contract_def lit_at_contract_def key_contract_def
        Search_lit_false_contract_def Search_find_watch_contract_def
        Search_enqueue_contract_def Search_key_true_contract_def close_gap_contract_def
      simp add: true_def false_def)
  apply (all \<open>search_bound\<close>)
  done


definition Search_propagate_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause list \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_propagate_contract r g s f L \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_propagate_spec:
  shows \<open>\<Gamma>; Search_propagate r f L \<Turnstile>\<^sub>F Search_propagate_contract r g s f L\<close>
  apply (crush_boot f: Search_propagate_def contract: Search_propagate_contract_def)
  apply (crush_base inline: len_def NONE_def simp add: true_def false_def)
  apply (ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>k. \<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> can_alloc_reference\<close> and
      INV'=\<open>\<lambda>k. \<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> can_alloc_reference \<star>
             \<langle>Search_qhead s' < word64_of_nat (length (Search_trail s'))\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s')\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>)
  apply (crush_base inline: len_def NONE_def
      specs add: key_spec Search_propagate_lit_spec
      contracts add: key_contract_def Search_propagate_lit_contract_def
      simp add: true_def false_def)
  apply (all \<open>search_bound\<close>)
  done

definition Search_rescale_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_rescale_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_rescale_spec:
  shows \<open>\<Gamma>; Search_rescale r \<Turnstile>\<^sub>F Search_rescale_contract r g s\<close>
  apply (crush_boot f: Search_rescale_def contract: Search_rescale_contract_def)
  apply (crush_base simp add: true_def false_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>i < word64_of_nat (length (Search_act s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: NONE_def simp add: true_def false_def)
    apply (all \<open>search_bound\<close>)
    done
  done

definition Search_prev_seen_contract :: \<open>Search \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_prev_seen_contract s i \<equiv> make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma Search_prev_seen_spec:
  shows \<open>\<Gamma>; Search_prev_seen s i \<Turnstile>\<^sub>F Search_prev_seen_contract s i\<close>
  apply (crush_boot f: Search_prev_seen_def contract: Search_prev_seen_contract_def)
  apply (crush_base inline: len_def NONE_def simp add: true_def false_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g j. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>j \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g j. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>j \<star> can_alloc_reference \<star> \<langle>0 < j\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. can_alloc_reference\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: NONE_def simp add: true_def false_def)
    apply (all \<open>search_bound\<close>)
    done
  done

definition Search_pick_contract :: \<open>Search \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_pick_contract s \<equiv> make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma Search_pick_spec:
  shows \<open>\<Gamma>; Search_pick s \<Turnstile>\<^sub>F Search_pick_contract s\<close>
  apply (crush_boot f: Search_pick_def contract: Search_pick_contract_def)
  apply (crush_base inline: len_def NONE_def simp add: true_def false_def)
  subgoal for best_ref best_act_ref v_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gb b ga a gv v. best_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>b \<star> best_act_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a \<star>
               v_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gb b ga a gv v. best_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>b \<star> best_act_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a \<star>
               v_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> can_alloc_reference \<star> \<langle>v < word64_of_nat (length (Search_set s))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def NONE_def simp add: true_def false_def)
    apply (all \<open>search_bound\<close>)
    done
  done

definition Search_backtrack_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_backtrack_contract r g s lvl \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_backtrack_spec:
  shows \<open>\<Gamma>; Search_backtrack r lvl \<Turnstile>\<^sub>F Search_backtrack_contract r g s lvl\<close>
  apply (crush_boot f: Search_backtrack_def contract: Search_backtrack_contract_def)
  apply (crush_base inline: len_def NONE_def vec_pop_def vec_truncate_def
      specs add: key_spec contracts add: key_contract_def simp add: true_def false_def)
  apply (ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>k. \<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> can_alloc_reference\<close> and
      INV'=\<open>\<lambda>k. \<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> can_alloc_reference \<star>
             \<langle>Search_lim s ! unat lvl < word64_of_nat (length (Search_trail s'))\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>)
  apply (crush_base inline: len_def NONE_def vec_pop_def vec_truncate_def
      specs add: key_spec contracts add: key_contract_def simp add: true_def false_def)
  apply (all \<open>search_bound\<close>)
  done


definition Search_bump_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_bump_contract r g s v \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_bump_spec:
  shows \<open>\<Gamma>; Search_bump r v \<Turnstile>\<^sub>F Search_bump_contract r g s v\<close>
  apply (crush_boot f: Search_bump_def contract: Search_bump_contract_def)
  apply (crush_base inline: len_def BIG_def specs add: Search_rescale_spec
      contracts add: Search_rescale_contract_def simp add: true_def false_def)
  apply (all \<open>search_bound\<close>)
  done

definition new_search_contract :: \<open>64 word \<Rightarrow> ('s, Search, 'abort) function_contract\<close> where
  \<open>new_search_contract n \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>n < 0x4000000000000000\<rangle>) (\<lambda>_. can_alloc_reference)\<close>

lemma new_search_spec:
  shows \<open>\<Gamma>; new_search n \<Turnstile>\<^sub>F new_search_contract n\<close>
  apply (crush_boot f: new_search_def contract: new_search_contract_def)
  apply (crush_base inline: NONE_def simp add: true_def false_def)
  apply (all \<open>search_bound\<close>)
  done


definition Search_analyze_clause_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_analyze_clause_contract r g s f L c p cur \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_analyze_clause_spec:
  shows \<open>\<Gamma>; Search_analyze_clause r f L c p cur \<Turnstile>\<^sub>F Search_analyze_clause_contract r g s f L c p cur\<close>
  apply (crush_boot f: Search_analyze_clause_def contract: Search_analyze_clause_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def vec_push_def
      specs add: clause_len_spec contracts add: clause_len_contract_def simp add: true_def false_def)
  subgoal for n count_ref j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gc cnt gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               count_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cnt \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gc cnt gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               count_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cnt \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>j < n\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def NONE_def BIG_def vec_push_def
        specs add: lit_at_spec Search_bump_spec contracts add: lit_at_contract_def Search_bump_contract_def
        simp add: true_def false_def)
    apply (all \<open>search_bound?\<close>)
    done
  done

definition Search_finish_learnt_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_finish_learnt_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_finish_learnt_spec:
  shows \<open>\<Gamma>; Search_finish_learnt r \<Turnstile>\<^sub>F Search_finish_learnt_contract r g s\<close>
  apply (crush_boot f: Search_finish_learnt_def contract: Search_finish_learnt_contract_def)
  apply (crush_base inline: len_def slice_swap_def simp add: true_def false_def)
  subgoal for best_ref bl_ref j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gb b gc c gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               best_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>b \<star> bl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star>
               can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gb b gc c gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               best_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>b \<star> bl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star>
               can_alloc_reference \<star> \<langle>j < word64_of_nat (length (Search_learnt s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def slice_swap_def simp add: true_def false_def)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(rule FalseE, rule swap_ok; assumption)?\<close>)
    done
  done

definition Search_copy_learnt_contract :: \<open>Search \<Rightarrow> ('s, Lit list, 'abort) function_contract\<close> where
  \<open>Search_copy_learnt_contract s \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>length r \<le> 4611686018427387904\<rangle>)\<close>

lemma Search_copy_learnt_spec:
  shows \<open>\<Gamma>; Search_copy_learnt s \<Turnstile>\<^sub>F Search_copy_learnt_contract s\<close>
  apply (crush_boot f: Search_copy_learnt_def contract: Search_copy_learnt_contract_def)
  apply (crush_base inline: len_def BIG_def vec_push_def Lit_mk_def simp add: true_def false_def)
  subgoal for out_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>go out gi i. out_ref \<mapsto>\<langle>\<top>\<rangle> go\<down>out \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>length out = unat i \<and> unat i \<le> 4611686018427387904\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>go out gi i. out_ref \<mapsto>\<langle>\<top>\<rangle> go\<down>out \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>length out = unat i \<and> i < word64_of_nat (length (Search_learnt s)) \<and>
                i < 0x4000000000000000\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def BIG_def vec_push_def Lit_mk_def simp add: true_def false_def)
    apply (all \<open>search_bound?\<close>)
    done
  done

definition Search_redundant_contract :: \<open>Search \<Rightarrow> Formula \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>Search_redundant_contract s f L v \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>db_small f L\<rangle>) (\<lambda>_. can_alloc_reference)\<close>

lemma Search_redundant_spec:
  shows \<open>\<Gamma>; Search_redundant s f L v \<Turnstile>\<^sub>F Search_redundant_contract s f L v\<close>
  apply (crush_boot f: Search_redundant_def contract: Search_redundant_contract_def)
  apply (crush_base inline: len_def NONE_def Lit_mk_def
      specs add: clause_len_spec contracts add: clause_len_contract_def
      simp add: true_def false_def)
  apply (all \<open>(erule word64_not_le_of_nat)?\<close>)
  subgoal for n j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g j. j_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>j \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g j. j_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>j \<star> can_alloc_reference \<star> \<langle>j < n\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. can_alloc_reference\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def NONE_def Lit_mk_def specs add: lit_at_spec
        contracts add: lit_at_contract_def simp add: true_def false_def)
    apply (all \<open>search_bound?\<close>)
    done
  done

definition Search_compact_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause list \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_compact_contract r g s f L \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_compact_spec:
  shows \<open>\<Gamma>; Search_compact r f L \<Turnstile>\<^sub>F Search_compact_contract r g s f L\<close>
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
    apply (crush_base inline: len_def slice_swap_def specs add: Search_redundant_spec
        contracts add: Search_redundant_contract_def simp add: true_def false_def)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(rule FalseE, rule swap_ok2; assumption)?\<close>)
    done
  done

definition Search_unmark_from_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_unmark_from_contract r g s i \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_unmark_from_spec:
  shows \<open>\<Gamma>; Search_unmark_from r i \<Turnstile>\<^sub>F Search_unmark_from_contract r g s i\<close>
  apply (crush_boot f: Search_unmark_from_def contract: Search_unmark_from_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for k_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gk kk. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gk kk. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> can_alloc_reference \<star>
               \<langle>kk < word64_of_nat (length (Search_learnt s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def simp add: true_def false_def)
    apply (all \<open>search_bound?\<close>)
    done
  done

definition Search_minimize_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause list \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_minimize_contract r g s f L \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_minimize_spec:
  shows \<open>\<Gamma>; Search_minimize r f L \<Turnstile>\<^sub>F Search_minimize_contract r g s f L\<close>
  apply (crush_boot f: Search_minimize_def contract: Search_minimize_contract_def)
  apply (crush_base inline: vec_truncate_def specs add: Search_compact_spec Search_unmark_from_spec
      contracts add: Search_compact_contract_def Search_unmark_from_contract_def
      simp add: true_def false_def)
  done

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

definition Search_learnt_lbd_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_learnt_lbd_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_learnt_lbd_spec:
  shows \<open>\<Gamma>; Search_learnt_lbd r \<Turnstile>\<^sub>F Search_learnt_lbd_contract r g s\<close>
  apply (crush_boot f: Search_learnt_lbd_def contract: Search_learnt_lbd_contract_def)
  apply (crush_base inline: len_def NONE_def simp add: true_def false_def)
  apply (all \<open>rename_tac n_ref j_ref\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>k. \<Squnion>gs s' gn n gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
             n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference\<close> and
      INV'=\<open>\<lambda>k. \<Squnion>gs s' gn n gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
             n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>j < word64_of_nat (length (Search_learnt s'))\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>\<close>)
  apply (crush_base inline: len_def NONE_def simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  done

definition init_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause list \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>init_contract r g s f L \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma init_spec:
  shows \<open>\<Gamma>; init r f L \<Turnstile>\<^sub>F init_contract r g s f L\<close>
  apply (crush_boot f: init_def contract: init_contract_def)
  apply (crush_base inline: len_def NONE_def simp add: true_def false_def)
  subgoal for confl_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gc c gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> confl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star>
               i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gc c gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> confl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star>
               i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>i < word64_of_nat (length (Formula_clauses f))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def NONE_def
        specs add: Search_attach_spec lit_at_spec Search_lit_false_spec Search_lit_true_spec
          Search_enqueue_spec
        contracts add: Search_attach_contract_def lit_at_contract_def Search_lit_false_contract_def
          Search_lit_true_contract_def Search_enqueue_contract_def
        simp add: true_def false_def)
    apply (all \<open>search_bound\<close>)
    done
  done

section \<open>Deletion of learned clauses\<close>

definition Search_count_live_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_count_live_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_count_live_spec:
  shows \<open>\<Gamma>; Search_count_live r \<Turnstile>\<^sub>F Search_count_live_contract r g s\<close>
  apply (crush_boot f: Search_count_live_def contract: Search_count_live_contract_def)
  apply (crush_base inline: len_def NONE_def simp add: true_def false_def)
  subgoal for live_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gl l gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               live_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gl l gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               live_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>i < word64_of_nat (length (Search_lbd s')) \<and> i < word64_of_nat (length (Search_dead s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def NONE_def simp add: true_def false_def)
    apply (all \<open>search_bound?\<close>)
    done
  done

definition Search_cut_contract :: \<open>Search \<Rightarrow> 64 word \<Rightarrow> ('s, Cut, 'abort) function_contract\<close> where
  \<open>Search_cut_contract s live \<equiv> make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma Search_cut_spec:
  shows \<open>\<Gamma>; Search_cut s live \<Turnstile>\<^sub>F Search_cut_contract s live\<close>
  apply (crush_boot f: Search_cut_def contract: Search_cut_contract_def)
  apply (crush_base inline: len_def Cut_mk_def simp add: true_def false_def)
  subgoal for left_ref t_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gl l gt t. left_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gl l gt t. left_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> t_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t \<star> can_alloc_reference \<star>
               \<langle>3 < t \<and> t - 1 < word64_of_nat (length (Search_hist s)) \<and>
                Search_hist s ! unat (t - 1) \<le> l\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. can_alloc_reference\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def Cut_mk_def simp add: true_def false_def)
    apply (all \<open>search_bound?\<close>)
    done
  done

lemma big_sum:
  assumes \<open>m + i < (0x4000000000000000 :: 64 word)\<close>
  shows \<open>unat (2 * m + 2 * i) = 2 * unat (m + i)\<close> \<open>unat (2 * m + 2 * i + 1) = 2 * unat (m + i) + 1\<close>
    \<open>unat (m + i) < 4611686018427387904\<close>
  using big_c[OF assms] by (simp_all add: distrib_left)

definition Search_unwatch_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_unwatch_contract r g s m i \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_unwatch_spec:
  shows \<open>\<Gamma>; Search_unwatch r m i \<Turnstile>\<^sub>F Search_unwatch_contract r g s m i\<close>
  apply (crush_boot f: Search_unwatch_def contract: Search_unwatch_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>((drule word64_less_of_nat)+)?\<close>)
  apply (simp_all only: big_sum)
  apply (all \<open>frule big_sum(3), linarith\<close>)
  done

definition Search_kill_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_kill_contract r g s m t left \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_kill_spec:
  shows \<open>\<Gamma>; Search_kill r m t left \<Turnstile>\<^sub>F Search_kill_contract r g s m t left\<close>
  apply (crush_boot f: Search_kill_def contract: Search_kill_contract_def)
  apply (crush_base inline: len_def specs add: Search_unwatch_spec
      contracts add: Search_unwatch_contract_def simp add: true_def false_def)
  subgoal for left_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gl l gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               left_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gl l gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               left_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>l \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>i < word64_of_nat (length (Search_lbd s')) \<and> i < word64_of_nat (length (Search_dead s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def specs add: Search_unwatch_spec
        contracts add: Search_unwatch_contract_def simp add: true_def false_def)
    apply (all \<open>search_bound?\<close>)
    done
  done

definition Search_reduce_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_reduce_contract r g s m \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_reduce_spec:
  shows \<open>\<Gamma>; Search_reduce r m \<Turnstile>\<^sub>F Search_reduce_contract r g s m\<close>
  apply (crush_boot f: Search_reduce_def contract: Search_reduce_contract_def)
  apply (crush_base specs add: Search_count_live_spec Search_cut_spec Search_kill_spec
      contracts add: Search_count_live_contract_def Search_cut_contract_def Search_kill_contract_def
      simp add: true_def false_def)
  done

end

end
