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
  shows \<open>Suc (length xs) \<le> 4611686018427387904\<close> \<open>length xs \<le> 4611686018427387903\<close>
proof -
  have \<open>unat (word64_of_nat (length xs)) = length xs\<close>
    using assms(1) by (simp add: unat_of_nat_eq)
  then show \<open>Suc (length xs) \<le> 4611686018427387904\<close> \<open>length xs \<le> 4611686018427387903\<close>
    using assms(2) by (simp_all add: word_less_nat_alt)
qed

lemma swap_ok:
  assumes \<open>(ra :: 64 word) < word64_of_nat n\<close> \<open>(2 :: 64 word) < word64_of_nat n\<close>
    \<open>Suc 0 < n \<longrightarrow> \<not> unat ra < n\<close>
  shows False
  using word64_less_of_nat[OF assms(1)] word64_less_of_nat[OF assms(2)] assms(3) by simp

lemma swap_ok2:
  assumes \<open>(a :: 64 word) < word64_of_nat n\<close> \<open>(b :: 64 word) < word64_of_nat n\<close>
    \<open>unat a < n \<longrightarrow> \<not> unat b < n\<close>
  shows False
  using assms word64_less_of_nat by blast

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

lemma succ_less:
  \<open>(j :: 64 word) < x \<Longrightarrow> unat (j + 1) = Suc (unat j)\<close>
  using word64_less_max[of j x] unat_word_Suc_simp[of j] by simp

text \<open>The frames of the search stack of the minimisation are three words; the top frame is read
  below its length.\<close>
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

text \<open>Offsets into the arena: below \<open>2^62\<close>, adding a small constant does not overflow.\<close>
lemma big_add:
  assumes \<open>(a :: 64 word) < 0x4000000000000000\<close> \<open>(b :: 64 word) \<le> 8\<close>
  shows \<open>unat (a + b) = unat a + unat b\<close>
proof -
  have \<open>unat a < 4611686018427387904\<close>
    using big_c(1)[OF assms(1)] .
  moreover have \<open>unat b \<le> 8\<close>
    using assms(2) by (simp add: word_le_nat_alt)
  ultimately show ?thesis
    by (simp add: unat_add_lem[symmetric])
qed

lemma arena_end:
  assumes \<open>(a :: 64 word) < 0x4000000000000000\<close> \<open>(x :: 64 word) < 0x4000000000000000\<close>
  shows \<open>unat (a + 6) + unat x < 18446744073709551616\<close>
  using big_add[OF assms(1), of 6] big_c(1)[OF assms(1)] big_c(1)[OF assms(2)] by simp

lemma arena_le:
  assumes \<open>a + c < word64_of_nat m\<close> \<open>(a :: 64 word) < 0x4000000000000000\<close> \<open>b \<le> c\<close> \<open>c \<le> 8\<close>
  shows \<open>unat (a + b) < m\<close>
proof -
  have \<open>unat (a + b) = unat a + unat b\<close> \<open>unat (a + c) = unat a + unat c\<close>
    using big_add[OF assms(2)] assms(3,4) by auto
  moreover have \<open>unat b \<le> unat c\<close>
    using assms(3) by (simp add: word_le_nat_alt)
  moreover have \<open>unat (a + c) < m\<close>
    using assms(1) by (rule word64_less_of_nat)
  ultimately show ?thesis
    by simp
qed

lemma big_twice:
  \<open>(a :: 64 word) < 0x4000000000000000 \<Longrightarrow> unat (2 * a) < 18446744073709551615\<close>
  using big_c[of a] by simp

lemma arena_ix:
  assumes \<open>\<not> word64_of_nat m \<le> a + c\<close> \<open>\<not> 0x4000000000000000 \<le> (a :: 64 word)\<close> \<open>b \<le> c\<close>
    \<open>c \<le> 8\<close>
  shows \<open>unat (a + b) < m\<close> \<open>unat (b + a) < m\<close>
  using arena_le[of a c m b] assms by (simp_all add: not_le add.commute)

text \<open>The index of the other watched key of a watch node: \<open>o + 5 - side\<close>.\<close>
lemma side_ix:
  assumes \<open>(a :: 64 word) < 0x4000000000000000\<close> \<open>a + 5 < word64_of_nat n\<close>
  shows \<open>unat (a + 5 - x mod 2) < n\<close> \<open>x mod 2 \<le> a + 5\<close>
proof -
  have m: \<open>unat (x mod 2) \<le> 1\<close>
    using word_mod_less_divisor[of 2 x] by (simp add: word_less_nat_alt)
  have u: \<open>unat (a + 5) = unat a + 5\<close>
    using big_add[OF assms(1), of 5] by simp
  show le: \<open>x mod 2 \<le> a + 5\<close>
    using m u by (simp add: word_le_nat_alt)
  have \<open>unat (a + 5) < n\<close>
    using assms(2) by (rule word64_less_of_nat)
  then show \<open>unat (a + 5 - x mod 2) < n\<close>
    using unat_sub[OF le] by simp
qed

lemma arena_small:
  assumes \<open>\<not> 0x4000000000000000 \<le> (a :: 64 word)\<close> \<open>b \<le> 8\<close>
  shows \<open>unat (a + b) < 18446744073709551614\<close> \<open>unat (a + b) < 18446744073709551615\<close>
proof -
  have a: \<open>a < 0x4000000000000000\<close>
    using assms(1) by (simp add: not_le)
  have \<open>unat (a + b) = unat a + unat b\<close>
    using big_add[OF a assms(2)] .
  moreover have \<open>unat a < 4611686018427387904\<close>
    using big_c(1)[OF a] .
  moreover have \<open>unat b \<le> 8\<close>
    using assms(2) by (simp add: word_le_nat_alt)
  ultimately show \<open>unat (a + b) < 18446744073709551614\<close> \<open>unat (a + b) < 18446744073709551615\<close>
    by simp_all
qed

lemma arena_ix0:
  assumes \<open>\<not> word64_of_nat m \<le> a + c\<close> \<open>\<not> 0x4000000000000000 \<le> (a :: 64 word)\<close> \<open>c \<le> 8\<close>
  shows \<open>unat a < m\<close>
  using arena_ix(1)[OF assms(1,2) _ assms(3), of 0] by simp

lemma big_nle:
  \<open>\<not> 0x4000000000000000 \<le> (a :: 64 word) \<Longrightarrow> unat a < 4611686018427387904\<close>
  using big_c(1)[of a] by (simp add: not_le)

lemma max_less:
  \<open>(0xFFFFFFFFFFFFFFFF :: 64 word) < y \<Longrightarrow> P\<close>
  using word64_less_max[of \<open>0xFFFFFFFFFFFFFFFF :: 64 word\<close> y] by simp

lemma big_succ_le:
  \<open>(c :: 64 word) < 0x4000000000000000 \<Longrightarrow> unat (c + 1) \<le> 4611686018427387904\<close>
  using big_c(1)[of c] succ_less[of c] by simp

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

text \<open>The goals that \<open>crush_base\<close> leaves in the search and in the minimisation
  (\<^verbatim>\<open>Sat_Minimize\<close>) are bounds of words, indices and arena offsets. Each closes in one step: by the
  simplifier or by one of the word lemmas. Every alternative closes its goal or fails.\<close>

method search_bound =
  ((simp only: word64_less_of_nat; fail) | erule word64_less_max | erule len_minus_one | rule drop30 |
    (simp add: word_le_nat_alt word_less_nat_alt; fail) |
    (rule add_big; assumption) | (frule big_c(1), linarith) |
    erule nz_len | (rule push_len; assumption) | erule counter_add |
    (rule one_le; assumption) | rule le_max | (rule succ_less; assumption) |
    (rule succ_less[symmetric]; assumption) | (rule big_succ_le; assumption) |
    (rule inc_div; assumption) | (rule inc_add; assumption) | (rule one_lt; assumption) |
    erule not_le_max | (rule len_minus; simp; fail) |
    erule max_less | erule word64_less_of_nat | (rule arena_ix, assumption, assumption, simp, simp) |
    (rule arena_small, assumption, simp) | erule big_twice | (erule arena_le, assumption, simp, simp) |
    (rule arena_ix0, assumption, assumption, simp) | (frule big_nle, linarith))

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

definition Search_push_clause_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow> Formula \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_push_clause_contract r g s f L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_push_clause_spec:
  shows \<open>\<Gamma>; Search_push_clause r f L c \<Turnstile>\<^sub>F Search_push_clause_contract r g s f L c\<close>
  apply (crush_boot f: Search_push_clause_def contract: Search_push_clause_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def Lit_mk_def vec_push_def
      specs add: clause_len_spec lit_at_spec key_spec
      contracts add: clause_len_contract_def lit_at_contract_def key_contract_def
      simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(erule (1) arena_end)?\<close>)
  apply (all \<open>rename_tac len j_ref\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>_. \<Squnion>gs s' gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference\<close> and
      INV'=\<open>\<lambda>_. \<Squnion>gs s' gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>j < len\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>\<close>)
  apply (crush_base inline: len_def NONE_def BIG_def Lit_mk_def vec_push_def
      specs add: clause_len_spec lit_at_spec key_spec
      contracts add: clause_len_contract_def lit_at_contract_def key_contract_def
      simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  done

definition Search_attach_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow> Formula \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_attach_contract r g s f L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_attach_spec:
  shows \<open>\<Gamma>; Search_attach r f L c \<Turnstile>\<^sub>F Search_attach_contract r g s f L c\<close>
  apply (crush_boot f: Search_attach_def contract: Search_attach_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def vec_push_def
      specs add: Search_push_clause_spec contracts add: Search_push_clause_contract_def
      simp add: true_def false_def)
  apply (all \<open>search_bound\<close>)
  done

definition Search_scan_contract :: \<open>Search \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_scan_contract s a b \<equiv>
     make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma Search_scan_spec:
  shows \<open>\<Gamma>; Search_scan s a b \<Turnstile>\<^sub>F Search_scan_contract s a b\<close>
  apply (crush_boot f: Search_scan_def contract: Search_scan_contract_def)
  apply (crush_base inline: len_def specs add: Search_key_false_spec
      contracts add: Search_key_false_contract_def simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>rename_tac j_ref\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>_. \<Squnion>gj j. j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference\<close> and
      INV'=\<open>\<lambda>_. \<Squnion>gj j. j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>j < word64_of_nat (length (Search_arena s))\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. can_alloc_reference\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>\<close>)
  apply (crush_base specs add: Search_key_false_spec
      contracts add: Search_key_false_contract_def simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  done

definition Search_find_watch_contract :: \<open>Search \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_find_watch_contract s b e op my \<equiv>
     make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma Search_find_watch_spec:
  shows \<open>\<Gamma>; Search_find_watch s b e op my \<Turnstile>\<^sub>F Search_find_watch_contract s b e op my\<close>
  apply (crush_boot f: Search_find_watch_def contract: Search_find_watch_contract_def)
  apply (crush_base specs add: Search_scan_spec
      contracts add: Search_scan_contract_def simp add: true_def false_def)
  apply (all \<open>search_bound\<close>)
  done

definition Search_other_key_contract :: \<open>Search \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_other_key_contract s nd \<equiv>
     make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma Search_other_key_spec:
  shows \<open>\<Gamma>; Search_other_key s nd \<Turnstile>\<^sub>F Search_other_key_contract s nd\<close>
  apply (crush_boot f: Search_other_key_def contract: Search_other_key_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def simp add: true_def false_def)
  apply (all \<open>(rule side_ix, assumption, assumption)?\<close>)
  apply (all \<open>search_bound\<close>)
  done

definition Search_skip_true_contract :: \<open>Search \<Rightarrow> 64 word list \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_skip_true_contract s ws i \<equiv>
     make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma Search_skip_true_spec:
  shows \<open>\<Gamma>; Search_skip_true s ws i \<Turnstile>\<^sub>F Search_skip_true_contract s ws i\<close>
  apply (crush_boot f: Search_skip_true_def contract: Search_skip_true_contract_def)
  apply (crush_base inline: len_def specs add: Search_key_true_spec Search_other_key_spec
      contracts add: Search_key_true_contract_def Search_other_key_contract_def
      simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>rename_tac p_ref\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>_. \<Squnion>gp p. p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> can_alloc_reference\<close> and
      INV'=\<open>\<lambda>_. \<Squnion>gp p. p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> can_alloc_reference \<star>
             \<langle>p < word64_of_nat (length ws)\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>\<close>)
  apply (crush_base inline: len_def specs add: Search_key_true_spec Search_other_key_spec
      contracts add: Search_key_true_contract_def Search_other_key_contract_def
      simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
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

definition Search_move_watch_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_move_watch_contract r g s k nd okey \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_move_watch_spec:
  shows \<open>\<Gamma>; Search_move_watch r k nd okey \<Turnstile>\<^sub>F Search_move_watch_contract r g s k nd okey\<close>
  apply (crush_boot f: Search_move_watch_def contract: Search_move_watch_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def vec_push_def
      specs add: Search_find_watch_spec Search_enqueue_spec Search_key_false_spec
      contracts add: Search_find_watch_contract_def Search_enqueue_contract_def
        Search_key_false_contract_def
      simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  done

definition Search_propagate_lit_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_propagate_lit_contract r g s k \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_propagate_lit_spec:
  shows \<open>\<Gamma>; Search_propagate_lit r k \<Turnstile>\<^sub>F Search_propagate_lit_contract r g s k\<close>
  apply (crush_boot f: Search_propagate_lit_def contract: Search_propagate_lit_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def mem_replace_def
      specs add: Search_move_watch_spec Search_skip_true_spec Search_other_key_spec close_gap_spec
      contracts add: Search_move_watch_contract_def Search_skip_true_contract_def
        Search_other_key_contract_def close_gap_contract_def
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
  apply (crush_base inline: len_def NONE_def BIG_def mem_replace_def
      specs add: Search_move_watch_spec Search_skip_true_spec Search_other_key_spec close_gap_spec
      contracts add: Search_move_watch_contract_def Search_skip_true_contract_def
        Search_other_key_contract_def close_gap_contract_def
      simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>_. \<Squnion>gw w gi i gj j. ws_ref \<mapsto>\<langle>\<top>\<rangle> gw\<down>w \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
             j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference\<close> and
      INV'=\<open>\<lambda>_. \<Squnion>gw w gi i gj j. ws_ref \<mapsto>\<langle>\<top>\<rangle> gw\<down>w \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
             j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>i < word64_of_nat (length w) \<and> j < i\<rangle>\<close> and
      BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>\<close>)
  apply (crush_base inline: len_def NONE_def BIG_def mem_replace_def
      specs add: Search_move_watch_spec Search_skip_true_spec Search_other_key_spec close_gap_spec
      contracts add: Search_move_watch_contract_def Search_skip_true_contract_def
        Search_other_key_contract_def close_gap_contract_def
      simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  done


definition Search_propagate_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_propagate_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_propagate_spec:
  shows \<open>\<Gamma>; Search_propagate r \<Turnstile>\<^sub>F Search_propagate_contract r g s\<close>
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


definition Search_clause_lbd_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_clause_lbd_contract r g s f L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_clause_lbd_spec:
  shows \<open>\<Gamma>; Search_clause_lbd r f L c \<Turnstile>\<^sub>F Search_clause_lbd_contract r g s f L c\<close>
  apply (crush_boot f: Search_clause_lbd_def contract: Search_clause_lbd_contract_def)
  apply (crush_base inline: len_def NONE_def
      specs add: clause_len_spec contracts add: clause_len_contract_def simp add: true_def false_def)
  apply (all \<open>rename_tac n n_ref j_ref\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>k. \<Squnion>gs s' gn cnt gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
             n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>cnt \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference\<close> and
      INV'=\<open>\<lambda>k. \<Squnion>gs s' gn cnt gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
             n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>cnt \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>j < n\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>\<close>)
  apply (crush_base inline: len_def NONE_def
      specs add: lit_at_spec contracts add: lit_at_contract_def simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  done

definition Search_update_lbd_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_update_lbd_contract r g s f L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') in
     make_function_contract pre post\<close>

lemma Search_update_lbd_spec:
  shows \<open>\<Gamma>; Search_update_lbd r f L c \<Turnstile>\<^sub>F Search_update_lbd_contract r g s f L c\<close>
  apply (crush_boot f: Search_update_lbd_def contract: Search_update_lbd_contract_def)
  apply (crush_base inline: len_def specs add: Search_clause_lbd_spec
      contracts add: Search_clause_lbd_contract_def simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
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
      specs add: Search_update_lbd_spec clause_len_spec
      contracts add: Search_update_lbd_contract_def clause_len_contract_def simp add: true_def false_def)
  apply (all \<open>rename_tac n count_ref j_ref\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>k. \<Squnion>gs s' gc cnt gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
             count_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cnt \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference\<close> and
      INV'=\<open>\<lambda>k. \<Squnion>gs s' gc cnt gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
             count_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cnt \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>j < n\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>\<close>)
  apply (crush_base inline: len_def NONE_def BIG_def vec_push_def
      specs add: lit_at_spec Search_bump_spec contracts add: lit_at_contract_def Search_bump_contract_def
      simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
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
  apply (all \<open>search_bound\<close>)
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
