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
  using assms unat_lt2p[of c] by (simp add: word_le_nat_alt not_less unat_sub)


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
  using assms by (simp add: word_le_nat_alt word_less_nat_alt unat_sub unat_of_nat)

text \<open>Offsets into the arena: below \<open>2^62\<close>, adding a small constant does not overflow.\<close>
lemma big_add:
  assumes \<open>(a :: 64 word) < 0x4000000000000000\<close> \<open>(b :: 64 word) \<le> 8\<close>
  shows \<open>unat (a + b) = unat a + unat b\<close>
  using assms by (simp add: word_le_nat_alt word_less_nat_alt unat_add_lem[symmetric])

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
  using assms word64_less_of_nat[OF assms(2)] word_mod_less_divisor[of 2 x]
  by (simp_all add: word_le_nat_alt word_less_nat_alt unat_sub unat_word_ariths)

lemma arena_small:
  assumes \<open>\<not> 0x4000000000000000 \<le> (a :: 64 word)\<close> \<open>b \<le> 8\<close>
  shows \<open>unat (a + b) < 18446744073709551614\<close> \<open>unat (a + b) < 18446744073709551615\<close>
  using assms by (simp_all add: word_le_nat_alt unat_word_ariths)

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
  \<open>(x :: 64 word) < 0x4000000000000000 \<Longrightarrow> unat (x div 0x200) < 18446744073709551615\<close>
  using big_c(1)[of x] by (simp add: unat_div)

lemma inc_add:
  assumes \<open>(x :: 64 word) < 0x4000000000000000\<close>
  shows \<open>unat x + unat (x div 0x200 + 1) < 18446744073709551616\<close>
  using assms by (simp add: word_less_nat_alt unat_div unat_word_ariths)

lemma one_lt:
  \<open>1 < word64_of_nat n \<Longrightarrow> Suc 0 < n\<close>
  using word64_less_of_nat[of 1 n] by simp

section \<open>Vectors that grow\<close>

text \<open>The translation models a \<^verbatim>\<open>Vec\<close> as an \<^typ>\<open>'a rvec\<close> whose \<^verbatim>\<open>push\<close> panics on a
  capacity overflow. A vector of the layout \<open>l\<close> that is well-formed (\<open>vok l\<close>) and shorter than
  \<open>2^56\<close> (the code's \<^verbatim>\<open>BIG\<close>) grows by up to eight elements without one, for every layout
  of the search, whose largest capacity is at least \<open>2^58 + 16\<close>.\<close>
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

lemma vok_new:
  \<open>vok l (rvec_new_val l)\<close>
  by (simp add: vok_def rvec_new_val_wf)

lemma vok_bound:
  assumes \<open>vok l v\<close> \<open>word64_of_nat (rvec_length v) < (0x100000000000000 :: 64 word)\<close>
  shows \<open>rvec_length v < 144115188075855872\<close>
proof -
  have \<open>unat (word64_of_nat (rvec_length v) :: 64 word) = rvec_length v\<close>
    using assms(1) rvec_len_unat(1)[of v] by (simp add: vok_def)
  then show ?thesis
    using assms(2) by (simp add: word_less_nat_alt)
qed

text \<open>A push of up to eight elements onto a vector of the search that is shorter than
  \<^verbatim>\<open>BIG\<close>.\<close>
lemma push_ok:
  assumes \<open>vok l v\<close> \<open>word64_of_nat (rvec_length v) < (0x100000000000000 :: 64 word)\<close>
    \<open>288230376151711760 \<le> rvec_cap_max l\<close> \<open>length xs \<le> 8\<close>
  shows \<open>\<exists>y. rvec_append_val v xs = Some y\<close> \<open>vok l (the (rvec_append_val v xs))\<close>
    \<open>rvec_elems (the (rvec_append_val v xs)) = rvec_elems v @ xs\<close>
  using vok_append[OF assms(1) vok_bound[OF assms(1,2)] assms(4,3)] by auto

lemma in_set_update:
  \<open>x \<in> set (xs[k := y]) \<Longrightarrow> x = y \<or> x \<in> set xs\<close>
  using set_update_subset_insert by fastforce

lemma all_set_update:
  \<open>(\<forall>w \<in> set xs. P w) \<Longrightarrow> P y \<Longrightarrow> \<forall>w \<in> set (xs[k := y]). P w\<close>
  using set_update_subset_insert by fastforce

text \<open>A push onto the watch list \<open>k\<close>.\<close>
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
    by (rule all_set_update[OF assms(1)])
qed

text \<open>The invariant of the search state: the vectors it grows are well-formed and have the
  layouts of their element types.\<close>
definition sok :: \<open>Search \<Rightarrow> bool\<close> where
  \<open>sok s \<equiv> vok L8 (Search_trail s) \<and> vok L8 (Search_start s) \<and> vok L8 (Search_arena s) \<and>
     (\<forall>w \<in> set (rvec_elems (Search_watches s)). vok L8 w) \<and> vok L16 (Search_learnt s) \<and>
     vok L8 (Search_stack s) \<and> vok L8 (Search_toclear s) \<and> vok L8 (Search_lim s) \<and>
     vok L8 (Search_lbd s) \<and> vok L1 (Search_dead s)\<close>

text \<open>The invariant in a precondition. \<open>crush_base\<close> would use a premise \<open>sok s\<close> to
  instantiate the \<open>sok ?s'\<close> of a postcondition before the points-to fixes \<open>?s'\<close>.\<close>
definition sok_in :: \<open>Search \<Rightarrow> bool\<close> where
  \<open>sok_in \<equiv> sok\<close>

lemma rvec_elems_focus_modify_fun:
  \<open>\<nabla>{rvec_elems_focus} f = update_rvec_elems f\<close>
  by (rule ext) (simp add: rvec_elems_focus_modify)

text \<open>The goals of the invariant that \<open>crush_base\<close> leaves.\<close>
method sok_tac =
  (auto simp add: sok_def sok_in_def vok_new cap_max_big push_ok rvec_elems_focus_modify_fun
    intro!: vok_update all_set_update dest!: in_set_update)

text \<open>\<^verbatim>\<open>BIG\<close> is \<open>2^56\<close>; the bounds below \<open>2^62\<close> of the word lemmas hold below it.\<close>
lemma big56_lt:
  \<open>(a :: 64 word) < 0x100000000000000 \<Longrightarrow> a < 0x4000000000000000\<close>
  by (simp add: word_less_nat_alt)

lemma big56_nle:
  \<open>\<not> 0x100000000000000 \<le> (a :: 64 word) \<Longrightarrow> \<not> 0x4000000000000000 \<le> a\<close>
  by (simp add: word_le_nat_alt)

text \<open>A watch node \<open>nd\<close> of the arena (\<open>4 \<le> nd < len\<close>) and the positions of its clause
  below it: \<open>nd - c\<close> for \<open>c \<le> 4\<close>, and \<open>c = 5\<close> for an odd \<open>nd\<close>. The simplifier writes
  \<open>nd - c\<close> as \<open>(2^64 - c) + nd\<close>.\<close>
lemma node_norm:
  \<open>(0xFFFFFFFFFFFFFFFF :: 64 word) + nd = nd - 1\<close> \<open>(0xFFFFFFFFFFFFFFFE :: 64 word) + nd = nd - 2\<close>
  \<open>(0xFFFFFFFFFFFFFFFD :: 64 word) + nd = nd - 3\<close> \<open>(0xFFFFFFFFFFFFFFFC :: 64 word) + nd = nd - 4\<close>
  \<open>(0xFFFFFFFFFFFFFFFB :: 64 word) + nd = nd - 5\<close>
  by simp_all

lemma node_facts:
  fixes nd :: \<open>64 word\<close>
  assumes \<open>\<not> nd < 4\<close> \<open>\<not> word64_of_nat m \<le> nd\<close>
  shows \<open>4 \<le> unat nd \<and> unat nd < m \<and> unat nd < 18446744073709551615 \<and>
    (nd mod 2 = 1 \<longrightarrow> 5 \<le> unat nd)\<close>
proof -
  have n: \<open>unat nd < m\<close> \<open>unat nd < 18446744073709551615\<close>
    using assms(2) word64_less_of_nat word64_less_max by (auto simp add: not_le)
  have f: \<open>4 \<le> unat nd\<close>
    using assms(1) by (simp add: not_less word_le_nat_alt)
  have \<open>5 \<le> unat nd\<close> if \<open>nd mod 2 = 1\<close>
  proof -
    have \<open>unat nd mod 2 = 1\<close>
      using that unat_mod[of nd 2] by simp
    then show ?thesis
      using f by presburger
  qed
  then show ?thesis
    using n f by blast
qed

lemma node_facts1:
  fixes nd :: \<open>64 word\<close>
  assumes \<open>\<not> word64_of_nat m \<le> nd\<close> \<open>\<not> word64_of_nat m \<le> 1 + nd\<close>
  shows \<open>unat nd + 1 < m \<and> unat nd < 18446744073709551614\<close>
proof -
  have n: \<open>unat nd < 18446744073709551615\<close>
    using assms(1) word64_less_max by (auto simp add: not_le)
  then have \<open>unat (1 + nd) = unat nd + 1\<close>
    using unat_word_Suc_simp[of nd] by (simp add: add.commute)
  moreover have \<open>unat (1 + nd) < m\<close> \<open>unat (1 + nd) < 18446744073709551615\<close>
    using assms(2) word64_less_of_nat word64_less_max by (auto simp add: not_le)
  ultimately show ?thesis
    by simp
qed

lemma node_sub_eq:
  \<open>unat (c :: 64 word) \<le> unat nd \<Longrightarrow> unat (nd - c) = unat nd - unat c\<close>
  by (simp add: unat_sub word_le_nat_alt)

text \<open>The arena offset \<open>nd - nd mod 2 - 4\<close> of the clause of the node \<open>nd\<close>.\<close>
lemma node_off:
  fixes nd :: \<open>64 word\<close>
  assumes \<open>\<not> nd < 4\<close> \<open>\<not> word64_of_nat m \<le> nd\<close>
  shows \<open>nd mod 2 \<le> nd\<close> \<open>4 \<le> nd - nd mod 2\<close>
    \<open>unat (nd - nd mod 2 - 4) < 18446744073709551611\<close>
proof -
  have f: \<open>4 \<le> unat nd\<close> \<open>unat nd < 18446744073709551615\<close>
    using node_facts[OF assms] by auto
  have u: \<open>unat (nd mod 2) = unat nd mod 2\<close>
    by (simp add: unat_mod)
  show a: \<open>nd mod 2 \<le> nd\<close>
    by (simp add: word_le_nat_alt u)
  have d: \<open>unat (nd - nd mod 2) = unat nd - unat nd mod 2\<close>
    using a u by (simp add: unat_sub)
  have e: \<open>4 \<le> unat nd - unat nd mod 2\<close>
    using f(1) by presburger
  show b: \<open>4 \<le> nd - nd mod 2\<close>
    using e d by (simp add: word_le_nat_alt)
  have \<open>unat (nd - nd mod 2 - 4) = unat (nd - nd mod 2) - 4\<close>
    using b by (simp add: unat_sub word_le_nat_alt)
  then show \<open>unat (nd - nd mod 2 - 4) < 18446744073709551611\<close>
    using d f(2) by linarith
qed

method node_bound =
  ((rule node_off, assumption, assumption) |
   ((simp only: node_norm)?, frule (1) node_facts, (frule (1) node_facts1)?,
    ((simp add: node_sub_eq; linarith?) | linarith)))

section \<open>Bounds\<close>

text \<open>The goals that \<open>crush_base\<close> leaves in the search and in the minimisation
  (\<^verbatim>\<open>Sat_Minimize\<close>) are bounds of words, indices and arena offsets. Each closes in one step: by the
  simplifier or by one of the word lemmas. Every alternative closes its goal or fails.\<close>

method search_bound =
  (((drule big56_lt | drule big56_nle)+)?,
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
    (rule arena_ix0, assumption, assumption, simp) | (frule big_nle, linarith) |
    (rule side_ix, assumption, assumption)))

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
  apply (crush_base simp add: true_def false_def)
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
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_enqueue_spec:
  shows \<open>\<Gamma>; Search_enqueue r v b c \<Turnstile>\<^sub>F Search_enqueue_contract r g s v b c\<close>
  apply (crush_boot f: Search_enqueue_def contract: Search_enqueue_contract_def)
  apply (crush_base inline: NONE_def BIG_def
      specs add: key_spec contracts add: key_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (auto simp add: sok_def sok_in_def cap_max_big push_ok intro: word64_less_of_nat)
  done

definition Search_push_clause_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow> Formula \<Rightarrow> Clause rvec \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_push_clause_contract r g s f L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s \<and> db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_push_clause_spec:
  shows \<open>\<Gamma>; Search_push_clause r f L c \<Turnstile>\<^sub>F Search_push_clause_contract r g s f L c\<close>
  apply (crush_boot f: Search_push_clause_def contract: Search_push_clause_contract_def)
  apply (crush_base inline: NONE_def BIG_def Lit_mk_def
      specs add: clause_len_spec lit_at_spec key_spec
      contracts add: clause_len_contract_def lit_at_contract_def key_contract_def
      simp add: true_def false_def)
  apply (all \<open>(auto simp add: sok_def sok_in_def cap_max_big push_ok; fail)?\<close>)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>((drule big56_lt)+, erule (1) arena_end)?\<close>)
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
  apply (all \<open>search_bound?\<close>)
  apply (auto simp add: sok_def sok_in_def cap_max_big push_ok)
  done

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
  apply (metis watch_push(2) word64_less_of_nat)
  done

definition Search_attach_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow> Formula \<Rightarrow> Clause rvec \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_attach_contract r g s f L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s \<and> db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_attach_spec:
  shows \<open>\<Gamma>; Search_attach r f L c \<Turnstile>\<^sub>F Search_attach_contract r g s f L c\<close>
  apply (crush_boot f: Search_attach_def contract: Search_attach_contract_def)
  apply (crush_base inline: NONE_def BIG_def
      specs add: Search_push_clause_spec Search_watch_spec
      contracts add: Search_push_clause_contract_def Search_watch_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition Search_scan_contract :: \<open>Search \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_scan_contract s a b \<equiv>
     make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma Search_scan_spec:
  shows \<open>\<Gamma>; Search_scan s a b \<Turnstile>\<^sub>F Search_scan_contract s a b\<close>
  apply (crush_boot f: Search_scan_def contract: Search_scan_contract_def)
  apply (crush_base specs add: Search_key_false_spec
      contracts add: Search_key_false_contract_def simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>rename_tac j_ref\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>_. \<Squnion>gj j. j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference\<close> and
      INV'=\<open>\<lambda>_. \<Squnion>gj j. j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>j < word64_of_nat (rvec_length (Search_arena s))\<rangle>\<close> and
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
  apply (crush_base inline: NONE_def BIG_def simp add: true_def false_def)
  apply (all \<open>search_bound\<close>)
  done

definition Search_skip_true_contract :: \<open>Search \<Rightarrow> (64 word) rvec \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_skip_true_contract s ws i \<equiv>
     make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma Search_skip_true_spec:
  shows \<open>\<Gamma>; Search_skip_true s ws i \<Turnstile>\<^sub>F Search_skip_true_contract s ws i\<close>
  apply (crush_boot f: Search_skip_true_def contract: Search_skip_true_contract_def)
  apply (crush_base specs add: Search_key_true_spec Search_other_key_spec
      contracts add: Search_key_true_contract_def Search_other_key_contract_def
      simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>rename_tac p_ref\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>_. \<Squnion>gp p. p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> can_alloc_reference\<close> and
      INV'=\<open>\<lambda>_. \<Squnion>gp p. p_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star> can_alloc_reference \<star>
             \<langle>p < word64_of_nat (rvec_length ws)\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>\<close>)
  apply (crush_base specs add: Search_key_true_spec Search_other_key_spec
      contracts add: Search_key_true_contract_def Search_other_key_contract_def
      simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  done

definition close_gap_contract :: \<open>(64 word) rvec \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, (64 word) rvec, 'abort) function_contract\<close> where
  \<open>close_gap_contract xs i j \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>vok L8 xs\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>vok L8 r\<rangle>)\<close>

lemma close_gap_spec:
  shows \<open>\<Gamma>; close_gap xs i j \<Turnstile>\<^sub>F close_gap_contract xs i j\<close>
  apply (crush_boot f: close_gap_def contract: close_gap_contract_def)
  apply (crush_base simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  apply (rename_tac ys_ref i_ref j_ref)
  apply (ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>_. \<Squnion>gy y gi i gj j. ys_ref \<mapsto>\<langle>\<top>\<rangle> gy\<down>y \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
             j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star> \<langle>vok L8 y\<rangle>\<close> and
      INV'=\<open>\<lambda>_. \<Squnion>gy y gi i gj j. ys_ref \<mapsto>\<langle>\<top>\<rangle> gy\<down>y \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
             j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>vok L8 y \<and> i < word64_of_nat (rvec_length y) \<and> j < i\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>)
  apply (crush_base simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (auto intro!: vok_update)
  done

definition Search_move_watch_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_move_watch_contract r g s k nd okey \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_move_watch_spec:
  shows \<open>\<Gamma>; Search_move_watch r k nd okey \<Turnstile>\<^sub>F Search_move_watch_contract r g s k nd okey\<close>
  apply (crush_boot f: Search_move_watch_def contract: Search_move_watch_contract_def)
  apply (crush_base inline: NONE_def BIG_def
      specs add: Search_find_watch_spec Search_enqueue_spec Search_key_false_spec Search_watch_spec
      contracts add: Search_find_watch_contract_def Search_enqueue_contract_def
        Search_key_false_contract_def Search_watch_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  apply (all \<open>(node_bound; fail)?\<close>)
  done

definition Search_propagate_lit_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_propagate_lit_contract r g s k \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

text \<open>\<^verbatim>\<open>propagate_lit\<close> takes the watch list \<open>k\<close> out and leaves an empty vector there.\<close>
lemma sok_watch_new:
  \<open>sok_in s \<Longrightarrow> sok (update_Search_watches (\<nabla>{rvec_elems_focus} (\<lambda>xs. xs[k := rvec_new_val L8])) s)\<close>
  unfolding sok_in_def sok_def rvec_elems_focus_modify_fun
  by (auto simp add: vok_new dest!: in_set_update)

lemma sok_watch_get:
  \<open>sok_in s \<Longrightarrow> \<not> word64_of_nat (rvec_length (Search_watches s)) \<le> k \<Longrightarrow>
    vok L8 (rvec_elems (Search_watches s) ! unat k)\<close>
  unfolding sok_in_def sok_def using word64_not_le_of_nat nth_mem by blast

lemma Search_propagate_lit_spec:
  shows \<open>\<Gamma>; Search_propagate_lit r k \<Turnstile>\<^sub>F Search_propagate_lit_contract r g s k\<close>
  apply (crush_boot f: Search_propagate_lit_def contract: Search_propagate_lit_contract_def)
  apply (crush_base inline: NONE_def BIG_def mem_replace_def
      specs add: Search_move_watch_spec Search_skip_true_spec Search_other_key_spec close_gap_spec
      contracts add: Search_move_watch_contract_def Search_skip_true_contract_def
        Search_other_key_contract_def close_gap_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  apply (rename_tac ws_ref confl_ref i_ref j_ref)
  apply (ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>_. \<Squnion>gs s' gw w gc c gi i gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> ws_ref \<mapsto>\<langle>\<top>\<rangle> gw\<down>w \<star>
             confl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>sok s' \<and> vok L8 w\<rangle>\<close> and
      INV'=\<open>\<lambda>_. \<Squnion>gs s' gw w gc c gi i gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> ws_ref \<mapsto>\<langle>\<top>\<rangle> gw\<down>w \<star>
             confl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>sok s' \<and> vok L8 w \<and> i < word64_of_nat (rvec_length w)\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>)
  apply (crush_base inline: NONE_def BIG_def mem_replace_def
      specs add: Search_move_watch_spec Search_skip_true_spec Search_other_key_spec close_gap_spec
      contracts add: Search_move_watch_contract_def Search_skip_true_contract_def
        Search_other_key_contract_def close_gap_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  apply (all \<open>(node_bound; fail)?\<close>)
  apply (all \<open>(erule sok_watch_new; fail)?\<close>)
  apply (all \<open>(erule (1) sok_watch_get; fail)?\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>_. \<Squnion>gw w gi i gj j. ws_ref \<mapsto>\<langle>\<top>\<rangle> gw\<down>w \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
             j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star> \<langle>vok L8 w\<rangle>\<close> and
      INV'=\<open>\<lambda>_. \<Squnion>gw w gi i gj j. ws_ref \<mapsto>\<langle>\<top>\<rangle> gw\<down>w \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star>
             j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>vok L8 w \<and> i < word64_of_nat (rvec_length w) \<and> j < i\<rangle>\<close> and
      BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>\<close>)
  apply (crush_base inline: NONE_def BIG_def mem_replace_def
      specs add: Search_move_watch_spec Search_skip_true_spec Search_other_key_spec close_gap_spec
      contracts add: Search_move_watch_contract_def Search_skip_true_contract_def
        Search_other_key_contract_def close_gap_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  apply (all \<open>(node_bound; fail)?\<close>)
  sorry


definition Search_propagate_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_propagate_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_propagate_spec:
  shows \<open>\<Gamma>; Search_propagate r \<Turnstile>\<^sub>F Search_propagate_contract r g s\<close>
  apply (crush_boot f: Search_propagate_def contract: Search_propagate_contract_def)
  apply (crush_base inline: NONE_def simp add: true_def false_def)
  apply (ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>k. \<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> can_alloc_reference \<star> \<langle>sok s'\<rangle>\<close> and
      INV'=\<open>\<lambda>k. \<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> can_alloc_reference \<star>
             \<langle>sok s' \<and> Search_qhead s' < word64_of_nat (rvec_length (Search_trail s'))\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>)\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>)
  apply (crush_base inline: NONE_def
      specs add: key_spec Search_propagate_lit_spec
      contracts add: key_contract_def Search_propagate_lit_contract_def
      simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(auto simp add: sok_def sok_in_def; fail)?\<close>)
  sorry

(*CUT*)
definition Search_rescale_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_rescale_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_rescale_spec:
  shows \<open>\<Gamma>; Search_rescale r \<Turnstile>\<^sub>F Search_rescale_contract r g s\<close>
  apply (crush_boot f: Search_rescale_def contract: Search_rescale_contract_def)
  apply (crush_base simp add: true_def false_def rvec_elems_focus_modify)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star> \<langle>sok s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>sok s' \<and> i < word64_of_nat (rvec_length (Search_act s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: NONE_def simp add: true_def false_def rvec_elems_focus_modify)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_prev_seen_contract :: \<open>Search \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_prev_seen_contract s i \<equiv> make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma Search_prev_seen_spec:
  shows \<open>\<Gamma>; Search_prev_seen s i \<Turnstile>\<^sub>F Search_prev_seen_contract s i\<close>
  apply (crush_boot f: Search_prev_seen_def contract: Search_prev_seen_contract_def)
  apply (crush_base inline: NONE_def simp add: true_def false_def rvec_elems_focus_modify)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g j. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>j \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g j. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>j \<star> can_alloc_reference \<star> \<langle>0 < j\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. can_alloc_reference\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: NONE_def simp add: true_def false_def rvec_elems_focus_modify)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_pick_contract :: \<open>Search \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_pick_contract s \<equiv> make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma Search_pick_spec:
  shows \<open>\<Gamma>; Search_pick s \<Turnstile>\<^sub>F Search_pick_contract s\<close>
  apply (crush_boot f: Search_pick_def contract: Search_pick_contract_def)
  apply (crush_base inline: NONE_def simp add: true_def false_def rvec_elems_focus_modify)
  subgoal for best_ref best_act_ref v_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gb b ga a gv v. best_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>b \<star> best_act_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a \<star>
               v_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gb b ga a gv v. best_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>b \<star> best_act_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a \<star>
               v_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> can_alloc_reference \<star> \<langle>v < word64_of_nat (rvec_length (Search_set s))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: NONE_def simp add: true_def false_def rvec_elems_focus_modify)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_backtrack_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_backtrack_contract r g s lvl \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_backtrack_spec:
  shows \<open>\<Gamma>; Search_backtrack r lvl \<Turnstile>\<^sub>F Search_backtrack_contract r g s lvl\<close>
  apply (crush_boot f: Search_backtrack_def contract: Search_backtrack_contract_def)
  apply (crush_base inline: NONE_def
      specs add: key_spec contracts add: key_contract_def simp add: true_def false_def rvec_elems_focus_modify)
  apply (ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>k. \<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> can_alloc_reference \<star> \<langle>sok s'\<rangle>\<close> and
      INV'=\<open>\<lambda>k. \<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> can_alloc_reference \<star>
             \<langle>sok s' \<and> rvec_elems (Search_lim s) ! unat lvl < word64_of_nat (rvec_length (Search_trail s'))\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>)
  apply (crush_base inline: NONE_def
      specs add: key_spec contracts add: key_contract_def simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done


definition Search_bump_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_bump_contract r g s v \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_bump_spec:
  shows \<open>\<Gamma>; Search_bump r v \<Turnstile>\<^sub>F Search_bump_contract r g s v\<close>
  apply (crush_boot f: Search_bump_def contract: Search_bump_contract_def)
  apply (crush_base inline: ACT_def specs add: Search_rescale_spec
      contracts add: Search_rescale_contract_def simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

text \<open>The vectors of a new search of \<open>n < 2^56\<close> variables fit their largest capacities.\<close>
lemma new_cap:
  assumes \<open>n < (0x100000000000000 :: 64 word)\<close>
  shows \<open>unat n \<le> rvec_cap_max L1\<close> \<open>unat n \<le> rvec_cap_max L8\<close>
    \<open>unat (2 * n) \<le> rvec_cap_max L1\<close> \<open>unat (2 * n) \<le> rvec_cap_max L24\<close>
    \<open>unat (n + 1) \<le> rvec_cap_max L8\<close>
  using assms by (simp_all add: word_less_nat_alt unat_word_ariths rvec_cap_max_def isize_max_def)

definition new_search_contract :: \<open>64 word \<Rightarrow> ('s, Search, 'abort) function_contract\<close> where
  \<open>new_search_contract n \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>n < 0x100000000000000\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>sok r\<rangle>)\<close>

lemma new_search_spec:
  shows \<open>\<Gamma>; new_search n \<Turnstile>\<^sub>F new_search_contract n\<close>
  apply (crush_boot f: new_search_def contract: new_search_contract_def)
  apply (crush_base inline: NONE_def simp add: true_def false_def)
  apply (all \<open>(simp add: new_cap; fail)?\<close>)
  apply (all \<open>search_bound?\<close>)
  apply (auto simp add: sok_def vok_new dest!: rvec_from_elem_val_Some(2))
  done

definition Search_clause_lbd_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause rvec \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_clause_lbd_contract r g s f L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s \<and> db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_clause_lbd_spec:
  shows \<open>\<Gamma>; Search_clause_lbd r f L c \<Turnstile>\<^sub>F Search_clause_lbd_contract r g s f L c\<close>
  apply (crush_boot f: Search_clause_lbd_def contract: Search_clause_lbd_contract_def)
  apply (crush_base inline: NONE_def
      specs add: clause_len_spec contracts add: clause_len_contract_def simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>rename_tac n n_ref j_ref\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>k. \<Squnion>gs s' gn cnt gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
             n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>cnt \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star> \<langle>sok s'\<rangle>\<close> and
      INV'=\<open>\<lambda>k. \<Squnion>gs s' gn cnt gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
             n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>cnt \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>sok s' \<and> j < n\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>\<close>)
  apply (crush_base inline: NONE_def
      specs add: lit_at_spec contracts add: lit_at_contract_def simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition Search_update_lbd_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause rvec \<Rightarrow> 64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_update_lbd_contract r g s f L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s \<and> db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_update_lbd_spec:
  shows \<open>\<Gamma>; Search_update_lbd r f L c \<Turnstile>\<^sub>F Search_update_lbd_contract r g s f L c\<close>
  apply (crush_boot f: Search_update_lbd_def contract: Search_update_lbd_contract_def)
  apply (crush_base specs add: Search_clause_lbd_spec
      contracts add: Search_clause_lbd_contract_def simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition Search_analyze_clause_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause rvec \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_analyze_clause_contract r g s f L c p cur \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s \<and> db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_analyze_clause_spec:
  shows \<open>\<Gamma>; Search_analyze_clause r f L c p cur \<Turnstile>\<^sub>F Search_analyze_clause_contract r g s f L c p cur\<close>
  apply (crush_boot f: Search_analyze_clause_def contract: Search_analyze_clause_contract_def)
  apply (crush_base inline: NONE_def BIG_def
      specs add: Search_update_lbd_spec clause_len_spec
      contracts add: Search_update_lbd_contract_def clause_len_contract_def simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>rename_tac n count_ref j_ref\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>k. \<Squnion>gs s' gc cnt gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
             count_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cnt \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star> \<langle>sok s'\<rangle>\<close> and
      INV'=\<open>\<lambda>k. \<Squnion>gs s' gc cnt gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
             count_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cnt \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>sok s' \<and> j < n\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>\<close>)
  apply (crush_base inline: NONE_def BIG_def
      specs add: lit_at_spec Search_bump_spec contracts add: lit_at_contract_def Search_bump_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition Search_finish_learnt_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_finish_learnt_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_finish_learnt_spec:
  shows \<open>\<Gamma>; Search_finish_learnt r \<Turnstile>\<^sub>F Search_finish_learnt_contract r g s\<close>
  apply (crush_boot f: Search_finish_learnt_def contract: Search_finish_learnt_contract_def)
  apply (crush_base inline: slice_swap_def simp add: true_def false_def rvec_elems_focus_modify)
  subgoal for best_ref bl_ref j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gb b gc c gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               best_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>b \<star> bl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star>
               can_alloc_reference \<star> \<langle>sok s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gb b gc c gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               best_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>b \<star> bl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star>
               can_alloc_reference \<star> \<langle>sok s' \<and> j < word64_of_nat (rvec_length (Search_learnt s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: slice_swap_def simp add: true_def false_def rvec_elems_focus_modify)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    apply (all \<open>(rule FalseE, rule swap_ok; assumption)?\<close>)
    done
  done

definition Search_copy_learnt_contract :: \<open>Search \<Rightarrow> ('s, Lit rvec, 'abort) function_contract\<close> where
  \<open>Search_copy_learnt_contract s \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>rvec_length r \<le> 4611686018427387904\<rangle>)\<close>

lemma Search_copy_learnt_spec:
  shows \<open>\<Gamma>; Search_copy_learnt s \<Turnstile>\<^sub>F Search_copy_learnt_contract s\<close>
  apply (crush_boot f: Search_copy_learnt_def contract: Search_copy_learnt_contract_def)
  apply (crush_base inline: BIG_def Lit_mk_def simp add: true_def false_def rvec_elems_focus_modify)
  subgoal for out_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>go out gi i. out_ref \<mapsto>\<langle>\<top>\<rangle> go\<down>out \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>vok L16 out \<and> rvec_length out \<le> 72057594037927936\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>go out gi i. out_ref \<mapsto>\<langle>\<top>\<rangle> go\<down>out \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>vok L16 out \<and> i < word64_of_nat (rvec_length (Search_learnt s)) \<and>
                word64_of_nat (rvec_length out) < 0x100000000000000\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: BIG_def Lit_mk_def simp add: true_def false_def rvec_elems_focus_modify)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_unmark_from_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_unmark_from_contract r g s i \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_unmark_from_spec:
  shows \<open>\<Gamma>; Search_unmark_from r i \<Turnstile>\<^sub>F Search_unmark_from_contract r g s i\<close>
  apply (crush_boot f: Search_unmark_from_def contract: Search_unmark_from_contract_def)
  apply (crush_base simp add: true_def false_def rvec_elems_focus_modify)
  subgoal for k_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gk kk. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> can_alloc_reference \<star> \<langle>sok s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gk kk. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> can_alloc_reference \<star>
               \<langle>sok s' \<and> kk < word64_of_nat (rvec_length (Search_learnt s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: true_def false_def rvec_elems_focus_modify)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_learnt_lbd_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_learnt_lbd_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_learnt_lbd_spec:
  shows \<open>\<Gamma>; Search_learnt_lbd r \<Turnstile>\<^sub>F Search_learnt_lbd_contract r g s\<close>
  apply (crush_boot f: Search_learnt_lbd_def contract: Search_learnt_lbd_contract_def)
  apply (crush_base inline: NONE_def simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>rename_tac n_ref j_ref\<close>)
  apply (all \<open>ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>k. \<Squnion>gs s' gn n gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
             n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star> \<langle>sok s'\<rangle>\<close> and
      INV'=\<open>\<lambda>k. \<Squnion>gs s' gn n gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
             n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
             \<langle>sok s' \<and> j < word64_of_nat (rvec_length (Search_learnt s'))\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>\<close>)
  apply (crush_base inline: NONE_def simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition init_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause rvec \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>init_contract r g s f L \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s \<and> db_small f L\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma init_spec:
  shows \<open>\<Gamma>; init r f L \<Turnstile>\<^sub>F init_contract r g s f L\<close>
  apply (crush_boot f: init_def contract: init_contract_def)
  apply (crush_base inline: NONE_def simp add: true_def false_def rvec_elems_focus_modify)
  subgoal for confl_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gc c gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> confl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star>
               i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star> \<langle>sok s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gc c gi i. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> confl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star>
               i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>sok s' \<and> i < word64_of_nat (length (cls f))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: NONE_def
        specs add: Search_attach_spec lit_at_spec Search_lit_false_spec Search_lit_true_spec
          Search_enqueue_spec
        contracts add: Search_attach_contract_def lit_at_contract_def Search_lit_false_contract_def
          Search_lit_true_contract_def Search_enqueue_contract_def
        simp add: true_def false_def rvec_elems_focus_modify)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

end

end
