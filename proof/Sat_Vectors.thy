theory Sat_Vectors
  imports Sat_Proof.Sat_Certify
begin

text \<open>The word lemmas and the vector invariant of the CDCL search of \<^verbatim>\<open>core/src/lib.rs\<close>
  (\<^verbatim>\<open>Sat_Search\<close>): the translation models a \<^verbatim>\<open>Vec\<close> as an \<^typ>\<open>'a rvec\<close> whose
  \<^verbatim>\<open>push\<close> panics on a capacity overflow, so the vectors that the search grows carry the
  invariant \<open>sok\<close>; the methods \<open>search_bound\<close>, \<open>node_bound\<close> and \<open>sok_tac\<close> close the goals
  that \<open>crush_base\<close> leaves.\<close>

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
  layouts of their element types, and the buffer of the marks of \<^verbatim>\<open>certify\<close> is well-formed.\<close>
definition sok :: \<open>Search \<Rightarrow> bool\<close> where
  \<open>sok s \<equiv> vok L8 (Search_trail s) \<and> vok L8 (Search_start s) \<and> vok L8 (Search_arena s) \<and>
     (\<forall>w \<in> set (rvec_elems (Search_watches s)). vok L8 w) \<and> vok L16 (Search_learnt s) \<and>
     vok L8 (Search_stack s) \<and> vok L8 (Search_toclear s) \<and> vok L8 (Search_lim s) \<and>
     vok L8 (Search_lbd s) \<and> vok L1 (Search_dead s) \<and> vok L8 (Search_hint s) \<and>
     rvec_wf (Search_marks s)\<close>

text \<open>The invariant in a precondition. \<open>crush_base\<close> would use a premise \<open>sok s\<close> to
  instantiate the \<open>sok ?s'\<close> of a postcondition before the points-to fixes \<open>?s'\<close>.\<close>
definition sok_in :: \<open>Search \<Rightarrow> bool\<close> where
  \<open>sok_in \<equiv> sok\<close>

text \<open>A goal \<open>sok_in s\<close> or \<open>sok s\<close> closed by a premise of either form.\<close>
method sok_asm = ((unfold sok_in_def)?, assumption)

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

end
