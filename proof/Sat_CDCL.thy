theory Sat_CDCL
  imports Sat_Proof.Sat_Partial
begin

text \<open>The contracts of the CDCL search of \<^verbatim>\<open>core/src/lib.rs\<close> (\<^verbatim>\<open>cdcl\<close> and the functions it
  calls). The search itself is not trusted: its functions only need to terminate without a panic,
  which they do because every index is checked before use and every loop is bounded by the fuel.
  Its answers rest on two checks: \<^verbatim>\<open>satisfies\<close> for a model, and \<^verbatim>\<open>certify\<close> for each learned
  clause, which must follow from the formula. A learned empty clause shows that the formula is
  unsatisfiable.\<close>

section \<open>The clause database\<close>

text \<open>The clause database: the formula's clauses followed by the learned ones.\<close>
definition db :: \<open>Formula \<Rightarrow> Clause list \<Rightarrow> Clause list\<close> where
  \<open>db f L \<equiv> Formula_clauses f @ L\<close>

text \<open>The learned clauses are few and short enough for 64-bit indices, and hold under every
  assignment that satisfies the formula.\<close>
definition learned_ok :: \<open>Formula \<Rightarrow> Clause list \<Rightarrow> bool\<close> where
  \<open>learned_ok f L \<equiv>
     length L \<le> 2^62 \<and> (\<forall>c \<in> set L. length (Clause_v0 c) \<le> 2^62) \<and>
     (\<forall>a. formula_sat a f \<longrightarrow> (\<forall>c \<in> set L. clause_sat a c))\<close>

text \<open>The formula has fewer than \<open>2^62\<close> clauses, and there are at most \<open>2^62\<close> learned
  clauses: indices of the clause database fit a \<^verbatim>\<open>usize\<close>. Every clause has fewer than \<open>2^63\<close>
  literals.\<close>
definition db_small :: \<open>Formula \<Rightarrow> Clause list \<Rightarrow> bool\<close> where
  \<open>db_small f L \<equiv> length (Formula_clauses f) < 2^62 \<and> length L \<le> 2^62 \<and>
     (\<forall>c \<in> set (db f L). length (Clause_v0 c) < 2^63)\<close>

section \<open>Words\<close>

lemma word64_less_of_nat:
  \<open>(x :: 64 word) < word64_of_nat n \<Longrightarrow> unat x < n\<close>
  by (metis le_unat_uoi linorder_not_le nat_less_le order_le_less_trans unat_mono word_less_nat_alt)

lemma word64_unat_less_max:
  assumes \<open>unat (x :: 64 word) < unat (y :: 64 word)\<close>
  shows \<open>unat x < 18446744073709551615\<close>
proof -
  have \<open>unat y < 2 ^ 64\<close>
    using unat_lt2p[of y] by simp
  then show ?thesis
    using assms by simp
qed

lemma word64_less_max:
  \<open>(x :: 64 word) < y \<Longrightarrow> unat x < 18446744073709551615\<close>
  using word64_unat_less_max word_less_nat_alt by blast

lemma len_word_f:
  assumes \<open>\<forall>c \<in> set (Formula_clauses f) \<union> set L. length (Clause_v0 c) < 9223372036854775808\<close>
    \<open>i < length (Formula_clauses f)\<close>
  shows \<open>unat (word64_of_nat (length (Clause_v0 (Formula_clauses f ! i)))) =
    length (Clause_v0 (Formula_clauses f ! i))\<close>
proof -
  have \<open>length (Clause_v0 (Formula_clauses f ! i)) < 9223372036854775808\<close>
    using assms(1) nth_mem[OF assms(2)] by blast
  then have \<open>length (Clause_v0 (Formula_clauses f ! i)) < 2 ^ 64\<close>
    by simp
  then show ?thesis
    by (simp add: unat_of_nat_eq)
qed

lemma len_word_L:
  assumes \<open>\<forall>c \<in> set (Formula_clauses f) \<union> set L. length (Clause_v0 c) < 9223372036854775808\<close>
    \<open>i < length L\<close>
  shows \<open>unat (word64_of_nat (length (Clause_v0 (L ! i)))) = length (Clause_v0 (L ! i))\<close>
proof -
  have \<open>length (Clause_v0 (L ! i)) < 9223372036854775808\<close>
    using assms(1) nth_mem[OF assms(2)] by blast
  then have \<open>length (Clause_v0 (L ! i)) < 2 ^ 64\<close>
    by simp
  then show ?thesis
    by (simp add: unat_of_nat_eq)
qed

lemma mark_upd:
  assumes \<open>\<forall>v < length fo. fo ! v \<longrightarrow> (\<exists>l \<in> set xs. unat (Lit_var l) = v)\<close> \<open>k < length xs\<close>
    \<open>v < length fo\<close> \<open>fo[unat (Lit_var (xs ! k)) := True] ! v\<close>
  shows \<open>\<exists>l \<in> set xs. unat (Lit_var l) = v\<close>
proof (cases \<open>v = unat (Lit_var (xs ! k))\<close>)
  case True
  then show ?thesis
    using nth_mem[OF assms(2)] by blast
next
  case False
  then show ?thesis
    using assms(1,3,4) by simp
qed

lemma word64_less_of_nat_2:
  \<open>(x :: 64 word) < 2 + word64_of_nat n \<Longrightarrow> unat x < Suc (Suc n)\<close>
  using word64_less_of_nat[of x \<open>Suc (Suc n)\<close>] by (simp add: add.commute)

text \<open>Below \<open>2^62\<close>, \<open>2c\<close> and \<open>2c + 1\<close> do not overflow.\<close>
lemma big_c:
  assumes \<open>c < (0x4000000000000000 :: 64 word)\<close>
  shows \<open>unat c < 4611686018427387904\<close> \<open>unat (2 * c) = 2 * unat c\<close>
    \<open>unat (2 * c + 1) = 2 * unat c + 1\<close>
proof -
  show c: \<open>unat c < 4611686018427387904\<close>
    using assms by (simp add: word_less_nat_alt)
  then show m: \<open>unat (2 * c) = 2 * unat c\<close>
    by (simp add: unat_word_ariths)
  then show \<open>unat (2 * c + 1) = 2 * unat c + 1\<close>
    using c by (simp add: unat_word_ariths)
qed

lemma len_minus_one:
  assumes \<open>(x :: 64 word) < word64_of_nat n\<close>
  shows \<open>unat (word64_of_nat n - 1) < n\<close>
proof -
  have nz: \<open>word64_of_nat n \<noteq> 0\<close>
    using assms by auto
  have \<open>unat (word64_of_nat n - 1) = unat (word64_of_nat n) - 1\<close>
    using nz by (simp add: unat_minus_one)
  moreover have \<open>unat (word64_of_nat n) \<le> n\<close>
    by (simp add: unat_of_nat)
  moreover have \<open>0 < unat (word64_of_nat n)\<close>
    using nz by (simp add: unat_gt_0)
  ultimately show ?thesis
    by linarith
qed

lemma drop30:
  \<open>unat (drop_bit 30 (x :: 64 word)) < 18446744073709551615\<close>
proof -
  have \<open>unat (drop_bit 30 x) = unat x div 2 ^ 30\<close>
    unfolding unat_drop_bit_eq by (simp add: drop_bit_eq_div)
  moreover have \<open>unat x < 2 ^ 64\<close>
    using unat_lt2p[of x] by simp
  ultimately show ?thesis
    by simp
qed

lemma add_big:
  assumes \<open>a < (0x4000000000000000 :: 64 word)\<close> \<open>b < (0x4000000000000000 :: 64 word)\<close>
  shows \<open>unat a + unat b < 18446744073709551616\<close>
  using big_c(1)[OF assms(1)] big_c(1)[OF assms(2)] by linarith

lemma unat_of_nat_small:
  \<open>n < 2^62 \<Longrightarrow> unat (word64_of_nat n) = n\<close>
  by (simp add: unat_of_nat_eq)

section \<open>Certified learned clauses\<close>

text \<open>Clause \<open>c\<close> of the clause database exists, and each of its literals (other than \<open>(v, b)\<close>
  if \<open>sk\<close>) has a marked variable and is false under \<open>assign\<close>: the result of
  \<^verbatim>\<open>reason_ok\<close>.\<close>
definition reason_holds :: \<open>Formula \<Rightarrow> Clause list \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> bool list \<Rightarrow>
    bool list \<Rightarrow> bool\<close> where
  \<open>reason_holds f L c sk v b assign fo \<equiv> c < length (db f L) \<and>
     (\<forall>l \<in> set (Clause_v0 (db f L ! c)). (sk \<and> Lit_var l = v \<and> Lit_value l = b) \<or>
        (unat (Lit_var l) < length fo \<and> unat (Lit_var l) < length assign \<and> fo ! unat (Lit_var l) \<and>
         assign ! unat (Lit_var l) \<noteq> Lit_value l))\<close>

text \<open>Every assignment that satisfies the clause database and \<open>X\<close> agrees with \<open>assign\<close> on the
  marked variables.\<close>
definition forced_sound :: \<open>Formula \<Rightarrow> Clause list \<Rightarrow> bool list \<Rightarrow> (bool list \<Rightarrow> bool) \<Rightarrow> bool list \<Rightarrow>
    bool\<close> where
  \<open>forced_sound f L assign X fo \<equiv>
     \<forall>a. (\<forall>c \<in> set (db f L). clause_sat a c) \<longrightarrow> X a \<longrightarrow> (\<forall>v < length fo. fo ! v \<longrightarrow> a ! v = assign ! v)\<close>

text \<open>The variables of the literals of \<open>learnt\<close>, false under \<open>assign\<close>, are forced by the
  negation of \<open>learnt\<close>.\<close>
lemma forced_sound_mark:
  assumes \<open>\<forall>v < length fo. fo ! v \<longrightarrow> (\<exists>l \<in> set learnt. unat (Lit_var l) = v)\<close>
    and \<open>\<forall>l \<in> set learnt. unat (Lit_var l) < length assign \<and> assign ! unat (Lit_var l) \<noteq> Lit_value l\<close>
  shows \<open>forced_sound f L assign (\<lambda>a. \<forall>l \<in> set learnt. \<not> lit_sat a l) fo\<close>
  unfolding forced_sound_def
proof (intro allI impI)
  fix a v
  assume x: \<open>\<forall>l \<in> set learnt. \<not> lit_sat a l\<close> and v: \<open>v < length fo\<close> and fv: \<open>fo ! v\<close>
  obtain l where l: \<open>l \<in> set learnt\<close> \<open>unat (Lit_var l) = v\<close>
    using assms(1) v fv by blast
  have \<open>a ! v \<noteq> Lit_value l\<close> \<open>assign ! v \<noteq> Lit_value l\<close>
    using x assms(2) l unfolding lit_sat_def by auto
  then show \<open>a ! v = assign ! v\<close>
    by (cases \<open>Lit_value l\<close>) auto
qed

text \<open>A reason clause whose other literals are forced and false forces its variable.\<close>
lemma forced_sound_step:
  assumes fs: \<open>forced_sound f L assign X fo\<close> and v: \<open>unat v < length fo\<close>
    and r: \<open>reason_holds f L c True v (assign ! unat v) assign fo\<close>
  shows \<open>forced_sound f L assign X (fo[unat v := True])\<close>
  unfolding forced_sound_def
proof (intro allI impI)
  fix a w
  assume sat: \<open>\<forall>c \<in> set (db f L). clause_sat a c\<close> and x: \<open>X a\<close>
    and w: \<open>w < length (fo[unat v := True])\<close> and fw: \<open>fo[unat v := True] ! w\<close>
  have old: \<open>\<forall>u < length fo. fo ! u \<longrightarrow> a ! u = assign ! u\<close>
    using fs sat x unfolding forced_sound_def by blast
  have c: \<open>c < length (db f L)\<close>
    using r unfolding reason_holds_def by blast
  have lits: \<open>\<forall>l \<in> set (Clause_v0 (db f L ! c)). (Lit_var l = v \<and> Lit_value l = assign ! unat v) \<or>
      (unat (Lit_var l) < length fo \<and> fo ! unat (Lit_var l) \<and> assign ! unat (Lit_var l) \<noteq> Lit_value l)\<close>
    using r unfolding reason_holds_def by blast
  have \<open>clause_sat a (db f L ! c)\<close>
    using sat c by simp
  then obtain l where l: \<open>l \<in> set (Clause_v0 (db f L ! c))\<close> \<open>lit_sat a l\<close>
    unfolding clause_sat_def by blast
  have av: \<open>a ! unat v = assign ! unat v\<close>
  proof (cases \<open>Lit_var l = v \<and> Lit_value l = assign ! unat v\<close>)
    case True
    then show ?thesis
      using l(2) unfolding lit_sat_def by auto
  next
    case False
    then have \<open>unat (Lit_var l) < length fo \<and> fo ! unat (Lit_var l) \<and> assign ! unat (Lit_var l) \<noteq> Lit_value l\<close>
      using lits l(1) by blast
    then have \<open>a ! unat (Lit_var l) \<noteq> Lit_value l\<close>
      using old by auto
    then show ?thesis
      using l(2) unfolding lit_sat_def by simp
  qed
  show \<open>a ! w = assign ! w\<close>
  proof (cases \<open>w = unat v\<close>)
    case True
    then show ?thesis using av by simp
  next
    case False
    then show ?thesis using old w fw by simp
  qed
qed

text \<open>If the marked variables falsify clause \<open>c\<close>, no assignment satisfies the clause database and
  falsifies \<open>learnt\<close>: \<open>learnt\<close> follows from the clause database.\<close>
lemma certify_sound:
  assumes fs: \<open>forced_sound f L assign (\<lambda>a. \<forall>l \<in> set learnt. \<not> lit_sat a l) fo\<close>
    and r: \<open>reason_holds f L c False v b assign fo\<close>
  shows \<open>\<forall>a. (\<forall>c \<in> set (db f L). clause_sat a c) \<longrightarrow> (\<exists>l \<in> set learnt. lit_sat a l)\<close>
proof (intro allI impI)
  fix a
  assume sat: \<open>\<forall>c \<in> set (db f L). clause_sat a c\<close>
  show \<open>\<exists>l \<in> set learnt. lit_sat a l\<close>
  proof (rule ccontr)
    assume \<open>\<not> (\<exists>l \<in> set learnt. lit_sat a l)\<close>
    then have x: \<open>\<forall>l \<in> set learnt. \<not> lit_sat a l\<close>
      by blast
    have old: \<open>\<forall>u < length fo. fo ! u \<longrightarrow> a ! u = assign ! u\<close>
      using fs sat x unfolding forced_sound_def by blast
    have c: \<open>c < length (db f L)\<close>
      using r unfolding reason_holds_def by blast
    have lits: \<open>\<forall>l \<in> set (Clause_v0 (db f L ! c)).
        unat (Lit_var l) < length fo \<and> fo ! unat (Lit_var l) \<and> assign ! unat (Lit_var l) \<noteq> Lit_value l\<close>
      using r unfolding reason_holds_def by blast
    have \<open>clause_sat a (db f L ! c)\<close>
      using sat c by simp
    then obtain l where l: \<open>l \<in> set (Clause_v0 (db f L ! c))\<close> \<open>lit_sat a l\<close>
      unfolding clause_sat_def by blast
    have \<open>a ! unat (Lit_var l) \<noteq> Lit_value l\<close>
      using lits l(1) old by auto
    then show False
      using l(2) unfolding lit_sat_def by simp
  qed
qed

lemma db_sat:
  \<open>learned_ok f L \<Longrightarrow> formula_sat a f \<Longrightarrow> \<forall>c \<in> set (db f L). clause_sat a c\<close>
  unfolding learned_ok_def db_def formula_sat_def by auto

text \<open>A certified clause may be learned.\<close>
lemma learned_ok_push:
  assumes ok: \<open>learned_ok f L\<close> and n: \<open>length L < 2^62\<close> and len: \<open>length learnt \<le> 2^62\<close>
    and cert: \<open>\<forall>a. (\<forall>c \<in> set (db f L). clause_sat a c) \<longrightarrow> (\<exists>l \<in> set learnt. lit_sat a l)\<close>
  shows \<open>learned_ok f (L @ [make_Clause learnt])\<close>
proof -
  have \<open>clause_sat a (make_Clause learnt)\<close> if \<open>formula_sat a f\<close> for a
    using cert db_sat[OF ok that] unfolding clause_sat_def by simp
  then show ?thesis
    using ok n len unfolding learned_ok_def by auto
qed

text \<open>A certified empty clause: the formula is unsatisfiable.\<close>
lemma learned_ok_unsat:
  assumes \<open>learned_ok f L\<close>
    and \<open>\<forall>a. (\<forall>c \<in> set (db f L). clause_sat a c) \<longrightarrow> (\<exists>l \<in> set ([] :: Lit list). lit_sat a l)\<close>
  shows \<open>\<not> formula_sat a f\<close>
  using assms db_sat by fastforce

text \<open>The result of \<^verbatim>\<open>cdcl\<close>: \<^verbatim>\<open>None\<close>, or an answer as in the contract of the solver.\<close>
definition cdcl_post :: \<open>Formula \<Rightarrow> Answer option \<Rightarrow> bool\<close> where
  \<open>cdcl_post f r \<equiv> case r of
       None \<Rightarrow> True
     | Some (Answer_Sat x) \<Rightarrow>
         length (Assignments_v0 x) = unat (Formula_num_vars f) \<and> formula_sat (Assignments_v0 x) f
     | Some Answer_Unsat \<Rightarrow> (\<forall>a. length a = unat (Formula_num_vars f) \<longrightarrow> \<not> formula_sat a f)\<close>

context Sat_ctx
begin

section \<open>Accessors of the clause database\<close>

definition clause_len_contract :: \<open>Formula \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>clause_len_contract f L c \<equiv>
     let pre = can_alloc_reference \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>unat c < length (db f L) \<longrightarrow> r = word64_of_nat (length (Clause_v0 (db f L ! unat c)))\<rangle> in
     make_function_contract pre post\<close>

lemma clause_len_spec:
  shows \<open>\<Gamma>; clause_len f L c \<Turnstile>\<^sub>F clause_len_contract f L c\<close>
  apply (crush_boot f: clause_len_def contract: clause_len_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  using word64_less_of_nat apply (auto simp add: db_def db_small_def nth_append word_less_nat_alt
      unat_of_nat_eq unat_sub word_le_nat_alt not_less)
  done

definition lit_at_contract :: \<open>Formula \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, Lit, 'abort) function_contract\<close> where
  \<open>lit_at_contract f L c j \<equiv>
     let pre = can_alloc_reference \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>unat c < length (db f L) \<longrightarrow> unat j < length (Clause_v0 (db f L ! unat c)) \<longrightarrow>
         r = Clause_v0 (db f L ! unat c) ! unat j\<rangle> in
     make_function_contract pre post\<close>

lemma lit_at_spec:
  shows \<open>\<Gamma>; lit_at f L c j \<Turnstile>\<^sub>F lit_at_contract f L c j\<close>
  apply (crush_boot f: lit_at_def contract: lit_at_contract_def)
  apply (crush_base inline: len_def Lit_mk_def NONE_def simp add: true_def false_def)
  using word64_less_of_nat apply (auto simp add: db_def db_small_def nth_append word_less_nat_alt
      unat_of_nat_eq unat_sub word_le_nat_alt not_less Lit.expand len_word_f len_word_L)
  done

definition clause_exists_contract :: \<open>Formula \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>clause_exists_contract f L c \<equiv>
     let pre = can_alloc_reference \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r \<longrightarrow> unat c < length (db f L)\<rangle> in
     make_function_contract pre post\<close>

lemma clause_exists_spec:
  shows \<open>\<Gamma>; clause_exists f L c \<Turnstile>\<^sub>F clause_exists_contract f L c\<close>
  apply (crush_boot f: clause_exists_def contract: clause_exists_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  using word64_less_of_nat apply (auto simp add: db_def db_small_def word_less_nat_alt
      unat_of_nat_eq unat_sub word_le_nat_alt not_less)
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

section \<open>The checks\<close>

definition all_false_contract :: \<open>Lit list \<Rightarrow> bool list \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>all_false_contract learnt assign \<equiv>
     let pre = can_alloc_reference \<star> \<langle>length learnt \<le> 2^62\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>r \<longrightarrow> (\<forall>l \<in> set learnt. unat (Lit_var l) < length assign \<and>
                  assign ! unat (Lit_var l) \<noteq> Lit_value l)\<rangle> in
     make_function_contract pre post\<close>

lemma all_false_spec:
  shows \<open>\<Gamma>; all_false learnt assign \<Turnstile>\<^sub>F all_false_contract learnt assign\<close>
  apply (crush_boot f: all_false_def contract: all_false_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length learnt \<and>
                (\<forall>j < unat i. unat (Lit_var (learnt ! j)) < length assign \<and>
                   assign ! unat (Lit_var (learnt ! j)) \<noteq> Lit_value (learnt ! j))\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length learnt \<and>
                (\<forall>j < unat i. unat (Lit_var (learnt ! j)) < length assign \<and>
                   assign ! unat (Lit_var (learnt ! j)) \<noteq> Lit_value (learnt ! j))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
               \<langle>r \<longrightarrow> (\<forall>l \<in> set learnt. unat (Lit_var l) < length assign \<and>
                  assign ! unat (Lit_var l) \<noteq> Lit_value l)\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: true_def false_def word_less_nat_alt word_le_nat_alt unat_of_nat_eq
        unat_word_Suc_simp)
    using word64_less_of_nat apply (auto simp add: less_Suc_eq in_set_conv_nth unat_of_nat_eq
        word_less_nat_alt word_le_nat_alt)
    done
  done

definition mark_contract :: \<open>Lit list \<Rightarrow> 64 word \<Rightarrow> ('s, bool list, 'abort) function_contract\<close> where
  \<open>mark_contract learnt n \<equiv>
     let pre = can_alloc_reference in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>\<forall>v < length r. r ! v \<longrightarrow> (\<exists>l \<in> set learnt. unat (Lit_var l) = v)\<rangle> in
     make_function_contract pre post\<close>

lemma mark_spec:
  shows \<open>\<Gamma>; mark learnt n \<Turnstile>\<^sub>F mark_contract learnt n\<close>
  apply (crush_boot f: mark_def contract: mark_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for forced_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gf fo g i. forced_ref \<mapsto>\<langle>\<top>\<rangle> gf\<down>fo \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>\<forall>v < length fo. fo ! v \<longrightarrow> (\<exists>l \<in> set learnt. unat (Lit_var l) = v)\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gf fo g i. forced_ref \<mapsto>\<langle>\<top>\<rangle> gf\<down>fo \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>i < word64_of_nat (length learnt) \<and>
                (\<forall>v < length fo. fo ! v \<longrightarrow> (\<exists>l \<in> set learnt. unat (Lit_var l) = v))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: true_def false_def)
    apply (auto simp add: word64_less_of_nat intro: word64_less_max)
    apply (metis mark_upd word64_less_of_nat)
    done
  done

definition reason_ok_contract :: \<open>Formula \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow>
    bool list \<Rightarrow> bool list \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>reason_ok_contract f L c sk v b assign fo \<equiv>
     let pre = can_alloc_reference \<star> \<langle>db_small f L\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r \<longrightarrow> reason_holds f L (unat c) sk v b assign fo\<rangle> in
     make_function_contract pre post\<close>

text \<open>The literals of clause \<open>c\<close> before position \<open>j\<close> are as \<^const>\<open>reason_holds\<close> requires.\<close>
definition reason_upto :: \<open>Formula \<Rightarrow> Clause list \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> bool list \<Rightarrow>
    bool list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>reason_upto f L c sk v b assign fo j \<equiv>
     \<forall>i < j. let l = Clause_v0 (db f L ! c) ! i in (sk \<and> Lit_var l = v \<and> Lit_value l = b) \<or>
        (unat (Lit_var l) < length fo \<and> unat (Lit_var l) < length assign \<and> fo ! unat (Lit_var l) \<and>
         assign ! unat (Lit_var l) \<noteq> Lit_value l)\<close>

lemma reason_upto_holds:
  \<open>c < length (db f L) \<Longrightarrow> reason_upto f L c sk v b assign fo (length (Clause_v0 (db f L ! c))) \<Longrightarrow>
    reason_holds f L c sk v b assign fo\<close>
  unfolding reason_upto_def reason_holds_def Let_def by (metis in_set_conv_nth)

lemma reason_upto_Suc:
  \<open>reason_upto f L c sk v b assign fo j \<Longrightarrow>
    (let l = Clause_v0 (db f L ! c) ! j in (sk \<and> Lit_var l = v \<and> Lit_value l = b) \<or>
        (unat (Lit_var l) < length fo \<and> unat (Lit_var l) < length assign \<and> fo ! unat (Lit_var l) \<and>
         assign ! unat (Lit_var l) \<noteq> Lit_value l)) \<Longrightarrow>
    reason_upto f L c sk v b assign fo (Suc j)\<close>
  unfolding reason_upto_def by (auto simp add: less_Suc_eq)

lemma db_succ:
  assumes \<open>unat (j :: 64 word) < length (Clause_v0 (db f L ! c))\<close> \<open>c < length (db f L)\<close>
    \<open>\<forall>c \<in> set (db f L). length (Clause_v0 c) < 9223372036854775808\<close>
  shows \<open>unat (j + 1) = Suc (unat j)\<close>
proof -
  have \<open>length (Clause_v0 (db f L ! c)) < 9223372036854775808\<close>
    using assms(2,3) nth_mem by blast
  then show ?thesis
    using assms(1) unat_word_Suc_simp[of j] by simp
qed

lemma reason_upto_0:
  \<open>reason_upto f L c sk v b assign fo 0\<close>
  unfolding reason_upto_def by simp

lemma reason_upto_end:
  assumes \<open>c < length (db f L)\<close> \<open>\<forall>c \<in> set (db f L). length (Clause_v0 c) < 9223372036854775808\<close>
    \<open>unat j \<le> length (Clause_v0 (db f L ! c))\<close>
    \<open>unat (word64_of_nat (length (Clause_v0 (db f L ! c)))) \<le> unat (j :: 64 word)\<close>
    \<open>reason_upto f L c sk v b assign fo (unat j)\<close>
  shows \<open>reason_holds f L c sk v b assign fo\<close>
proof -
  have \<open>length (Clause_v0 (db f L ! c)) < 9223372036854775808\<close>
    using assms(1,2) nth_mem by blast
  then have \<open>unat (word64_of_nat (length (Clause_v0 (db f L ! c)))) = length (Clause_v0 (db f L ! c))\<close>
    by (simp add: unat_of_nat_eq)
  then have \<open>unat j = length (Clause_v0 (db f L ! c))\<close>
    using assms(3,4) by simp
  then show ?thesis
    using reason_upto_holds[OF assms(1)] assms(5) by simp
qed

lemma reason_ok_spec:
  shows \<open>\<Gamma>; reason_ok f L c sk v b assign fo \<Turnstile>\<^sub>F reason_ok_contract f L c sk v b assign fo\<close>
  apply (crush_boot f: reason_ok_def contract: reason_ok_contract_def)
  apply (crush_base inline: len_def
      specs add: clause_exists_spec clause_len_spec
      contracts add: clause_exists_contract_def clause_len_contract_def
      simp add: true_def false_def)
  subgoal for x j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g j. j_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat j \<le> length (Clause_v0 (db f L ! unat c)) \<and>
                length (Clause_v0 (db f L ! unat c)) < 2^63 \<and> unat c < length (db f L) \<and>
                reason_upto f L (unat c) sk v b assign fo (unat j)\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g j. j_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>j \<star> can_alloc_reference \<star>
               \<langle>unat j < length (Clause_v0 (db f L ! unat c)) \<and>
                length (Clause_v0 (db f L ! unat c)) < 2^63 \<and> unat c < length (db f L) \<and>
                reason_upto f L (unat c) sk v b assign fo (unat j)\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r \<longrightarrow> reason_holds f L (unat c) sk v b assign fo\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base specs add: lit_at_spec contracts add: lit_at_contract_def
        simp add: true_def false_def)
    apply (auto simp add: Let_def db_succ word64_less_of_nat word_le_nat_alt db_small_def
        unat_of_nat_eq reason_upto_0 intro: word64_less_max reason_upto_Suc reason_upto_end)
    done
  done

definition force_trail_contract :: \<open>Formula \<Rightarrow> Clause list \<Rightarrow> bool list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow>
    bool list \<Rightarrow> (bool list \<Rightarrow> bool) \<Rightarrow> ('s, bool list, 'abort) function_contract\<close> where
  \<open>force_trail_contract f L assign trail reason fo X \<equiv>
     let pre = can_alloc_reference \<star> \<langle>db_small f L \<and> forced_sound f L assign X fo\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>forced_sound f L assign X r\<rangle> in
     make_function_contract pre post\<close>

lemma force_trail_spec:
  shows \<open>\<Gamma>; force_trail f L assign trail reason fo \<Turnstile>\<^sub>F force_trail_contract f L assign trail reason fo X\<close>
  apply (crush_boot f: force_trail_def contract: force_trail_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for forced_ref j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gf fo' g j. forced_ref \<mapsto>\<langle>\<top>\<rangle> gf\<down>fo' \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>j \<star> can_alloc_reference \<star>
               \<langle>forced_sound f L assign X fo'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gf fo' g j. forced_ref \<mapsto>\<langle>\<top>\<rangle> gf\<down>fo' \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>j \<star> can_alloc_reference \<star>
               \<langle>j < word64_of_nat (length trail) \<and> forced_sound f L assign X fo'\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base specs add: reason_ok_spec contracts add: reason_ok_contract_def
        simp add: true_def false_def)
    apply (auto simp add: word64_less_of_nat intro: word64_less_max forced_sound_step)
    done
  done

definition certify_contract :: \<open>Formula \<Rightarrow> Clause list \<Rightarrow> bool list \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow>
    64 word \<Rightarrow> Lit list \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>certify_contract f L assign trail reason c learnt \<equiv>
     let pre = can_alloc_reference \<star> \<langle>db_small f L \<and> length learnt \<le> 2^62\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>r \<longrightarrow> (\<forall>a. (\<forall>c \<in> set (db f L). clause_sat a c) \<longrightarrow> (\<exists>l \<in> set learnt. lit_sat a l))\<rangle> in
     make_function_contract pre post\<close>

lemma certify_spec:
  shows \<open>\<Gamma>; certify f L assign trail reason c learnt \<Turnstile>\<^sub>F certify_contract f L assign trail reason c learnt\<close>
  apply (crush_boot f: certify_def contract: certify_contract_def)
  apply (crush_base inline: len_def
      specs add: all_false_spec mark_spec force_trail_spec[where X=\<open>\<lambda>a. \<forall>l \<in> set learnt. \<not> lit_sat a l\<close>]
        reason_ok_spec
      contracts add: all_false_contract_def mark_contract_def force_trail_contract_def reason_ok_contract_def
      simp add: true_def false_def)
  subgoal using certify_sound by blast
  subgoal by (rule forced_sound_mark) auto
  done

definition model_contract :: \<open>bool list \<Rightarrow> 64 word \<Rightarrow> ('s, bool list, 'abort) function_contract\<close> where
  \<open>model_contract assign n \<equiv>
     let pre = can_alloc_reference in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>length r = unat n\<rangle> in
     make_function_contract pre post\<close>

lemma model_spec:
  shows \<open>\<Gamma>; model assign n \<Turnstile>\<^sub>F model_contract assign n\<close>
  apply (crush_boot f: model_def contract: model_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for m_ref v_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gm m g v. m_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>m \<star> v_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> can_alloc_reference \<star>
               \<langle>length m = unat n\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gm m g v. m_ref \<mapsto>\<langle>\<top>\<rangle> gm\<down>m \<star> v_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> can_alloc_reference \<star>
               \<langle>v < n \<and> length m = unat n\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: true_def false_def)
    using word64_less_of_nat word64_unat_less_max apply (auto simp add: word_less_nat_alt)
    done
  done

definition clause_holds_contract :: \<open>Clause \<Rightarrow> bool list \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>clause_holds_contract c a \<equiv>
     let pre = can_alloc_reference in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r \<longrightarrow> clause_sat a c\<rangle> in
     make_function_contract pre post\<close>

lemma clause_holds_spec:
  shows \<open>\<Gamma>; clause_holds c a \<Turnstile>\<^sub>F clause_holds_contract c a\<close>
  apply (crush_boot f: clause_holds_def contract: clause_holds_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g j. j_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>j \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g j. j_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>j \<star> can_alloc_reference \<star>
               \<langle>j < word64_of_nat (length (Clause_v0 c))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r \<longrightarrow> clause_sat a c\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: true_def false_def)
    using word64_less_of_nat word64_unat_less_max
    apply (auto simp add: clause_sat_def lit_sat_def word_less_nat_alt)
    done
  done

definition satisfies_contract :: \<open>Formula \<Rightarrow> bool list \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>satisfies_contract f a \<equiv>
     let pre = can_alloc_reference \<star> \<langle>length (Formula_clauses f) < 2^64\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r \<longrightarrow> formula_sat a f\<rangle> in
     make_function_contract pre post\<close>

lemma satisfies_spec:
  shows \<open>\<Gamma>; satisfies f a \<Turnstile>\<^sub>F satisfies_contract f a\<close>
  apply (crush_boot f: satisfies_def contract: satisfies_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length (Formula_clauses f) \<and>
                (\<forall>j < unat i. clause_sat a (Formula_clauses f ! j))\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length (Formula_clauses f) \<and>
                (\<forall>j < unat i. clause_sat a (Formula_clauses f ! j))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r \<longrightarrow> formula_sat a f\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base specs add: clause_holds_spec contracts add: clause_holds_contract_def
        simp add: true_def false_def word_less_nat_alt word_le_nat_alt unat_of_nat_eq unat_word_Suc_simp)
    apply (auto simp add: less_Suc_eq formula_sat_iff_nth unat_of_nat_eq word_less_nat_alt word_le_nat_alt)
    done
  done

section \<open>The search\<close>

text \<open>The functions of the search only need to return without a panic. Those that read the state
  have the trivial postcondition; those that change it leave the reference pointing to some
  state.\<close>

definition Search_lit_true_contract :: \<open>Search \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>Search_lit_true_contract s v b \<equiv>
     make_function_contract (can_alloc_reference) (\<lambda>_. can_alloc_reference)\<close>

lemma Search_lit_true_spec:
  shows \<open>\<Gamma>; Search_lit_true s v b \<Turnstile>\<^sub>F Search_lit_true_contract s v b\<close>
  apply (crush_boot f: Search_lit_true_def contract: Search_lit_true_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def Lit_mk_def vec_push_def vec_pop_def vec_truncate_def slice_swap_def
      simp add: true_def false_def)
  using word64_less_of_nat apply auto
  done

definition Search_lit_false_contract :: \<open>Search \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>Search_lit_false_contract s v b \<equiv>
     make_function_contract (can_alloc_reference) (\<lambda>_. can_alloc_reference)\<close>

lemma Search_lit_false_spec:
  shows \<open>\<Gamma>; Search_lit_false s v b \<Turnstile>\<^sub>F Search_lit_false_contract s v b\<close>
  apply (crush_boot f: Search_lit_false_def contract: Search_lit_false_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def Lit_mk_def vec_push_def vec_pop_def vec_truncate_def slice_swap_def
      simp add: true_def false_def)
  using word64_less_of_nat apply auto
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
      simp add: true_def false_def)
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
  apply (all \<open>(drule word64_less_of_nat_2)?\<close>)
  apply (simp_all only: word64_less_of_nat big_c)
  apply (all \<open>(frule big_c(1))?, linarith\<close>)
  done


definition Search_find_watch_contract :: \<open>Search \<Rightarrow> Formula \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_find_watch_contract s f L c op my \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>db_small f L\<rangle>) (\<lambda>_. can_alloc_reference)\<close>

lemma Search_find_watch_spec:
  shows \<open>\<Gamma>; Search_find_watch s f L c op my \<Turnstile>\<^sub>F Search_find_watch_contract s f L c op my\<close>
  apply (crush_boot f: Search_find_watch_def contract: Search_find_watch_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def Lit_mk_def
      specs add: clause_len_spec lit_at_spec Search_lit_false_spec
      contracts add: clause_len_contract_def lit_at_contract_def Search_lit_false_contract_def
      simp add: true_def false_def)
  subgoal for x j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g j. j_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>j \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g j. j_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>j \<star> can_alloc_reference \<star> \<langle>j < x\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. can_alloc_reference\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base specs add: lit_at_spec Search_lit_false_spec
        contracts add: lit_at_contract_def Search_lit_false_contract_def simp add: true_def false_def)
    apply (all \<open>erule word64_less_max\<close>)
    done
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
  apply (crush_base inline: len_def NONE_def BIG_def Lit_mk_def
      specs add: clause_len_spec lit_at_spec key_spec Search_lit_true_spec Search_lit_false_spec
        Search_find_watch_spec Search_enqueue_spec
      contracts add: clause_len_contract_def lit_at_contract_def key_contract_def
        Search_lit_true_contract_def Search_lit_false_contract_def Search_find_watch_contract_def
        Search_enqueue_contract_def
      simp add: true_def false_def)
  subgoal for prev_ref node_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gp p gn n. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> prev_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star>
               node_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gp p gn n. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> prev_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star>
               node_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> can_alloc_reference \<star>
               \<langle>n < word64_of_nat (length (Search_next s')) \<and> n < word64_of_nat (length (Search_wpos s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s')\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def NONE_def BIG_def Lit_mk_def
        specs add: clause_len_spec lit_at_spec key_spec Search_lit_true_spec Search_lit_false_spec
          Search_find_watch_spec Search_enqueue_spec
        contracts add: clause_len_contract_def lit_at_contract_def key_contract_def
          Search_lit_true_contract_def Search_lit_false_contract_def Search_find_watch_contract_def
          Search_enqueue_contract_def
        simp add: true_def false_def)
    apply (all \<open>(simp only: word64_less_of_nat; fail) | erule word64_less_max\<close>)
    done
  subgoal for prev_ref node_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gp p gn n. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> prev_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star>
               node_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gp p gn n. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> prev_ref \<mapsto>\<langle>\<top>\<rangle> gp\<down>p \<star>
               node_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> can_alloc_reference \<star>
               \<langle>n < word64_of_nat (length (Search_next s')) \<and> n < word64_of_nat (length (Search_wpos s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s')\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def NONE_def BIG_def Lit_mk_def
        specs add: clause_len_spec lit_at_spec key_spec Search_lit_true_spec Search_lit_false_spec
          Search_find_watch_spec Search_enqueue_spec
        contracts add: clause_len_contract_def lit_at_contract_def key_contract_def
          Search_lit_true_contract_def Search_lit_false_contract_def Search_find_watch_contract_def
          Search_enqueue_contract_def
        simp add: true_def false_def)
    apply (all \<open>(simp only: word64_less_of_nat; fail) | erule word64_less_max\<close>)
    done
  subgoal by (simp add: word64_less_of_nat)
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
  apply (all \<open>(simp only: word64_less_of_nat; fail) | erule word64_less_max | erule len_minus_one | rule drop30 |
        (simp add: word_le_nat_alt word_less_nat_alt; fail) |
        (rule add_big; assumption) | (frule big_c(1), linarith)\<close>)
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
    apply (all \<open>(simp only: word64_less_of_nat; fail) | erule word64_less_max | erule len_minus_one | rule drop30 |
        (simp add: word_le_nat_alt word_less_nat_alt; fail) |
        (rule add_big; assumption) | (frule big_c(1), linarith)\<close>)
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
    apply (all \<open>(simp only: word64_less_of_nat; fail) | erule word64_less_max | erule len_minus_one | rule drop30 |
        (simp add: word_le_nat_alt word_less_nat_alt; fail) |
        (rule add_big; assumption) | (frule big_c(1), linarith)\<close>)
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
    apply (all \<open>(simp only: word64_less_of_nat; fail) | erule word64_less_max | erule len_minus_one | rule drop30 |
        (simp add: word_le_nat_alt word_less_nat_alt; fail) |
        (rule add_big; assumption) | (frule big_c(1), linarith)\<close>)
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
  apply (crush_base inline: len_def NONE_def vec_pop_def vec_truncate_def simp add: true_def false_def)
  apply (ucincl_discharge\<open>
    rule_tac
      INV=\<open>\<lambda>k. \<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> can_alloc_reference\<close> and
      INV'=\<open>\<lambda>k. \<Squnion>gs s'. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> can_alloc_reference \<star>
             \<langle>Search_lim s ! unat lvl < word64_of_nat (length (Search_trail s'))\<rangle>\<close> and
      \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
      \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_bounded_while_framedI\<close>)
  apply (crush_base inline: len_def NONE_def vec_pop_def vec_truncate_def simp add: true_def false_def)
  apply (all \<open>(simp only: word64_less_of_nat; fail) | erule word64_less_max | erule len_minus_one | rule drop30 |
        (simp add: word_le_nat_alt word_less_nat_alt; fail) |
        (rule add_big; assumption) | (frule big_c(1), linarith)\<close>)
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
  apply (all \<open>(simp only: word64_less_of_nat; fail) | erule word64_less_max | erule len_minus_one | rule drop30 |
        (simp add: word_le_nat_alt word_less_nat_alt; fail) |
        (rule add_big; assumption) | (frule big_c(1), linarith)\<close>)
  done

definition new_search_contract :: \<open>64 word \<Rightarrow> ('s, Search, 'abort) function_contract\<close> where
  \<open>new_search_contract n \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>n < 0x4000000000000000\<rangle>) (\<lambda>_. can_alloc_reference)\<close>

lemma new_search_spec:
  shows \<open>\<Gamma>; new_search n \<Turnstile>\<^sub>F new_search_contract n\<close>
  apply (crush_boot f: new_search_def contract: new_search_contract_def)
  apply (crush_base inline: NONE_def simp add: true_def false_def)
  apply (all \<open>(simp only: word64_less_of_nat; fail) | erule word64_less_max | erule len_minus_one | rule drop30 |
        (simp add: word_le_nat_alt word_less_nat_alt; fail) |
        (rule add_big; assumption) | (frule big_c(1), linarith)\<close>)
  done


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
    by linarith
qed

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
  subgoal for x count_ref j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gc cnt gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               count_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cnt \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gc cnt gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star>
               count_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cnt \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>j < x\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def NONE_def BIG_def vec_push_def
        specs add: lit_at_spec Search_bump_spec contracts add: lit_at_contract_def Search_bump_contract_def
        simp add: true_def false_def)
    apply (all \<open>((simp only: word64_less_of_nat; fail) | erule word64_less_max | erule len_minus_one | rule drop30 |
        (simp add: word_le_nat_alt word_less_nat_alt; fail) |
        (rule add_big; assumption) | (frule big_c(1), linarith) |
        erule nz_len | (rule push_len; assumption) | (erule counter_add) | (rule push_len'; assumption))?\<close>)
    sorry
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
    apply (all \<open>((simp only: word64_less_of_nat; fail) | erule word64_less_max | erule len_minus_one | rule drop30 |
        (simp add: word_le_nat_alt word_less_nat_alt; fail) |
        (rule add_big; assumption) | (frule big_c(1), linarith) |
        erule nz_len | (rule push_len; assumption) | (erule counter_add) | (rule push_len'; assumption))?\<close>)
    apply (all \<open>(rule FalseE, rule swap_ok; assumption)?\<close>)
    sorry
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
    apply (all \<open>((simp only: word64_less_of_nat; fail) | erule word64_less_max | erule len_minus_one | rule drop30 |
        (simp add: word_le_nat_alt word_less_nat_alt; fail) |
        (rule add_big; assumption) | (frule big_c(1), linarith) |
        erule nz_len | (rule push_len; assumption) | (erule counter_add) | (rule push_len'; assumption))?\<close>)
    sorry
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
          Search_copy_learnt_spec
        contracts add: Search_analyze_clause_contract_def Search_prev_seen_contract_def
          Search_finish_learnt_contract_def Search_copy_learnt_contract_def
        simp add: true_def false_def)
    apply (all \<open>((simp only: word64_less_of_nat; fail) | erule word64_less_max | erule len_minus_one | rule drop30 |
        (simp add: word_le_nat_alt word_less_nat_alt; fail) |
        (rule add_big; assumption) | (frule big_c(1), linarith) |
        erule nz_len | (rule push_len; assumption) | (erule counter_add) | (rule push_len'; assumption))?\<close>)
    sorry
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
    apply (all \<open>((simp only: word64_less_of_nat; fail) | erule word64_less_max | erule len_minus_one | rule drop30 |
        (simp add: word_le_nat_alt word_less_nat_alt; fail) |
        (rule add_big; assumption) | (frule big_c(1), linarith) |
        erule nz_len | (rule push_len; assumption) | (erule counter_add) | (rule push_len'; assumption))\<close>)
    done
  done

section \<open>The search with certified answers\<close>

text \<open>The facts about the clause database and the answers that the main loop of \<^verbatim>\<open>cdcl\<close> uses.\<close>

lemma learned_ok_Nil:
  \<open>learned_ok f []\<close>
  unfolding learned_ok_def by simp

lemma f_small:
  assumes \<open>sat_repr_ok f\<close> \<open>\<not> 0x4000000000000000 \<le> word64_of_nat (length (Formula_clauses f))\<close>
  shows \<open>length (Formula_clauses f) < 4611686018427387904\<close>
proof -
  have lf: \<open>length (Formula_clauses f) < 2 ^ 64\<close>
    using assms(1) unfolding sat_repr_ok_def by simp
  then have \<open>unat (word64_of_nat (length (Formula_clauses f))) = length (Formula_clauses f)\<close>
    by (simp add: unat_of_nat_eq)
  then show ?thesis
    using assms(2) by (simp add: word_le_nat_alt not_le)
qed

lemma db_small_of:
  assumes \<open>sat_repr_ok f\<close> \<open>length (Formula_clauses f) < 4611686018427387904\<close> \<open>learned_ok f L\<close>
  shows \<open>db_small f L\<close>
  using assms unfolding db_small_def db_def sat_repr_ok_def learned_ok_def by fastforce

lemma db_index_add:
  assumes \<open>length (Formula_clauses f) < 4611686018427387904\<close> \<open>length L < 4611686018427387904\<close>
  shows \<open>unat (word64_of_nat (length (Formula_clauses f))) + unat (word64_of_nat (length L))
    < 18446744073709551616\<close>
  using assms by (simp add: unat_of_nat_eq)

lemma learned_small:
  assumes \<open>learned_ok f L\<close> \<open>\<not> 0x4000000000000000 \<le> word64_of_nat (length L)\<close>
  shows \<open>length L < 4611686018427387904\<close>
proof -
  have \<open>length L < 2 ^ 64\<close>
    using assms(1) unfolding learned_ok_def by simp
  then have \<open>unat (word64_of_nat (length L)) = length L\<close>
    by (simp add: unat_of_nat_eq)
  then show ?thesis
    using assms(2) by (simp add: word_le_nat_alt not_le)
qed

lemma cdcl_post_None:
  \<open>cdcl_post f None\<close>
  unfolding cdcl_post_def by simp

lemma cdcl_post_Unsat:
  assumes \<open>learned_ok f L\<close>
    \<open>\<forall>a. (\<forall>c \<in> set (db f L). clause_sat a c) \<longrightarrow> (\<exists>l \<in> set ([] :: Lit list). lit_sat a l)\<close>
  shows \<open>cdcl_post f (Some Answer_Unsat)\<close>
  using learned_ok_unsat[OF assms] unfolding cdcl_post_def by simp

lemma cdcl_post_Sat:
  \<open>length m = unat (Formula_num_vars f) \<Longrightarrow> formula_sat m f \<Longrightarrow>
    cdcl_post f (Some (Answer_Sat (make_Assignments m)))\<close>
  unfolding cdcl_post_def by simp

lemma half_add:
  assumes \<open>x < (0x4000000000000000 :: 64 word)\<close>
  shows \<open>unat x + unat (x div 2) < 18446744073709551616\<close>
proof -
  have \<open>unat (x div 2) \<le> unat x\<close>
    by (simp add: unat_div)
  then show ?thesis
    using big_c(1)[OF assms] by linarith
qed


definition on_conflict_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> ('addr, 'gv, Clause list) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Clause list \<Rightarrow> 64 word \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>on_conflict_contract r g s f lref gl L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> lref \<mapsto>\<langle>\<top>\<rangle> gl\<down>L \<star>
        \<langle>sat_repr_ok f \<and> length (Formula_clauses f) < 4611686018427387904 \<and> learned_ok f L\<rangle> in
     let post = \<lambda>res. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s') \<star>
        (\<Squnion>gl' L'. lref \<mapsto>\<langle>\<top>\<rangle> gl'\<down>L' \<star>
           \<langle>learned_ok f L' \<and> (res = 1 \<longrightarrow> (\<forall>a. \<not> formula_sat a f))\<rangle>) in
     make_function_contract pre post\<close>

lemma on_conflict_spec:
  shows \<open>\<Gamma>; on_conflict r f lref c \<Turnstile>\<^sub>F on_conflict_contract r g s f lref gl L c\<close>
  apply (crush_boot f: on_conflict_def contract: on_conflict_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def vec_push_def Clause_mk_def
      specs add: certify_spec Search_analyze_spec Search_backtrack_spec Search_attach_spec
        Search_enqueue_spec
      contracts add: certify_contract_def Search_analyze_contract_def Search_backtrack_contract_def
        Search_attach_contract_def Search_enqueue_contract_def
      simp add: true_def false_def)
  sorry

definition cdcl_contract :: \<open>Formula \<Rightarrow> ('s, Answer option, 'abort) function_contract\<close> where
  \<open>cdcl_contract f \<equiv>
     let pre = can_alloc_reference \<star> \<langle>sat_repr_ok f\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>cdcl_post f r\<rangle> in
     make_function_contract pre post\<close>

lemma cdcl_spec:
  shows \<open>\<Gamma>; cdcl f \<Turnstile>\<^sub>F cdcl_contract f\<close>
  apply (crush_boot f: cdcl_def contract: cdcl_contract_def)
  apply (crush_base inline: len_def NONE_def BIG_def
      specs add: new_search_spec init_spec
      contracts add: new_search_contract_def init_contract_def
      simp add: true_def false_def)
  subgoal for x s_ref l_ref y g' z confl_ref k_ref rst_ref st_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gl L gc c gk kk gr rr gt t. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>L \<star>
               confl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> rst_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>rr \<star>
               st_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t \<star> can_alloc_reference \<star> \<langle>learned_ok f L\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gl L gc c gk kk gr rr gt t. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>L \<star>
               confl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>kk \<star> rst_ref \<mapsto>\<langle>\<top>\<rangle> gr\<down>rr \<star>
               st_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t \<star> can_alloc_reference \<star>
               \<langle>learned_ok f L \<and> t < 0xFFFFFFFFFFFFFFFF\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>cdcl_post f r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def NONE_def BIG_def vec_push_def Answer_Sat_mk_def Assignments_mk_def
        specs add: Search_propagate_spec on_conflict_spec Search_backtrack_spec Search_enqueue_spec
          Search_pick_spec model_spec satisfies_spec
        contracts add: Search_propagate_contract_def on_conflict_contract_def Search_backtrack_contract_def
          Search_enqueue_contract_def Search_pick_contract_def model_contract_def satisfies_contract_def
        simp add: true_def false_def)
    sorry
  sorry

end

end
