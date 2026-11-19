theory Sat_Certify
  imports Sat_Proof.Sat_Partial
begin

text \<open>The checks on which the answers of the CDCL search of \<^verbatim>\<open>core/src/lib.rs\<close> rest:
  \<^verbatim>\<open>satisfies\<close> for a model, and \<^verbatim>\<open>certify\<close> for each learned clause, which must follow from the
  formula. A learned empty clause shows that the formula is unsatisfiable. The search itself is in
  \<^verbatim>\<open>Sat_CDCL\<close>.\<close>

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

lemma word64_not_le_of_nat:
  \<open>\<not> word64_of_nat n \<le> (x :: 64 word) \<Longrightarrow> unat x < n\<close>
  by (simp add: not_le word64_less_of_nat)

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

end

end
