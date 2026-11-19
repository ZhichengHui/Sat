theory Sat_Proof
  imports Sat_Proof.Sat_Partial
begin

text \<open>The contracts of the functions of \<^verbatim>\<open>core/src/lib.rs\<close> and their proofs: the verification
  of Friday (CreuSAT) carried over to the AutoCorrode translation, with \<^verbatim>\<open>solve\<close> returning
  a satisfying assignment (\<open>sol\<close>), on the semantics of \<^verbatim>\<open>Sat_Partial\<close>. \<^verbatim>\<open>Sat_Top\<close> derives the
  contract of the specification.\<close>

context Sat_ctx
begin

section \<open>Function contracts\<close>

text \<open>The formula's literals refer to variables below \<open>n\<close>; every list fits in a \<^verbatim>\<open>usize\<close>
  (a clause has fewer than \<open>2^63\<close> literals, so its length plus one does too) and is at most
  \<^term>\<open>urust_fuel\<close> long, so no bounded loop runs out of fuel.\<close>
definition formula_wf :: \<open>Formula \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>formula_wf f n \<equiv>
     length (Formula_clauses f) \<le> urust_fuel \<and> length (Formula_clauses f) < 2^64 \<and>
     (\<forall>c \<in> set (Formula_clauses f).
        length (Clause_v0 c) \<le> urust_fuel \<and> length (Clause_v0 c) < 2^63 \<and>
        (\<forall>l \<in> set (Clause_v0 c). unat (Lit_var l) < n))\<close>

lemma formula_wf_vars_below:
  \<open>formula_wf f n \<Longrightarrow> vars_below f n\<close>
  unfolding formula_wf_def vars_below_def by blast

text \<open>The precondition of the clause functions: every literal's variable indexes both lists of
  the partial assignment, and the clause fits the fuel, and its length plus one a
  \<^verbatim>\<open>usize\<close>.\<close>
definition clause_pre :: \<open>Clause \<Rightarrow> Pasn \<Rightarrow> bool\<close> where
  \<open>clause_pre c pa \<equiv>
     (\<forall>l \<in> set (Clause_v0 c). unat (Lit_var l) < length (Assignments_v0 (Pasn_assign pa)) \<and>
        unat (Lit_var l) < length (Pasn_set pa)) \<and>
     length (Clause_v0 c) \<le> urust_fuel \<and> length (Clause_v0 c) < 2^63\<close>

lemma formula_wf_clause_pre:
  assumes \<open>formula_wf f (length (Assignments_v0 (Pasn_assign pa)))\<close>
    \<open>length (Pasn_set pa) = length (Assignments_v0 (Pasn_assign pa))\<close>
    \<open>j < length (Formula_clauses f)\<close>
  shows \<open>clause_pre (Formula_clauses f ! j) pa\<close>
  using assms nth_mem[OF assms(3)] unfolding formula_wf_def clause_pre_def by auto

definition Clause_has_true_contract :: \<open>Clause \<Rightarrow> Pasn \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>Clause_has_true_contract c pa \<equiv>
     let pre = can_alloc_reference \<star> \<langle>clause_pre c pa\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>r = clause_true (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) c\<rangle> in
     make_function_contract pre post\<close>

lemma Clause_has_true_spec:
  shows \<open>\<Gamma>; Clause_has_true c pa \<Turnstile>\<^sub>F Clause_has_true_contract c pa\<close>
  apply (crush_boot f: Clause_has_true_def contract: Clause_has_true_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length (Clause_v0 c) \<and>
                (\<forall>j < unat i. \<not> (Pasn_set pa ! unat (Lit_var (Clause_v0 c ! j)) \<and>
                   lit_sat (Assignments_v0 (Pasn_assign pa)) (Clause_v0 c ! j))) \<and>
                length (Clause_v0 c) - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length (Clause_v0 c) \<and>
                (\<forall>j < unat i. \<not> (Pasn_set pa ! unat (Lit_var (Clause_v0 c ! j)) \<and>
                   lit_sat (Assignments_v0 (Pasn_assign pa)) (Clause_v0 c ! j))) \<and>
                length (Clause_v0 c) - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
               \<langle>r = clause_true (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) c\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: true_def false_def lit_sat_def clause_true_def word_less_nat_alt
        word_le_nat_alt unat_of_nat_eq unat_word_Suc_simp clause_pre_def)
    apply (auto simp add: less_Suc_eq clause_true_def lit_sat_def clause_pre_def)
    done
  done

text \<open>The result of \<^verbatim>\<open>Clause::unset_from\<close> started at \<open>s\<close>.\<close>
definition unset_from_post :: \<open>bool list \<Rightarrow> Clause \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>unset_from_post d c s r \<equiv>
     s \<le> r \<and> r \<le> length (Clause_v0 c) \<and>
     (r < length (Clause_v0 c) \<longrightarrow> \<not> d ! unat (Lit_var (Clause_v0 c ! r))) \<and>
     (\<forall>j. s \<le> j \<and> j < r \<longrightarrow> d ! unat (Lit_var (Clause_v0 c ! j)))\<close>

definition Clause_unset_from_contract :: \<open>Clause \<Rightarrow> Pasn \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Clause_unset_from_contract c pa s \<equiv>
     let pre = can_alloc_reference \<star> \<langle>clause_pre c pa \<and> unat s \<le> length (Clause_v0 c)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>unset_from_post (Pasn_set pa) c (unat s) (unat r)\<rangle> in
     make_function_contract pre post\<close>

lemma Clause_unset_from_spec:
  shows \<open>\<Gamma>; Clause_unset_from c pa s \<Turnstile>\<^sub>F Clause_unset_from_contract c pa s\<close>
  apply (crush_boot f: Clause_unset_from_def contract: Clause_unset_from_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat s \<le> unat i \<and> unat i \<le> length (Clause_v0 c) \<and>
                (\<forall>j. unat s \<le> j \<and> j < unat i \<longrightarrow> Pasn_set pa ! unat (Lit_var (Clause_v0 c ! j))) \<and>
                length (Clause_v0 c) - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat s \<le> unat i \<and> unat i < length (Clause_v0 c) \<and>
                (\<forall>j. unat s \<le> j \<and> j < unat i \<longrightarrow> Pasn_set pa ! unat (Lit_var (Clause_v0 c ! j))) \<and>
                length (Clause_v0 c) - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>unset_from_post (Pasn_set pa) c (unat s) (unat r)\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: true_def false_def word_less_nat_alt
        word_le_nat_alt unat_of_nat_eq unat_word_Suc_simp clause_pre_def)
    apply (auto simp add: less_Suc_eq le_Suc_eq unset_from_post_def clause_pre_def)
    done
  done

text \<open>The result of \<^verbatim>\<open>Clause::unit_lit\<close>: the index of the only unassigned literal if the
  clause is unit, otherwise not below the clause's length, and equal to it iff the clause is
  settled.\<close>
definition unit_lit_post :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>unit_lit_post a d c r \<equiv>
     (r < length (Clause_v0 c) \<longrightarrow> unit_at a d c r) \<and>
     ((\<exists>k. unit_at a d c k) \<longrightarrow> r < length (Clause_v0 c)) \<and>
     (r = length (Clause_v0 c) \<longleftrightarrow> settled a d c)\<close>

text \<open>The state of the loop of \<^verbatim>\<open>Clause::unit_lit\<close> after the literals below \<open>i\<close>: none of them
  is true, and \<open>k\<close> is the clause's length if all are assigned, otherwise the index of the only
  unassigned one.\<close>
definition unit_scan :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>unit_scan a d c i k \<equiv>
     i \<le> length (Clause_v0 c) \<and>
     (\<forall>j < i. \<not> (d ! unat (Lit_var (Clause_v0 c ! j)) \<and> lit_sat a (Clause_v0 c ! j))) \<and>
     (k = length (Clause_v0 c) \<and> (\<forall>j < i. d ! unat (Lit_var (Clause_v0 c ! j))) \<or>
      k < i \<and> \<not> d ! unat (Lit_var (Clause_v0 c ! k)) \<and>
      (\<forall>j < i. j \<noteq> k \<longrightarrow> d ! unat (Lit_var (Clause_v0 c ! j))))\<close>

lemma unit_scan_start:
  \<open>unit_scan a d c 0 (length (Clause_v0 c))\<close>
  unfolding unit_scan_def by simp

lemma unit_scan_bound:
  assumes \<open>unit_scan a d c i k\<close>
  shows \<open>i \<le> length (Clause_v0 c)\<close> \<open>k \<le> length (Clause_v0 c)\<close>
  using assms unfolding unit_scan_def by auto

lemma unit_scan_false:
  assumes \<open>unit_scan a d c i k\<close> \<open>i < length (Clause_v0 c)\<close> \<open>d ! unat (Lit_var (Clause_v0 c ! i))\<close>
    \<open>\<not> lit_sat a (Clause_v0 c ! i)\<close>
  shows \<open>unit_scan a d c (Suc i) k\<close>
  using assms unfolding unit_scan_def by (auto simp add: less_Suc_eq)

lemma unit_lit_post_true:
  assumes \<open>i < length (Clause_v0 c)\<close> \<open>d ! unat (Lit_var (Clause_v0 c ! i))\<close> \<open>lit_sat a (Clause_v0 c ! i)\<close>
  shows \<open>unit_lit_post a d c (length (Clause_v0 c))\<close>
proof -
  have t: \<open>clause_true a d c\<close>
    using assms unfolding clause_true_def by blast
  have \<open>\<not> clause_false a d c\<close>
    using assms nth_mem[OF assms(1)] unfolding clause_false_def by blast
  then show ?thesis
    using clause_true_not_unit[OF t] unfolding unit_lit_post_def settled_def by blast
qed

lemma unit_lit_post_two:
  assumes \<open>unit_scan a d c i k\<close> \<open>k < length (Clause_v0 c)\<close> \<open>i < length (Clause_v0 c)\<close>
    \<open>\<not> d ! unat (Lit_var (Clause_v0 c ! i))\<close>
  shows \<open>unit_lit_post a d c (length (Clause_v0 c))\<close>
proof -
  have k: \<open>k < i\<close> \<open>\<not> d ! unat (Lit_var (Clause_v0 c ! k))\<close>
    using assms(1,2) unfolding unit_scan_def by auto
  have nu: \<open>\<forall>k'. \<not> unit_at a d c k'\<close>
    using two_unset_not_unit[OF k(1) assms(3) k(2) assms(4)] by blast
  have \<open>\<not> clause_false a d c\<close>
    using assms(3,4) nth_mem[OF assms(3)] unfolding clause_false_def by blast
  then show ?thesis
    using nu unfolding unit_lit_post_def settled_def by blast
qed

lemma unit_lit_post_end:
  assumes \<open>unit_scan a d c (length (Clause_v0 c)) k\<close>
  shows \<open>unit_lit_post a d c (if k = length (Clause_v0 c) then Suc k else k)\<close>
proof (cases \<open>k = length (Clause_v0 c)\<close>)
  case True
  then have s: \<open>\<forall>j < length (Clause_v0 c). d ! unat (Lit_var (Clause_v0 c ! j))\<close>
    \<open>\<forall>j < length (Clause_v0 c). \<not> lit_sat a (Clause_v0 c ! j)\<close>
    using assms unfolding unit_scan_def by auto
  then have \<open>clause_false a d c\<close>
    unfolding clause_false_iff_nth lit_sat_def by blast
  then show ?thesis
    using True all_set_not_unit[OF s(1)] unfolding unit_lit_post_def settled_def by auto
next
  case False
  then have k: \<open>k < length (Clause_v0 c)\<close> \<open>\<not> d ! unat (Lit_var (Clause_v0 c ! k))\<close>
    \<open>\<forall>j < length (Clause_v0 c). j \<noteq> k \<longrightarrow> d ! unat (Lit_var (Clause_v0 c ! j)) \<and>
       \<not> lit_sat a (Clause_v0 c ! j)\<close>
    using assms unfolding unit_scan_def by auto
  then have u: \<open>unit_at a d c k\<close>
    unfolding unit_at_def by blast
  then show ?thesis
    using False k(1) unfolding unit_lit_post_def settled_def by auto
qed

text \<open>The steps of the loop of \<^verbatim>\<open>Clause::unit_lit\<close> in the form of its goals: the first
  unassigned literal, \<open>k\<close> not yet below the clause's length.\<close>
lemma unit_scan_unset_first:
  assumes \<open>unit_scan a d c i k\<close> \<open>i < length (Clause_v0 c)\<close> \<open>\<not> d ! unat (Lit_var (Clause_v0 c ! i))\<close>
    \<open>\<not> k < length (Clause_v0 c)\<close>
  shows \<open>unit_scan a d c (Suc i) i\<close>
  using assms unfolding unit_scan_def by (auto simp add: less_Suc_eq)

text \<open>The end of the loop with one unassigned literal \<open>k\<close>, and with none.\<close>
lemma unit_lit_post_end_unit:
  fixes i k :: \<open>64 word\<close>
  assumes \<open>unit_scan a d c (unat i) (unat k)\<close> \<open>length (Clause_v0 c) \<le> unat i\<close>
    \<open>length (Clause_v0 c) < 9223372036854775808\<close> \<open>k \<noteq> word64_of_nat (length (Clause_v0 c))\<close>
  shows \<open>unit_lit_post a d c (unat k)\<close>
proof -
  have i: \<open>unat i = length (Clause_v0 c)\<close>
    using unit_scan_bound(1)[OF assms(1)] assms(2) by simp
  have \<open>unat k \<noteq> length (Clause_v0 c)\<close>
    using assms(3,4) word64_eq_of_nat_iff[of \<open>length (Clause_v0 c)\<close> k] by simp
  then show ?thesis
    using unit_lit_post_end[of _ _ c \<open>unat k\<close>] assms(1) i by simp
qed

lemma unit_lit_post_end_settled:
  fixes i :: \<open>64 word\<close>
  assumes \<open>unit_scan a d c (unat i) (length (Clause_v0 c))\<close> \<open>length (Clause_v0 c) \<le> unat i\<close>
  shows \<open>unit_lit_post a d c (Suc (length (Clause_v0 c)))\<close>
proof -
  have \<open>unat i = length (Clause_v0 c)\<close>
    using unit_scan_bound(1)[OF assms(1)] assms(2) by simp
  then show ?thesis
    using unit_lit_post_end[of _ _ c \<open>length (Clause_v0 c)\<close>] assms(1) by simp
qed

definition Clause_unit_lit_contract :: \<open>Clause \<Rightarrow> Pasn \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Clause_unit_lit_contract c pa \<equiv>
     let pre = can_alloc_reference \<star> \<langle>clause_pre c pa\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>unit_lit_post (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) c (unat r)\<rangle> in
     make_function_contract pre post\<close>

lemma Clause_unit_lit_spec:
  shows \<open>\<Gamma>; Clause_unit_lit c pa \<Turnstile>\<^sub>F Clause_unit_lit_contract c pa\<close>
  apply (crush_boot f: Clause_unit_lit_def contract: Clause_unit_lit_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for k_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>j. \<Squnion>g k g' i. k_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>k \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>i \<star> can_alloc_reference \<star>
               \<langle>unit_scan (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) c (unat i) (unat k) \<and>
                length (Clause_v0 c) - unat i \<le> j\<rangle>\<close> and
        INV'=\<open>\<lambda>j. \<Squnion>g k g' i. k_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>k \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> g'\<down>i \<star> can_alloc_reference \<star>
               \<langle>unit_scan (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) c (unat i) (unat k) \<and>
                unat i < length (Clause_v0 c) \<and> length (Clause_v0 c) - unat i \<le> Suc j\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
               \<langle>unit_lit_post (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) c (unat r)\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: true_def false_def word_less_nat_alt
        word_le_nat_alt unat_of_nat_eq unat_word_Suc_simp clause_pre_def)
    subgoal by (rule unit_scan_unset_first)
    subgoal by (rule unit_lit_post_two)
    apply (solves \<open>rule unit_scan_false; simp add: lit_sat_def\<close>)+
    apply (solves \<open>(rule unit_lit_post_true, assumption); simp add: lit_sat_def\<close>)+
    subgoal by (rule unit_lit_post_end_unit)
    subgoal by (rule unit_lit_post_end_settled)
    subgoal by (rule unit_scan_start)
    done
  done

text \<open>The result of \<^verbatim>\<open>Formula::unit_clause\<close> on the clauses \<open>s..e\<close>: the first clause there
  that is not settled, or \<open>e\<close> if they all are.\<close>
definition unit_clause_post :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Formula \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>unit_clause_post a d f s e r \<equiv>
     s \<le> r \<and> r \<le> e \<and> (r < e \<longrightarrow> \<not> settled a d (Formula_clauses f ! r)) \<and>
     (\<forall>j. s \<le> j \<and> j < r \<longrightarrow> settled a d (Formula_clauses f ! j))\<close>

text \<open>A clause for which \<^verbatim>\<open>Clause::unit_lit\<close> returns the clause's length is settled.\<close>
lemma unit_lit_post_settled:
  assumes \<open>formula_wf f n\<close> \<open>j < length (Formula_clauses f)\<close>
    \<open>unit_lit_post a d (Formula_clauses f ! j) (unat (word64_of_nat (length (Clause_v0 (Formula_clauses f ! j)))))\<close>
  shows \<open>settled a d (Formula_clauses f ! j)\<close>
proof -
  have \<open>length (Clause_v0 (Formula_clauses f ! j)) < 2^63\<close>
    using assms(1) nth_mem[OF assms(2)] unfolding formula_wf_def by blast
  then show ?thesis
    using assms(3) unfolding unit_lit_post_def by (simp add: unat_of_nat_eq)
qed

text \<open>A clause for which it returns something else is not.\<close>
lemma unit_lit_post_not_settled:
  assumes \<open>formula_wf f n\<close> \<open>j < length (Formula_clauses f)\<close>
    \<open>unit_lit_post a d (Formula_clauses f ! j) (unat x)\<close>
    \<open>x \<noteq> word64_of_nat (length (Clause_v0 (Formula_clauses f ! j)))\<close>
  shows \<open>\<not> settled a d (Formula_clauses f ! j)\<close>
proof -
  have \<open>length (Clause_v0 (Formula_clauses f ! j)) < 2^64\<close>
    using assms(1) nth_mem[OF assms(2)] unfolding formula_wf_def by fastforce
  then have \<open>unat x \<noteq> length (Clause_v0 (Formula_clauses f ! j))\<close>
    using assms(4) word64_eq_of_nat_iff by blast
  then show ?thesis
    using assms(3) unfolding unit_lit_post_def by simp
qed

text \<open>The next index after one below \<open>e\<close>, for an \<open>e\<close> that is at most the number of clauses.\<close>
lemma unit_clause_next:
  fixes r e :: \<open>64 word\<close>
  assumes \<open>formula_wf f n\<close> \<open>unat e \<le> length (Formula_clauses f)\<close> \<open>unat r < unat e\<close>
  shows \<open>unat (r + 1) = Suc (unat r)\<close> \<open>unat r < 18446744073709551615\<close>
proof -
  have \<open>length (Formula_clauses f) < 2^64\<close>
    using assms(1) unfolding formula_wf_def by simp
  then show \<open>unat r < 18446744073709551615\<close>
    using assms(2,3) by simp
  then show \<open>unat (r + 1) = Suc (unat r)\<close>
    by (rule unat_word_Suc_simp)
qed

text \<open>The steps of the loop of \<^verbatim>\<open>Formula::unit_clause\<close> on the clause \<open>r\<close>: if it is
  settled, the scan goes on; otherwise it is the result.\<close>
lemma unit_clause_settled_step:
  fixes r e :: \<open>64 word\<close>
  assumes wf: \<open>formula_wf f n\<close> and e: \<open>unat e \<le> length (Formula_clauses f)\<close> and r: \<open>unat r < unat e\<close>
    and below: \<open>\<forall>j. s \<le> j \<and> j < unat r \<longrightarrow> settled a d (Formula_clauses f ! j)\<close>
    and ulp: \<open>unit_lit_post a d (Formula_clauses f ! unat r)
      (unat (word64_of_nat (length (Clause_v0 (Formula_clauses f ! unat r)))))\<close>
    and j: \<open>s \<le> j\<close> \<open>j < unat (r + 1)\<close>
  shows \<open>settled a d (Formula_clauses f ! j)\<close>
proof -
  have \<open>settled a d (Formula_clauses f ! unat r)\<close>
    using unit_lit_post_settled[OF wf _ ulp] e r by simp
  then show ?thesis
    using below j unit_clause_next(1)[OF wf e r] by (cases \<open>j = unat r\<close>) auto
qed

lemma unit_clause_found:
  fixes s r e x :: \<open>64 word\<close>
  assumes wf: \<open>formula_wf f n\<close> and e: \<open>unat e \<le> length (Formula_clauses f)\<close>
    and r: \<open>unat s \<le> unat r\<close> \<open>unat r < unat e\<close>
    and below: \<open>\<forall>j. unat s \<le> j \<and> j < unat r \<longrightarrow> settled a d (Formula_clauses f ! j)\<close>
    and ulp: \<open>unit_lit_post a d (Formula_clauses f ! unat r) (unat x)\<close>
    and ne: \<open>x \<noteq> word64_of_nat (length (Clause_v0 (Formula_clauses f ! unat r)))\<close>
  shows \<open>unit_clause_post a d f (unat s) (unat e) (unat r)\<close>
  using unit_lit_post_not_settled[OF wf _ ulp ne] e r below
  unfolding unit_clause_post_def by simp

definition Formula_unit_clause_contract :: \<open>Formula \<Rightarrow> Pasn \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Formula_unit_clause_contract f pa s e \<equiv>
     let a = Assignments_v0 (Pasn_assign pa) in
     let pre = can_alloc_reference \<star>
        \<langle>formula_wf f (length a) \<and> length (Pasn_set pa) = length a \<and>
         unat s \<le> unat e \<and> unat e \<le> length (Formula_clauses f)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>unit_clause_post a (Pasn_set pa) f (unat s) (unat e) (unat r)\<rangle> in
     make_function_contract pre post\<close>

lemma Formula_unit_clause_spec:
  shows \<open>\<Gamma>; Formula_unit_clause f pa s e \<Turnstile>\<^sub>F Formula_unit_clause_contract f pa s e\<close>
  apply (crush_boot f: Formula_unit_clause_def contract: Formula_unit_clause_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat s \<le> unat i \<and> unat i \<le> unat e \<and>
                (\<forall>j. unat s \<le> j \<and> j < unat i \<longrightarrow>
                   settled (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) (Formula_clauses f ! j)) \<and>
                unat e - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat s \<le> unat i \<and> unat i < unat e \<and>
                (\<forall>j. unat s \<le> j \<and> j < unat i \<longrightarrow>
                   settled (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) (Formula_clauses f ! j)) \<and>
                unat e - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
               \<langle>unit_clause_post (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) f (unat s) (unat e) (unat r)\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def specs add: Clause_unit_lit_spec contracts add: Clause_unit_lit_contract_def
        simp add: true_def false_def formula_wf_clause_pre word_less_nat_alt unat_of_nat_eq unat_word_Suc_simp)
    subgoal by (frule (2) unit_clause_next(1)) simp
    subgoal by (rule unit_clause_settled_step)
    apply (solves \<open>frule (2) unit_clause_next(1), simp\<close>)+
    subgoal by (rule unit_clause_next(2))
    subgoal by (rule unit_clause_found)
    subgoal by (simp add: unit_clause_post_def)
    subgoal unfolding formula_wf_def by linarith
    done
  done

text \<open>The result of \<^verbatim>\<open>Formula::open_clause\<close>: the index of a clause without a true literal,
  or the number of clauses if every clause has one.\<close>
definition open_clause_post :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Formula \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>open_clause_post a d f r \<equiv>
     r \<le> length (Formula_clauses f) \<and>
     (r < length (Formula_clauses f) \<longrightarrow> \<not> clause_true a d (Formula_clauses f ! r)) \<and>
     (\<forall>j < r. clause_true a d (Formula_clauses f ! j))\<close>

definition Formula_open_clause_contract :: \<open>Formula \<Rightarrow> Pasn \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Formula_open_clause_contract f pa \<equiv>
     let a = Assignments_v0 (Pasn_assign pa) in
     let pre = can_alloc_reference \<star> \<langle>formula_wf f (length a) \<and> length (Pasn_set pa) = length a\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>open_clause_post a (Pasn_set pa) f (unat r)\<rangle> in
     make_function_contract pre post\<close>

lemma Formula_open_clause_spec:
  shows \<open>\<Gamma>; Formula_open_clause f pa \<Turnstile>\<^sub>F Formula_open_clause_contract f pa\<close>
  apply (crush_boot f: Formula_open_clause_def contract: Formula_open_clause_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length (Formula_clauses f) \<and>
                (\<forall>j < unat i. clause_true (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa)
                   (Formula_clauses f ! j)) \<and>
                length (Formula_clauses f) - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length (Formula_clauses f) \<and>
                (\<forall>j < unat i. clause_true (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa)
                   (Formula_clauses f ! j)) \<and>
                length (Formula_clauses f) - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
               \<langle>open_clause_post (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) f (unat r)\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def specs add: Clause_has_true_spec contracts add: Clause_has_true_contract_def
        simp add: true_def false_def formula_wf_clause_pre word_less_nat_alt unat_of_nat_eq unat_word_Suc_simp)
    apply (auto simp add: less_Suc_eq open_clause_post_def formula_wf_def unat_of_nat_eq unat_word_Suc_simp)
    done
  done

definition updated_contract :: \<open>bool list \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> ('s, bool list, 'abort) function_contract\<close> where
  \<open>updated_contract xs i x \<equiv>
     let pre = can_alloc_reference \<star> \<langle>unat i < length xs\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = xs[unat i := x]\<rangle> in
     make_function_contract pre post\<close>

lemma updated_spec:
  shows \<open>\<Gamma>; updated xs i x \<Turnstile>\<^sub>F updated_contract xs i x\<close>
  apply (crush_boot f: updated_def contract: updated_contract_def)
  apply (crush_base simp add: true_def false_def focus_components)
  done

definition set_var_contract :: \<open>Pasn \<Rightarrow> 64 word \<Rightarrow> bool \<Rightarrow> ('s, Pasn, 'abort) function_contract\<close> where
  \<open>set_var_contract pa v b \<equiv>
     let a = Assignments_v0 (Pasn_assign pa) in
     let pre = can_alloc_reference \<star> \<langle>unat v < length a \<and> unat v < length (Pasn_set pa)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>r = make_Pasn (make_Assignments (a[unat v := b])) ((Pasn_set pa)[unat v := True])\<rangle> in
     make_function_contract pre post\<close>

lemma set_var_spec:
  shows \<open>\<Gamma>; set_var pa v b \<Turnstile>\<^sub>F set_var_contract pa v b\<close>
  apply (crush_boot f: set_var_def contract: set_var_contract_def)
  apply (crush_base inline: Pasn_mk_def Assignments_mk_def specs add: updated_spec
      contracts add: updated_contract_def simp add: true_def false_def)
  done

definition copy_contract :: \<open>Pasn \<Rightarrow> ('s, Pasn, 'abort) function_contract\<close> where
  \<open>copy_contract pa \<equiv>
     let pre = can_alloc_reference in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = pa\<rangle> in
     make_function_contract pre post\<close>

lemma copy_spec:
  shows \<open>\<Gamma>; copy pa \<Turnstile>\<^sub>F copy_contract pa\<close>
  apply (crush_boot f: copy_def contract: copy_contract_def)
  apply (crush_base inline: Pasn_mk_def Assignments_mk_def simp add: Pasn.expand Assignments.expand)
  done

text \<open>The \<open>k\<close>-th unfolding of \<^const>\<open>propagate\<close> on the clauses \<open>s..e\<close>. Either \<open>e\<close> is the number
  of clauses, or \<open>s\<close> is \<open>0\<close> and the clauses from \<open>e\<close> on are settled (the scan has come round to
  the clause after the last unit one). Each recursive call either assigns one more variable or
  goes on from the first clause, which it does not do twice in a row: twice the number of
  unassigned variables, plus one if the scan has yet to come round, decreases and must be below
  \<open>k\<close>.\<close>
definition prop_pre :: \<open>Formula \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>prop_pre f a d s e k \<equiv>
     formula_wf f (length a) \<and> length d = length a \<and> s \<le> e \<and> e \<le> length (Formula_clauses f) \<and>
     (e \<noteq> length (Formula_clauses f) \<longrightarrow>
        s = 0 \<and> (\<forall>j. e \<le> j \<and> j < length (Formula_clauses f) \<longrightarrow> settled a d (Formula_clauses f ! j))) \<and>
     2 * unset d + (if e = length (Formula_clauses f) \<and> s \<noteq> 0 then 1 else 0) < k\<close>

text \<open>\<^verbatim>\<open>Conflict\<close> means that no extension satisfies the formula; \<^verbatim>\<open>Fixpoint(pb)\<close> gives an
  extension with the same satisfying extensions under which every clause is settled. The contract
  states both conditions through these definitions, which \<open>crush_base\<close> does not unfold.\<close>
definition prop_post :: \<open>Formula \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> Propagated \<Rightarrow> bool\<close> where
  \<open>prop_post f a d r \<equiv> case r of
     Propagated_Conflict \<Rightarrow> \<not> ext_sat f a d
   | Propagated_Fixpoint pb \<Rightarrow> prop_rel f a d (Assignments_v0 (Pasn_assign pb)) (Pasn_set pb) \<and>
       (\<forall>j < length (Formula_clauses f). settled (Assignments_v0 (Pasn_assign pb)) (Pasn_set pb) (Formula_clauses f ! j))\<close>

definition propagate_contract :: \<open>nat \<Rightarrow> Formula \<Rightarrow> Pasn \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, Propagated, 'abort) function_contract\<close> where
  \<open>propagate_contract k f pa s e \<equiv>
     let a = Assignments_v0 (Pasn_assign pa) in
     let d = Pasn_set pa in
     let pre = can_alloc_reference \<star> \<langle>prop_pre f a d (unat s) (unat e) k\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>prop_post f a d r\<rangle> in
     make_function_contract pre post\<close>

text \<open>The facts about the clause \<open>x\<close> that \<^verbatim>\<open>Formula::unit_clause\<close> found (it is below \<open>e\<close>), and
  \<open>xa\<close>, the result of \<^verbatim>\<open>Clause::unit_lit\<close> on it.\<close>
lemma prop_found_facts:
  fixes s e x :: \<open>64 word\<close>
  assumes pre: \<open>prop_pre f a d (unat s) (unat e) k\<close>
    and ucp: \<open>unit_clause_post a d f (unat s) (unat e) (unat x)\<close> and ne: \<open>x \<noteq> e\<close>
  shows \<open>unat x < unat e\<close> \<open>unat x < length (Formula_clauses f)\<close> \<open>unat x < 18446744073709551615\<close>
    \<open>\<not> settled a d (Formula_clauses f ! unat x)\<close>
    \<open>length (Clause_v0 (Formula_clauses f ! unat x)) < 2^63\<close>
proof -
  have \<open>unat x \<noteq> unat e\<close>
    using ne word_unat.Rep_inject by blast
  moreover have \<open>unat x \<le> unat e\<close>
    using ucp unfolding unit_clause_post_def by simp
  ultimately show x: \<open>unat x < unat e\<close>
    by linarith
  have n: \<open>unat e \<le> length (Formula_clauses f)\<close> \<open>length (Formula_clauses f) < 2^64\<close>
    using pre unfolding prop_pre_def formula_wf_def by simp_all
  show xn: \<open>unat x < length (Formula_clauses f)\<close>
    using x n by simp
  show \<open>unat x < 18446744073709551615\<close>
    using xn n by simp
  show \<open>\<not> settled a d (Formula_clauses f ! unat x)\<close>
    using ucp x unfolding unit_clause_post_def by simp
  show \<open>length (Clause_v0 (Formula_clauses f ! unat x)) < 2^63\<close>
    using pre nth_mem[OF xn] unfolding prop_pre_def formula_wf_def by blast
qed

text \<open>The clause found by \<^verbatim>\<open>Formula::unit_clause\<close> meets the precondition of
  \<^verbatim>\<open>Clause::unit_lit\<close>.\<close>
lemma prop_found_clause_pre:
  fixes s e x :: \<open>64 word\<close>
  assumes pre: \<open>prop_pre f (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) (unat s) (unat e) k\<close>
    and ucp: \<open>unit_clause_post (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) f (unat s) (unat e) (unat x)\<close>
    and ne: \<open>x \<noteq> e\<close>
  shows \<open>clause_pre (Formula_clauses f ! unat x) pa\<close>
  using formula_wf_clause_pre[of f pa] prop_found_facts(2)[OF pre ucp ne] pre
  unfolding prop_pre_def by simp

text \<open>A clause found by \<^verbatim>\<open>Formula::unit_clause\<close> that is not unit is false: the conflict.\<close>
lemma prop_conflict:
  fixes s e x xa :: \<open>64 word\<close>
  assumes pre: \<open>prop_pre f a d (unat s) (unat e) k\<close>
    and ucp: \<open>unit_clause_post a d f (unat s) (unat e) (unat x)\<close> and ne: \<open>x \<noteq> e\<close>
    and ulp: \<open>unit_lit_post a d (Formula_clauses f ! unat x) (unat xa)\<close>
    and nk: \<open>word64_of_nat (length (Clause_v0 (Formula_clauses f ! unat x))) \<le> xa\<close>
  shows \<open>prop_post f a d Propagated_Conflict\<close>
proof -
  note fx = prop_found_facts[OF pre ucp ne]
  have \<open>length (Clause_v0 (Formula_clauses f ! unat x)) \<le> unat xa\<close>
    using nk fx(5) by (simp add: word_le_nat_alt unat_of_nat_eq)
  then have \<open>\<forall>k. \<not> unit_at a d (Formula_clauses f ! unat x) k\<close>
    using ulp unfolding unit_lit_post_def by auto
  then have \<open>clause_false a d (Formula_clauses f ! unat x)\<close>
    using fx(4) unfolding settled_def by blast
  then have \<open>conflict a d f\<close>
    using fx(2) unfolding conflict_iff_nth by blast
  moreover have \<open>vars_below f (length d)\<close>
    using pre formula_wf_vars_below unfolding prop_pre_def by simp
  ultimately show ?thesis
    using conflict_not_ext_sat unfolding prop_post_def by simp
qed

text \<open>The facts about one assignment of \<^verbatim>\<open>propagate\<close>: the clause \<open>x\<close> is unit with the
  unassigned literal \<open>xa\<close>.\<close>
lemma prop_assign_facts:
  fixes s e x xa :: \<open>64 word\<close>
  assumes pre: \<open>prop_pre f a d (unat s) (unat e) (Suc k)\<close>
    and ucp: \<open>unit_clause_post a d f (unat s) (unat e) (unat x)\<close> and ne: \<open>x \<noteq> e\<close>
    and ulp: \<open>unit_lit_post a d (Formula_clauses f ! unat x) (unat xa)\<close>
    and nk: \<open>\<not> word64_of_nat (length (Clause_v0 (Formula_clauses f ! unat x))) \<le> xa\<close>
  defines \<open>v \<equiv> unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa))\<close>
    and \<open>b \<equiv> Lit_value (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)\<close>
  shows \<open>prop_rel f a d (a[v := b]) (d[v := True])\<close>
    \<open>prop_pre f (a[v := b]) (d[v := True]) (unat (x + 1)) (unat (word64_of_nat (length (Formula_clauses f)))) k\<close>
    \<open>v < length d\<close> \<open>v < length a\<close> \<open>unat xa < length (Clause_v0 (Formula_clauses f ! unat x))\<close>
proof -
  note fx = prop_found_facts[OF pre ucp ne]
  have wf: \<open>formula_wf f (length a)\<close> and len: \<open>length d = length a\<close>
    and m: \<open>2 * unset d < Suc k\<close>
    using pre unfolding prop_pre_def by (simp_all split: if_splits)
  have lf: \<open>length (Formula_clauses f) < 2^64\<close>
    using wf unfolding formula_wf_def by simp
  have x: \<open>unat x < length (Formula_clauses f)\<close> \<open>unat x < 18446744073709551615\<close>
    using fx by simp_all
  define c where \<open>c = Formula_clauses f ! unat x\<close>
  have c: \<open>c \<in> set (Formula_clauses f)\<close>
    using x unfolding c_def by simp
  show xa: \<open>unat xa < length (Clause_v0 (Formula_clauses f ! unat x))\<close>
    using nk fx(5) by (simp add: word_le_nat_alt unat_of_nat_eq)
  have u: \<open>unit_at a d c (unat xa)\<close>
    using ulp xa unfolding unit_lit_post_def c_def by blast
  have vb: \<open>vars_below f (length a)\<close>
    using wf by (rule formula_wf_vars_below)
  show va: \<open>v < length a\<close>
    using vb nth_mem[OF x(1)] nth_mem[OF xa] unfolding vars_below_def v_def by blast
  then show \<open>v < length d\<close>
    using len by simp
  have nd: \<open>\<not> d ! v\<close>
    using u unfolding unit_at_def c_def v_def by simp
  show pr: \<open>prop_rel f a d (a[v := b]) (d[v := True])\<close>
    using prop_rel_unit[OF c u vb len] unfolding c_def v_def b_def .
  have us: \<open>unset (d[v := True]) < unset d\<close>
    using unset_update[OF _ nd] va len by simp
  have x1: \<open>unat (x + 1) = Suc (unat x)\<close>
    using unat_word_Suc_simp[OF x(2)] .
  show \<open>prop_pre f (a[v := b]) (d[v := True]) (unat (x + 1)) (unat (word64_of_nat (length (Formula_clauses f)))) k\<close>
    using wf len us m x1 x(1) lf unfolding prop_pre_def by (simp add: unat_of_nat_eq)
qed

lemma prop_post_rel:
  assumes \<open>prop_rel f a d a' d'\<close> \<open>prop_post f a' d' r\<close>
  shows \<open>prop_post f a d r\<close>
proof (cases r)
  case Propagated_Conflict
  then show ?thesis
    using assms unfolding prop_post_def prop_rel_def by simp
next
  case (Propagated_Fixpoint pb)
  then show ?thesis
    using assms prop_rel_trans[OF assms(1)] unfolding prop_post_def by simp
qed

text \<open>The scan of \<open>s..e\<close> to the last clause found none to propagate: it goes on from the first
  clause up to \<open>s\<close>.\<close>
lemma prop_round:
  fixes s :: \<open>64 word\<close> and f :: Formula
  defines \<open>e \<equiv> unat (word64_of_nat (length (Formula_clauses f)))\<close>
  assumes pre: \<open>prop_pre f a d (unat s) e (Suc k)\<close>
    and ucp: \<open>unit_clause_post a d f (unat s) e e\<close> and s: \<open>s \<noteq> 0\<close>
  shows \<open>prop_pre f a d 0 (unat s) k\<close>
proof -
  have \<open>length (Formula_clauses f) < 2^64\<close>
    using pre unfolding prop_pre_def formula_wf_def by simp
  then have \<open>e = length (Formula_clauses f)\<close>
    unfolding e_def by (simp add: unat_of_nat_eq)
  moreover have \<open>\<forall>j. unat s \<le> j \<and> j < e \<longrightarrow> settled a d (Formula_clauses f ! j)\<close>
    using ucp unfolding unit_clause_post_def by simp
  moreover have \<open>unat s \<noteq> 0\<close>
    using s unat_eq_zero by blast
  ultimately show ?thesis
    using pre unfolding prop_pre_def by auto
qed

text \<open>The scan found no clause to propagate and has come round: every clause is settled.\<close>
lemma prop_fixpoint:
  assumes pre: \<open>prop_pre f a d s e k\<close> and ucp: \<open>unit_clause_post a d f s e e\<close>
    and en: \<open>e \<noteq> length (Formula_clauses f) \<or> s = 0\<close>
    and pa: \<open>a = Assignments_v0 (Pasn_assign pa)\<close> \<open>d = Pasn_set pa\<close>
  shows \<open>prop_post f a d (Propagated_Fixpoint pa)\<close>
proof -
  have se: \<open>\<forall>j. s \<le> j \<and> j < e \<longrightarrow> settled a d (Formula_clauses f ! j)\<close>
    using ucp unfolding unit_clause_post_def by simp
  have \<open>\<forall>j < length (Formula_clauses f). settled a d (Formula_clauses f ! j)\<close>
  proof (cases \<open>e = length (Formula_clauses f)\<close>)
    case True
    then show ?thesis
      using se en by auto
  next
    case False
    have s0: \<open>s = 0\<close>
      and ge: \<open>\<forall>j. e \<le> j \<and> j < length (Formula_clauses f) \<longrightarrow> settled a d (Formula_clauses f ! j)\<close>
      using pre False unfolding prop_pre_def by simp_all
    show ?thesis
    proof (intro allI impI)
      fix j assume j: \<open>j < length (Formula_clauses f)\<close>
      show \<open>settled a d (Formula_clauses f ! j)\<close>
      proof (cases \<open>j < e\<close>)
        case True
        then show ?thesis using se s0 by simp
      next
        case False
        then show ?thesis using ge j by simp
      qed
    qed
  qed
  then show ?thesis
    using pa prop_rel_refl unfolding prop_post_def by simp
qed

text \<open>The same, when the scan ended before the last clause.\<close>
lemma prop_fixpoint_inner:
  fixes s e :: \<open>64 word\<close>
  assumes pre: \<open>prop_pre f (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) (unat s) (unat e) k\<close>
    and ucp: \<open>unit_clause_post (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) f (unat s) (unat e) (unat e)\<close>
    and ne: \<open>e \<noteq> word64_of_nat (length (Formula_clauses f))\<close>
  shows \<open>prop_post f (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) (Propagated_Fixpoint pa)\<close>
proof -
  have \<open>length (Formula_clauses f) < 2^64\<close>
    using pre unfolding prop_pre_def formula_wf_def by simp
  then have \<open>unat e \<noteq> length (Formula_clauses f)\<close>
    using ne word64_eq_of_nat_iff by blast
  then show ?thesis
    using prop_fixpoint[OF pre ucp] by simp
qed

lemma propagate_rec_step_spec:
  assumes \<open>\<And>pa s e. \<Gamma>; R f pa s e \<Turnstile>\<^sub>F propagate_contract k f pa s e\<close>
  shows \<open>\<Gamma>; propagate_rec_step R f pa s e \<Turnstile>\<^sub>F propagate_contract (Suc k) f pa s e\<close>
  apply (crush_boot f: propagate_rec_step_def contract: propagate_contract_def)
  apply (crush_base inline: len_def Propagated_Fixpoint_mk_def
      specs add: assms Formula_unit_clause_spec Clause_unit_lit_spec set_var_spec
      contracts add: propagate_contract_def Formula_unit_clause_contract_def Clause_unit_lit_contract_def
        set_var_contract_def
      simp add: true_def false_def)
  subgoal by (rule prop_post_rel[OF prop_assign_facts(1)])
  apply (solves \<open>rule prop_assign_facts(2-5) prop_found_facts(2,3); assumption\<close>)+
  subgoal by (rule prop_conflict)
  subgoal by (rule prop_found_facts(2))
  subgoal by (rule prop_found_clause_pre)
  subgoal by (rule prop_found_facts(2))
  subgoal by (rule prop_fixpoint_inner)
  subgoal by (rule prop_fixpoint, assumption+) simp_all
  subgoal by (rule prop_round)
  apply (simp_all add: prop_pre_def)
  done

lemma propagate_rec_spec:
  shows \<open>\<Gamma>; (propagate_rec_step ^^ k) g f pa s e \<Turnstile>\<^sub>F propagate_contract k f pa s e\<close>
proof (induction k arbitrary: pa s e)
  case 0
  show ?case
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: propagate_contract_def prop_pre_def Let_def apure_precise_False asepconj_bot_zero2
        bot_aentails_all)
    done
next
  case (Suc k)
  show ?case
    unfolding funpow.simps(2) comp_def by (rule propagate_rec_step_spec) (rule Suc.IH)
qed

lemma propagate_spec:
  shows \<open>\<Gamma>; propagate f pa s e \<Turnstile>\<^sub>F propagate_contract urust_fuel f pa s e\<close>
  unfolding propagate_def by (rule propagate_rec_spec)

text \<open>The \<open>k\<close>-th unfolding of \<^const>\<open>solve\<close>. Its precondition requires fewer than \<open>k\<close>
  variables to be unassigned, so the innermost function is never called.\<close>
definition solve_contract :: \<open>nat \<Rightarrow> Formula \<Rightarrow> Pasn \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  \<open>solve_contract k f pa \<equiv>
     let a = Assignments_v0 (Pasn_assign pa) in
     let d = Pasn_set pa in
     let pre = can_alloc_reference \<star>
        \<langle>formula_wf f (length a) \<and> length d = length a \<and> 2 * length a < urust_fuel \<and> unset d < k\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>sol f a d r\<rangle> in
     make_function_contract pre post\<close>

text \<open>The facts about the partial assignment \<open>pb\<close> after unit propagation, at the first clause
  \<open>xa\<close> without a true literal and its first unassigned literal \<open>xb\<close>.\<close>
lemma solve_prop_facts:
  assumes wf: \<open>formula_wf f (length a)\<close> and len: \<open>length d = length a\<close>
    and fuel: \<open>2 * length a < urust_fuel\<close>
    and pr: \<open>prop_rel f a d (Assignments_v0 (Pasn_assign pb)) (Pasn_set pb)\<close>
  shows \<open>length (Pasn_set pb) = length (Assignments_v0 (Pasn_assign pb))\<close>
    \<open>formula_wf f (length (Assignments_v0 (Pasn_assign pb)))\<close>
    \<open>2 * length (Assignments_v0 (Pasn_assign pb)) < urust_fuel\<close>
    \<open>unset (Pasn_set pb) \<le> unset d\<close>
  using assms unset_more_set[of d \<open>Pasn_set pb\<close>] unfolding prop_rel_def more_set_def by simp_all

lemma solve_open_idx:
  assumes \<open>formula_wf f n\<close> \<open>open_clause_post a d f (unat xa)\<close>
    \<open>xa \<noteq> word64_of_nat (length (Formula_clauses f))\<close>
  shows \<open>unat xa < length (Formula_clauses f)\<close>
  using assms word64_eq_of_nat_iff[of \<open>length (Formula_clauses f)\<close> xa]
  unfolding formula_wf_def open_clause_post_def by simp

lemma solve_branch_facts:
  assumes wf: \<open>formula_wf f (length a)\<close> and len: \<open>length d = length a\<close>
    and fuel: \<open>2 * length a < urust_fuel\<close> and k: \<open>unset d < Suc k\<close>
    and pr: \<open>prop_rel f a d (Assignments_v0 (Pasn_assign pb)) (Pasn_set pb)\<close>
    and st: \<open>\<forall>j < length (Formula_clauses f). settled (Assignments_v0 (Pasn_assign pb)) (Pasn_set pb) (Formula_clauses f ! j)\<close>
    and oc: \<open>open_clause_post (Assignments_v0 (Pasn_assign pb)) (Pasn_set pb) f (unat xa)\<close>
    and ne: \<open>xa \<noteq> word64_of_nat (length (Formula_clauses f))\<close>
    and uf: \<open>unset_from_post (Pasn_set pb) (Formula_clauses f ! unat xa) 0 (unat xb)\<close>
  shows \<open>unat xb < length (Clause_v0 (Formula_clauses f ! unat xa))\<close>
    \<open>unat (Lit_var (Clause_v0 (Formula_clauses f ! unat xa) ! unat xb)) < length (Assignments_v0 (Pasn_assign pb))\<close>
    \<open>unat (Lit_var (Clause_v0 (Formula_clauses f ! unat xa) ! unat xb)) < length (Pasn_set pb)\<close>
    \<open>unset ((Pasn_set pb)[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat xa) ! unat xb)) := True]) < k\<close>
    \<open>\<not> Pasn_set pb ! unat (Lit_var (Clause_v0 (Formula_clauses f ! unat xa) ! unat xb))\<close>
proof -
  note p = solve_prop_facts[OF wf len fuel pr]
  have nc: \<open>\<not> conflict (Assignments_v0 (Pasn_assign pb)) (Pasn_set pb) f\<close>
    by (rule settled_no_conflict[OF st])
  have xa: \<open>unat xa < length (Formula_clauses f)\<close>
    by (rule solve_open_idx[OF wf oc ne])
  define c where \<open>c = Formula_clauses f ! unat xa\<close>
  have ct: \<open>\<not> clause_true (Assignments_v0 (Pasn_assign pb)) (Pasn_set pb) c\<close>
    using oc xa unfolding open_clause_post_def c_def by simp
  have \<open>unat xb \<noteq> length (Clause_v0 c)\<close>
  proof
    assume \<open>unat xb = length (Clause_v0 c)\<close>
    then have \<open>\<forall>i < length (Clause_v0 c). Pasn_set pb ! unat (Lit_var (Clause_v0 c ! i))\<close>
      using uf unfolding unset_from_post_def c_def by simp
    then have \<open>conflict (Assignments_v0 (Pasn_assign pb)) (Pasn_set pb) f\<close>
      using no_unset_conflict[OF xa] ct unfolding c_def by blast
    then show False
      using nc by simp
  qed
  then show xb: \<open>unat xb < length (Clause_v0 (Formula_clauses f ! unat xa))\<close>
    using uf unfolding unset_from_post_def c_def by simp
  have vb: \<open>vars_below f (length (Assignments_v0 (Pasn_assign pb)))\<close>
    using p(2) by (rule formula_wf_vars_below)
  show v: \<open>unat (Lit_var (Clause_v0 (Formula_clauses f ! unat xa) ! unat xb)) < length (Assignments_v0 (Pasn_assign pb))\<close>
    using vb nth_mem[OF xa] nth_mem[OF xb] unfolding vars_below_def by blast
  then show \<open>unat (Lit_var (Clause_v0 (Formula_clauses f ! unat xa) ! unat xb)) < length (Pasn_set pb)\<close>
    using p(1) by simp
  show nd: \<open>\<not> Pasn_set pb ! unat (Lit_var (Clause_v0 (Formula_clauses f ! unat xa) ! unat xb))\<close>
    using uf xb unfolding unset_from_post_def by simp
  show \<open>unset ((Pasn_set pb)[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat xa) ! unat xb)) := True]) < k\<close>
    using unset_update[OF _ nd] v p(1,4) k by simp
qed

text \<open>The answer of the branch on the first unassigned literal \<open>l\<close> of the open clause \<open>c\<close>,
  given the answer \<open>r1\<close> of the recursive call that sets it to its value.\<close>
lemma solve_branch_sol:
  fixes c l :: \<open>64 word\<close> and f :: Formula
  defines \<open>v \<equiv> unat (Lit_var (Clause_v0 (Formula_clauses f ! unat c) ! unat l))\<close>
    and \<open>b \<equiv> Lit_value (Clause_v0 (Formula_clauses f ! unat c) ! unat l)\<close>
  assumes wf: \<open>formula_wf f (length a)\<close> and len: \<open>length d = length a\<close>
    and fuel: \<open>2 * length a < urust_fuel\<close> and k: \<open>unset d < Suc k\<close>
    and pr: \<open>prop_rel f a d (Assignments_v0 (Pasn_assign pb)) (Pasn_set pb)\<close>
    and st: \<open>\<forall>j < length (Formula_clauses f). settled (Assignments_v0 (Pasn_assign pb)) (Pasn_set pb) (Formula_clauses f ! j)\<close>
    and oc: \<open>open_clause_post (Assignments_v0 (Pasn_assign pb)) (Pasn_set pb) f (unat c)\<close>
    and ne: \<open>c \<noteq> word64_of_nat (length (Formula_clauses f))\<close>
    and uf: \<open>unset_from_post (Pasn_set pb) (Formula_clauses f ! unat c) 0 (unat l)\<close>
    and r1: \<open>sol f ((Assignments_v0 (Pasn_assign pb))[v := b]) ((Pasn_set pb)[v := True]) r1\<close>
    and r: \<open>case r1 of Answer_Sat m \<Rightarrow> r = Answer_Sat m
      | Answer_Unsat \<Rightarrow> sol f ((Assignments_v0 (Pasn_assign pb))[v := \<not> b]) ((Pasn_set pb)[v := True]) r\<close>
  shows \<open>sol f a d r\<close>
  using r1 r unfolding v_def b_def
  by (rule sol_prop_rel[OF pr sol_step[OF solve_branch_facts(2)[OF wf len fuel k pr st oc ne uf]
      solve_prop_facts(1)[OF wf len fuel pr] solve_branch_facts(5)[OF wf len fuel k pr st oc ne uf]]])

lemma solve_sat_leaf:
  assumes \<open>formula_wf f n\<close> \<open>prop_rel f a d (Assignments_v0 m) d'\<close>
    \<open>open_clause_post (Assignments_v0 m) d' f (unat (word64_of_nat (length (Formula_clauses f))))\<close>
  shows \<open>sol f a d (Answer_Sat m)\<close>
proof -
  have \<open>unat (word64_of_nat (length (Formula_clauses f))) = length (Formula_clauses f)\<close>
    using assms(1) unfolding formula_wf_def by (simp add: unat_of_nat_eq)
  then have \<open>formula_sat (Assignments_v0 m) f\<close>
    using assms(3) all_clause_true_formula_sat unfolding open_clause_post_def by simp
  then show ?thesis
    using assms(2) unfolding prop_rel_def sol_def by simp
qed

lemma solve_rec_step_spec:
  assumes \<open>\<And>pa. \<Gamma>; R f pa \<Turnstile>\<^sub>F solve_contract k f pa\<close>
  shows \<open>\<Gamma>; solve_rec_step R f pa \<Turnstile>\<^sub>F solve_contract (Suc k) f pa\<close>
  apply (crush_boot f: solve_rec_step_def contract: solve_contract_def)
  apply (crush_base inline: len_def
      specs add: assms propagate_spec Formula_open_clause_spec Clause_unset_from_spec
        set_var_spec copy_spec
      contracts add: solve_contract_def propagate_contract_def
        Formula_open_clause_contract_def Clause_unset_from_contract_def set_var_contract_def copy_contract_def
      simp add: true_def false_def word_less_nat_alt unat_of_nat_eq word64_eq_of_nat_iff)
  text \<open>\<open>r\<close> is the result of the propagation; \<open>pb\<close> the partial assignment it reached,
    \<open>c\<close> the index of a clause without a true literal, \<open>l\<close> that of its first unassigned literal,
    \<open>r1\<close> the answer of the branch that sets it to its value.\<close>
  subgoal for r
    apply (cases r)
     apply (crush_base simp add: prop_post_def sol_def)
    apply (crush_base inline: len_def
        specs add: assms Formula_open_clause_spec Clause_unset_from_spec set_var_spec copy_spec
        contracts add: solve_contract_def Formula_open_clause_contract_def Clause_unset_from_contract_def
          set_var_contract_def copy_contract_def
        simp add: true_def false_def prop_post_def word_less_nat_alt unat_of_nat_eq word64_eq_of_nat_iff)
    subgoal for pb c l r1
      apply (cases r1)
       apply (crush_base inline: Answer_Sat_mk_def)
      apply (crush_base specs add: assms set_var_spec contracts add: solve_contract_def set_var_contract_def)
      apply (solves \<open>rule solve_branch_sol, assumption+, simp\<close>)+
      apply (solves \<open>rule solve_branch_facts solve_prop_facts solve_open_idx; assumption\<close>)+
      done
    apply (solves \<open>rule solve_branch_facts solve_prop_facts solve_open_idx solve_sat_leaf; assumption\<close>)+
    subgoal by (rule formula_wf_clause_pre[OF solve_prop_facts(2,1) solve_open_idx])
    apply (solves \<open>rule solve_branch_facts solve_prop_facts solve_open_idx solve_sat_leaf; assumption\<close>)+
    done
  subgoal using unset_le_length[of \<open>Pasn_set pa\<close>]
    by (simp add: prop_pre_def formula_wf_def unat_of_nat_eq)
  done

lemma solve_rec_spec:
  shows \<open>\<Gamma>; (solve_rec_step ^^ k) g f pa \<Turnstile>\<^sub>F solve_contract k f pa\<close>
proof (induction k arbitrary: pa)
  case 0
  show ?case
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: solve_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  show ?case
    unfolding funpow.simps(2) comp_def by (rule solve_rec_step_spec) (rule Suc.IH)
qed

lemma solve_spec:
  shows \<open>\<Gamma>; solve f pa \<Turnstile>\<^sub>F solve_contract urust_fuel f pa\<close>
  unfolding solve_def by (rule solve_rec_spec)

end

end
