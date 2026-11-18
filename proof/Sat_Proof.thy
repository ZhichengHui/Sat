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

text \<open>An index into the clauses that is not their number is below it.\<close>
lemma formula_wf_idx:
  assumes \<open>formula_wf f n\<close> \<open>unat x \<le> length (Formula_clauses f)\<close>
    \<open>x \<noteq> word64_of_nat (length (Formula_clauses f))\<close>
  shows \<open>unat x < length (Formula_clauses f)\<close>
  using assms word_ne_length[of x \<open>length (Formula_clauses f)\<close>] unfolding formula_wf_def by simp

definition Clause_falsified_contract :: \<open>Clause \<Rightarrow> Pasn \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>Clause_falsified_contract c pa \<equiv>
     let pre = can_alloc_reference \<star> \<langle>clause_pre c pa\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>r = clause_false (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) c\<rangle> in
     make_function_contract pre post\<close>

lemma Clause_falsified_spec:
  shows \<open>\<Gamma>; Clause_falsified c pa \<Turnstile>\<^sub>F Clause_falsified_contract c pa\<close>
  apply (crush_boot f: Clause_falsified_def contract: Clause_falsified_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length (Clause_v0 c) \<and>
                (\<forall>j < unat i. Pasn_set pa ! unat (Lit_var (Clause_v0 c ! j)) \<and>
                   \<not> lit_sat (Assignments_v0 (Pasn_assign pa)) (Clause_v0 c ! j)) \<and>
                length (Clause_v0 c) - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length (Clause_v0 c) \<and>
                (\<forall>j < unat i. Pasn_set pa ! unat (Lit_var (Clause_v0 c ! j)) \<and>
                   \<not> lit_sat (Assignments_v0 (Pasn_assign pa)) (Clause_v0 c ! j)) \<and>
                length (Clause_v0 c) - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star>
               \<langle>r = clause_false (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) c\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: true_def false_def lit_sat_def clause_false_iff_nth word_less_nat_alt
        word_le_nat_alt unat_of_nat_eq unat_word_Suc_simp clause_pre_def)
    apply (auto simp add: less_Suc_eq clause_false_iff_nth lit_sat_def clause_pre_def)
    done
  done

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
  clause is unit, otherwise not below the clause's length.\<close>
definition unit_lit_post :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>unit_lit_post a d c r \<equiv>
     (r < length (Clause_v0 c) \<longrightarrow> unit_at a d c r) \<and>
     ((\<exists>k. unit_at a d c k) \<longrightarrow> r < length (Clause_v0 c))\<close>

lemma unit_lit_post_true:
  \<open>clause_true a d c \<Longrightarrow> unit_lit_post a d c (length (Clause_v0 c))\<close>
  unfolding unit_lit_post_def using clause_true_not_unit by blast

lemma unit_lit_post_all_set:
  assumes \<open>unset_from_post d c 0 (length (Clause_v0 c))\<close>
  shows \<open>unit_lit_post a d c (Suc (length (Clause_v0 c)))\<close>
proof -
  have \<open>\<forall>j < length (Clause_v0 c). d ! unat (Lit_var (Clause_v0 c ! j))\<close>
    using assms unfolding unset_from_post_def by simp
  then have \<open>\<forall>k. \<not> unit_at a d c k\<close>
    using all_set_not_unit by blast
  then show ?thesis
    unfolding unit_lit_post_def by simp
qed

lemma unit_lit_post_two:
  \<open>unset_from_post d c 0 k \<Longrightarrow> k < length (Clause_v0 c) \<Longrightarrow> unset_from_post d c (Suc k) k2 \<Longrightarrow>
    k2 < length (Clause_v0 c) \<Longrightarrow> unit_lit_post a d c (length (Clause_v0 c))\<close>
  unfolding unit_lit_post_def unset_from_post_def using two_unset_not_unit[of k k2 c d a]
  by auto

lemma unit_lit_post_one:
  \<open>\<not> clause_true a d c \<Longrightarrow> unset_from_post d c 0 k \<Longrightarrow> k < length (Clause_v0 c) \<Longrightarrow>
    unset_from_post d c (Suc k) (length (Clause_v0 c)) \<Longrightarrow> unit_lit_post a d c k\<close>
  unfolding unit_lit_post_def unset_from_post_def using one_unset_unit[of a d c k] by auto

definition Clause_unit_lit_contract :: \<open>Clause \<Rightarrow> Pasn \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Clause_unit_lit_contract c pa \<equiv>
     let pre = can_alloc_reference \<star> \<langle>clause_pre c pa\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>unit_lit_post (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) c (unat r)\<rangle> in
     make_function_contract pre post\<close>

lemma Clause_unit_lit_spec:
  shows \<open>\<Gamma>; Clause_unit_lit c pa \<Turnstile>\<^sub>F Clause_unit_lit_contract c pa\<close>
  apply (crush_boot f: Clause_unit_lit_def contract: Clause_unit_lit_contract_def)
  apply (crush_base inline: len_def
      specs add: Clause_has_true_spec Clause_unset_from_spec
      contracts add: Clause_has_true_contract_def Clause_unset_from_contract_def
      simp add: true_def false_def word_less_nat_alt unat_of_nat_eq unat_word_Suc_simp
        word64_eq_of_nat_iff clause_pre_def)
  subgoal premises prems for x xa
  proof -
    have x: \<open>unat x < length (Clause_v0 c)\<close>
      using prems(5,6) unfolding unset_from_post_def by simp
    have s: \<open>unat (x + 1) = Suc (unat x)\<close>
      using unat_word_Suc[of x \<open>length (Clause_v0 c)\<close>] x prems(3) by simp
    have xa: \<open>unat xa = length (Clause_v0 c)\<close>
      using prems(7,8) unfolding unset_from_post_def by simp
    show ?thesis
      using unit_lit_post_one[OF prems(4,5) x] prems(7) s xa by simp
  qed
  subgoal premises prems for x xa
  proof -
    have x: \<open>unat x < length (Clause_v0 c)\<close>
      using prems(5,6) unfolding unset_from_post_def by simp
    have s: \<open>unat (x + 1) = Suc (unat x)\<close>
      using unat_word_Suc[of x \<open>length (Clause_v0 c)\<close>] x prems(3) by simp
    show ?thesis
      using unit_lit_post_two[OF prems(5) x _ prems(8)] prems(7) s by simp
  qed
  subgoal premises prems for x
  proof -
    have x: \<open>unat x < length (Clause_v0 c)\<close>
      using prems(5,6) unfolding unset_from_post_def by simp
    have s: \<open>unat (x + 1) = Suc (unat x)\<close>
      using unat_word_Suc[of x \<open>length (Clause_v0 c)\<close>] x prems(3) by simp
    show ?thesis
      using x s by simp
  qed
  subgoal premises prems for x
  proof -
    have x: \<open>unat x < length (Clause_v0 c)\<close>
      using prems(5,6) unfolding unset_from_post_def by simp
    then show ?thesis
      using prems(3) by simp
  qed
  subgoal premises prems
    by (rule unit_lit_post_all_set[OF prems(5)])
  subgoal premises prems
    by (rule unit_lit_post_true[OF prems(4)])
  done

definition Formula_unit_clause_contract :: \<open>Formula \<Rightarrow> Pasn \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Formula_unit_clause_contract f pa s \<equiv>
     let a = Assignments_v0 (Pasn_assign pa) in
     let pre = can_alloc_reference \<star>
        \<langle>formula_wf f (length a) \<and> length (Pasn_set pa) = length a \<and>
         unat s \<le> length (Formula_clauses f)\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>unat r \<le> length (Formula_clauses f)\<rangle> in
     make_function_contract pre post\<close>

text \<open>Only the bound of the result is needed: \<^verbatim>\<open>propagate\<close> calls \<^verbatim>\<open>Clause::unit_lit\<close> again
  on the clause found.\<close>
lemma Formula_unit_clause_spec:
  shows \<open>\<Gamma>; Formula_unit_clause f pa s \<Turnstile>\<^sub>F Formula_unit_clause_contract f pa s\<close>
  apply (crush_boot f: Formula_unit_clause_def contract: Formula_unit_clause_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length (Formula_clauses f) \<and> length (Formula_clauses f) - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length (Formula_clauses f) \<and> length (Formula_clauses f) - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>unat r \<le> length (Formula_clauses f)\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def specs add: Clause_unit_lit_spec contracts add: Clause_unit_lit_contract_def
        simp add: true_def false_def formula_wf_clause_pre word_less_nat_alt unat_of_nat_eq unat_word_Suc_simp)
    apply (auto simp add: less_Suc_eq formula_wf_def unat_of_nat_eq unat_word_Suc_simp)
    done
  done

definition Formula_conflict_contract :: \<open>Formula \<Rightarrow> Pasn \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>Formula_conflict_contract f pa \<equiv>
     let a = Assignments_v0 (Pasn_assign pa) in
     let pre = can_alloc_reference \<star> \<langle>formula_wf f (length a) \<and> length (Pasn_set pa) = length a\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = conflict a (Pasn_set pa) f\<rangle> in
     make_function_contract pre post\<close>

lemma Formula_conflict_spec:
  shows \<open>\<Gamma>; Formula_conflict f pa \<Turnstile>\<^sub>F Formula_conflict_contract f pa\<close>
  apply (crush_boot f: Formula_conflict_def contract: Formula_conflict_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length (Formula_clauses f) \<and>
                (\<forall>j < unat i. \<not> clause_false (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa)
                   (Formula_clauses f ! j)) \<and>
                length (Formula_clauses f) - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length (Formula_clauses f) \<and>
                (\<forall>j < unat i. \<not> clause_false (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa)
                   (Formula_clauses f ! j)) \<and>
                length (Formula_clauses f) - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = conflict (Assignments_v0 (Pasn_assign pa)) (Pasn_set pa) f\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def specs add: Clause_falsified_spec contracts add: Clause_falsified_contract_def
        simp add: true_def false_def conflict_iff_nth formula_wf_clause_pre word_less_nat_alt unat_of_nat_eq
          unat_word_Suc_simp)
    apply (auto simp add: less_Suc_eq conflict_iff_nth formula_wf_def unat_of_nat_eq unat_word_Suc_simp)
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

text \<open>The facts about one step of \<^verbatim>\<open>propagate\<close> in the form the proof of its body needs them:
  the clause \<open>x\<close> found from \<open>s\<close> on is unit with the unassigned literal \<open>xa\<close>.\<close>
lemma propagate_step_facts:
  assumes wf: \<open>formula_wf f (length a)\<close> and len: \<open>length d = length a\<close>
    and s: \<open>unat s \<le> length (Formula_clauses f)\<close>
    and k: \<open>2 * unset d + min (Suc 0) (unat s) < Suc k\<close>
    and uc: \<open>unat x \<le> length (Formula_clauses f)\<close>
    and ne: \<open>x \<noteq> word64_of_nat (length (Formula_clauses f))\<close>
    and ul: \<open>unit_lit_post a d (Formula_clauses f ! unat x) (unat xa)\<close>
    and nk: \<open>\<not> unat (word64_of_nat (length (Clause_v0 (Formula_clauses f ! unat x)))) \<le> unat xa\<close>
  shows \<open>prop_rel f a d
       (a[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) :=
          Lit_value (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)])
       (d[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) := True])\<close>
    \<open>2 * unset (d[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) := True]) +
       min (Suc 0) (unat (x + 1)) < k\<close>
    \<open>unat (x + 1) \<le> length (Formula_clauses f)\<close>
    \<open>unat x < 18446744073709551615\<close>
    \<open>unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) < length a\<close>
    \<open>unat xa < length (Clause_v0 (Formula_clauses f ! unat x))\<close>
    \<open>unat x < length (Formula_clauses f)\<close>
proof -
  have lf: \<open>length (Formula_clauses f) < 2^64\<close>
    using wf unfolding formula_wf_def by simp
  show x: \<open>unat x < length (Formula_clauses f)\<close>
    by (rule formula_wf_idx[OF wf uc ne])
  define c where \<open>c = Formula_clauses f ! unat x\<close>
  have c: \<open>c \<in> set (Formula_clauses f)\<close>
    using x unfolding c_def by simp
  have \<open>length (Clause_v0 c) < 2^63\<close>
    using wf c unfolding formula_wf_def by blast
  then show xa: \<open>unat xa < length (Clause_v0 (Formula_clauses f ! unat x))\<close>
    using nk unfolding c_def by (simp add: unat_of_nat_eq)
  have u: \<open>unit_at a d c (unat xa)\<close>
    using ul xa unfolding unit_lit_post_def c_def by blast
  have vb: \<open>vars_below f (length a)\<close>
    using wf by (rule formula_wf_vars_below)
  show v: \<open>unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) < length a\<close>
    using vb c xa nth_mem[OF xa] unfolding vars_below_def c_def by blast
  have nd: \<open>\<not> d ! unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa))\<close>
    using u unfolding unit_at_def c_def by simp
  have \<open>min (Suc 0) (unat (x + 1)) \<le> Suc 0\<close>
    by simp
  then show \<open>2 * unset (d[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) := True]) +
       min (Suc 0) (unat (x + 1)) < k\<close>
    using unset_update[OF _ nd] v len k by simp
  show \<open>prop_rel f a d
       (a[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) :=
          Lit_value (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)])
       (d[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) := True])\<close>
    using prop_rel_unit[OF c u vb len] unfolding c_def .
  show \<open>unat (x + 1) \<le> length (Formula_clauses f)\<close>
    using unat_word_Suc[OF x lf] x by simp
  show \<open>unat x < 18446744073709551615\<close>
    using x lf by simp
qed

text \<open>The \<open>k\<close>-th unfolding of \<^const>\<open>propagate\<close>. Each recursive call either assigns one
  more variable or restarts the search for a unit clause from the first one, which it does not
  do twice in a row: twice the number of unassigned variables, plus one if \<open>s\<close> is not \<open>0\<close>,
  decreases and must be below \<open>k\<close>.\<close>
definition propagate_contract :: \<open>nat \<Rightarrow> Formula \<Rightarrow> Pasn \<Rightarrow> 64 word \<Rightarrow> ('s, Pasn, 'abort) function_contract\<close> where
  \<open>propagate_contract k f pa s \<equiv>
     let a = Assignments_v0 (Pasn_assign pa) in
     let d = Pasn_set pa in
     let pre = can_alloc_reference \<star>
        \<langle>formula_wf f (length a) \<and> length d = length a \<and> unat s \<le> length (Formula_clauses f) \<and>
         2 * unset d + min 1 (unat s) < k\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>prop_rel f a d (Assignments_v0 (Pasn_assign r)) (Pasn_set r)\<rangle> in
     make_function_contract pre post\<close>

lemma propagate_rec_step_spec:
  assumes \<open>\<And>pa s. \<Gamma>; R f pa s \<Turnstile>\<^sub>F propagate_contract k f pa s\<close>
  shows \<open>\<Gamma>; propagate_rec_step R f pa s \<Turnstile>\<^sub>F propagate_contract (Suc k) f pa s\<close>
  apply (crush_boot f: propagate_rec_step_def contract: propagate_contract_def)
  apply (crush_base inline: len_def
      specs add: assms Formula_unit_clause_spec Clause_unit_lit_spec set_var_spec
      contracts add: propagate_contract_def Formula_unit_clause_contract_def Clause_unit_lit_contract_def
        set_var_contract_def
      simp add: true_def false_def word_less_nat_alt word_le_nat_alt unat_of_nat_eq word64_eq_of_nat_iff
        prop_rel_refl)
  subgoal premises prems
    using prop_rel_trans[OF propagate_step_facts(1)[OF prems(1-8)] prems(9)] .
  subgoal premises prems by (rule propagate_step_facts(2)[OF prems(1-8)])
  subgoal premises prems by (rule propagate_step_facts(3)[OF prems(1-8)])
  subgoal premises prems by (rule propagate_step_facts(4)[OF prems(1-8)])
  subgoal premises prems by (rule propagate_step_facts(5)[OF prems(1-8)])
  subgoal premises prems by (rule propagate_step_facts(6)[OF prems(1-8)])
  subgoal premises prems by (rule propagate_step_facts(7)[OF prems(1-8)])
  subgoal premises prems by (rule propagate_step_facts(6)[OF prems(1-8)])
  subgoal premises prems by (rule propagate_step_facts(7)[OF prems(1-8)])
  subgoal premises prems by (rule formula_wf_idx[OF prems(1,5,6)])
  subgoal premises prems
    by (rule formula_wf_clause_pre[OF prems(1,2) formula_wf_idx[OF prems(1,5,6)]])
  subgoal premises prems by (rule formula_wf_idx[OF prems(1,5,6)])
  subgoal premises prems
    using prems(4,6) unat_gt_0[of s] by (simp add: min_def split: if_splits)
  done

lemma propagate_rec_spec:
  shows \<open>\<Gamma>; (propagate_rec_step ^^ k) g f pa s \<Turnstile>\<^sub>F propagate_contract k f pa s\<close>
proof (induction k arbitrary: pa s)
  case 0
  show ?case
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>)
    apply (subst wp_sstriple_iff)
    apply (simp add: propagate_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  show ?case
    unfolding funpow.simps(2) comp_def by (rule propagate_rec_step_spec) (rule Suc.IH)
qed

lemma propagate_spec:
  shows \<open>\<Gamma>; propagate f pa s \<Turnstile>\<^sub>F propagate_contract urust_fuel f pa s\<close>
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
  using formula_wf_idx[OF assms(1) _ assms(3)] assms(2) unfolding open_clause_post_def by simp

lemma solve_branch_facts:
  assumes wf: \<open>formula_wf f (length a)\<close> and len: \<open>length d = length a\<close>
    and fuel: \<open>2 * length a < urust_fuel\<close> and k: \<open>unset d < Suc k\<close>
    and pr: \<open>prop_rel f a d (Assignments_v0 (Pasn_assign pb)) (Pasn_set pb)\<close>
    and nc: \<open>\<not> conflict (Assignments_v0 (Pasn_assign pb)) (Pasn_set pb) f\<close>
    and oc: \<open>open_clause_post (Assignments_v0 (Pasn_assign pb)) (Pasn_set pb) f (unat xa)\<close>
    and ne: \<open>xa \<noteq> word64_of_nat (length (Formula_clauses f))\<close>
    and uf: \<open>unset_from_post (Pasn_set pb) (Formula_clauses f ! unat xa) 0 (unat xb)\<close>
  shows \<open>unat xa < length (Formula_clauses f)\<close>
    \<open>unat xb < length (Clause_v0 (Formula_clauses f ! unat xa))\<close>
    \<open>unat (Lit_var (Clause_v0 (Formula_clauses f ! unat xa) ! unat xb)) < length (Assignments_v0 (Pasn_assign pb))\<close>
    \<open>unat (Lit_var (Clause_v0 (Formula_clauses f ! unat xa) ! unat xb)) < length (Pasn_set pb)\<close>
    \<open>unset ((Pasn_set pb)[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat xa) ! unat xb)) := True]) < k\<close>
    \<open>\<not> Pasn_set pb ! unat (Lit_var (Clause_v0 (Formula_clauses f ! unat xa) ! unat xb))\<close>
proof -
  note p = solve_prop_facts[OF wf len fuel pr]
  show xa: \<open>unat xa < length (Formula_clauses f)\<close>
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

lemma solve_conflict_leaf:
  assumes \<open>formula_wf f (length a)\<close> \<open>length d = length a\<close> \<open>prop_rel f a d a' d'\<close> \<open>conflict a' d' f\<close>
  shows \<open>sol f a d Answer_Unsat\<close>
proof -
  have \<open>vars_below f (length d')\<close>
    using assms(1-3) formula_wf_vars_below unfolding prop_rel_def more_set_def by simp
  then have \<open>\<not> ext_sat f a' d'\<close>
    using conflict_not_ext_sat[OF assms(4)] by simp
  then show ?thesis
    using assms(3) unfolding prop_rel_def sol_def by simp
qed

lemma solve_rec_step_spec:
  assumes \<open>\<And>pa. \<Gamma>; R f pa \<Turnstile>\<^sub>F solve_contract k f pa\<close>
  shows \<open>\<Gamma>; solve_rec_step R f pa \<Turnstile>\<^sub>F solve_contract (Suc k) f pa\<close>
  apply (crush_boot f: solve_rec_step_def contract: solve_contract_def)
  apply (crush_base inline: len_def
      specs add: assms propagate_spec Formula_conflict_spec Formula_open_clause_spec Clause_unset_from_spec
        set_var_spec
      contracts add: solve_contract_def propagate_contract_def Formula_conflict_contract_def
        Formula_open_clause_contract_def Clause_unset_from_contract_def set_var_contract_def
      simp add: true_def false_def word_less_nat_alt unat_of_nat_eq word64_eq_of_nat_iff)
  subgoal for x xa xb xc
    apply (cases xc)
     apply (crush_base inline: Answer_Sat_mk_def)
    apply (crush_base specs add: assms set_var_spec contracts add: solve_contract_def set_var_contract_def)
    subgoal premises prems
      using sol_prop_rel[OF prems(5) sol_step[OF solve_branch_facts(3)[OF prems(1-9)]
          solve_prop_facts(1)[OF prems(1-3,5)] solve_branch_facts(6)[OF prems(1-9)] prems(10)]]
      by simp
    subgoal premises prems
      using sol_prop_rel[OF prems(5) sol_step[OF solve_branch_facts(3)[OF prems(1-9)]
          solve_prop_facts(1)[OF prems(1-3,5)] solve_branch_facts(6)[OF prems(1-9)] prems(10)]] prems(12)
      by simp
    subgoal premises prems by (rule solve_branch_facts(5)[OF prems(1-9)])
    subgoal premises prems by (rule solve_prop_facts(3)[OF prems(1-3,5)])
    subgoal premises prems by (rule solve_prop_facts(1)[OF prems(1-3,5)])
    subgoal premises prems by (rule solve_prop_facts(2)[OF prems(1-3,5)])
    subgoal premises prems by (rule solve_branch_facts(3,4)[OF prems(1-9)])
    subgoal premises prems by (rule solve_branch_facts(3,4)[OF prems(1-9)])
    done
  subgoal premises prems by (rule solve_branch_facts(5)[OF prems(1-9)])
  subgoal premises prems by (rule solve_prop_facts(3)[OF prems(1-3,5)])
  subgoal premises prems by (rule solve_prop_facts(1)[OF prems(1-3,5)])
  subgoal premises prems by (rule solve_prop_facts(2)[OF prems(1-3,5)])
  subgoal premises prems by (rule solve_branch_facts(4)[OF prems(1-9)])
  subgoal premises prems by (rule solve_branch_facts(3)[OF prems(1-9)])
  subgoal premises prems by (rule solve_branch_facts(2)[OF prems(1-9)])
  subgoal premises prems by (rule solve_branch_facts(1)[OF prems(1-9)])
  subgoal premises prems by (rule solve_branch_facts(2)[OF prems(1-9)])
  subgoal premises prems by (rule solve_branch_facts(1)[OF prems(1-9)])
  subgoal premises prems
    by (rule formula_wf_clause_pre[OF solve_prop_facts(2,1)[OF prems(1-3,5)] solve_open_idx[OF prems(1,7,8)]])
  subgoal premises prems by (rule solve_open_idx[OF prems(1,7,8)])
  subgoal premises prems by (rule solve_sat_leaf[OF prems(1,5,7)])
  subgoal premises prems by (rule solve_prop_facts(1)[OF prems(1-3,5)])
  subgoal premises prems by (rule solve_prop_facts(2)[OF prems(1-3,5)])
  subgoal premises prems by (rule solve_conflict_leaf[OF prems(1,2,5,6)])
  subgoal premises prems by (rule solve_prop_facts(1)[OF prems(1-3,5)])
  subgoal premises prems by (rule solve_prop_facts(2)[OF prems(1-3,5)])
  subgoal premises prems using unset_le_length[of \<open>Pasn_set pa\<close>] prems(2,3) by simp
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
