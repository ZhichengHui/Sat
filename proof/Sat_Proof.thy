theory Sat_Proof
  imports Sat_Spec.Sat_Spec
begin

text \<open>The contracts of the functions of \<^verbatim>\<open>core/src/lib.rs\<close> and their proofs: the verification
  of Friday (CreuSAT) carried over to the AutoCorrode translation, with \<^verbatim>\<open>solve\<close> returning
  a satisfying assignment (\<open>sol\<close>). \<^verbatim>\<open>Sat_Top\<close> derives the contract of the specification.\<close>

section \<open>Pure facts\<close>

lemma clause_sat_iff_nth:
  \<open>clause_sat a c \<longleftrightarrow>
     (\<exists>j < length (Clause_v0 c). a ! unat (Lit_var (Clause_v0 c ! j)) = Lit_value (Clause_v0 c ! j))\<close>
  unfolding clause_sat_def lit_sat_def Bex_def in_set_conv_nth by blast

lemma formula_sat_iff_nth:
  \<open>formula_sat a f \<longleftrightarrow> (\<forall>j < length (Formula_clauses f). clause_sat a (Formula_clauses f ! j))\<close>
  unfolding formula_sat_def by (simp add: all_set_conv_all_nth)

text \<open>A partial assignment is a pair \<open>(a, d)\<close>: the variable \<open>v\<close> is assigned iff \<open>d ! v\<close>, and
  then has the value \<open>a ! v\<close>. The assignment \<open>a'\<close> agrees with it if it gives every assigned
  variable its value.\<close>
definition agree :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>agree d a a' \<equiv> \<forall>v < length d. d ! v \<longrightarrow> a' ! v = a ! v\<close>

text \<open>Some assignment that agrees with the partial assignment satisfies \<open>f\<close>.\<close>
definition ext_sat :: \<open>Formula \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>ext_sat f a d \<equiv> \<exists>a'. length a' = length a \<and> agree d a a' \<and> formula_sat a' f\<close>

text \<open>\<open>d'\<close> assigns at least the variables of \<open>d\<close>.\<close>
definition more_set :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>more_set d d' \<equiv> length d' = length d \<and> (\<forall>v < length d. d ! v \<longrightarrow> d' ! v)\<close>

lemma agree_trans:
  assumes \<open>agree d a b\<close> \<open>agree d b c\<close>
  shows \<open>agree d a c\<close>
  using assms unfolding agree_def by simp

lemma agree_more_set:
  assumes \<open>more_set d d'\<close> \<open>agree d' a b\<close>
  shows \<open>agree d a b\<close>
  using assms unfolding agree_def more_set_def by simp

lemma more_set_update:
  \<open>more_set d (d[v := True])\<close>
  unfolding more_set_def
proof (intro conjI allI impI)
  fix u assume \<open>u < length d\<close> \<open>d ! u\<close>
  then show \<open>d[v := True] ! u\<close>
    by (cases \<open>v = u\<close>) (simp_all add: nth_list_update_neq)
qed simp

lemma agree_update_self:
  assumes \<open>\<not> d ! v\<close>
  shows \<open>agree d a (a[v := b])\<close>
  unfolding agree_def
proof (intro allI impI)
  fix u assume \<open>u < length d\<close> \<open>d ! u\<close>
  then have \<open>v \<noteq> u\<close> using assms by auto
  then show \<open>a[v := b] ! u = a ! u\<close> by (simp add: nth_list_update_neq)
qed

lemma agree_update:
  assumes \<open>agree (d[v := True]) (a[v := b]) m\<close> \<open>\<not> d ! v\<close>
  shows \<open>agree d a m\<close>
  unfolding agree_def
proof (intro allI impI)
  fix u assume u: \<open>u < length d\<close> \<open>d ! u\<close>
  then have vu: \<open>v \<noteq> u\<close> using assms(2) by auto
  have \<open>u < length (d[v := True])\<close> \<open>d[v := True] ! u\<close>
    using u vu by (simp_all add: nth_list_update_neq)
  then have \<open>m ! u = a[v := b] ! u\<close>
    using assms(1) unfolding agree_def by blast
  then show \<open>m ! u = a ! u\<close>
    using vu by (simp add: nth_list_update_neq)
qed

lemma agree_update_intro:
  assumes \<open>agree d a m\<close> \<open>m ! v = b\<close> \<open>v < length a\<close>
  shows \<open>agree (d[v := True]) (a[v := b]) m\<close>
  unfolding agree_def
proof (intro allI impI)
  fix u assume u: \<open>u < length (d[v := True])\<close> \<open>d[v := True] ! u\<close>
  show \<open>m ! u = a[v := b] ! u\<close>
  proof (cases \<open>u = v\<close>)
    case True
    then show ?thesis using assms(2,3) by simp
  next
    case False
    then have vu: \<open>v \<noteq> u\<close> by simp
    then have \<open>u < length d\<close> \<open>d ! u\<close>
      using u by (simp_all add: nth_list_update_neq)
    then have \<open>m ! u = a ! u\<close>
      using assms(1) unfolding agree_def by blast
    then show ?thesis
      using vu by (simp add: nth_list_update_neq)
  qed
qed

lemma ext_sat_step:
  assumes \<open>v < length a\<close> \<open>length d = length a\<close> \<open>\<not> d ! v\<close>
  shows \<open>ext_sat f a d \<longleftrightarrow>
    ext_sat f (a[v := True]) (d[v := True]) \<or> ext_sat f (a[v := False]) (d[v := True])\<close>
proof
  assume \<open>ext_sat f a d\<close>
  then obtain a' where a': \<open>length a' = length a\<close> \<open>agree d a a'\<close> \<open>formula_sat a' f\<close>
    unfolding ext_sat_def by blast
  have \<open>agree (d[v := True]) (a[v := a' ! v]) a'\<close>
    using a'(2) assms unfolding agree_def by (simp add: nth_list_update)
  then have \<open>ext_sat f (a[v := a' ! v]) (d[v := True])\<close>
    using a' unfolding ext_sat_def by auto
  then show \<open>ext_sat f (a[v := True]) (d[v := True]) \<or> ext_sat f (a[v := False]) (d[v := True])\<close>
    by (cases \<open>a' ! v\<close>) simp_all
next
  have \<open>ext_sat f a d\<close> if h: \<open>ext_sat f (a[v := b]) (d[v := True])\<close> for b
  proof -
    obtain a' where a': \<open>length a' = length a\<close> \<open>agree (d[v := True]) (a[v := b]) a'\<close>
      \<open>formula_sat a' f\<close>
      using h unfolding ext_sat_def length_list_update by blast
    have \<open>agree d a a'\<close>
      using a'(2) assms(3) by (rule agree_update)
    then show ?thesis
      using a' unfolding ext_sat_def by blast
  qed
  then show \<open>ext_sat f (a[v := True]) (d[v := True]) \<or> ext_sat f (a[v := False]) (d[v := True]) \<Longrightarrow>
      ext_sat f a d\<close>
    by blast
qed

lemma ext_sat_step_value:
  assumes \<open>v < length a\<close> \<open>length d = length a\<close> \<open>\<not> d ! v\<close>
  shows \<open>ext_sat f a d \<longleftrightarrow>
    ext_sat f (a[v := b]) (d[v := True]) \<or> ext_sat f (a[v := \<not> b]) (d[v := True])\<close>
  using ext_sat_step[OF assms, of f] by (cases b) auto

lemma ext_sat_start:
  \<open>ext_sat f (replicate n False) (replicate n False) \<longleftrightarrow> (\<exists>a. length a = n \<and> formula_sat a f)\<close>
  unfolding ext_sat_def agree_def by simp

text \<open>The answer \<open>r\<close> is right for the subproblem of the partial assignment \<open>(a, d)\<close>:
  \<^verbatim>\<open>Sat(m)\<close> gives a satisfying assignment \<open>m\<close> of the same length that agrees with it;
  \<^verbatim>\<open>Unsat\<close> means that there is none.\<close>
definition sol :: \<open>Formula \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> Answer \<Rightarrow> bool\<close> where
  \<open>sol f a d r \<equiv> case r of
     Answer_Sat m \<Rightarrow> length (Assignments_v0 m) = length a \<and> agree d a (Assignments_v0 m) \<and>
       formula_sat (Assignments_v0 m) f
   | Answer_Unsat \<Rightarrow> \<not> ext_sat f a d\<close>

lemma sol_step:
  assumes \<open>v < length a\<close> \<open>length d = length a\<close> \<open>\<not> d ! v\<close>
    \<open>sol f (a[v := b]) (d[v := True]) r1\<close>
    \<open>case r1 of Answer_Sat m \<Rightarrow> r = Answer_Sat m | Answer_Unsat \<Rightarrow> sol f (a[v := \<not> b]) (d[v := True]) r\<close>
  shows \<open>sol f a d r\<close>
proof -
  have ag: \<open>agree d a m\<close> if \<open>agree (d[v := True]) (a[v := b']) m\<close> for m b'
    using that assms(3) by (rule agree_update)
  show ?thesis
  proof (cases r1)
    case (Answer_Sat m)
    then show ?thesis using assms(4,5) by (auto simp add: sol_def intro: ag)
  next
    case Answer_Unsat
    then have u: \<open>\<not> ext_sat f (a[v := b]) (d[v := True])\<close>
      and r: \<open>sol f (a[v := \<not> b]) (d[v := True]) r\<close>
      using assms(4,5) by (simp_all add: sol_def)
    show ?thesis
    proof (cases r)
      case (Answer_Sat m)
      then show ?thesis using r by (auto simp add: sol_def intro: ag)
    next
      case Answer_Unsat
      then show ?thesis using r u ext_sat_step_value[OF assms(1-3), of f b] by (simp add: sol_def)
    qed
  qed
qed

lemma sol_start:
  assumes \<open>sol f (replicate n False) (replicate n False) r\<close>
  shows \<open>case r of
     Answer_Sat a \<Rightarrow> length (Assignments_v0 a) = n \<and> formula_sat (Assignments_v0 a) f
   | Answer_Unsat \<Rightarrow> (\<forall>a. length a = n \<longrightarrow> \<not> formula_sat a f)\<close>
  using assms by (cases r) (auto simp add: sol_def ext_sat_start)

text \<open>The clause is false under the partial assignment: every literal's variable is assigned and
  has the other value.\<close>
definition clause_false :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow> bool\<close> where
  \<open>clause_false a d c \<equiv> \<forall>l \<in> set (Clause_v0 c). d ! unat (Lit_var l) \<and> \<not> lit_sat a l\<close>

text \<open>Some clause of the formula is false under that partial assignment.\<close>
definition conflict :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Formula \<Rightarrow> bool\<close> where
  \<open>conflict a d f \<equiv> \<exists>c \<in> set (Formula_clauses f). clause_false a d c\<close>

lemma clause_false_iff_nth:
  \<open>clause_false a d c \<longleftrightarrow>
     (\<forall>j < length (Clause_v0 c). d ! unat (Lit_var (Clause_v0 c ! j)) \<and>
        a ! unat (Lit_var (Clause_v0 c ! j)) \<noteq> Lit_value (Clause_v0 c ! j))\<close>
  unfolding clause_false_def lit_sat_def by (simp add: all_set_conv_all_nth)

lemma conflict_iff_nth:
  \<open>conflict a d f \<longleftrightarrow> (\<exists>j < length (Formula_clauses f). clause_false a d (Formula_clauses f ! j))\<close>
  unfolding conflict_def by (simp add: Bex_def in_set_conv_nth) blast

text \<open>Every literal's variable of the formula is below \<open>n\<close>.\<close>
definition vars_below :: \<open>Formula \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>vars_below f n \<equiv> \<forall>c \<in> set (Formula_clauses f). \<forall>l \<in> set (Clause_v0 c). unat (Lit_var l) < n\<close>

text \<open>A conflict of the partial assignment excludes all its extensions.\<close>
lemma conflict_not_ext_sat:
  assumes \<open>conflict a d f\<close> \<open>vars_below f (length d)\<close>
  shows \<open>\<not> ext_sat f a d\<close>
proof
  assume \<open>ext_sat f a d\<close>
  then obtain a' where a': \<open>agree d a a'\<close> \<open>formula_sat a' f\<close>
    unfolding ext_sat_def by blast
  obtain c where c: \<open>c \<in> set (Formula_clauses f)\<close> \<open>clause_false a d c\<close>
    using assms unfolding conflict_def by blast
  have \<open>\<not> clause_sat a' c\<close>
    using c assms(2) a'(1)
    unfolding clause_false_def clause_sat_def lit_sat_def agree_def vars_below_def by fastforce
  then show False
    using a'(2) c(1) unfolding formula_sat_def by blast
qed

text \<open>Without a conflict, an assignment of every variable satisfies the formula.\<close>
lemma no_conflict_formula_sat:
  assumes \<open>\<not> conflict a d f\<close> \<open>\<forall>v < length d. d ! v\<close> \<open>vars_below f (length d)\<close>
  shows \<open>formula_sat a f\<close>
  using assms unfolding conflict_def clause_false_def formula_sat_def clause_sat_def vars_below_def
  by blast

text \<open>The clause is unit under the partial assignment, with \<open>k\<close> the index of its only
  unassigned literal: every other literal is assigned and false.\<close>
definition unit_at :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>unit_at a d c k \<equiv> k < length (Clause_v0 c) \<and> \<not> d ! unat (Lit_var (Clause_v0 c ! k)) \<and>
     (\<forall>j < length (Clause_v0 c). j \<noteq> k \<longrightarrow>
        d ! unat (Lit_var (Clause_v0 c ! j)) \<and> \<not> lit_sat a (Clause_v0 c ! j))\<close>

text \<open>The partial assignment \<open>(a', d')\<close> extends \<open>(a, d)\<close> and has the same extensions that
  satisfy \<open>f\<close>: the relation between the input and the output of unit propagation.\<close>
definition prop_rel :: \<open>Formula \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool\<close> where
  \<open>prop_rel f a d a' d' \<equiv>
     length a' = length a \<and> more_set d d' \<and> agree d a a' \<and> (ext_sat f a' d' \<longleftrightarrow> ext_sat f a d)\<close>

lemma prop_rel_refl:
  \<open>prop_rel f a d a d\<close>
  unfolding prop_rel_def more_set_def agree_def by simp

lemma prop_rel_trans:
  assumes \<open>prop_rel f a d a' d'\<close> \<open>prop_rel f a' d' a'' d''\<close>
  shows \<open>prop_rel f a d a'' d''\<close>
  using assms unfolding prop_rel_def more_set_def agree_def by auto

text \<open>Assigning the remaining literal of a unit clause keeps the extensions that satisfy \<open>f\<close>.\<close>
lemma prop_rel_unit:
  assumes \<open>c \<in> set (Formula_clauses f)\<close> \<open>unit_at a d c k\<close> \<open>vars_below f (length a)\<close>
    \<open>length d = length a\<close>
  shows \<open>prop_rel f a d (a[unat (Lit_var (Clause_v0 c ! k)) := Lit_value (Clause_v0 c ! k)])
    (d[unat (Lit_var (Clause_v0 c ! k)) := True])\<close>
proof -
  define v where \<open>v = unat (Lit_var (Clause_v0 c ! k))\<close>
  define b where \<open>b = Lit_value (Clause_v0 c ! k)\<close>
  have k: \<open>k < length (Clause_v0 c)\<close> \<open>\<not> d ! v\<close>
    using assms(2) unfolding unit_at_def v_def by simp_all
  have v: \<open>v < length a\<close>
    using assms(1,3) k(1) unfolding vars_below_def v_def by (meson nth_mem)
  have ag: \<open>agree d a (a[v := b])\<close>
    using k(2) by (rule agree_update_self)
  have ms: \<open>more_set d (d[v := True])\<close>
    by (rule more_set_update)
  have \<open>ext_sat f (a[v := b]) (d[v := True])\<close> if h: \<open>ext_sat f a d\<close>
  proof -
    obtain a' where a': \<open>length a' = length a\<close> \<open>agree d a a'\<close> \<open>formula_sat a' f\<close>
      using h unfolding ext_sat_def by blast
    have \<open>clause_sat a' c\<close>
      using a'(3) assms(1) unfolding formula_sat_def by blast
    then obtain j where j: \<open>j < length (Clause_v0 c)\<close> \<open>lit_sat a' (Clause_v0 c ! j)\<close>
      using clause_sat_iff_nth[of a' c] unfolding lit_sat_def by blast
    have \<open>j = k\<close>
    proof (rule ccontr)
      assume \<open>j \<noteq> k\<close>
      then have \<open>d ! unat (Lit_var (Clause_v0 c ! j))\<close> \<open>\<not> lit_sat a (Clause_v0 c ! j)\<close>
        using assms(2) j(1) unfolding unit_at_def by auto
      moreover have \<open>unat (Lit_var (Clause_v0 c ! j)) < length d\<close>
        using assms(1,3,4) j(1) nth_mem[of j \<open>Clause_v0 c\<close>] unfolding vars_below_def by auto
      ultimately show False
        using a'(2) j(2) unfolding agree_def lit_sat_def by simp
    qed
    then have \<open>a' ! v = b\<close>
      using j(2) unfolding lit_sat_def v_def b_def by simp
    then have \<open>agree (d[v := True]) (a[v := b]) a'\<close>
      by (rule agree_update_intro[OF a'(2) _ v])
    then show ?thesis
      using a' unfolding ext_sat_def by auto
  qed
  moreover have \<open>ext_sat f a d\<close> if \<open>ext_sat f (a[v := b]) (d[v := True])\<close>
    using that agree_update[OF _ k(2)] unfolding ext_sat_def length_list_update by blast
  ultimately show ?thesis
    using ag ms unfolding prop_rel_def v_def b_def by auto
qed

lemma sol_prop_rel:
  assumes \<open>prop_rel f a d a' d'\<close> \<open>sol f a' d' r\<close>
  shows \<open>sol f a d r\<close>
proof (cases r)
  case (Answer_Sat m)
  have m: \<open>length (Assignments_v0 m) = length a'\<close> \<open>agree d' a' (Assignments_v0 m)\<close>
    \<open>formula_sat (Assignments_v0 m) f\<close>
    using assms(2) Answer_Sat by (simp_all add: sol_def)
  have p: \<open>length a' = length a\<close> \<open>more_set d d'\<close> \<open>agree d a a'\<close>
    using assms(1) unfolding prop_rel_def by simp_all
  have \<open>agree d a (Assignments_v0 m)\<close>
    using agree_trans[OF p(3) agree_more_set[OF p(2) m(2)]] .
  then show ?thesis
    using Answer_Sat m p by (simp add: sol_def)
next
  case Answer_Unsat
  then show ?thesis
    using assms unfolding prop_rel_def sol_def by simp
qed

text \<open>Some literal of the clause is assigned its value.\<close>
definition clause_true :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow> bool\<close> where
  \<open>clause_true a d c \<equiv>
     \<exists>j < length (Clause_v0 c). d ! unat (Lit_var (Clause_v0 c ! j)) \<and> lit_sat a (Clause_v0 c ! j)\<close>

text \<open>If every clause has a true literal, the assignment satisfies the formula.\<close>
lemma all_clause_true_formula_sat:
  assumes \<open>\<forall>j < length (Formula_clauses f). clause_true a d (Formula_clauses f ! j)\<close>
  shows \<open>formula_sat a f\<close>
  using assms unfolding formula_sat_iff_nth clause_true_def clause_sat_iff_nth lit_sat_def by blast

text \<open>A clause without a true literal whose literals are all assigned is false.\<close>
lemma no_unset_conflict:
  assumes \<open>j < length (Formula_clauses f)\<close> \<open>\<not> clause_true a d (Formula_clauses f ! j)\<close>
    \<open>\<forall>i < length (Clause_v0 (Formula_clauses f ! j)).
       d ! unat (Lit_var (Clause_v0 (Formula_clauses f ! j) ! i))\<close>
  shows \<open>conflict a d f\<close>
  using assms unfolding conflict_iff_nth clause_false_iff_nth clause_true_def lit_sat_def by blast

lemma clause_true_not_unit:
  assumes \<open>clause_true a d c\<close>
  shows \<open>\<not> unit_at a d c k\<close>
  using assms unfolding clause_true_def unit_at_def by blast

lemma all_set_not_unit:
  assumes \<open>\<forall>j < length (Clause_v0 c). d ! unat (Lit_var (Clause_v0 c ! j))\<close>
  shows \<open>\<not> unit_at a d c k\<close>
  using assms unfolding unit_at_def by blast

lemma two_unset_not_unit:
  assumes \<open>k1 < k2\<close> \<open>k2 < length (Clause_v0 c)\<close>
    \<open>\<not> d ! unat (Lit_var (Clause_v0 c ! k1))\<close> \<open>\<not> d ! unat (Lit_var (Clause_v0 c ! k2))\<close>
  shows \<open>\<not> unit_at a d c k\<close>
proof
  assume u: \<open>unit_at a d c k\<close>
  have \<open>k1 < length (Clause_v0 c)\<close> using assms(1,2) by simp
  then have \<open>k1 = k\<close> using u assms(3) unfolding unit_at_def by blast
  moreover have \<open>k2 = k\<close> using u assms(2,4) unfolding unit_at_def by blast
  ultimately show False using assms(1) by simp
qed

lemma one_unset_unit:
  assumes \<open>\<not> clause_true a d c\<close> \<open>k < length (Clause_v0 c)\<close>
    \<open>\<not> d ! unat (Lit_var (Clause_v0 c ! k))\<close>
    \<open>\<forall>j < k. d ! unat (Lit_var (Clause_v0 c ! j))\<close>
    \<open>\<forall>j. Suc k \<le> j \<and> j < length (Clause_v0 c) \<longrightarrow> d ! unat (Lit_var (Clause_v0 c ! j))\<close>
  shows \<open>unit_at a d c k\<close>
  unfolding unit_at_def
proof (intro conjI allI impI)
  fix j assume j: \<open>j < length (Clause_v0 c)\<close> \<open>j \<noteq> k\<close>
  show d: \<open>d ! unat (Lit_var (Clause_v0 c ! j))\<close>
    using assms(4,5) j by (cases \<open>j < k\<close>) auto
  show \<open>\<not> lit_sat a (Clause_v0 c ! j)\<close>
    using assms(1) j d unfolding clause_true_def by blast
qed (use assms in auto)

text \<open>The number of unassigned variables, which bounds the depth of the recursions.\<close>
definition unset :: \<open>bool list \<Rightarrow> nat\<close> where
  \<open>unset d \<equiv> card {v. v < length d \<and> \<not> d ! v}\<close>

lemma unset_more_set:
  assumes \<open>more_set d d'\<close>
  shows \<open>unset d' \<le> unset d\<close>
  using assms unfolding unset_def more_set_def by (intro card_mono) auto

lemma unset_le_length:
  \<open>unset d \<le> length d\<close>
proof -
  have \<open>card {v. v < length d \<and> \<not> d ! v} \<le> card {..<length d}\<close>
    by (intro card_mono) auto
  then show ?thesis
    unfolding unset_def by simp
qed

lemma unset_update:
  assumes \<open>v < length d\<close> \<open>\<not> d ! v\<close>
  shows \<open>unset (d[v := True]) < unset d\<close>
proof -
  have eq: \<open>{u. u < length (d[v := True]) \<and> \<not> d[v := True] ! u} = {u. u < length d \<and> \<not> d ! u} - {v}\<close>
    using assms(1) by (auto simp add: nth_list_update split: if_splits)
  have lt: \<open>card ({u. u < length d \<and> \<not> d ! u} - {v}) < card {u. u < length d \<and> \<not> d ! u}\<close>
    using assms by (intro card_Diff1_less) auto
  show ?thesis
    unfolding unset_def eq by (rule lt)
qed

lemma unat_word_Suc:
  fixes x :: \<open>64 word\<close>
  assumes \<open>unat x < n\<close> \<open>n < 2^64\<close>
  shows \<open>unat (x + 1) = Suc (unat x)\<close>
proof -
  have \<open>unat x + unat (1 :: 64 word) < 2 ^ LENGTH(64)\<close>
    using assms by simp
  then have \<open>unat (x + 1) = unat x + unat (1 :: 64 word)\<close>
    using unat_add_lem[of x \<open>1 :: 64 word\<close>] by blast
  then show ?thesis
    by simp
qed

lemma unat_word_Suc_simp:
  fixes x :: \<open>64 word\<close>
  assumes \<open>unat x < 18446744073709551615\<close>
  shows \<open>unat (x + 1) = Suc (unat x)\<close>
  using assms unat_word_Suc[of x 18446744073709551615] by simp

lemma word64_eq_of_nat_iff:
  fixes x :: \<open>64 word\<close>
  assumes \<open>n < 2^64\<close>
  shows \<open>x = word_of_nat n \<longleftrightarrow> unat x = n\<close>
  using assms
  by (metis nat_neq_iff unat_less_helper unat_word_of_nat64_less word_of_nat_less word_unat.Rep_inverse)

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

lemma clause_pre_nth:
  assumes \<open>clause_pre c pa\<close> \<open>j < length (Clause_v0 c)\<close>
  shows \<open>unat (Lit_var (Clause_v0 c ! j)) < length (Assignments_v0 (Pasn_assign pa))\<close>
    \<open>unat (Lit_var (Clause_v0 c ! j)) < length (Pasn_set pa)\<close>
  using assms nth_mem unfolding clause_pre_def by blast+

lemma formula_wf_clause_pre:
  assumes \<open>formula_wf f (length (Assignments_v0 (Pasn_assign pa)))\<close>
    \<open>length (Pasn_set pa) = length (Assignments_v0 (Pasn_assign pa))\<close>
    \<open>j < length (Formula_clauses f)\<close>
  shows \<open>clause_pre (Formula_clauses f ! j) pa\<close>
  using assms nth_mem[OF assms(3)] unfolding formula_wf_def clause_pre_def by auto

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

lemma word_ne_length:
  fixes x :: \<open>64 word\<close>
  assumes \<open>x \<noteq> word64_of_nat n\<close> \<open>unat x \<le> n\<close> \<open>n < 2^64\<close>
  shows \<open>unat x < n\<close>
  using assms word64_eq_of_nat_iff[of n x] by simp

text \<open>The facts about one step of unit propagation, at the literal \<open>xa\<close> of the clause \<open>x\<close>.\<close>
lemma propagate_unit_facts:
  assumes wf: \<open>formula_wf f (length a)\<close> and len: \<open>length d = length a\<close>
    and k: \<open>2 * unset d + j < Suc k\<close>
    and uc: \<open>unat x \<le> length (Formula_clauses f)\<close>
    and ne: \<open>x \<noteq> word64_of_nat (length (Formula_clauses f))\<close>
    and ul: \<open>unit_lit_post a d (Formula_clauses f ! unat x) (unat xa)\<close>
    and xa: \<open>unat xa < length (Clause_v0 (Formula_clauses f ! unat x))\<close>
  shows \<open>unat x < length (Formula_clauses f)\<close>
    \<open>unat xa < length (Clause_v0 (Formula_clauses f ! unat x))\<close>
    \<open>unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) < length a\<close>
    \<open>2 * unset (d[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) := True]) + 1 < k\<close>
    \<open>prop_rel f a d
       (a[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) :=
          Lit_value (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)])
       (d[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) := True])\<close>
proof -
  show x: \<open>unat x < length (Formula_clauses f)\<close>
    using wf uc ne word_ne_length[of x \<open>length (Formula_clauses f)\<close>] unfolding formula_wf_def by simp
  define c where \<open>c = Formula_clauses f ! unat x\<close>
  have c: \<open>c \<in> set (Formula_clauses f)\<close>
    using x unfolding c_def by simp
  have u: \<open>unit_at a d c (unat xa)\<close>
    using ul xa unfolding unit_lit_post_def c_def by blast
  show \<open>unat xa < length (Clause_v0 (Formula_clauses f ! unat x))\<close>
    by (rule xa)
  have vb: \<open>vars_below f (length a)\<close>
    using wf by (rule formula_wf_vars_below)
  show v: \<open>unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) < length a\<close>
    using vb c xa nth_mem[OF xa] unfolding vars_below_def c_def by blast
  have nd: \<open>\<not> d ! unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa))\<close>
    using u unfolding unit_at_def c_def by simp
  show \<open>2 * unset (d[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) := True]) + 1 < k\<close>
    using unset_update[OF _ nd] v len k by simp
  show \<open>prop_rel f a d
       (a[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) :=
          Lit_value (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)])
       (d[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) := True])\<close>
    using prop_rel_unit[OF c u vb len] unfolding c_def .
qed

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
    using uc ne lf word_ne_length[of x \<open>length (Formula_clauses f)\<close>] by simp
  have \<open>length (Clause_v0 (Formula_clauses f ! unat x)) < 2^63\<close>
    using wf x nth_mem[OF x] unfolding formula_wf_def by blast
  then have \<open>unat (word64_of_nat (length (Clause_v0 (Formula_clauses f ! unat x)))) =
      length (Clause_v0 (Formula_clauses f ! unat x))\<close>
    by (simp add: unat_of_nat_eq)
  then have xa: \<open>unat xa < length (Clause_v0 (Formula_clauses f ! unat x))\<close>
    using nk by simp
  have j: \<open>2 * unset d + min (Suc 0) (unat s) < Suc k\<close>
    by (rule k)
  note F = propagate_unit_facts[OF wf len j uc ne ul xa]
  show \<open>prop_rel f a d
       (a[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) :=
          Lit_value (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)])
       (d[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) := True])\<close>
    by (rule F(5))
  have \<open>min (Suc 0) (unat (x + 1)) \<le> Suc 0\<close>
    by simp
  then show \<open>2 * unset (d[unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) := True]) +
       min (Suc 0) (unat (x + 1)) < k\<close>
    using F(4) by linarith
  show \<open>unat (x + 1) \<le> length (Formula_clauses f)\<close>
    using unat_word_Suc[OF x lf] x by simp
  show \<open>unat x < 18446744073709551615\<close>
    using x lf by simp
  show \<open>unat (Lit_var (Clause_v0 (Formula_clauses f ! unat x) ! unat xa)) < length a\<close>
    by (rule F(3))
  show \<open>unat xa < length (Clause_v0 (Formula_clauses f ! unat x))\<close>
    by (rule xa)
qed

lemma propagate_idx:
  assumes \<open>formula_wf f n\<close> \<open>unat x \<le> length (Formula_clauses f)\<close>
    \<open>x \<noteq> word64_of_nat (length (Formula_clauses f))\<close>
  shows \<open>unat x < length (Formula_clauses f)\<close>
  using assms word_ne_length[of x \<open>length (Formula_clauses f)\<close>] unfolding formula_wf_def by simp

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
  subgoal premises prems by (rule propagate_idx[OF prems(1,5,6)])
  subgoal premises prems
    by (rule formula_wf_clause_pre[OF prems(1,2) propagate_idx[OF prems(1,5,6)]])
  subgoal premises prems by (rule propagate_idx[OF prems(1,5,6)])
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
  using assms word_ne_length[of xa \<open>length (Formula_clauses f)\<close>]
  unfolding formula_wf_def open_clause_post_def by simp

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
