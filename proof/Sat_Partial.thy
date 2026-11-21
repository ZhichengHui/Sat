theory Sat_Partial
  imports Sat_Spec.Sat_Spec
begin

text \<open>The facts that do not depend on the code of \<^verbatim>\<open>core/src/lib.rs\<close>: partial assignments and
  their extensions (\<open>agree\<close>, \<open>ext_sat\<close>, \<open>sol\<close>), false, true and unit clauses, the relation
  \<open>prop_rel\<close> between the input and the output of unit propagation, the measure \<open>unset\<close>, and
  64-bit index arithmetic. \<^verbatim>\<open>Sat_Proof\<close> proves the contracts of the code with them; a solver
  with another search (CDCL) can reuse them unchanged.\<close>

section \<open>The selector-update equations of the records\<close>

text \<open>The simproc of \<^verbatim>\<open>scalable_datatype_record\<close> proves \<open>g (update_f h r) = g r\<close> when first
  needed and keeps it in a cache shared by every theory, certified by the theory of the proof that
  needed it first. With parallel proofs, that may be a theory the later users do not extend (a
  proof of \<^verbatim>\<open>Sat_Proof\<close> while \<^verbatim>\<open>Sat_Certify\<close> and \<^verbatim>\<open>Sat_Search\<close> run beside it), and then a
  user fails with ``Cannot transfer: not a super theory''. Proving every such equation here, at
  the root of the proofs and before any proof is forked, certifies the cache by a theory that
  every later one extends.\<close>
ML \<open>
  let
    val ctxt = \<^context>
    fun warm T =
      let
        val {selss = [sels], ...} = the (Ctr_Sugar.ctr_sugar_of ctxt (Proof_Context.read_type_name
          {proper = true, strict = true} ctxt T |> dest_Type_name))
        val upds = map (fn s => Syntax.read_term ctxt ("update_" ^ Long_Name.base_name (dest_Const_name s))) sels
        fun eq (sel, upd) =
          let
            val t = Syntax.check_term ctxt (map_types (K dummyT) sel $
              (map_types (K dummyT) upd $ Free ("h", dummyT) $ Free ("r", dummyT)))
            val (sel', upd_h_r) = dest_comb t
            val rhs = Thm.rhs_of (Simplifier.rewrite ctxt (Thm.cterm_of ctxt t))
          in
            if Thm.term_of rhs aconv sel' $ snd (dest_comb upd_h_r) then ()
            else error ("record warm-up: " ^ Syntax.string_of_term ctxt t)
          end
      in
        List.app (fn (i, u) => List.app (fn (j, s) => if i = j then () else eq (s, u))
          (map_index I sels)) (map_index I upds)
      end
  in List.app warm ["Lit", "Pasn", "Formula", "Cut", "Search"] end
\<close>

section \<open>The elements of the vectors\<close>

text \<open>The translation models a \<^verbatim>\<open>Vec\<close> as an \<^typ>\<open>'a rvec\<close>; the proofs reason about
  its elements.\<close>
abbreviation cls :: \<open>Formula \<Rightarrow> Clause list\<close> where
  \<open>cls f \<equiv> rvec_elems (Formula_clauses f)\<close>

abbreviation lits :: \<open>Clause \<Rightarrow> Lit list\<close> where
  \<open>lits c \<equiv> rvec_elems (Clause_v0 c)\<close>

abbreviation asg :: \<open>Assignments \<Rightarrow> bool list\<close> where
  \<open>asg a \<equiv> rvec_elems (Assignments_v0 a)\<close>

section \<open>Satisfaction by index\<close>


lemma clause_sat_iff_nth:
  \<open>clause_sat a c \<longleftrightarrow>
     (\<exists>j < length (lits c). a ! unat (Lit_var (lits c ! j)) = Lit_value (lits c ! j))\<close>
  unfolding clause_sat_def lit_sat_def Bex_def in_set_conv_nth by blast

lemma formula_sat_iff_nth:
  \<open>formula_sat a f \<longleftrightarrow> (\<forall>j < length (cls f). clause_sat a (cls f ! j))\<close>
  unfolding formula_sat_def by (simp add: all_set_conv_all_nth)

section \<open>Partial assignments and their extensions\<close>

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
  using assms unfolding agree_def by (metis nth_list_update_neq)

lemma agree_update:
  assumes \<open>agree (d[v := True]) (a[v := b]) m\<close> \<open>\<not> d ! v\<close>
  shows \<open>agree d a m\<close>
  using assms unfolding agree_def by (metis length_list_update nth_list_update_neq)

lemma agree_update_intro:
  assumes \<open>agree d a m\<close> \<open>m ! v = b\<close> \<open>v < length a\<close>
  shows \<open>agree (d[v := True]) (a[v := b]) m\<close>
  using assms unfolding agree_def by (simp add: nth_list_update)

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
     Answer_Sat m \<Rightarrow> length (asg m) = length a \<and> agree d a (asg m) \<and>
       formula_sat (asg m) f
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
     Answer_Sat a \<Rightarrow> length (asg a) = n \<and> formula_sat (asg a) f
   | Answer_Unsat \<Rightarrow> (\<forall>a. length a = n \<longrightarrow> \<not> formula_sat a f)\<close>
  using assms by (cases r) (auto simp add: sol_def ext_sat_start)

section \<open>False, true and unit clauses\<close>

text \<open>The clause is false under the partial assignment: every literal's variable is assigned and
  has the other value.\<close>
definition clause_false :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow> bool\<close> where
  \<open>clause_false a d c \<equiv> \<forall>l \<in> set (lits c). d ! unat (Lit_var l) \<and> \<not> lit_sat a l\<close>

text \<open>Some clause of the formula is false under that partial assignment.\<close>
definition conflict :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Formula \<Rightarrow> bool\<close> where
  \<open>conflict a d f \<equiv> \<exists>c \<in> set (cls f). clause_false a d c\<close>

lemma clause_false_iff_nth:
  \<open>clause_false a d c \<longleftrightarrow>
     (\<forall>j < length (lits c). d ! unat (Lit_var (lits c ! j)) \<and>
        a ! unat (Lit_var (lits c ! j)) \<noteq> Lit_value (lits c ! j))\<close>
  unfolding clause_false_def lit_sat_def by (simp add: all_set_conv_all_nth)

lemma conflict_iff_nth:
  \<open>conflict a d f \<longleftrightarrow> (\<exists>j < length (cls f). clause_false a d (cls f ! j))\<close>
  unfolding conflict_def by (simp add: Bex_def in_set_conv_nth) blast

text \<open>Every literal's variable of the formula is below \<open>n\<close>.\<close>
definition vars_below :: \<open>Formula \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>vars_below f n \<equiv> \<forall>c \<in> set (cls f). \<forall>l \<in> set (lits c). unat (Lit_var l) < n\<close>

text \<open>A conflict of the partial assignment excludes all its extensions.\<close>
lemma conflict_not_ext_sat:
  assumes \<open>conflict a d f\<close> \<open>vars_below f (length d)\<close>
  shows \<open>\<not> ext_sat f a d\<close>
proof
  assume \<open>ext_sat f a d\<close>
  then obtain a' where a': \<open>agree d a a'\<close> \<open>formula_sat a' f\<close>
    unfolding ext_sat_def by blast
  obtain c where c: \<open>c \<in> set (cls f)\<close> \<open>clause_false a d c\<close>
    using assms unfolding conflict_def by blast
  have \<open>\<not> clause_sat a' c\<close>
    using c assms(2) a'(1)
    unfolding clause_false_def clause_sat_def lit_sat_def agree_def vars_below_def by fastforce
  then show False
    using a'(2) c(1) unfolding formula_sat_def by blast
qed

text \<open>Some literal of the clause is assigned its value.\<close>
definition clause_true :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow> bool\<close> where
  \<open>clause_true a d c \<equiv>
     \<exists>j < length (lits c). d ! unat (Lit_var (lits c ! j)) \<and> lit_sat a (lits c ! j)\<close>

text \<open>If every clause has a true literal, the assignment satisfies the formula.\<close>
lemma all_clause_true_formula_sat:
  assumes \<open>\<forall>j < length (cls f). clause_true a d (cls f ! j)\<close>
  shows \<open>formula_sat a f\<close>
  using assms unfolding formula_sat_iff_nth clause_true_def clause_sat_iff_nth lit_sat_def by blast

text \<open>A clause without a true literal whose literals are all assigned is false.\<close>
lemma no_unset_conflict:
  assumes \<open>j < length (cls f)\<close> \<open>\<not> clause_true a d (cls f ! j)\<close>
    \<open>\<forall>i < length (lits (cls f ! j)).
       d ! unat (Lit_var (lits (cls f ! j) ! i))\<close>
  shows \<open>conflict a d f\<close>
  using assms unfolding conflict_iff_nth clause_false_iff_nth clause_true_def lit_sat_def by blast

text \<open>The clause is unit under the partial assignment, with \<open>k\<close> the index of its only
  unassigned literal: every other literal is assigned and false.\<close>
definition unit_at :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>unit_at a d c k \<equiv> k < length (lits c) \<and> \<not> d ! unat (Lit_var (lits c ! k)) \<and>
     (\<forall>j < length (lits c). j \<noteq> k \<longrightarrow>
        d ! unat (Lit_var (lits c ! j)) \<and> \<not> lit_sat a (lits c ! j))\<close>

lemma clause_true_not_unit:
  assumes \<open>clause_true a d c\<close>
  shows \<open>\<not> unit_at a d c k\<close>
  using assms unfolding clause_true_def unit_at_def by blast

lemma all_set_not_unit:
  assumes \<open>\<forall>j < length (lits c). d ! unat (Lit_var (lits c ! j))\<close>
  shows \<open>\<not> unit_at a d c k\<close>
  using assms unfolding unit_at_def by blast

lemma two_unset_not_unit:
  assumes \<open>k1 < k2\<close> \<open>k2 < length (lits c)\<close>
    \<open>\<not> d ! unat (Lit_var (lits c ! k1))\<close> \<open>\<not> d ! unat (Lit_var (lits c ! k2))\<close>
  shows \<open>\<not> unit_at a d c k\<close>
proof
  assume u: \<open>unit_at a d c k\<close>
  have \<open>k1 < length (lits c)\<close> using assms(1,2) by simp
  then have \<open>k1 = k\<close> using u assms(3) unfolding unit_at_def by blast
  moreover have \<open>k2 = k\<close> using u assms(2,4) unfolding unit_at_def by blast
  ultimately show False using assms(1) by simp
qed

text \<open>The clause is neither false nor unit under the partial assignment: unit propagation has
  nothing to do with it.\<close>
definition settled :: \<open>bool list \<Rightarrow> bool list \<Rightarrow> Clause \<Rightarrow> bool\<close> where
  \<open>settled a d c \<equiv> \<not> clause_false a d c \<and> (\<forall>k. \<not> unit_at a d c k)\<close>

text \<open>If every clause is settled, there is no conflict.\<close>
lemma settled_no_conflict:
  assumes \<open>\<forall>j < length (cls f). settled a d (cls f ! j)\<close>
  shows \<open>\<not> conflict a d f\<close>
  using assms unfolding conflict_iff_nth settled_def by blast

section \<open>Unit propagation\<close>

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
  assumes \<open>c \<in> set (cls f)\<close> \<open>unit_at a d c k\<close> \<open>vars_below f (length a)\<close>
    \<open>length d = length a\<close>
  shows \<open>prop_rel f a d (a[unat (Lit_var (lits c ! k)) := Lit_value (lits c ! k)])
    (d[unat (Lit_var (lits c ! k)) := True])\<close>
proof -
  define v where \<open>v = unat (Lit_var (lits c ! k))\<close>
  define b where \<open>b = Lit_value (lits c ! k)\<close>
  have k: \<open>k < length (lits c)\<close> \<open>\<not> d ! v\<close>
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
    then obtain j where j: \<open>j < length (lits c)\<close> \<open>lit_sat a' (lits c ! j)\<close>
      using clause_sat_iff_nth[of a' c] unfolding lit_sat_def by blast
    have \<open>j = k\<close>
    proof (rule ccontr)
      assume \<open>j \<noteq> k\<close>
      then have \<open>d ! unat (Lit_var (lits c ! j))\<close> \<open>\<not> lit_sat a (lits c ! j)\<close>
        using assms(2) j(1) unfolding unit_at_def by auto
      moreover have \<open>unat (Lit_var (lits c ! j)) < length d\<close>
        using assms(1,3,4) j(1) nth_mem[of j \<open>lits c\<close>] unfolding vars_below_def by auto
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
  have m: \<open>length (asg m) = length a'\<close> \<open>agree d' a' (asg m)\<close>
    \<open>formula_sat (asg m) f\<close>
    using assms(2) Answer_Sat by (simp_all add: sol_def)
  have p: \<open>length a' = length a\<close> \<open>more_set d d'\<close> \<open>agree d a a'\<close>
    using assms(1) unfolding prop_rel_def by simp_all
  have \<open>agree d a (asg m)\<close>
    using agree_trans[OF p(3) agree_more_set[OF p(2) m(2)]] .
  then show ?thesis
    using Answer_Sat m p by (simp add: sol_def)
next
  case Answer_Unsat
  then show ?thesis
    using assms unfolding prop_rel_def sol_def by simp
qed

section \<open>The number of unassigned variables\<close>

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

section \<open>64-bit indices\<close>

lemma unat_word_Suc_simp:
  fixes x :: \<open>64 word\<close>
  assumes \<open>unat x < 18446744073709551615\<close>
  shows \<open>unat (x + 1) = Suc (unat x)\<close>
  using assms unat_add_lem[of x 1] by simp

lemma word64_eq_of_nat_iff:
  fixes x :: \<open>64 word\<close>
  assumes \<open>n < 2^64\<close>
  shows \<open>x = word_of_nat n \<longleftrightarrow> unat x = n\<close>
proof
  show \<open>unat x = n\<close> if \<open>x = word_of_nat n\<close>
    using that assms by (simp add: unat_of_nat_eq)
  show \<open>x = word_of_nat n\<close> if \<open>unat x = n\<close>
    using that by (metis word_unat.Rep_inverse)
qed

end
