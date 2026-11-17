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

text \<open>Some assignment that agrees with \<open>a\<close> on its first \<open>i\<close> variables satisfies \<open>f\<close>.\<close>
definition ext_sat :: \<open>Formula \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>ext_sat f a i \<equiv> \<exists>a'. length a' = length a \<and> take i a' = take i a \<and> formula_sat a' f\<close>

lemma ext_sat_complete:
  \<open>ext_sat f a (length a) \<longleftrightarrow> formula_sat a f\<close>
  unfolding ext_sat_def by auto

lemma ext_sat_step:
  assumes \<open>i < length a\<close>
  shows \<open>ext_sat f a i \<longleftrightarrow> ext_sat f (a[i := True]) (Suc i) \<or> ext_sat f (a[i := False]) (Suc i)\<close>
proof
  assume \<open>ext_sat f a i\<close>
  then obtain a' where a': \<open>length a' = length a\<close> \<open>take i a' = take i a\<close> \<open>formula_sat a' f\<close>
    unfolding ext_sat_def by blast
  have \<open>take (Suc i) a' = take (Suc i) (a[i := a' ! i])\<close>
    using a' assms by (simp add: take_Suc_conv_app_nth take_update_cancel)
  then have \<open>ext_sat f (a[i := a' ! i]) (Suc i)\<close>
    using a' unfolding ext_sat_def by auto
  then show \<open>ext_sat f (a[i := True]) (Suc i) \<or> ext_sat f (a[i := False]) (Suc i)\<close>
    by (cases \<open>a' ! i\<close>) simp_all
next
  have \<open>ext_sat f (a[i := b]) (Suc i) \<Longrightarrow> ext_sat f a i\<close> for b
  proof -
    assume \<open>ext_sat f (a[i := b]) (Suc i)\<close>
    then obtain a' where a': \<open>length a' = length a\<close> \<open>take (Suc i) a' = take (Suc i) (a[i := b])\<close>
      \<open>formula_sat a' f\<close>
      unfolding ext_sat_def by auto
    then have \<open>take i a' = take i a\<close>
      by (metis append_eq_conv_conj assms length_list_update length_take min.absorb4 take_hd_drop
          upd_conv_take_nth_drop)
    then show \<open>ext_sat f a i\<close>
      using a' unfolding ext_sat_def by blast
  qed
  then show \<open>ext_sat f (a[i := True]) (Suc i) \<or> ext_sat f (a[i := False]) (Suc i) \<Longrightarrow> ext_sat f a i\<close>
    by blast
qed

lemma ext_sat_start:
  \<open>ext_sat f (replicate n False) 0 \<longleftrightarrow> (\<exists>a. length a = n \<and> formula_sat a f)\<close>
  unfolding ext_sat_def by simp

text \<open>The answer \<open>r\<close> is right for the subproblem in which the first \<open>i\<close> variables have the
  values of \<open>a\<close>: \<^verbatim>\<open>Sat(m)\<close> gives a satisfying assignment \<open>m\<close> of the same length that agrees with
  \<open>a\<close> on them; \<^verbatim>\<open>Unsat\<close> means that there is none.\<close>
definition sol :: \<open>Formula \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> Answer \<Rightarrow> bool\<close> where
  \<open>sol f a i r \<equiv> case r of
     Answer_Sat m \<Rightarrow> length (Assignments_v0 m) = length a \<and> take i (Assignments_v0 m) = take i a \<and>
       formula_sat (Assignments_v0 m) f
   | Answer_Unsat \<Rightarrow> \<not> ext_sat f a i\<close>

lemma sol_leaf:
  \<open>sol f a (length a) (if formula_sat a f then Answer_Sat (make_Assignments a) else Answer_Unsat)\<close>
  by (simp add: sol_def ext_sat_complete)

lemma sol_step:
  assumes \<open>i < length a\<close> \<open>sol f (a[i := True]) (Suc i) r1\<close>
    \<open>case r1 of Answer_Sat m \<Rightarrow> r = Answer_Sat m | Answer_Unsat \<Rightarrow> sol f (a[i := False]) (Suc i) r\<close>
  shows \<open>sol f a i r\<close>
proof -
  have tk: \<open>take i m = take i a\<close> if \<open>take (Suc i) m = take (Suc i) (a[i := b])\<close> for m b
  proof -
    have \<open>take i m = take i (take (Suc i) m)\<close> by simp
    also have \<open>\<dots> = take i (a[i := b])\<close> using that by simp
    also have \<open>\<dots> = take i a\<close> by simp
    finally show ?thesis .
  qed
  show ?thesis
  proof (cases r1)
    case (Answer_Sat m)
    then show ?thesis using assms(2,3) tk by (simp add: sol_def)
  next
    case Answer_Unsat
    then have u: \<open>\<not> ext_sat f (a[i := True]) (Suc i)\<close> and r: \<open>sol f (a[i := False]) (Suc i) r\<close>
      using assms(2,3) by (simp_all add: sol_def)
    show ?thesis
    proof (cases r)
      case (Answer_Sat m)
      then show ?thesis using r tk by (simp add: sol_def)
    next
      case Answer_Unsat
      then show ?thesis using r u ext_sat_step[OF assms(1)] by (simp add: sol_def)
    qed
  qed
qed

lemma sol_start:
  assumes \<open>sol f (replicate n False) 0 r\<close>
  shows \<open>case r of
     Answer_Sat a \<Rightarrow> length (Assignments_v0 a) = n \<and> formula_sat (Assignments_v0 a) f
   | Answer_Unsat \<Rightarrow> (\<forall>a. length a = n \<longrightarrow> \<not> formula_sat a f)\<close>
  using assms by (cases r) (auto simp add: sol_def ext_sat_start)

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

text \<open>The formula's literals refer to variables below \<open>n\<close>; every list fits in a \<^verbatim>\<open>usize\<close> and
  is at most \<^term>\<open>urust_fuel\<close> long, so no bounded loop runs out of fuel.\<close>
definition formula_wf :: \<open>Formula \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>formula_wf f n \<equiv>
     length (Formula_clauses f) \<le> urust_fuel \<and> length (Formula_clauses f) < 2^64 \<and>
     (\<forall>c \<in> set (Formula_clauses f).
        length (Clause_v0 c) \<le> urust_fuel \<and> length (Clause_v0 c) < 2^64 \<and>
        (\<forall>l \<in> set (Clause_v0 c). unat (Lit_var l) < n))\<close>

definition Clause_eval_contract :: \<open>Clause \<Rightarrow> Assignments \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>Clause_eval_contract c a \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>(\<forall>l \<in> set (Clause_v0 c). unat (Lit_var l) < length (Assignments_v0 a)) \<and>
         length (Clause_v0 c) \<le> urust_fuel \<and> length (Clause_v0 c) < 2^64\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = clause_sat (Assignments_v0 a) c\<rangle> in
     make_function_contract pre post\<close>

lemma Clause_eval_spec:
  shows \<open>\<Gamma>; Clause_eval c a \<Turnstile>\<^sub>F Clause_eval_contract c a\<close>
  apply (crush_boot f: Clause_eval_def contract: Clause_eval_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length (Clause_v0 c) \<and>
                (\<forall>j < unat i. \<not> lit_sat (Assignments_v0 a) (Clause_v0 c ! j)) \<and>
                length (Clause_v0 c) - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length (Clause_v0 c) \<and>
                (\<forall>j < unat i. \<not> lit_sat (Assignments_v0 a) (Clause_v0 c ! j)) \<and>
                length (Clause_v0 c) - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = clause_sat (Assignments_v0 a) c\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: true_def false_def lit_sat_def clause_sat_iff_nth word_less_nat_alt unat_of_nat_eq
        unat_word_Suc_simp)
    apply (auto simp add: less_Suc_eq clause_sat_iff_nth)
    done
  done

definition Formula_eval_contract :: \<open>Formula \<Rightarrow> Assignments \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>Formula_eval_contract f a \<equiv>
     let pre = can_alloc_reference \<star> \<langle>formula_wf f (length (Assignments_v0 a))\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = formula_sat (Assignments_v0 a) f\<rangle> in
     make_function_contract pre post\<close>

lemma Formula_eval_spec:
  shows \<open>\<Gamma>; Formula_eval f a \<Turnstile>\<^sub>F Formula_eval_contract f a\<close>
  apply (crush_boot f: Formula_eval_def contract: Formula_eval_contract_def)
  apply (crush_base inline: len_def simp add: true_def false_def)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i \<le> length (Formula_clauses f) \<and>
                (\<forall>j < unat i. clause_sat (Assignments_v0 a) (Formula_clauses f ! j)) \<and>
                length (Formula_clauses f) - unat i \<le> k\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>g i. i_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i \<star> can_alloc_reference \<star>
               \<langle>unat i < length (Formula_clauses f) \<and>
                (\<forall>j < unat i. clause_sat (Assignments_v0 a) (Formula_clauses f ! j)) \<and>
                length (Formula_clauses f) - unat i \<le> Suc k\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = formula_sat (Assignments_v0 a) f\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: len_def specs add: Clause_eval_spec contracts add: Clause_eval_contract_def
        simp add: true_def false_def formula_sat_iff_nth formula_wf_def word_less_nat_alt unat_of_nat_eq unat_word_Suc_simp)
    apply (auto simp add: less_Suc_eq formula_sat_iff_nth)
    done
  done

definition set_next_contract :: \<open>Pasn \<Rightarrow> bool \<Rightarrow> ('s, Pasn, 'abort) function_contract\<close> where
  \<open>set_next_contract pa b \<equiv>
     let a = Assignments_v0 (Pasn_assign pa) in
     let pre = can_alloc_reference \<star> \<langle>unat (Pasn_ix pa) < length a \<and> length a < 2^64\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>r = make_Pasn (make_Assignments (a[unat (Pasn_ix pa) := b])) (Pasn_ix pa + 1)\<rangle> in
     make_function_contract pre post\<close>

lemma set_next_spec:
  shows \<open>\<Gamma>; set_next pa b \<Turnstile>\<^sub>F set_next_contract pa b\<close>
  apply (crush_boot f: set_next_def contract: set_next_contract_def)
  apply (crush_base inline: Pasn_mk_def Assignments_mk_def simp add: true_def false_def focus_components)
  done

text \<open>The \<open>k\<close>-th unfolding of \<^const>\<open>solve\<close>. Its precondition requires fewer than \<open>k\<close>
  variables to remain unassigned, so the innermost function is never called.\<close>
definition solve_contract :: \<open>nat \<Rightarrow> Formula \<Rightarrow> Pasn \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  \<open>solve_contract k f pa \<equiv>
     let a = Assignments_v0 (Pasn_assign pa) in
     let pre = can_alloc_reference \<star>
        \<langle>formula_wf f (length a) \<and> unat (Pasn_ix pa) \<le> length a \<and> length a < 2^64 \<and>
         length a - unat (Pasn_ix pa) < k\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>sol f a (unat (Pasn_ix pa)) r\<rangle> in
     make_function_contract pre post\<close>

lemma solve_rec_step_spec:
  assumes \<open>\<And>pa. \<Gamma>; R f pa \<Turnstile>\<^sub>F solve_contract k f pa\<close>
  shows \<open>\<Gamma>; solve_rec_step R f pa \<Turnstile>\<^sub>F solve_contract (Suc k) f pa\<close>
  apply (crush_boot f: solve_rec_step_def contract: solve_contract_def)
  apply (crush_base inline: len_def specs add: assms Formula_eval_spec set_next_spec
      contracts add: solve_contract_def Formula_eval_contract_def set_next_contract_def
      simp add: true_def false_def word_less_nat_alt unat_of_nat_eq unat_word_Suc_simp word64_eq_of_nat_iff)
  subgoal for x
    apply (cases x)
     apply (crush_base inline: Answer_Sat_mk_def)
     apply (crush_base specs add: assms set_next_spec contracts add: solve_contract_def set_next_contract_def
        simp add: word_less_nat_alt unat_of_nat_eq unat_word_Suc_simp)
    subgoal for m
      using sol_step[of \<open>unat (Pasn_ix pa)\<close> \<open>Assignments_v0 (Pasn_assign pa)\<close> f
          \<open>Answer_Sat m\<close> \<open>Answer_Sat m\<close>]
      by (simp add: le_neq_implies_less)
    subgoal for r
      using sol_step[of \<open>unat (Pasn_ix pa)\<close> \<open>Assignments_v0 (Pasn_assign pa)\<close> f Answer_Unsat r]
      by (simp add: le_neq_implies_less)
    done
  subgoal by (simp add: sol_def ext_sat_complete)
  subgoal by (simp add: sol_def ext_sat_complete)
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
