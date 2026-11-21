theory Sat_Top
  imports Sat_Proof.Sat_Proof Sat_Proof.Sat_CDCL
begin

section \<open>The top-level theorem\<close>

text \<open>The fuel that suffices for a formula: more than twice the number of variables (bounding the
  depth of the recursions of \<^verbatim>\<open>solve\<close> and \<^verbatim>\<open>propagate\<close>), and at least the number of clauses and the
  length of every clause (the iterations of the loops over the clauses and over a clause's
  literals).\<close>
definition fuel_top :: \<open>Formula \<Rightarrow> nat\<close> where
  \<open>fuel_top f \<equiv>
     Suc (2 * unat (Formula_num_vars f)) + length (cls f) +
     sum_list (List.map (\<lambda>c. length (lits c)) (cls f))\<close>

lemma fuel_top_clause:
  assumes \<open>c \<in> set (cls f)\<close>
  shows \<open>length (lits c) \<le> fuel_top f\<close>
proof -
  have \<open>length (lits c) \<le> sum_list (List.map (\<lambda>c. length (lits c)) (cls f))\<close>
    using assms by (simp add: member_le_sum_list)
  then show ?thesis by (simp add: fuel_top_def)
qed

text \<open>The answer of \<^verbatim>\<open>solve\<close> from the assignment of \<^verbatim>\<open>vec![false; n]\<close>.\<close>
lemma sol_start_rvec:
  assumes \<open>rvec_from_elem_val l False n = Some x\<close> \<open>sol f (rvec_elems x) (rvec_elems x) r\<close>
  shows \<open>case r of
     Answer_Sat a \<Rightarrow> length (asg a) = n \<and> formula_sat (asg a) f
   | Answer_Unsat \<Rightarrow> (\<forall>a. length a = n \<longrightarrow> \<not> formula_sat a f)\<close>
  using sol_start[of f n r] assms(2) rvec_from_elem_val_Some(2)[OF assms(1)] by simp

context Sat_ctx
begin

text \<open>With enough fuel \<^verbatim>\<open>dpll\<close>, the fallback of the solver, satisfies the contract of the
  specification: the proof reuses \<open>solve_spec\<close> of \<^verbatim>\<open>Sat_Proof\<close> and turns its answer into the
  contract's with \<open>sol_start\<close>; the fuel bound \<^const>\<open>fuel_top\<close> and \<^const>\<open>sat_repr_ok\<close> give the
  size conditions of \<open>formula_wf\<close>.\<close>
lemma dpll_spec:
  assumes \<open>fuel_top f \<le> urust_fuel\<close>
  shows \<open>\<Gamma>; dpll f \<Turnstile>\<^sub>F solver_contract f\<close>
  apply (crush_boot f: dpll_def contract: solver_contract_def)
  apply (crush_base inline: Pasn_mk_def Assignments_mk_def
      specs add: solve_spec contracts add: solve_contract_def
      simp add: true_def false_def unat_lt2p formula_wf_def)
  subgoal \<comment> \<open>the answer of \<^verbatim>\<open>solve\<close> from the empty assignment\<close>
    by (erule (1) sol_start_rvec)
  subgoal \<comment> \<open>the fuel of the recursion of \<^verbatim>\<open>solve\<close>\<close>
    using assms unset_le_length[of \<open>replicate (unat (Formula_num_vars f)) False\<close>]
    by (drule_tac rvec_from_elem_val_Some(2)) (simp add: fuel_top_def)
  subgoal \<comment> \<open>the fuel of the recursion of \<^verbatim>\<open>propagate\<close>\<close>
    using assms by (drule_tac rvec_from_elem_val_Some(2)) (simp add: fuel_top_def)
  subgoal \<comment> \<open>\<open>formula_wf\<close>: every variable is below the number of variables\<close>
    by (drule rvec_from_elem_val_Some(2)) (auto simp add: formula_invariant_def)
  subgoal \<comment> \<open>\<open>formula_wf\<close>: every clause is shorter than \<open>2^63\<close>\<close>
    by (auto simp add: sat_repr_ok_def)
  subgoal \<comment> \<open>the fuel of the loops over a clause's literals\<close>
    by (rule order_trans[OF fuel_top_clause assms])
  subgoal \<comment> \<open>the number of clauses fits in a word\<close>
    by (simp add: sat_repr_ok_def)
  subgoal \<comment> \<open>the fuel of the loops over the clauses\<close>
    using assms by (simp add: fuel_top_def)
  subgoal \<comment> \<open>\<^verbatim>\<open>vec![false; num_vars]\<close> fits a \<^verbatim>\<open>Vec<bool>\<close>\<close>
    by (simp add: sat_sizes_ok_def cap_max_bool)
  subgoal
    by (simp add: sat_sizes_ok_def cap_max_bool)
  done

text \<open>With enough fuel the solver satisfies the contract of the specification: the answer of
  \<open>cdcl_spec\<close> (\<^verbatim>\<open>Sat_CDCL\<close>) when it is one, otherwise that of \<open>dpll_spec\<close>.\<close>
lemma solver_spec:
  assumes \<open>fuel_top f \<le> urust_fuel\<close>
  shows \<open>\<Gamma>; solver f \<Turnstile>\<^sub>F solver_contract f\<close>
  apply (crush_boot f: solver_def contract: solver_contract_def)
  apply (crush_base specs add: cdcl_spec contracts add: cdcl_contract_def simp add: true_def false_def)
  subgoal premises prems for x
  proof (cases x)
    case None
    show ?thesis
      unfolding None
      apply (simp only: option.case)
      apply (crush_base specs add: dpll_spec[OF assms] contracts add: solver_contract_def)
      using prems by auto
  next
    case (Some a)
    have \<open>cdcl_post f (Some a)\<close>
      using prems Some by simp
    then show ?thesis
      unfolding Some
      apply (simp only: option.case)
      apply crush_base
      apply (auto simp: cdcl_post_def split: Answer.splits)
      done
  qed
  done

end

context Sat_heap
begin

text \<open>\<^verbatim>\<open>Sat_heap\<close> has the assumptions of \<^locale>\<open>Sat_ctx\<close>, so its parameters with any fuel
  form an instance of \<^locale>\<open>Sat_ctx\<close>, and the contract lemmas of \<^locale>\<open>Sat_ctx\<close> apply.\<close>
lemma Sat_ctxI:
  \<open>Sat_ctx update_raw_fun dereference_raw_fun reference_raw_fun points_to_raw' gref_can_store
     new_gref_can_store can_alloc_reference prism_1 prism_2 prism_3 prism_4 prism_5 prism_6\<close>
  by intro_locales

theorem solver_correct:
  shows \<open>solver_correct \<Gamma>\<close>
proof (unfold solver_correct_def, intro allI impI)
  fix f :: Formula
  assume \<open>formula_invariant f \<and> sat_repr_ok f \<and> sat_sizes_ok f\<close>
  have \<open>\<Gamma>; solver fuel f \<Turnstile>\<^sub>F solver_contract f\<close> if \<open>fuel_top f \<le> fuel\<close> for fuel
    by (rule Sat_ctx.solver_spec[OF Sat_ctxI that])
  then show \<open>\<exists>N. \<forall>fuel \<ge> N. \<Gamma>; solver fuel f \<Turnstile>\<^sub>F solver_contract f\<close>
    by (intro exI[of _ \<open>fuel_top f\<close>]) simp
qed

end

end
