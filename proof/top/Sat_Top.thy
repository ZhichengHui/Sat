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
     Suc (2 * unat (Formula_num_vars f)) + length (Formula_clauses f) +
     sum_list (List.map (\<lambda>c. length (Clause_v0 c)) (Formula_clauses f))\<close>

lemma fuel_top_clause:
  assumes \<open>c \<in> set (Formula_clauses f)\<close>
  shows \<open>length (Clause_v0 c) \<le> fuel_top f\<close>
proof -
  have \<open>length (Clause_v0 c) \<le> sum_list (List.map (\<lambda>c. length (Clause_v0 c)) (Formula_clauses f))\<close>
    using assms by (simp add: member_le_sum_list)
  then show ?thesis by (simp add: fuel_top_def)
qed

context Sat_ctx
begin

text \<open>With enough fuel the solver satisfies the contract of the specification. The answer of
  \<open>cdcl_spec\<close> (\<^verbatim>\<open>Sat_CDCL\<close>) is the contract's when it is one; otherwise the proof reuses
  \<open>solve_spec\<close> of \<^verbatim>\<open>Sat_Proof\<close> and turns its answer into the contract's with \<open>sol_start\<close>;
  the fuel bound \<^const>\<open>fuel_top\<close> and \<^const>\<open>sat_repr_ok\<close> give the size conditions of
  \<open>formula_wf\<close>.\<close>
lemma solver_spec:
  assumes \<open>fuel_top f \<le> urust_fuel\<close>
  shows \<open>\<Gamma>; solver f \<Turnstile>\<^sub>F solver_contract f\<close>
  apply (crush_boot f: solver_def contract: solver_contract_def)
  apply (crush_base specs add: cdcl_spec contracts add: cdcl_contract_def simp add: true_def false_def)
  subgoal premises prems for x
  proof (cases x)
    case None
    have inv: \<open>formula_invariant f\<close> and repr: \<open>sat_repr_ok f\<close>
      using prems by auto
    show ?thesis
      unfolding None
      apply (simp only: option.case)
      apply (crush_base inline: vec_from_elem_def Pasn_mk_def Assignments_mk_def
          specs add: solve_spec contracts add: solve_contract_def
          simp add: true_def false_def unat_lt2p formula_wf_def)
      subgoal \<comment> \<open>the answer of \<^verbatim>\<open>solve\<close> from the empty assignment\<close>
        by (erule sol_start)
      subgoal \<comment> \<open>the fuel of the recursion of \<^verbatim>\<open>solve\<close>\<close>
        using assms unset_le_length[of \<open>replicate (unat (Formula_num_vars f)) False\<close>]
        by (simp add: fuel_top_def)
      subgoal \<comment> \<open>the fuel of the recursion of \<^verbatim>\<open>propagate\<close>\<close>
        using assms by (simp add: fuel_top_def)
      subgoal \<comment> \<open>\<open>formula_wf\<close>: every variable is below the number of variables\<close>
        using inv unfolding formula_invariant_def by blast
      subgoal \<comment> \<open>\<open>formula_wf\<close>: every clause is shorter than \<open>2^63\<close>\<close>
        using repr by (auto simp add: sat_repr_ok_def)
      subgoal \<comment> \<open>the fuel of the loops over a clause's literals\<close>
        by (rule order_trans[OF fuel_top_clause assms])
      subgoal \<comment> \<open>the number of clauses fits in a word\<close>
        using repr by (simp add: sat_repr_ok_def)
      subgoal \<comment> \<open>the fuel of the loops over the clauses\<close>
        using assms by (simp add: fuel_top_def)
      done
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
     new_gref_can_store can_alloc_reference prism_1 prism_2 prism_3 prism_4 prism_5\<close>
  by intro_locales

theorem solver_correct:
  shows \<open>solver_correct \<Gamma>\<close>
proof (unfold solver_correct_def, intro allI impI)
  fix f :: Formula
  assume \<open>formula_invariant f \<and> sat_repr_ok f\<close>
  have \<open>\<Gamma>; solver fuel f \<Turnstile>\<^sub>F solver_contract f\<close> if \<open>fuel_top f \<le> fuel\<close> for fuel
    by (rule Sat_ctx.solver_spec[OF Sat_ctxI that])
  then show \<open>\<exists>N. \<forall>fuel \<ge> N. \<Gamma>; solver fuel f \<Turnstile>\<^sub>F solver_contract f\<close>
    by (intro exI[of _ \<open>fuel_top f\<close>]) simp
qed

end

end
