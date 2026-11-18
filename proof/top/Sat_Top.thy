theory Sat_Top
  imports Sat_Proof.Sat_Proof
begin

section \<open>The top-level theorem\<close>

text \<open>The fuel that suffices for a formula: more than the number of variables (the depth of the
  recursion of \<^verbatim>\<open>solve\<close>), and at least the number of clauses and the length of every clause
  (the iterations of the loops of \<^verbatim>\<open>Formula::conflict\<close> and \<^verbatim>\<open>Clause::falsified\<close>).\<close>
definition fuel_top :: \<open>Formula \<Rightarrow> nat\<close> where
  \<open>fuel_top f \<equiv>
     Suc (unat (Formula_num_vars f)) + length (Formula_clauses f) +
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

text \<open>With enough fuel the solver satisfies the contract of the specification. The proof reuses
  \<open>solve_spec\<close> of \<^verbatim>\<open>Sat_Proof\<close> and turns its answer into the contract's with
  \<open>sol_start\<close>; the fuel bound \<^const>\<open>fuel_top\<close> and \<^const>\<open>sat_repr_ok\<close>
  give the size conditions of \<open>formula_wf\<close>.\<close>
lemma solver_spec:
  assumes \<open>fuel_top f \<le> urust_fuel\<close>
  shows \<open>\<Gamma>; solver f \<Turnstile>\<^sub>F solver_contract f\<close>
  apply (crush_boot f: solver_def contract: solver_contract_def)
  apply (crush_base inline: vec_from_elem_def Pasn_mk_def Assignments_mk_def
      specs add: solve_spec contracts add: solve_contract_def
      simp add: true_def false_def unat_lt2p formula_wf_def)
  using assms fuel_top_clause[of _ f] unat_lt2p[of \<open>Formula_num_vars f\<close>] sol_start
  by (fastforce simp: fuel_top_def sat_repr_ok_def formula_invariant_def)+

end

context Sat_heap
begin

text \<open>\<^verbatim>\<open>Sat_heap\<close> has the assumptions of \<^locale>\<open>Sat_ctx\<close>, so its parameters with any fuel
  form an instance of \<^locale>\<open>Sat_ctx\<close>, and the contract lemmas of \<^locale>\<open>Sat_ctx\<close> apply.\<close>
lemma Sat_ctxI:
  \<open>Sat_ctx update_raw_fun dereference_raw_fun reference_raw_fun points_to_raw' gref_can_store
     new_gref_can_store can_alloc_reference prism_1 prism_2\<close>
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
