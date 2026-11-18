theory Sat_Spec
  imports Formula_Types
begin

section \<open>The top-level specification\<close>

text \<open>
  This theory, with \<^verbatim>\<open>Formula_Types\<close> that it builds on, is the whole specification of the solver:
  the meaning of the top-level theorem depends on nothing outside \<^verbatim>\<open>spec/\<close>. The proofs
  (\<^verbatim>\<open>proof/\<close>) and the solver may change; this directory changes only when the specification
  does.

  The Rust entry point is \<^verbatim>\<open>pub fn solver(f: &Formula) -> Answer\<close> (\<^verbatim>\<open>core/src/lib.rs\<close>),
  translated to \<^verbatim>\<open>Sat_ctx.solver\<close>, where \<^verbatim>\<open>enum Answer { Sat(Assignments), Unsat }\<close>. The
  solver is based on Friday of CreuSAT (\<^url>\<open>https://github.com/sarsko/CreuSAT\<close>), whose
  Creusot contract is
  \<^verbatim>\<open>
  #[requires(f.invariant())]
  #[ensures(!result ==> forall<a: Assignments> a@.len() == f.num_vars() ==> !f.sat(a))]
  #[ensures( result ==> exists<a: Assignments> f.sat(a))]
  pub fn solver(f: &Formula) -> bool
  \<close>
  Friday answers only a Boolean; the SAT competition requires a satisfying assignment with every
  satisfiable answer. This solver returns it, and its contract strengthens Friday's: the answer
  \<^verbatim>\<open>Sat(a)\<close> carries an assignment \<open>a\<close> of all the formula's variables that satisfies the
  formula (instead of only stating that one exists), and \<^verbatim>\<open>Unsat\<close> keeps Friday's meaning.
  The statement \<open>solver_correct\<close> at the end of this theory: for every formula that satisfies the
  precondition there is a bound \<open>N\<close> such that, with any fuel at least \<open>N\<close>, \<^verbatim>\<open>solver\<close>
  satisfies its contract. The solver answers \<^verbatim>\<open>Sat\<close> or \<^verbatim>\<open>Unsat\<close> for every formula: it has no
  answer \<^verbatim>\<open>Unknown\<close>, so there is no input range.

  Trusted, not proved here:
  \<^item> The translation (AutoCorrode) gives the Rust program its meaning. The theorem is about the
    translated function; that it carries over to the compiled Rust program rests on the
    translation.
  \<^item> The statement is made in the locale \<open>Sat_heap\<close>, whose assumptions describe a heap with one
    kind of reference per type of mutable local. They are those of AutoCorrode's reference model,
    and the theorem holds for every heap that satisfies them.
  \<^item> The command line (\<^verbatim>\<open>cli/\<close>), which reads a DIMACS file into a \<^typ>\<open>Formula\<close> and prints
    the answer and the assignment in the format of the SAT competition, is not verified.
\<close>

subsection \<open>Formulas and their semantics\<close>

text \<open>Transcription of the Creusot logic functions:
  \<^item> \<^verbatim>\<open>Assignments\<close> is \<^verbatim>\<open>Vec<bool>\<close>; its model \<^verbatim>\<open>a@\<close> is the sequence of booleans, so
    assignments are quantified as @{typ \<open>bool list\<close>}.
  \<^item> Creusot's mathematical integers (\<^verbatim>\<open>x@\<close> of a \<^verbatim>\<open>usize\<close>) are \<^term>\<open>unat\<close> of the word.
  \<^item> \<^verbatim>\<open>s[i]\<close> on a Creusot sequence and \<^term>\<open>xs ! i\<close> in HOL are both unspecified out of
    bounds; \<open>formula_invariant\<close> makes every literal's variable a valid index.\<close>

text \<open>\<^verbatim>\<open>Lit::sat\<close>: the literal's variable has the literal's value.\<close>
definition lit_sat :: \<open>bool list \<Rightarrow> Lit \<Rightarrow> bool\<close> where
  \<open>lit_sat a l \<equiv> a ! unat (Lit_var l) = Lit_value l\<close>

text \<open>\<^verbatim>\<open>Clause::sat\<close>: some literal of the clause is satisfied.\<close>
definition clause_sat :: \<open>bool list \<Rightarrow> Clause \<Rightarrow> bool\<close> where
  \<open>clause_sat a c \<equiv> \<exists>l \<in> set (Clause_v0 c). lit_sat a l\<close>

text \<open>\<^verbatim>\<open>Formula::sat\<close>: every clause of the formula is satisfied.\<close>
definition formula_sat :: \<open>bool list \<Rightarrow> Formula \<Rightarrow> bool\<close> where
  \<open>formula_sat a f \<equiv> \<forall>c \<in> set (Formula_clauses f). clause_sat a c\<close>

text \<open>\<^verbatim>\<open>Formula::invariant\<close>, with \<^verbatim>\<open>Clause::vars_in_range\<close> and
  \<^verbatim>\<open>Lit::var_in_range\<close>: every literal's variable is below the number of variables.\<close>
definition formula_invariant :: \<open>Formula \<Rightarrow> bool\<close> where
  \<open>formula_invariant f \<equiv>
     \<forall>c \<in> set (Formula_clauses f). \<forall>l \<in> set (Clause_v0 c). unat (Lit_var l) < unat (Formula_num_vars f)\<close>

text \<open>Every list in the formula has fewer than \<open>2^63\<close> elements. This holds for every value of a
  Rust program (a \<^verbatim>\<open>Vec\<close> has at most \<^verbatim>\<open>isize::MAX\<close> elements); HOL lists have no such
  bound, so the precondition states it.\<close>
definition sat_repr_ok :: \<open>Formula \<Rightarrow> bool\<close> where
  \<open>sat_repr_ok f \<equiv>
     length (Formula_clauses f) < 2 ^ 63 \<and> (\<forall>c \<in> set (Formula_clauses f). length (Clause_v0 c) < 2 ^ 63)\<close>

subsection \<open>The contract\<close>

context Sat_ctx
begin

definition solver_contract :: \<open>Formula \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  \<open>solver_contract f \<equiv>
     let pre = can_alloc_reference \<star> \<langle>formula_invariant f \<and> sat_repr_ok f\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>case r of
           Answer_Sat a \<Rightarrow>
             length (Assignments_v0 a) = unat (Formula_num_vars f) \<and> formula_sat (Assignments_v0 a) f
         | Answer_Unsat \<Rightarrow> (\<forall>a. length a = unat (Formula_num_vars f) \<longrightarrow> \<not> formula_sat a f)\<rangle> in
     make_function_contract pre post\<close>

text \<open>\<^const>\<open>solver_contract\<close> \<open>f\<close>:
  \<^item> Precondition: every literal's variable is below the number of variables
    (\<^const>\<open>formula_invariant\<close>), and every list in \<open>f\<close> has fewer than \<open>2^63\<close> elements
    (\<^const>\<open>sat_repr_ok\<close>).
  \<^item> \<^verbatim>\<open>Sat(a)\<close>: \<open>a\<close> assigns a value to each of the formula's variables (its length is the
    number of variables) and satisfies \<open>f\<close>. \<^verbatim>\<open>Unsat\<close>: no assignment of the formula's
    variables satisfies \<open>f\<close>.
  \<^item> No panic (the abort postcondition is false). The program logic does not model the
    exhaustion of memory or of the stack, so the contract says nothing about them.
  \<^item> \<open>can_alloc_reference\<close>: the solver allocates mutable locals; this is AutoCorrode's
    requirement, not part of the Rust contract.\<close>

end

subsection \<open>The statement over all instances with enough fuel\<close>

text \<open>The translation bounds every loop without an iteration bound and every recursion by the
  fuel \<^verbatim>\<open>urust_fuel\<close>, the last parameter of \<^locale>\<open>Sat_ctx\<close>, and panics when it runs out.
  A statement that quantifies over the fuel is therefore made outside that locale. The
  assumptions of \<^locale>\<open>Sat_ctx\<close> do not mention the fuel, so its instances that differ only in
  the fuel share their assumptions. The locale \<open>Sat_heap\<close> has the parameters and assumptions of
  \<^locale>\<open>Sat_ctx\<close> except the fuel (it repeats \<^verbatim>\<open>urust/Sat_Locale.thy\<close> without its last
  line); each value of the fuel gives an instance of \<^locale>\<open>Sat_ctx\<close> with the parameters of
  \<open>Sat_heap\<close>. The abbreviation \<open>solver\<close> below passes to \<^verbatim>\<open>Sat_ctx.solver\<close> the prisms
  of the locale that this function takes, in order. Like the locale, this list follows the
  implementation (\<^verbatim>\<open>tools/check-spec.sh\<close> checks its form, type checking that it is the
  function's list); the contract is stated on the input and output types only.\<close>

locale Sat_heap =
  reference reference_types
  + ref_1: reference_allocatable reference_types _ _ _ _ _ _ _ prism_1 \<comment> \<open>bool list\<close>
  + ref_2: reference_allocatable reference_types _ _ _ _ _ _ _ prism_2 \<comment> \<open>64 word\<close>
  + ref_3: reference_allocatable reference_types _ _ _ _ _ _ _ prism_3 \<comment> \<open>Search\<close>
  + ref_4: reference_allocatable reference_types _ _ _ _ _ _ _ prism_4 \<comment> \<open>Clause list\<close>
  + ref_5: reference_allocatable reference_types _ _ _ _ _ _ _ prism_5 \<comment> \<open>Lit list\<close>
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
  and prism_1 :: \<open>('gv, bool list) prism\<close>
  and prism_2 :: \<open>('gv, 64 word) prism\<close>
  and prism_3 :: \<open>('gv, Search) prism\<close>
  and prism_4 :: \<open>('gv, Clause list) prism\<close>
  and prism_5 :: \<open>('gv, Lit list) prism\<close>
begin

abbreviation solver :: \<open>nat \<Rightarrow> Formula \<Rightarrow> ('s, Answer, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>solver fuel \<equiv> Sat_ctx.solver update_raw_fun dereference_raw_fun reference_raw_fun prism_1 prism_2 prism_3 prism_4 prism_5 fuel\<close>

abbreviation solver_contract :: \<open>Formula \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  \<open>solver_contract \<equiv> Sat_ctx.solver_contract can_alloc_reference\<close>

definition solver_correct where
  \<open>solver_correct \<Gamma> \<equiv>
     \<forall>f. formula_invariant f \<and> sat_repr_ok f \<longrightarrow> (\<exists>N. \<forall>fuel \<ge> N. \<Gamma>; solver fuel f \<Turnstile>\<^sub>F solver_contract f)\<close>

text \<open>\<^const>\<open>solver_correct\<close> \<open>\<Gamma>\<close> is the top-level statement: for every formula that satisfies the
  precondition of \<^const>\<open>Sat_ctx.solver_contract\<close> there is a bound \<open>N\<close> such that, with any
  fuel at least \<open>N\<close>, \<^verbatim>\<open>solver\<close> satisfies the contract. \<^verbatim>\<open>Sat_Top\<close> proves it as the theorem
  \<open>solver_correct\<close>.\<close>

end

end
