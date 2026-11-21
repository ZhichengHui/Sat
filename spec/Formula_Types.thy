theory Formula_Types
  imports Sat.Sat_Funs
begin

section \<open>The data types of formulas\<close>

text \<open>
  The types of formulas (\<^verbatim>\<open>Formula\<close>, \<^verbatim>\<open>Clause\<close>, \<^verbatim>\<open>Lit\<close>) and of answers
  (\<^verbatim>\<open>Answer\<close>, \<^verbatim>\<open>Assignments\<close>) are generated from
  \<^verbatim>\<open>core/src/lib.rs\<close> into \<^verbatim>\<open>urust/\<close>. The specification depends on their exact shape, so
  this theory states it: every constructor with the types of its arguments, and every record field
  with its type. The lemmas are proved from the
  generated types, so a change to one of these types in the Rust code makes this theory fail to
  build. Every name is written with \<open>CONST\<close>, so a constructor or field that no longer exists is an
  error, not a new variable.
\<close>

text \<open>\<^typ>\<open>Lit\<close> is a record with exactly these fields.\<close>
lemma Lit_shape:
  fixes x y :: Lit
  shows \<open>x = y \<longleftrightarrow>
     (CONST Lit_var x :: 64 word) = Lit_var y \<and>
     (CONST Lit_value x :: bool) = Lit_value y\<close>
  by (cases x; cases y) simp

text \<open>\<^typ>\<open>Clause\<close> is a record with exactly these fields.\<close>
lemma Clause_shape:
  fixes x y :: Clause
  shows \<open>x = y \<longleftrightarrow> (CONST Clause_v0 x :: Lit rvec) = Clause_v0 y\<close>
  by (cases x; cases y) simp

text \<open>\<^typ>\<open>Formula\<close> is a record with exactly these fields.\<close>
lemma Formula_shape:
  fixes x y :: Formula
  shows \<open>x = y \<longleftrightarrow>
     (CONST Formula_clauses x :: Clause rvec) = Formula_clauses y \<and>
     (CONST Formula_num_vars x :: 64 word) = Formula_num_vars y\<close>
  by (cases x; cases y) simp

text \<open>\<^typ>\<open>Assignments\<close> is a record with exactly these fields.\<close>
lemma Assignments_shape:
  fixes x y :: Assignments
  shows \<open>x = y \<longleftrightarrow> (CONST Assignments_v0 x :: bool rvec) = Assignments_v0 y\<close>
  by (cases x; cases y) simp

text \<open>\<^typ>\<open>Answer\<close> has exactly these constructors.\<close>
lemma Answer_shape:
  fixes x :: Answer
  obtains a0 where \<open>x = CONST Answer_Sat (a0 :: Assignments)\<close>
  | \<open>x = CONST Answer_Unsat\<close>
  by (cases x) auto

end
