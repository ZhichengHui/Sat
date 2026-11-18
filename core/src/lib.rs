#![allow(non_snake_case)]

// A naive, but verified SAT solver: backtracking over the variables in a fixed order, which
// abandons a branch as soon as the partial assignment falsifies a clause.
// It is a port of a verified WhyML solver, and is therefore
// an imperative implementation of a functional program.

pub struct Assignments(pub Vec<bool>);
pub struct Lit {
    pub var: usize,
    pub value: bool,
}
pub struct Clause(pub Vec<Lit>);

pub struct Pasn {
    assign: Assignments,
    ix: usize,
}
pub struct Formula {
    pub clauses: Vec<Clause>,
    pub num_vars: usize,
}

/// The answer of the solver: a satisfying assignment of all the formula's variables, or none.
pub enum Answer {
    Sat(Assignments),
    Unsat,
}

impl Clause {
    /// The clause is false under the partial assignment: every literal's variable is assigned
    /// (below `pa.ix`) and has the other value.
    fn falsified(&self, pa: &Pasn) -> bool {
        let mut i: usize = 0;
        let clause_len = self.0.len();
        while i < clause_len {
            if self.0[i].var >= pa.ix {
                return false;
            }
            if pa.assign.0[self.0[i].var] == self.0[i].value {
                return false;
            }
            i += 1;
        }
        true
    }
}

impl Formula {
    /// Some clause is false under the partial assignment.
    fn conflict(&self, pa: &Pasn) -> bool {
        let mut i: usize = 0;
        while i < self.clauses.len() {
            if self.clauses[i].falsified(pa) {
                return true;
            }
            i += 1;
        }
        false
    }
}

fn set_next(pa: &Pasn, b: bool) -> Pasn {
    let mut assign = pa.assign.0.clone();
    assign[pa.ix] = b;
    Pasn { assign: Assignments(assign), ix: pa.ix + 1 }
}

fn solve(f: &Formula, pa: Pasn) -> Answer {
    if f.conflict(&pa) {
        return Answer::Unsat;
    }
    if pa.ix == pa.assign.0.len() {
        return Answer::Sat(pa.assign);
    }
    match solve(f, set_next(&pa, true)) {
        Answer::Sat(a) => Answer::Sat(a),
        Answer::Unsat => solve(f, set_next(&pa, false)),
    }
}

pub fn solver(f: &Formula) -> Answer {
    solve(f, Pasn { assign: Assignments(vec![false; f.num_vars]), ix: 0 })
}
