#![allow(non_snake_case)]

// This is a very naive, but verified SAT solver.
// It is a port of a verified WhyML solver, and is therefore
// an imperative implementation of a functional prgram.
// In other words: very naive, very slow.

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
    fn eval(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        let clause_len = self.0.len();
        while i < clause_len {
            if a.0[self.0[i].var] == self.0[i].value {
                return true;
            }
            i += 1;
        }
        false
    }
}

impl Formula {
    fn eval(&self, a: &Assignments) -> bool {
        let mut i: usize = 0;
        while i < self.clauses.len() {
            if !self.clauses[i].eval(a) {
                return false;
            }
            i += 1;
        }
        true
    }
}

fn set_next(pa: &Pasn, b: bool) -> Pasn {
    let mut assign = pa.assign.0.clone();
    assign[pa.ix] = b;
    Pasn { assign: Assignments(assign), ix: pa.ix + 1 }
}

fn solve(f: &Formula, pa: Pasn) -> Answer {
    if pa.ix == pa.assign.0.len() {
        if f.eval(&pa.assign) {
            return Answer::Sat(pa.assign);
        }
        return Answer::Unsat;
    }
    match solve(f, set_next(&pa, true)) {
        Answer::Sat(a) => Answer::Sat(a),
        Answer::Unsat => solve(f, set_next(&pa, false)),
    }
}

pub fn solver(f: &Formula) -> Answer {
    solve(f, Pasn { assign: Assignments(vec![false; f.num_vars]), ix: 0 })
}
