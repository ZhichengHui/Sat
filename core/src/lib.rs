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

impl Clone for Assignments {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl Clone for Pasn {
    fn clone(&self) -> Self {
        Self { assign: self.assign.clone(), ix: self.ix }
    }
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
    let mut new_pa = pa.clone();
    new_pa.assign.0[pa.ix] = b;
    new_pa.ix += 1;
    new_pa
}

fn solve(f: &Formula, pa: Pasn) -> bool {
    if pa.ix == pa.assign.0.len() {
        return f.eval(&pa.assign);
    }
    solve(f, set_next(&pa, true)) || solve(f, set_next(&pa, false))
}

pub fn solver(f: &Formula) -> bool {
    solve(f, Pasn { assign: Assignments(vec![false; f.num_vars]), ix: 0 })
}
