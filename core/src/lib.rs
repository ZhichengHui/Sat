#![allow(non_snake_case)]

// A naive, but verified SAT solver: backtracking with unit propagation. Before each decision it
// assigns the remaining literal of every unit clause until none is left, abandons a branch as soon
// as the partial assignment falsifies a clause, and decides the first unassigned literal of the
// first clause without a true literal, trying the literal's value first.
// It is a port of a verified WhyML solver, and is therefore
// an imperative implementation of a functional program.

pub struct Assignments(pub Vec<bool>);
pub struct Lit {
    pub var: usize,
    pub value: bool,
}
pub struct Clause(pub Vec<Lit>);

/// A partial assignment: variable `v` is assigned iff `set[v]`, and then has the value
/// `assign.0[v]`.
pub struct Pasn {
    assign: Assignments,
    set: Vec<bool>,
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
    /// and has the other value.
    fn falsified(&self, pa: &Pasn) -> bool {
        let mut i: usize = 0;
        let clause_len = self.0.len();
        while i < clause_len {
            if !pa.set[self.0[i].var] {
                return false;
            }
            if pa.assign.0[self.0[i].var] == self.0[i].value {
                return false;
            }
            i += 1;
        }
        true
    }

    /// Some literal is assigned its value.
    fn has_true(&self, pa: &Pasn) -> bool {
        let mut i: usize = 0;
        let clause_len = self.0.len();
        while i < clause_len {
            if pa.set[self.0[i].var] && pa.assign.0[self.0[i].var] == self.0[i].value {
                return true;
            }
            i += 1;
        }
        false
    }

    /// The index of the first unassigned literal at or after `start`; the clause's length if
    /// there is none.
    fn unset_from(&self, pa: &Pasn, start: usize) -> usize {
        let mut i: usize = start;
        let clause_len = self.0.len();
        while i < clause_len {
            if !pa.set[self.0[i].var] {
                return i;
            }
            i += 1;
        }
        clause_len
    }

    /// The index of the only unassigned literal if the clause is unit under the partial
    /// assignment (every other literal is assigned and false); the clause's length plus one if
    /// the clause is false; otherwise the clause's length.
    fn unit_lit(&self, pa: &Pasn) -> usize {
        let clause_len = self.0.len();
        if self.has_true(pa) {
            return clause_len;
        }
        let k = self.unset_from(pa, 0);
        if k == clause_len {
            return clause_len + 1;
        }
        if self.unset_from(pa, k + 1) < clause_len {
            return clause_len;
        }
        k
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

    /// The index of the first clause without a true literal under the partial assignment; the
    /// number of clauses if every clause has one.
    fn open_clause(&self, pa: &Pasn) -> usize {
        let mut i: usize = 0;
        while i < self.clauses.len() {
            if !self.clauses[i].has_true(pa) {
                return i;
            }
            i += 1;
        }
        self.clauses.len()
    }

    /// The index of the first clause at or after `start` that is unit or false under the partial
    /// assignment; the number of clauses if there is none.
    fn unit_clause(&self, pa: &Pasn, start: usize) -> usize {
        let mut i: usize = start;
        while i < self.clauses.len() {
            if self.clauses[i].unit_lit(pa) != self.clauses[i].0.len() {
                return i;
            }
            i += 1;
        }
        self.clauses.len()
    }
}

/// The list `xs` with the element at `i` replaced by `x`.
fn updated(xs: &Vec<bool>, i: usize, x: bool) -> Vec<bool> {
    let mut ys = xs.clone();
    ys[i] = x;
    ys
}

/// The partial assignment `pa` with the variable `v` assigned the value `b`.
fn set_var(pa: &Pasn, v: usize, b: bool) -> Pasn {
    Pasn { assign: Assignments(updated(&pa.assign.0, v, b)), set: updated(&pa.set, v, true) }
}

/// Unit propagation: assigns the remaining literal of a unit clause until there is none or a
/// clause is false. It looks for the next unit clause from `start` on, after the last one, and
/// stops after a pass from the first clause finds none.
fn propagate(f: &Formula, pa: Pasn, start: usize) -> Pasn {
    let c = f.unit_clause(&pa, start);
    if c == f.clauses.len() {
        if start == 0 {
            return pa;
        }
        return propagate(f, pa, 0);
    }
    let k = f.clauses[c].unit_lit(&pa);
    if k >= f.clauses[c].0.len() {
        return pa;
    }
    let pb = set_var(&pa, f.clauses[c].0[k].var, f.clauses[c].0[k].value);
    propagate(f, pb, c + 1)
}

fn solve(f: &Formula, pa: Pasn) -> Answer {
    let pb = propagate(f, pa, 0);
    if f.conflict(&pb) {
        return Answer::Unsat;
    }
    let c = f.open_clause(&pb);
    if c == f.clauses.len() {
        return Answer::Sat(pb.assign);
    }
    let k = f.clauses[c].unset_from(&pb, 0);
    let v = f.clauses[c].0[k].var;
    let b = f.clauses[c].0[k].value;
    match solve(f, set_var(&pb, v, b)) {
        Answer::Sat(a) => Answer::Sat(a),
        Answer::Unsat => solve(f, set_var(&pb, v, !b)),
    }
}

pub fn solver(f: &Formula) -> Answer {
    solve(f, Pasn { assign: Assignments(vec![false; f.num_vars]), set: vec![false; f.num_vars] })
}
