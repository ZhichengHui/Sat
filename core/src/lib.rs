#![allow(non_snake_case)]

// A verified SAT solver: conflict-driven clause learning (CDCL) with two watched literals, first-UIP
// learning and non-chronological backjumping; it decides the first unassigned variable, false
// first (`cdcl`). Its answers need no proof of termination: `Unsat` only when it has derived the
// empty clause by resolution, `Sat` only for an assignment of every variable that falsifies no
// clause of the formula. Should it stop without an answer, the solver falls back on DPLL with unit
// propagation (`solve`), a port of a verified WhyML solver.

pub struct Assignments(pub Vec<bool>);
#[derive(Clone, Copy)]
pub struct Lit {
    pub var: usize,
    pub value: bool,
}
#[derive(Clone)]
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

/// The reason of a decision and of an unassigned variable, and the absence of a conflict.
const NONE: usize = usize::MAX;
/// The CDCL search stops (and the solver falls back on `solve`) if the formula has this many
/// variables or more, so that the index of a literal fits a `usize`.
const MAX_VARS: usize = 1 << 62;

/// The index of the literal `l` in the watch lists: `2·var + value`.
fn lit_idx(l: Lit) -> usize {
    if l.value { 2 * l.var + 1 } else { 2 * l.var }
}

/// The literal `l` occurs in `c`.
fn contains(c: &Vec<Lit>, l: Lit) -> bool {
    let mut i: usize = 0;
    while i < c.len() {
        if c[i].var == l.var && c[i].value == l.value {
            return true;
        }
        i += 1;
    }
    false
}

/// The clause `c` without repeated literals; `None` if it has a complementary pair (a tautology).
fn normalize(c: &Clause) -> Option<Clause> {
    let mut out: Vec<Lit> = Vec::new();
    let mut i: usize = 0;
    while i < c.0.len() {
        let l = c.0[i];
        if contains(&c.0, Lit { var: l.var, value: !l.value }) {
            return None;
        }
        if !contains(&out, l) {
            out.push(l);
        }
        i += 1;
    }
    Some(Clause(out))
}

/// The resolvent of `c` and `d` on the variable `v`: `c` without the literal `(v, !b)` and `d`
/// without the literal `(v, b)`, each literal once.
fn resolve(c: &Vec<Lit>, d: &Vec<Lit>, v: usize, b: bool) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::new();
    let mut i: usize = 0;
    while i < c.len() {
        if !(c[i].var == v && c[i].value != b) {
            out.push(c[i]);
        }
        i += 1;
    }
    let mut j: usize = 0;
    while j < d.len() {
        if !(d[j].var == v && d[j].value == b) && !contains(&out, d[j]) {
            out.push(d[j]);
        }
        j += 1;
    }
    out
}

/// The state of the CDCL search. `db` holds the clauses of the formula (without repeated
/// literals and tautologies) and the learned clauses; every one of them is satisfied by every
/// model of the formula. A clause of at least two literals is watched by its first two literals:
/// `watches[lit_idx(l)]` lists the clauses that watch `l`. The variables assigned are listed in
/// `trail` in the order of assignment, those before `qhead` already propagated; `level` and
/// `reason` give the decision level of each and the clause that implied it (`NONE` for a
/// decision); `dl` is the current decision level.
struct Cdcl {
    pa: Pasn,
    level: Vec<usize>,
    reason: Vec<usize>,
    trail: Vec<usize>,
    qhead: usize,
    db: Vec<Clause>,
    watches: Vec<Vec<usize>>,
    dl: usize,
}

impl Cdcl {
    /// The literal `l` is assigned its value.
    fn lit_true(&self, l: Lit) -> bool {
        self.pa.set[l.var] && self.pa.assign.0[l.var] == l.value
    }

    /// The literal `l` is assigned the other value.
    fn lit_false(&self, l: Lit) -> bool {
        self.pa.set[l.var] && self.pa.assign.0[l.var] != l.value
    }

    /// Assigns the literal `l` at the current decision level, with the reason `r`.
    fn enqueue(&mut self, l: Lit, r: usize) {
        self.pa.set[l.var] = true;
        self.pa.assign.0[l.var] = l.value;
        self.level[l.var] = self.dl;
        self.reason[l.var] = r;
        self.trail.push(l.var);
    }

    /// Adds the clause `c` (of at least two literals) to the database, watched by its first two
    /// literals; returns its index.
    fn add_clause(&mut self, c: Clause) -> usize {
        let i = self.db.len();
        let w0 = lit_idx(c.0[0]);
        let w1 = lit_idx(c.0[1]);
        self.db.push(c);
        self.watches[w0].push(i);
        self.watches[w1].push(i);
        i
    }

    /// The index of a literal of clause `c` from position 2 on that is not false; the clause's
    /// length if there is none.
    fn new_watch(&self, c: usize) -> usize {
        let mut k: usize = 2;
        while k < self.db[c].0.len() {
            if !self.lit_false(self.db[c].0[k]) {
                return k;
            }
            k += 1;
        }
        self.db[c].0.len()
    }

    /// Unit propagation with the watched literals: processes the trail from `qhead` on. Returns
    /// the index of a clause whose literals are all false, or `NONE`.
    fn propagate(&mut self) -> usize {
        while self.qhead < self.trail.len() {
            let v = self.trail[self.qhead];
            self.qhead += 1;
            let fl = Lit { var: v, value: !self.pa.assign.0[v] };
            let fi = lit_idx(fl);
            let ws = std::mem::replace(&mut self.watches[fi], Vec::new());
            let mut confl = NONE;
            let mut i: usize = 0;
            while i < ws.len() {
                let c = ws[i];
                i += 1;
                if confl != NONE || self.db[c].0.len() < 2 {
                    self.watches[fi].push(c);
                    continue;
                }
                if self.db[c].0[0].var == fl.var && self.db[c].0[0].value == fl.value {
                    self.db[c].0.swap(0, 1);
                }
                let first = self.db[c].0[0];
                if self.lit_true(first) {
                    self.watches[fi].push(c);
                    continue;
                }
                let k = self.new_watch(c);
                if k < self.db[c].0.len() {
                    self.db[c].0.swap(1, k);
                    let w = lit_idx(self.db[c].0[1]);
                    self.watches[w].push(c);
                    continue;
                }
                self.watches[fi].push(c);
                if self.pa.set[first.var] {
                    confl = c;
                } else {
                    self.enqueue(first, c);
                }
            }
            if confl != NONE {
                return confl;
            }
        }
        NONE
    }

    /// The number of literals of `c` whose variable has the decision level `lv`.
    fn count_level(&self, c: &Vec<Lit>, lv: usize) -> usize {
        let mut n: usize = 0;
        let mut i: usize = 0;
        while i < c.len() {
            if self.level[c[i].var] == lv {
                n += 1;
            }
            i += 1;
        }
        n
    }

    /// Conflict analysis: from the clause `confl` (all false), resolves with the reasons of the
    /// variables of the current level, latest first, until one literal of that level is left (the
    /// first unique implication point); at level 0 until none is left. It stops early if the
    /// clause gets more literals than there are variables, which does not happen: all its
    /// literals are false.
    fn analyze(&self, confl: usize) -> Vec<Lit> {
        let mut cl: Vec<Lit> = self.db[confl].0.clone();
        let stop: usize = if self.dl == 0 { 0 } else { 1 };
        let mut t = self.trail.len();
        while t > 0 && cl.len() <= self.pa.set.len() && self.count_level(&cl, self.dl) > stop {
            t -= 1;
            let v = self.trail[t];
            let r = self.reason[v];
            let b = self.pa.assign.0[v];
            if r != NONE && contains(&cl, Lit { var: v, value: !b }) {
                cl = resolve(&cl, &self.db[r].0, v, b);
            }
        }
        cl
    }

    /// Unassigns every variable of a decision level above `lv`.
    fn backjump(&mut self, lv: usize) {
        while self.trail.len() > 0 && self.level[self.trail[self.trail.len() - 1]] > lv {
            let v = self.trail[self.trail.len() - 1];
            self.trail.pop();
            self.pa.set[v] = false;
            self.reason[v] = NONE;
        }
        self.qhead = self.trail.len();
        self.dl = lv;
    }

    /// The first unassigned variable; `NONE` if every variable is assigned.
    fn pick(&self) -> usize {
        let mut v: usize = 0;
        while v < self.pa.set.len() {
            if !self.pa.set[v] {
                return v;
            }
            v += 1;
        }
        NONE
    }

    /// Learns the (non-empty) clause `c` derived by `analyze` at a level above 0: backjumps to
    /// the largest level of its other literals, adds it to the database with its literal of the
    /// current level first, and assigns that literal.
    fn learn(&mut self, cl: Vec<Lit>) {
        let mut c = cl;
        let mut i: usize = 0;
        while i < c.len() {
            if self.level[c[i].var] == self.dl {
                c.swap(0, i);
            }
            i += 1;
        }
        let mut bj: usize = 0;
        let mut j: usize = 1;
        while j < c.len() {
            if self.level[c[j].var] > bj {
                bj = self.level[c[j].var];
                c.swap(1, j);
            }
            j += 1;
        }
        self.backjump(bj);
        let l = c[0];
        let r = if c.len() == 1 {
            let r = self.db.len();
            self.db.push(Clause(c));
            r
        } else {
            self.add_clause(Clause(c))
        };
        if !self.pa.set[l.var] {
            self.enqueue(l, r);
        }
    }
}

/// The CDCL search: `Some` answer, or `None` if it stops without one.
pub fn cdcl(f: &Formula) -> Option<Answer> {
    let n = f.num_vars;
    if n >= MAX_VARS {
        return None;
    }
    let mut s = Cdcl {
        pa: Pasn { assign: Assignments(vec![false; n]), set: vec![false; n] },
        level: vec![0; n],
        reason: vec![NONE; n],
        trail: Vec::new(),
        qhead: 0,
        db: Vec::new(),
        watches: vec![Vec::new(); 2 * n],
        dl: 0,
    };
    let mut confl = NONE;
    let mut i: usize = 0;
    while i < f.clauses.len() {
        match normalize(&f.clauses[i]) {
            None => {}
            Some(c) => {
                if c.0.len() == 0 {
                    return Some(Answer::Unsat);
                }
                if c.0.len() == 1 {
                    let l = c.0[0];
                    let r = s.db.len();
                    s.db.push(c);
                    if !s.pa.set[l.var] {
                        s.enqueue(l, r);
                    } else if s.pa.assign.0[l.var] != l.value {
                        confl = r;
                    }
                } else {
                    s.add_clause(c);
                }
            }
        }
        i += 1;
    }
    loop {
        if confl == NONE {
            confl = s.propagate();
        }
        if confl != NONE {
            let cl = s.analyze(confl);
            confl = NONE;
            if cl.len() == 0 {
                return Some(Answer::Unsat);
            }
            if s.dl == 0 || cl.len() > n {
                return None;
            }
            s.learn(cl);
            continue;
        }
        let v = s.pick();
        if v == NONE {
            if f.conflict(&s.pa) {
                return None;
            }
            return Some(Answer::Sat(s.pa.assign));
        }
        if s.dl >= n {
            return None;
        }
        s.dl += 1;
        s.enqueue(Lit { var: v, value: false }, NONE);
    }
}

pub fn solver(f: &Formula) -> Answer {
    match cdcl(f) {
        Some(a) => a,
        None => solve(f, Pasn { assign: Assignments(vec![false; f.num_vars]), set: vec![false; f.num_vars] }),
    }
}
