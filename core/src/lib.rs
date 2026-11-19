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
        let mut k: usize = clause_len;
        let mut i: usize = 0;
        while i < clause_len {
            if pa.set[self.0[i].var] {
                if pa.assign.0[self.0[i].var] == self.0[i].value {
                    return clause_len;
                }
            } else {
                if k < clause_len {
                    return clause_len;
                }
                k = i;
            }
            i += 1;
        }
        if k == clause_len {
            return clause_len + 1;
        }
        k
    }
}

impl Formula {
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

    /// The index of the first clause in `start..end` that is unit or false under the partial
    /// assignment; `end` if there is none.
    fn unit_clause(&self, pa: &Pasn, start: usize, end: usize) -> usize {
        let mut i: usize = start;
        while i < end {
            if self.clauses[i].unit_lit(pa) != self.clauses[i].0.len() {
                return i;
            }
            i += 1;
        }
        end
    }
}

/// The list `xs` with the element at `i` replaced by `x`.
fn updated(xs: Vec<bool>, i: usize, x: bool) -> Vec<bool> {
    let mut ys = xs;
    ys[i] = x;
    ys
}

/// A copy of the partial assignment `pa`.
fn copy(pa: &Pasn) -> Pasn {
    Pasn { assign: Assignments(pa.assign.0.clone()), set: pa.set.clone() }
}

/// The partial assignment `pa` with the variable `v` assigned the value `b`.
fn set_var(pa: Pasn, v: usize, b: bool) -> Pasn {
    Pasn { assign: Assignments(updated(pa.assign.0, v, b)), set: updated(pa.set, v, true) }
}

/// The result of unit propagation: a clause is false, or the partial assignment has no unit or
/// false clause.
enum Propagated {
    Conflict,
    Fixpoint(Pasn),
}

/// Unit propagation: assigns the remaining literal of a unit clause until there is none or a
/// clause is false. It scans the clauses `start..end`; after a unit clause it goes on from the
/// next clause to the last one, then from the first clause up to the next one after the unit
/// clause, so it stops after a whole round of the clauses that finds none.
fn propagate(f: &Formula, pa: Pasn, start: usize, end: usize) -> Propagated {
    let c = f.unit_clause(&pa, start, end);
    if c == end {
        if end == f.clauses.len() && start != 0 {
            return propagate(f, pa, 0, start);
        }
        return Propagated::Fixpoint(pa);
    }
    let k = f.clauses[c].unit_lit(&pa);
    if k >= f.clauses[c].0.len() {
        return Propagated::Conflict;
    }
    let pb = set_var(pa, f.clauses[c].0[k].var, f.clauses[c].0[k].value);
    propagate(f, pb, c + 1, f.clauses.len())
}

fn solve(f: &Formula, pa: Pasn) -> Answer {
    match propagate(f, pa, 0, f.clauses.len()) {
        Propagated::Conflict => Answer::Unsat,
        Propagated::Fixpoint(pb) => {
            let c = f.open_clause(&pb);
            if c == f.clauses.len() {
                return Answer::Sat(pb.assign);
            }
            let k = f.clauses[c].unset_from(&pb, 0);
            let v = f.clauses[c].0[k].var;
            let b = f.clauses[c].0[k].value;
            match solve(f, set_var(copy(&pb), v, b)) {
                Answer::Sat(a) => Answer::Sat(a),
                Answer::Unsat => solve(f, set_var(pb, v, !b)),
            }
        }
    }
}

// Conflict-driven clause learning (CDCL). The search below is not trusted: every index is checked
// before use, so it never panics, and its answers are checked before they are returned. A `Sat`
// answer is an assignment that `satisfies` checks against the formula; an `Unsat` answer is a
// learned empty clause. Every learned clause is first certified by `certify` to follow from the
// formula and the clauses learned before. When a check fails, or a loop runs out of fuel, `cdcl`
// gives up and `solver` falls back to `solve`.

/// No clause, node or variable: the largest `usize`.
const NONE: usize = 18446744073709551615;
/// A bound on the number of variables and clauses for which the search runs (`2^62`), so that
/// `2 * v + 1` and `2 * c + 1` do not overflow.
const BIG: usize = 4611686018427387904;

/// The number of literals of clause `c` of the clause database: the formula's clauses followed by
/// the learned ones; 0 if there is no such clause.
fn clause_len(f: &Formula, learned: &Vec<Clause>, c: usize) -> usize {
    let m = f.clauses.len();
    if c < m {
        return f.clauses[c].0.len();
    }
    if c - m < learned.len() {
        return learned[c - m].0.len();
    }
    0
}

/// Literal `j` of clause `c` of the clause database; a literal of the variable `NONE` if there is
/// none.
fn lit_at(f: &Formula, learned: &Vec<Clause>, c: usize, j: usize) -> Lit {
    let m = f.clauses.len();
    if c < m {
        if j < f.clauses[c].0.len() {
            return Lit { var: f.clauses[c].0[j].var, value: f.clauses[c].0[j].value };
        }
        return Lit { var: NONE, value: false };
    }
    if c - m < learned.len() && j < learned[c - m].0.len() {
        return Lit { var: learned[c - m].0[j].var, value: learned[c - m].0[j].value };
    }
    Lit { var: NONE, value: false }
}

/// Clause `c` exists in the clause database.
fn clause_exists(f: &Formula, learned: &Vec<Clause>, c: usize) -> bool {
    c < f.clauses.len() || c - f.clauses.len() < learned.len()
}

/// The index of the watch list of the literal `(v, b)`: `2v + b`; `NONE` if `v` is too large.
fn key(v: usize, b: bool) -> usize {
    if v < BIG {
        if b {
            return 2 * v + 1;
        }
        return 2 * v;
    }
    NONE
}

/// The cut of `reduce`: the learned clauses of a literal block distance above `t` die, and `left`
/// of those of the distance `t`.
struct Cut {
    t: usize,
    left: usize,
}

/// The state of the CDCL search. The partial assignment is `assign`/`set` as in `Pasn`, and
/// `false_lit[key(v, b)]` holds iff the literal `(v, b)` is false under it; `trail`
/// lists the assigned variables in order, decision level `d + 1` starts at trail position
/// `lim[d]`, `level[v]` is the decision level of `v` and `reason[v]` the clause that propagated
/// `v` (`NONE` for a decision). The clauses are copied into the flat `arena`, clause `c` at
/// offset `o = start[c]`: `arena[o]` is `c`, `arena[o + 1]` the end of the entry, `arena[o + 2]`
/// and `arena[o + 3]` the arena positions of its two watched literals, `arena[o + 4]` and
/// `arena[o + 5]` their keys, and from `o + 6` on the keys of its literals. The watch nodes of the
/// clause are `2o` and `2o + 1`; the watch list `watches[key(v, b)]` of the literal `(v, b)` holds
/// the nodes that watch it. A visit finds whether the other watched literal is true, and the
/// literals to scan, in one place of the arena. Each list is a vector of nodes, compacted in place
/// when it is visited.
/// `qhead` is the first trail position not yet propagated. `phase` is the last value of each
/// variable, `act` its activity, raised by `inc` whenever it takes part in a conflict; `seen`
/// marks variables during conflict analysis, and `learnt` collects the literals of the clause it
/// learns. Learned clause `i` has the literal block distance `lbd[i]` (the number of decision
/// levels of its literals when it was learned); `reduce` sets `dead[i]` for about half of them and
/// the keys of their watched literals to `NONE`, and a node whose other watched key is `NONE` is dropped
/// from a watch list when the list is visited, so a dead clause no longer takes part
/// in the search (it stays in the clause database). `stamp[l]` is `tick` if level `l` has been
/// counted by the current `learnt_lbd`; `hist` is the histogram of the distances in `reduce`.
struct Search {
    assign: Vec<bool>,
    set: Vec<bool>,
    false_lit: Vec<bool>,
    level: Vec<usize>,
    reason: Vec<usize>,
    trail: Vec<usize>,
    lim: Vec<usize>,
    qhead: usize,
    watches: Vec<Vec<usize>>,
    arena: Vec<usize>,
    start: Vec<usize>,
    phase: Vec<bool>,
    act: Vec<usize>,
    inc: usize,
    seen: Vec<bool>,
    learnt: Vec<Lit>,
    dead: Vec<bool>,
    lbd: Vec<usize>,
    stamp: Vec<usize>,
    tick: usize,
    hist: Vec<usize>,
}

impl Search {
    /// The literal of the key `k` is false.
    fn key_false(&self, k: usize) -> bool {
        k < self.false_lit.len() && self.false_lit[k]
    }

    /// The literal `(v, b)` is true.
    fn lit_true(&self, v: usize, b: bool) -> bool {
        self.key_false(key(v, !b))
    }

    /// The literal `(v, b)` is false.
    fn lit_false(&self, v: usize, b: bool) -> bool {
        self.key_false(key(v, b))
    }

    /// Assigns `b` to `v` with the reason `r` at the current decision level.
    fn enqueue(&mut self, v: usize, b: bool, r: usize) {
        if v < self.assign.len() && v < self.set.len() && v < self.level.len() && v < self.reason.len() {
            self.assign[v] = b;
            self.set[v] = true;
            self.level[v] = self.lim.len();
            self.reason[v] = r;
            self.trail.push(v);
            let k = key(v, !b);
            if k < self.false_lit.len() {
                self.false_lit[k] = true;
            }
        }
    }

    /// Adds the new clause `c` to the arena and, if it has two literals, its watch nodes `2o`,
    /// `2o + 1` watching its first two literals.
    fn attach(&mut self, f: &Formula, learned: &Vec<Clause>, c: usize) {
        let o = self.arena.len();
        self.start.push(o);
        self.push_clause(f, learned, c);
        if o < BIG && o + 7 < self.arena.len() && self.arena[o + 1] >= o + 8 {
            let k0 = self.arena[o + 6];
            let k1 = self.arena[o + 7];
            if k0 < self.watches.len() && k1 < self.watches.len() {
                self.arena[o + 4] = k0;
                self.arena[o + 5] = k1;
                self.watches[k0].push(2 * o);
                self.watches[k1].push(2 * o + 1);
            }
        }
    }

    /// Appends the entry of clause `c` to the arena: its index, the end of its entry, the
    /// positions of its first two literals, two keys `NONE`, and the keys of its literals.
    fn push_clause(&mut self, f: &Formula, learned: &Vec<Clause>, c: usize) {
        let len = clause_len(f, learned, c);
        let o = self.arena.len();
        if o < BIG && len < BIG {
            self.arena.push(c);
            self.arena.push(o + 6 + len);
            self.arena.push(o + 6);
            self.arena.push(o + 7);
            self.arena.push(NONE);
            self.arena.push(NONE);
            let mut j: usize = 0;
            while j < len {
                let l = lit_at(f, learned, c, j);
                self.arena.push(key(l.var, l.value));
                j += 1;
            }
        }
    }

    /// A position of the arena in `base..end` other than `op` and `my` whose literal is not
    /// false; `end` if there is none. The scan is cyclic and starts after the later of the two
    /// watched positions, so that the literals just before them, found false before, are read
    /// last; it reads the three ranges between the watched positions in turn.
    fn find_watch(&self, base: usize, end: usize, op: usize, my: usize) -> usize {
        if op >= end || my >= end || op < base || my < base {
            return end;
        }
        let hi = if my > op { my } else { op };
        let lo = if my > op { op } else { my };
        let a = self.scan(hi + 1, end);
        if a < end {
            return a;
        }
        let b = self.scan(base, lo);
        if b < lo {
            return b;
        }
        let d = self.scan(lo + 1, hi);
        if d < hi {
            return d;
        }
        end
    }

    /// The first position of the arena in `from..to` whose literal is not false; `to` if there
    /// is none.
    fn scan(&self, from: usize, to: usize) -> usize {
        let end = if to < self.arena.len() { to } else { self.arena.len() };
        let mut j = from;
        while j < end {
            if !self.key_false(self.arena[j]) {
                return j;
            }
            j += 1;
        }
        to
    }

    /// The literal with the key `k` is true: the literal of the key `k ^ 1` is false.
    fn key_true(&self, k: usize) -> bool {
        self.key_false(k ^ 1)
    }

    /// Visits the watch list `k` of a literal that has become false, until a clause is false: a
    /// node whose other watched key is `NONE` (a dead clause) is dropped from it; each other
    /// clause on it gets a new watched literal that is not false, propagates its other watched
    /// literal, or is false. The list is compacted in place: the nodes that stay on it move to the
    /// front, in order. The index of a false clause, or `NONE`.
    fn propagate_lit(&mut self, k: usize) -> usize {
        if k >= self.watches.len() {
            return NONE;
        }
        let mut ws = std::mem::replace(&mut self.watches[k], Vec::new());
        let mut confl = NONE;
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < ws.len() && confl == NONE {
            let node = ws[i];
            i += 1;
            let o = node / 2;
            let side = node % 2;
            let okey = if o < BIG && o + 5 < self.arena.len() { self.arena[o + 5 - side] } else { NONE };
            if okey == NONE {
            } else if self.key_true(okey) {
                if j < ws.len() {
                    ws[j] = node;
                    j += 1;
                }
            } else {
                let c = self.arena[o];
                let my = self.arena[o + 2 + side];
                let op = self.arena[o + 3 - side];
                let found = self.find_watch(o + 6, self.arena[o + 1], op, my);
                let nk = if found < self.arena[o + 1] && found < self.arena.len() { self.arena[found] } else { NONE };
                if nk < self.watches.len() && nk != k {
                    self.arena[o + 2 + side] = found;
                    self.arena[o + 4 + side] = nk;
                    self.watches[nk].push(node);
                } else {
                    if j < ws.len() {
                        ws[j] = node;
                        j += 1;
                    }
                    if self.key_false(okey) {
                        confl = c;
                    } else {
                        self.enqueue(okey / 2, okey % 2 == 1, c);
                    }
                }
            }
        }
        if k < self.watches.len() {
            self.watches[k] = close_gap(ws, i, j);
        }
        confl
    }

    /// Unit propagation of the trail from `qhead` on; the index of a false clause, or `NONE`.
    fn propagate(&mut self) -> usize {
        while self.qhead < self.trail.len() {
            let v = self.trail[self.qhead];
            self.qhead += 1;
            if v < self.assign.len() {
                let k = key(v, !self.assign[v]);
                let c = self.propagate_lit(k);
                if c != NONE {
                    self.qhead = self.trail.len();
                    return c;
                }
            }
        }
        NONE
    }

    /// Divides every activity and the increment by `2^30`.
    fn rescale(&mut self) {
        let mut i: usize = 0;
        while i < self.act.len() {
            self.act[i] = self.act[i] >> 30;
            i += 1;
        }
        self.inc = (self.inc >> 30) + 1;
    }

    /// Raises the activity of `v` by `inc`.
    fn bump(&mut self, v: usize) {
        if v < self.act.len() {
            if self.act[v] < BIG && self.inc < BIG {
                self.act[v] += self.inc;
            }
            if self.act[v] >= BIG / 2 {
                self.rescale();
            }
        }
    }

    /// The literals of clause `c` in conflict analysis: each variable other than `p`, not yet
    /// seen and above level 0 is marked; the literal is added to `learnt` if its level is below
    /// `cur`. The number of the marked variables at level `cur` or above.
    fn analyze_clause(&mut self, f: &Formula, learned: &Vec<Clause>, c: usize, p: usize, cur: usize) -> usize {
        let len = clause_len(f, learned, c);
        let mut count: usize = 0;
        let mut j: usize = 0;
        while j < len {
            let q = lit_at(f, learned, c, j);
            let v = q.var;
            if v != p && v < self.seen.len() && v < self.level.len() && !self.seen[v] && self.level[v] > 0 {
                self.seen[v] = true;
                let lv = self.level[v];
                self.bump(v);
                if lv >= cur {
                    if count < NONE {
                        count += 1;
                    }
                } else {
                    self.learnt.push(q);
                }
            }
            j += 1;
        }
        count
    }

    /// The last trail position before `idx` whose variable is marked; `NONE` if there is none.
    fn prev_seen(&self, idx: usize) -> usize {
        let mut i = idx;
        while i > 0 {
            i -= 1;
            if i < self.trail.len() && self.trail[i] < self.seen.len() && self.seen[self.trail[i]] {
                return i;
            }
        }
        NONE
    }

    /// Clears the marks of the literals of `learnt` after the first, and moves one of the highest
    /// level among them to the second position.
    fn finish_learnt(&mut self) {
        let mut best: usize = 1;
        let mut best_level: usize = 0;
        let mut j: usize = 1;
        while j < self.learnt.len() {
            let v = self.learnt[j].var;
            if v < self.seen.len() {
                self.seen[v] = false;
            }
            if v < self.level.len() && self.level[v] > best_level {
                best = j;
                best_level = self.level[v];
            }
            j += 1;
        }
        if best < self.learnt.len() && self.learnt.len() > 2 {
            self.learnt.swap(1, best);
        }
    }

    /// The literal of `v` in the learned clause is implied by the others: `v` has a reason clause
    /// whose other literals have marked variables or variables of level 0.
    fn redundant(&self, f: &Formula, learned: &Vec<Clause>, v: usize) -> bool {
        if v >= self.reason.len() || self.reason[v] == NONE {
            return false;
        }
        let r = self.reason[v];
        let len = clause_len(f, learned, r);
        let mut j: usize = 0;
        while j < len {
            let q = lit_at(f, learned, r, j).var;
            if q != v && !(q < self.seen.len() && q < self.level.len() && (self.seen[q] || self.level[q] == 0)) {
                return false;
            }
            j += 1;
        }
        true
    }

    /// Moves the literals of `learnt` after the first that are not `redundant` to the front, in
    /// order; the number of literals moved, plus one.
    fn compact(&mut self, f: &Formula, learned: &Vec<Clause>) -> usize {
        let mut i: usize = 1;
        let mut j: usize = 1;
        while j < self.learnt.len() {
            if !self.redundant(f, learned, self.learnt[j].var) && i < self.learnt.len() {
                if i < j {
                    self.learnt.swap(i, j);
                }
                i += 1;
            }
            j += 1;
        }
        i
    }

    /// Clears the marks of the variables of the literals of `learnt` from position `i` on.
    fn unmark_from(&mut self, i: usize) {
        let mut k = i;
        while k < self.learnt.len() {
            let v = self.learnt[k].var;
            if v < self.seen.len() {
                self.seen[v] = false;
            }
            k += 1;
        }
    }

    /// Removes from `learnt` the literals after the first that are `redundant`, and clears the
    /// marks of their variables.
    fn minimize(&mut self, f: &Formula, learned: &Vec<Clause>) {
        let i = self.compact(f, learned);
        self.unmark_from(i);
        self.learnt.truncate(i);
    }

    /// The number of decision levels of the literals of `learnt`.
    fn learnt_lbd(&mut self) -> usize {
        if self.tick < NONE {
            self.tick += 1;
        }
        let mut n: usize = 0;
        let mut j: usize = 0;
        while j < self.learnt.len() {
            let v = self.learnt[j].var;
            if v < self.level.len() {
                let lv = self.level[v];
                if lv < self.stamp.len() && self.stamp[lv] != self.tick {
                    self.stamp[lv] = self.tick;
                    if n < NONE {
                        n += 1;
                    }
                }
            }
            j += 1;
        }
        n
    }

    /// Sets `hist` to the histogram of the literal block distances of the live learned clauses
    /// (below the length of `stamp`); their number.
    fn count_live(&mut self) -> usize {
        let size = self.stamp.len();
        self.hist = vec![0; size];
        let mut live: usize = 0;
        let mut i: usize = 0;
        while i < self.lbd.len() && i < self.dead.len() {
            let d = self.lbd[i];
            if !self.dead[i] && d < self.hist.len() && self.hist[d] < NONE && live < NONE {
                self.hist[d] += 1;
                live += 1;
            }
            i += 1;
        }
        live
    }

    /// The cut of `reduce` from the histogram `hist` of `live` clauses: the clauses of a distance
    /// above `t`, with `left` of those of the distance `t`, are about half of them; `t` is at
    /// least 3.
    fn cut(&self, live: usize) -> Cut {
        let mut left = live / 2;
        let mut t = self.hist.len();
        while t > 3 && t - 1 < self.hist.len() && self.hist[t - 1] <= left {
            left -= self.hist[t - 1];
            t -= 1;
        }
        if t > 3 {
            return Cut { t: t - 1, left: left };
        }
        Cut { t: t, left: 0 }
    }

    /// Marks dead every live learned clause of a distance above `t`, and the first `left` of the
    /// distance `t`; the clause database starts the learned clauses at `m`.
    fn kill(&mut self, m: usize, t: usize, left: usize) {
        let mut left = left;
        let mut i: usize = 0;
        while i < self.lbd.len() && i < self.dead.len() {
            let d = self.lbd[i];
            if !self.dead[i] && d >= t {
                if d > t {
                    self.dead[i] = true;
                    self.unwatch(m, i);
                } else if left > 0 {
                    self.dead[i] = true;
                    left -= 1;
                    self.unwatch(m, i);
                }
            }
            i += 1;
        }
    }

    /// Sets both watched keys of learned clause `i` (clause `m + i`) to `NONE`, so that
    /// the clause is dropped from the watch lists when they are visited.
    fn unwatch(&mut self, m: usize, i: usize) {
        if m < BIG && i < BIG {
            let c = m + i;
            if c < self.start.len() && self.start[c] < BIG && self.start[c] + 5 < self.arena.len() {
                let o = self.start[c];
                self.arena[o + 4] = NONE;
                self.arena[o + 5] = NONE;
            }
        }
    }

    /// Marks about half of the live learned clauses dead: those of the highest literal block
    /// distances, the oldest first among equal ones; clauses of distance 2 or less stay.
    fn reduce(&mut self, m: usize) {
        let live = self.count_live();
        let c = self.cut(live);
        self.kill(m, c.t, c.left);
    }

    /// A copy of `learnt`, of at most `BIG` literals.
    fn copy_learnt(&self) -> Vec<Lit> {
        let mut out: Vec<Lit> = Vec::new();
        let mut i: usize = 0;
        while i < self.learnt.len() && i < BIG {
            out.push(Lit { var: self.learnt[i].var, value: self.learnt[i].value });
            i += 1;
        }
        out
    }

    /// First-UIP conflict analysis of the false clause `confl` at a decision level above 0: the
    /// learned clause, its asserting literal first and a literal of the backjump level second;
    /// empty if the analysis fails.
    fn analyze(&mut self, f: &Formula, learned: &Vec<Clause>, confl: usize) -> Vec<Lit> {
        let cur = self.lim.len();
        self.learnt.clear();
        self.learnt.push(Lit { var: NONE, value: false });
        let mut counter: usize = 0;
        let mut p = NONE;
        let mut idx = self.trail.len();
        let mut c = confl;
        loop {
            let added = self.analyze_clause(f, learned, c, p, cur);
            if added > NONE - counter {
                return Vec::new();
            }
            counter += added;
            let i = self.prev_seen(idx);
            if i >= self.trail.len() || counter == 0 {
                return Vec::new();
            }
            idx = i;
            p = self.trail[i];
            if p >= self.seen.len() || p >= self.reason.len() || p >= self.assign.len() {
                return Vec::new();
            }
            self.seen[p] = false;
            counter -= 1;
            if counter == 0 {
                break;
            }
            c = self.reason[p];
        }
        if counter != 0 || p >= self.assign.len() || self.learnt.len() == 0 {
            return Vec::new();
        }
        self.learnt[0] = Lit { var: p, value: !self.assign[p] };
        if self.inc < BIG {
            self.inc += self.inc / 32 + 1;
        }
        self.minimize(f, learned);
        self.finish_learnt();
        self.copy_learnt()
    }

    /// Undoes every assignment above decision level `lvl`.
    fn backtrack(&mut self, lvl: usize) {
        if lvl < self.lim.len() {
            let stop = self.lim[lvl];
            while stop < self.trail.len() {
                let v = self.trail[self.trail.len() - 1];
                if v < self.set.len() && v < self.phase.len() && v < self.assign.len() && v < self.reason.len() {
                    self.set[v] = false;
                    self.phase[v] = self.assign[v];
                    self.reason[v] = NONE;
                    let k = key(v, !self.assign[v]);
                    if k < self.false_lit.len() {
                        self.false_lit[k] = false;
                    }
                }
                self.trail.pop();
            }
            self.lim.truncate(lvl);
            self.qhead = self.trail.len();
        }
    }

    /// The unassigned variable of the highest activity; `NONE` if every variable is assigned.
    fn pick(&self) -> usize {
        let mut best = NONE;
        let mut best_act: usize = 0;
        let mut v: usize = 0;
        while v < self.set.len() {
            if !self.set[v] && v < self.act.len() && (best == NONE || self.act[v] > best_act) {
                best = v;
                best_act = self.act[v];
            }
            v += 1;
        }
        best
    }
}

/// The list `xs` with its elements from position `i` on moved to position `j` on, and the
/// elements after them dropped.
fn close_gap(xs: Vec<usize>, i: usize, j: usize) -> Vec<usize> {
    let mut ys = xs;
    let mut i = i;
    let mut j = j;
    while i < ys.len() && j < i {
        ys[j] = ys[i];
        i += 1;
        j += 1;
    }
    if j < i {
        ys.truncate(j);
    }
    ys
}

/// The empty search state for `n` variables.
fn new_search(n: usize) -> Search {
    Search {
        assign: vec![false; n],
        set: vec![false; n],
        false_lit: vec![false; 2 * n],
        level: vec![0; n],
        reason: vec![NONE; n],
        trail: Vec::new(),
        lim: Vec::new(),
        qhead: 0,
        watches: vec![Vec::new(); 2 * n],
        arena: Vec::new(),
        start: Vec::new(),
        phase: vec![false; n],
        act: vec![0; n],
        inc: 1,
        seen: vec![false; n],
        learnt: Vec::new(),
        dead: Vec::new(),
        lbd: Vec::new(),
        stamp: vec![0; n + 1],
        tick: 0,
        hist: Vec::new(),
    }
}

/// Attaches every clause of the formula and assigns the literal of every unit clause; the index
/// of a clause that is empty or false, or `NONE`.
fn init(s: &mut Search, f: &Formula, learned: &Vec<Clause>) -> usize {
    let mut confl = NONE;
    let mut i: usize = 0;
    while i < f.clauses.len() {
        s.attach(f, learned, i);
        if confl == NONE {
            let len = f.clauses[i].0.len();
            if len == 0 {
                confl = i;
            } else if len == 1 {
                let l = lit_at(f, learned, i, 0);
                if s.lit_false(l.var, l.value) {
                    confl = i;
                } else if !s.lit_true(l.var, l.value) {
                    s.enqueue(l.var, l.value, i);
                }
            }
        }
        i += 1;
    }
    confl
}

/// Every literal of `learnt` has a variable below the length of `assign`, and is false under
/// `assign`.
fn all_false(learnt: &Vec<Lit>, assign: &Vec<bool>) -> bool {
    let mut i: usize = 0;
    while i < learnt.len() {
        if !(learnt[i].var < assign.len() && assign[learnt[i].var] != learnt[i].value) {
            return false;
        }
        i += 1;
    }
    i >= learnt.len()
}

/// Marks the variables of the literals of `learnt` in a list of `n` marks.
fn mark(learnt: &Vec<Lit>, n: usize) -> Vec<bool> {
    let mut forced = vec![false; n];
    let mut i: usize = 0;
    while i < learnt.len() {
        if learnt[i].var < forced.len() {
            forced[learnt[i].var] = true;
        }
        i += 1;
    }
    forced
}

/// Clause `c` exists, and each of its literals (other than `(v, b)` if `skip`) has a marked
/// variable and is false under `assign`.
fn reason_ok(
    f: &Formula,
    learned: &Vec<Clause>,
    c: usize,
    skip: bool,
    v: usize,
    b: bool,
    assign: &Vec<bool>,
    forced: &Vec<bool>,
) -> bool {
    if !clause_exists(f, learned, c) {
        return false;
    }
    let len = clause_len(f, learned, c);
    let mut j: usize = 0;
    while j < len {
        let l = lit_at(f, learned, c, j);
        if !(skip && l.var == v && l.value == b)
            && !(l.var < forced.len() && l.var < assign.len() && forced[l.var] && assign[l.var] != l.value)
        {
            return false;
        }
        j += 1;
    }
    j >= len
}

/// Marks, in trail order, every variable whose reason clause has all its other literals marked
/// and false.
fn force_trail(
    f: &Formula,
    learned: &Vec<Clause>,
    assign: &Vec<bool>,
    trail: &Vec<usize>,
    reason: &Vec<usize>,
    forced: Vec<bool>,
) -> Vec<bool> {
    let mut forced = forced;
    let mut j: usize = 0;
    while j < trail.len() {
        let v = trail[j];
        if v < forced.len() && v < assign.len() && v < reason.len() {
            if reason_ok(f, learned, reason[v], true, v, assign[v], assign, &forced) {
                forced[v] = true;
            }
        }
        j += 1;
    }
    forced
}

/// The clause `learnt` follows from the formula and the clauses `learned`: its literals are false
/// under `assign`, and the reasons of the trail, from the negation of `learnt`, force the values
/// of `assign` that falsify clause `confl`. Every assignment that satisfies the clauses and
/// falsifies `learnt` agrees with `assign` on the marked variables, so it falsifies clause `confl`:
/// there is none.
fn certify(
    f: &Formula,
    learned: &Vec<Clause>,
    assign: &Vec<bool>,
    trail: &Vec<usize>,
    reason: &Vec<usize>,
    confl: usize,
    learnt: &Vec<Lit>,
) -> bool {
    if !all_false(learnt, assign) {
        return false;
    }
    let forced = force_trail(f, learned, assign, trail, reason, mark(learnt, assign.len()));
    reason_ok(f, learned, confl, false, 0, false, assign, &forced)
}

/// The values of the variables below `n` in `assign` (`false` where `assign` has none).
fn model(assign: &Vec<bool>, n: usize) -> Vec<bool> {
    let mut m = vec![false; n];
    let mut v: usize = 0;
    while v < n {
        if v < assign.len() {
            m[v] = assign[v];
        }
        v += 1;
    }
    m
}

/// Some literal of `c` is satisfied by `a`.
fn clause_holds(c: &Clause, a: &Vec<bool>) -> bool {
    let mut j: usize = 0;
    while j < c.0.len() {
        if c.0[j].var < a.len() && a[c.0[j].var] == c.0[j].value {
            return true;
        }
        j += 1;
    }
    false
}

/// Every clause of `f` has a literal that `a` satisfies.
fn satisfies(f: &Formula, a: &Vec<bool>) -> bool {
    let mut i: usize = 0;
    while i < f.clauses.len() {
        if !clause_holds(&f.clauses[i], a) {
            return false;
        }
        i += 1;
    }
    i >= f.clauses.len()
}

/// Handles the false clause `confl`: learns a certified clause and asserts its first literal
/// after backjumping (0); or, at decision level 0, certifies the empty clause: the formula is
/// unsatisfiable (1); or gives up (2).
fn on_conflict(s: &mut Search, f: &Formula, learned: &mut Vec<Clause>, confl: usize) -> usize {
    if s.lim.len() == 0 {
        let empty: Vec<Lit> = Vec::new();
        if certify(f, learned, &s.assign, &s.trail, &s.reason, confl, &empty) {
            return 1;
        }
        return 2;
    }
    let learnt = s.analyze(f, learned, confl);
    if learnt.len() == 0
        || learned.len() >= BIG
        || !certify(f, learned, &s.assign, &s.trail, &s.reason, confl, &learnt)
    {
        return 2;
    }
    let v = learnt[0].var;
    let b = learnt[0].value;
    let bj = if learnt.len() > 1 && learnt[1].var < s.level.len() { s.level[learnt[1].var] } else { 0 };
    let lbd = s.learnt_lbd();
    s.backtrack(bj);
    let c = f.clauses.len() + learned.len();
    learned.push(Clause(learnt));
    s.lbd.push(lbd);
    s.dead.push(false);
    s.attach(f, learned, c);
    s.enqueue(v, b, c);
    0
}

/// The CDCL search; `None` when it gives up. Public so that tests can call it without the
/// fallback.
pub fn cdcl(f: &Formula) -> Option<Answer> {
    let n = f.num_vars;
    if n >= BIG || f.clauses.len() >= BIG {
        return None;
    }
    let mut s = new_search(n);
    let mut learned: Vec<Clause> = Vec::new();
    let mut confl = init(&mut s, f, &learned);
    let mut conflicts: usize = 0;
    let mut restart_at: usize = 100;
    let mut since_reduce: usize = 0;
    let mut reduce_at: usize = 1000;
    let mut steps: usize = 0;
    while steps < NONE {
        steps += 1;
        if confl == NONE {
            confl = s.propagate();
        }
        if confl != NONE {
            let r = on_conflict(&mut s, f, &mut learned, confl);
            if r == 1 {
                return Some(Answer::Unsat);
            }
            if r == 2 {
                return None;
            }
            confl = NONE;
            if since_reduce < reduce_at {
                since_reduce += 1;
            }
            if since_reduce >= reduce_at {
                since_reduce = 0;
                if reduce_at < BIG {
                    reduce_at += 500;
                }
                s.reduce(f.clauses.len());
            }
            if conflicts < restart_at {
                conflicts += 1;
            }
            if conflicts >= restart_at {
                conflicts = 0;
                if restart_at < BIG {
                    restart_at += restart_at / 2;
                }
                s.backtrack(0);
            }
        } else {
            let v = s.pick();
            if v == NONE {
                let m = model(&s.assign, n);
                if satisfies(f, &m) {
                    return Some(Answer::Sat(Assignments(m)));
                }
                return None;
            }
            s.lim.push(s.trail.len());
            let b = if v < s.phase.len() { s.phase[v] } else { false };
            s.enqueue(v, b, NONE);
        }
    }
    None
}

/// The solver: CDCL, and the verified DPLL `solve` if CDCL gives up.
pub fn solver(f: &Formula) -> Answer {
    match cdcl(f) {
        Some(a) => a,
        None => solve(f, Pasn { assign: Assignments(vec![false; f.num_vars]), set: vec![false; f.num_vars] }),
    }
}
