//! Test cases shared by `solve.rs` and `dpll.rs`, run against a solver given as a function: edge
//! cases and random small formulas, whose answers are compared with an independent brute-force
//! evaluation. Every model returned is checked against the formula. `solver_tests!(f)` makes a
//! test of each case for the solver `f`.

#![allow(dead_code)]

use sat::{Answer, Clause, Formula, Lit};

/// A solver under test.
pub type Solver = fn(&Formula) -> Answer;

#[macro_export]
macro_rules! solver_tests {
    ($s:expr) => {
        $crate::solver_tests!(@ $s; empty_formula, empty_clause, single_literal, pigeonhole_3_2, random_against_brute_force, repeated_and_complementary_literals, empty_clause_with_units, unit_chains, conflict_by_propagation, repeated_literals_in_unit_position, unused_variables, random_propagation_heavy);
    };
    (@ $s:expr; $($name:ident),*) => {
        $(
            #[test]
            fn $name() {
                common::$name($s)
            }
        )*
    };
}

/// The solver's answer as a Boolean; every `Sat` model is checked independently: it gives a value to
/// each variable and satisfies every clause.
pub fn decide(solve: Solver, f: &Formula) -> bool {
    match solve(f) {
        Answer::Sat(a) => {
            assert_eq!(a.0.len(), f.num_vars, "the model does not give a value to each variable");
            assert!(
                f.clauses.iter().all(|c| c.0.iter().any(|l| a.0[l.var] == l.value)),
                "the model does not satisfy the formula"
            );
            true
        }
        Answer::Unsat => false,
    }
}

pub fn lit(x: i64) -> Lit {
    Lit { var: (x.unsigned_abs() - 1) as usize, value: x > 0 }
}

pub fn formula(num_vars: usize, cs: &[&[i64]]) -> Formula {
    Formula { clauses: cs.iter().map(|c| Clause(c.iter().map(|&x| lit(x)).collect())).collect(), num_vars }
}

/// Satisfiability by enumerating all assignments, independent of the solver.
pub fn brute(num_vars: usize, cs: &[Vec<i64>]) -> bool {
    (0u64..1 << num_vars).any(|bits| {
        cs.iter().all(|c| c.iter().any(|&x| ((bits >> (x.unsigned_abs() - 1)) & 1 == 1) == (x > 0)))
    })
}

pub fn empty_formula(solve: Solver) {
    assert!(decide(solve, &formula(0, &[])));
    assert!(decide(solve, &formula(3, &[])));
}

pub fn empty_clause(solve: Solver) {
    assert!(!decide(solve, &formula(0, &[&[]])));
    assert!(!decide(solve, &formula(2, &[&[1, 2], &[]])));
}

pub fn single_literal(solve: Solver) {
    assert!(decide(solve, &formula(1, &[&[1]])));
    assert!(decide(solve, &formula(1, &[&[-1]])));
    assert!(!decide(solve, &formula(1, &[&[1], &[-1]])));
}

/// Three pigeons in two holes: variable 2p+h+1 says pigeon p sits in hole h.
pub fn pigeonhole_3_2(solve: Solver) {
    let mut cs: Vec<Vec<i64>> = (0..3).map(|p| vec![2 * p + 1, 2 * p + 2]).collect();
    for h in 0..2 {
        for p in 0..3 {
            for q in p + 1..3 {
                cs.push(vec![-(2 * p + h + 1), -(2 * q + h + 1)]);
            }
        }
    }
    let refs: Vec<&[i64]> = cs.iter().map(|c| c.as_slice()).collect();
    assert!(!decide(solve, &formula(6, &refs)));
}

/// Random 3-CNF formulas around the satisfiability threshold, from a fixed-seed generator.
pub fn random_against_brute_force(solve: Solver) {
    let mut s: u64 = 0x2545_f491_4f6c_dd1d;
    let mut next = |m: u64| {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s % m
    };
    let (mut nsat, mut nunsat) = (0, 0);
    for _ in 0..300 {
        let n = 1 + next(10) as usize;
        let m = next(5 * n as u64 + 1) as usize;
        let cs: Vec<Vec<i64>> = (0..m)
            .map(|_| {
                (0..1 + next(3))
                    .map(|_| {
                        let v = 1 + next(n as u64) as i64;
                        if next(2) == 0 { v } else { -v }
                    })
                    .collect()
            })
            .collect();
        let refs: Vec<&[i64]> = cs.iter().map(|c| c.as_slice()).collect();
        let expected = brute(n, &cs);
        assert_eq!(decide(solve, &formula(n, &refs)), expected, "n={n} clauses={cs:?}");
        if expected { nsat += 1 } else { nunsat += 1 }
    }
    assert!(nsat > 30 && nunsat > 30, "{nsat} sat, {nunsat} unsat");
}

/// A repeated literal (`1 1`) means the same as the single literal; a complementary pair
/// (`1 -1`) makes a tautology, true under every assignment.
pub fn repeated_and_complementary_literals(solve: Solver) {
    // Repeated literals, alone and with other clauses.
    assert!(decide(solve, &formula(1, &[&[1, 1]])));
    assert!(decide(solve, &formula(1, &[&[-1, -1, -1]])));
    assert!(decide(solve, &formula(2, &[&[1, 1], &[-1, 2, 2]])));
    assert!(!decide(solve, &formula(1, &[&[1, 1], &[-1, -1]])));
    assert!(!decide(solve, &formula(2, &[&[1, 1], &[-1, 2], &[-2, -2]])));
    // Tautologies, alone and with other clauses: they never change the answer.
    assert!(decide(solve, &formula(1, &[&[1, -1]])));
    assert!(decide(solve, &formula(2, &[&[1, -1], &[2, -2]])));
    assert!(decide(solve, &formula(3, &[&[-2, 1, 3, 2]])));
    assert!(decide(solve, &formula(2, &[&[1, -1], &[-1, 2]])));
    assert!(!decide(solve, &formula(1, &[&[1, -1], &[1], &[-1]])));
    assert!(!decide(solve, &formula(2, &[&[2, -2], &[1, -1], &[]])));
    // Both together.
    assert!(decide(solve, &formula(2, &[&[1, 1, -1], &[2, 2]])));
    assert!(decide(solve, &formula(2, &[&[1, -1, 1, -1], &[-2, -2, 1]])));
    assert!(!decide(solve, &formula(2, &[&[1, 1, -1], &[2, 2], &[-2, -2]])));
    assert!(!decide(solve, &formula(2, &[&[1, -1, -1], &[1, 1], &[-1, 2], &[-2, -2, -1]])));
}

/// Empty clauses next to unit clauses and clauses that propagation would make unit.
pub fn empty_clause_with_units(solve: Solver) {
    assert!(!decide(solve, &formula(1, &[&[1], &[]])));
    assert!(!decide(solve, &formula(2, &[&[1], &[-1, 2], &[]])));
    assert!(!decide(solve, &formula(2, &[&[], &[1], &[-1, 2]])));
}

/// The implications `x1 -> x2 -> ... -> xn`, in forward and reverse clause order, started by the
/// unit clause `x1` placed first or last: propagation must resume after the last unit clause and
/// restart from the first clause to reach every variable.
fn chain(n: i64, reverse: bool, unit_last: bool) -> Vec<Vec<i64>> {
    let mut cs: Vec<Vec<i64>> = (1..n).map(|i| vec![-i, i + 1]).collect();
    if reverse {
        cs.reverse();
    }
    if unit_last { cs.push(vec![1]) } else { cs.insert(0, vec![1]) }
    cs
}

fn decide_vec(solve: Solver, num_vars: usize, cs: &[Vec<i64>]) -> bool {
    let refs: Vec<&[i64]> = cs.iter().map(|c| c.as_slice()).collect();
    decide(solve, &formula(num_vars, &refs))
}

pub fn unit_chains(solve: Solver) {
    for reverse in [false, true] {
        for unit_last in [false, true] {
            for n in [2, 3, 10, 200] {
                let cs = chain(n, reverse, unit_last);
                assert!(decide_vec(solve, n as usize, &cs));
                // The chain forces every variable true; `-xn` makes it unsatisfiable.
                let mut neg = cs.clone();
                neg.push(vec![-n]);
                assert!(!decide_vec(solve, n as usize, &neg), "n={n} reverse={reverse} unit_last={unit_last}");
                neg.rotate_right(1);
                assert!(!decide_vec(solve, n as usize, &neg), "n={n} reverse={reverse} unit_last={unit_last}");
            }
        }
    }
}

/// Conflicts that only propagation finds: no clause is false before propagation, and both
/// branches on the first open clause fail by propagation alone.
pub fn conflict_by_propagation(solve: Solver) {
    assert!(!decide(solve, &formula(2, &[&[1], &[-1, 2], &[-1, -2]])));
    assert!(!decide(solve, &formula(2, &[&[-1, -2], &[-1, 2], &[1]])));
    assert!(!decide(solve, &formula(3, &[&[-2, 3], &[-3, -1], &[1], &[-1, 2]])));
    // Every assignment of `x1` propagates to a conflict.
    assert!(!decide(solve, &formula(3, &[&[1, 2], &[1, -2], &[-1, 3], &[-1, -3]])));
    assert!(!decide(solve, &formula(3, &[&[-1, 3], &[1, 2], &[-1, -3], &[1, -2]])));
}

/// A clause whose unassigned literals all have the same variable (`1 1`, `1 -1`) is not unit;
/// the solver must still find the forced value, or the tautology, by a decision.
pub fn repeated_literals_in_unit_position(solve: Solver) {
    assert!(!decide(solve, &formula(1, &[&[1, 1], &[-1]])));
    assert!(!decide(solve, &formula(1, &[&[-1], &[1, 1]])));
    assert!(!decide(solve, &formula(2, &[&[2], &[1, 1, -2], &[-1]])));
    assert!(decide(solve, &formula(2, &[&[2], &[1, -1, -2], &[-1]])));
    assert!(decide(solve, &formula(2, &[&[2], &[-2, 1, 1], &[-1, -1, 2]])));
    assert!(!decide(solve, &formula(2, &[&[2], &[-2, 1, 1], &[-1, -1, -2]])));
    assert!(decide(solve, &formula(3, &[&[1, -1], &[3, 3, -2], &[2], &[-1, 3]])));
}

/// Variables that no clause mentions still get a value in the model.
pub fn unused_variables(solve: Solver) {
    assert!(decide(solve, &formula(5, &[&[3]])));
    assert!(decide(solve, &formula(5, &[&[-5, 1], &[5]])));
    assert!(!decide(solve, &formula(5, &[&[2], &[-2]])));
}

/// Random formulas with many unit and binary clauses, so that most of the work is propagation,
/// compared with brute force.
pub fn random_propagation_heavy(solve: Solver) {
    let mut s: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = |m: u64| {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s % m
    };
    let (mut nsat, mut nunsat) = (0, 0);
    for _ in 0..500 {
        let n = 1 + next(14) as usize;
        let m = next(3 * n as u64 + 1) as usize;
        let cs: Vec<Vec<i64>> = (0..m)
            .map(|_| {
                let len = [0, 1, 1, 2, 2, 2, 3, 4][next(8) as usize];
                (0..len)
                    .map(|_| {
                        let v = 1 + next(n as u64) as i64;
                        if next(2) == 0 { v } else { -v }
                    })
                    .collect()
            })
            .collect();
        let expected = brute(n, &cs);
        assert_eq!(decide_vec(solve, n, &cs), expected, "n={n} clauses={cs:?}");
        if expected { nsat += 1 } else { nunsat += 1 }
    }
    assert!(nsat > 50 && nunsat > 50, "{nsat} sat, {nunsat} unsat");
}
