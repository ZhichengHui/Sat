//! Tests of the verified solver `sat::solver` on formulas built directly: edge cases and random
//! small formulas, whose answers are compared with an independent brute-force evaluation. Every
//! model returned is checked against the formula.

use sat::{Answer, Clause, Formula, Lit, solver};

/// The solver's answer as a Boolean; every `Sat` model is checked independently: it gives a value to
/// each variable and satisfies every clause.
fn decide(f: &Formula) -> bool {
    match solver(f) {
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

fn lit(x: i64) -> Lit {
    Lit { var: (x.unsigned_abs() - 1) as usize, value: x > 0 }
}

fn formula(num_vars: usize, cs: &[&[i64]]) -> Formula {
    Formula { clauses: cs.iter().map(|c| Clause(c.iter().map(|&x| lit(x)).collect())).collect(), num_vars }
}

/// Satisfiability by enumerating all assignments, independent of the solver.
fn brute(num_vars: usize, cs: &[Vec<i64>]) -> bool {
    (0u64..1 << num_vars).any(|bits| {
        cs.iter().all(|c| c.iter().any(|&x| ((bits >> (x.unsigned_abs() - 1)) & 1 == 1) == (x > 0)))
    })
}

#[test]
fn empty_formula() {
    assert!(decide(&formula(0, &[])));
    assert!(decide(&formula(3, &[])));
}

#[test]
fn empty_clause() {
    assert!(!decide(&formula(0, &[&[]])));
    assert!(!decide(&formula(2, &[&[1, 2], &[]])));
}

#[test]
fn single_literal() {
    assert!(decide(&formula(1, &[&[1]])));
    assert!(decide(&formula(1, &[&[-1]])));
    assert!(!decide(&formula(1, &[&[1], &[-1]])));
}

/// Three pigeons in two holes: variable 2p+h+1 says pigeon p sits in hole h.
#[test]
fn pigeonhole_3_2() {
    let mut cs: Vec<Vec<i64>> = (0..3).map(|p| vec![2 * p + 1, 2 * p + 2]).collect();
    for h in 0..2 {
        for p in 0..3 {
            for q in p + 1..3 {
                cs.push(vec![-(2 * p + h + 1), -(2 * q + h + 1)]);
            }
        }
    }
    let refs: Vec<&[i64]> = cs.iter().map(|c| c.as_slice()).collect();
    assert!(!decide(&formula(6, &refs)));
}

/// Random 3-CNF formulas around the satisfiability threshold, from a fixed-seed generator.
#[test]
fn random_against_brute_force() {
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
        assert_eq!(decide(&formula(n, &refs)), expected, "n={n} clauses={cs:?}");
        if expected { nsat += 1 } else { nunsat += 1 }
    }
    assert!(nsat > 30 && nunsat > 30, "{nsat} sat, {nunsat} unsat");
}

/// A repeated literal (`1 1`) means the same as the single literal; a complementary pair
/// (`1 -1`) makes a tautology, true under every assignment.
#[test]
fn repeated_and_complementary_literals() {
    // Repeated literals, alone and with other clauses.
    assert!(decide(&formula(1, &[&[1, 1]])));
    assert!(decide(&formula(1, &[&[-1, -1, -1]])));
    assert!(decide(&formula(2, &[&[1, 1], &[-1, 2, 2]])));
    assert!(!decide(&formula(1, &[&[1, 1], &[-1, -1]])));
    assert!(!decide(&formula(2, &[&[1, 1], &[-1, 2], &[-2, -2]])));
    // Tautologies, alone and with other clauses: they never change the answer.
    assert!(decide(&formula(1, &[&[1, -1]])));
    assert!(decide(&formula(2, &[&[1, -1], &[2, -2]])));
    assert!(decide(&formula(3, &[&[-2, 1, 3, 2]])));
    assert!(decide(&formula(2, &[&[1, -1], &[-1, 2]])));
    assert!(!decide(&formula(1, &[&[1, -1], &[1], &[-1]])));
    assert!(!decide(&formula(2, &[&[2, -2], &[1, -1], &[]])));
    // Both together.
    assert!(decide(&formula(2, &[&[1, 1, -1], &[2, 2]])));
    assert!(decide(&formula(2, &[&[1, -1, 1, -1], &[-2, -2, 1]])));
    assert!(!decide(&formula(2, &[&[1, 1, -1], &[2, 2], &[-2, -2]])));
    assert!(!decide(&formula(2, &[&[1, -1, -1], &[1, 1], &[-1, 2], &[-2, -2, -1]])));
}
