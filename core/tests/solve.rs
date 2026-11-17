//! Tests of the verified solver `sat::solver` on formulas built directly: edge cases and random
//! small formulas, whose answers are compared with an independent brute-force evaluation.

use sat::{Clause, Formula, Lit, solver};

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
    assert!(solver(&formula(0, &[])));
    assert!(solver(&formula(3, &[])));
}

#[test]
fn empty_clause() {
    assert!(!solver(&formula(0, &[&[]])));
    assert!(!solver(&formula(2, &[&[1, 2], &[]])));
}

#[test]
fn single_literal() {
    assert!(solver(&formula(1, &[&[1]])));
    assert!(solver(&formula(1, &[&[-1]])));
    assert!(!solver(&formula(1, &[&[1], &[-1]])));
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
    assert!(!solver(&formula(6, &refs)));
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
        assert_eq!(solver(&formula(n, &refs)), expected, "n={n} clauses={cs:?}");
        if expected { nsat += 1 } else { nunsat += 1 }
    }
    assert!(nsat > 30 && nunsat > 30, "{nsat} sat, {nunsat} unsat");
}
