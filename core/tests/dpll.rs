//! Tests of the verified DPLL `sat::dpll`, the fallback of `sat::solver`, which `solve.rs` does not
//! reach because `cdcl` always answers there: the cases of `common/mod.rs`, and the agreement of
//! `solver`, `dpll` and `cdcl` on random formulas.

mod common;

use common::{decide, formula};
use sat::{Answer, cdcl, dpll, solver};

solver_tests!(dpll);

/// Random 3-CNF formulas near the satisfiability threshold, too large for brute force: `solver`
/// and `dpll` give the answer of `cdcl` (every model checked against the formula).
#[test]
fn agrees_with_cdcl() {
    let mut s: u64 = 0x5851_f42d_4c95_7f2d;
    let mut next = |m: u64| {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s % m
    };
    let (mut nsat, mut nunsat) = (0, 0);
    for _ in 0..200 {
        let n = 15 + next(16) as usize;
        let m = (n * 426 + 50) / 100;
        let cs: Vec<Vec<i64>> = (0..m)
            .map(|_| {
                (0..3)
                    .map(|_| {
                        let v = 1 + next(n as u64) as i64;
                        if next(2) == 0 { v } else { -v }
                    })
                    .collect()
            })
            .collect();
        let refs: Vec<&[i64]> = cs.iter().map(|c| c.as_slice()).collect();
        let f = formula(n, &refs);
        let Some(a) = cdcl(&f) else { continue };
        let expected = matches!(a, Answer::Sat(_));
        assert_eq!(decide(dpll, &f), expected, "dpll: n={n} clauses={cs:?}");
        assert_eq!(decide(solver, &f), expected, "solver: n={n} clauses={cs:?}");
        if expected { nsat += 1 } else { nunsat += 1 }
    }
    assert!(nsat > 40 && nunsat > 40, "{nsat} sat, {nunsat} unsat");
}
