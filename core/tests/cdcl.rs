//! Tests of the CDCL search `sat::cdcl` alone, without the fallback to the DPLL `solve` that
//! `sat::solver` adds: a bug that makes the search give up (`None`) is hidden by the fallback in
//! `solve.rs`, but fails here. Every answer is compared with an independent evaluation, and every
//! model is checked against the formula.

use sat::{Answer, Clause, Formula, Lit, cdcl};

fn lit(x: i64) -> Lit {
    Lit { var: (x.unsigned_abs() - 1) as usize, value: x > 0 }
}

fn formula(num_vars: usize, cs: &[Vec<i64>]) -> Formula {
    Formula { clauses: cs.iter().map(|c| Clause(c.iter().map(|&x| lit(x)).collect())).collect(), num_vars }
}

/// The answer of `cdcl` as a Boolean, `None` if it gives up; every `Sat` model is checked: it gives
/// a value to each variable and satisfies every clause.
fn try_cdcl(num_vars: usize, cs: &[Vec<i64>]) -> Option<bool> {
    let f = formula(num_vars, cs);
    match cdcl(&f)? {
        Answer::Sat(a) => {
            assert_eq!(a.0.len(), num_vars, "the model does not give a value to each variable");
            assert!(
                f.clauses.iter().all(|c| c.0.iter().any(|l| a.0[l.var] == l.value)),
                "the model does not satisfy the formula {cs:?}"
            );
            Some(true)
        }
        Answer::Unsat => Some(false),
    }
}

/// The answer of `cdcl`, which must not give up.
fn decide(num_vars: usize, cs: &[Vec<i64>]) -> bool {
    try_cdcl(num_vars, cs).unwrap_or_else(|| panic!("cdcl gave up on n={num_vars} clauses={cs:?}"))
}

/// Satisfiability by enumerating all assignments, independent of the solver.
fn brute(num_vars: usize, cs: &[Vec<i64>]) -> bool {
    (0u64..1 << num_vars).any(|bits| {
        cs.iter().all(|c| c.iter().any(|&x| ((bits >> (x.unsigned_abs() - 1)) & 1 == 1) == (x > 0)))
    })
}

/// `cdcl` answers, and agrees with brute force.
fn check(num_vars: usize, cs: &[Vec<i64>]) -> bool {
    let expected = brute(num_vars, cs);
    assert_eq!(decide(num_vars, cs), expected, "n={num_vars} clauses={cs:?}");
    expected
}

fn cls(cs: &[&[i64]]) -> Vec<Vec<i64>> {
    cs.iter().map(|c| c.to_vec()).collect()
}

/// A xorshift generator with a fixed seed; `next(m)` is below `m`.
fn rng(seed: u64) -> impl FnMut(u64) -> u64 {
    let mut s = seed;
    move |m| {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s % m
    }
}

#[test]
fn empty_formula() {
    assert!(check(0, &[]));
    assert!(check(3, &[]));
}

#[test]
fn empty_clause() {
    assert!(!check(0, &cls(&[&[]])));
    assert!(!check(2, &cls(&[&[1, 2], &[]])));
    assert!(!check(2, &cls(&[&[1], &[-1, 2], &[]])));
}

/// Conflicts at decision level 0: between unit clauses, or found by propagating them.
#[test]
fn unit_conflicts_at_level_0() {
    assert!(!check(1, &cls(&[&[1], &[-1]])));
    assert!(!check(1, &cls(&[&[1, 1], &[-1]])));
    assert!(!check(2, &cls(&[&[1], &[-1, 2], &[-2]])));
    assert!(!check(2, &cls(&[&[-1, -2], &[-1, 2], &[1]])));
    assert!(!check(3, &cls(&[&[-2, 3], &[-3, -1], &[1], &[-1, 2]])));
}

/// Conflicts above level 0 that need learned clauses: with every activity 0 the search decides
/// `x1`, `x2`, `x3`, `x4` false in this order. Deciding `x4` propagates `x5` into a conflict whose
/// learned clause `x1 x4` jumps back over levels 3 and 2 to level 1, where it asserts `x4`, which
/// in the unsatisfiable case conflicts again (learning `x1`); `x1` then conflicts at level 0.
#[test]
fn learned_clause_and_long_backjump() {
    let sat = cls(&[&[1, 4, 5], &[1, 4, -5], &[2, 3, -6], &[-2, 6]]);
    assert!(check(6, &sat));
    let mut unsat = sat.clone();
    unsat.extend(cls(&[&[1, -4, 7], &[1, -4, -7], &[-1, 8], &[-1, -8]]));
    assert!(!check(8, &unsat));
}

/// `p` pigeons in `h` holes: variable `h * i + j + 1` says pigeon `i` sits in hole `j`.
fn pigeons(p: i64, h: i64) -> Vec<Vec<i64>> {
    let mut cs: Vec<Vec<i64>> = (0..p).map(|i| (0..h).map(|j| h * i + j + 1).collect()).collect();
    for j in 0..h {
        for i in 0..p {
            for k in i + 1..p {
                cs.push(vec![-(h * i + j + 1), -(h * k + j + 1)]);
            }
        }
    }
    cs
}

/// The pigeon hole formulas: `n + 1` pigeons do not fit in `n` holes, `n` do.
#[test]
fn pigeon_hole() {
    for n in 3..=5 {
        assert!(!decide(((n + 1) * n) as usize, &pigeons(n + 1, n)), "{} pigeons, {n} holes", n + 1);
        assert!(decide((n * n) as usize, &pigeons(n, n)), "{n} pigeons, {n} holes");
    }
    assert!(!check(12, &pigeons(4, 3)));
}

/// The implications `x1 -> x2 -> ... -> xn` with the unit clause `x1`, alone and with `-xn`; and
/// the same chain without the unit clause, so that the search has to decide.
#[test]
fn implication_chain() {
    for n in [2, 10, 1000] {
        let mut cs: Vec<Vec<i64>> = (1..n).map(|i| vec![-i, i + 1]).collect();
        assert!(decide(n as usize, &cs));
        cs.push(vec![-n]);
        assert!(decide(n as usize, &cs));
        cs.push(vec![1]);
        assert!(!decide(n as usize, &cs));
        cs.pop();
        cs.pop();
        cs.insert(0, vec![1]);
        assert!(decide(n as usize, &cs));
    }
}

/// Random 3-CNF formulas near the satisfiability threshold (about 4.26 clauses per variable),
/// compared with brute force. `cdcl` must answer every one.
#[test]
fn random_3sat_near_threshold() {
    let mut next = rng(0x2545_f491_4f6c_dd1d);
    let (mut nsat, mut nunsat) = (0, 0);
    for _ in 0..400 {
        let n = 5 + next(10) as usize;
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
        if check(n, &cs) { nsat += 1 } else { nunsat += 1 }
    }
    assert!(nsat > 100 && nunsat > 100, "{nsat} sat, {nunsat} unsat");
}

/// Satisfiability by a plain DPLL with unit propagation over a list of values (0 unassigned,
/// 1 true, 2 false), independent of the solver, for formulas too large for brute force.
fn dpll(cs: &[Vec<i64>], val: &mut Vec<u8>) -> bool {
    let value = |val: &Vec<u8>, x: i64| match val[(x.unsigned_abs() - 1) as usize] {
        0 => None,
        v => Some((v == 1) == (x > 0)),
    };
    let mut trail = Vec::new();
    let result = loop {
        let mut open = None;
        let mut unit = None;
        let mut conflict = false;
        for c in cs {
            if c.iter().any(|&x| value(val, x) == Some(true)) {
                continue;
            }
            let free: Vec<i64> = c.iter().copied().filter(|&x| value(val, x).is_none()).collect();
            match free.len() {
                0 => conflict = true,
                1 => unit = Some(free[0]),
                _ => open = open.or(Some(free[0])),
            }
        }
        if conflict {
            break false;
        }
        let Some(x) = unit else {
            break match open {
                None => true,
                Some(x) => [x, -x].iter().any(|&y| {
                    val[(y.unsigned_abs() - 1) as usize] = if y > 0 { 1 } else { 2 };
                    let r = dpll(cs, val);
                    val[(y.unsigned_abs() - 1) as usize] = 0;
                    r
                }),
            };
        };
        val[(x.unsigned_abs() - 1) as usize] = if x > 0 { 1 } else { 2 };
        trail.push(x);
    };
    for x in trail {
        val[(x.unsigned_abs() - 1) as usize] = 0;
    }
    result
}

/// Larger random 3-CNF formulas at the threshold, too large for brute force: `cdcl` must answer,
/// and agree with `dpll`.
#[test]
fn random_3sat_larger() {
    let mut next = rng(0x9e37_79b9_7f4a_7c15);
    let (mut nsat, mut nunsat) = (0, 0);
    for _ in 0..100 {
        let n = 40 + next(21) as usize;
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
        let got = decide(n, &cs);
        let expected = dpll(&cs, &mut vec![0; n]);
        assert_eq!(got, expected, "n={n} clauses={cs:?}");
        if got { nsat += 1 } else { nunsat += 1 }
    }
    assert!(nsat > 20 && nunsat > 20, "{nsat} sat, {nunsat} unsat");
}
