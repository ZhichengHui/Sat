//! End-to-end tests of the command line `sat`: DIMACS text on standard input, the answer line
//! and the exit code (10 satisfiable, 20 unsatisfiable, 1 malformed input). After `s SATISFIABLE`,
//! the `v` lines are checked independently: they give each variable exactly one value, end with
//! `0`, and satisfy every clause of the input.

use std::collections::HashMap;
use std::io::Write;
use std::process::{Command, Stdio};

/// Runs `sat` on `src`; returns the answer line (the first line of the output) and the exit code.
fn run(src: &str) -> (String, i32) {
    let mut child = Command::new(env!("CARGO_BIN_EXE_sat"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(src.as_bytes()).unwrap();
    let out = child.wait_with_output().unwrap();
    let stdout = String::from_utf8(out.stdout).unwrap();
    let lines: Vec<&str> = stdout.lines().collect();
    let answer = lines.first().copied().unwrap_or("").to_string();
    if answer == "s SATISFIABLE" {
        check_model(src, &lines[1..]);
    }
    (answer, out.status.code().unwrap())
}

/// The number of variables and the clauses of a DIMACS text (comments, header, clauses ended by
/// `0`, an optional `%` line ending the input).
fn clauses(src: &str) -> (usize, Vec<Vec<i64>>) {
    let mut n = 0;
    let mut cs = Vec::new();
    let mut cur = Vec::new();
    for line in src.lines().map(str::trim) {
        if line.starts_with('%') {
            break;
        }
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if line.starts_with('p') {
            n = line.split_whitespace().nth(2).unwrap().parse().unwrap();
            continue;
        }
        for x in line.split_whitespace().map(|t| t.parse::<i64>().unwrap()) {
            if x == 0 {
                cs.push(std::mem::take(&mut cur));
            } else {
                cur.push(x);
            }
        }
    }
    if !cur.is_empty() {
        cs.push(cur);
    }
    (n, cs)
}

fn check_model(src: &str, vlines: &[&str]) {
    let (n, cs) = clauses(src);
    let mut lits = Vec::new();
    for l in vlines {
        let mut toks = l.split_whitespace();
        assert_eq!(toks.next(), Some("v"), "not a v line: {l}");
        lits.extend(toks.map(|t| t.parse::<i64>().unwrap()));
    }
    assert_eq!(lits.pop(), Some(0), "the v lines do not end with 0");
    let mut value = HashMap::new();
    for x in lits {
        assert!(x != 0 && x.unsigned_abs() as usize <= n, "bad literal {x}");
        assert!(value.insert(x.unsigned_abs(), x > 0).is_none(), "variable {} twice", x.abs());
    }
    assert_eq!(value.len(), n, "not every variable has a value");
    for c in &cs {
        assert!(c.iter().any(|&x| value[&x.unsigned_abs()] == (x > 0)), "clause {c:?} is false");
    }
}

#[test]
fn satisfiable() {
    assert_eq!(run("c example\np cnf 3 2\n1 -3 0\n2 3 -1 0\n"), ("s SATISFIABLE".into(), 10));
}

#[test]
fn unsatisfiable() {
    assert_eq!(run("p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"), ("s UNSATISFIABLE".into(), 20));
}

#[test]
fn empty_formula() {
    assert_eq!(run("p cnf 0 0\n"), ("s SATISFIABLE".into(), 10));
}

#[test]
fn empty_clause() {
    assert_eq!(run("p cnf 1 1\n0\n"), ("s UNSATISFIABLE".into(), 20));
}

/// Clauses may span lines; a `%` line ends the input (SATLIB files).
#[test]
fn layout() {
    assert_eq!(run("p cnf 2 2\n1\n2 0 -1\n0\n%\n0\n"), ("s SATISFIABLE".into(), 10));
}

#[test]
fn malformed() {
    assert_eq!(run("1 2 0\n").1, 1);
    assert_eq!(run("p cnf 1 1\n2 0\n").1, 1);
    assert_eq!(run("p cnf 1 1\nx 0\n").1, 1);
}

/// A model on several `v` lines (more variables than fit on one line). The solver tries `true`
/// first, so a formula satisfied by all-true is answered at the first leaf of its search.
#[test]
fn long_model() {
    let n: i64 = 40;
    let mut src = format!("p cnf {n} {n}\n");
    for i in 1..=n {
        src.push_str(&format!("{i} -{} 0\n", i % n + 1));
    }
    assert_eq!(run(&src), ("s SATISFIABLE".into(), 10));
}
