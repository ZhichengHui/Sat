//! End-to-end tests of the command line `sat`: DIMACS text on standard input, the answer line
//! and the exit code (10 satisfiable, 20 unsatisfiable, 1 malformed input).

use std::io::Write;
use std::process::{Command, Stdio};

fn run(src: &str) -> (String, i32) {
    let mut child = Command::new(env!("CARGO_BIN_EXE_sat"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(src.as_bytes()).unwrap();
    let out = child.wait_with_output().unwrap();
    (String::from_utf8(out.stdout).unwrap().trim().to_string(), out.status.code().unwrap())
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
