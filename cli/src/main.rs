//! The command line `sat`: reads a CNF formula in DIMACS format (from the file named by the only
//! argument, or from standard input), decides it with the verified `sat::solver`, and prints the
//! answer in the format of the SAT competition: `s SATISFIABLE` (exit code 10) or
//! `s UNSATISFIABLE` (exit code 20). A malformed input is reported on standard error (exit code 1).
//!
//! This file is not verified. It builds a `Formula` that satisfies the precondition of the
//! contract: DIMACS variable `v` (from 1) is index `v - 1`, a positive literal has value `true`,
//! and the number of variables is that of the header, which every literal must respect.

use sat::{Clause, Formula, Lit};
use std::io::Read;
use std::process::ExitCode;

/// Parses DIMACS CNF text: comment lines (`c ...`), one header `p cnf VARS CLAUSES`, then the
/// clauses as integers, each clause ended by `0`. A `%` line ends the input (as in SATLIB files).
fn parse(src: &str) -> Result<Formula, String> {
    let mut header: Option<(usize, usize)> = None;
    let mut clauses = Vec::new();
    let mut cur = Vec::new();
    for line in src.lines() {
        let t = line.trim();
        if t.starts_with('%') {
            break;
        }
        if t.is_empty() || t.starts_with('c') {
            continue;
        }
        if t.starts_with('p') {
            if header.is_some() {
                return Err("second header line".into());
            }
            let w: Vec<&str> = t.split_whitespace().collect();
            if w.len() != 4 || w[1] != "cnf" {
                return Err(format!("bad header: {t}"));
            }
            let n = w[2].parse().map_err(|_| format!("bad header: {t}"))?;
            let m = w[3].parse().map_err(|_| format!("bad header: {t}"))?;
            header = Some((n, m));
            continue;
        }
        let (n, _) = header.ok_or("clause before the header")?;
        for tok in t.split_whitespace() {
            let x: i64 = tok.parse().map_err(|_| format!("bad literal: {tok}"))?;
            if x == 0 {
                clauses.push(Clause(std::mem::take(&mut cur)));
                continue;
            }
            let v = x.unsigned_abs();
            if v > n as u64 {
                return Err(format!("variable {v} exceeds the header's {n}"));
            }
            cur.push(Lit { var: (v - 1) as usize, value: x > 0 });
        }
    }
    let (n, m) = header.ok_or("no header line")?;
    if !cur.is_empty() {
        clauses.push(Clause(cur));
    }
    if clauses.len() != m {
        eprintln!("warning: the header announces {m} clauses, the file has {}", clauses.len());
    }
    Ok(Formula { clauses, num_vars: n })
}

fn main() -> ExitCode {
    let mut src = String::new();
    let read = match std::env::args().nth(1) {
        Some(path) => std::fs::read_to_string(&path).map(|s| src = s),
        None => std::io::stdin().read_to_string(&mut src).map(|_| ()),
    };
    if let Err(e) = read {
        eprintln!("error: {e}");
        return ExitCode::from(1);
    }
    match parse(&src) {
        Ok(f) => {
            if sat::solver(&f) {
                println!("s SATISFIABLE");
                ExitCode::from(10)
            } else {
                println!("s UNSATISFIABLE");
                ExitCode::from(20)
            }
        }
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::from(1)
        }
    }
}
