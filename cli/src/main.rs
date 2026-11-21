//! The command line `sat`: reads a CNF formula in DIMACS format (from the file named by the only
//! argument, or from standard input), decides it with the verified `sat::solver`, and prints the
//! answer in the format of the SAT competition: `s SATISFIABLE` followed by `v` lines giving the
//! value of every variable as a DIMACS literal and ending with `0` (exit code 10), or
//! `s UNSATISFIABLE` (exit code 20). A malformed input is reported on standard error (exit code 1).
//!
//! This file is not verified. It builds a `Formula` that satisfies the precondition of the
//! contract: DIMACS variable `v` (from 1) is index `v - 1`, a positive literal has value `true`,
//! and the number of variables is that of the header, which every literal must respect.

use sat::{Answer, Clause, Formula, Lit};
use std::io::Read;
use std::process::ExitCode;

/// Parses DIMACS CNF text: comment lines (`c ...`), one header `p cnf VARS CLAUSES`, then the
/// clauses as integers, each clause ended by `0`. A `%` line ends the input (as in SATLIB files).
/// An empty clause (a `0` that ends no literal) read after the header's number of clauses is
/// ignored with a warning: the SATLIB pret files end with such a lone `0`. Within that number it
/// is an empty clause, and the formula is unsatisfiable.
fn parse(src: &str) -> Result<Formula, String> {
    let mut header: Option<(usize, usize)> = None;
    let mut clauses = Vec::new();
    let mut cur = Vec::new();
    let mut ignored = 0;
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
        let (n, m) = header.ok_or("clause before the header")?;
        for tok in t.split_whitespace() {
            let x: i64 = tok.parse().map_err(|_| format!("bad literal: {tok}"))?;
            if x == 0 {
                if cur.is_empty() && clauses.len() >= m {
                    ignored += 1;
                    continue;
                }
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
    if ignored > 0 {
        eprintln!("warning: ignored {ignored} empty clause(s) after the header's {m} clauses");
    }
    if !cur.is_empty() {
        clauses.push(Clause(cur));
    }
    if clauses.len() != m {
        eprintln!("warning: the header announces {m} clauses, the file has {}", clauses.len());
    }
    Ok(Formula { clauses, num_vars: n })
}

/// Prints the assignment as `v` lines: the literal of every variable (`i` if variable `i` is true,
/// `-i` if false), at most about 80 characters per line, the last line ending with `0`.
fn print_model(values: &[bool]) {
    let mut line = String::from("v");
    for (i, &b) in values.iter().enumerate() {
        let lit = if b { format!(" {}", i + 1) } else { format!(" -{}", i + 1) };
        if line.len() + lit.len() > 78 {
            println!("{line}");
            line = String::from("v");
        }
        line.push_str(&lit);
    }
    println!("{line} 0");
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
            match sat::solver(&f) {
                Answer::Sat(a) => {
                    println!("s SATISFIABLE");
                    print_model(&a.0);
                    ExitCode::from(10)
                }
                Answer::Unsat => {
                    println!("s UNSATISFIABLE");
                    ExitCode::from(20)
                }
            }
        }
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::from(1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lens(f: &Formula) -> Vec<usize> {
        f.clauses.iter().map(|c| c.0.len()).collect()
    }

    #[test]
    fn trailing_zero_after_the_count_is_ignored() {
        let f = parse("c pret\np cnf 3 2\n1 -2 0\n2 3 0\n0\n").unwrap();
        assert_eq!(f.num_vars, 3);
        assert_eq!(lens(&f), vec![2, 2]);
    }

    #[test]
    fn empty_clause_within_the_count_is_kept() {
        let f = parse("p cnf 2 3\n1 0\n0\n-2 0\n").unwrap();
        assert_eq!(lens(&f), vec![1, 0, 1]);
        let f = parse("p cnf 1 1\n0\n").unwrap();
        assert_eq!(lens(&f), vec![0]);
    }

    #[test]
    fn percent_line_ends_the_input() {
        let f = parse("p cnf 2 2\n1 2 0\n-1 0\n%\n0\n\n").unwrap();
        assert_eq!(lens(&f), vec![2, 1]);
        let f = parse("p cnf 2 1\n1 2 0\n%\n-1 0\n").unwrap();
        assert_eq!(lens(&f), vec![2]);
    }
}
