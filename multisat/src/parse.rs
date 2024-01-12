use crate::ds::*;
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::Path;


pub fn parse_cnf(filename: &str) -> io::Result<ParsedOut> {
    let file = File::open(Path::new(filename))?;
    let reader = BufReader::new(file);

    let mut num_clauses: usize = 0;
    let mut num_variables: usize = 0;
    let mut clause_vec: Vec<Vec<Literal>> = Vec::new();

    for line in reader.lines() {
        let line = line?;
        let cleaned = line.trim().replace('\r', "");

        if cleaned.starts_with('c') || cleaned.is_empty() {
            // Ignore comments and empty lines
            continue;
        }
        if cleaned.starts_with("p cnf") {
            let parts: Vec<&str> = cleaned.split_whitespace().collect();
            num_variables = parts[2].parse().unwrap();
            num_clauses = parts[3].parse().unwrap();
        } else if num_clauses != 0 {
            let lit_vec = cleaned
                .split_whitespace()
                .map(|s| s.parse::<i32>().unwrap())
                .take_while(|&n| n != 0)
                .map(Literal::from)
                .collect();
            clause_vec.push(lit_vec);
        } else {
            // Error: clauses appear before header
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Invalid CNF format",
            ));
        }
    }
    if num_variables == 0 {
        Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "No CNF header found",
        ))
    } else {
        assert!(num_clauses == clause_vec.len());
        Ok(ParsedOut {
            num_variables,
            num_clauses,
            clauses: clause_vec,
        })
    }
}

#[cfg(test)]
mod tests;
