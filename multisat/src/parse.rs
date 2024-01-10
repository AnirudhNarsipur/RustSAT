use crate::ds::*;
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::Path;

pub fn parse_cnf(filename: &str) -> io::Result<SolverState> {
    let file = File::open(Path::new(filename))?;
    let reader = BufReader::new(file);

    // let mut num_clauses: usize = 0;
    let mut solver_state: Option<SolverState> = None;

    for line in reader.lines() {
        let line = line?;
        let cleaned = line.trim().replace('\r', "");

        if cleaned.starts_with('c') || cleaned.is_empty() {
            // Ignore comments and empty lines
            continue;
        }

        if cleaned.starts_with("p cnf") {
            let parts: Vec<&str> = cleaned.split_whitespace().collect();
            let num_variables = parts[2].parse().unwrap();
            // num_clauses = parts[3].parse().unwrap();
            solver_state = Some(SolverState::make_new(num_variables));
        } else if let Some(state) = solver_state.as_mut() {
            state.add_raw_clause(cleaned.split_whitespace().collect());
        } else {
            // Error: clauses appear before header
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Invalid CNF format",
            ));
        }
    }
    solver_state.ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "No CNF header found"))
}

#[cfg(test)]
mod tests;