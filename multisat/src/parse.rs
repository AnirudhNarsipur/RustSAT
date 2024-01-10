use std::fs::File;
use std::io::{self, prelude::*};
use std::path::Path;
use crate::ds::*;

pub fn parse_cnf(filename: &str) -> io::Result<SolverState> {
    let path = Path::new(filename);
    let file = File::open(&path)?;
    let reader = io::BufReader::new(file);

    let mut num_clauses: usize = 0;
    let mut num_variables: usize = 0;
    let mut solver_state = SolverState::make_new(num_variables);

    for line in reader.lines() {
        let cleaned = (line?).replace("\r", "");
        if cleaned.starts_with("c") {
            continue;
        } else if cleaned.starts_with("p cnf") {
            let parts: Vec<&str> = cleaned.split_whitespace().collect();
            num_variables = parts[2].parse().unwrap();
            num_clauses = parts[3].parse().unwrap();
        } else if !cleaned.is_empty() {
            solver_state.add_raw_clause(cleaned.split_whitespace().collect()) ;  
        } else {
            break;
        }
    }
    
    return Ok(solver_state);
}
