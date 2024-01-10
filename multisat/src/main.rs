use crate::ds::*;
use crate::parse::parse_cnf;
use std::env;
pub mod ds;
pub mod parse;

#[derive(Debug)]
enum CNFStatus {
    SAT,
    UNSAT,
}

fn solver(mut solver_state: SolverState) -> CNFStatus {
    let mut conflict_unit: Option<ConflictAnalysisResult> = None;

    while solver_state.decision_stack_size() < solver_state.num_variables {
        let dec: Decision = match conflict_unit {
            Some(ConflictAnalysisResult::Backtrack {
                level: _,
                unit_lit,
                unit_idx,
            }) => {
                let nd = Decision::make_new(unit_lit, Some(unit_idx));
                conflict_unit = None;
                nd
            }
            None => Decision::make_new(solver_state.pick_var(), None),
            _ => panic!("unreachable!"),
        };
        solver_state.add_unit_or_decision(&dec);
        match solver_state.unit_prop(&dec) {
            FormulaUnitProp::Ok => continue,
            FormulaUnitProp::Conflict { conflict_cause_idx } => {
                let conflict_res = solver_state.analyze_conflict(conflict_cause_idx);
                match conflict_res {
                    ConflictAnalysisResult::UNSAT => return CNFStatus::UNSAT,
                    ConflictAnalysisResult::Backtrack {
                        level,
                        unit_lit,
                        unit_idx,
                    } => {
                        solver_state.backtrack_to_level(level);
                        conflict_unit = Some(conflict_res);
                        continue;
                    }
                }
            }
        }
    }
    return CNFStatus::SAT;
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let formula_file = args[0].clone();
    let mut solver_state = parse_cnf(&formula_file).unwrap();
    solver_state.preprocess();
    let res = solver(solver_state);
    println!("Result is {:?} ", res);
}
