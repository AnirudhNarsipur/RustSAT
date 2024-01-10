use crate::ds::*;
use crate::parse::parse_cnf;

pub mod ds;
pub mod parse;

#[derive(Debug)]
pub enum CNFStatus {
    SAT { model: Vec<i32> },
    UNSAT,
}

fn solver(mut solver_state: SolverState) -> CNFStatus {
    let mut conflict_unit: Option<ConflictAnalysisResult> = None;

    while solver_state.assigments_len() < solver_state.num_variables {
        let dec: Decision = {
            if let Some(ConflictAnalysisResult::Backtrack {
                level: _,
                unit_lit,
                unit_idx: Some(idx),
            }) = conflict_unit
            {
                let nd = Decision::make_new(unit_lit, Some(idx));
                conflict_unit = None;
                nd
            } else {
                Decision::make_new(solver_state.pick_var(), None)
            }
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
                        unit_lit: _,
                        unit_idx: _,
                    } => {
                        print!("Backtracking!");
                        let nc = &solver_state.clauses[solver_state.clauses.len() - 1];
                        let mut cnt = 0;
                        for lit in nc.literals.iter() {
                            if solver_state.assig.contains_key(&lit.var) {
                                cnt += 1;
                            }
                        }
                        println!("Before backtracking cnt: {} and lit count {}", cnt, nc.literals.len() );
                        assert_eq!(cnt, nc.literals.len());
                        solver_state.backtrack_to_level(level,&nc.literals.clone());
                        conflict_unit = Some(conflict_res);

                        let nc = &solver_state.clauses[solver_state.clauses.len() - 1];
                        let mut cnt = 0;
                        for lit in nc.literals.iter() {
                            if solver_state.assig.contains_key(&lit.var) {
                                cnt += 1;
                            }
                        }
                        println!("Checking after");
                        assert_eq!(cnt, nc.literals.len() - 1);
                        continue;
                    }
                }
            }
        }
    }
    CNFStatus::SAT {
        model: solver_state.get_model(),
    }
}

pub fn print_result(res: CNFStatus) {
    match res {
        CNFStatus::SAT { model } => {
            println!("s SATISFIABLE");
            print!("v ");
            for lit in model.iter() {
                print!("{} ", lit);
            }
            println!("0");
        }
        CNFStatus::UNSAT => println!("s UNSATISFIABLE"),
    }
}
fn main() {
    // let args: Vec<String> = env::args().collect();

    // let formula_file = args[0].clone();
    let formula_file = "../input/C1597_024.cnf";
    let mut solver_state = parse_cnf(formula_file).unwrap();
    solver_state.preprocess();
    let res = solver(solver_state);
    print_result(res);
}
