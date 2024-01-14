use rustc_hash::FxHashMap;

use crate::ds::*;
use crate::parse::*;
use std::env;
use std::path::Path;
use std::process::exit;

pub mod ds;
pub mod parse;

#[derive(Debug, PartialEq)]
pub enum CNFStatus {
    SAT { model: Vec<i32> },
    UNSAT,
}
fn unit_prop_sat(solver_state: &mut SolverState, recent_dec: &Decision) -> bool {
    let mut cur_dec = recent_dec.clone();
    loop {
        // println!("UP {:?} level: {}", cur_dec,solver_state.level);
        match solver_state.unit_prop(&cur_dec) {
            FormulaUnitProp::Ok => {
                return true;
            }
            FormulaUnitProp::Conflict { conflict_cause_idx } => {
                let conflict_res = solver_state.analyze_conflict_backtrack(conflict_cause_idx);
                match conflict_res {
                    ConflictAnalysisResult::UNSAT => return false,
                    ConflictAnalysisResult::Backtrack { decision } => {
                        // println!("CONFLICT");
                        cur_dec = decision;
                    }
                }
            }
        }
    }
}

fn solver(solver_state: &mut SolverState) -> CNFStatus {
    println!(
        "Have {} vars {} clauses",
        solver_state.num_variables,
        solver_state.clauses.len()
    );
    while solver_state.assigments_len() < solver_state.num_variables {
        debug_assert!(solver_state.check_watch_invariant());
        let recent_dec: Decision = Decision::make_choice(solver_state.pick_var());

        // println!("Have {} assigs", solver_state.assig.len());

        // println!(
        //     "solver loop level {} num clauses: {}",
        //     solver_state.level,
        //     solver_state.clauses.len()
        // );
        solver_state.add_decision(&recent_dec);
        if !unit_prop_sat(solver_state, &recent_dec) {
            return CNFStatus::UNSAT;
        }
    }
    CNFStatus::SAT {
        model: solver_state.get_model(),
    }
}
pub fn print_result(formula_file: String, res: CNFStatus, time: f32) {
    let mut res_dict: FxHashMap<String, String> = FxHashMap::default();
    res_dict.insert(
        "Instance".to_string(),
        Path::new(&formula_file)
            .file_name()
            .unwrap()
            .to_str()
            .unwrap()
            .to_string(),
    );
    res_dict.insert("Time".to_string(), time.to_string());
    res_dict.insert(
        "Result".to_string(),
        if res == CNFStatus::UNSAT {
            "UNSAT"
        } else {
            "SAT"
        }
        .to_string(),
    );

    match res {
        CNFStatus::SAT { model } => {
            let tmpvec: Vec<String> = model
                .iter()
                .map(|&lit| {
                    format!(
                        "{} {} ",
                        lit.abs(),
                        if lit.is_positive() { "true" } else { "false" }
                    )
                })
                .collect();
            let solution_string: String = tmpvec.join(" ");
            res_dict.insert("Solution".to_string(), solution_string);
        }
        CNFStatus::UNSAT => {}
    }
    let vals = res_dict
        .iter()
        .map(|(k, v)| format!("\"{}\":\"{}\"", k, v))
        .collect::<Vec<String>>()
        .join(",");
    println!("{{{}}}", vals);
}
pub fn check_result(solver_state: &SolverState, res: &CNFStatus) {
    println!("Checking result");

    match res {
        CNFStatus::SAT { model } => {
            //Check that assignment equal to model
            for &n in model.iter() {
                let lit = Literal::from(n);
                let assig = solver_state.assig.get(&lit.var).unwrap();
                if assig.litsign != n.is_positive() {
                    println!("Error: assignment {:?} not equal to model {:?}", assig, lit);
                    exit(1);
                }
            }

            for clause in solver_state.clauses.iter() {
                let satisfied = clause
                    .literals
                    .iter()
                    .any(|&lit| lit.sign == model[lit.var - 1].is_positive());

                if !satisfied {
                    let mut corresponding_assig: Vec<Literal> = Vec::new();
                    for &lit in clause.literals.iter() {
                        corresponding_assig.push(Literal {
                            var: lit.var,
                            sign: solver_state.assig.get(&lit.var).unwrap().litsign,
                        });
                    }
                    println!(
                        "Error: clause {:?} not satisfied corrsp assig {:?}",
                        clause, corresponding_assig
                    );
                    assert!(false);
                }
            }
            println!("ALL GOOD");
        }
        _ => {}
    }
}

fn run_solver(formula_file : String) -> (f32, CNFStatus){
    let start = std::time::Instant::now();
    let parsed_out = match parse_cnf(&formula_file) {
        Ok(p) => p,
        Err(e) => {
            println!("c Error: {}", e);
            exit(1);
        }
    };
    let mut solver_state = SolverState::from_parsed_out(parsed_out);
    match solver_state.preprocess() {
        FormulaPreprocess::Ok => {}
        FormulaPreprocess::TrivialUNSAT => {
            let res = CNFStatus::UNSAT;
            check_result(&solver_state, &res);
            let mut total = start.elapsed().as_secs_f32();
            total = (total * 100.0).round() / 100.0;
            return (total,res);
        }
    };
    let res = solver(&mut solver_state);
    println!("c Got result");
    check_result(&solver_state, &res);
    let mut total = start.elapsed().as_secs_f32();
    total = (total * 100.0).round() / 100.0;
    return (total,res);
}
fn main() {
    //get current time
    // println!("Size of clause struct is {}", std::mem::size_of::<Clause>());
    let args: Vec<String> = env::args().collect();
    let formula_file = args[1].clone();
    // let formula_file = "../input/C168_128.cnf".to_string();
    let (total,res) = run_solver(formula_file.clone());
    print_result(formula_file, res, total);
}
