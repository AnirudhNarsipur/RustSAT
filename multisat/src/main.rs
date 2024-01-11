use crate::ds::*;
use crate::parse::*;
use std::env;
use std::process::exit;

pub mod ds;
pub mod parse;

#[derive(Debug)]
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
    println!("Have {} clauses", solver_state.clauses.len());
    while solver_state.assigments_len() < solver_state.num_variables {
        solver_state.check_watch_invariant();
        let recent_dec: Decision = Decision::make_choice(solver_state.pick_var());
        println!(
            "solver loop level {} num clauses: {}",
            solver_state.level,
            solver_state.clauses.len()
        );
        solver_state.add_decision(&recent_dec);
        if !unit_prop_sat(solver_state, &recent_dec) {
            return CNFStatus::UNSAT;
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
            for &lit in model.iter() {
                print!("{} ", lit);
            }
            println!("0");
        }
        CNFStatus::UNSAT => println!("s UNSATISFIABLE"),
    }
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
fn main() {
    let args: Vec<String> = env::args().collect();
    // let formula_file = args[1].clone();
    let formula_file = "../input/C168_128.cnf";

    let parsed_out = match parse_cnf(&formula_file) {
        Ok(p) => p,
        Err(e) => {
            println!("Error: {}", e);
            exit(1);
        }
    };
    let mut solver_state = SolverState::from_parsed_out(parsed_out);
    match solver_state.preprocess() {
        FormulaPreprocess::Ok => {},
        FormulaPreprocess::TrivialUNSAT => {
            let res = CNFStatus::UNSAT;
            check_result(&solver_state, &res);
            print_result(res);
            return;
        }
    } ;
    let res = solver(&mut solver_state);
    println!("Got result");
    check_result(&solver_state, &res);
    print_result(res);
   
}
