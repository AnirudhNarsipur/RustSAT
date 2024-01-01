use std::fs::File;
use std::io::{self, prelude::*};
use std::path::Path;
use std::process::exit;

#[derive(Debug, Clone, PartialEq)]
enum ClauseStatus {
    Unknown,
    Satisfied,
    Conflict,
}

type Assig = Vec<Option<bool>>;
type WatchList = Vec<Vec<usize>> ;
enum Tracking {
    BackTrack,
    Recur,
    Negate,
}
#[derive(Debug)]
enum CNFStatus {
    SAT { assignment: Assig },
    UNSAT
}

struct SolverState {
    assignment: Assig,
    stack: Vec<Literal>,
    watchlist : WatchList
}

impl SolverState {
    fn make_new(num_vars: usize) -> Self {
        
        Self {
            assignment: vec![None; num_vars + 1],
            stack: Vec::new(),
            watchlist : vec![Vec::new();num_vars+1]
        }
    }
    fn add_assignment(&mut self, lit: Literal) {
        self.assignment[lit.var as usize] = Some(lit.sign);
        self.stack.push(lit);
    }
    fn remove_assignment(&mut self) -> Literal {
        self.assignment[self.stack.last().unwrap().var as usize] = None;
        return self.stack.pop().unwrap();
    }
    fn negate_assignment(&mut self) {
        let lit = self.stack.last_mut().unwrap();
        lit.sign = !lit.sign;
        self.assignment[lit.var as usize] = Some(lit.sign);
    }
}

#[inline(always)]
fn literal_satisifed(assig: &Assig, lit: &Literal) -> ClauseStatus {
    return match assig[lit.var as usize] {
        None => ClauseStatus::Unknown,
        Some(lit_assig) => {
            if lit_assig == lit.sign {
                ClauseStatus::Satisfied
            } else {
                ClauseStatus::Conflict
            }
        }
    };
}
#[derive(Debug, Clone)]
struct Literal {
    var: u16,
    sign: bool,
}
impl Literal {
    fn make_new(n: &str) -> Self {
        let tmp: i16 = n.parse().unwrap();
        if tmp == 0 {
            panic!("literal cannot be 0")
        }
        return Literal {
            var: tmp.abs() as u16,
            sign: tmp.is_positive(),
        };
    }
    fn is_positive(&self) -> bool {
        return self.sign;
    }
}

#[derive(Debug, Clone)]
struct Clause {
    literals: Vec<Literal>,
}

struct WatchClause {
    literals : Vec<Literal>,
    w1  : u16 ,
    w2 : u16,
}

// impl WatchClause {
//     fn make_new(cl : Clause) -> Self {
//         assert!(cl.literals.len() >= 2)
//         random
//     }
// }
#[derive(Debug, Clone)]
struct CNF {
    num_variables: u16,
    num_clauses: u16,
    clauses: Vec<Clause>,
}
impl Clause {
    fn make_clause(raw_clause: Vec<&str>) -> Clause {
        let lits: Vec<Literal> = raw_clause
            .iter()
            .take_while(|&&lit| !lit.eq("0"))
            .map(|raw_lit| Literal::make_new(&raw_lit))
            .collect();

        return Clause { literals: lits };
    }
}
impl CNF {
    fn unit_prop(&mut self, assignment: &mut Assig) -> ClauseStatus {
        let mut stat = ClauseStatus::Satisfied;
        for clause in self.clauses.iter_mut() {
            match propogate_unit(clause, assignment) {
                ClauseStatus::Unknown => stat = ClauseStatus::Unknown,
                ClauseStatus::Satisfied => continue,
                ClauseStatus::Conflict => return ClauseStatus::Conflict,
            }
        }
        return stat;
    }
}

fn parse_cnf(filename: &str) -> io::Result<CNF> {
    let path = Path::new(filename);
    let file = File::open(&path)?;
    let reader = io::BufReader::new(file);

    let mut num_clauses: u16 = 0;
    let mut num_variables: u16 = 0;
    let mut clauses: Vec<Clause> = Vec::new();
    for line in reader.lines() {
        let cleaned = (line?).replace("\r", "");
        if cleaned.starts_with("c") {
            continue;
        } else if cleaned.starts_with("p cnf") {
            let parts: Vec<&str> = cleaned.split_whitespace().collect();
            num_variables = parts[2].parse().unwrap();
            num_clauses = parts[3].parse().unwrap();
        } else if !cleaned.is_empty() {
            let new_clause = Clause::make_clause(cleaned.split_whitespace().collect());
            clauses.push(new_clause);
        } else {
            break;
        }
    }
    return Ok(CNF {
        num_variables: num_variables,
        num_clauses: num_clauses,
        clauses: clauses,
    });
}

fn pure_literal_elimination(cnf: &CNF) -> CNF {
    let mut pure_lit: Vec<[bool; 2]> = vec![[false; 2]; (cnf.num_variables + 1) as usize];
    cnf.clauses.iter().for_each(|clause| {
        clause.literals.iter().for_each(|lit| {
            if !lit.is_positive() {
                pure_lit[lit.var as usize][0] = true
            } else {
                pure_lit[lit.var as usize][1] = true
            }
        })
    });

    let filter_clauses = cnf
        .clauses
        .iter()
        .filter(|clause| {
            clause
                .literals
                .iter()
                .all(|lit| !(pure_lit[lit.var as usize][0] ^ pure_lit[lit.var as usize][1]))
        })
        .cloned()
        .collect();
    return CNF {
        num_variables: cnf.num_variables,
        num_clauses: cnf.clauses.len().try_into().unwrap(),
        clauses: filter_clauses,
    };
}

// fn remove_units(cnf : &CNF) -> CNF {
//     let (non_unit_clauses,unit_clauses) = cnf.clauses.clone().into_iter().partition(|cl| cl.literals.len() > 1);

// }

fn propogate_unit(clause: &mut Clause, assigment: &Assig) -> ClauseStatus {
    let mut all_conflict: bool = true;
    for lit in clause.literals.iter() {
        match literal_satisifed(assigment, lit) {
            ClauseStatus::Unknown => all_conflict = false,

            ClauseStatus::Satisfied => {
                return ClauseStatus::Satisfied;
            }
            ClauseStatus::Conflict => continue,
        }
    }
    if all_conflict {
        return ClauseStatus::Conflict;
    } else {
        return ClauseStatus::Unknown;
    }
}
fn jsw(cnf: &CNF) -> Vec<Literal> {
    let mut jsw_vec = vec![0 as f32; (cnf.num_variables as usize) + 1];
    for clause in cnf.clauses.iter() {
        for lit in clause.literals.iter() {
            let abslit = lit.var;
            jsw_vec[abslit as usize] += 2.0_f32.powf(-1.0 * (clause.literals.len() as f32));
        }
    }
    let mut tmp: Vec<(usize, f32)> = jsw_vec.into_iter().enumerate().collect();
    tmp.sort_by(|a, b| (a.1).partial_cmp(&b.1).unwrap());
    return tmp
        .iter()
        .filter_map(|&k| {
            if k.0 != 0 {
                Some(Literal {
                    var: k.0 as u16,
                    sign: true,
                })
            } else {
                None
            }
        })
        .collect();
}
fn dpll(cnf: &mut CNF) -> CNFStatus {
    let mut solver_state = SolverState::make_new(cnf.num_variables as usize);
    let mut var_order: Vec<u16> =  (1..=cnf.num_variables).collect() ; // jsw(cnf);
    let mut tracker = Tracking::Recur;
    // let mut crct : Vec<Option<bool>> = vec![0,1, -2, -3, 4, -5, 6, -7, -8, -9, -10, -11, -12, 13, 14, 15, -16, 17, -18, -19, 20].iter()
    // .enumerate()
    // .map(|(idx,&val)| if idx == 0 {None} else if val < 0 {Some(false) } else {Some(true)})
    // .collect:: <Vec<Option<bool>>>() ;
    // crct.reverse();
    loop {
        // println!("Running loop. made {} assigs",solver_state.stack.len());
        match tracker {
            Tracking::Recur => {
                let lit = var_order.pop().unwrap();
                solver_state.add_assignment(Literal { var: lit, sign: true });

                match cnf.unit_prop(&mut solver_state.assignment) {
                    ClauseStatus::Conflict =>  tracker = Tracking::Negate,
                   
                    ClauseStatus::Satisfied => {
                        return CNFStatus::SAT {
                            assignment: solver_state.assignment,
                        }
                    }
                    ClauseStatus::Unknown => {}
                }
            }
            Tracking::Negate => {
                if !solver_state.stack.last().unwrap().is_positive() {
                    tracker = Tracking::BackTrack;
                    continue;
                }
                solver_state.negate_assignment();
                match cnf.unit_prop(&mut solver_state.assignment) {
                    ClauseStatus::Conflict => tracker = Tracking::BackTrack, //Go up  
                    ClauseStatus::Satisfied => {
                        return CNFStatus::SAT {
                            assignment: solver_state.assignment,
                        }
                    }
                    ClauseStatus::Unknown => tracker = Tracking::Recur,
                }
            }
            Tracking::BackTrack => {
                var_order.push(solver_state.remove_assignment().var);
                tracker = Tracking::Negate;
                if var_order.len() == cnf.num_variables as usize {
                    return CNFStatus::UNSAT;
                }
            }
        }
    }
}

fn main() {
    let cnf: CNF = match parse_cnf("/Users/anirudh/Projects/RustSAT/small_inst/toy_solveable.cnf") {
        Ok(cnf) => cnf,
        Err(e) => {
            eprintln!("Failed to parse CNF file: {}", e);
            exit(1);
        }
    };

    let mut filted_pure_cnf = pure_literal_elimination(&cnf);
    println!(
        "Deleted {} clauses",
        cnf.clauses.len() - filted_pure_cnf.clauses.len()
    );
    let res = dpll(&mut filted_pure_cnf);
    match res {
        CNFStatus::SAT { assignment } => {
            let crct = filted_pure_cnf.clauses.iter().all(|clause| {
                clause.literals.iter().any(|literal| {
                    literal_satisifed(&assignment, literal) == ClauseStatus::Satisfied
                })
            });
            println!(
                "Got SAT.Result is {:?} assignment is {:?}",
                crct, assignment
            );
        }
        CNFStatus::UNSAT => println!("UNSAT!"),
    }
}
