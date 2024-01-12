use std::{cmp::Ordering, collections::{ HashMap}};

use crate::ds::utils::*;

pub trait Heuristic {
    fn new(num_vars : usize,clauses : Vec<Clause>) -> Self;

    fn pick_var(&mut self,assig : &Assig) -> Literal;

    fn add_clause(&mut self, clause : Clause);

    fn delete_clause(&mut self, clause : Clause);
    
}

#[derive(PartialEq,Clone)]
struct ScoreVar {
    score : usize,
    var : LiteralSize,
    stored_phase : Option<bool>
}

fn literal_from_score_var(var : &ScoreVar) -> Literal {
    if var.stored_phase.is_some_and(|x| !x) {
        Literal::from(-(var.var as i32))
    } else {
        Literal::from(var.var as i32)
    
    }
}

impl PartialOrd for ScoreVar {
    fn partial_cmp(&self, other: &ScoreVar) -> Option<Ordering> {
        self.score.partial_cmp(&other.score)
    }
}
struct VSIDS {
    variable_scores : HashMap<LiteralSize,usize>,
    var_order : Vec<ScoreVar>,
    nclause_counter : usize,
    decay_rate : usize,
    add_bump : usize,
    
}

impl VSIDS {
    fn sort_var_order(&mut self) {
        for var in self.var_order.iter_mut() {
            var.score = *self.variable_scores.get(&var.var).unwrap();
        }
        self.var_order.sort_by(|a,b| b.partial_cmp(a).unwrap());
    }
    fn decay(&mut self) {
        for score in self.variable_scores.values_mut() {
            *score = *score >> 1;
        }
    }
}
impl Heuristic for VSIDS {
    fn new(num_vars : usize,clauses : Vec<Clause>) -> Self {
        let mut var_ord  : Vec<ScoreVar> = Vec::with_capacity(num_vars);
        let mut var_scores: HashMap<LiteralSize,usize> = HashMap::with_capacity(num_vars);

        for v in 1..=num_vars {
           
            var_scores.insert(v ,0);
        };
        for clause in clauses.iter() {
            for lit in clause.literals.iter() {
                let  var = var_scores.get_mut(&lit.var).unwrap();
                *var += 1;
            }
        }
        for v in 1..=num_vars {
            let nvar =ScoreVar{score : 0,var : v as LiteralSize,stored_phase : None};
            var_ord.push(nvar);
        }
        
        let mut n = VSIDS{variable_scores : var_scores,var_order : var_ord,nclause_counter : 0,decay_rate : 256,add_bump : 1} ;
        n.sort_var_order();
        n

    }

    fn pick_var(&mut self,assig : &Assig) -> Literal {
        for var in self.var_order.iter() {
            if assig.get(&var.var).is_none() {
                return literal_from_score_var(var);
            }
        }
        unreachable!("No unassigned variables left");
    }

    fn add_clause(&mut self, clause : Clause) {
        self.nclause_counter += 1;
        if self.nclause_counter == self.decay_rate {
            self.nclause_counter = 0;
            self.decay();
            self.sort_var_order();

        }
        for lit in clause.literals.iter() {
            let var = self.variable_scores.get_mut(&lit.var).unwrap();
            *var += self.add_bump;
        }
    }

    fn delete_clause(&mut self, clause : Clause) {  
        for lit in clause.literals.iter() {
            let var = self.variable_scores.get_mut(&lit.var).unwrap();
            *var -= self.add_bump;
        }
       
    }
}