use std::cmp::Ordering;
use rustc_hash::FxHashMap;


use crate::ds::utils::*;
#[derive(PartialEq,Eq,Clone,Debug,PartialOrd, Ord)]
struct Phase {
    true_score : usize,
    false_score : usize,
}
impl Phase {
    pub fn bump(&mut self,lit: &Literal,bump : usize) {
        if lit.is_negative() {
            self.false_score += bump;
        } else {
            self.true_score += bump;
        }
    }
    pub fn decrement(&mut self) {
        self.true_score -= 1;
        self.false_score -= 1;
    }
}
impl Default for Phase {
    fn default() -> Self {
        Phase{true_score : 0,false_score : 0}
    }
}
#[derive(PartialEq,Eq,Clone,Debug,PartialOrd)]
struct ScoreVar {
    phase : Phase,
    var : LiteralSize,
    stored_phase : Option<bool>
}

fn literal_from_score_var(var : &mut ScoreVar) -> Literal {
    match var.stored_phase {
        Some(true) => Literal::from(var.var as i32),
        Some(false) => Literal::from(-(var.var as i32)),
        None => {
            if var.phase.true_score > var.phase.false_score {
                var.stored_phase = Some(true);
                Literal::from(var.var as i32)
            } else {
                var.stored_phase = Some(false);
                Literal::from(-(var.var as i32))
            }

        }
    }
}

impl Ord for ScoreVar {
    fn cmp(&self, other: &ScoreVar) -> Ordering {
        self.phase.cmp(&other.phase)
    }
}

#[derive(PartialEq,Debug)]
pub struct VSIDS {
    variable_scores : FxHashMap<LiteralSize,Phase>,
    var_order : Vec<ScoreVar>,
    nclause_counter : usize,
    decay_rate : usize,
    add_bump : usize,
    
}

impl VSIDS {
    pub fn sort_var_order(&mut self) {
        for var in self.var_order.iter_mut() {
            let act_phase = self.variable_scores.get(&var.var).unwrap();
            var.phase.true_score = act_phase.true_score;
            var.phase.false_score = act_phase.false_score;
        }
        self.var_order.sort_by(|a,b| b.partial_cmp(a).unwrap());
    }
    fn decay(&mut self) {
        for score in self.variable_scores.values_mut() {
            score.true_score >>= 1;
            score.false_score >>= 1;
        }
    }

    pub fn new(num_vars : usize) -> Self {
        let mut var_ord  : Vec<ScoreVar> = Vec::with_capacity(num_vars);
        
        let mut var_scores: FxHashMap<LiteralSize,Phase> = FxHashMap::with_capacity_and_hasher(num_vars, Default::default());

        for v in 1..=num_vars {
           
            var_scores.insert(v ,Default::default());
        };
        for v in 1..=num_vars {
            let nvar =ScoreVar{phase : Default::default(),var : v as LiteralSize,stored_phase : None};
            var_ord.push(nvar);
        }
        
        let mut n = VSIDS{variable_scores : var_scores,var_order : var_ord,nclause_counter : 0,decay_rate : 256,add_bump : 1} ;
        n.sort_var_order();
        n

    }

    pub fn pick_var(&mut self,assig : &Assig) -> Literal {
        for var in self.var_order.iter_mut() {
            if assig.get(&var.var).is_none() {
                return literal_from_score_var(var);
            }
        }
        unreachable!("No unassigned variables left");
    }
  

    pub fn add_clause(&mut self, clause : &Clause) {
        self.nclause_counter += 1;
        if self.nclause_counter == self.decay_rate {
            // println!("Decaying");
            self.nclause_counter = 0;
            self.decay();
            self.sort_var_order();

        }
        for lit in clause.literals.iter() {
            let var = self.variable_scores.get_mut(&lit.var).unwrap();
            var.bump(&lit, self.add_bump);

        }
    }

    pub fn delete_clause(&mut self, clause : &Clause) {  
        for lit in clause.literals.iter() {
            let var = self.variable_scores.get_mut(&lit.var).unwrap();
            var.decrement();
        }
       
    }
}

// pub fn jsw(&self) -> Vec<Literal> {
//     let mut jsw_vec = vec![[0 as f32, 0 as f32]; self.num_variables + 1];
//     for clause in self.clauses.iter() {
//         for lit in clause.literals.iter() {
//             let qnt = 2.0_f32.powf(-1.0 * (clause.literals.len() as f32));
//             if lit.is_negative() {
//                 jsw_vec[lit.var][0] += qnt;
//             } else {
//                 jsw_vec[lit.var][1] += qnt;
//             }
//         }
//     }
//     let mut res: Vec<(f32, Literal)> = Vec::new();
//     for (idx, arr) in jsw_vec.into_iter().enumerate() {
//         res.push((arr[0], Literal::from(-(idx as i32))));
//         res.push((arr[1], Literal::from(idx as i32)));
//     }
//     //reverse sort
//     res.sort_by(|a, b| (b.0).partial_cmp(&a.0).unwrap());
//     return res
//         .iter()
//         .filter_map(|&k| if k.1.var != 0 { Some(k.1) } else { None })
//         .collect();
// }