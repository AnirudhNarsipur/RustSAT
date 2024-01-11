use std::{
    collections::{HashMap, HashSet},
    vec,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub struct Literal {
    pub var: LiteralSize,
    pub sign: bool,
}
impl From<i32> for Literal {
    fn from(i: i32) -> Self {
        Literal {
            var: i.unsigned_abs() as LiteralSize,
            sign: i.is_positive(),
        }
    }
}
impl Literal {
    pub fn make_new(n: &str) -> Self {
        let tmp: i32 = n.parse().unwrap();
        if tmp == 0 {
            panic!("literal cannot be 0")
        }
        Literal {
            var: tmp.unsigned_abs() as LiteralSize,
            sign: tmp.is_positive(),
        }
    }

    pub fn is_negative(&self) -> bool {
        !self.sign
    }
    pub fn invert(&self) -> Literal {
        Literal {
            var: self.var,
            sign: !self.sign,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub struct AssigInfo {
    pub litsign: bool,
    pub level: usize,
}

pub type Assig = HashMap<LiteralSize, AssigInfo>;

#[inline(always)]
pub fn literal_falsified(lit: &Literal, assig: &Assig) -> bool {
    match assig.get(&lit.var) {
        Some(&b) => b.litsign != lit.sign,
        None => false,
    }
}

pub fn literal_satisfied(lit: &Literal, assig: &Assig) -> bool {
    match assig.get(&lit.var) {
        Some(&b) => b.litsign == lit.sign,
        None => false,
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Clause {
    pub literals: Vec<Literal>,
    pub w1: usize,
    pub w2: usize,
}

#[derive(Debug)]
pub enum ClauseUnitProp {
    Reassigned {
        old_watch: Literal,
        new_watch: Literal,
    },
    Unit {
        lit: Literal,
    },
    Conflict,
    Satisfied,
}

#[derive(PartialEq, Debug)]
pub enum FormulaUnitProp {
    Ok,
    Conflict { conflict_cause_idx: usize },
}

impl TryFrom<Vec<i32>> for Clause {
    type Error = &'static str;
    fn try_from(vc: Vec<i32>) -> Result<Self, Self::Error> {
        if vc.len() < 2 {
            return Err("Must have at least 2 literals");
        }
        let lits = vc.into_iter().map(Literal::from).collect();
        Result::Ok(Self {
            literals: lits,
            w1: 0,
            w2: 1,
        })
    }
}

impl Clause {
    pub fn make_clause(raw_clause: Vec<&str>) -> Self {
        assert!(raw_clause.len() >= 2);
        let lits: Vec<Literal> = raw_clause
            .iter()
            .take_while(|&&lit| !lit.eq("0"))
            .map(|raw_lit| Literal::make_new(raw_lit))
            .collect();

        Self {
            literals: lits,
            w1: 0,
            w2: 1,
        }
    }
    pub fn unit_prop(&mut self, assig: &Assig, lit: &Literal) -> ClauseUnitProp {
        assert!(literal_falsified(lit, assig));
        let (cur_idx, oidx) = if self.literals[self.w1] == *lit {
            (self.w1, self.w2)
        } else if self.literals[self.w2] == *lit {
            (self.w2, self.w1)
        } else {
            panic!("unreachable!");
        };
        let other_watch_lit = &self.literals[oidx];

        if literal_falsified(other_watch_lit, assig) {
            //print any literal that was not falsified

            // println!("Current lit: {:?} Falsified watch {:?}  assigned {:?} decision {:?}",lit,other_watch_lit,assig.get(&other_watch_lit.var),find_decision(&dstack, &other_watch_lit.invert()));
            // for lit in self.literals.iter() {
            //     if !literal_falsified(lit, assig) {
            //         println!("{:?} not falsified assigned at level {:?}",lit,assig.get(&lit.var));
            //     }
            // }
            return ClauseUnitProp::Conflict;
        } else if literal_satisfied(&self.literals[oidx], assig) {
            return ClauseUnitProp::Satisfied;
        }

        for (idx, itr_lit) in self.literals.iter().enumerate() {
            if idx != self.w1 && idx != self.w2 && !literal_falsified(itr_lit, assig) {
                if cur_idx == self.w1 {
                    self.w1 = idx;
                } else {
                    self.w2 = idx;
                }
                return ClauseUnitProp::Reassigned {
                    old_watch: *lit,
                    new_watch: self.literals[idx],
                };
            }
        }

        ClauseUnitProp::Unit {
            lit: self.literals[oidx],
        }
    }
}

pub type LiteralSize = usize;

// #[derive(Debug)]
// struct Assig {
//     stack : Vec<Vec<Literal>>,
// }

#[derive(Debug, Clone, PartialEq)]
pub struct VarWatch {
    pub false_watch: HashSet<usize>,
    pub true_watch: HashSet<usize>,
}
impl Default for VarWatch {
    fn default() -> Self {
        Self::new()
    }
}

impl VarWatch {
    pub fn new() -> Self {
        Self {
            false_watch: HashSet::new(),
            true_watch: HashSet::new(),
        }
    }
    pub fn remove_idx(&mut self, lit: &Literal, idx: usize) {
        match lit.sign {
            true => self.true_watch.remove(&idx),
            false => self.false_watch.remove(&idx),
        };
    }
}
#[derive(PartialEq, Debug)]
pub struct WatchList {
   pub watchlist: Vec<VarWatch>,
}
impl WatchList {
    pub fn empty() -> Self {
        Self {
            watchlist: Vec::new(),
        }
    }
    pub fn new(num_vars: usize) -> Self {
        Self {
            watchlist: vec![VarWatch::new(); num_vars + 1],
        }
    }
    pub fn add_to_list(&mut self, lit: &Literal, clause_idx: usize) {
        let var = lit.var;
        if lit.sign {
            self.watchlist[var].true_watch.insert(clause_idx);
        } else {
            self.watchlist[var].false_watch.insert(clause_idx);
        }
    }

    #[allow(dead_code)]
    pub fn get(&self, idx: usize) -> &VarWatch {
        &self.watchlist[idx]
    }
    pub fn get_lit(&self, lit: &Literal) -> &HashSet<usize> {
        match lit.sign {
            true => &self.watchlist[lit.var].true_watch,
            false => &self.watchlist[lit.var].false_watch,
        }
    }
    pub fn move_watch(&mut self, old_watch: Literal, new_watch: Literal, clause_idx: usize) {
        self.watchlist[old_watch.var].remove_idx(&old_watch, clause_idx);
        self.add_to_list(&new_watch, clause_idx);
    }
}

#[derive(Clone, PartialEq, Debug, Eq)]
pub struct Decision {
    pub lit: Literal,
    pub unit_prop_idx: Option<usize>,
}
impl Decision {
    pub fn make_new(lit: Literal, unit_prop_idx: Option<usize>) -> Self {
        Self { lit, unit_prop_idx }
    }
    pub fn new(lit: i32, unit_prop_idx: Option<usize>) -> Self {
        Self {
            lit: Literal::from(lit),
            unit_prop_idx,
        }
    }
}

pub enum ConflictAnalysisResult {
    UNSAT,
    Backtrack {
        level: usize,
        unit_lit: Literal,
        unit_idx: Option<usize>,
    },
}
