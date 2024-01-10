use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub struct Literal {
    var: LiteralSize,
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
    fn is_negative(&self) -> bool {
        return !self.sign;
    }
    fn invert(&self) -> Literal {
        Literal {
            var: self.var,
            sign: !self.sign,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
struct AssigInfo {
    litsign: bool,
    level: usize,
}

type Assig = HashMap<LiteralSize, AssigInfo>;

#[inline(always)]
fn literal_falsified(lit: &Literal, assig: &Assig) -> bool {
    match assig.get(&lit.var) {
        Some(&b) => return b.litsign != lit.sign,
        None => return false,
    }
}

#[derive(Debug, Clone)]
pub struct Clause {
    literals: Vec<Literal>,
    w1: usize,
    w2: usize,
}

enum ClauseUnitProp {
    Reassigned,
    Unit { lit: Literal },
    Conflict,
}

#[derive(PartialEq)]
pub enum FormulaUnitProp {
    Ok,
    Conflict { conflict_cause_idx: usize },
}
impl Clause {
    pub fn make_clause(raw_clause: Vec<&str>) -> Clause {
        assert!(raw_clause.len() >= 2);
        let lits: Vec<Literal> = raw_clause
            .iter()
            .take_while(|&&lit| !lit.eq("0"))
            .map(|raw_lit| Literal::make_new(&raw_lit))
            .collect();

        return Clause {
            literals: lits,
            w1: 0,
            w2: 1,
        };
    }
    fn unit_prop(&mut self, assig: &Assig, lit: &Literal) -> ClauseUnitProp {
        let cur_idx = if self.literals[self.w1] == *lit {
            self.w1
        } else {
            self.w2
        };
        let oidx = if self.w1 == cur_idx { self.w2 } else { self.w1 };
        for (idx, lit) in self.literals.iter().enumerate() {
            if idx != self.w1 && idx != self.w2 && !literal_falsified(lit, assig) {
                if cur_idx == self.w1 {
                    self.w1 = idx;
                } else {
                    self.w2 = idx;
                }
                return ClauseUnitProp::Reassigned;
            }
        }
        if literal_falsified(&self.literals[oidx], assig) {
            return ClauseUnitProp::Conflict;
        } else {
            return ClauseUnitProp::Unit {
                lit: self.literals[oidx].clone(),
            };
        }
    }
}

type LiteralSize = u16;
#[derive(Debug, Clone, PartialEq)]
enum ClauseStatus {
    Unknown,
    Satisfied,
    Conflict,
}

// #[derive(Debug)]
// struct Assig {
//     stack : Vec<Vec<Literal>>,
// }

type WatchList = Vec<Vec<usize>>;

#[derive(Clone)]
pub struct Decision {
    lit: Literal,
    unit_prop_idx: Option<usize>,
}
impl Decision {
    pub fn make_new(lit : Literal,unit_prop_idx : Option<usize>) -> Self {
        Self {
            lit : lit,
            unit_prop_idx : unit_prop_idx
        }
    }
}

pub enum ConflictAnalysisResult {
    UNSAT,
    Backtrack { level: usize, unit_lit: Literal,unit_idx : usize },
}
pub struct SolverState {
    decision_stack: Vec<Decision>,
    assig: HashMap<LiteralSize, AssigInfo>,
    level: usize,
    watchlist: WatchList,
    pub num_variables: usize,
    clauses: Vec<Clause>,
}
impl SolverState {
    pub fn make_new(num_vars: usize) -> Self {
        let dstack: Vec<Decision> = Vec::with_capacity(num_vars);
        Self {
            decision_stack: dstack,
            assig: HashMap::new(),
            level: 0,
            watchlist: vec![Vec::new(); num_vars + 1],
            num_variables: num_vars,
            clauses: Vec::new(),
        }
    }
    pub fn decision_stack_size(&self) -> usize {
        self.decision_stack.len()
    }

    pub fn pick_var(&self) -> Literal {
        for i in 1..=self.num_variables {
            if !self.assig.contains_key(&(i as u16)) {
                return Literal {
                    var: i as u16,
                    sign: true,
                };
            }
        }
        panic!("unreachable!");
    }
    fn add_decision(&mut self, lit: &Literal) {
        assert!(self.assig.contains_key(&lit.var));
        self.assig.insert(
            lit.var,
            AssigInfo {
                litsign: lit.sign,
                level: self.level,
            },
        );
        self.decision_stack.push(Decision {
            lit: lit.clone(),
            unit_prop_idx: None,
        });
        self.level += 1;
    }
    fn add_unit(&mut self, lit: &Literal, blame_idx: usize) {
        assert!(self.assig.contains_key(&lit.var));
        self.assig.insert(
            lit.var,
            AssigInfo {
                litsign: lit.sign,
                level: self.level,
            },
        );
        self.decision_stack.push(Decision {
            lit: lit.clone(),
            unit_prop_idx: Some(blame_idx),
        });
    }

    pub fn add_unit_or_decision(&mut self, d: &Decision) {
        match d.unit_prop_idx {
            None => self.add_decision(&d.lit),
            Some(idx) => self.add_unit(&d.lit, idx),
        }
    }

    pub fn backtrack_to_level(&mut self, backtrack_level: usize) {
        assert!(backtrack_level < self.decision_stack.len() - 1);

        while self.level != backtrack_level {
            self.pop_decision_stack();
        }
    }

    fn pop_decision_stack(&mut self) -> Decision {
        let dec = self.decision_stack.pop().unwrap();
        match dec {
            Decision {
                lit,
                unit_prop_idx: None,
            } => {
                //this is a decision
                self.level -= 1;
                self.assig.remove(&lit.var);
                return dec;
            }
            Decision {
                lit,
                unit_prop_idx: Some(_),
            } => {
                self.assig.remove(&lit.var);
                return dec;
            }
        }
    }
    pub fn add_raw_clause(&mut self, raw_clause: Vec<&str>) {
        if raw_clause.len() == 2 {
            let unit: Literal = Literal::make_new(raw_clause[0]);
            self.add_unit(&unit, self.clauses.len());
        } else {
            let clause = Clause::make_clause(raw_clause);
            self.watchlist[clause.w1].push(self.clauses.len() - 1);
            self.watchlist[clause.w2].push(self.clauses.len() - 1);
            self.clauses.push(clause);
        }
    }

    fn pure_literal_elimination(&mut self) -> () {
        let mut pure_lit: Vec<[bool; 2]> = vec![[false; 2]; (self.num_variables + 1) as usize];
        self.clauses.iter().for_each(|clause| {
            clause.literals.iter().for_each(|lit| {
                if lit.is_negative() {
                    pure_lit[lit.var as usize][0] = true
                } else {
                    pure_lit[lit.var as usize][1] = true
                }
            })
        });
        let pure_lit_vec: Vec<Literal> = pure_lit
            .iter()
            .enumerate()
            .filter_map(|(idx, &x)| {
                if x[0] ^ x[1] {
                    if x[0] {
                        Some(Literal {
                            var: idx as u16,
                            sign: false,
                        })
                    } else {
                        Some(Literal {
                            var: idx as u16,
                            sign: true,
                        })
                    }
                } else {
                    None
                }
            })
            .collect();

        let pure_lit_set: HashSet<Literal> = HashSet::from_iter(pure_lit_vec);

        self.clauses.retain(|clause| {
            clause
                .literals
                .iter()
                .any(|lit| !pure_lit_set.contains(lit))
        });
        pure_lit_set
            .iter()
            .enumerate()
            .for_each(|(idx, lit)| self.add_unit(lit, idx)); // TODO fix
    }

    pub fn unit_prop(&mut self, blame: &Decision) -> FormulaUnitProp {
        self.add_unit_or_decision(blame);
        let unit = blame.lit.clone();
        let mut new_units: Vec<Decision> = Vec::new();
        for (idx, clause) in self.clauses.iter_mut().enumerate() {
            match clause.unit_prop(&self.assig, &unit) {
                ClauseUnitProp::Reassigned => continue,
                ClauseUnitProp::Unit { lit } => new_units.push(Decision {
                    lit: lit,
                    unit_prop_idx: Some(idx),
                }),
                ClauseUnitProp::Conflict => {
                    return FormulaUnitProp::Conflict {
                        conflict_cause_idx: idx,
                    }
                }
            }
        }

        for nblame in new_units.into_iter() {
            let res = self.unit_prop(&nblame);
            if res != FormulaUnitProp::Ok {
                return res;
            }
        }
        return FormulaUnitProp::Ok;
    }
    fn remove_units(&mut self) {
        let (unit_clauses, non_unit): (Vec<Clause>, Vec<Clause>) = self
            .clauses
            .iter()
            .cloned()
            .partition(|cl| cl.literals.len() == 1);
        let unit_literals: Vec<Literal> = unit_clauses
            .iter()
            .map(|cl| cl.literals[0].clone())
            .collect();
        unit_literals
            .iter()
            .enumerate()
            .for_each(|(idx, unit)| self.add_unit(unit, 0)); //TODO fix

        let units_set: HashSet<Literal> = HashSet::from_iter(unit_literals);
        self.clauses = non_unit
            .iter()
            .cloned()
            .filter(|cl| cl.literals.iter().any(|lit| !units_set.contains(lit)))
            .collect();
    }
    pub fn preprocess(&mut self) {
        assert!(self.level == 0);
        let mut origsize = self.clauses.len();
        self.pure_literal_elimination();
        self.remove_units();
        while self.clauses.len() != origsize {
            self.pure_literal_elimination();
            self.remove_units();
        }
    }
    fn get_lit_level(&self, lit: &Literal) -> usize {
        self.assig.get(&lit.var).unwrap().level
    }

    pub fn get_backtrack_level(&self, lits: &Vec<Literal>) -> usize {
        let mut highest = None;
        let mut second_highest = None;

        for &value in lits.iter() {
            let v_level = self.get_lit_level(&value);
            match highest {
                Some(h) if v_level > h => {
                    second_highest = highest;
                    highest = Some(v_level);
                }
                Some(h) if v_level < h => match second_highest {
                    Some(sh) if v_level > sh => {
                        second_highest = Some(v_level);
                    }
                    None => {
                        second_highest = Some(v_level);
                    }
                    _ => {}
                },
                None => {
                    highest = Some(v_level);
                }
                _ => {}
            }
        }

        second_highest.unwrap()
    }
    pub fn analyze_conflict(&mut self, conflict_idx: usize) -> ConflictAnalysisResult {
        if self.level == 0 {
            return ConflictAnalysisResult::UNSAT;
        }
        let conflict_clause = &self.clauses[conflict_idx];
        assert!(conflict_clause
            .literals
            .iter()
            .all(|lit| literal_falsified(lit, &self.assig)));

        let blamed_decisions: Vec<Literal> = conflict_clause
            .literals
            .iter()
            .map(|lit| lit.invert())
            .collect();
        let (cur_level_decs, old_level_decs): (Vec<Literal>, Vec<Literal>) = blamed_decisions
            .into_iter()
            .partition(|lit| self.assig.get(&lit.var).unwrap().level == self.level);
        let mut blamed_decs = old_level_decs;
        let mut curset: HashSet<Literal> = HashSet::from_iter(cur_level_decs.into_iter());
        let curlvl = self.level;
        while curset.len() != 1 {
            match self.pop_decision_stack() {
                Decision {
                    lit,
                    unit_prop_idx: None,
                } => {
                    panic!("unreachable!");
                }
                Decision {
                    lit,
                    unit_prop_idx: Some(unit_idx),
                } => {
                    curset.remove(&lit);
                    for &resp_lit in self.clauses[unit_idx].literals.iter() {
                        if resp_lit == lit {
                            continue;
                        }
                        let resp_lit_level = self.get_lit_level(&resp_lit);
                        if resp_lit_level < self.level {
                            blamed_decs.push(resp_lit);
                        } else {
                            curset.insert(resp_lit);
                        }
                    }
                }
            }
        }
        //curset now has the UIP
        let &uip = curset.iter().next().unwrap();
        blamed_decs.push(uip);

        let clause_lits: Vec<Literal> = blamed_decs.into_iter().map(|lit| lit.invert()).collect();

        let backtrack_level = self.get_backtrack_level(&clause_lits);

        if clause_lits.len() != 1 {
            let uip_idx = clause_lits.len() - 1;
            let new_clause = Clause {
                literals: clause_lits,
                w1: 0,
                w2: uip_idx,
            };
            self.clauses.push(new_clause);
        }
        return ConflictAnalysisResult::Backtrack {
            level: backtrack_level,
            unit_lit: uip.invert(),
            unit_idx : self.clauses.len()-1
        };

        //Find UIP
    }
}
