pub mod utils;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    vec,
};
pub use utils::*;

#[derive(PartialEq, Debug)]
pub struct SolverState {
    decision_stack: Vec<Decision>,
    pub assig: HashMap<LiteralSize, AssigInfo>,
    level: usize,
    watchlist: WatchList,
    pub num_variables: usize,
    pub clauses: Vec<Clause>,
    pub var_order: Vec<Literal>,
}
impl SolverState {
    pub fn make_new(num_vars: usize) -> Self {
        let dstack: Vec<Decision> = Vec::with_capacity(num_vars);
        Self {
            decision_stack: dstack,
            assig: HashMap::new(),
            level: 0,
            watchlist: WatchList::empty(), //Initialize later
            num_variables: num_vars,
            clauses: Vec::new(),
            var_order: Vec::new(),
        }
    }

    pub fn jsw(&self) -> Vec<Literal> {
        let mut jsw_vec = vec![[0 as f32, 0 as f32]; self.num_variables + 1];
        for clause in self.clauses.iter() {
            for lit in clause.literals.iter() {
                let qnt = 2.0_f32.powf(-1.0 * (clause.literals.len() as f32));
                if lit.is_negative() {
                    jsw_vec[lit.var][0] += qnt;
                } else {
                    jsw_vec[lit.var][1] += qnt;
                }
            }
        }
        let mut res: Vec<(f32, Literal)> = Vec::new();
        for (idx, arr) in jsw_vec.into_iter().enumerate() {
            res.push((arr[0], Literal::from(-(idx as i32))));
            res.push((arr[1], Literal::from(idx as i32)));
        }
        //reverse sort
        res.sort_by(|a, b| (b.0).partial_cmp(&a.0).unwrap());
        return res
            .iter()
            .filter_map(|&k| if k.1.var != 0 { Some(k.1) } else { None })
            .collect();
    }
    pub fn decision_stack_size(&self) -> usize {
        self.decision_stack.len()
    }

    pub fn pick_var(&self) -> Literal {
        for i in self.var_order.iter() {
            if !self.assig.contains_key(&i.var) {
                return *i;
            }
        }
        panic!("unreachable!");
    }
    pub fn add_unit_or_decision(&mut self, d: &Decision) {
        let lit = d.lit;
        assert!(!self.assig.contains_key(&lit.var));
        if d.unit_prop_idx.is_none() {
            self.level += 1;
        }
        self.assig.insert(
            lit.var,
            AssigInfo {
                litsign: lit.sign,
                level: self.level,
            },
        );
        self.decision_stack.push(d.clone());
    }
    pub fn add_preproc(&mut self, lit: &Literal) -> bool {
        if literal_falsified(lit, &self.assig) {
            return false;
        }
        self.assig.insert(
            lit.var,
            AssigInfo {
                litsign: lit.sign,
                level: 0,
            },
        );
        true
    }
    pub fn backtrack_to_level(&mut self, backtrack_level: usize) {
        assert!(backtrack_level < self.level);

        while self.level != backtrack_level {
            self.pop_decision();
        }
    }

    fn pop_decision(&mut self) -> Decision {
        match self.decision_stack.pop() {
            Some(dec) => {
                self.assig.remove(&dec.lit.var);
                if dec.unit_prop_idx.is_none() {
                    self.level -= 1
                }
                dec
            }
            None => unreachable!("nothing to remove!"),
        }
    }
    pub fn add_clause(&mut self, clause: Clause) {
        let clauseset = clause
            .literals
            .iter()
            .map(|lit| lit.var)
            .collect::<HashSet<LiteralSize>>();
        assert!(clauseset.len() == clause.literals.len());
        //We have to add watchlist later
        self.clauses.push(clause);
    }
    pub fn add_raw_clause(&mut self, raw_clause: Vec<&str>) -> bool {
        let mut clause_ints: Vec<i32> = raw_clause
            .into_iter()
            .map(|lit_str| lit_str.parse::<i32>().unwrap())
            .take_while(|&n| n != 0)
            .collect();
        let mut set = HashSet::new();
        clause_ints.retain(|e| set.insert(*e));

        if clause_ints.len() == 1 {
            let unit: Literal = Literal::from(clause_ints[0]);
            if !self.add_preproc(&unit) {
                return false;
            }
        } else {
            let clause = Clause::try_from(clause_ints).unwrap();
            self.add_clause(clause);
        }
        true
    }
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    fn pure_literal_elimination(&mut self) {
        let mut pure_var_tracker: HashMap<LiteralSize, [bool; 2]> = HashMap::new();
        for var in 1..=self.num_variables {
            pure_var_tracker.insert(var, [false, false]);
        }
        //Get all the pure lits
        for clause in self.clauses.iter() {
            for lit in clause.literals.iter() {
                if lit.is_negative() {
                    pure_var_tracker.get_mut(&lit.var).unwrap()[0] = true;
                } else {
                    pure_var_tracker.get_mut(&lit.var).unwrap()[1] = true;
                }
            }
        }
        //Filter them
        let pure_vars: HashSet<LiteralSize> = pure_var_tracker
            .iter()
            .filter(|(&_var, &arr)| arr[0] ^ arr[1])
            .map(|(&var, &_arr)| var)
            .collect();

        //Remove clause containg pure vars
        self.clauses.retain(|clause| {
            !clause
                .literals
                .iter()
                .any(|lit| pure_vars.contains(&lit.var))
        });

        //assign them
        for pure_var in pure_vars.iter() {
            let sign = !pure_var_tracker.get(pure_var).unwrap()[0];
            let lit = Literal {
                var: *pure_var,
                sign,
            };
            self.add_preproc(&lit);
        }
    }

    pub fn unit_prop(&mut self, blame: &Decision) -> FormulaUnitProp {
        let mut units_queue = VecDeque::from([blame.clone()]);
        // maintain a seperate set from the assignments because we want the chronology to be correct -
        // all parents lits in the implication graph should precede the given lit without ^ that would break

        let mut seen_new_units: HashSet<Literal> = HashSet::from([blame.lit]);
        let mut add_unit: bool = false;
        while !units_queue.is_empty() {
            let d = units_queue.pop_front().unwrap();
            let unit = d.lit;
            let unit_inverted = unit.invert();

            if add_unit {
                self.add_unit_or_decision(&d);
            }

            for &clause_idx in self.watchlist.get_lit(&unit_inverted).clone().iter() {
                let clause = self.clauses.get_mut(clause_idx).unwrap();
                match clause.unit_prop(&self.assig, &unit_inverted) {
                    ClauseUnitProp::Reassigned {
                        old_watch,
                        new_watch,
                    } => {
                        self.watchlist.move_watch(old_watch, new_watch, clause_idx);
                    }
                    ClauseUnitProp::Satisfied => continue,
                    ClauseUnitProp::Unit { lit } => {
                        if seen_new_units.contains(&lit) || self.assig.contains_key(&lit.var) {
                            continue;
                        }
                        units_queue.push_back(Decision {
                            lit,
                            unit_prop_idx: Some(clause_idx),
                        });
                        seen_new_units.insert(lit);
                    }
                    ClauseUnitProp::Conflict => {
                        return FormulaUnitProp::Conflict {
                            conflict_cause_idx: clause_idx,
                        }
                    }
                }
            }
            //After the first add all the rest
            add_unit = true;
        }
        FormulaUnitProp::Ok
    }
    pub fn setup_watchlist(&mut self) {
        self.watchlist = WatchList::new(self.num_variables);
        for (idx, clause) in self.clauses.iter().enumerate() {
            self.watchlist.add_to_list(&clause.literals[clause.w1], idx);
            self.watchlist.add_to_list(&clause.literals[clause.w2], idx);
        }
    }

    pub fn preprocess(&mut self) {
        //Remove clauses assigned from units
        self.clauses.retain(|clause| {
            !clause
                .literals
                .iter()
                .any(|lit| self.assig.contains_key(&lit.var))
        });

        //Pure lit elimination till saturation
        assert!(self.level == 0);
        let mut oldsize = self.clauses.len();
        self.pure_literal_elimination();
        while self.clauses.len() != oldsize {
            self.pure_literal_elimination();
            oldsize = self.clauses.len();
        }
        self.setup_watchlist();
        self.var_order = self.jsw();
    }
    fn get_lit_level(&self, lit: &Literal) -> usize {
        self.assig.get(&lit.var).unwrap().level
    }

    pub fn get_backtrack_level(&self, lits: &[Literal]) -> usize {
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
        match second_highest {
            None => highest.unwrap() - 1,
            Some(lvl) => lvl,
        }
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

        let mut blamed_decs: HashSet<Literal> = HashSet::from_iter(old_level_decs);
        let mut curset: HashSet<Literal> = HashSet::from_iter(cur_level_decs);

        while curset.len() != 1 {
            match self.pop_decision() {
                Decision {
                    lit: _,
                    unit_prop_idx: None,
                } => {
                    panic!("unreachable!");
                }
                Decision {
                    lit,
                    unit_prop_idx: Some(unit_idx),
                } => {
                    let lit_present = curset.remove(&lit);
                    if !lit_present {
                        continue;
                    }
                    for &negated_lit in self.clauses[unit_idx].literals.iter() {
                        let decided_lit = negated_lit.invert();
                        if decided_lit.var == lit.var {
                            continue;
                        }

                        let resp_lit_level = self.get_lit_level(&decided_lit);
                        if resp_lit_level < self.level {
                            blamed_decs.insert(decided_lit);
                        } else {
                            curset.insert(decided_lit);
                        }
                    }
                }
            }
        }
        //curset now has the UIP
        let &uip = curset.iter().next().unwrap();
        blamed_decs.insert(uip);

        let clause_lits: Vec<Literal> = blamed_decs.into_iter().map(|lit| lit.invert()).collect();

        let backtrack_level = self.get_backtrack_level(&clause_lits);

        if clause_lits.len() != 1 {
            let uip_idx = clause_lits.len() - 1;
            let new_clause = Clause {
                literals: clause_lits,
                w1: 0,
                w2: uip_idx,
            };
            let clauseset: HashSet<Literal> = HashSet::from_iter(new_clause.literals.clone());
            assert!(clauseset.len() == new_clause.literals.len());
            self.add_clause(new_clause);

            ConflictAnalysisResult::Backtrack {
                level: backtrack_level,
                unit_lit: uip.invert(),
                unit_idx: Some(self.clauses.len() - 1),
            }
        } else {
            ConflictAnalysisResult::Backtrack {
                level: backtrack_level,
                unit_lit: uip.invert(),
                unit_idx: None,
            }
        }

        //Find UIP
    }
    pub fn assigments_len(&self) -> usize {
        self.assig.len()
    }

    pub fn get_model(&self) -> Vec<i32> {
        let mut v: Vec<i32> = Vec::with_capacity(self.num_variables);
        for var in 1..=self.num_variables {
            let assigninfo = self.assig.get(&var).unwrap();
            v.push(var as i32 * if assigninfo.litsign { 1 } else { -1 });
        }
        v
    }

    pub fn check_watch_invariant(&self) {
        for clause in self.clauses.iter() {
            let l1 = clause.literals[clause.w1];
            let l2 = clause.literals[clause.w2];
            assert!(!(literal_falsified(&l1, &self.assig) && literal_falsified(&l2, &self.assig)));
        }
    }
}
#[cfg(test)]
mod tests;
