pub mod utils;

use std::{
    collections::{HashMap, HashSet, VecDeque},
    vec,
};
pub use utils::*;
pub mod heuristic;
pub enum FormulaPreprocess {
    TrivialUNSAT,
    Ok,
}

#[derive(PartialEq, Debug)]
pub struct SolverState {
    decision_stack: Vec<Decision>,
    pub assig: HashMap<LiteralSize, AssigInfo>,
    pub level: usize,
    watchlist: WatchList,
    pub num_variables: usize,
    pub clauses: Vec<Clause>,
    pub var_order: Vec<Literal>,
}

impl SolverState {
    fn make_new(num_vars: usize) -> Self {
        let dstack: Vec<Decision> = Vec::with_capacity(num_vars);

        Self {
            decision_stack: dstack,
            assig: HashMap::new(),
            level: 0,
            watchlist: WatchList::new(num_vars), //Initialize later
            num_variables: num_vars,
            clauses: Vec::new(),
            var_order: Vec::new(),
        }
    }

    pub fn from_parsed_out(parsed_out: ParsedOut) -> Self {
        let mut solver_state = Self::make_new(parsed_out.num_variables);
        for clause in parsed_out.clauses {
            solver_state.add_raw_clause(clause);
        }
        solver_state
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
    pub fn add_decision(&mut self, d: &Decision) -> () {
        assert!(!literal_falsified(&d.get_lit(), &self.assig));

        match d {
            Decision::AssertUnit { lit } => {
                // println!("Adding decision {:?} lvl: {}", d, 0);
                self.assig.insert(lit.var, AssigInfo::new(lit.sign, 0));
            }
            Decision::Choice { lit } => {
                self.level += 1;
                // println!("Adding decision {:?} lvl: {}", d, self.level);

                self.assig
                    .insert(lit.var, AssigInfo::new(lit.sign, self.level));
                self.decision_stack.push(d.clone());
            }
            Decision::UnitProp { lit, unit_prop_idx } => {
                assert!(*unit_prop_idx < self.clauses.len());
                // println!("Adding decision {:?} lvl: {}", d, self.level);

                self.assig
                    .insert(lit.var, AssigInfo::new(lit.sign, self.level));
                if self.level != 0 {
                    self.decision_stack.push(d.clone());
                }
            }
        }
    }
    pub fn add_decision_prop(&mut self, d: &Decision) -> FormulaUnitProp {
        self.add_decision(d);
        return self.unit_prop(d);
    }

    pub fn backtrack_to_level(&mut self, backtrack_level: usize) {
        assert!(backtrack_level < self.level);

        while self.level != backtrack_level {
            self.pop_decision();
        }
    }

    fn pop_decision(&mut self) -> Decision {
        return match self.decision_stack.pop() {
            Some(dec) => {
                // println!("Popping decision {:?} lvl: {}", dec, self.level);
                match dec {
                    Decision::AssertUnit { .. } => unreachable!(),
                    Decision::Choice { lit } => {
                        self.level -= 1;
                        self.assig.remove(&lit.var);
                        dec
                    }
                    Decision::UnitProp { lit, .. } => {
                        self.assig.remove(&lit.var);
                        dec
                    }
                }
            }
            None => unreachable!(),
        };
    }
    pub fn add_clause(&mut self, mut clause: Clause) {
        let clauseset = clause
            .literals
            .iter()
            .map(|lit| lit.var)
            .collect::<HashSet<LiteralSize>>();
        assert!(clauseset.len() == clause.literals.len());
        clause.set_unassigned_watches(&self.assig);
        self.watchlist
            .add_to_list(&clause.literals[clause.w1], self.clauses.len());
        self.watchlist
            .add_to_list(&clause.literals[clause.w2], self.clauses.len());
        self.clauses.push(clause);
    }
    pub fn add_conflict_clause(&mut self, mut clause: Clause, uip: Literal) {
        let clauseset = clause
            .literals
            .iter()
            .map(|lit| lit.var)
            .collect::<HashSet<LiteralSize>>();
        assert!(clauseset.len() == clause.literals.len());
        // let res = print_clause_lit_assigs(&clause, &self.assig);
        // println!("Cur level: {} {}", self.level, res);
        clause.w1 = clause
            .literals
            .iter()
            .position(|&lit| {
                self.assig
                    .get(&lit.var)
                    .is_some_and(|x| x.level == self.level)
            })
            .unwrap();
        clause.w2 = clause.literals.iter().position(|&lit| lit == uip).unwrap();
        assert!(clause.literals[clause.w2] == uip);

        self.watchlist
            .add_to_list(&clause.literals[clause.w1], self.clauses.len());
        self.watchlist
            .add_to_list(&clause.literals[clause.w2], self.clauses.len());

        self.clauses.push(clause);
    }
    pub fn add_raw_clause(&mut self, mut raw_clause: Vec<Literal>) -> bool {
        let mut set = HashSet::new();
        raw_clause.retain(|e| set.insert(*e));

        if raw_clause.len() == 1 {
            let unit: Literal = Literal::from(raw_clause[0]);
            let d = Decision::make_assertunit(unit);
            self.add_decision(&d);
        } else {
            let clause = Clause::try_from(raw_clause).unwrap();
            self.add_clause(clause);
        }
        true
    }
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    pub fn unit_prop(&mut self, blame: &Decision) -> FormulaUnitProp {
        let mut units_queue = VecDeque::from([blame.clone()]);
        // maintain a seperate set from the assignments because we want the chronology to be correct -
        // all parents lits in the implication graph should precede the given lit without ^ that would break

        let mut seen_new_units: HashSet<Literal> = HashSet::from([blame.get_lit()]);
        let mut add_unit: bool = false;
        while !units_queue.is_empty() {
            let d = units_queue.pop_front().unwrap();
            let unit = d.get_lit();
            let unit_inverted = unit.invert();

            if add_unit {
                self.add_decision(&d);
            }
            assert!(literal_satisfied(&unit, &self.assig));
            for &clause_idx in self.watchlist.get_lit(&unit_inverted).clone().iter() {
                let clause = self.clauses.get_mut(clause_idx).unwrap();
                assert!(literal_falsified(&unit_inverted, &self.assig));

                match clause.unit_prop(&self.assig, &unit_inverted) {
                    ClauseUnitProp::Reassigned {
                        old_watch,
                        new_watch,
                    } => {
                        assert!(clause.literals.iter().find(|&x| *x == new_watch).is_some());
                        self.watchlist.move_watch(old_watch, new_watch, clause_idx);
                    }
                    ClauseUnitProp::Satisfied => continue,
                    ClauseUnitProp::Unit { lit } => {
                        if seen_new_units.contains(&lit) || self.assig.contains_key(&lit.var) {
                            continue;
                        }
                        units_queue.push_back(Decision::make_unitprop(lit, clause_idx));
                        seen_new_units.insert(lit);
                    }
                    ClauseUnitProp::Conflict => {
                        return FormulaUnitProp::Conflict {
                            conflict_cause_idx: clause_idx,
                        };
                    }
                }
            }
            //After the first add all the rest
            add_unit = true;
        }
        FormulaUnitProp::Ok
    }
    pub fn reset_watchlist(&mut self) {
        self.watchlist.clear();
        for (idx, clause) in self.clauses.iter_mut().enumerate() {
            clause.set_unassigned_watches(&self.assig);
            self.watchlist.add_to_list(&clause.literals[clause.w1], idx);
            self.watchlist.add_to_list(&clause.literals[clause.w2], idx);
        }
    }
 

    pub fn preprocess(&mut self) -> FormulaPreprocess {
        assert!(self.decision_stack.len() == 0);
        let orig_len = self.clauses.len();
        //Unit prop all the unit clauses and then remove them
        let  unit_vars: HashSet<Literal> = self
            .assig
            .keys()
            .map(|&var| Literal {
                var,
                sign: self.assig.get(&var).unwrap().litsign,
            })
            .collect();

        for &lit in unit_vars.iter() {
            let unit = Decision::make_assertunit(lit);
            assert!(literal_satisfied(&lit, &self.assig) || literal_unassigned(&lit, &self.assig));
            if let FormulaUnitProp::Conflict { .. } = self.unit_prop(&unit) {
                return FormulaPreprocess::TrivialUNSAT;
            }
        }
        self.clauses
            .retain(|clause| !clause.clause_satisfied(&self.assig));

        self.var_order = self.jsw();

        self.reset_watchlist();
        self.check_watch_invariant();

        println!(
            "Original : {} now : {} removed: {} ",
            orig_len,
            self.clauses.len(),
            orig_len - self.clauses.len()
        );
        FormulaPreprocess::Ok
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
            None => 0,
            Some(lvl) => lvl,
        }
    }

    fn check_new_clause(&self, new_clause: &Clause) {
        let clauseset: HashSet<Literal> = HashSet::from_iter(new_clause.literals.clone());
        assert!(clauseset.len() == new_clause.literals.len());
        assert_eq!(
            new_clause
                .literals
                .iter()
                .filter(|lit| literal_falsified(lit, &self.assig))
                .count(),
            new_clause.literals.len() - 1
        );
        //Only 1 lit from current level
        assert_eq!(
            new_clause
                .literals
                .iter()
                .filter(|lit| literal_unassigned(lit, &self.assig))
                .count(),
            1
        );
    }

    fn create_conflict_clause(&self, clause_lits: Vec<Literal>) -> Clause {
        let uip_idx = clause_lits.len() - 1;
        let new_clause = Clause {
            literals: clause_lits,
            w1: 0,
            w2: uip_idx,
        };
        self.check_new_clause(&new_clause);
        new_clause
    }
    fn check_conflict_clause(&self, conflict_clause: &Clause) {
        print_non_falsified_lits(&conflict_clause, &self.assig);
        assert!(conflict_clause
            .literals
            .iter()
            .all(|lit| literal_falsified(lit, &self.assig)));
    }
    pub fn analyze_conflict_backtrack(&mut self, conflict_idx: usize) -> ConflictAnalysisResult {
        if self.level == 0 {
            return ConflictAnalysisResult::UNSAT;
        }
        let conflict_clause = &self.clauses[conflict_idx];

        self.check_conflict_clause(&conflict_clause);

        let blamed_decisions: Vec<Literal> = conflict_clause
            .literals
            .iter()
            .map(|lit| lit.invert())
            .collect();
        let (cur_level_decs, old_level_decs): (Vec<Literal>, Vec<Literal>) = blamed_decisions
            .into_iter()
            .partition(|lit| self.assig.get(&lit.var).unwrap().level == self.level);

        assert!(cur_level_decs.len() >= 1);
        let mut blamed_decs: HashSet<Literal> = HashSet::from_iter(old_level_decs);
        let mut curset: HashSet<Literal> = HashSet::from_iter(cur_level_decs);
        assert!(
            curset.len() >= 1,
            "{}",
            print_clause_lit_assigs(&conflict_clause, &self.assig)
        );
        assert!(curset.iter().all(|lit| self.assig.get(&lit.var).unwrap().level == self.level));
        while curset.len() > 1 {
            match self.pop_decision() {
                Decision::UnitProp {
                    lit,
                    unit_prop_idx: unit_idx,
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
                        
                        if 0 < resp_lit_level && resp_lit_level < self.level {
                            blamed_decs.insert(decided_lit);
                        } else if resp_lit_level == self.level{
                            curset.insert(decided_lit);
                        }
                    }
                }
                d => {
                    print!("Level is {} Curset has: ",self.level);
                    for lit in curset.iter() {
                        print!(" {} ",print_lit_assig(&lit, &self.assig));
                    }
                    println!();
                    unreachable!("Got unexpected {:?} ", d);
                }
            }
        }
        //curset now has the UIP
        let &uip = curset.iter().next().unwrap();
        blamed_decs.insert(uip);

        let clause_lits: Vec<Literal> = blamed_decs.into_iter().map(|lit| lit.invert()).collect();
        let backtrack_level = self.get_backtrack_level(&clause_lits);
        self.backtrack_to_level(backtrack_level);
        let d = if clause_lits.len() != 1 {
            let new_clause = self.create_conflict_clause(clause_lits);
            self.add_conflict_clause(new_clause, uip.invert());
            Decision::make_unitprop(uip.invert(), self.clauses.len() - 1)
        } else {
            assert_eq!(self.level,0);
            Decision::make_assertunit(uip.invert())
        };
        self.add_decision(&d);
        ConflictAnalysisResult::Backtrack { decision: d }
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

    pub fn check_watch_invariant(&self) -> bool {
        for (idx, clause) in self.clauses.iter().enumerate() {
            assert!(idx < self.clauses.len());

            let l1 = clause.literals[clause.w1];
            let l2 = clause.literals[clause.w2];

            assert!(self.watchlist.watchlist[l1.var].has(idx));
            assert!(self.watchlist.watchlist[l2.var].has(idx));
            //both have to be unassigned or one of them has to be true
            let invariant = (literal_unassigned(&l1, &self.assig)
                && literal_unassigned(&l2, &self.assig))
                || (literal_satisfied(&l1, &self.assig) || literal_satisfied(&l2, &self.assig));

            if !invariant {
                println!("Idx is {} ", idx);
                println!(
                    "Failed at idx {} lits: {:?} assigs are {}:{:?} , {}:{:?}",
                    idx,
                    clause.literals,
                    l1,
                    self.assig.get(&l1.var),
                    l2,
                    self.assig.get(&l2.var)
                );
                assert!(false);
            }

        }
        return  true;
    }
}

#[cfg(test)]
mod tests;
