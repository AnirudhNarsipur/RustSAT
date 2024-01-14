use std::{fmt, vec};

#[derive(Clone, PartialEq, Eq, Hash, Copy)]
pub struct Literal {
    pub var: LiteralSize,
    pub sign: bool,
}

impl fmt::Display for Literal {
    // This trait requires `fmt` with this exact signature.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Write strictly the first element into the supplied output
        // stream: `f`. Returns `fmt::Result` which indicates whether the
        // operation succeeded or failed. Note that `write!` uses syntax which
        // is very similar to `println!`.
        let sign = if self.sign { "" } else { "-" };
        write!(f, "{}{}", sign, self.var)
    }
}
impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
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
impl AssigInfo {
    pub fn new(litsign: bool, level: usize) -> Self {
        Self { litsign, level }
    }
}
// pub type Assig = HashMap<LiteralSize, AssigInfo>;

#[derive(Debug, PartialEq)]
pub struct Assig {
    assn: Vec<Option<AssigInfo>>,
    ln: usize,
}

impl Assig {
    pub fn new(num_vars: usize) -> Self {
        Self {
            assn: vec![None; num_vars + 1],
            ln: 0,
        }
    }

    pub fn get(&self, var: &LiteralSize) -> Option<&AssigInfo> {
        self.assn[*var].as_ref()
    }

    pub fn insert(&mut self, var: LiteralSize, assig_info: AssigInfo) {
        self.assn[var] = Some(assig_info);
        self.ln += 1;
    }

    pub fn remove(&mut self, var: &LiteralSize) {
        self.ln -= 1;
        self.assn[*var] = None
    }

    pub fn contains_key(&self, var: &LiteralSize) -> bool {
        self.assn[*var].is_some()
    }

    pub fn keys(&self) -> impl Iterator<Item = LiteralSize> + '_ {
        self.assn.iter().enumerate().filter_map(
            |(idx, assig)| {
                if assig.is_some() {
                    Some(idx)
                } else {
                    None
                }
            },
        )
    }

    pub fn len(&self) -> usize {
        self.ln
    }
}
#[inline(always)]
pub fn literal_falsified(lit: &Literal, assig: &Assig) -> bool {
    match assig.assn[lit.var] {
        Some(b) => b.litsign != lit.sign,
        None => false,
    }
}

pub fn literal_satisfied(lit: &Literal, assig: &Assig) -> bool {
    match assig.assn[lit.var] {
        Some(b) => b.litsign == lit.sign,
        None => false,
    }
}
pub fn literal_unassigned(lit: &Literal, assig: &Assig) -> bool {
    assig.assn[lit.var].is_none()
}

pub fn check_clause_watch_invariant(clause: &Clause, assig: &Assig) -> bool {
    assert!(clause.w1 != clause.w2);
    assert!(
        !(literal_falsified(&clause.literals[clause.w1], assig)
            && literal_falsified(&clause.literals[clause.w2], assig))
    );
    true
}
pub fn check_single_unit(clause: &Clause, assig: &Assig, lit_idx: usize) -> bool {
    assert!(
        lit_idx < clause.literals.len(),
        "idx {} len {}",
        lit_idx,
        clause.literals.len()
    );
    assert_eq!(
        clause
            .literals
            .iter()
            .filter(|lit| literal_falsified(lit, assig))
            .count(),
        clause.literals.len() - 1
    );
    let unassigned_lit: Vec<Literal> = clause
        .literals
        .iter()
        .cloned()
        .filter(|lit| literal_unassigned(lit, assig))
        .collect();
    let cond = unassigned_lit.len() == 1;
    if !cond {
        assert!(
            false,
            "unassigned lit {:?} clause {:?} assigs: {:?}",
            unassigned_lit,
            clause,
            print_clause_lit_assigs(clause, assig)
        );
    }
    assert!(unassigned_lit[0] == clause.literals[lit_idx]);
    true
}

pub fn print_lit_assig(lit: &Literal, assig: &Assig) -> String {
    match assig.get(&lit.var) {
        Some(inf) => format!("Lit:{}:{},level:{}", lit.var, inf.litsign, inf.level),
        None => format!("Lit:{}:None", lit),
    }
}
pub fn print_clause_lit_assigs(clause: &Clause, assig: &Assig) -> String {
    let mut tmp = String::new();
    for lit in clause.literals.iter() {
        tmp.push_str(&format!("({:?}:{:?})", lit, assig.get(&lit.var)));
    }
    tmp
}
pub fn print_non_falsified_lits(clause: &Clause, assig: &Assig) -> String {
    let mut tmpstr = String::new();

    let tmp: Vec<Literal> = clause
        .literals
        .iter()
        .cloned()
        .filter(|lit| !literal_falsified(lit, assig))
        .collect();
    if !tmp.is_empty() {
        for lit in tmp {
            tmpstr.push_str(&print_lit_assig(&lit, assig));
        }
    }
    tmpstr
}

fn check_all_falsified(clause: &Clause, assig: &Assig) -> bool {
    let tmp: Vec<Literal> = clause
        .literals
        .iter()
        .cloned()
        .filter(|lit| !literal_falsified(lit, assig))
        .collect();
    assert!(
        tmp.is_empty(),
        "tmp is {:?} non false: {:?} watch1_assig: {:?} watch2_assig: {:?}",
        tmp,
        print_non_falsified_lits(clause, assig),
        print_lit_assig(&clause.literals[clause.w1], assig),
        print_lit_assig(&clause.literals[clause.w2], assig)
    );
    true
}

#[derive(Debug, Clone, PartialEq)]
pub struct Clause {
    pub literals: Vec<Literal>,
    pub w1: usize,
    pub w2: usize,
    pub deleted : bool,
    pub conflict : bool
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

impl TryFrom<Vec<Literal>> for Clause {
    type Error = &'static str;
    fn try_from(vc: Vec<Literal>) -> Result<Self, Self::Error> {
        if vc.len() < 2 {
            return Err("Must have at least 2 literals");
        }
        let lits = vc.into_iter().map(Literal::from).collect();
        Result::Ok(Self {
            literals: lits,
            w1: 0,
            w2: 1,
            deleted : false,
            conflict : false
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
            deleted:false,
            conflict:false
        }
    }
    pub fn clause_satisfied(&self, assig: &Assig) -> bool {
        self.literals
            .iter()
            .any(|lit| literal_satisfied(lit, assig))
    }

    pub fn reset_watch(&mut self, assig: &Assig, cur_idx: usize) -> Option<usize> {
        debug_assert!(cur_idx == self.w1 || cur_idx == self.w2);
        if !literal_falsified(&self.literals[cur_idx], assig) {
            return Some(cur_idx);
        }
        for (idx, lit) in self.literals.iter().enumerate() {
            if idx != self.w1 && idx != self.w2 && !literal_falsified(lit, assig) {
                if cur_idx == self.w1 {
                    self.w1 = idx;
                } else {
                    self.w2 = idx;
                }
                return Some(idx);
            }
        }
        None
    }

    pub fn set_unassigned_watches(&mut self, assig: &Assig) {
        let mut c = 0;
        if self.reset_watch(assig, self.w1).is_none() {
            c += 1;
        }

        if self.reset_watch(assig, self.w2).is_none() {
            c += 1;
        }
        debug_assert!(c == 0);

        debug_assert!(check_clause_watch_invariant(self, assig));
    }

    // #[inline(always)]
    pub fn unit_prop(&mut self, assig: &Assig, lit: &Literal) -> ClauseUnitProp {
        debug_assert!(literal_falsified(lit, assig));

        let (cur_idx, oidx) = match *lit {
            _ if self.literals[self.w1] == *lit => (self.w1, self.w2),
            _ if self.literals[self.w2] == *lit => (self.w2, self.w1),
            _ => unreachable!(),
        };
        
        let other_watch_lit = self.literals[oidx];

        if let Some(b) = assig.assn[other_watch_lit.var] {
            if b.litsign == other_watch_lit.sign {
                debug_assert!(check_clause_watch_invariant(self, assig));
                return ClauseUnitProp::Satisfied;
            } else {
                debug_assert!(check_all_falsified(self, assig));
                return ClauseUnitProp::Conflict;
            }
        }

        if let Some(nidx) = self.reset_watch(assig, cur_idx) {
            debug_assert!(!literal_falsified(&self.literals[nidx], assig));
            debug_assert!(check_clause_watch_invariant(self, assig));

            ClauseUnitProp::Reassigned {
                old_watch: *lit,
                new_watch: self.literals[nidx],
            }
        } else {
            debug_assert!(check_single_unit(self, assig, oidx));
            debug_assert!(check_clause_watch_invariant(self, assig));

            ClauseUnitProp::Unit {
                lit: self.literals[oidx],
            }
        }
    }
}

pub type LiteralSize = usize;

#[derive(Debug, Clone, PartialEq)]
pub struct VarWatch {
    false_watch: Vec<usize>,
    true_watch: Vec<usize>,
}
impl Default for VarWatch {
    fn default() -> Self {
        Self::new()
    }
}

impl VarWatch {
    pub fn new() -> Self {
        Self {
            false_watch: Vec::new(),
            true_watch: Vec::new(),
        }
    }
    pub fn remove_idx(&mut self, lit: bool, watch_idx: usize) {
        match lit {
            true => self.true_watch.swap_remove(watch_idx),
            false => self.false_watch.swap_remove(watch_idx),
        };
    }
    pub fn add_clause(&mut self, lit: bool, clause_idx: usize) {
        match lit {
            true => self.true_watch.push(clause_idx),
            false => self.false_watch.push(clause_idx),
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
    pub fn clear(&mut self) {
        self.watchlist.iter_mut().for_each(|vlist| {
            vlist.true_watch.clear();
            vlist.false_watch.clear()
        });
    }
    pub fn new(num_vars: usize) -> Self {
        Self {
            watchlist: vec![VarWatch::new(); num_vars + 1],
        }
    }
    pub fn add_to_list(&mut self, lit: &Literal, clause_idx: usize) {
        if lit.sign {
            self.watchlist[lit.var].true_watch.push(clause_idx);
        } else {
            self.watchlist[lit.var].false_watch.push(clause_idx);
        }
    }

    #[allow(dead_code)]
    pub fn get(&self, idx: usize) -> &VarWatch {
        &self.watchlist[idx]
    }
    pub fn get_lit(&self, lit: &Literal) -> &Vec<usize> {
        match lit.sign {
            true => &self.watchlist[lit.var].true_watch,
            false => &self.watchlist[lit.var].false_watch,
        }
    }

    pub fn remove_watch(&mut self, lit: &Literal, watch_idx: usize) {
        self.watchlist[lit.var].remove_idx(lit.sign, watch_idx);
    }
}

#[derive(Clone, PartialEq, Debug, Eq)]
pub enum Decision {
    AssertUnit { lit: Literal },
    UnitProp { lit: Literal, unit_prop_idx: usize },
    Choice { lit: Literal },
}

impl Decision {
    pub fn make_assertunit(lit: Literal) -> Self {
        Self::AssertUnit { lit }
    }
    pub fn make_unitprop(lit: Literal, unit_prop_idx: usize) -> Self {
        Self::UnitProp { lit, unit_prop_idx }
    }
    pub fn make_choice(lit: Literal) -> Self {
        Self::Choice { lit }
    }
    pub fn get_lit(&self) -> Literal {
        match self {
            Self::AssertUnit { lit } => *lit,
            Self::UnitProp { lit, .. } => *lit,
            Self::Choice { lit } => *lit,
        }
    }
}

pub enum ConflictAnalysisResult {
    UNSAT,
    Backtrack { decision: Decision },
}

#[derive(PartialEq, Debug)]
pub struct ParsedOut {
    pub num_variables: usize,
    pub num_clauses: usize,
    pub clauses: Vec<Vec<Literal>>,
}
