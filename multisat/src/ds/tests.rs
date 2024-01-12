use super::*;

#[test]
fn literal_struct_tests() {
    let l1 = Literal::make_new("12");
    assert_eq!(
        l1,
        Literal {
            var: 12,
            sign: true
        }
    );

    let l2 = Literal::make_new("-15");
    assert_eq!(
        l2,
        Literal {
            var: 15,
            sign: false
        }
    );

    assert_eq!(l1.is_negative(), false);
    assert_eq!(l2.is_negative(), true);

    assert_eq!(
        l1.invert(),
        Literal {
            var: 12,
            sign: false
        }
    );
    assert_eq!(
        l2.invert(),
        Literal {
            var: 15,
            sign: true
        }
    );
}

#[test]
fn literal_falsified_tests() {
    let assig = HashMap::from([
        (
            1,
            AssigInfo {
                litsign: true,
                level: 0,
            },
        ),
        (
            2,
            AssigInfo {
                litsign: false,
                level: 5,
            },
        ),
    ]);
    assert!(!literal_falsified(&Literal { var: 1, sign: true }, &assig));
    assert!(literal_falsified(
        &Literal {
            var: 1,
            sign: false
        },
        &assig
    ));

    assert!(!literal_falsified(
        &Literal {
            var: 2,
            sign: false
        },
        &assig
    ));
    assert!(literal_falsified(&Literal { var: 2, sign: true }, &assig));

    assert!(!literal_falsified(
        &Literal {
            var: 3,
            sign: false
        },
        &assig
    ));
    assert!(!literal_falsified(&Literal { var: 3, sign: true }, &assig));
}

#[test]
fn make_clause_test() {
    let c_raw1 = vec!["-1", "19", "-8", "0"];
    let c1 = Clause {
        literals: vec![
            Literal {
                var: 1,
                sign: false,
            },
            Literal {
                var: 19,
                sign: true,
            },
            Literal {
                var: 8,
                sign: false,
            },
        ],
        w1: 0,
        w2: 1,
    };
    assert_eq!(Clause::make_clause(c_raw1), c1);
}

#[test]
fn unit_prop_conflict_test() {
    let mut clause = Clause::try_from(vec![1, -2]).unwrap();
    let mut assig: Assig = HashMap::new();
    assig.insert(
        1,
        AssigInfo {
            litsign: false,
            level: 2,
        },
    );
    assig.insert(
        2,
        AssigInfo {
            litsign: true,
            level: 1,
        },
    );

    let result = clause.unit_prop(&assig, &Literal::from(1));
    match result {
        ClauseUnitProp::Conflict => assert!(true),
        _ => assert!(false, "Expected conflict but got {:?}", result),
    }
}

#[test]
fn unit_prop_reassigned_test() {
    let mut clause = Clause::try_from(vec![-1, 3, -19]).unwrap();
    let mut assig: Assig = HashMap::new();
    assig.insert(
        1,
        AssigInfo {
            litsign: true,
            level: 2,
        },
    );

    let result = clause.unit_prop(&assig, &Literal::from(-1));
    match result {
        ClauseUnitProp::Reassigned{old_watch: _,new_watch: _} => assert!(clause.w1 == 2),
        _ => assert!(false, "Expected reassigned but got {:?}", result),
    }
}

#[test]
fn unit_prop_new_unit_test() {
    let mut clause = Clause::try_from(vec![-11, -22]).unwrap();
    let mut assig: Assig = HashMap::new();
    assig.insert(
        22,
        AssigInfo {
            litsign: true,
            level: 2,
        },
    );

    let result = clause.unit_prop(&assig, &Literal::from(-22));
    match result {
        ClauseUnitProp::Unit { lit } => assert_eq!(lit, Literal::from(-11)),
        _ => assert!(false, "Expected new unit but got {:?}", result),
    }
}

#[test]
fn unit_prop_satisfied_test() {
    let mut clause = Clause::try_from(vec![-11, -22]).unwrap();
    let mut assig: Assig = HashMap::new();
    assig.insert(
        22,
        AssigInfo {
            litsign: false,
            level: 2,
        },
    );
    assig.insert(
        11,
        AssigInfo {
            litsign: true,
            level: 3,
        },
    );
    let result = clause.unit_prop(&assig, &Literal::from(-11));
    match result {
        ClauseUnitProp::Satisfied => assert!(true),
        _ => assert!(false, "Expected new unit but got {:?}", result),
    }
}

#[test]
fn solver_state_new() {
    let s = SolverState::make_new(5);
    assert_eq!(s.level, 0);
    assert!(s.decision_stack.is_empty());
    assert!(s.assig.is_empty());
}

#[test]
fn add_decision_test() {
    let mut s = SolverState::make_new(10);
    let lit = Literal::from(-16);
    let d = Decision {
        lit: lit,
        unit_prop_idx: None,
    };
    let expected_assig = AssigInfo {
        litsign: lit.sign,
        level: 1,
    };
    s.add_decision_prop(&d);
    assert_eq!(s.decision_stack[0], d);
    let actual_assig = s.assig.get(&lit.var);
    assert!(actual_assig.map_or(false, |&a| a == expected_assig));
    assert!(s.level == 1);
}

#[test]
fn add_unit_test() {
    let mut s = SolverState::make_new(10);
    let lit = Literal::from(20);
    let d = Decision {
        lit: lit,
        unit_prop_idx: Some(21),
    };
    let expected_assig = AssigInfo {
        litsign: lit.sign,
        level: s.level,
    };
    s.add_decision_prop(&d);
    assert_eq!(s.decision_stack[0], d);
    let actual_assig = s.assig.get(&lit.var);
    assert!(actual_assig.map_or(false, |&a| a == expected_assig));
    assert!(s.level == 0);
}

#[test]
fn test_pop_decision() {
    let mut s = SolverState::make_new(10);
    let d1 = Decision {
        lit: Literal::from(-9),
        unit_prop_idx: None,
    };
    let d2 = Decision {
        lit: Literal::from(20),
        unit_prop_idx: Some(42),
    };
    s.add_decision_prop(&d1);
    s.add_decision_prop(&d2);
    assert!(s.level == 1);
    assert_eq!(s.pop_decision(), d2);
    assert!(s.level == 1);
    assert_eq!(s.pop_decision(), d1);
    assert!(s.level == 0);
}

#[test]
fn test_add_raw_clause() { 
    let mut s = SolverState::make_new(15);
    let c_raw1 = vec!["-3","5","-7","0"];
    let c1 = Clause::try_from(vec![-3,5,-7]).unwrap();
    s.add_raw_clause(c_raw1);
    assert_eq!(s.clauses[0], c1);
    assert_eq!(s.watchlist.watchlist.len(),0);
    s.setup_watchlist();
    assert_eq!(*s.watchlist.get(3).false_watch.iter().next().unwrap(), 0);
    assert_eq!(*s.watchlist.get(5).true_watch.iter().next().unwrap(), 0);


    let c_raw2 = vec!["-2","0"]; 
    s.add_raw_clause(c_raw2);
    assert_eq!(s.clauses.len(),1) ; //clause len does not change
    assert_eq!(s.decision_stack.len(), 0); //decision stack does not change
    assert_eq!(*s.assig.get( &2).unwrap(), AssigInfo{litsign: false, level: 0});

}

#[test]
fn test_pure_literal_elimination() {
    //2 is the only pure literal
    let c1 = Clause::try_from(vec![1,-2,3]).unwrap();
    let c2 = Clause::try_from(vec![-1,-3]).unwrap();
    let c3 = Clause::try_from(vec![-2,5]).unwrap();
    let c4 = Clause::try_from(vec![-3,-5]).unwrap();
    let mut s = SolverState::make_new(5);
    let expected_clauses = vec![c2.clone(),c4.clone()];
    for c in vec![c1,c2,c3,c4] {
        s.add_clause(c);
    }
    s.pure_literal_elimination();
    assert_eq!(s.clauses, expected_clauses); // not sure if this equality is right 
}

#[test]
fn test_formula_unit_prop_duplicate_units() { 
    let c1 = Clause::try_from(vec![-1,-2]).unwrap();
    let c2 = Clause::try_from(vec![-1,-3,-2]).unwrap();

    let mut s = SolverState::make_new(3);
    s.add_clause(c1);
    s.add_clause(c2);
    s.setup_watchlist();
    let d1 =  Decision::new(3, None);
    s.add_decision_prop(&d1);
    assert_eq!(s.unit_prop(&d1),FormulaUnitProp::Ok);
    let d2 = Decision::new(1,None);
    s.add_decision_prop(&d2);
    assert_eq!(s.unit_prop(&d2),FormulaUnitProp::Ok);
    // Assignments are now 1,-2,3
    assert_eq!(HashSet::from_iter(s.get_model()), HashSet::from([1,-2,3]));

}

#[test]
fn test_watchlist_reassigned_correctly(){

    let c1 = Clause::try_from(vec![-1,-2]).unwrap();
    let c2 = Clause::try_from(vec![-1,-3,-2]).unwrap();

    let mut s = SolverState::make_new(3);
    s.add_clause(c1);
    s.add_clause(c2);
    s.setup_watchlist();
    let d1 =  Decision::new(3, None);
    s.add_decision_prop(&d1);

    assert!(!s.watchlist.get(2).false_watch.contains(&(1)));
    assert!(s.watchlist.get(3).false_watch.contains(&(1)));

    assert_eq!(s.unit_prop(&d1),FormulaUnitProp::Ok);

    assert!(s.watchlist.get(2).false_watch.contains(&(1)));
    assert!(!s.watchlist.get(3).false_watch.contains(&(1)));
  
}