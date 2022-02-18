use egg::{rewrite, Analysis, DidMerge, Id, Language, Pattern, Rewrite, Runner, RecExpr};
use primitive_types::U256;
use rand::seq::SliceRandom;
use rand::{thread_rng, Rng};
use rust_evm::{eval_evm, EVM};
use std::time::Duration;


use serde_json::{Value};

pub fn get_pregenerated_rules() -> Vec<(String, String)> {
    let contents = include_str!("./ruler-rules.json");
    let json = serde_json::from_str(&contents).unwrap();
    match json {
        Value::Object(map) => {
            let eqs = map.get("all_eqs").unwrap();
            if let Value::Array(rules) = eqs {
                let mut res = vec![];

                for entry in rules {
                    if let Value::Object(rule) = entry {
                        let lhs = rule.get("lhs").unwrap();
                        let rhs = rule.get("rhs").unwrap();
                        if let Value::String(lhs) = lhs {
                            if let Value::String(rhs) = rhs {
                                if let Value::Bool(bidrectional) = rule.get("bidirectional").unwrap() {
                                    res.push((lhs.to_string(), rhs.to_string()));
                                    if *bidrectional {
                                        res.push((rhs.to_string(), lhs.to_string()));
                                    }
                                }
                                
                            }
                        }
                    } else {
                        panic!("invalid entry in rules");
                    }
                }



                res.push(("(* ?a (+ ?b ?c))".to_string(), "(+ (* ?a ?b) (* ?a ?c))".to_string()));


                res
            } else {
                panic!("expected array from json all_eqs");
            }
        }
        _ => panic!("invalid json"),
    }
}



pub fn start_logical_pair(expr1: String, expr2: String, timeout: u64) -> (bool, bool) {
    if expr1 == expr2 {
        return (true, true);
    }
    let expr1 = expr1.parse().unwrap();
    let expr2 = expr2.parse().unwrap();
    let mut runner = LogicalRunner::new();
    runner.add_pair(&expr1, &expr2);
    if runner.are_unequal_fuzzing(&expr1, &expr2) {
        return (false, true);
    }

    runner.run(timeout);

    (runner.are_equal(&expr1, &expr2), false)
}

pub fn start_logical(expr1: String, expr2: String, timeout: u64) -> String {
    let res = start_logical_pair(expr1, expr2, timeout);
    format!("({} {})", res.0, res.1)
}

pub fn logical_rules() -> Vec<Rewrite<EVM, LogicalAnalysis>> {
    let str_rules = get_pregenerated_rules();
    let mut res = vec![];
    for (index, (lhs, rhs)) in str_rules.into_iter().enumerate() {
        let lparsed: Pattern<EVM> = lhs.parse().unwrap();
        let rparsed: Pattern<EVM> = rhs.parse().unwrap();
        res.push(
            Rewrite::<EVM, LogicalAnalysis>::new(index.to_string(), lparsed, rparsed).unwrap(),
        );
    }

    let manual_rules = vec![
        rewrite!("distr*+"; "(* (+ ?a ?b) ?c)" => "(+ (* ?a ?c) (* ?b ?c))"),
        rewrite!("doubleneg!=="; "(! (== (== ?x ?y) 0))" => "(== ?x ?y)"),
    ];
    for rule in manual_rules {
        res.push(rule);
    }

<<<<<<< HEAD
=======
    let manual_rules = vec![
        rewrite!("distr*+"; "(* (+ ?a ?b) ?c)" => "(+ (* ?a ?c) (* ?b ?c))"),
        rewrite!("doubleneg!=="; "(! (== (== ?x ?y) 0))" => "(== ?x ?y)"),
    ];
    for rule in manual_rules {
        res.push(rule);
    }

>>>>>>> cnandi/lin-invs
    res
}

type EGraph = egg::EGraph<EVM, LogicalAnalysis>;

#[derive(Default, Debug, Clone)]
pub struct Data {
    cvec: Vec<U256>,
    constant: Option<U256>,
}

fn random_256() -> U256 {
    let mut rng = rand::thread_rng();
    let lower = U256::from_dec_str(&rng.gen::<u128>().to_string()).unwrap();
    let dummy_vec: [Id; 2] = [Id::from(0), Id::from(0)];
<<<<<<< HEAD
    let upper = eval_evm(
        &EVM::ShiftLeft(dummy_vec),
        Some(lower),
        Some(U256::from_dec_str("128").unwrap()),
    )
    .unwrap();
=======
    let upper = eval_evm(&EVM::ShiftLeft(dummy_vec), Some(lower), Some(U256::from_dec_str("128").unwrap())).unwrap();
>>>>>>> cnandi/lin-invs
    let lower_2 = U256::from_dec_str(&rng.gen::<u128>().to_string()).unwrap();
    eval_evm(&EVM::BWOr(dummy_vec), Some(lower_2), Some(upper)).unwrap()
}

const CVEC_LEN: usize = 30;

#[derive(Default, Debug, Clone)]
pub struct LogicalAnalysis {
    special_constants: Vec<U256>,
    cvec_enabled: bool,
}
impl Analysis<EVM> for LogicalAnalysis {
    type Data = Data;

    fn make(egraph: &EGraph, enode: &EVM) -> Self::Data {
        // cvec computation turned off because we just do fuzzing
        let cvec = if egraph.analysis.cvec_enabled {
            match enode {
                EVM::Var(_) => {
                    let mut cvec = vec![];
                    for c in &egraph.analysis.special_constants {
                        cvec.push(*c);
                    }
<<<<<<< HEAD
                    // randomize order of constants
=======
                    // randomize order of constants 
>>>>>>> cnandi/lin-invs
                    cvec.shuffle(&mut thread_rng());
                    for c in &egraph.analysis.special_constants {
                        cvec.push(*c);
                    }
                    for _i in 0..(CVEC_LEN.checked_sub(cvec.len()).unwrap_or(0)) {
                        cvec.push(random_256());
                    }
<<<<<<< HEAD

                    cvec
=======
                    
                    Some(cvec)
>>>>>>> cnandi/lin-invs
                }
                _ => {
                    let mut cvec = vec![];
                    let mut child_const = vec![];
<<<<<<< HEAD
                    enode.for_each(|child| child_const.push(&egraph[child].data.cvec));
                    for i in 0..CVEC_LEN {
                        let first = child_const.get(0).map(|v| v.get(i).unwrap().clone());
                        let second = child_const.get(1).map(|v| v.get(i).unwrap().clone());

                        cvec.push(eval_evm(enode, first, second).unwrap())
                    }
                    cvec
                }
            }
        } else {
            vec![]
=======
                    enode.for_each(|child| child_const.push(egraph[child].data.cvec.as_ref()));
                    for i in 0..CVEC_LEN {
                        let first = child_const.get(0).unwrap_or(&None)
                            .map(|v| *v.get(i).unwrap());
                        let second = child_const.get(1).unwrap_or(&None)
                            .map(|v| *v.get(i).unwrap());
                                            
                        cvec.push(eval_evm(enode, first, second))
                    }
                    match cvec[0] {
                        Some(_) => {
                            Some(cvec.into_iter().map(|v| v.unwrap()).collect())
                        }
                        _ => None
                    }
                }
            }
        } else {
            None   
>>>>>>> cnandi/lin-invs
        };

        let mut child_const = vec![];
        enode.for_each(|child| child_const.push(egraph[child].data.constant));
        let first = child_const.get(0).unwrap_or(&None);
        let second = child_const.get(1).unwrap_or(&None);
        let constant = eval_evm(enode, *first, *second);

        Data { cvec, constant }
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        let mut merge_l = false;
        let mut merge_r = false;
        match (to.constant, from.constant) {
            (None, Some(b)) => {
                to.constant = Some(b.clone());
                merge_l = true;
            }
            (None, None) => (),
            (Some(_), None) => {
                merge_r = true;
            }
            (Some(a), Some(b)) => assert_eq!(a, b),
        }

        DidMerge(merge_l, merge_r)
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        let class = &mut egraph[id];
        if let Some(c) = class.data.constant {
            let added = egraph.add(EVM::from(c));
            egraph.union(id, added);
            assert!(
                !egraph[id].nodes.is_empty(),
                "empty eclass! {:#?}",
                egraph[id]
            );
        }
    }
}

#[derive(Debug)]
pub struct LogicalRunner {
    egraph: EGraph,
    fuzzing_egraph: EGraph,
    exprs: Vec<(RecExpr<EVM>, RecExpr<EVM>)>,
}

impl LogicalRunner {
    pub fn new() -> Self {
        let constants = vec![
            U256::zero(),
            U256::one(),
            U256::zero().overflowing_sub(U256::one()).0,
        ];
        let mut analysis = LogicalAnalysis::default();
        analysis.special_constants = constants;
        analysis.cvec_enabled = true;
        LogicalRunner {
            egraph: EGraph::new(LogicalAnalysis::default()),
            fuzzing_egraph: EGraph::new(analysis),
            exprs: vec![],
        }
    }

    fn add_constants(egraph: &mut EGraph, expr: &RecExpr<EVM>) {
        for node in expr.as_ref() {
            match node {
                EVM::Num(c) => {
                    egraph.analysis.special_constants.push(c.value);
                    egraph
                        .analysis
                        .special_constants
                        .push(c.value.overflowing_add(U256::one()).0);
                    egraph
                        .analysis
                        .special_constants
                        .push(c.value.overflowing_sub(U256::one()).0);
                }
                _ => (),
            }
<<<<<<< HEAD
=======
            s.push_str(")");
            s
>>>>>>> cnandi/lin-invs
        }
    }

<<<<<<< HEAD
    pub fn add_expr(&mut self, expr: &RecExpr<EVM>) {
        self.egraph.add_expr(expr);
        LogicalRunner::add_constants(&mut self.fuzzing_egraph, expr);
    }

    pub fn add_pair(&mut self, expr1: &RecExpr<EVM>, expr2: &RecExpr<EVM>) {
        self.add_expr(expr1);
        self.add_expr(expr2);
        self.exprs.push((expr1.clone(), expr2.clone()));
    }

    pub fn are_unequal_fuzzing(&mut self, lhs: &RecExpr<EVM>, rhs: &RecExpr<EVM>) -> bool {
        let start_f = self.fuzzing_egraph.add_expr(lhs);
        let end_f = self.fuzzing_egraph.add_expr(rhs);
        self.fuzzing_egraph.rebuild();
        let leftvec = &self.fuzzing_egraph[start_f].data.cvec;
        let rightvec = &self.fuzzing_egraph[end_f].data.cvec;
=======
#[derive(Debug)]
pub struct LogicalRunner {
    egraph: RwLock<EGraph>,
    fuzzing_egraph: RwLock<EGraph>,
    exprs: RwLock<Vec<(String, String)>>,
}

impl LogicalRunner {
    pub fn new() -> Self {
        let constants = vec![U256::zero(),
                            U256::one(),
                            U256::zero().overflowing_sub(U256::one()).0];
        let mut analysis = LogicalAnalysis::default();
        analysis.special_constants = constants;
        analysis.cvec_enabled = true;
        LogicalRunner {
            egraph: RwLock::new(EGraph::new(LogicalAnalysis::default())),
            fuzzing_egraph: RwLock::new(EGraph::new(analysis)),
            exprs: RwLock::new(vec![]),
        }
    }

    fn add_constants(egraph: &mut EGraph, expr: &egg::RecExpr<EVM>) {
        for node in expr.as_ref() {
            match node {
                EVM::Num(c) => {
                    egraph.analysis.special_constants.push(c.value);
                    egraph.analysis.special_constants.push(c.value.overflowing_add(U256::one()).0);
                    egraph.analysis.special_constants.push(c.value.overflowing_sub(U256::one()).0);
                }
                _ => ()
            }
        }
    }

    pub fn add_expr(&self, expr: String) {
        let mut egraph = self.egraph.write().unwrap();
        let mut fuzzing_egraph = self.fuzzing_egraph.write().unwrap();
        let l_parsed: egg::RecExpr<EVM> = expr.parse().unwrap();
        egraph.add_expr(&l_parsed);
        fuzzing_egraph.add_expr(&l_parsed);
        LogicalRunner::add_constants(&mut fuzzing_egraph, &l_parsed);
    }

    pub fn add_pair(&self, expr1: String, expr2: String) {
        self.add_expr(expr1.clone());
        self.add_expr(expr2.clone());
        let mut exprs = self.exprs.write().unwrap();
        exprs.push((expr1, expr2));
    }

    pub fn are_unequal_fuzzing(&self, lhs: String, rhs: String) -> bool {
        let mut fuzzing_egraph = self.fuzzing_egraph.write().unwrap();
        let start_f = fuzzing_egraph.add_expr(&lhs.parse().unwrap());
        let end_f = fuzzing_egraph.add_expr(&rhs.parse().unwrap());
        fuzzing_egraph.rebuild();
        let leftvec = fuzzing_egraph[start_f].data.cvec.as_ref();
        let rightvec = fuzzing_egraph[end_f].data.cvec.as_ref();
>>>>>>> cnandi/lin-invs
        if leftvec != rightvec {
            true
        } else {
            false
        }
    }

<<<<<<< HEAD
    pub fn are_equal(&mut self, lhs: &RecExpr<EVM>, rhs: &RecExpr<EVM>) -> bool {
        let start = self.egraph.add_expr(lhs);
        let end = self.egraph.add_expr(rhs);
        let result = start == end;

        return result;
    }

    pub fn run(&mut self, timeout: u64) {
        let exprs_check = self.exprs.clone();
        let mut runner: Runner<EVM, LogicalAnalysis> = Runner::new(LogicalAnalysis::default())
            .with_egraph(self.egraph.clone())
=======
    pub fn are_equal(&self, lhs: String, rhs: String) -> bool {
        let mut egraph = self.egraph.write().unwrap();
        
        let start = egraph.add_expr(&lhs.parse().unwrap());
        let end = egraph.add_expr(&rhs.parse().unwrap());
        egraph.rebuild();
        let result = start == end;

        return result
    }

    pub fn run(&self, timeout: u64) {
        let egraph = self.egraph.read().unwrap().clone();
        let exprs_check = self.exprs.read().unwrap().clone();
        let mut runner: Runner<EVM, LogicalAnalysis> = Runner::new(LogicalAnalysis::default())
            .with_egraph(egraph)
>>>>>>> cnandi/lin-invs
            .with_node_limit(1_000_000)
            .with_time_limit(Duration::from_millis(timeout))
            .with_iter_limit(usize::MAX)
            .with_hook(move |runner| {
                let mut done = true;
                for (expr1, expr2) in &exprs_check {
<<<<<<< HEAD
                    if runner.egraph.add_expr(&expr1)
                        != runner.egraph.add_expr(&expr2)
                    {
=======
                    if runner.egraph.add_expr(&expr1.parse().unwrap()) != runner.egraph.add_expr(&expr2.parse().unwrap()) {
>>>>>>> cnandi/lin-invs
                        done = false;
                        break;
                    }
                }
                if done {
                    Err("All equal".to_string())
                } else {
                    Ok(())
                }
            });
<<<<<<< HEAD

        runner = runner.run(&logical_rules());
        self.egraph = runner.egraph;
=======
        
        runner = runner.run(&logical_rules());
        *self.egraph.write().unwrap() = runner.egraph;
>>>>>>> cnandi/lin-invs
    }
}

#[cfg(test)]
mod tests {
<<<<<<< HEAD
    use super::*;

    #[test]
    fn logical_proves_equal() {
        let queries = vec![
            ("(+ 1 1)", "2"),
            ("(- a 1)", "(+ a (- 0 1))"),
            ("(* (- c 1) 32)", "(- (* c 32) 32)"),
            ("(- (+ a (+ b (* c 32))) (+ a (+ b (* (- c 1) 32))))", "32"),
            (
                "(- (+ a (+ b (* longname 32))) (+ a (+ b (* (- longname 1) 32))))",
                "32",
            ),
            (
                "(! (== (== 3264763256 tacSighash) 0))",
                "(== 3264763256 tacSighash)",
            ),
            ("(== (! (== certoraOutVar0bv256 0)) 0)", "(== certoraOutVar0bv256 0)"),
        ];
        for (lhs, rhs) in queries {
            let res = start_logical_pair(lhs.to_string(), rhs.to_string(), 8000);
            if !res.0 {
                if res.1 {
                    panic!(
                        "Proved unequal: {} and {}",
                        lhs,
                        rhs,
                    );
                }
=======
    use crate::*;
    use crate::logical_equality::{LogicalRunner};

    #[test]
    fn logical_simple() {
        let queries = vec![("(+ 1 1)", "2"),
                           ("(- a 1)", "(+ a (- 0 1))"),
                           ("(* (- c 1) 32)", "(- (* c 32) 32)"),
                           ("(- (+ a (+ b (* c 32))) (+ a (+ b (* (- c 1) 32))))", "32"),
                           ("(- (+ a (+ b (* longname 32))) (+ a (+ b (* (- longname 1) 32))))",  "32"),
                           ("(! (== (== 3264763256 tacSighash) 0))", "(== 3264763256 tacSighash)")
                           ];
        for (lhs, rhs) in queries {
            let runner = LogicalRunner::new();
            runner.add_expr(lhs.to_string());
            runner.add_expr(rhs.to_string());
            runner.run(500);

            let l_parsed = &lhs.parse().unwrap();
            let r_parsed = &rhs.parse().unwrap();

            println!("{} {}", l_parsed, r_parsed);

            let mut egraph = runner.egraph.write().unwrap();
            if egraph.add_expr(l_parsed) != egraph.add_expr(r_parsed) {
>>>>>>> cnandi/lin-invs
                panic!("could not prove equal {},   {}", lhs, rhs);
            }
        }
    }
}
