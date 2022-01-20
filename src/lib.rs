pub mod logical_equality;
mod statement;

use clap::Parser;
use egg::*;
use once_cell::sync::Lazy;
use serde::*;
// use statement::Stmt;
use crate::logical_equality::{LogicalRunner};
use ruler::{EVM};
use primitive_types::U256;
use std::sync::Mutex;
use std::{cmp::*, collections::HashMap};
use std::sync::Arc;

// use bigint::B256;

pub type EGraph = egg::EGraph<EVM, TacAnalysis>;

// NOTE: this should be "freshness" perhaps. Oldest vars have least age.
static AGE: Lazy<Mutex<usize>> = Lazy::new(|| {
    let age: usize = 1;
    Mutex::new(age)
});

static AGE_MAP: Lazy<Mutex<HashMap<Symbol, usize>>> = Lazy::new(|| {
    let age_map: HashMap<Symbol, usize> = HashMap::new();
    Mutex::new(age_map)
});

#[derive(Parser)]
#[clap(rename_all = "kebab-case")]
pub enum Command {
    // only one command for now
    Optimize(OptParams),
}

#[derive(Serialize, Deserialize, Parser, Default)]
#[clap(rename_all = "kebab-case")]
pub struct OptParams {
    ////////////////
    // eqsat args //
    ////////////////
    #[clap(long, default_value = "5")]
    pub eqsat_iter_limit: u64,
    #[clap(long, default_value = "100000")]
    pub eqsat_node_limit: u64,
    ////////////////
    // block from TAC CFG //
    ////////////////
    // #[clap(long, default_value = "input.json")]
    // pub input: String,
}

pub struct EggAssign {
    pub lhs: String,
    pub rhs: String,
}

pub struct LHSCostFn;
impl egg::CostFunction<EVM> for LHSCostFn {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &EVM, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            EVM::Var(_) => 1,
            _ => 100,
        };
        enode.fold(op_cost, |sum, i| sum + costs(i))
    }
}

pub struct RHSCostFn {
    age_limit: usize,
    lhs: Symbol,
}

impl egg::CostFunction<EVM> for RHSCostFn {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &EVM, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            EVM::Var(v) => {
                if v == &self.lhs {
                    1000
                } else if AGE_MAP.lock().unwrap().get(v).unwrap() < &self.age_limit {
                    1
                } else {
                    100
                }
            }
            _ => 1,
        };
        enode.fold(op_cost, |sum, i| sum + costs(i))
    }
}

#[derive(Default, Debug, Clone)]
pub struct Data {
    constant: Option<U256>,
    age: Option<usize>,
}

#[derive(Default, Debug, Clone)]
pub struct TacAnalysis;
impl Analysis<EVM> for TacAnalysis {
    type Data = Data;

    fn make(egraph: &egg::EGraph<EVM, TacAnalysis>, enode: &EVM) -> Self::Data {
        let ct = |i: &Id| egraph[*i].data.constant;
        let ag = |i: &Id| egraph[*i].data.age;
        let constant: Option<U256>;
        let age: Option<usize>;
        match enode {
            EVM::Num(c) => {
                constant = Some(c.value);
                age = Some(0);
            }
            EVM::Havoc => {
                constant = None;
                age = Some(0);
            }
            EVM::Add([a, b]) => {
                constant = match (ct(a), ct(b)) {
                    (Some(x), Some(y)) => Some(x + y),
                    (_, _) => None,
                };
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            EVM::Sub([a, b]) => {
                constant = match (ct(a), ct(b)) {
                    (Some(x), Some(y)) => Some(x - y),
                    (_, _) => None,
                };
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            EVM::Mul([a, b]) => {
                constant = match (ct(a), ct(b)) {
                    (Some(x), Some(y)) => Some(x * y),
                    (_, _) => None,
                };
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            EVM::Div([a, b]) => {
                constant = match (ct(a), ct(b)) {
                    (Some(x), Some(y)) => Some(x / y),
                    (_, _) => None,
                };
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            EVM::Var(v) => {
                constant = None;
                age = {
                    let a = *AGE.lock().unwrap();
                    AGE_MAP.lock().unwrap().insert(*v, a);
                    *AGE.lock().unwrap() = a + 1;
                    Some(a)
                };
            }
            EVM::Lt([a, b]) => {
                constant = None; // TODO: should change this to fold bools too
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            EVM::Gt([a, b]) => {
                constant = None; // TODO: should change this to fold bools too
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            EVM::Le([a, b]) => {
                constant = None; // TODO: should change this to fold bools too
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            EVM::Ge([a, b]) => {
                constant = None; // TODO: should change this to fold bools too
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            _ => {
                constant = None;
                age = None;
            }
        }
        Data { constant, age }
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        match (to.constant, from.constant) {
            (None, Some(b)) => to.constant = Some(b.clone()),
            (None, None) => (),
            (Some(_), None) => (),
            (Some(a), Some(b)) => assert_eq!(a, b),
        }
        match (to.age, from.age) {
            (None, Some(b)) => to.age = Some(b.clone()),
            (None, None) => (),
            (Some(_), None) => (),
            // when two eclasses with different variables are merged,
            // update the age to be the one of the youngest (largest age value).
            (Some(a), Some(b)) => to.age = Some(max(a, b)),
        }

        // TODO this is overapproximating
        DidMerge(true, true)
    }

    // We don't modify the eclass based on variable age.
    // Just add the constants we get from constant folding.
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

// some standard axioms
pub fn rules() -> Vec<Rewrite<EVM, TacAnalysis>> {
    let mut uni_dirs: Vec<Rewrite<EVM, TacAnalysis>> = vec![
        rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("sub-cancel"; "(- ?a ?a)" => "0"),
        rewrite!("add-neg"; "(+ ?a (~ ?a))" => "0"),
        rewrite!("mul-0"; "(* ?a 0)" => "0"),
    ];

    let mut bi_dirs: Vec<Rewrite<EVM, TacAnalysis>> = vec![
        rewrite!("add-0"; "(+ ?a 0)" <=> "?a"),
        rewrite!("sub-0"; "(- ?a 0)" <=> "?a"),
        rewrite!("mul-1"; "(* ?a 1)" <=> "?a"),
        rewrite!("sub-add"; "(- ?a ?b)" <=> "(+ ?a (~ ?b))"),
        // rewrite!("add-sub";  "(+ ?a (~ ?b))" <=> "(- ?a ?b)"),
        rewrite!("assoc-add"; "(+ ?a (+ ?b ?c))" <=> "(+ (+ ?a ?b) ?c)"),
    ]
    .concat();

    uni_dirs.append(&mut bi_dirs);
    uni_dirs
}

// Get the eclass ids for all eclasses in an egraph
fn ids(egraph: &EGraph) -> Vec<egg::Id> {
    egraph.classes().map(|c| c.id).collect()
}

pub struct TacOptimizer {
    params: OptParams,
    egraph: EGraph,
}

impl TacOptimizer {
    pub fn new(params: OptParams) -> Self {
        let optimizer = Self {
            params,
            egraph: EGraph::new(TacAnalysis),
        };
        optimizer
    }

    pub fn run(mut self, block_assgns: Vec<EggAssign>) -> Vec<EggAssign> {
        let mut roots = vec![];
        let mut res = vec![];
        // add lhs and rhs of each assignment to a new egraph
        // and union their eclasses
        for b in &block_assgns {
            let id_l = self.egraph.add_expr(&b.lhs.parse().unwrap());;
            assert!(b.rhs.len() > 0, "RHS of this assignment is empty!");
            let id_r = self.egraph.add_expr(&b.rhs.parse().unwrap());
            // if b.rhs.as_ref()[0] != EVM::Havoc {
            //     id_r = self.egraph.add_expr(&b.rhs);
            // }
            self.egraph.union(id_l, id_r);
            roots.push(id_l);
        }
        self.egraph.rebuild();

        // run eqsat with the domain rules
        let mut runner: Runner<EVM, TacAnalysis> = Runner::new(self.egraph.analysis.clone())
            .with_egraph(self.egraph)
            .with_iter_limit(self.params.eqsat_iter_limit as usize)
            .with_node_limit(self.params.eqsat_node_limit as usize)
            .with_scheduler(egg::SimpleScheduler);
        // runner.roots = ids(&runner.egraph);
        runner.roots = roots.clone();
        runner = runner.run(&rules());
        runner.egraph.rebuild();

        let mut c = 0;
        for id in roots {
            // simply get lhs from the assignments
            let best_l: &RecExpr<EVM> = &block_assgns[c].lhs.parse().unwrap();
            // TODO: check that this is indeed a var.
            match best_l.as_ref()[0] {
                EVM::Var(vl) => {
                    let vl_age = AGE_MAP.lock().unwrap().get(&vl).unwrap().clone();
                    let extract_right = Extractor::new(
                        &runner.egraph,
                        RHSCostFn {
                            age_limit: vl_age,
                            lhs: vl,
                        },
                    );
                    let (_, best_r) = extract_right.find_best(id);
                    let assg = EggAssign {
                        lhs: best_l.to_string(),
                        rhs: best_r.to_string(),
                    };
                    res.push(assg);
                }
                _ => (),
            }
            c = c + 1;
        }
        return res;
    }
}

// logical runner entry point
pub fn make_logical_egraph() -> Arc<LogicalRunner> {
    Arc::new(LogicalRunner::new())
}

pub fn add_logical_pair(runner: Arc<LogicalRunner>, expr: String, expr2: String) {
    runner.add_pair(expr, expr2);
}

pub fn run_logical(runner: Arc<LogicalRunner>, timeout: u64) {
    runner.run(timeout)
}

pub fn are_equal_logical(runner: Arc<LogicalRunner>, expr1: String, expr2: String) -> bool {
    runner.are_equal(expr1, expr2)
}

pub fn are_unequal_fuzzing(runner: Arc<LogicalRunner>, expr1: String, expr2: String) -> bool {
    runner.are_unequal_fuzzing(expr1, expr2)
}

// Entry point
pub fn start(ss: Vec<EggAssign>) -> Vec<EggAssign> {
    let params: OptParams = Default::default();
    let res = TacOptimizer::new(params).run(ss);
    return res;
    // let _ = env_logger::builder().try_init();

    // match Command::parse() {
    //     Command::Optimize(params) => {
    //         let opt = TacOptimizer::new(params);
    //         opt.run()

    //     }
    // }
}

std::include!("tac_optimizer.uniffi.rs");

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test1() {
        let params = Default::default();
        let opt = crate::TacOptimizer::new(params);
        let input = vec![
            EggAssign {
                lhs: "R194".to_string(),
                rhs: "64".to_string(),
            },
            EggAssign {
                lhs: "R198".to_string(),
                rhs: "(+ 32 R194)".to_string(),
            },
            EggAssign {
                lhs: "R202".to_string(),
                rhs: "(- R198 R194)".to_string(),
            },
        ];
        let res = opt.run(input);
        for r in res {
            println!("{} = {}", r.lhs, r.rhs);
        }
    }

    #[test]
    fn test2() {
        let params = Default::default();
        let opt = crate::TacOptimizer::new(params);
        let input = vec![
            EggAssign {
                lhs: "x2".to_string(),
                rhs: "Havoc".to_string(),
            },
            EggAssign {
                lhs: "x1".to_string(),
                rhs: "(+ x2 96)".to_string(),
            },
            EggAssign {
                lhs: "x3".to_string(),
                rhs: "(- x1 32)".to_string(),
            },
            EggAssign {
                lhs: "x4".to_string(),
                rhs: "(- x3 x2)".to_string(),
            },
        ];
        let res = opt.run(input);
        for r in res {
            println!("{} = {}", r.lhs, r.rhs);
        }
    }

    #[test]
    fn test3() {
        let params = Default::default();
        let opt = crate::TacOptimizer::new(params);
        let input = vec![
            EggAssign {
                lhs: "R11".to_string(),
                rhs: "0".to_string(),
            },
            EggAssign {
                lhs: "R13".to_string(),
                rhs: "0".to_string(),
            },
            EggAssign {
                lhs: "lastHasThrown".to_string(),
                rhs: "0".to_string(),
            },
            EggAssign {
                lhs: "lastReverted".to_string(),
                rhs: "1".to_string(),
            },
            EggAssign {
                lhs: "R7".to_string(),
                rhs: "tacCalldatasize".to_string(),
            },
            EggAssign {
                lhs: "B9".to_string(),
                rhs: "(< R7 4)".to_string(),
            },
        ];
        let res = opt.run(input);
        for r in res {
            println!("{} = {}", r.lhs, r.rhs);
        }
    }
}

// TODO: need to havocify, then ssa-ify, then eqsat, then unhavoc-ify, then unssa-ify, handle other expressions
/*
x2 := havoc
x1 := x2 + 96 // x1 = x2 + 96
x3 := x1 - 32 // x1 = (x3 + 32)
x4 := x3 - x2 // x4 = 64
*/
