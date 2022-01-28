pub mod logical_equality;
mod statement;

use clap::Parser;
use egg::*;
use once_cell::sync::Lazy;
use serde::*;
// use statement::Stmt;
use ruler::{EVM, eval_evm};
use primitive_types::U256;
use crate::logical_equality::{LogicalEquality, LogicalAnalysis};
use std::sync::Mutex;
use std::{cmp::*, collections::HashMap};

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

#[derive(Serialize, Deserialize, Parser)]
#[clap(rename_all = "kebab-case")]
pub struct OptParams {
    ////////////////
    // eqsat args //
    ////////////////
    #[clap(long, default_value = "5")]
    pub eqsat_iter_limit: usize,
    #[clap(long, default_value = "100000")]
    pub eqsat_node_limit: usize,
    ////////////////
    // block from TAC CFG //
    ////////////////
    // #[clap(long, default_value = "input.json")]
    // pub input: String,
}

impl Default for OptParams {
    fn default() -> Self {
        Self {
            eqsat_iter_limit: 5,
            eqsat_node_limit: 10000
        }
    }
}
pub struct EggAssign {
    pub lhs: String,
    pub rhs: String,
}

pub struct EqualityResult {
    pub result: bool,
    pub leftv: String,
    pub rightv: String,
}

// TODO: not used.
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
            EVM::Num(_) => 1,
            EVM::Var(v) => {
                if v == &self.lhs {
                    1000
                } else if AGE_MAP.lock().unwrap().get(v).unwrap() < &self.age_limit {
                    10
                } else {
                    100
                }
            }
            _ => 5,
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
        let ag = |i: &Id| egraph[*i].data.age;
        let age: Option<usize>;
        match enode {
            EVM::Num(c) => {
                age = Some(0);
            }
            EVM::Add([a, b]) => {
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            EVM::Sub([a, b]) => {
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            EVM::Mul([a, b]) => {
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            EVM::Div([a, b]) => {
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            EVM::Lt([a, b]) => {
                //constant = None; // TODO: should change this to fold bools too
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            EVM::Gt([a, b]) => {
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            EVM::Le([a, b]) => {
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            EVM::Ge([a, b]) => {
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            EVM::Var(v) => {
                age = {
                    let a = *AGE.lock().unwrap();
                    AGE_MAP.lock().unwrap().insert(*v, a);
                    *AGE.lock().unwrap() = a + 1;
                    Some(a)
                };
            }
            _ => {
                age = None;
            }
        }

        let mut child_const = vec![];
        enode.for_each(|child| child_const.push(egraph[child].data.constant));
        let first = child_const.get(0).unwrap_or(&None);
        let second = child_const.get(1).unwrap_or(&None);
        let constant = eval_evm(enode, *first, *second);
        Data { constant, age }
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
       match (to.constant.as_ref(), from.constant) {
            (None, Some(b)) => to.constant = Some(b.clone()),
            (None, None) => (),
            (Some(_), None) => (),
            (Some(a), Some(b)) => assert_eq!(*a, b),
        }
        match (to.age, from.age) {
            (None, Some(b)) => to.age = Some(b.clone()),
            (None, None) => (),
            (Some(_), None) => (),
            // when two eclasses with different variables are merged,
            // update the age to be the one of the youngest (largest age value).
            (Some(a), Some(b)) => to.age = Some(max(a, b)),
        }
        DidMerge(false, false)
    }

    // We don't modify the eclass based on variable age.
    // Just add the constants we get from constant folding.
    fn modify(egraph: &mut EGraph, id: Id) {
        let class = &mut egraph[id];
        if let Some(c) = class.data.constant {
            let added = egraph.add(EVM::from(c));
            egraph.union(id, added);
            egraph.rebuild();
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
        rewrite!("add-neg"; "(+ ?a (- 0 ?a))" => "0"),
        rewrite!("mul-0"; "(* ?a 0)" => "0"),
    ];

    let mut bi_dirs: Vec<Rewrite<EVM, TacAnalysis>> = vec![
        rewrite!("add-0"; "(+ ?a 0)" <=> "?a"),
        rewrite!("sub-0"; "(- ?a 0)" <=> "?a"),
        rewrite!("mul-1"; "(* ?a 1)" <=> "?a"),
        rewrite!("sub-add"; "(- ?a ?b)" <=> "(+ ?a (- 0 ?b))"),
        rewrite!("add-sub";  "(+ ?a (- 0 ?b))" <=> "(- ?a ?b)"),
        rewrite!("assoc-sub"; "(- (+ ?a ?b) ?c))" <=> "(+ ?a (- ?b ?c))"),
        rewrite!("assoc-add"; "(+ ?a (+ ?b ?c))" <=> "(+ (+ ?a ?b) ?c)"),
    ].concat();

    uni_dirs.append(&mut bi_dirs);
    uni_dirs
}

// Get the eclass ids for all eclasses in an egraph
fn _ids(egraph: &EGraph) -> Vec<egg::Id> {
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
            let id_l = self.egraph.add_expr(&b.lhs.parse().unwrap());
            // let mut id_r: Id = id_l;
            assert!(b.rhs.len() > 0, "RHS of this assignment is empty!");
            let id_r = self.egraph.add_expr(&b.rhs.parse().unwrap());
            self.egraph.union(id_l, id_r);
            roots.push(id_l);
        }
        log::info!("Done adding terms to the egraph.");
        self.egraph.rebuild();

        // run eqsat with the domain rules
        let mut runner: Runner<EVM, TacAnalysis> = Runner::new(self.egraph.analysis.clone())
            .with_egraph(self.egraph)
            .with_iter_limit(self.params.eqsat_iter_limit)
            .with_node_limit(self.params.eqsat_node_limit)
            .with_scheduler(egg::SimpleScheduler);
        runner.roots = roots.clone();
        runner = runner.run(&rules());
        runner.egraph.rebuild();
        log::info!("Done running rules.");
        //runner.egraph.dot().to_svg("target/foo.svg").unwrap();
        let mut c = 0;
        for id in roots {
            // TODO: carefully think why we know that the RHS corresponds to this LHS?
            // I think the root ids have the right order but need to be careful.
            let best_l: &RecExpr<EVM> = &block_assgns[c].lhs.parse().unwrap();
            // let extract_left = Extractor::new(&runner.egraph, LHSCostFn);
            // let best_l = extract_left.find_best(id).1;
            // check that this is indeed a var.
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

// Entry point
pub fn start(ss: Vec<EggAssign>) -> Vec<EggAssign> {
    let params: OptParams = OptParams::default();
    let res = TacOptimizer::new(params).run(ss);
    return res;

    // match Command::parse() {
    //     Command::Optimize(params) => {
    //         let opt = TacOptimizer::new(params);
    //         opt.run()

    //     }
    // }
}

// Logical Equality Entry Point
pub fn check_eq(lhs: String, rhs: String) -> EqualityResult {
    LogicalEquality::new().run(lhs, rhs)
}

std::include!("tac_optimizer.uniffi.rs");

pub fn check_test(input: Vec<EggAssign>, expected: Vec<EggAssign>) {
    let _ = env_logger::builder().try_init();
    let actual = start(input);
    for r in &actual {
        println!("{} = {}", r.lhs, r.rhs);
    }
    assert_eq!(actual.len(), expected.len());
    let mut res = true;
    for (a, e) in actual.iter().zip(expected.iter()) {
        if res == false {
            break;
        }
        res = res
            && (a.lhs.to_string() == e.lhs.to_string())
            && (a.rhs.to_string() == e.rhs.to_string())
    }
    assert_eq!(res, true)
}

#[cfg(test)]
mod tests {
    use ruler::WrappedU256;

    use crate::*;

    #[test]
    fn test1() {
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
        let expected = vec![
            EggAssign {
                lhs: "R194".to_string(),
                rhs: "64".to_string(),
            },
            EggAssign {
                lhs: "R198".to_string(),
                rhs: "96".to_string(),
            },
            EggAssign {
                lhs: "R202".to_string(),
                rhs: "32".to_string(),
            },
        ];
        check_test(input, expected);
    }

    #[test]
    fn test2() {
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
        let expected = vec![
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
                rhs: "64".to_string(),
            },
        ];
        check_test(input, expected);
    }

    #[test]
    fn test3() {
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
        let expected = vec![
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
        check_test(input, expected);
    }

    #[test]
    fn test4() {
        let input = vec![
            EggAssign {
                lhs: "R1".to_string(),
                rhs: "64".to_string(),
            },
            EggAssign {
                lhs: "R2".to_string(),
                rhs: "(+ 32 R1)".to_string(),
            }
        ];
        let expected = vec![
            EggAssign {
                lhs: "R1".to_string(),
                rhs: "64".to_string(),
            },
            EggAssign {
                lhs: "R2".to_string(),
                rhs: "96".to_string(),
            }
        ];
        check_test(input, expected);
    }

    #[test]
    fn test5() {
        let input = vec![
            EggAssign {
                lhs: "R1".to_string(),
                rhs: "64".to_string(),
            },
            EggAssign {
                lhs: "R2".to_string(),
                rhs: "(- 32 R1)".to_string(),
            }
        ];
        let expected = vec![
            EggAssign {
                lhs: "R1".to_string(),
                rhs: "64".to_string(),
            },
            EggAssign {
                lhs: "R2".to_string(),
                rhs: "115792089237316195423570985008687907853269984665640564039457584007913129639904".to_string(),
            }
        ];
        check_test(input, expected);
    }

    #[test]
    fn test6() {
        let input = vec![
            EggAssign {
                lhs: "R1".to_string(),
                rhs: "64".to_string(),
            },
            EggAssign {
                lhs: "R2".to_string(),
                rhs: "(- R1 32)".to_string(),
            }
        ];
        let expected = vec![
            EggAssign {
                lhs: "R1".to_string(),
                rhs: "64".to_string(),
            },
            EggAssign {
                lhs: "R2".to_string(),
                rhs: "32".to_string(),
            }
        ];
        check_test(input, expected);
    }
    #[test]
    fn test7() {
        let input = vec![
            EggAssign {
                lhs: "R1".to_string(),
                rhs: "(- 5 0)".to_string(),
            }
        ];
        let expected = vec![
            EggAssign {
                lhs: "R1".to_string(),
                rhs: "5".to_string(),
            }
        ];
        check_test(input, expected);
    }

    #[test]
    fn parse_test1() {
        let from_string: RecExpr<EVM> = "(+ x 0)".to_string().parse().unwrap();
        let v1 = EVM::Var(Symbol::from("x"));
        let v2 = EVM::Num(WrappedU256{value: U256::zero()});
        let mut foo = RecExpr::default();
        let id1 = foo.add(v1);
        let id2 = foo.add(v2);
        let _id3 = foo.add(EVM::Add([id1, id2]));
        assert_eq!(foo, from_string);

    }

    #[test]
    fn parse_test2() {
        let v1 = EVM::from(U256::from(32));
        let v2 = EVM::new(U256::from_dec_str("32").unwrap());
        assert_eq!(v1, v2);
    }
}

// TODO: need to havocify, then ssa-ify, then eqsat, then unhavoc-ify, then unssa-ify, handle other expressions
/*
x2 := havoc
x1 := x2 + 96 // x1 = x2 + 96
x3 := x1 - 32 // x3 = x2 + 64
x4 := x3 - x2 // x4 = 64
*/
