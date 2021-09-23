use clap::Clap;
use egg::*;
use once_cell::sync::Lazy;
use serde::*;
// use statement::Stmt;
use std::sync::Mutex;
use std::{cmp::*, collections::HashMap};

// use bigint::B256;

mod statement;

pub type EGraph = egg::EGraph<TAC, TacAnalysis>;

// NOTE: this should be "freshness" perhaps. Oldest vars have least age.
static AGE: Lazy<Mutex<usize>> = Lazy::new(|| {
    let age: usize = 1;
    Mutex::new(age)
});

static AGE_MAP: Lazy<Mutex<HashMap<Symbol, usize>>> = Lazy::new(|| {
    let age_map: HashMap<Symbol, usize> = HashMap::new();
    Mutex::new(age_map)
});

#[derive(Clap)]
#[clap(rename_all = "kebab-case")]
pub enum Command {
    // only one command for now
    Optimize(OptParams),
}

#[derive(Serialize, Deserialize, Clap, Default)]
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

define_language! {
    pub enum TAC {
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "~" = Neg([Id; 1]),
        ">" = Gt([Id; 2]),
        "<" = Lt([Id; 2]),
        ">=" = Ge([Id; 2]),
        "<=" = Le([Id; 2]),
        "Havoc" = Havoc, // TODO: not the same thing!
        Bool(bool),
        // TODO: this should be 256 bits not 64 bits
        Num(i64),
        Var(egg::Symbol),
    }
}

pub struct EggAssign {
    pub lhs: String,
    pub rhs: String
}


pub struct LHSCostFn;
impl egg::CostFunction<TAC> for LHSCostFn {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &TAC, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            TAC::Var(_) => 1,
            _ => 100,
        };
        enode.fold(op_cost, |sum, i| sum + costs(i))
    }
}

pub struct RHSCostFn {
    age_limit: usize,
}

impl egg::CostFunction<TAC> for RHSCostFn {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &TAC, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            TAC::Var(v) => {
                if AGE_MAP.lock().unwrap().get(v).unwrap() < &self.age_limit {
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
    constant: Option<i64>,
    age: Option<usize>,
}

#[derive(Default, Debug, Clone)]
pub struct TacAnalysis;
impl Analysis<TAC> for TacAnalysis {
    type Data = Data;

    fn make(egraph: &egg::EGraph<TAC, TacAnalysis>, enode: &TAC) -> Self::Data {
        let ct = |i: &Id| egraph[*i].data.constant;
        let ag = |i: &Id| egraph[*i].data.age;
        let constant: Option<i64>;
        let age: Option<usize>;
        match enode {
            TAC::Num(c) => {
                constant = Some(*c);
                age = Some(0);
            }
            TAC::Havoc => {
                constant = None;
                age = Some(0);
            }
            TAC::Bool(_) => {
                constant = None; // TODO: should change this to fold bools too
                age = Some(0);
            }
            TAC::Add([a, b]) => {
                constant = match (ct(a), ct(b)) {
                    (Some(x), Some(y)) => Some(x + y),
                    (_, _) => None,
                };
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            TAC::Sub([a, b]) => {
                constant = match (ct(a), ct(b)) {
                    (Some(x), Some(y)) => Some(x - y),
                    (_, _) => None,
                };
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            TAC::Mul([a, b]) => {
                constant = match (ct(a), ct(b)) {
                    (Some(x), Some(y)) => Some(x * y),
                    (_, _) => None,
                };
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            TAC::Neg([a]) => {
                constant = match ct(a) {
                    Some(x) => Some(-x),
                    _ => None,
                };
                age = ag(a);
            }
            TAC::Var(v) => {
                constant = None;
                age = {
                    let a = *AGE.lock().unwrap();
                    AGE_MAP.lock().unwrap().insert(*v, a);
                    *AGE.lock().unwrap() = a + 1;
                    Some(a)
                };
            }
            TAC::Lt([a, b]) => {
                constant = None; // TODO: should change this to fold bools too
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            TAC::Gt([a, b]) => {
                constant = None; // TODO: should change this to fold bools too
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            TAC::Le([a, b]) => {
                constant = None; // TODO: should change this to fold bools too
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
            TAC::Ge([a, b]) => {
                constant = None; // TODO: should change this to fold bools too
                age = match (ag(a), ag(b)) {
                    (Some(x), Some(y)) => Some(max(x, y)),
                    (_, _) => None,
                };
            }
        }
        Data { constant, age }
    }

    fn merge(&self, to: &mut Self::Data, from: Self::Data) -> bool {
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

        false
    }

    // We don't modify the eclass based on variable age.
    fn modify(egraph: &mut EGraph, id: Id) {
        let class = &mut egraph[id];
        if let Some(c) = class.data.constant {
            let added = egraph.add(TAC::Num(c));
            let (id, _did_something) = egraph.union(id, added);
            assert!(
                !egraph[id].nodes.is_empty(),
                "empty eclass! {:#?}",
                egraph[id]
            );
        }
    }
}

// some standard axioms
pub fn rules() -> Vec<Rewrite<TAC, TacAnalysis>> {
    let mut uni_dirs: Vec<Rewrite<TAC, TacAnalysis>> = vec![
        rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("sub-cancel"; "(- ?a ?a)" => "0"),
        rewrite!("add-neg"; "(+ ?a (~ ?a))" => "0"),
        rewrite!("mul-0"; "(* ?a 0)" => "0"),
    ];

    let mut bi_dirs: Vec<Rewrite<TAC, TacAnalysis>> = vec![
        rewrite!("add-0"; "(+ ?a 0)" <=> "?a"),
        rewrite!("sub-0"; "(- ?a 0)" <=> "?a"),
        rewrite!("mul-1"; "(* ?a 1)" <=> "?a"),
        rewrite!("sub-add"; "(- ?a ?b)" <=> "(+ ?a (~ ?b))"),
        rewrite!("add-sub";  "(+ ?a (~ ?b))" <=> "(- ?a ?b)"),
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

    pub fn run(mut self, block_assgns: Vec<EggAssign>) {
        println!("Fried eggs say HI!!");
        let mut roots = vec![];

        // add lhs and rhs of each assignment to a new egraph
        // and union their eclasses
        for b in &block_assgns {
            let id_l = self.egraph.add_expr(&b.lhs.parse().unwrap());
            // let mut id_r: Id = id_l;
            assert!(b.rhs.len() > 0, "RHS of this assignment is empty!");
            let id_r = self.egraph.add_expr(&b.rhs.parse().unwrap());
            // if b.rhs.as_ref()[0] != TAC::Havoc {
            //     id_r = self.egraph.add_expr(&b.rhs);
            // }
            let (id, _) = self.egraph.union(id_l, id_r);
            roots.push(id);
        }
        self.egraph.rebuild();

        // run eqsat with the domain rules
        let mut runner: Runner<TAC, TacAnalysis> = Runner::new(self.egraph.analysis.clone())
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
            let best_l: &RecExpr<TAC> = &block_assgns[c].lhs.parse().unwrap();
            // TODO: check that this is indeed a var.
            match best_l.as_ref()[0] {
                TAC::Var(vl) => {
                    let vl_age = AGE_MAP.lock().unwrap().get(&vl).unwrap().clone();
                    let mut extract_right =
                        Extractor::new(&runner.egraph, RHSCostFn { age_limit: vl_age });
                    let (_, best_r) = extract_right.find_best(id);
                    println!("{} = {}", best_l, best_r);
                }
                _ => (),
            }
            c = c + 1;
        }
    }
}

// Entry point
pub fn start(ss: Vec<EggAssign>) {
    let params: OptParams = Default::default();
    TacOptimizer::new(params).run(ss)
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
            EggAssign{lhs: "R194".to_string(), rhs: "64".to_string()},
            EggAssign{lhs: "R198".to_string(), rhs: "(+ 32 R194)".to_string()},
            EggAssign{lhs: "R202".to_string(), rhs: "(- R198 R194)".to_string()}
        ];
        opt.run(input)
    }
}





// TODO: need to havocify, then ssa-ify, then eqsat, then unhavoc-ify, then unssa-ify, handle other expressions
/*
x2 := havoc
x1 := x2 + 96 // x1 = x2 + 96
x3 := x1 - 32 // x1 = (x3 + 32)
x4 := x3 - x2 // x4 = 64
*/