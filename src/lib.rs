use serde::*;
// use bigint::B256;
use clap::Clap;
use egg::*;
use statement::Stmt;

mod statement;

pub type EGraph = egg::EGraph<TAC, ConstantFold>;

#[derive(Serialize, Deserialize, Clap)]
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
    #[clap(long, default_value = "input.json")]
    pub input: String
}

define_language! {
    pub enum TAC {
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "~" = Neg([Id; 1]),
        "Havoc" = Havoc, // TODO: not the same thing!
        Bool(bool),
        // TODO: this should be 256 bits not 64 bits
        Num(i64),
        Var(egg::Symbol),
    }
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

pub struct RHSCostFn;
impl egg::CostFunction<TAC> for RHSCostFn {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &TAC, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            TAC::Havoc => 1,
            TAC::Bool(_) => 1,
            TAC::Num(_) => 1,
            TAC::Var(_) => 2,
            _ => 1,
        };
        enode.fold(op_cost, |sum, i| sum + costs(i))
    }
}

#[derive(Default, Debug, Clone)]
pub struct ConstantFold;
impl Analysis<TAC> for ConstantFold {
    type Data = Option<i64>;

    fn make(egraph: &egg::EGraph<TAC, ConstantFold>, enode: &TAC) -> Self::Data {
        let dat = |i: &Id| egraph[*i].data;
        Some(match enode {
            TAC::Num(c) => *c,
            TAC::Add([a, b]) => dat(a)? + dat(b)?,
            TAC::Sub([a, b]) => dat(a)? - dat(b)?,
            TAC::Mul([a, b]) => dat(a)? * dat(b)?,
            TAC::Neg([a]) => -dat(a)?,
            _ => return None,
        })
    }

    fn merge(&self, to: &mut Self::Data, from: Self::Data) -> bool {
        match (to.clone(), from.clone()) {
            (None, Some(_)) => *to = from.clone(),
            (None, None) => (),
            (Some(_), None) => (),
            (Some(_), Some(_)) => assert_eq!(to, &mut from.clone()),
        }
        false
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        let class = &mut egraph[id];
        if let Some(c) = class.data {
            let added = egraph.add(TAC::Num(c));
            let (id, _did_something) = egraph.union(id, added);
            assert!(
                !egraph[id].nodes.is_empty(),
                "empty eclass! {:#?}",
                egraph[id]
            );
            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
    }
}

// some standard axioms
pub fn rules() -> Vec<Rewrite<TAC, ConstantFold>> {
    let mut uni_dirs: Vec<Rewrite<TAC, ConstantFold>> = vec![
        rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("sub-cancel"; "(- ?a ?a)" => "0"),
        rewrite!("add-neg"; "(+ ?a (~ ?a))" => "0"),
        rewrite!("mul-0"; "(* ?a 0)" => "0"),
    ];

    let mut bi_dirs: Vec<Rewrite<TAC, ConstantFold>> = vec![
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
            egraph: EGraph::new(ConstantFold),
        };
        optimizer
    }

    pub fn run(mut self) {
        let block_assgns: Vec<Stmt<TAC>> = statement::parse(&self.params.input);
        // add lhs and rhs of each assignment to a new egraph
        // and union their eclasses
        for b in block_assgns {
            let id_l = self.egraph.add_expr(&b.lhs);
            let id_r = self.egraph.add_expr(&b.rhs);
            self.egraph.union(id_l, id_r);
        }

        self.egraph.rebuild();

        // run eqsat with the domain rules
        let mut runner: Runner<TAC, ConstantFold> = Runner::new(self.egraph.analysis.clone())
            .with_egraph(self.egraph)
            .with_iter_limit(self.params.eqsat_iter_limit)
            .with_node_limit(self.params.eqsat_node_limit)
            .with_scheduler(egg::SimpleScheduler);
        runner.roots = ids(&runner.egraph);
        runner = runner.run(&rules());
        runner.egraph.rebuild();

        let mut extract_left = Extractor::new(&runner.egraph, LHSCostFn);
        let mut extract_right = Extractor::new(&runner.egraph, RHSCostFn);

        for id in ids(&runner.egraph) {
            let (_, best_l) = extract_left.find_best(id);
            let (_, best_r) = extract_right.find_best(id);
            println!("{} := {}", best_l, best_r);
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
