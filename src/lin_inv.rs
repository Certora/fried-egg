use clap::Parser;
use egg::*;
use serde::*;
use std::io;
use std::io::prelude::*;
// use statement::Stmt;
use egg::{ENodeOrVar, Pattern, RecExpr};
use itertools::Itertools;
use num_bigint::BigUint;
use primitive_types::U256;
use rust_evm::WrappedU256;
use rust_evm::{eval_evm, EVM};
use std::iter::FromIterator;
use std::{cmp::*, collections::HashMap, collections::HashSet};
use symbolic_expressions::parser::parse_str;
use symbolic_expressions::Sexp;

use crate::logical_equality::logical_rules;

pub type EGraph = egg::EGraph<EVM, TacAnalysis>;

// NOTE: this should be "freshness" perhaps. Oldest vars have least age.
//
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
    #[clap(long, default_value = "10000")]
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
            eqsat_node_limit: 10000,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct EggAssign {
    pub lhs: String,
    pub rhs: String,
    pub indexWrites: Vec<String>,
    pub nextFp: String,
}

impl EggAssign {
    pub fn new(lhs: &str, rhs: &str) -> Self {
        Self {
            lhs: lhs.to_string(),
            rhs: rhs.to_string(),
            indexWrites: vec![],
            nextFp: "noNextFp".to_string(),
        }
    }
}

pub struct LinearCostFn {}

pub struct GeneralCostFn {}

impl egg::CostFunction<EVM> for GeneralCostFn {
    type Cost = BigUint;
    fn cost<C>(&mut self, enode: &EVM, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let basic_cost = "5".parse().unwrap();
        let var_value = "5".parse().unwrap();
        let num_value = "2".parse().unwrap();
        let complex_cost = "20".parse().unwrap();
        match enode {
            EVM::Num(n) => if n.value < "1000".parse().unwrap() {
                "1".parse().unwrap()
            } else  {
                num_value
            },
            EVM::Var(_) => var_value,
            EVM::Div(_) => enode.fold(complex_cost, |sum, i| sum + costs(i)),
            EVM::Exp(_) => enode.fold(complex_cost, |sum, i| sum + costs(i)),
            _ => enode.fold(basic_cost, |sum, i| sum + costs(i)),
        }
    }

}

// Extract linear expressions by looking for sums of multiplication of variables and constants
impl egg::CostFunction<EVM> for LinearCostFn {
    type Cost = BigUint;
    fn cost<C>(&mut self, enode: &EVM, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let upper_value = "1000".parse().unwrap();
        let add_value = "40".parse().unwrap();
        let mul_value = "20".parse().unwrap();
        let var_value = "5".parse().unwrap();
        let num_value = "2".parse().unwrap();
        match enode {
            EVM::Num(n) => if n.value < "1000".parse().unwrap() {
                "1".parse().unwrap()
            } else  {
                num_value
            },
            EVM::Var(_) => var_value,
            EVM::Mul([child1, child2]) => {
                let (mut costa, mut costb) = (costs(*child1), costs(*child2));
                if costb < costa {
                    std::mem::swap(&mut costa, &mut costb);
                }

                if costa < var_value && costb < mul_value {
                    return costa + costb + mul_value;
                } else {
                    return costa + costb + upper_value;
                }
            }
            EVM::Add(_) => enode.fold(add_value, |sum, i| sum + costs(i)),
            EVM::Sub(_) => enode.fold(add_value, |sum, i| sum + costs(i)),
            _ => enode.fold(upper_value, |sum, i| sum + costs(i)),
        }
    }
}

#[derive(Default, Debug, Clone)]
pub struct Data {
    constant: Option<(U256, PatternAst<EVM>, Subst)>,
    linear_terms: Vec<LinearTerm>,
}

#[derive(Default, Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LinearTerm {
    number: U256,
    variables: Vec<(Symbol, U256)>,
}

impl LinearTerm {
    pub fn canonicalize(&self) -> LinearTerm {
        let mut variables = self.variables.clone();
        variables.sort_by(|a, b| a.0.cmp(&b.0));
        let mut new_vars: Vec<(Symbol, U256)> = vec![];
        if variables.len() > 0 {
            for var in variables.iter() {
                if var.1 != "0".parse().unwrap() {
                    if new_vars.len() > 0 && var.0 == new_vars.last().unwrap().0 {
                        new_vars.last_mut().unwrap().1 = eval_evm(
                            &EVM::Add([Id::from(0), Id::from(0)]),
                            Some(new_vars.last().unwrap().1),
                            Some(var.1),
                        )
                        .unwrap();
                    } else {
                        new_vars.push(*var);
                    }
                }
            }
        }

        LinearTerm {
            number: self.number,
            variables: new_vars,
        }
    }

    pub fn add_canon(&self, other: &LinearTerm) -> LinearTerm {
        let mut variables = self.variables.clone();
        variables.extend(other.variables.clone());
        let number = eval_evm(
            &EVM::Add([Id::from(0), Id::from(0)]),
            Some(self.number),
            Some(other.number),
        );
        LinearTerm {
            number: number.unwrap(),
            variables,
        }
        .canonicalize()
    }

    pub fn to_expr(&self) -> RecExpr<EVM> {
        let mut expr = RecExpr::default();
        if self.number != "0".parse().unwrap() {
            expr.add(EVM::Num(WrappedU256 { value: self.number }));
        }

        for variable in &self.variables {
            let before = expr.as_ref().len();
            expr.add(EVM::Num(WrappedU256 { value: variable.1 }));
            let num = expr.as_ref().len() - 1;
            expr.add(EVM::Var(variable.0));
            let var = expr.as_ref().len() - 1;
            expr.add(EVM::Mul([Id::from(num), Id::from(var)]));
            let mul = expr.as_ref().len() - 1;

            if before != 0 {
                expr.add(EVM::Add([Id::from(before - 1), Id::from(mul)]));
            }
        }

        expr
    }
}

#[derive(Debug, Clone)]
pub struct TacAnalysis {
    pub age_map: HashMap<Symbol, usize>,
}

impl Analysis<EVM> for TacAnalysis {
    type Data = Data;

    fn make(egraph: &egg::EGraph<EVM, TacAnalysis>, enode: &EVM) -> Self::Data {
        let mut child_const = vec![];
        enode.for_each(|child| child_const.push(egraph[child].data.constant.as_ref().map(|x| x.0)));
        let first = child_const.get(0).unwrap_or(&None);
        let second = child_const.get(1).unwrap_or(&None);
        let constant_option = eval_evm(enode, *first, *second);
        let constant = if let Some(c) = constant_option {
            let mut expr = PatternAst::default();
            let mut subst = Subst::default();
            let top_node = enode.clone().map_children(|child| {
                if egraph[child].data.constant.is_none() {
                    let var = format!("?{}", child).parse().unwrap();
                    subst.insert(var, child);
                    expr.add(ENodeOrVar::Var(var))
                } else {
                    expr.add(ENodeOrVar::ENode(EVM::new(
                        egraph[child].data.constant.as_ref().unwrap().0,
                    )))
                }
            });
            expr.add(ENodeOrVar::ENode(top_node));
            Some((c, expr, subst))
        } else {
            None
        };

        let terms = match enode {
            EVM::Var(v) => vec![LinearTerm {
                number: "0".parse().unwrap(),
                variables: vec![(*v, "1".parse().unwrap())],
            }
            .canonicalize()],
            EVM::Num(n) => vec![LinearTerm {
                number: n.value,
                variables: vec![],
            }],
            EVM::Mul([left, right]) => {
                if let Some(c) = egraph[*left].data.constant.as_ref() {
                    if c.0 > "0".parse().unwrap() {
                        let mut terms = vec![];
                        for term in &egraph[*right].data.linear_terms {
                            if term.variables.len() == 1 && term.number == "0".parse().unwrap() {
                                let var = term.variables.get(0).unwrap();
                                terms.push(
                                    LinearTerm {
                                        number: "0".parse().unwrap(),
                                        variables: vec![(
                                            var.0,
                                            eval_evm(enode, Some(c.0), Some(var.1)).unwrap(),
                                        )],
                                    }
                                    .canonicalize(),
                                );
                            }
                        }
                        terms
                    } else {
                        vec![]
                    }
                } else {
                    vec![]
                }
            }

            EVM::Add([left, right]) => {
                let mut terms = vec![];
                for term in &egraph[*left].data.linear_terms {
                    for term2 in &egraph[*right].data.linear_terms {
                        terms.push(term.add_canon(term2));
                    }
                }
                terms.sort();
                terms.dedup();
                terms
            }

            _ => vec![],
        };

        Data {
            constant,
            linear_terms: terms,
        }
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        let mut merge_a = false;
        match (to.constant.as_ref(), from.constant) {
            (None, Some(b)) => {
                to.constant = Some(b);
                merge_a = true;
            }
            (None, None) => (),
            (Some(_), None) => (),
            (Some(a), Some(b)) => assert_eq!(a.0, b.0),
        }

        if let Some(c) = &to.constant {
            to.linear_terms = vec![LinearTerm {
                number: c.0,
                variables: vec![],
            }];
        } else {
            if from.linear_terms.len() > 0 {
                let before_size = to.linear_terms.len();
                to.linear_terms.extend(from.linear_terms);
                to.linear_terms.sort();
                to.linear_terms.dedup();
                merge_a = merge_a || to.linear_terms.len() != before_size;
            }
        }

        DidMerge(merge_a, true)
    }

    // We don't modify the eclass based on variable age.
    // Just add the constants we get from constant folding.
    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some((c, lhs, subst)) = egraph[id].data.constant.clone() {
            let mut const_pattern = PatternAst::default();
            const_pattern.add(ENodeOrVar::ENode(EVM::new(c)));
            let (id, _added) = egraph.union_instantiations(
                &lhs,
                &const_pattern,
                &subst,
                "constant_folding",
            );

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
        // rewrite!("assoc-add"; "(+ ?a (+ ?b ?c))" <=> "(+ (+ ?a ?b) ?c)"),
    ]
    .concat();

    uni_dirs.append(&mut bi_dirs);
    uni_dirs
}

// Get the eclass ids for all eclasses in an egraph
fn _ids(egraph: &EGraph) -> Vec<egg::Id> {
    egraph.classes().map(|c| c.id).collect()
}

pub struct TacOptimizer {}

impl TacOptimizer {
    fn find_variables(&self, egraph: &EGraph, id: Id) -> Vec<EVM> {
        // todo
        return vec![];
    }

    fn find_nonzero_constants(&self, egraph: &EGraph, id: Id) -> Vec<EVM> {
        if let Some(c) = &egraph[id].data.constant {
            if c.0 != "0".parse().unwrap() {
                return vec![EVM::Num(WrappedU256 { value: c.0 })];
            }
        }
        return vec![];
    }

    fn find_nonzero_nonone_constants(&self, egraph: &EGraph, id: Id) -> Vec<EVM> {
        if let Some(c) = &egraph[id].data.constant {
            if c.0 != "0".parse().unwrap() && c.0 != "1".parse().unwrap() {
                return vec![EVM::Num(WrappedU256 { value: c.0 })];
            }
        }
        return vec![];
    }

    fn pattern_substitute(
        &self,
        pattern: &Pattern<EVM>,
        subst: &HashMap<Var, RecExpr<EVM>>,
    ) -> RecExpr<EVM> {
        let mut new_egraph = egg::EGraph::<EVM, ()>::new(());

        let mut new_subst = Subst::default();
        for (var, expr) in subst {
            let new_id = new_egraph.add_expr(&expr);
            new_subst.insert(*var, new_id);
        }

        let root = new_egraph.add_instantiation(&pattern.ast, &new_subst);
        let get_first_enode = |id| new_egraph[id].nodes[0].clone();
        get_first_enode(root).build_recexpr(get_first_enode)
    }

    // Attempts to find as many linear equations as possible, and may return some non-linear ones as well
    fn find_linear_equations(
        &self,
        egraph: &EGraph,
        id: Id,
        current_variable: EVM,
    ) -> Vec<RecExpr<EVM>> {
        // Non-zero constant variables
        let const_variables: HashSet<Var> = HashSet::from_iter(
            vec!["?c", "?m", "?n"]
                .into_iter()
                .map(|v| v.parse().unwrap()),
        );
        // non-zero, non-one constants
        let nonone_const_variables: HashSet<Var> = HashSet::from_iter(
            vec!["?c1", "?m1", "?n1"]
                .into_iter()
                .map(|v| v.parse().unwrap()),
        );
        // variables
        let variable_variables: HashSet<Var> = HashSet::from_iter(
            vec!["?x", "?y", "?z"]
                .into_iter()
                .map(|v| v.parse().unwrap()),
        );

        let searchers: Vec<Pattern<EVM>> = vec![
            "0",                                // zero
            "?c",                               // non-zero constants
            "?x",                               // variables
            "(+ ?x ?y)",                        // two variables
            "(+ ?c ?y)",                        // constant and variable
            "(+ (* ?c1 ?x) ?c)",                // constant and variable multiple
            "(+ (* ?c1 ?x) ?y)",                // two variables
            "(+ (* ?c1 ?x) (* ?m1 ?y))",        // two variables with multipliers
            "(+ ?x (+ ?y ?z))",                 // three variables
            "(+ ?c (+ ?y ?z))",                 // one constant, two variables
            "(+ (* ?c1 ?x) (+ ?x ?y))",         // three variables
            "(+ (* ?c1 ?x) (+ ?y ?c))",         // two vars, one constant
            "(+ (* ?c1 ?x) (+ (* ?m1 ?y) ?z))", // three variables
            "(+ (* ?c1 ?x) (+ (* ?m1 ?y) ?c))", // two variables, one constant
                                                //"(+ (* ?c1 ?x) (+ (* ?m1 ?y) (* ?n1 ?z)))", // three variables
        ]
        .into_iter()
        .map(|s| s.parse().unwrap())
        .collect();

        let mut results = vec![];
        for searcher in searchers {
            if let Some(matches) = searcher.search_eclass(egraph, id) {
                for subst in matches.substs {
                    let mut possibilities: Vec<Vec<EVM>> = vec![];
                    let mut vars_seen: HashSet<EVM> = Default::default();
                    vars_seen.insert(current_variable.clone());
                    for var in &searcher.vars() {
                        let class = subst.get(*var).unwrap();
                        let mut nodes = vec![];
                        let in_const = const_variables.contains(var);
                        let in_var = variable_variables.contains(var);
                        let in_nonone_const = nonone_const_variables.contains(var);
                        if in_const {
                            nodes.extend(self.find_nonzero_constants(egraph, *class));
                        }
                        if in_nonone_const {
                            nodes.extend(self.find_nonzero_nonone_constants(egraph, *class));
                        }
                        if in_var {
                            let vars: Vec<EVM> = self.find_variables(egraph, *class);
                            for v in vars.into_iter() {
                                if !vars_seen.contains(&v) {
                                    nodes.push(v.clone());
                                }
                                vars_seen.insert(v);
                            }
                        }
                        possibilities.push(nodes);
                    }

                    for product in possibilities
                        .into_iter()
                        .map(|v| v.into_iter())
                        .multi_cartesian_product()
                    {
                        let mut subst: HashMap<Var, RecExpr<EVM>> = HashMap::new();
                        for (i, var) in searcher.vars().iter().enumerate() {
                            subst.insert(*var, product[i].build_recexpr(|_id| unreachable!()));
                        }

                        results.push(self.pattern_substitute(&searcher, &subst));
                    }
                }
            }
        }

        results
    }

    pub fn run(self, params: OptParams, block_assgns: Vec<EggAssign>) -> Vec<EggAssign> {
        let analysis = TacAnalysis {
            age_map: Default::default(),
        };
        let mut egraph = EGraph::new(analysis).with_explanations_enabled();
        for (index, assign) in block_assgns.iter().enumerate() {
            egraph
                .analysis
                .age_map
                .insert(egg::Symbol::from(assign.lhs.clone()), index + 1);
        }

        let mut variable_roots: HashMap<Symbol, Id> = Default::default();
        // add lhs and rhs of each assignment to a new egraph
        // and union their eclasses
        for assign in &block_assgns {
            let rhs = assign.rhs.clone();
            assert!(!rhs.is_empty(), "RHS of this assignment is empty!");
            let rhs_parsed: RecExpr<EVM> = rhs.parse().unwrap();
            let mut rhs_pattern: PatternAst<EVM> = Default::default();
            let mut subst = Subst::default();
            let mut subst_size = 0;
            for node in rhs_parsed.as_ref() {
                if let EVM::Var(name) = node {
                    // add unbound variables to the egraph
                    if variable_roots.get(name).is_none() {
                        variable_roots.insert(*name, egraph.add(node.clone()));
                    }
                    let var = ("?".to_string() + &format!("{}", subst_size))
                        .parse()
                        .unwrap();
                    subst.insert(var, *variable_roots.get(name).unwrap());
                    subst_size += 1;
                    rhs_pattern.add(ENodeOrVar::Var(var));
                } else {
                    rhs_pattern.add(ENodeOrVar::ENode(node.clone()));
                }
            }

            let id = egraph.add_instantiation(&rhs_pattern, &subst);
            variable_roots.insert(assign.lhs.parse().unwrap(), id);
        }
        log::info!("Done adding terms to the egraph.");

        // put all the byte queries in
        for assign in &block_assgns {
            is_byte_array_length_computation(&variable_roots, &mut egraph, &assign);
        }

        // run eqsat with the domain rules
        let mut runner: Runner<EVM, TacAnalysis> = Runner::new(egraph.analysis.clone())
            .with_egraph(egraph)
            .with_iter_limit(params.eqsat_iter_limit)
            .with_node_limit(params.eqsat_node_limit)
            .with_scheduler(egg::SimpleScheduler);
        runner = runner.run(&logical_rules());
        log::info!("Done running rules.");

        let mut keep_same = vec![];
        for assign in &block_assgns {
            keep_same.push(is_byte_array_length_computation(&variable_roots, &mut runner.egraph, assign))
        }

        let mut res = vec![];
        let extract_linear = Extractor::new(&runner.egraph, LinearCostFn {});
        let extract_ordinary = Extractor::new(&runner.egraph, GeneralCostFn {});
        //runner.egraph.dot().to_svg("target/foo.svg").unwrap();
        for (assign, keep_this_same) in block_assgns.iter().zip(keep_same.iter()) {
            let current_var: Symbol = assign.lhs.parse().unwrap();
            let id = variable_roots.get(&current_var).unwrap();
            
            let best_r = if *keep_this_same {
                assign.rhs.clone()
            } else {
                let (cost1, best1) = extract_linear.find_best(*id);
                let (cost2, best2) = extract_ordinary.find_best(*id);
                let factor: BigUint = "4".parse().unwrap();
                if cost1 < cost2 * factor {
                    best1.to_string()
                } else {
                    best2.to_string()
                }
            };
            let assg = EggAssign::new(&current_var.to_string(), &best_r.to_string());
            res.push(assg);
        }
        res
    }
}

fn is_byte_array_length_computation(variable_roots: &HashMap<Symbol, Id>, egraph: &mut EGraph, assignment: &EggAssign) -> bool {
    assignment.indexWrites.iter().any(|write| {
        let lhs_id = variable_roots.get(&assignment.lhs.parse().unwrap());
        let nextfp_id = variable_roots.get(&assignment.nextFp.parse().unwrap());
        let write_id = variable_roots.get(&write.parse().unwrap());
        if lhs_id == None || nextfp_id == None || write_id == None {
            return false;
        }
        let mut left_subst = Subst::default();
        left_subst.insert("lhs".parse().unwrap(), *lhs_id.unwrap());
        let mut right_subst = Subst::default();
        right_subst.insert("nextFp".parse().unwrap(), *nextfp_id.unwrap());
        right_subst.insert("write".parse().unwrap(), *write_id.unwrap());

        let left = egraph.add_instantiation(&"(+ ?lhs 32)".parse().unwrap(), &left_subst);
        let right = egraph.add_instantiation(&"(- ?nextFp ?write)".parse().unwrap(), &right_subst);

        left == right
    })
}

fn start(ss: Vec<EggAssign>) -> Vec<EggAssign> {
    let mut seen = HashSet::new();
    for assign in ss.iter() {
        if seen.contains(&assign.lhs) {
            panic!("Duplicate assignment: {:?}", assign);
        }
        seen.insert(assign.lhs.clone());
    }

    let params: OptParams = OptParams::default();
    TacOptimizer {}.run(params, ss)
}

// Entry point
pub fn start_optimize(assignments: Sexp) -> String {
    let mut ss: Vec<EggAssign> = vec![];

    if let Sexp::List(ref list) = assignments {
        for pair in list {
            if let Sexp::List(ref pair_list) = pair {
                assert_eq!(pair_list.len(), 4);
                let options = (pair_list.get(0), pair_list.get(1), pair_list.get(3));
                let indexWritesSexp = pair_list.get(2).unwrap();
                let indexWrites = if let Sexp::List(ref indexVars) = indexWritesSexp {
                    indexVars
                        .iter()
                        .map(|x| {
                            if let Sexp::String(ref x) = x {
                                x.clone()
                            } else {
                                panic!("Expected symbol")
                            }
                        })
                        .collect()
                } else {
                    panic!("Index writes is not a list!");
                };
                if let (Some(Sexp::String(lhs)), Some(rhs), Some(Sexp::String(nextFp))) = options {
                    ss.push(EggAssign {
                        lhs: lhs.clone(),
                        rhs: rhs.to_string(),
                        indexWrites,
                        nextFp: nextFp.clone(),
                    });
                } else {
                    panic!("Invalid assignment pair: {:?}", pair_list);
                }
            } else {
                panic!("Expected a list of pairs!");
            }
        }
    } else {
        panic!("Expected a list of assignments!");
    }

    let mut res = vec![];
    for assignment in start(ss) {
        let right = parse_str(&assignment.rhs).unwrap();
        res.push(Sexp::List(vec![Sexp::String(assignment.lhs), right]));
    }

    Sexp::List(res).to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use egg::{RecExpr, Symbol};
    use primitive_types::U256;
    use rust_evm::{eval_evm, WrappedU256, EVM};

    fn check_test(input: Vec<EggAssign>, expected: Vec<EggAssign>) {
        let actual = start(input);
        println!("{:#?}", actual);
        let actualSet: HashSet<EggAssign> = HashSet::from_iter(actual.into_iter());
        let expectedSet: HashSet<EggAssign> = HashSet::from_iter(expected.into_iter());

        assert!(expectedSet.is_subset(&actualSet));
    }

    #[test]
    fn test1() {
        let input = vec![
            EggAssign::new("R194", "64"),
            EggAssign::new("R198", "(+ 32 R194)"),
            EggAssign::new("R202", "(- R198 R194)"),
        ];
        let expected = vec![
            EggAssign::new("R194", "64"),
            EggAssign::new("R198", "96"),
            EggAssign::new("R202", "32"),
        ];
        check_test(input, expected);
    }

    #[test]
    fn test2() {
        let input = vec![
            EggAssign::new("x1", "(+ x2 96)"),
            EggAssign::new("x3", "(- x1 32)"),
            EggAssign::new("x4", "(- x3 x2)"),
        ];
        let expected = vec![
            EggAssign::new("x1", "(+ x2 96)"),
            EggAssign::new("x3", "(+ x2 64)"),
            EggAssign::new("x4", "64"),
        ];
        check_test(input, expected);
    }

    #[test]
    fn test4() {
        let input = vec![
            EggAssign::new("R1", "64"),
            EggAssign::new("R2", "(+ 32 R1)"),
        ];
        let expected = vec![EggAssign::new("R1", "64"), EggAssign::new("R2", "96")];
        check_test(input, expected);
    }

    #[test]
    fn test5() {
        let input = vec![
            EggAssign::new("R1", "64"),
            EggAssign::new("R2", "(- 32 R1)"),
        ];
        let expected =
            vec![
            EggAssign::new("R1", "64"),
            EggAssign::new("R2",
                "115792089237316195423570985008687907853269984665640564039457584007913129639904"),
        ];
        check_test(input, expected);
    }

    #[test]
    fn test6() {
        let input = vec![
            EggAssign::new("R1", "64"),
            EggAssign::new("R2", "(- R1 32)"),
        ];
        let expected = vec![EggAssign::new("R1", "64"), EggAssign::new("R2", "32")];
        check_test(input, expected);
    }

    #[test]
    fn test7() {
        let input = vec![EggAssign::new("R1", "(- 5 0)")];

        let expected = vec![EggAssign::new("R1", "5")];
        check_test(input, expected);
    }

    #[test]
    fn parse_test1() {
        let from_string: RecExpr<EVM> = "(+ x 0)".to_string().parse().unwrap();
        let v1 = EVM::Var(Symbol::from("x"));
        let v2 = EVM::Num(WrappedU256 {
            value: U256::zero(),
        });
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

/*
stuff to investigate
R2304 = tacM0x40
R2307 = (+ tacM0x40 32)
R2310 = (+ tacM0x40 64)
R2320 = (+ tacM0x40 96)
R2322 = (+ tacM0x40 128)
R2328 = (+ tacM0x40 160)
R2330 = (+ tacM0x40 192)
R2335 = tacM0x40
R2349 = (+ tacM0x40 224)
tacM0x40 = R2349
R2361 = (+ tacM0x40 256)
R2395 = (+ tacM0x40 322)
tacM0x40 = R2395
R2560 = tacM0x40
R2564 = (+ 32 R2560)
tacM0x40.1375 = R2564
R2565 = tacM0x40.1375
R2570 = (+ 32 R2565)
R2574 = (& 255 R1284)
R2577 = (+ 32 R2570)
R2581 = (+ 32 R2577)
R2585 = (+ 32 R2581)
R2588 = 32
R2589 = tacM0x40.1375
R2591 = (- R2589 32)
R2598 = (- R2585 R2589)
R2603 = 1
R2605 = tacRC
B2608 = (== R2605 0)
B2614 = (! B2608)
*/
