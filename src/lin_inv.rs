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

type BlockId = Symbol;

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct EggBlock {
    pub id: BlockId,
    pub predecessors: Vec<BlockId>,
    pub assignments: Vec<EggAssign>,
}

impl EggBlock {
    pub fn from_sexp(expr: &Sexp) -> EggBlock {
        match expr {
            Sexp::List(contents) => match &contents[..] {
                [Sexp::String(block_string), Sexp::String(id), Sexp::List(predecessors), Sexp::List(assignments)] => {
                    if block_string != "block" {
                        panic!("Expected keyword block, got {}", block_string);
                    }
                    EggBlock {
                        id: id.into(),
                        predecessors: predecessors.iter().map(|parent| {
                            if let Sexp::String(pred) = parent {
                                pred.into()
                            } else {
                                panic!("Expected string for block parent, got {}", parent)
                            }
                        }).collect(),
                        assignments: assignments
                            .into_iter()
                            .map(|pair| EggAssign::from_sexp(pair))
                            .collect(),
                    }
                },
                _ => panic!("Expected a block, got: {}", expr),
            },
            _ => panic!("Expected an id and expressions for a block, got: {}", expr),
        }
    }

    pub fn to_sexp(&self) -> Sexp {
        Sexp::List(vec![
            Sexp::String("block".to_string()),
            Sexp::String(self.id.to_string()),
            Sexp::List(self.predecessors.iter().map(|id| Sexp::String(id.to_string())).collect()),
            Sexp::List(
                self.assignments
                    .iter()
                    .map(|assign| assign.to_sexp())
                    .collect(),
            ),
        ])
    }

    pub fn rename_variables(
        &self,
        name_to_original: &mut HashMap<Symbol, (BlockId, Symbol)>,
        original_to_name: &mut HashMap<(Symbol, BlockId), Symbol>,
    ) -> EggBlock {
        let mut new_assignments = Vec::new();
        for assign in self.assignments.iter() {
            new_assignments.push(assign.rename_variables(
                self.id,
                name_to_original,
                original_to_name,
            ));
        }

        EggBlock {
            id: self.id,
            predecessors: self.predecessors.clone(),
            assignments: new_assignments,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct EggAssign {
    pub lhs: Symbol,
    pub rhs: RecExpr<EVM>,
}

impl EggAssign {
    pub fn new(lhs: &str, rhs: &str) -> Self {
        Self {
            lhs: lhs.into(),
            rhs: rhs.parse().unwrap(),
        }
    }

    pub fn from_sexp(expr: &Sexp) -> EggAssign {
        if let Sexp::List(inner) = expr {
            if inner.len() != 2 {
                panic!("Expected assignment to have length 2, got: {:?}", inner);
            }
            if let Sexp::String(lhs) = &inner[0] {
                EggAssign::new(lhs, &inner[1].to_string())
            } else {
                panic!("Expected variable on lhs, got: {}", inner[0]);
            }
        } else {
            panic!("Expected an assignment, got: {}", expr);
        }
    }

    pub fn to_sexp(&self) -> Sexp {
        Sexp::List(vec![
            Sexp::String(self.lhs.to_string()),
            parse_str(&self.rhs.to_string()).unwrap(),
        ])
    }

    pub fn rename_variables(
        &self,
        block: BlockId,
        name_to_original: &mut HashMap<Symbol, (BlockId, Symbol)>,
        original_to_name: &mut HashMap<(Symbol, BlockId), Symbol>,
    ) -> EggAssign {
        let mut new_rhs: RecExpr<EVM> = Default::default();
        for node in self.rhs.as_ref() {
            if let EVM::Var(var) = node {
                if let Some(existing) = original_to_name.get(&(block, *var)) {
                    new_rhs.add(EVM::Var(existing.clone()));
                } else {
                    let new_var = format!("var_{}", name_to_original.len());
                    original_to_name.insert((block, *var), new_var.clone().into());
                    name_to_original.insert(new_var.clone().into(), (block, *var));
                    new_rhs.add(EVM::Var(new_var.clone().into()));
                }
            } else {
                new_rhs.add(node.clone());
            }
        }

        let new_lhs = format!("var_{}", name_to_original.len()).into();
        original_to_name.insert((block, self.lhs), new_lhs);
        name_to_original.insert(new_lhs, (block, self.lhs));

        EggAssign {
            lhs: new_lhs.into(),
            rhs: new_rhs,
        }
    }

    pub fn rename_back(self, name_to_original: &HashMap<Symbol, (BlockId, Symbol)>) -> EggAssign {
        let old_lhs = name_to_original.get(&self.lhs).unwrap().1;
        let mut old_rhs: RecExpr<EVM> = Default::default();
        for node in self.rhs.as_ref() {
            if let EVM::Var(var) = node {
                let old_var = name_to_original.get(&var).unwrap().1;
                old_rhs.add(EVM::Var(old_var.clone()));
            } else {
                old_rhs.add(node.clone());
            }
        }

        EggAssign {
            lhs: old_lhs.clone(),
            rhs: old_rhs,
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
            EVM::Num(n) => {
                if n.value < "1000".parse().unwrap() {
                    "1".parse().unwrap()
                } else {
                    num_value
                }
            }
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
            EVM::Num(n) => {
                if n.value < "1000".parse().unwrap() {
                    "1".parse().unwrap()
                } else {
                    num_value
                }
            }
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
            let (id, _added) =
                egraph.union_instantiations(&lhs, &const_pattern, &subst, "constant_folding");

            assert!(
                !egraph[id].nodes.is_empty(),
                "empty eclass! {:#?}",
                egraph[id]
            );
        }
    }
}

// some standard axioms, not used anymore in favor of ruler
/*
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
}*/

// Get the eclass ids for all eclasses in an egraph
fn _ids(egraph: &EGraph) -> Vec<egg::Id> {
    egraph.classes().map(|c| c.id).collect()
}

pub struct TacOptimizer {}

impl TacOptimizer {
    pub fn run(self, params: OptParams, blocks: Vec<EggBlock>) -> Vec<EggBlock> {
        let analysis = TacAnalysis {
            age_map: Default::default(),
        };
        let mut egraph = EGraph::new(analysis).with_explanations_enabled();
        let mut original_to_name = Default::default();
        let mut name_to_original = Default::default();
        let renamed_blocks: Vec<EggBlock> = blocks
            .iter()
            .map(|block| block.rename_variables(&mut name_to_original, &mut original_to_name))
            .collect();
        
        let mut variable_roots: HashMap<Symbol, Id> = Default::default();
        for block in renamed_blocks.iter() {
            for assign in block.assignments.iter() {
                let mut rhs_pattern: PatternAst<EVM> = Default::default();
                let mut subst = Subst::default();
                let mut subst_size = 0;
                for node in assign.rhs.as_ref() {
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
                variable_roots.insert(assign.lhs, id);
            }
        }

        log::info!("Done adding terms to the egraph.");

        // run eqsat with the domain rules
        let mut runner: Runner<EVM, TacAnalysis> = Runner::new(egraph.analysis.clone())
            .with_egraph(egraph)
            .with_iter_limit(params.eqsat_iter_limit)
            .with_node_limit(params.eqsat_node_limit)
            .with_scheduler(egg::SimpleScheduler);
        runner = runner.run(&logical_rules());
        log::info!("Done running rules.");

        let mut final_blocks = vec![];
        let extract_linear = Extractor::new(&runner.egraph, LinearCostFn {});
        let extract_ordinary = Extractor::new(&runner.egraph, GeneralCostFn {});
        //runner.egraph.dot().to_svg("target/foo.svg").unwrap();

        for block in renamed_blocks {
            let mut new_assignments = vec![];

            for assignment in block.assignments {
                let rhs_id = variable_roots.get(&assignment.lhs).unwrap();
                let (cost1, best1) = extract_linear.find_best(*rhs_id);
                let (cost2, best2) = extract_ordinary.find_best(*rhs_id);
                let factor: BigUint = "4".parse().unwrap();

                let new_assignment = EggAssign {
                    lhs: assignment.lhs,
                    rhs: if cost1 < cost2 * factor { best1 } else { best2 },
                };
                new_assignments.push(new_assignment.rename_back(&name_to_original));
            }

            final_blocks.push(EggBlock {
                id: block.id,
                predecessors: block.predecessors,
                assignments: new_assignments,
            });
        }
        final_blocks
    }
}

fn start_blocks(blocks: Vec<EggBlock>) -> Vec<EggBlock> {
    let params: OptParams = OptParams::default();
    TacOptimizer {}.run(params, blocks)
}

// Entry point
pub fn start_optimize(blocks_in: Sexp) -> String {
    let mut blocks: Vec<EggBlock> = vec![];

    if let Sexp::List(list) = blocks_in {
        for block in list.into_iter() {
            blocks.push(EggBlock::from_sexp(&block));
        }
    }

    let blocks_list = start_blocks(blocks)
        .iter()
        .map(|block| block.to_sexp())
        .collect();

    Sexp::List(blocks_list).to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use egg::{RecExpr, Symbol};
    use primitive_types::U256;
    use rust_evm::{eval_evm, WrappedU256, EVM};

    fn check_test(input: Vec<EggAssign>, expected: Vec<EggAssign>) {
        let mut actual_blocks = start_blocks(vec![EggBlock {
            id: "whatever".into(),
            predecessors: vec![],
            assignments: input,
        }]);
        assert_eq!(actual_blocks.len(), 1);
        let actual = actual_blocks.pop().unwrap().assignments;
        let actualSet: HashSet<String> =
            HashSet::from_iter(actual.into_iter().map(|expr| expr.to_sexp().to_string()));
        let expectedSet: HashSet<String> =
            HashSet::from_iter(expected.into_iter().map(|expr| expr.to_sexp().to_string()));

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

    #[test]
    fn full_program1() {
        let program_sexp = "((block block1 (
            (a 2)
            (b a)
            (a (+ a 4))
            (a (* a 3))
        ))
            (block block2 (
                (b a)
                (b (* 2 (+ b 1)))
                (b (* 2 b))
            ))
        )";
        let expected = "((block block1 (
                (a 2)
                (b 2)
                (a 6)
                (a 18)
            ))
            (block block2 (
                (b a)
                (b (+ 2 (* 2 a)))
                (b (+ 4 (* 4 a)))
            ))
        )";
        let result = start_optimize(parse_str(program_sexp).unwrap());
        println!("{}", result);
        assert_eq!(parse_str(&result).unwrap(), parse_str(expected).unwrap());
    }

    #[test]
    fn full_program2() {
         let program_sexp = "((block 0_0_0_0_0_0_0_0 () ((currentContract 274184521717934524641157099916833587208) (certoraTmpBool 1) (certoraTmpBool (&& (<= 0 targetAddress) (<= targetAddress 1461501637330902918203684832716283019655932542975))) (tacTmpreplacement8044 tacS!ce4604a0000000000000000000000008!0!0) (certoraTmpBool (&& (<= 0 tacTmpreplacement8044) (<= tacTmpreplacement8044 1461501637330902918203684832716283019655932542975))) (tacTmpreplacement8045 tacS!ce4604a0000000000000000000000008!11!0) (certoraTmpBool (&& (<= 0 tacTmpreplacement8045) (<= tacTmpreplacement8045 1461501637330902918203684832716283019655932542975))) (tacTmpreplacement8046 tacS!ce4604a0000000000000000000000008!10!0) (certoraTmpBool (&& (<= 0 tacTmpreplacement8046) (<= tacTmpreplacement8046 1461501637330902918203684832716283019655932542975))) (tacTmpreplacement8047 tacS!ce4604a0000000000000000000000008!12!0) (certoraTmpBool (&& (<= 0 tacTmpreplacement8047) (<= tacTmpreplacement8047 1461501637330902918203684832716283019655932542975))) (tacTmpreplacement8048 tacS!ce4604a0000000000000000000000008!17!0) (certoraTmpBool (&& (<= 0 tacTmpreplacement8048) (<= tacTmpreplacement8048 255))) (tacTmpreplacement8049 tacS!ce4604a0000000000000000000000008!5!0) (certoraTmpBool (&& (<= 0 tacTmpreplacement8049) (<= tacTmpreplacement8049 255))) (tacTmpreplacement8050 tacS!ce4604a0000000000000000000000008!1!0) (certoraTmpBool (&& (<= 0 tacTmpreplacement8050) (<= tacTmpreplacement8050 1461501637330902918203684832716283019655932542975))) (tacTmpreplacement8051 tacS!ce4604a0000000000000000000000008!13!0) (certoraTmpBool (&& (<= 0 tacTmpreplacement8051) (<= tacTmpreplacement8051 1461501637330902918203684832716283019655932542975))) (tacTmp!274184521717934524641157099916833587208!cmp (>= tacTmp274184521717934524641157099916833587208!start!balance 0)) (certoraTmpBool (&& (<= 0 tacTmpstructAccess2852) (<= tacTmpstructAccess2852 1461501637330902918203684832716283019655932542975))) (certoraTmpBool (&& (<= 0 tacTmpstructAccess2856) (<= tacTmpstructAccess2856 1461501637330902918203684832716283019655932542975))) (tacTmpcvlArg2861 targetAddress) (certoraArg0bv256 tacTmpcvlArg2861))) (block 0_0_0_0_50_0_748_0 (0_0_0_0_0_0_0_0) ((tacCaller e.msg.sender) (certoraTmpBool (&& (<= 0 tacCaller@50) (<= tacCaller@50 1461501637330902918203684832716283019655932542975))) (tacCallvalue e.msg.value) (certoraTmpBool (== tacAddress@50 e.msg.address)) (certoraTmpBool (&& (<= 0 tacAddress@50) (<= tacAddress@50 1461501637330902918203684832716283019655932542975))) (tacAddress 274184521717934524641157099916833587208) (certoraTmpBool (&& (<= 0 tacOrigin@50) (<= tacOrigin@50 1461501637330902918203684832716283019655932542975))) (B1 (> R0@50 0)) (B21 (== 117300739 tacSighash@50)) (B30 (== 157198259 tacSighash@50)) (B44 (== 325542942 tacSighash@50)) (B156 (== 404098525 tacSighash@50)) (B198 (== 562397451 tacSighash@50)) (B307 (== 566080110 tacSighash@50)) (B429 (== 599290589 tacSighash@50)) (B627 (== 826074471 tacSighash@50)) (B814 (== 832031670 tacSighash@50)) (B906 (== 1173877321 tacSighash@50)) (B955 (== 1364493914 tacSighash@50)) (B1075 (== 1513848386 tacSighash@50)) (B1152 (== 1580545438 tacSighash@50)) (B1213 (== 1617670136 tacSighash@50)) (B1423 (== 1778827154 tacSighash@50)) (B1539 (== 1889567281 tacSighash@50)) (B1638 (== tacCallvalue@50 0)) (R1760 (& 1461501637330902918203684832716283019655932542975 certoraArg0bv256)) (tacM0x0 R1760@50) (tacTmpretSym R1910@50) (lastReverted 0) (tacRetval0 R1910@50) (certoraOutVar0bv256 tacRetval0@50))) (block 1112_0_0_0_0_0_0_0 (0_0_0_0_50_0_748_0) ((origBalanceOfTarget certoraOutVar0bv256) (tacTmp2866 2835717307) (tacTmp2867 599290589) (tacTmp2865 1) (tacTmp2869 2835717307) (tacTmp2870 2835717307) (tacTmp2868 0) (certoraAssume2864 0) (certoraTmpBool (&& (<= 0 tacTmpstructAccess2872) (<= tacTmpstructAccess2872 1461501637330902918203684832716283019655932542975))) (certoraTmpBool (&& (<= 0 tacTmpstructAccess2876) (<= tacTmpstructAccess2876 1461501637330902918203684832716283019655932542975))) (tacOrigS!ce4604a0000000000000000000000008!2374 tacS!ce4604a0000000000000000000000008!3) (tacOrigS!ce4604a0000000000000000000000008!2375 tacS!ce4604a0000000000000000000000008!StructAccess(base=ArrayAccess(base=Root(slot=3)), offset=0)) (tacOrigS!ce4604a0000000000000000000000008!2376 tacS!ce4604a0000000000000000000000008!StructAccess(base=MapAccess(base=StructAccess(base=MapAccess(base=Root(slot=8)), offset=0)), offset=0)) (tacOrigS!ce4604a0000000000000000000000008!2377 tacS!ce4604a0000000000000000000000008!0!0) (tacOrigS!ce4604a0000000000000000000000008!2378 tacS!ce4604a0000000000000000000000008!14) (tacOrigS!ce4604a0000000000000000000000008!2379 tacS!ce4604a0000000000000000000000008!11!0) (tacOrigS!ce4604a0000000000000000000000008!2380 tacS!ce4604a0000000000000000000000008!StructAccess(base=MapAccess(base=Root(slot=7)), offset=0)) (tacOrigS!ce4604a0000000000000000000000008!2381 tacS!ce4604a0000000000000000000000008!16) (tacOrigS!ce4604a0000000000000000000000008!2382 tacS!ce4604a0000000000000000000000008!9) (tacOrigS!ce4604a0000000000000000000000008!2383 tacS!ce4604a0000000000000000000000008!10!0) (tacOrigS!ce4604a0000000000000000000000008!2384 tacS!ce4604a0000000000000000000000008!12!0) (tacOrigS!ce4604a0000000000000000000000008!2385 tacS!ce4604a0000000000000000000000008!17!0) (tacOrigS!ce4604a0000000000000000000000008!2386 tacS!ce4604a0000000000000000000000008!5!0) (tacOrigS!ce4604a0000000000000000000000008!2387 tacS!ce4604a0000000000000000000000008!2) (tacOrigS!ce4604a0000000000000000000000008!2388 tacS!ce4604a0000000000000000000000008!StructAccess(base=ArrayAccess(base=Root(slot=2)), offset=0)) (tacOrigS!ce4604a0000000000000000000000008!2389 tacS!ce4604a0000000000000000000000008!1!0) (tacOrigS!ce4604a0000000000000000000000008!2390 tacS!ce4604a0000000000000000000000008!4) (tacOrigS!ce4604a0000000000000000000000008!2391 tacS!ce4604a0000000000000000000000008!StructAccess(base=ArrayAccess(base=Root(slot=4)), offset=0)) (tacOrigS!ce4604a0000000000000000000000008!2392 tacS!ce4604a0000000000000000000000008!15) (tacOrigS!ce4604a0000000000000000000000008!2393 tacS!ce4604a0000000000000000000000008!19) (tacOrigS!ce4604a0000000000000000000000008!2394 tacS!ce4604a0000000000000000000000008!18) (tacOrigS!ce4604a0000000000000000000000008!2395 tacS!ce4604a0000000000000000000000008!13!0) (tacOrigS!ce4604a0000000000000000000000008!2396 egg_var_0) (tacOrigBalance!2397 egg_var_1) (tacOrigNonce!2397 egg_var_2) (tacCalldatabuf!4 arg!4) (tacCalldatabuf!36 arg!36) (tacCalldatasize arg!size) (tacTmpBool (s< 67 arg!size)) (tacCaller ef.msg.sender) (certoraTmpBool (&& (<= 0 tacCaller@51) (<= tacCaller@51 1461501637330902918203684832716283019655932542975))) (tacCallvalue ef.msg.value) (certoraTmpBool (== tacAddress@51 ef.msg.address)) (certoraTmpBool (&& (<= 0 tacAddress@51) (<= tacAddress@51 1461501637330902918203684832716283019655932542975))) (tacAddress 274184521717934524641157099916833587208) (certoraTmpBool (&& (<= 0 tacOrigin@51) (<= tacOrigin@51 1461501637330902918203684832716283019655932542975))) (tacTimestamp ef.block.timestamp))) (block 1131_0_0_0_0_0_0_0 (1249_0_0_0_0_0_0_0) ()) (block 1130_0_0_0_0_0_0_0 (1249_0_0_0_0_0_0_0) ((tacS!ce4604a0000000000000000000000008!3 tacOrigS!ce4604a0000000000000000000000008!2374) (tacS!ce4604a0000000000000000000000008!StructAccess(base=ArrayAccess(base=Root(slot=3)), offset=0) tacOrigS!ce4604a0000000000000000000000008!2375) (tacS!ce4604a0000000000000000000000008!StructAccess(base=MapAccess(base=StructAccess(base=MapAccess(base=Root(slot=8)), offset=0)), offset=0) tacOrigS!ce4604a0000000000000000000000008!2376) (tacS!ce4604a0000000000000000000000008!0!0 tacOrigS!ce4604a0000000000000000000000008!2377) (tacS!ce4604a0000000000000000000000008!14 tacOrigS!ce4604a0000000000000000000000008!2378) (tacS!ce4604a0000000000000000000000008!11!0 tacOrigS!ce4604a0000000000000000000000008!2379) (tacS!ce4604a0000000000000000000000008!StructAccess(base=MapAccess(base=Root(slot=7)), offset=0) tacOrigS!ce4604a0000000000000000000000008!2380) (tacS!ce4604a0000000000000000000000008!16 tacOrigS!ce4604a0000000000000000000000008!2381) (tacS!ce4604a0000000000000000000000008!9 tacOrigS!ce4604a0000000000000000000000008!2382) (tacS!ce4604a0000000000000000000000008!10!0 tacOrigS!ce4604a0000000000000000000000008!2383) (tacS!ce4604a0000000000000000000000008!12!0 tacOrigS!ce4604a0000000000000000000000008!2384) (tacS!ce4604a0000000000000000000000008!17!0 tacOrigS!ce4604a0000000000000000000000008!2385) (tacS!ce4604a0000000000000000000000008!5!0 tacOrigS!ce4604a0000000000000000000000008!2386) (tacS!ce4604a0000000000000000000000008!2 tacOrigS!ce4604a0000000000000000000000008!2387) (tacS!ce4604a0000000000000000000000008!StructAccess(base=ArrayAccess(base=Root(slot=2)), offset=0) tacOrigS!ce4604a0000000000000000000000008!2388) (tacS!ce4604a0000000000000000000000008!1!0 tacOrigS!ce4604a0000000000000000000000008!2389) (tacS!ce4604a0000000000000000000000008!4 tacOrigS!ce4604a0000000000000000000000008!2390) (tacS!ce4604a0000000000000000000000008!StructAccess(base=ArrayAccess(base=Root(slot=4)), offset=0) tacOrigS!ce4604a0000000000000000000000008!2391) (tacS!ce4604a0000000000000000000000008!15 tacOrigS!ce4604a0000000000000000000000008!2392) (tacS!ce4604a0000000000000000000000008!19 tacOrigS!ce4604a0000000000000000000000008!2393) (tacS!ce4604a0000000000000000000000008!18 tacOrigS!ce4604a0000000000000000000000008!2394) (tacS!ce4604a0000000000000000000000008!13!0 tacOrigS!ce4604a0000000000000000000000008!2395) (tacS!ce4604a0000000000000000000000008 tacOrigS!ce4604a0000000000000000000000008!2396) (tacBalance egg_var_3) (tacNonce egg_var_4))) (block 1129_0_0_0_0_0_0_1 (1131_0_0_0_0_0_0_0 1130_0_0_0_0_0_0_0) ((certoraTmpBool (&& (<= 0 tacTmpstructAccess2882) (<= tacTmpstructAccess2882 1461501637330902918203684832716283019655932542975))) (certoraTmpBool (&& (<= 0 tacTmpstructAccess2886) (<= tacTmpstructAccess2886 1461501637330902918203684832716283019655932542975))) (certoraAssume2891 (>= tacTmp2892 tacTmp2893)) (tacTmpcvlArg2894 targetAddress) (certoraArg0bv256 tacTmpcvlArg2894))) (block 0_0_0_0_52_0_750_0 (1129_0_0_0_0_0_0_1) ((tacCaller e2.msg.sender) (certoraTmpBool (&& (<= 0 tacCaller@52) (<= tacCaller@52 1461501637330902918203684832716283019655932542975))) (tacCallvalue e2.msg.value) (certoraTmpBool (== tacAddress@52 e2.msg.address)) (certoraTmpBool (&& (<= 0 tacAddress@52) (<= tacAddress@52 1461501637330902918203684832716283019655932542975))) (tacAddress 274184521717934524641157099916833587208) (certoraTmpBool (&& (<= 0 tacOrigin@52) (<= tacOrigin@52 1461501637330902918203684832716283019655932542975))) (B1 (> R0@52 0)) (B21 (== 117300739 tacSighash@52)) (B30 (== 157198259 tacSighash@52)) (B44 (== 325542942 tacSighash@52)) (B156 (== 404098525 tacSighash@52)) (B198 (== 562397451 tacSighash@52)) (B307 (== 566080110 tacSighash@52)) (B429 (== 599290589 tacSighash@52)) (B627 (== 826074471 tacSighash@52)) (B814 (== 832031670 tacSighash@52)) (B906 (== 1173877321 tacSighash@52)) (B955 (== 1364493914 tacSighash@52)) (B1075 (== 1513848386 tacSighash@52)) (B1152 (== 1580545438 tacSighash@52)) (B1213 (== 1617670136 tacSighash@52)) (B1423 (== 1778827154 tacSighash@52)) (B1539 (== 1889567281 tacSighash@52)) (B1638 (== tacCallvalue@52 0)) (R1760 (& 1461501637330902918203684832716283019655932542975 certoraArg0bv256)) (tacM0x0 R1760@52) (tacTmpretSym R1910@52) (lastReverted 0) (tacRetval0 R1910@52) (certoraOutVar0bv256 tacRetval0@52))) (block 1218_0_0_0_0_0_0_0 (0_0_0_0_52_0_750_0) ((newBalanceOfTarget certoraOutVar0bv256) (tacTmp2897 newBalanceOfTarget) (tacTmp2898 origBalanceOfTarget) (certoraAssert_21 (== tacTmp2897 tacTmp2898)))) (block 0_0_0_0_51_0_929_0 (1112_0_0_0_0_0_0_0) ((B1 (> R0@51 0)) (B4 (< tacCalldatasize@51 4)) (B21 (== 117300739 tacSighash@51)) (B30 (== 157198259 tacSighash@51)) (B44 (== 325542942 tacSighash@51)) (B156 (== 404098525 tacSighash@51)) (B198 (== 562397451 tacSighash@51)) (B307 (== 566080110 tacSighash@51)) (B429 (== 599290589 tacSighash@51)) (B627 (== 826074471 tacSighash@51)) (B814 (== 832031670 tacSighash@51)) (B906 (== 1173877321 tacSighash@51)) (B955 (== 1364493914 tacSighash@51)) (B1075 (== 1513848386 tacSighash@51)) (B1152 (== 1580545438 tacSighash@51)) (B1213 (== 1617670136 tacSighash@51)) (B1423 (== 1778827154 tacSighash@51)) (B1539 (== 1889567281 tacSighash@51)) (B1642 (== 1947540010 tacSighash@51)) (B1780 (== 2042253463 tacSighash@51)) (B1924 (== 2376452955 tacSighash@51)) (B2086 (== 2514000705 tacSighash@51)) (B2231 (== 2530529425 tacSighash@51)) (B2532 (== 2562853888 tacSighash@51)) (B2713 (== 2821965739 tacSighash@51)) (B2809 (== 2835717307 tacSighash@51)) (B2998 (== tacCallvalue@51 0)))) (block 2099_1023_0_0_51_0_930_0 (0_0_0_0_51_0_929_0) ((lastReverted 1))) (block 2103_1023_0_0_51_2_931_0 (0_0_0_0_51_0_929_0) ((R3096 (& 1461501637330902918203684832716283019655932542975 egg_var_5)) (R3107 egg_var_6) (B3439 (> tacTimestamp@51 1509494340)))) (block 7891_1019_0_0_51_0_932_0 (9732_1016_0_0_51_0_941_0) ((tacTmpreplacement8052 tacS!ce4604a0000000000000000000000008!10!0) (tacTmpStorageReadEnforce!1887 (< tacTmpreplacement8052 1461501637330902918203684832716283019655932542976)) (tacTmpreplacement8053 tacS!ce4604a0000000000000000000000008!10!0) (B3920 (== tacCaller@51 tacTmpreplacement8053)))) (block 7973_1019_0_0_51_1_933_0 (9732_1016_0_0_51_0_941_0) ((B3918 B3833@51))) (block 7979_1019_0_0_51_0_934_0 (7891_1019_0_0_51_0_932_0) ((tacTmpreplacement8054 tacS!ce4604a0000000000000000000000008!12!0) (tacTmpStorageReadEnforce!1888 (< tacTmpreplacement8054 1461501637330902918203684832716283019655932542976)) (tacTmpreplacement8055 tacS!ce4604a0000000000000000000000008!12!0) (B4151 (== tacCaller@51 tacTmpreplacement8055)) (B3918 B4151@51))) (block 8061_1019_0_0_51_0_935_0 (7973_1019_0_0_51_1_933_0 7979_1019_0_0_51_0_934_0 7973_1019_0_0_51_0_950_0) ()) (block 8067_1020_0_0_51_0_936_0 (8061_1019_0_0_51_0_935_0) ((B4235 (== R3096@51 0)) (B4239 (! B4235@51)) (B4243 (! B4239@51)))) (block 8093_1020_0_0_51_0_937_0 (8061_1019_0_0_51_0_935_0) ((lastReverted 1))) (block 9606_1009_0_0_51_0_938_0 (11578_1010_0_0_51_0_948_0) ((lastReverted 1))) (block 9607_1009_0_0_51_0_939_0 (11578_1010_0_0_51_0_948_0) ((R4634 R4575@51) (tacM0x0 R3096@51) (R4681 R3096@51) (R4684 tacCaller@51) (R4714 1) (R4845 1) (B4872 1) (lastReverted 0) (tacRetval0 tacTmpretSym@51))) (block 9708_1016_0_0_51_0_940_0 (2103_1023_0_0_51_2_931_0) ((tacTmpreplacement8056 tacS!ce4604a0000000000000000000000008!17!0) (tacTmpStorageReadEnforce!1889 (< tacTmpreplacement8056 256)) (tacTmpreplacement8057 tacS!ce4604a0000000000000000000000008!17!0) (B3551 (== tacTmpreplacement8057 0)) (B3555 (! B3551@51)) (B3519 B3555@51))) (block 9732_1016_0_0_51_0_941_0 (9708_1016_0_0_51_0_940_0 9617_1018_0_0_51_0_949_0) ((R3746 R3663@51) (B3826 (== R3663@51 0)) (B3830 (! B3826@51)) (B3833 B3830@51))) (block 10824_1014_0_0_51_0_945_0 (8067_1020_0_0_51_0_936_0) ((lastReverted 1))) (block 10828_1014_0_0_51_0_946_0 (8067_1020_0_0_51_0_936_0) ((tacM0x0 tacCaller@51) (B4414 (< R4335@51 R3107@51)) (B4418 (! B4414@51)) (B4422 (! B4418@51)))) (block 11577_1010_0_0_51_0_947_0 (10828_1014_0_0_51_0_946_0) ((lastReverted 1))) (block 11578_1010_0_0_51_0_948_0 (10828_1014_0_0_51_0_946_0) ((R4496 (- R4335@51 R3107@51)) (R4503 R4496@51) (tacM0x0 tacCaller@51) (tacM0x0 R3096@51) (R4575 (+ R4549@51 R3107@51)) (B4583 (< R4575@51 R4549@51)) (B4587 (! B4583@51)) (B4591 (! B4587@51)))) (block 9617_1018_0_0_51_0_949_0 (2103_1023_0_0_51_2_931_0) ((B3519 B3439@51))) (block 7973_1019_0_0_51_0_950_0 (7891_1019_0_0_51_0_932_0) ((B3918 B3920@51))) (block 1249_0_0_0_0_0_0_0 (2099_1023_0_0_51_0_930_0 8093_1020_0_0_51_0_937_0 9606_1009_0_0_51_0_938_0 9607_1009_0_0_51_0_939_0 10824_1014_0_0_51_0_945_0 11577_1010_0_0_51_0_947_0) ())) ";
         let result = start_optimize(parse_str(program_sexp).unwrap());
    }
}
