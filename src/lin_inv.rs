use clap::Parser;
use egg::*;
use serde::*;
use std::cell::RefCell;
// use statement::Stmt;
use egg::{ENodeOrVar, Justification, Pattern, RecExpr};
use rust_evm::{eval_evm, BitVar, BoolVar, Constant, Type, EVM};
use std::{cmp::*, collections::HashMap, collections::HashSet};
use symbolic_expressions::parser::parse_str;
use symbolic_expressions::Sexp;

use crate::logical_equality::get_pregenerated_rules;

pub type EGraph = egg::EGraph<EVM, TacAnalysis>;
type NameToOriginal = HashMap<EVM, (EVM, BlockId)>;
type OriginalToName = HashMap<(EVM, BlockId), EVM>;
type OriginalToNames = HashMap<EVM, Vec<EVM>>;

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
    pub eqsat_iter_limit: usize,
    pub eqsat_node_limit: usize,
}

impl Default for OptParams {
    fn default() -> Self {
        Self {
            eqsat_iter_limit: 3,
            eqsat_node_limit: 50_000,
        }
    }
}

type BlockId = Symbol;

#[derive(Debug, PartialEq, Eq, Hash)]
// Rust representation of a program block
pub struct EggBlock {
    pub id: BlockId,
    pub predecessors: Vec<BlockId>,
    pub assignments: Vec<EggAssign>,
}

impl EggBlock {
    pub fn from_sexp(expr: &Sexp) -> EggBlock {
        match expr {
            Sexp::List(contents) => match &contents[..] {
                [Sexp::String(block_string), Sexp::String(id), Sexp::List(predecessors), Sexp::List(assignments)] =>
                {
                    if block_string != "block" {
                        panic!("Expected keyword block, got {}", block_string);
                    }
                    EggBlock {
                        id: id.into(),
                        predecessors: predecessors
                            .iter()
                            .map(|parent| {
                                if let Sexp::String(pred) = parent {
                                    pred.into()
                                } else {
                                    panic!("Expected string for block parent, got {}", parent)
                                }
                            })
                            .collect(),
                        assignments: assignments.iter().map(EggAssign::from_sexp).collect(),
                    }
                }
                _ => panic!("Expected a block, got: {}", expr),
            },
            _ => panic!("Expected an id and expressions for a block, got: {}", expr),
        }
    }

    // Rename all the variables to unique names to avoid clashing with other blocks
    pub fn rename_variables(
        &self,
        name_to_original: &mut NameToOriginal,
        original_to_name: &mut OriginalToName,
        original_to_names: &mut OriginalToNames,
    ) -> EggBlock {
        let mut new_assignments = Vec::new();
        for assign in self.assignments.iter() {
            new_assignments.push(assign.rename_variables(
                self.id,
                name_to_original,
                original_to_name,
                original_to_names,
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
    pub lhs: EVM,
    pub rhs: RecExpr<EVM>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct EggEquality {
    pub lhs: RecExpr<EVM>,
    pub rhs: RecExpr<EVM>,
}

impl EggEquality {
    fn to_sexp(&self) -> Sexp {
        Sexp::List(vec![
            parse_str(&self.lhs.to_string()).unwrap(),
            parse_str(&self.rhs.to_string()).unwrap(),
        ])
    }

    fn rename_recexpr(recexpr: &RecExpr<EVM>, name_to_original: &NameToOriginal) -> RecExpr<EVM> {
        let mut old_recexpr: RecExpr<EVM> = Default::default();
        for node in recexpr.as_ref() {
            if let EVM::BoolVar(_) | EVM::BitVar(_) = node {
                let old_var = &name_to_original.get(node).unwrap().0;
                old_recexpr.add(old_var.clone());
            } else {
                old_recexpr.add(node.clone());
            }
        }
        old_recexpr
    }

    pub fn rename_back(self, name_to_original: &NameToOriginal) -> EggEquality {
        EggEquality {
            lhs: EggEquality::rename_recexpr(&self.lhs, name_to_original),
            rhs: EggEquality::rename_recexpr(&self.rhs, name_to_original),
        }
    }
}

impl EggAssign {
    pub fn new(lhs: &str, rhs: &str) -> Self {
        Self {
            lhs: EVM::from_op(lhs, vec![]).unwrap(),
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

    pub fn rename_variables(
        &self,
        block: BlockId,
        name_to_original: &mut NameToOriginal,
        original_to_name: &mut OriginalToName,
        original_to_names: &mut OriginalToNames,
    ) -> EggAssign {
        let mut new_rhs: RecExpr<EVM> = Default::default();
        for node in self.rhs.as_ref() {
            if let EVM::BoolVar(_) | EVM::BitVar(_) = node {
                if let Some(existing) = original_to_name.get(&(node.clone(), block)) {
                    new_rhs.add(existing.clone());
                } else {
                    let new_var = if let EVM::BoolVar(_) = node {
                        EVM::BoolVar(BoolVar(
                            format!("bool_rust_{}", name_to_original.len()).into(),
                        ))
                    } else {
                        EVM::BitVar(BitVar(
                            format!("bv256_rust_{}", name_to_original.len()).into(),
                        ))
                    };
                    original_to_name.insert((node.clone(), block), new_var.clone());
                    name_to_original.insert(new_var.clone(), (node.clone(), block));
                    new_rhs.add(new_var.clone());

                    if original_to_names.get(node).is_none() {
                        original_to_names.insert(node.clone(), vec![]);
                    }
                    original_to_names.get_mut(node).unwrap().push(new_var);
                }
            } else {
                new_rhs.add(node.clone());
            }
        }

        let new_lhs = if let EVM::BoolVar(_) = self.lhs {
            EVM::BoolVar(BoolVar(
                format!("bool_rust_{}", name_to_original.len()).into(),
            ))
        } else {
            EVM::BitVar(BitVar(
                format!("bv256_rust_{}", name_to_original.len()).into(),
            ))
        };
        original_to_name.insert((self.lhs.clone(), block), new_lhs.clone());
        name_to_original.insert(new_lhs.clone(), (self.lhs.clone(), block));

        if original_to_names.get(&self.lhs).is_none() {
            original_to_names.insert(self.lhs.clone(), vec![]);
        }
        original_to_names
            .get_mut(&self.lhs)
            .unwrap()
            .push(new_lhs.clone());

        EggAssign {
            lhs: new_lhs,
            rhs: new_rhs,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Data {
    // A constant for this eclass and the pattern for how it was computed
    constant: Option<(Constant, PatternAst<EVM>, Subst)>,
    eclass_type: Type,
}

#[derive(Debug, Clone)]
pub struct TacAnalysis {
    pub name_to_original: NameToOriginal,
    // A set of variables that are no longer needed because they were renamed intermediates
    // We proved all the paths are the same for these variables in the DSA
    pub obsolete_variables: HashSet<EVM>,

    // A set of unions that actually did anything (unioned two eclasses)
    pub important_unions: RefCell<Vec<(Id, Id)>>,
}

impl Analysis<EVM> for TacAnalysis {
    type Data = Data;

    fn make(egraph: &egg::EGraph<EVM, TacAnalysis>, enode: &EVM) -> Self::Data {
        let mut child_const = vec![];
        enode.for_each(|child| child_const.push(egraph[child].data.constant.as_ref().map(|x| x.0)));
        let first = child_const.get(0).unwrap_or(&None);
        let second = child_const.get(1).unwrap_or(&None);
        let third = child_const.get(2).unwrap_or(&None);
        let constant_option = eval_evm(enode, *first, *second, *third);
        let constant = if let Some(c) = constant_option {
            let mut expr = PatternAst::default();
            let mut subst = Subst::default();
            let top_node = enode.clone().map_children(|child| {
                if egraph[child].data.constant.is_none() {
                    let var = format!("?{}", child).parse().unwrap();
                    subst.insert(var, child);
                    expr.add(ENodeOrVar::Var(var))
                } else {
                    expr.add(ENodeOrVar::ENode(EVM::from(
                        egraph[child].data.constant.as_ref().unwrap().0,
                    )))
                }
            });
            expr.add(ENodeOrVar::ENode(top_node));
            Some((c, expr, subst))
        } else {
            None
        };

        Data {
            constant,
            eclass_type: enode.type_of(),
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
            (Some(a), Some(b)) => assert_eq!(
                a.0, b.0,
                " got different constants with evaluations {} and {}",
                a.1, b.1
            ),
        }

        assert_eq!(to.eclass_type, from.eclass_type);

        DidMerge(merge_a, true)
    }

    // We don't modify the eclass based on variable age.
    // Just add the constants we get from constant folding.
    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some((c, lhs, subst)) = egraph[id].data.constant.clone() {
            let mut const_pattern = PatternAst::default();
            const_pattern.add(ENodeOrVar::ENode(EVM::from(c)));
            let (id, _added) =
                egraph.union_instantiations(&lhs, &const_pattern, &subst, "constant_folding");

            assert!(
                !egraph[id].nodes.is_empty(),
                "empty eclass! {:#?}",
                egraph[id]
            );
        }
    }

    fn pre_union(egraph: &EGraph, left: Id, right: Id, _reason: &Option<Justification>) {
        if egraph.find(left) != egraph.find(right) {
            egraph
                .analysis
                .important_unions
                .borrow_mut()
                .push((left, right))
        }
    }
}

struct TypeCondition {
    cond_type: Type,
}

impl Condition<EVM, TacAnalysis> for TypeCondition {
    fn check(&self, egraph: &mut EGraph, eclass: Id, _subst: &Subst) -> bool {
        egraph[eclass].data.eclass_type == self.cond_type
    }
}

pub fn rules() -> Vec<Rewrite<EVM, TacAnalysis>> {
    let str_rules = get_pregenerated_rules();
    let mut res = vec![];
    for (index, (lhs, rhs)) in str_rules.into_iter().enumerate() {
        let lparsed: Pattern<EVM> = lhs.parse().unwrap();
        let rparsed: Pattern<EVM> = rhs.parse().unwrap();

        // Check the type when the lhs is a variable
        if lparsed.ast.as_ref().len() == 1 {
            if let ENodeOrVar::Var(v) = lparsed.ast.as_ref()[0] {
                let var_type = if v.to_string().starts_with("?bv256") {
                    Type::Bit256
                } else if v.to_string().starts_with("?bool") {
                    Type::Bool
                } else {
                    panic!("Rule variables should start with bv256 or bool");
                };
                let applier = ConditionalApplier {
                    condition: TypeCondition {
                        cond_type: var_type,
                    },
                    applier: rparsed,
                };
                res.push(
                    Rewrite::<EVM, TacAnalysis>::new(index.to_string(), lparsed, applier).unwrap(),
                );
            } else {
                res.push(
                    Rewrite::<EVM, TacAnalysis>::new(index.to_string(), lparsed, rparsed).unwrap(),
                );
            }
        } else {
            res.push(
                Rewrite::<EVM, TacAnalysis>::new(index.to_string(), lparsed, rparsed).unwrap(),
            );
        }
    }

    let manual_rules = vec![
        rewrite!("distr*+"; "(* (+ ?a ?b) ?c)" => "(+ (* ?a ?c) (* ?b ?c))"),
        rewrite!("doubleneg!=="; "(! (bit== (bit== ?x ?y) 0))" => "(bit== ?x ?y)"),
    ];
    for rule in manual_rules {
        res.push(rule);
    }

    res
}

pub struct TacCost {
    obsolete_variables: HashSet<EVM>,
}

impl CostFunction<EVM> for TacCost {
    type Cost = usize;

    fn cost<C>(&mut self, enode: &EVM, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            EVM::BitVar(_) | EVM::BoolVar(_) => {
                if self.obsolete_variables.contains(enode) {
                    1000
                } else {
                    1
                }
            }
            _ => 1,
        };

        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}

pub struct TacOptimizer {}

impl TacOptimizer {
    pub fn run(self, params: OptParams, blocks: Vec<EggBlock>) -> Vec<EggEquality> {
        // Find the name of this variable with respect to the current block
        let mut original_to_name = Default::default();
        // Find the original name of a variable
        let mut name_to_original = Default::default();
        // Find all the possible names of a variable
        let mut original_to_names = Default::default();

        // Rename all the blocks so they are independent
        let renamed_blocks: Vec<EggBlock> = blocks
            .iter()
            .map(|block| {
                block.rename_variables(
                    &mut name_to_original,
                    &mut original_to_name,
                    &mut original_to_names,
                )
            })
            .collect();

        let analysis = TacAnalysis {
            name_to_original: name_to_original.clone(),
            obsolete_variables: Default::default(),
            important_unions: Default::default(),
        };
        // Set up the egraph with fresh analysis
        let mut egraph = EGraph::new(analysis).with_explanations_enabled();

        // Add all the blocks to the egraph, keeping track of the eclasses for each variable
        let mut variable_roots: HashMap<EVM, Id> = Default::default();
        let mut unbound_variables: HashSet<EVM> = Default::default();
        for block in renamed_blocks.iter() {
            for assign in block.assignments.iter() {
                let mut rhs_pattern: PatternAst<EVM> = Default::default();
                let mut subst = Subst::default();
                let mut subst_size = 0;
                for node in assign.rhs.as_ref() {
                    if let EVM::BitVar(_) | EVM::BoolVar(_) = node {
                        // add unbound variables to the egraph
                        if variable_roots.get(node).is_none() {
                            variable_roots.insert(node.clone(), egraph.add(node.clone()));
                            unbound_variables.insert(node.clone());
                        }
                        let var = ("?".to_string() + &format!("{}", subst_size))
                            .parse()
                            .unwrap();
                        subst.insert(var, *variable_roots.get(node).unwrap());
                        subst_size += 1;
                        rhs_pattern.add(ENodeOrVar::Var(var));
                    } else {
                        rhs_pattern.add(ENodeOrVar::ENode(node.clone()));
                    }
                }

                let id = egraph.add_instantiation(&rhs_pattern, &subst);
                variable_roots.insert(assign.lhs.clone(), id);
            }
        }

        log::info!("Done adding terms to the egraph.");

        // run eqsat with the domain rules
        let variable_roots_clone = variable_roots.clone();
        let unbound_clone = unbound_variables.clone();
        let mut runner: Runner<EVM, TacAnalysis> = Runner::new(egraph.analysis.clone())
            .with_egraph(egraph)
            .with_iter_limit(params.eqsat_iter_limit)
            .with_node_limit(params.eqsat_node_limit)
            .with_scheduler(egg::SimpleScheduler)
            // When we prove all instances of a variable are the same, get rid of intermediate renamings
            .with_hook(move |runner| {
                for names in original_to_names.values() {
                    let mut unbound: Vec<EVM> = vec![];
                    let mut ids: Vec<Id> = names
                        .iter()
                        .filter_map(|name| {
                            if unbound_clone.contains(name) {
                                unbound.push(name.clone());
                                None
                            } else {
                                Some(runner.egraph.find(*variable_roots_clone.get(name).unwrap()))
                            }
                        })
                        .collect();
                    ids.dedup();

                    if ids.len() == 1 {
                        for intermediate in unbound {
                            runner.egraph.union_trusted(
                                *variable_roots_clone.get(&intermediate).unwrap(),
                                ids[0],
                                "intermediateequal",
                            );
                            runner
                                .egraph
                                .analysis
                                .obsolete_variables
                                .insert(intermediate);
                        }
                    }
                }
                runner.egraph.rebuild();
                Ok(())
            });
        runner = runner.run(&rules());
        log::info!("Done running rules.");

        // Extract out interesting equalities
        let mut final_equalities: Vec<EggEquality> = vec![];

        let extractor = Extractor::new(
            &runner.egraph,
            TacCost {
                obsolete_variables: runner.egraph.analysis.obsolete_variables.clone(),
            },
        );
        for (variable, old_eclass) in &variable_roots {
            if !runner.egraph.analysis.obsolete_variables.contains(variable)
                && !unbound_variables.contains(variable)
            {
                let mut expr1 = RecExpr::default();
                expr1.add(variable.clone());
                let (cost, extracted) = extractor.find_best(*old_eclass);
                if cost >= 1000 {
                    panic!("Cost of extraction over 1000! Likely failed to find something valid.");
                }
                final_equalities.push(
                    EggEquality {
                        lhs: expr1,
                        rhs: extracted,
                    }
                    .rename_back(&name_to_original),
                )
            }
        }

        final_equalities
    }
}

fn start_blocks(blocks: Vec<EggBlock>) -> Vec<EggEquality> {
    let params: OptParams = OptParams::default();
    TacOptimizer {}.run(params, blocks)
}

// Entry point- parse Sexp and run optimization
// We expect all the blocks to be DSA
pub fn start_optimize(blocks_in: &Sexp) -> String {
    let mut blocks: Vec<EggBlock> = vec![];

    if let Sexp::List(list) = blocks_in {
        for block in list {
            blocks.push(EggBlock::from_sexp(block));
        }
    } else {
        panic!("Expected a list of blocks");
    }

    let blocks_list = start_blocks(blocks)
        .iter()
        .map(|equality| equality.to_sexp())
        .collect();

    Sexp::List(blocks_list).to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use egg::{RecExpr, Symbol};
    use primitive_types::U256;
    use rust_evm::{eval_evm, EVM};

    // TODO make check_test actually check that we proved them equal to expected
    fn check_test(input: &str, expected: &str) {
        let result = start_optimize(&parse_str(input).unwrap());
        let first_list = parse_str(expected).unwrap();
        let second_list = parse_str(&result).unwrap();
        if let (Sexp::List(first), Sexp::List(second)) = (first_list, second_list) {
            let mut vec_strings: Vec<String> = first.iter().map(Sexp::to_string).collect();
            let mut vec2_strings: Vec<String> = second.iter().map(Sexp::to_string).collect();
            vec_strings.sort();
            vec2_strings.sort();
            assert_eq!(vec_strings, vec2_strings);
        } else {
            panic!("expected lists, got {} and {}", result, expected);
        }
    }

    #[test]
    fn eval_equality() {
        let program_sexp = "((block 0_0_0_0_0_0_0 () ((boolB14 (bit== 3 4)))))";
        let expected = "((boolB14 false))";

        check_test(program_sexp, expected);
    }

    #[test]
    fn test1() {
        let program_sexp = "(
            (block block1 () (
                (bv256R194 64)
                (bv256R198 (+ 32 bv256R194))
                (bv256R202 (- bv256R198 bv256R194))
            ))
            )";
        let expected = "(
            (bv256R194 64)
            (bv256R198 96)
            (bv256R202 32)
        )";
        check_test(program_sexp, expected);
    }

    #[test]
    fn test2() {
        let program_sexp = "(
            (block block1 () (
                (bv256x1 (+ bv256x2 96))
                (bv256x3 (- bv256x1 32))
                (bv256x4 (- bv256x3 bv256x2))
            ))
        )";
        let expected = "(
            (bv256x1 (+ bv256x2 96))
            (bv256x3 (+ bv256x2 64))
            (bv256x4 64)
        )";
        check_test(program_sexp, expected);
    }

    fn test3() {
        let program_sexp = "(
            (block block1 () (
                (bv256R1 64)
                (bv256R2 (- R1 32))
            ))
        )";
        let expected = "(
            (bv256R1 64)
            (bv256R2 32)
        )";
        check_test(program_sexp, expected);
    }

    #[test]
    fn parse_test1() {
        let from_string: RecExpr<EVM> = "(+ bv256x 0)".to_string().parse().unwrap();
        let v1 = EVM::BitVar(BitVar(Symbol::from("bv256x")));
        let v2 = EVM::Constant(Constant::Num(U256::zero()));
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
        let program_sexp = "(
        (block block1 () (
            (bv256a 2)
            (bv256b bv256a)
        ))
            (block block2 () (
                (bv256b bv256a)
                (bv256c (* 2 (+ bv256b 1)))
                (bv256d (* 2 bv256c))
            ))
        )";
        let expected = "((bv256a 2)
                               (bv256b 2)
                               (bv256b 2)
                                (bv256c 6)
                                (bv256d 12))
                                ";
        check_test(program_sexp, expected);
    }

    #[test]
    fn mixed_boolean() {
        let program_sexp = "(
            (block block1 () (
                (bool1 boolunbound)
                (bv256number1 (* 3 3))
                (bool2 (< bv256unbound2 bv256number1))
                (bool3 (|| bool2 bool1))
            ))
        )";
        let expected = "(
                (bool1 boolunbound)
                (bv256number1 9)
                (bool2 (> 9 bv256unbound2))
                (bool3 (|| boolunbound (> 9 bv256unbound2)))
        )";
        check_test(program_sexp, expected);
    }

    #[test]
    fn full_program2() {
        let program_sexp = "(
            (block block1 () (
                (bv256a (+ 1 2))
            ))
            (block block2 () (
                (bv256b 10)
                (bv256a (- bv256b 7))
            ))
            (block block3 (block1 block2) (
                (bv256z (* bv256a 2))
            ))
        )";
        let expected = "(
                (bv256a 3)
                (bv256b 10)
                (bv256a 3)
                (bv256z 6)
        )";
        check_test(program_sexp, expected);
    }

    #[test]
    fn bwand() {
        let program_sexp = "((block 387_1018_0_0_0_0_0 () ((bv256R24 (& 4294967295 0)))))";
        let expected = "((bv256R24 0))";

        check_test(program_sexp, expected);
    }

    #[test]
    fn boolean_fold() {
        let program_sexp = "((block 641_1013_0_2_0_18_0 (779_1018_0_2_0_20_0) ((boolB88 (bit== (bitif (|| (> 192 18446744073709551615) (< 192 128)) 1 0) 0))
        (boolB76 (s< bv256R73 64)))
    ) )";
        let expected = "((boolB88 true) (boolB76 (s< bv256R73 64)))";
        check_test(program_sexp, expected)
    }

    #[test]
    fn subtract_fold() {
        let program_sexp = "((block 0 (0) ((bv256x (- bv256a 1)) 
        (bv256y (+ bv256a (- 0 1))))))";

        let expected = "((bv256x (- bv256a 1)) (bv256y (- bv256a 1))))";

        check_test(program_sexp, expected);
    }
}
