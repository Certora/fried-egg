use clap::Parser;
use egg::*;
use serde::*;
use std::cell::RefCell;
// use statement::Stmt;
use egg::{ENodeOrVar, Justification, Pattern, RecExpr};
use rust_evm::{eval_evm, BitVar, BoolVar, Constant, Type, EVM};
use std::{cmp::*, collections::HashMap, collections::HashSet, time::Duration};
use symbolic_expressions::parser::parse_str;
use symbolic_expressions::Sexp;

use crate::logical_equality::get_pregenerated_rules;

pub type EGraph = egg::EGraph<EVM, TacAnalysis>;
type NameToOriginal = HashMap<EVM, (EVM, BlockId)>;
type OriginalToName = HashMap<(EVM, BlockId), EVM>;
type OriginalToNames = HashMap<EVM, Vec<EVM>>;

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
            eqsat_node_limit: 100_000,
        }
    }
}

impl OptParams {
    fn from_sexp(sexp: &Sexp) -> OptParams {
        if let Sexp::List(args) = sexp {
            assert!(args.len() == 2);
            OptParams {
                eqsat_iter_limit: args[0].to_string().parse().unwrap(),
                eqsat_node_limit: args[1].to_string().parse().unwrap(),
            }
        } else {
            panic!("Expected list of args for optparams. Got: {}", sexp);
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

pub trait TypeData {
    fn get_type(&self) -> Type;
}

#[derive(Debug, Clone)]
pub struct Data {
    // A constant for this eclass and the pattern for how it was computed
    constant: Option<(Constant, PatternAst<EVM>, Subst)>,
    eclass_type: Type,
}

impl TypeData for Data {
    fn get_type(&self) -> Type {
        self.eclass_type.clone()
    }
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

pub fn rules<D: TypeData, A: Analysis<EVM, Data = D>>() -> Vec<Rewrite<EVM, A>> {
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
                let condition = move |egraph: &mut egg::EGraph<EVM, A>, id: Id, _subst: &Subst| {
                    egraph[id].data.get_type() == var_type
                };
                let applier = ConditionalApplier {
                    condition,
                    applier: rparsed,
                };
                res.push(Rewrite::<EVM, A>::new(index.to_string(), lparsed, applier).unwrap());
            } else {
                res.push(Rewrite::<EVM, A>::new(index.to_string(), lparsed, rparsed).unwrap());
            }
        } else {
            res.push(Rewrite::<EVM, A>::new(index.to_string(), lparsed, rparsed).unwrap());
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
            .with_time_limit(Duration::from_secs(u64::MAX))
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
        //eprintln!("STOP REASON {:?}", runner.stop_reason);

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

fn start_blocks(blocks: Vec<EggBlock>, config: OptParams) -> Vec<EggEquality> {
    TacOptimizer {}.run(config, blocks)
}

// Entry point- parse Sexp and run optimization
// We expect all the blocks to be DSA
pub fn start_optimize(config: &Sexp, blocks_in: &Sexp) -> String {
    let config = OptParams::from_sexp(config);
    let mut blocks: Vec<EggBlock> = vec![];

    if let Sexp::List(list) = blocks_in {
        for block in list {
            blocks.push(EggBlock::from_sexp(block));
        }
    } else {
        panic!("Expected a list of blocks");
    }

    let blocks_list = start_blocks(blocks, config)
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
        let result = start_optimize(
            &parse_str("(3 10000000)").unwrap(),
            &parse_str(input).unwrap(),
        );
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

    fn complicated_stuff() {
        let program_sexp = "(3 1000000000) ((block 0_0_0_0_0_0_0 () ((bv256R0 bv256egg_var_0) (bv256R1 bv256egg_var_1) (bv256e343.msg.sender bv256egg_var_2)\
        (bv256e343.block.coinbase bv256egg_var_3) (bv256e343.msg.value bv256egg_var_4) (bv256e343.msg.address bv256egg_var_5)\
        (bv256R4 bv256egg_var_6) (bv256R5 bv256egg_var_7) (bv256R6 bv256egg_var_8) (bv256R8 bv256egg_var_9) (bv256tacCalldatabuf!0@6 bv256egg_var_10)\
        (bv256R9 bv256egg_var_11) (bv256R10 bv256egg_var_12) (bv256tacCalldatabuf!0@7 bv256egg_var_13) (bv256R11 bv256egg_var_14) (bv256R12 bv256egg_var_15)\
        (bv256R13 bv256egg_var_16) (bv256R14 bv256egg_var_17) (bv256R15 bv256egg_var_18) (bv256R17 bv256egg_var_19) (bv256tacCalldatabuf!0@9 bv256egg_var_20)\
        (bv256R18 bv256egg_var_21) (bv256R19 bv256egg_var_22) (bv256tacCalldatabuf!0@10 bv256egg_var_23) (bv256R20 bv256egg_var_24) (bv256R21 bv256egg_var_25)\
        (bv256R22 bv256egg_var_26) (bv256R23 bv256egg_var_27) (bv256R25 bv256egg_var_28) (bv256tacCalldatabuf!0@12 bv256egg_var_29) (bv256R26 bv256egg_var_30)\
        (bv256R27 bv256egg_var_31) (bv256tacCalldatabuf!0@13 bv256egg_var_32) (bv256R28 bv256egg_var_33) (boolB33 boolegg_var_34) (boolB34 boolegg_var_35) (boolB35 boolegg_var_36)\
        (bv256R36 bv256egg_var_37) (bv256R38 bv256egg_var_38) (bv256R40 bv256egg_var_39) (bv256R42 bv256egg_var_40) (bv256R44 bv256egg_var_41) (bv256R46 bv256egg_var_42)\
        (bv256R48 bv256egg_var_43) (bv256R50 bv256egg_var_44) (bv256R52 bv256egg_var_45) (bv256R54 bv256egg_var_46) (bv256R56 bv256egg_var_47) (bv256R58 bv256egg_var_48)\
        (bv256R60 bv256egg_var_49) (bv256R62 bv256egg_var_50) (bv256R64 bv256egg_var_51) (bv256R66 bv256egg_var_52) (bv256R68 bv256egg_var_53) (bv256R70 bv256egg_var_54)\
        (bv256R72 bv256egg_var_55) (bv256R74 bv256egg_var_56) (bv256R76 bv256egg_var_57) (bv256R78 bv256egg_var_58))) (block 0_0_0_5_0_17_0 (0_0_0_0_0_0_0) ((bv256R95 bv256egg_var_59)\
        (bv256R107 128) (bv256R108 bv256egg_var_60) (bv256R110 bv256egg_var_61))) (block 0_0_0_6_0_25_0 (0_0_0_5_0_17_0) ((bv256R114 bv256egg_var_62)\
        (bv256R122 (& 1461501637330902918203684832716283019655932542975 bv256R0)))) (block 1_0_0_5_0_26_0 (0_0_0_6_0_25_0) ((bv256R125 bv256egg_var_63)\
        (bv256R126 (& 1461501637330902918203684832716283019655932542975 bv256R125)) (bv256R128 128) (bv256R129 bv256egg_var_64) (bv256R131 bv256egg_var_65)))\
        (block 0_0_0_7_0_27_0 (1_0_0_5_0_26_0) ((bv256R135 bv256egg_var_66))) (block 2_0_0_5_0_28_0 (0_0_0_7_0_27_0) ((bv256R145 bv256egg_var_67) (bv256tacRetval0@5 bv256R145)))\
        (block 12_0_0_0_0_0_0 (2_0_0_5_0_28_0) ((bv256val_x_orig354 bv256tacRetval0@5) (bv256tacTmp357 bv256val_x_orig354) (bv256tacTmp358 0) (boolcertoraAssume356 (bit== bv256tacTmp357 0))))\
        (block 0_0_0_8_0_29_0 (12_0_0_0_0_0_0) ((bv256R155 bv256egg_var_68) (bv256R168 128) (bv256R169 bv256egg_var_69) (bv256R171 bv256egg_var_70))) (block 0_0_0_9_0_36_0 (0_0_0_8_0_29_0)\
        ((bv256R175 bv256egg_var_71) (bv256R183 (& 1461501637330902918203684832716283019655932542975 bv256R0)))) (block 3_0_0_8_0_37_0 (0_0_0_9_0_36_0) ((bv256R185 bv256egg_var_72)\
        (bv256R186 (& 1461501637330902918203684832716283019655932542975 bv256R185)) (bv256R188 128) (bv256R189 bv256egg_var_73) (bv256R191 bv256egg_var_74)))\
        (block 0_0_0_10_0_38_0 (3_0_0_8_0_37_0) ((bv256R195 bv256egg_var_75) (bv256R204 (+ bv256R12 1)) (bv256R205 (+ bv256R12 1))))\
        (block 4_0_0_8_0_39_0 (0_0_0_10_0_38_0) ()) (block 26_0_0_0_0_0_0 (4_0_0_8_0_39_0) ())\
        (block 0_0_0_11_0_40_0 (26_0_0_0_0_0_0) ((bv256R213 bv256egg_var_76) (bv256R225 128)\
        (bv256R226 bv256egg_var_77) (bv256R228 bv256egg_var_78))) (block 0_0_0_12_0_48_0 (0_0_0_11_0_40_0)\
        ((bv256R232 bv256egg_var_79) (bv256R240 (& 1461501637330902918203684832716283019655932542975 bv256R0))))\
        (block 1_0_0_11_0_49_0 (0_0_0_12_0_48_0) ((bv256R243 bv256egg_var_80) (bv256R244 (& 1461501637330902918203684832716283019655932542975 bv256R243))\
        (bv256R246 128) (bv256R247 bv256egg_var_81) (bv256R249 bv256egg_var_82))) (block 0_0_0_13_0_50_0 (1_0_0_11_0_49_0) ((bv256R253 bv256egg_var_83)))\
        (block 2_0_0_11_0_51_0 (0_0_0_13_0_50_0) ((bv256R263 bv256egg_var_84) (bv256tacRetval0@11 bv256R263))) (block 34_0_0_0_0_0_0 (2_0_0_11_0_51_0)\
        ((bv256val_x360 bv256tacRetval0@11) (bv256tacTmp362 bv256val_x360) (bv256tacTmp363 2) (boolcertoraAssert_1 (bit== bv256tacTmp362 2))))))";
        let expected = "";
        check_test(program_sexp, expected);

    }

}
