use clap::Parser;
use egg::*;
use serde::*;
use std::io;
use std::io::prelude::*;
use std::cell::RefCell;
// use statement::Stmt;
use egg::{ENodeOrVar, Pattern, RecExpr, Justification};
use itertools::Itertools;
use num_bigint::BigUint;
use primitive_types::U256;
use rust_evm::WrappedU256;
use rust_evm::{eval_evm, EVM};
use std::iter::FromIterator;
use std::ops::BitAnd;
use std::{cmp::*, collections::HashMap, collections::HashSet};
use symbolic_expressions::parser::parse_str;
use symbolic_expressions::Sexp;
use indexmap::IndexSet;

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

    // Rename all the variables to unique names to avoid clashing with other blocks
    pub fn rename_variables(
        &self,
        name_to_original: &mut HashMap<Symbol, (BlockId, Symbol)>,
        original_to_name: &mut HashMap<(Symbol, BlockId), Symbol>,
        original_to_names: &mut HashMap<Symbol, Vec<Symbol>>,
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
    pub lhs: Symbol,
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

    fn rename_recexpr(recexpr: &RecExpr<EVM>, name_to_original: &HashMap<Symbol, (BlockId, Symbol)>) -> RecExpr<EVM>{
        let mut old_recexpr: RecExpr<EVM> = Default::default();
        for node in recexpr.as_ref() {
            if let EVM::Var(var) = node {
                let old_var = name_to_original.get(&var).unwrap().1;
                old_recexpr.add(EVM::Var(old_var.clone()));
            } else {
                old_recexpr.add(node.clone());
            }
        }
        old_recexpr
    }

    pub fn rename_back(self, name_to_original: &HashMap<Symbol, (BlockId, Symbol)>) -> EggEquality {
        EggEquality {
            lhs: EggEquality::rename_recexpr(&self.lhs, name_to_original),
            rhs: EggEquality::rename_recexpr(&self.rhs, name_to_original),
        }
    }
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
        original_to_names: &mut HashMap<Symbol, Vec<Symbol>>,
    ) -> EggAssign {
        let mut new_rhs: RecExpr<EVM> = Default::default();
        for node in self.rhs.as_ref() {
            if let EVM::Var(var) = node {
                if let Some(existing) = original_to_name.get(&(block, *var)) {
                    new_rhs.add(EVM::Var(existing.clone()));
                } else {
                    let new_var = format!("rust_{}", name_to_original.len()).into();
                    original_to_name.insert((block, *var), new_var);
                    name_to_original.insert(new_var, (block, *var));
                    new_rhs.add(EVM::Var(new_var));

                    if original_to_names.get(&var).is_none() {
                        original_to_names.insert(*var, vec![]);
                    }
                    original_to_names.get_mut(&var).unwrap().push(new_var);
                }
            } else {
                new_rhs.add(node.clone());
            }
        }

        let new_lhs = format!("rust_{}", name_to_original.len()).into();
        original_to_name.insert((block, self.lhs), new_lhs);
        name_to_original.insert(new_lhs, (block, self.lhs));
        
        if original_to_names.get(&self.lhs).is_none() {
            original_to_names.insert(self.lhs, vec![]);
        }
        original_to_names.get_mut(&self.lhs).unwrap().push(new_lhs);

        EggAssign {
            lhs: new_lhs,
            rhs: new_rhs,
        }
    }
}

#[derive(Default, Debug, Clone)]
pub struct Data {
    // A constant for this eclass and the pattern for how it was computed
    constant: Option<(U256, PatternAst<EVM>, Subst)>,
    // The best enodes per type for linear expressions
    type_to_best_linear: BestForType,
    // The best enode per type with a general cost function
    type_to_best_general: BestForType,
}

// A map from type to a tuple (enode, cost, type of children)
// The type of the children is used to extract back out the best program
type BestForType = HashMap<Symbol, (EVM, BigUint, Symbol)>;

#[derive(Debug, Clone)]
pub struct LinearAnalysis {
}

#[derive(Debug, Clone)]
pub struct GeneralAnalysis {
}

#[derive(Debug, Clone)]
pub struct TacAnalysis {
    pub linear_analysis: LinearAnalysis,
    pub general_analysis: GeneralAnalysis,
    pub typemap: HashMap<Symbol, Symbol>,
    pub name_to_original: HashMap<Symbol, (BlockId, Symbol)>,
    // A set of variables that are no longer needed because they were renamed intermediates
    // We proved all the paths are the same for these variables in the DSA
    pub obsolete_variables: HashSet<Symbol>,

    // A set of unions that actually did anything (unioned two eclasses)
    pub important_unions: RefCell<Vec<(Id, Id)>>
}

impl GeneralAnalysis {
    pub fn my_build_recexpr<F>(class: Id, target_type: Symbol, mut get_node: F) -> RecExpr<EVM>
    where
        F: FnMut(Id, Symbol) -> (EVM, Symbol),
    {
        let (node, newtype) = get_node(class, target_type);
        let mut set = IndexSet::<EVM>::default();
        let mut ids = HashMap::<Id, Id>::default();
        let mut todo: Vec<(Id, Symbol)> = node.children().iter().map(|id| (*id, newtype)).collect();

        while let Some((id, this_type)) = todo.last().copied() {
            if ids.contains_key(&id) {
                todo.pop();
                continue;
            }

            let (node, child_type) = get_node(id, this_type);

            // check to see if we can do this node yet
            let mut ids_has_all_children = true;
            for child in node.children() {
                if !ids.contains_key(child) {
                    ids_has_all_children = false;
                    todo.push((*child, child_type));
                }
            }

            // all children are processed, so we can lookup this node safely
            if ids_has_all_children {
                let node = node.map_children(|id| ids[&id]);
                let new_id = set.insert_full(node).0;
                ids.insert(id, Id::from(new_id));
                todo.pop();
            }
        }

        // finally, add the root node and create the expression
        let mut nodes: Vec<EVM> = set.into_iter().collect();
        nodes.push(node.clone().map_children(|id| ids[&id]));
        RecExpr::from(nodes)
    }


    pub fn get_best_from_eclass(egraph: &egg::EGraph<EVM, TacAnalysis>, eclass: Id, target_type: Symbol) -> Option<(RecExpr<EVM>, BigUint)> {
        if !egraph[eclass].data.type_to_best_general.contains_key(&target_type) {
            return None
        }

        let get_enode = |id, this_type| (egraph[id].data.type_to_best_general[&this_type].0.clone(), egraph[id].data.type_to_best_general[&this_type].2);
        return Some((
            Self::my_build_recexpr(eclass, target_type, get_enode),
            egraph[eclass].data.type_to_best_general[&target_type].1.clone()
        ));
    }

    pub fn make(&self, egraph: &egg::EGraph<EVM, TacAnalysis>, enode: &EVM, typemap: &HashMap<Symbol, Symbol>, name_to_original: &HashMap<Symbol, (BlockId, Symbol)>, obsolete_variables: &HashSet<Symbol>) -> BestForType {
        let mut best: BestForType = HashMap::new();

        let cost_sum = |child_type: Symbol| -> Option<BigUint> {
            let mut sum = "0".parse().unwrap();
            let mut success = true;
            enode.for_each(|child| {
                if let Some((_, cost, _)) = egraph[child].data.type_to_best_general.get(&child_type) {
                    sum += cost.clone();
                } else {
                    success = false;
                }
            });
            if success {
                Some(sum)
            } else {
                None
            }
        };

        let good_cost: BigUint = "5".parse().unwrap();
        let bad_cost: BigUint = "10".parse().unwrap();
        let very_bad_cost: BigUint = "50".parse().unwrap();
        let var_value = "5".parse().unwrap();
        let num_value = "2".parse().unwrap();
        let bvtype = "bv256".into();
        let booltype = "bool".into();

        let mut type_to_type = |childtype, outputtype, cost| {
            if let Some(child_val) = cost_sum(childtype) {
                let new_cost = child_val + cost;
                if let Some((_, existing, _)) = best.get(&outputtype) {
                    if existing < &new_cost {
                        return;
                    }
                }
                best.insert(outputtype, (enode.clone(), new_cost, childtype));
            }
        };


        match enode {
            EVM::Num(n) => {
                let cost: BigUint = if n.value < "1000".parse().unwrap() {
                    "1".parse().unwrap()
                } else {
                    num_value
                };
                // when there are no children, the type part doesn't matter
                best.insert("bv256".into(), (enode.clone(), cost.clone(), "nochildren".into()));
                if n.value <= "1".parse().unwrap() {
                    best.insert("bool".into(), (enode.clone(), cost, "nochildren".into()));
                }
            }

            EVM::Var(v) => {
                if let Some(var_type) = typemap.get(&name_to_original.get(&v).unwrap().1) {
                    let cost = if obsolete_variables.contains(v) {
                        very_bad_cost
                    } else {
                        var_value
                    };
                    best.insert(*var_type, (enode.clone(), cost, "nochildren".into()));
                } else {
                    panic!("Variable {} has no type in typemap", &name_to_original.get(&v).unwrap().1);
                }
            }

            EVM::Mul(_) => type_to_type(bvtype, bvtype, bad_cost),
            EVM::Add(_) => type_to_type(bvtype, bvtype, good_cost),
            EVM::Sub(_) => type_to_type(bvtype, bvtype, good_cost),
            EVM::Div(_) => type_to_type(bvtype, bvtype, very_bad_cost),
            EVM::BWAnd(_) => type_to_type(bvtype, bvtype, bad_cost),
            EVM::BWOr(_) => type_to_type(bvtype, bvtype, bad_cost),
            EVM::ShiftLeft(_) => type_to_type(bvtype, bvtype, bad_cost),
            EVM::ShiftRight(_) => type_to_type(bvtype, bvtype, bad_cost),
            EVM::LOr(_) => type_to_type(booltype, booltype, good_cost),
            EVM::LAnd(_) => type_to_type(booltype, booltype, good_cost),

            EVM::Gt(_) => type_to_type(bvtype, booltype, good_cost),
            EVM::Ge(_) => type_to_type(bvtype, booltype, good_cost),
            EVM::Lt(_) => type_to_type(bvtype, booltype, good_cost),
            EVM::Le(_) => type_to_type(bvtype, booltype, good_cost),
            EVM::Eq(_) => {
                type_to_type(bvtype, booltype, good_cost.clone());
                type_to_type(booltype, booltype, good_cost);
            }
            EVM::Slt(_) => type_to_type(bvtype, booltype, good_cost),
            EVM::Sle(_) => type_to_type(bvtype, booltype, good_cost),
            EVM::Sgt(_) => type_to_type(bvtype, booltype, good_cost),
            EVM::Sge(_) => type_to_type(bvtype, booltype, good_cost),

            EVM::LNot(_) => type_to_type(booltype, booltype, good_cost),
            EVM::BWNot(_) => type_to_type(bvtype, bvtype, bad_cost),

            EVM::Exp(_) => type_to_type(bvtype, bvtype, very_bad_cost),

            EVM::Apply(_) => ()
        }

        best
    }
}

impl LinearAnalysis {
    pub fn get_best_from_eclass(egraph: &egg::EGraph<EVM, TacAnalysis>, eclass: Id, target_type: Symbol) -> Option<(RecExpr<EVM>, BigUint)> {
        if !egraph[eclass].data.type_to_best_linear.contains_key(&target_type) {
            return None
        }

        let get_enode = |id, this_type| (egraph[id].data.type_to_best_linear[&this_type].0.clone(), egraph[id].data.type_to_best_linear[&this_type].2);
        return Some((
            GeneralAnalysis::my_build_recexpr(eclass, target_type, get_enode),
            egraph[eclass].data.type_to_best_linear[&target_type].1.clone()
        ));
    }


    pub fn make(&self, egraph: &egg::EGraph<EVM, TacAnalysis>, enode: &EVM, typemap: &HashMap<Symbol, Symbol>, name_to_original: &HashMap<Symbol, (BlockId, Symbol)>) -> BestForType {
        let mut best: BestForType = HashMap::new();
        let add_value: BigUint = "40".parse().unwrap();
        let mul_value: BigUint = "20".parse().unwrap();
        let var_value = "5".parse().unwrap();
        let num_value = "2".parse().unwrap();

        let cost_sum = |child_type: Symbol| -> Option<BigUint> {
            let mut sum = "0".parse().unwrap();
            let mut success = true;
            enode.for_each(|child| {
                if let Some((_, cost, _)) = egraph[child].data.type_to_best_linear.get(&child_type) {
                    sum += cost.clone();
                } else {
                    success = false;
                }
            });
            if success {
                Some(sum)
            } else {
                None
            }
        };


        match enode {
            EVM::Num(n) => {
                let cost = if n.value < "1000".parse().unwrap() {
                    "1".parse().unwrap()
                } else {
                    num_value
                };
                best.insert("bv256".into(), (enode.clone(), cost, "nochildren".into()));
            }

            EVM::Var(v) => {
                if let Some(var_type) = typemap.get(&name_to_original.get(&v).unwrap().1) {
                    best.insert(*var_type, (enode.clone(), var_value, "nochildren".into()));
                } else {
                    panic!("Variable {} has no type in typemap", &name_to_original.get(&v).unwrap().1);
                }
            }

            // Only multiplications of a constant and variable are accepted
            EVM::Mul([child1, child2]) => {
                if let (Some((_, costafound, _)), Some((_, costbfound, _))) = (
                    egraph[*child1].data.type_to_best_linear.get(&"bv256".into()),
                    egraph[*child2].data.type_to_best_linear.get(&"bv256".into())) {
                    let mut costa = costafound.clone();
                    let mut costb = costbfound.clone();
                    if costb < costa {
                        std::mem::swap(&mut costa, &mut costb);
                    }
                    if costa < num_value && costb < var_value {
                        best.insert("bv256".into(), (enode.clone(), costa + costb + mul_value, "bv256".into()));
                    }
                }
            }

            EVM::Add(_) => {
                if let Some(child_val) = cost_sum("bv256".into()) {
                    best.insert("bv256".into(), (enode.clone(), add_value + child_val, "bv256".into()));
                }
            }
            EVM::Sub(_) => {
                if let Some(child_val) = cost_sum("bv256".into()) {
                    best.insert("bv256".into(), (enode.clone(), add_value + child_val, "bv256".into()));
                }
            }
            _ => {}
        }

        best
    }
}

impl TacAnalysis {
    pub fn merge_best_for_type(to: &mut BestForType, from: &BestForType) -> bool {
        let mut merge_a = false;
        for (key, (enode, cost, child_type)) in from {
            if let Some((enode2, cost2, child_type2)) = to.get_mut(key) {
                if cost < cost2 {
                    *enode2 = enode.clone();
                    *cost2 = cost.clone();
                    *child_type2 = child_type.clone();
                    merge_a = true;
                }
            } else {
                to.insert(key.clone(), (enode.clone(), cost.clone(), child_type.clone()));
                merge_a = true;
            }
        }

        merge_a
    }
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

        Data {
            constant,
            type_to_best_linear: egraph.analysis.linear_analysis.make(egraph, enode, &egraph.analysis.typemap, &egraph.analysis.name_to_original),
            type_to_best_general: egraph.analysis.general_analysis.make(egraph, enode, &egraph.analysis.typemap, &egraph.analysis.name_to_original, &egraph.analysis.obsolete_variables),
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

        merge_a |= TacAnalysis::merge_best_for_type(&mut to.type_to_best_linear, &from.type_to_best_linear);
        merge_a |= TacAnalysis::merge_best_for_type(&mut to.type_to_best_general, &from.type_to_best_general);


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

    fn pre_union(egraph: &EGraph, left: Id, right: Id, _reason: &Option<Justification>) {
        if (egraph.find(left) != egraph.find(right)) {
            egraph.analysis.important_unions.borrow_mut().push((left, right))
        }
    }
}

pub struct TacOptimizer {}

impl TacOptimizer {
    pub fn run(self, params: OptParams, blocks: Vec<EggBlock>, typemap: HashMap<Symbol, Symbol>) -> Vec<EggEquality> {
        // Find the name of this variable with respect to the current block
        let mut original_to_name = Default::default();
        // Find the original name of a variable
        let mut name_to_original = Default::default();
        // Find all the possible names of a variable
        let mut original_to_names = Default::default();

        // Rename all the blocks so they are independent
        let renamed_blocks: Vec<EggBlock> = blocks
            .iter()
            .map(|block| block.rename_variables(&mut name_to_original, &mut original_to_name, &mut original_to_names))
            .collect();

        let analysis = TacAnalysis {
            linear_analysis: LinearAnalysis {},
            general_analysis: GeneralAnalysis {},
            typemap,
            name_to_original: name_to_original.clone(),
            obsolete_variables: Default::default(),
            important_unions: Default::default(),
        };
        // Set up the egraph with fresh analysis
        let mut egraph = EGraph::new(analysis).with_explanations_enabled();
        

        // Add all the blocks to the egraph, keeping track of the eclasses for each variable
        let mut variable_roots: HashMap<Symbol, Id> = Default::default();
        let mut unbound_variables: HashSet<Symbol> = Default::default();
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
                            unbound_variables.insert(*name);
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
        let variable_roots_clone = variable_roots.clone();
        let mut runner: Runner<EVM, TacAnalysis> = Runner::new(egraph.analysis.clone())
            .with_egraph(egraph)
            .with_iter_limit(params.eqsat_iter_limit)
            .with_node_limit(params.eqsat_node_limit)
            .with_scheduler(egg::SimpleScheduler)
            // When we prove all instances of a variable are the same, get rid of intermediate renamings
            .with_hook(move |runner| {
                for (_original, names) in &original_to_names {
                    let mut unbound: Vec<Symbol> = vec![];
                    let mut ids: Vec<Id> = names.iter().filter_map(|name|
                        if unbound_variables.contains(name) {
                            unbound.push(*name);
                            None
                        } else {
                            Some(runner.egraph.find(*variable_roots_clone.get(name).unwrap()))
                        }
                    )
                        .collect();
                    ids.dedup();

                    if ids.len() == 1 {
                        for intermediate in unbound {
                            runner.egraph.union_trusted(*variable_roots_clone.get(&intermediate).unwrap(), ids[0], "intermediateequal");
                            runner.egraph.analysis.obsolete_variables.insert(intermediate);
                        }
                    }
                }
                runner.egraph.rebuild();
                Ok(())
            });
        runner = runner.run(&logical_rules());
        log::info!("Done running rules.");

        // Find out which variables are equal to each other
        let mut final_equalities: Vec<EggEquality> = vec![];
        let mut equal_vars: HashMap<Id, HashSet<Symbol>> = Default::default();
        for (variable, old_eclass) in variable_roots {
            let eclass = runner.egraph.find(old_eclass);
            if runner.egraph.analysis.obsolete_variables.contains(&variable) {
                let old_var = name_to_original.get(&variable).unwrap().1;
                if let Some(existing) = equal_vars.get_mut(&eclass) {
                    existing.insert(old_var);
                } else {
                    let mut new_set: HashSet<Symbol> = Default::default();
                    new_set.insert(old_var);
                    equal_vars.insert(eclass, new_set);
                }
            }
        }

        for (_class, vars) in equal_vars {
            let mut expr1 = RecExpr::default();
            let mut iter = vars.iter();
            expr1.add(EVM::Var(*iter.next().unwrap()));
            for var in iter {
                let mut expr2 = RecExpr::default();
                expr2.add(EVM::Var(*var));
                final_equalities.push(EggEquality { lhs: expr1.clone(), rhs: expr2 });
            }
        }


        final_equalities
    }
}

fn start_blocks(blocks: Vec<EggBlock>, typemap: HashMap<Symbol, Symbol>) -> Vec<EggEquality> {
    let params: OptParams = OptParams::default();
    TacOptimizer {}.run(params, blocks, typemap)
}

fn parse_type_map(sexp: &Sexp) -> HashMap<Symbol, Symbol> {
    let mut typemap: HashMap<Symbol, Symbol> = Default::default();
    if let Sexp::List(list) = sexp {
        for entry in list {
            if let Sexp::List(pair) = entry {
                if let [Sexp::String(name), Sexp::String(type_name)] = &pair[..] {
                    typemap.insert(name.into(), type_name.into());
                } else {
                    panic!("Invalid type map entry: {:?}", pair);
                }
            } else {
                panic!("Expected list of pairs in type map.");
            }
        }
    } else {
        panic!("Expected a list of type mappings.");
    }
    typemap
}

// Entry point- parse Sexp and run optimization
// We expect all the blocks to be DSA
pub fn start_optimize(blocks_in: &Sexp, typemap_in: &Sexp) -> String {
    let mut blocks: Vec<EggBlock> = vec![];

    if let Sexp::List(list) = blocks_in {
        for block in list.into_iter() {
            blocks.push(EggBlock::from_sexp(&block));
        }
    } else {
        panic!("Expected a list of blocks");
    }

    let blocks_list = start_blocks(blocks, parse_type_map(typemap_in))
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
    use rust_evm::{eval_evm, WrappedU256, EVM};

    fn check_test(input: &str, expected: &str, types: &str) {
        let result = start_optimize(&parse_str(input).unwrap(), &parse_str(types).unwrap());
        assert_eq!(parse_str(expected).unwrap().to_string(), parse_str(&result).unwrap().to_string());
    }

    #[test]
    fn test1() {
        let program_sexp = "(
            (block block1 () (
                (R194 64)
                (R198 (+ 32 R194))
                (R202 (- R198 R194))
            ))
            )";
        let expected = "(
            (block block1 () (
                (R194 64)
                (R198 96)
                (R202 32)
            ))
        )";
        let types = "((R194 bv256) (R198 bv256) (R202 bv256))";
        check_test(program_sexp, expected, types);
    }

    #[test]
    fn test2() {
        let program_sexp = "(
            (block block1 () (
                (x1 (+ x2 96))
                (x3 (- x1 32))
                (x4 (- x3 x2))
            ))
        )";
        let expected = "(
            (block block1 () (
                (x1 (+ x2 96))
                (x3 (+ x2 64))
                (x4 64)
            ))
        )";
        let types = "((x1 bv256) (x2 bv256) (x3 bv256) (x4 bv256))";
        check_test(program_sexp, expected, types);
    }

    fn test3() {
        let program_sexp = "(
            (block block1 () (
                (R1 64)
                (R2 (- R1 32))
            ))
        )";
        let expected = "(
            (block block1 () (
                (R1 64)
                (R2 32)
            ))
        )";
        let types = "((R1 bv256) (R2 bv256))";
        check_test(program_sexp, expected, types);
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
        let program_sexp = "(
        (block block1 () (
            (a 2)
            (b a)
            (a (+ a 4))
            (a (* a 3))
        ))
            (block block2 () (
                (b a)
                (b (* 2 (+ b 1)))
                (b (* 2 b))
            ))
        )";
        let expected = "((block block1 () ((a 2) (b 2) (a 6) (a 18))) (block block2 () ((b a) (b (+ 2 (+ a a))) (b (* 4 (+ a 1))))))";
        let types = "((a bv256) (b bv256))";
        check_test(program_sexp, expected, types);
    }

    #[test]
    fn mixed_boolean() {
        let program_sexp = "(
            (block block1 () (
                (bool1 unbound)
                (number1 (* 3 3))
                (bool2 (< unbound2 number1))
                (bool3 (|| bool2 bool1))
            ))
        )";
        let expected = "(
            (block block1 () (
                (bool1 unbound)
                (number1 9)
                (bool2 (< unbound2 9))
                (bool3 (|| (< unbound2 9) unbound))
            ))
        )";
        let types = "((unbound bool) (unbound2 bv256) (number1 bv256) (bool1 bool) (bool2 bool) (bool3 bool))";
        check_test(program_sexp, expected, types);
    }

    #[test]
    fn full_program2() {
        let program_sexp = "(
            (block block1 () (
                (a (+ 1 2))
            ))
            (block block2 () (
                (b 10)
                (a (- b 7))
            ))
            (block block3 (block1 block2) (
                (z (* a 2))
            ))
        )";
        let expected = "(
            (block block1 () (
                (a 3)
            ))
            (block block2 () (
                (b 10)
                (a 3)
            ))
            (block block3 (block1 block2) (
                (z 6)
            ))
        )";
        let types = "((a bv256) (b bv256) (z bv256))";
        check_test(program_sexp, expected, types);
    }

    #[test]
    fn bwand() {
        let program_sexp = "((block 387_1018_0_0_0_0_0 () ((R24 (& 4294967295 0)))))";
        let expected = "((block 387_1018_0_0_0_0_0 () ((R24 0))))";


        let types = "((R24 bv256))";

        check_test(program_sexp, expected, types);
    }
}
