
use egg::{Rewrite, Runner, Analysis, Id, Language, DidMerge, Pattern};
use ruler::{self, EVM, eval_evm, get_pregenerated_rules};
use std::time::Duration;
use primitive_types::U256;
use rand::Rng;

pub struct LogicalEquality {}

pub fn logical_rules() -> Vec<Rewrite<EVM, LogicalAnalysis>> {
    let str_rules = get_pregenerated_rules();
    let mut res = vec![];
    for (index, (lhs, rhs)) in str_rules.into_iter().enumerate() {
        let lparsed: Pattern<EVM> = lhs.parse().unwrap();
        let rparsed: Pattern<EVM> = rhs.parse().unwrap();
        res.push(Rewrite::<EVM, LogicalAnalysis>::new(index.to_string(), lparsed, rparsed).unwrap());
    }
    res
}

type EGraph = egg::EGraph<EVM, LogicalAnalysis>;

#[derive(Default, Debug, Clone)]
pub struct Data {
    cvec: Option<Vec<U256>>,
    constant: Option<U256>,
}

const CVEC_LEN: usize = 20;

#[derive(Default, Debug, Clone)]
pub struct LogicalAnalysis;
impl Analysis<EVM> for LogicalAnalysis {
    type Data = Data;

    fn make(egraph: &EGraph, enode: &EVM) -> Self::Data {
        let cvec = match enode {
            EVM::Var(_) => {
                let mut cvec = vec![];
                cvec.push(U256::zero());
                cvec.push(U256::one());
                cvec.push(U256::zero().overflowing_sub(U256::one()).0);
                let mut rng = rand::thread_rng();
                for i in 0..CVEC_LEN {
                    cvec.push(rng.gen::<u32>().into());
                }
                Some(cvec)
            }
            _ => {
                let mut cvec = vec![];
                let mut child_const = vec![];
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
        };

        let mut child_const = vec![];
        enode.for_each(|child| child_const.push(egraph[child].data.constant));
        let first = child_const.get(0).unwrap_or(&None);
        let second = child_const.get(1).unwrap_or(&None);
        let constant = eval_evm(enode, *first, *second);

        Data { cvec, constant }
    }


    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        match (to.cvec.as_ref(), from.cvec) {
            (None, Some(b)) => to.cvec = Some(b.clone()),
            (None, None) => (),
            (Some(_), None) => (),
            (Some(_), Some(_)) => (),
        }

        match (to.constant, from.constant) {
            (None, Some(b)) => to.constant = Some(b.clone()),
            (None, None) => (),
            (Some(_), None) => (),
            (Some(a), Some(b)) => assert_eq!(a, b),
        }

        DidMerge(false, false)
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        let class = &mut egraph[id];
        if let Some(c) = class.data.constant {
            let added = egraph.add(EVM::Num(c));
            egraph.union(id, added);
            assert!(
                !egraph[id].nodes.is_empty(),
                "empty eclass! {:#?}",
                egraph[id]
            );
        }
    }
}

fn cvec_to_string(cvec: Option<&Vec<U256>>) -> String {
    match cvec {
        Some(cvec) => {
            let mut s = String::new();
            s.push_str("(");
            for val in cvec {
                s.push_str(&format!("{} ", val));
            }
            s
        }
        None => "()".to_string()
    }
}

impl LogicalEquality {
    pub fn new() -> Self {
        Self {}
    }

    pub fn make_runner(lhs: &String, rhs: &String) -> Runner<EVM, LogicalAnalysis> {
        let mut egraph = EGraph::new(LogicalAnalysis);
        let start = egraph.add_expr(&lhs.parse().unwrap());
        let end = egraph.add_expr(&rhs.parse().unwrap());

        Runner::new(egraph.analysis.clone())
            .with_egraph(egraph)
            .with_node_limit(1_000_000)
            .with_time_limit(Duration::from_secs(2))
            .with_iter_limit(usize::MAX)
            .with_hook(move |runner| {
                let svec = runner.egraph[start].data.cvec.as_ref();
                let evec = runner.egraph[end].data.cvec.as_ref();
                if runner.egraph.find(start) == runner.egraph.find(end) {
                    Err("equal".to_string())
                } else if svec.is_some() && evec.is_some() && svec != evec {
                    Err("not equal".to_string())
                } else {
                    Ok(())
                }
            })
    }

    pub fn run(self, lhs: String, rhs: String) -> crate::EqualityResult {
        let mut runner: Runner<EVM, LogicalAnalysis> = LogicalEquality::make_runner(&lhs, &rhs);

        runner = runner.run(&logical_rules());
        let start = runner.egraph.add_expr(&lhs.parse().unwrap());
        let end = runner.egraph.add_expr(&rhs.parse().unwrap());
        let result = if start == end {
            true 
        } else {
            false
        };

        println!("Results: {} {} {}", lhs, rhs, result);
        let cvec_left_string = cvec_to_string(runner.egraph[start].data.cvec.as_ref());
        let cvec_right_string = cvec_to_string(runner.egraph[end].data.cvec.as_ref());
        return crate::EqualityResult {
            result,
            leftv: cvec_left_string,
            rightv: cvec_right_string,
        }
    }
}


#[cfg(test)]
mod tests {
    use crate::*;
    use crate::logical_equality::logical_rules;
    use egg::Runner;

    #[test]
    fn logical_simple() {
        let queries = vec![("(+ 1 1)", "2"),
                           ("(- a 1)", "(+ a (- 0 1))"),
                           ("(* (- c 1) 32)", "(- (* c 32) 32)"),
                           ("(- (+ a (+ b (* c 32))) (+ a (+ b (* (- c 1) 32))))", "32")];
        for (lhs, rhs) in queries {
            let mut runner: Runner<EVM, LogicalAnalysis> = LogicalEquality::make_runner(&lhs.to_string(), &rhs.to_string());

            runner = runner.run(&logical_rules());

            if runner.egraph.add_expr(&lhs.parse().unwrap()) != runner.egraph.add_expr(&rhs.parse().unwrap()) {
                panic!("could not prove equal {},   {}", lhs, rhs);
            }
        }
    }
}