use crate::tac::{TAC, eval_tac};
use egg::{rewrite as rw, Rewrite, Runner, Analysis, Id, Language};
use std::time::Duration;
use primitive_types::U256;
use rand::Rng;

pub struct LogicalEquality {}

#[rustfmt::skip]
fn rules() -> Vec<Rewrite<TAC, LogicalAnalysis>> {
    vec![
        rw!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rw!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),

        rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("assoc-add-rev"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rw!("assoc-mul-rev"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),

        rw!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
        rw!("dup-canon"; "(+ ?a ?a)" => "(* 2 ?a)"),

        rw!("zero-add"; "(+ ?a 0)" => "?a"),
        rw!("zero-mul"; "(* ?a 0)" => "0"),
        rw!("one-mul";  "(* ?a 1)" => "?a"),
        rw!("add-zero"; "?a" => "(+ ?a 0)"),
        rw!("mul-one";  "?a" => "(* ?a 1)"),

        rw!("cancel-sub"; "(- ?a ?a)" => "0"),
        rw!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
        rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),

        // comparisons
        rw!("lt-same"; "(< ?a ?a)" => "false"),
        rw!("gt-same"; "(> ?a ?a)" => "false"),
        rw!("lte-same"; "(<= ?a ?a)" => "true"),
        rw!("gte-same"; "(>= ?a ?a)" => "true"),
    ]
}

type EGraph = egg::EGraph<TAC, LogicalAnalysis>;

#[derive(Default, Debug, Clone)]
struct Data {
    cvec: Option<Vec<U256>>,
    constant: Option<U256>,
}

const CVEC_LEN: usize = 20;

#[derive(Default, Debug, Clone)]
struct LogicalAnalysis;
impl Analysis<TAC> for LogicalAnalysis {
    type Data = Data;

    fn make(egraph: &EGraph, enode: &TAC) -> Self::Data {
        let cvec = match enode {
            TAC::Var(_) => {
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
                                        
                    cvec.push(eval_tac(enode, first, second))
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
        let constant = eval_tac(enode, *first, *second);

        Data { cvec, constant }
    }


    fn merge(&self, to: &mut Self::Data, from: Self::Data) -> bool {
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

        false
    }

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

    pub fn run(self, lhs: String, rhs: String) -> crate::EqualityResult {
        let mut egraph = EGraph::new(LogicalAnalysis);
        let start = egraph.add_expr(&lhs.parse().unwrap());
        let end = egraph.add_expr(&rhs.parse().unwrap());
        println!("{} {}", lhs, rhs);

        let mut runner: Runner<TAC, LogicalAnalysis> = Runner::new(egraph.analysis.clone())
            .with_egraph(egraph)
            .with_node_limit(20_000)
            .with_time_limit(Duration::from_secs(60))
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
            });
        runner = runner.run(&rules());
        let result = if runner.egraph.find(start) == runner.egraph.find(end) {
            true
        } else {
            false
        };
        let cvec_left_string = cvec_to_string(runner.egraph[start].data.cvec.as_ref());
        let cvec_right_string = cvec_to_string(runner.egraph[end].data.cvec.as_ref());
        return crate::EqualityResult {
            result,
            leftv: cvec_left_string,
            rightv: cvec_right_string,
        }
    }
}
