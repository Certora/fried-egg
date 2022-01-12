use crate::tac::TAC;
use egg::{rewrite as rw, EGraph, Rewrite, Runner};
use std::time::Duration;

pub struct LogicalEquality {}

#[rustfmt::skip]
fn rules() -> Vec<Rewrite<TAC, ()>> {
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

impl LogicalEquality {
    pub fn new() -> Self {
        Self {}
    }

    pub fn run(self, lhs: String, rhs: String) -> bool {
        let mut egraph = EGraph::<TAC, ()>::default();
        let start = egraph.add_expr(&lhs.parse().unwrap());
        let end = egraph.add_expr(&rhs.parse().unwrap());

        let mut runner: Runner<TAC, ()> = Runner::new(egraph.analysis.clone())
            .with_egraph(egraph)
            .with_node_limit(20_000)
            .with_time_limit(Duration::from_secs(60))
            .with_iter_limit(usize::MAX);
        runner = runner.run(&rules());
        if runner.egraph.find(start) == runner.egraph.find(end) {
            true
        } else {
            false
        }
    }
}
