use egg::{EGraph, Runner, rewrite as rw, Rewrite};
use crate::tac::{TAC};

pub struct LogicalEquality {}

fn rules() -> Vec<Rewrite<TAC, ()>> { vec![
  rw!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
  rw!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),
  rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
  rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),

  rw!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),

  rw!("zero-add"; "(+ ?a 0)" => "?a"),
  rw!("zero-mul"; "(* ?a 0)" => "0"),
  rw!("one-mul";  "(* ?a 1)" => "?a"),

  rw!("add-zero"; "?a" => "(+ ?a 0)"),
  rw!("mul-one";  "?a" => "(* ?a 1)"),

  rw!("cancel-sub"; "(- ?a ?a)" => "0"),

  rw!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
  rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
]}

impl LogicalEquality {
    pub fn new() -> Self {
        Self {}
    }

    pub fn run(self, lhs: String, rhs: String) -> bool {
      println!("{} {}", lhs, rhs);
        let mut egraph = EGraph::<TAC, ()>::default();
        let start = egraph.add_expr(&lhs.parse().unwrap());
        let end = egraph.add_expr(&rhs.parse().unwrap());

        let mut runner: Runner<TAC, ()> = Runner::new(egraph.analysis.clone()).with_egraph(egraph);
        runner = runner.run(&rules());
        if runner.egraph.find(start) == runner.egraph.find(end) {
          true
        } else {
          false
        }
    }
}