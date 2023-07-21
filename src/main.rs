use std::io::{self, BufRead, Write};
use symbolic_expressions::parser::parse_str;
use symbolic_expressions::Sexp;

// pub(crate) mod lin_inv;
pub(crate) mod logical_equality;

// use lin_inv::start_optimize;
use logical_equality::start_logical;

fn main() {
    let stdin = io::stdin();
    'outer: for line in stdin.lock().lines() {
        let expr = parse_str(&line.unwrap()).unwrap();
        if let Sexp::List(list) = expr {
            if let Sexp::String(atom) = &list[0] {
                match atom.as_ref() {
                    "logical_eq" => {
                        println!(
                            "{}",
                            start_logical(
                                list.clone()[1].to_string(),
                                list.clone()[2..list.clone().len() - 1].iter_mut().map(|e| e.to_string()).collect(),
                                list.clone()[list.clone().len() - 1].to_string().parse().unwrap()
                            )
                        );
                    }
                    // "optimize" => {
                    //    let mut iter = list.into_iter();
                    //    iter.next();
                    //    println!("{}", start_optimize(iter.next().unwrap()));
                    // }
                    "exit" => break 'outer,
                    _ => panic!("unknown command {}", atom),
                }
            }
            io::stdout().flush().unwrap();
        } else {
            panic!("Expected an s-expression, got: {}", expr);
        }
    }
}
