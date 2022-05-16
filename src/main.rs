use std::io::{self, BufRead, Write};
use symbolic_expressions::parser::parse_str;
use symbolic_expressions::Sexp;

pub(crate) mod lin_inv;
pub(crate) mod logical_equality;

use lin_inv::start_optimize;
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
                                list[1].to_string(),
                                list[2].to_string(),
                                list[3].to_string().parse().unwrap()
                            )
                        );
                    }
                    "optimize" => {
                        println!("{}", start_optimize(list[1]));
                    }
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
