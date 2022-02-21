use std::io::{self, BufRead, Write};
use symbolic_expressions::parser::parse_str;
use symbolic_expressions::Sexp;

pub(crate) mod logical_equality;
pub(crate) mod optimize;

use logical_equality::start_logical;
use optimize::start_optimize;

fn main() {
    let stdin = io::stdin();
    'outer: for line in stdin.lock().lines() {
        let expr = parse_str(&line.unwrap()).unwrap();
        if let Sexp::List(ref list) = expr {
            if let Sexp::String(ref atom) = list[0] {
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
                        println!("{}", start_optimize("".to_string()));
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
