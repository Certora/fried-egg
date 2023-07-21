use std::io::{self, BufRead, Write};
use symbolic_expressions::parser::parse_str;
use symbolic_expressions::Sexp;

// pub(crate) mod lin_inv;
pub(crate) mod logical_equality;

// use lin_inv::start_optimize;
use logical_equality::start_logical;

fn main() {
    let stdin = io::stdin();
    for line in stdin.lock().lines() {
        let expr = parse_str(&line.unwrap()).unwrap();
        let list = if let Sexp::List(list) = &expr {
            list.as_slice()
        } else {
            panic!("Expected an s-expression, got: {}", expr);
        };
        let atom = if let Sexp::String(atom) = &list[0] {
            atom.as_str()
        } else {
            continue;
        };
        match atom {
            "logical_eq" => {
            println!(
                "{}",
                start_logical(list.to_vec())
            )
            },
            // "optimize" => println!("{}", start_optimize(list[1])),
            "exit" => return,
            _ => panic!("unknown command {:?}", list),
        }
        io::stdout().flush().unwrap();
    }
}
