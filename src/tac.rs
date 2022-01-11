use egg::{define_language, Id};

define_language! {
    pub enum TAC {
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "~" = Neg([Id; 1]),
        ">" = Gt([Id; 2]),
        "<" = Lt([Id; 2]),
        ">=" = Ge([Id; 2]),
        "<=" = Le([Id; 2]),
        "Havoc" = Havoc, // TODO: not the same thing!
        Bool(bool),
        // TODO: this should be 256 bits not 64 bits
        Num(i64),
        Var(egg::Symbol),
    }
}