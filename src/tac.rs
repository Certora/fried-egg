use egg::{define_language, Id};

define_language! {
    pub enum TAC {
        "-" = Sub([Id; 2]),
        "/" = Div([Id; 2]),
        "&" = BWAnd([Id; 2]),
        "|" = BWOr([Id; 2]),
        "<<" = ShiftLeft([Id; 2]),
        ">>" = ShiftRight([Id; 2]),
        "||" = LOr([Id; 2]),
        "&&" = LAnd([Id; 2]),

        ">" = Gt([Id; 2]),
        ">=" = Ge([Id; 2]),
        "<" = Lt([Id; 2]),
        "<=" = Le([Id; 2]),
        "==" = Eq([Id; 2]),
        "s<" = Slt([Id; 2]),
        "s<=" = Sle([Id; 2]),
        "s>" = Sgt([Id; 2]),
        "s>=" = Sge([Id; 2]),

        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),

        "!" = LNot([Id; 1]),
        "~" = BWNot([Id; 1]),
        
        "Havoc" = Havoc, // TODO: not the same thing!
        Bool(bool),
        // TODO: this should be 256 bits not 64 bits
        Num(i64),
        Var(egg::Symbol),
    }
}