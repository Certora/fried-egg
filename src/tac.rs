use core::ops::{BitAnd, BitOr, BitXor};
use egg::{define_language, Id};
use evm_core::eval::arithmetic as arith;
use evm_core::eval::bitwise;
use primitive_types::U256;

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
        Num(U256),
        Var(egg::Symbol),
    }
}

fn boolU256(b: bool) -> U256 {
    if b {
        U256::one()
    } else {
        U256::zero()
    }
}

fn U256bool(u: U256) -> bool {
    u != U256::zero()
}

pub fn eval_tac(
    op: &TAC,
    first: Option<U256>,
    second: Option<U256>,
) -> Option<U256> {
    Some(match op {
        TAC::Var(_) => None?,
        TAC::Num(n) => *n,
        TAC::Havoc => None?,

        TAC::Sub(_) => first?.overflowing_sub(second?).0,
        TAC::Div(_) => arith::div(first?, second?),
        TAC::BWAnd(_) => first?.bitand(second?),
        TAC::BWOr(_) => first?.bitand(second?),
        TAC::ShiftLeft(_) => bitwise::shl(first?, second?),
        TAC::ShiftRight(_) => bitwise::shr(first?, second?),

        TAC::LOr(_) => boolU256(U256bool(first?) || U256bool(second?)),
        TAC::LAnd(_) => boolU256(U256bool(first?) && U256bool(second?)),

        TAC::Gt(_) => boolU256(first?.gt(&second?)),
        TAC::Ge(_) => boolU256(first?.ge(&second?)),
        TAC::Lt(_) => boolU256(first?.lt(&second?)),
        TAC::Le(_) => boolU256(first?.le(&second?)),
        TAC::Eq(_) => boolU256(first?.eq(&second?)),

        TAC::Slt(_) => bitwise::slt(first?, second?),
        TAC::Sle(_) => if first? == second? { boolU256(true) } else {bitwise::slt(first?, second?)},
        TAC::Sgt(_) => bitwise::sgt(first?, second?),
        TAC::Sge(_) => if first? == second? { boolU256(true) } else {bitwise::sgt(first?, second?)},

        TAC::Add(_) => first?.overflowing_add(second?).0,
        TAC::Mul(_) => first?.overflowing_mul(second?).0,


        TAC::LNot(_) => boolU256(!U256bool(first?)),
        TAC::BWNot(_) => bitwise::not(first?),
    })
}
