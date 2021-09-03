use std::{fs::File};
use serde::*;
use egg::*;

// TODO: will need expr since a block can have other assume etc.
#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(from = "StringStmt")]
#[serde(into = "StringStmt")]
#[serde(bound = "L: egg::Language")]
pub struct Stmt<L> {
    pub lhs: RecExpr<L>,
    pub rhs: RecExpr<L>,
}

#[derive(Clone, Deserialize, Serialize, Debug)]
pub struct StringStmt {
    pub lhs: String,
    pub rhs: String
}

impl<L: egg::Language> From<StringStmt> for Stmt<L> {
    fn from(s: StringStmt) -> Self {
        let lhs: RecExpr<L> = s.lhs.parse().unwrap();
        let rhs: RecExpr<L> = s.rhs.parse().unwrap();
        Self::new(lhs, rhs)
    }
}

impl<L: egg::Language> From<Stmt<L>> for StringStmt {
    fn from(s: Stmt<L>) -> Self {
        Self {
            lhs: s.lhs.to_string(),
            rhs: s.rhs.to_string(),
        }
    }
}

impl<L> Stmt<L> {
    pub fn new (e1: RecExpr<L>, e2: RecExpr<L>) -> Self {
       Self {
           lhs: e1,
           rhs: e2
       }
    }
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(bound = "L: egg::Language")]
struct Input<L> {
    assignments: Vec<Stmt<L>>,
}

pub fn parse<L: egg::Language>(filename: &String) -> Vec<Stmt<L>> {
    let file = File::open(filename).unwrap_or_else(|_| panic!("Failed to open {}", filename));
    let input: Input<L> = serde_json::from_reader(file).unwrap();
    input.assignments
}