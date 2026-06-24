//! Numeric expressions.
//!
//! Kept intentionally minimal: classical planning does not evaluate these. They
//! exist so numeric content can be represented if it ever needs to be carried,
//! but lowering rejects fluents before any of this is constructed.

use std::rc::Rc;

use crate::functions::Function;
use crate::terms::Term;

/// A fluent application: a function applied to a list of terms.
#[derive(Debug, Clone, PartialEq)]
pub struct Fluent {
    pub function: Function,
    pub terms: Vec<Term>,
}

/// A numeric expression tree.
#[derive(Debug, Clone)]
pub enum Expression {
    Value(f64),
    Fluent(Fluent),
    Add(Rc<Expression>, Rc<Expression>),
    Sub(Rc<Expression>, Rc<Expression>),
    Mul(Rc<Expression>, Rc<Expression>),
    Div(Rc<Expression>, Rc<Expression>),
    Min(Rc<Expression>, Rc<Expression>),
    Max(Rc<Expression>, Rc<Expression>),
}
