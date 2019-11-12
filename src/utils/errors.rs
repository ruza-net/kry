use std::fmt;
use std::error::Error;

use crate::parsing::ast::{ Expression, Type };


#[derive(Debug)]
pub enum PreparationError {
    NoSource,
    ReadError(String),
    OpenError(String),

    ParseError(String),
}

impl fmt::Display for PreparationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            PreparationError::NoSource => write![f, "No source file specified!"],
            PreparationError::ReadError(err_msg) => write![f, "Error while reading file: {}", err_msg],
            PreparationError::OpenError(err_msg) => write![f, "Error while opening file: {}", err_msg],

            PreparationError::ParseError(err_msg) => write![f, "{}", &err_msg],

            _ => unreachable!(),
        }
    }
}

impl Error for PreparationError {}


#[derive(Debug)]
pub enum TypeError {
    NotDeclared(String),
    NotDefined(String),

    TypesDoNotMatch(Expression, Type),
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            TypeError::NotDeclared(term) => write![f, "Term not declared: {}", term],
            TypeError::NotDefined(term) => write![f, "Term not defined: {}", term],

            TypeError::TypesDoNotMatch(t1, t2) => write![f, "Types do not match:\n\t(a)  {}\n\t(b)  {}", t1, t2],

            _ => unreachable!(),
        }
    }
}

impl Error for TypeError {}
