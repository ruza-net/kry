use crate::parsing::ast::*;
use crate::parsing::transform::*;
use crate::typing::type_checker;
use crate::utils::errors::PreparationError;

use std::fs::File;
use std::path::Path;
use std::io::prelude::*;

use pest::Parser;

#[derive(Parser)]
#[grammar = "parsing/grammar.pest"]
pub struct KryParser;


pub fn extract_lines(path_str: &str) -> Result<Vec<Item>, PreparationError> {
    match Path::new(path_str).canonicalize() {
        Ok(path) => {

            match File::open(path) {
                Ok(mut f) => {
                    let mut contents = String::new();

                    match f.read_to_string(&mut contents) {
                        Ok(_) => {
                            match KryParser::parse(Rule::root, &contents) {
                                Ok(mut pairs) => {
                                    let lines = pairs.next().unwrap().into_inner();
                                    let mut converted = vec![];

                                    for line in lines {
                                        converted.push(line_to_ast(line));
                                    }

                                    Ok(converted)
                                }

                                Err(e) => {
                                    Err(PreparationError::ParseError(e.to_string()))
                                }
                            }
                        }

                        Err(e) => {
                            Err(PreparationError::ReadError(e.to_string()))
                        }
                    }
                }

                Err(e) => {
                    Err(PreparationError::OpenError(e.to_string()))
                }
            }
        }

        Err(e) => {
            Err(PreparationError::OpenError(e.to_string()))
        }
    }
}
