#![feature(box_patterns)]

extern crate colored;

extern crate pest;
//#[macro_use] extern crate pest_ast;
#[macro_use] extern crate pest_derive;

mod utils;
mod typing;
mod parsing;

use utils::msg;
use utils::errors::PreparationError;

use parsing::parser::extract_lines;


use std::env;
use std::process;


macro_rules! error {
    ($scope:expr , $msg:expr) => {
        msg::error($scope, $msg);

        process::exit(1);
    };
}

fn main() {
    if let Err(e) = program() {
        let err_msg = &format!["{}", e];

        error!["kry_preparation", err_msg];
    }
}


fn program() -> Result<(), PreparationError> {
    let args: Vec<String> = env::args().collect();

    if args.len() == 2 {
        run_on_source(&args[1])

    } else {
        Err(PreparationError::NoSource)
    }
}

fn run_on_source(path_str: &str) -> Result<(), PreparationError> {
    let result = extract_lines(path_str);

    match result {
        Ok(lines) => {
            for line in lines {
                println!("{}\n\n", line);
            }

            Ok(())
        }

        Err(e) => {
            Err(e)
        }
    }
}
