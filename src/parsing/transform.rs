use pest::Span;
use pest::iterators::Pair;

#[macro_use] use crate::parsing::ast::*;
use crate::parsing::parser::Rule;


fn span_to_pos(s: Span) -> (usize, usize) {
    (s.start(), s.end())
}


pub fn line_to_ast(line: Pair<Rule>) -> Item {
    match line.as_rule() {
        Rule::EOI => { Item::EOI }

        _ => {
            let mut children = line.into_inner();

            let item = item_to_ast(children.next().unwrap());

            let mut addons = vec![];

            if let Some(wheres) = children.next() {
                for item in wheres.into_inner() {
                    addons.push(enbox![item_to_ast(item)]);
                }
            }

            match item {
                Item::Declaration(elim, ty, _) => Item::Declaration(elim, ty, addons),
                Item::Definition(elim, val, _) => Item::Definition(elim, val, addons),

                _ => unreachable!(),
            }
        }
    }
}

fn item_to_ast(rule: Pair<Rule>) -> Item {
    let span = span_to_pos(rule.as_span());
    let kind = rule.as_rule();

    match kind {
        Rule::term_def => {
            let mut def_children = rule.into_inner();

            let elim_rule = def_children.next().unwrap();

            let (elim, expr) = match elim_rule.as_rule() {
                Rule::function_reduction_eliminator => {
                    let mut children = elim_rule.into_inner();

                    let head = term_eliminator_to_ast(children.next().unwrap());
                    let rhs_rule = def_children.next().unwrap();

                    let mut rhs_span = span_to_pos(rhs_rule.as_span());
                    let mut rhs = term_expr_to_ast(rhs_rule);

                    while let Some(arg_rule) = children.next() {
                        let arg_rule_span = span_to_pos(arg_rule.as_span());
                        let arg = term_eliminator_to_ast(arg_rule);

                        rhs = Expr::LambdaExpr(enbox![arg], None, enbox![rhs]);

                        rhs_span = (rhs_span.0 + arg_rule_span.0, rhs_span.1 + arg_rule_span.1);
                    }

                    (head, rhs)
                }

                _ => (term_eliminator_to_ast(elim_rule), term_expr_to_ast(def_children.next().unwrap()))
            };

            Item::Definition(elim, expr, vec![])
        }

        Rule::term_bind => {
            let (elim, ty) = term_bind_to_ast(rule);

            Item::Declaration(elim, ty, vec![])
        }

        Rule::EOI => {
            Item::EOI
        }

        _ => panic!["Unexpected rule {:?}", kind]
    }
}


fn term_bind_to_ast(rule: Pair<Rule>) -> (TermElim, Type) {
    let span = span_to_pos(rule.as_span());
    let mut children = rule.into_inner();

    let decl_eliminator = term_eliminator_to_ast(children.next().unwrap());

    let texp = children.next().unwrap();
    let type_expr = type_expr_to_ast(texp);

    (decl_eliminator, type_expr)
}

fn term_eliminator_to_ast(rule: Pair<Rule>) -> TermElim {
    let mut span = span_to_pos(rule.as_span());
    let child = rule.into_inner().next().unwrap();

    match child.as_rule() {
        Rule::lambda_eliminator => {
            let mut children = child.into_inner();

            let (arg, ty) = lambda_arg_to_pair(children.next().unwrap().into_inner().next().unwrap());
            let body = term_eliminator_to_ast(children.next().unwrap());

            TermElim::Lambda(enbox![arg], enbox![ty], enbox![body])
        }

        Rule::pair_eliminator => {
            let mut children = child.into_inner();

            let v1 = term_eliminator_to_ast(children.next().unwrap());
            let v2 = term_eliminator_to_ast(children.next().unwrap());

            TermElim::Pair(enbox![v1], enbox![v2])
        }

        Rule::unit_term => {
            TermElim::Unit
        }

        Rule::identifier => {
            TermElim::Identifier(child.as_str().to_string())
        }

        Rule::term_eliminator | Rule::atom_term_eliminator => {
            span = span_to_pos(child.as_span());

            term_eliminator_to_ast(child)
        }

        _ => panic!["Unexpected rule {:?}", child.as_rule()]
    }
}


fn lambda_arg_to_pair(rule: Pair<Rule>) -> (TermElim, Option<Type>) {
    match rule.as_rule() {
        Rule::term_bind => {
            let bind = term_bind_to_ast(rule);

            (bind.0, Some(bind.1))
        }

        Rule::atom_term_eliminator => {
            let child = rule.into_inner().next().unwrap();

            (term_eliminator_to_ast(child), None)
        }

        _ => unreachable!()
    }
}

fn dependent_head_to_ast(rule: Pair<Rule>) -> (Option<TermElim>, Type) {
    let span = span_to_pos(rule.as_span());
    let child = rule.into_inner().next().unwrap();

    match child.as_rule() {
        Rule::type_expr_compact => {
            (None, type_expr_to_ast(child))
        }

        Rule::term_bind => {
            let bind = term_bind_to_ast(child);

            (Some(bind.0), bind.1)
        }

        _ => unreachable!()
    }
}


fn dim_expr_to_ast(rule: Pair<Rule>) -> DimExpr {
    let mut span = span_to_pos(rule.as_span());
    let child = rule.into_inner().next().unwrap();

    match child.as_rule() {
        Rule::identifier => { DimExpr::Name(child.as_str().to_string()) }

        Rule::dim_one => { DimExpr::One }

        Rule::dim_zero => { DimExpr::Zero }

        Rule::dim_inverted => {
            let inner = dim_expr_to_ast(child.into_inner().next().unwrap());

            DimExpr::Invert(enbox![inner])
        }

        Rule::dim_max => {
            let mut children = child.into_inner();

            let a = dim_expr_to_ast(children.next().unwrap());
            let b = dim_expr_to_ast(children.next().unwrap());

            DimExpr::Or(enbox![a], enbox![b])
        }

        Rule::dim_min => {
            let mut children = child.into_inner();

            let a = dim_expr_to_ast(children.next().unwrap());
            let b = dim_expr_to_ast(children.next().unwrap());

            DimExpr::And(enbox![a], enbox![b])
        }

        Rule::dim_expr | Rule::dim_expr_compact => {
            let paren_expr = child.into_inner().next().unwrap();
            span = span_to_pos(paren_expr.as_span());

            dim_expr_to_ast(paren_expr)
        }

        _ => unreachable!()
    }
}

fn term_expr_to_ast(rule: Pair<Rule>) -> Expr {
    let mut span = span_to_pos(rule.as_span());
    let child = rule.into_inner().next().unwrap();

    match child.as_rule() {
        Rule::function_reduction => {
            let (head, arg) = function_reduction_to_ast(child);

            Expr::FunctionApplication(enbox![head], enbox![arg])
        }

        Rule::path_reduction => {
            let mut children = child.into_inner();

            let path = term_expr_to_ast(children.next().unwrap());
            let dim = dim_expr_to_ast(children.next().unwrap());

            Expr::PathReduction(enbox![path], dim)
        }

        Rule::pair_reduction => {
            let mut children = child.into_inner();

            let val = term_expr_to_ast(children.next().unwrap());
            let mut reduc = val;

            while let Some(index) = children.next() {
                let idx_span = span_to_pos(index.as_span());
                let idx: usize = str::parse(index.as_str()).unwrap();

                for _ in 0..idx/2 {
                    reduc = Expr::PairSecond(enbox![reduc]);
                }

                if idx%2 == 1 {
                    reduc = Expr::PairFirst(enbox![reduc]);
                }
            }

            reduc
        }

        Rule::identifier => {
            Expr::TermValue(child.as_str().to_string())
        }

        Rule::unit_term => { Expr::UnitTerm }

        Rule::lambda_expr => {
            let mut children = child.into_inner();

            let (arg, ty) = lambda_arg_to_pair(children.next().unwrap());
            let body = term_expr_to_ast(children.next().unwrap());

            Expr::LambdaExpr(enbox![arg], ty, enbox![body])
        }

        Rule::path_expr => {
            let mut children = child.into_inner();

            let dim = children.next().unwrap();
            let body = term_expr_to_ast(children.next().unwrap());

            Expr::PathExpr(dim.as_str().to_string(), enbox![body])
        }

        Rule::term_expr | Rule::atom_expr_init => {
            span = span_to_pos(child.as_span());

            term_expr_to_ast(child)
        }

        Rule::type_expr | Rule::type_expr_compact => {
            Expr::TypeValue(type_expr_to_ast(child))
        }

        _ => unreachable!()
    }
}

fn type_expr_to_ast(rule: Pair<Rule>) -> Type {
    let mut span = span_to_pos(rule.as_span());
    let inner = rule.into_inner().next().unwrap();

    match inner.as_rule() {
        Rule::function_type => {
            let mut children = inner.into_inner();

            let (maybe_elim, head) = dependent_head_to_ast(children.next().unwrap());
            let body = type_expr_to_ast(children.next().unwrap());

            Type::Function(maybe_elim, enbox![head], enbox![body])
        }

        Rule::pair_type => {
            let mut children = inner.into_inner();

            let (maybe_elim, head) = dependent_head_to_ast(children.next().unwrap());
            let body = type_expr_to_ast(children.next().unwrap());

            Type::Pair(maybe_elim, enbox![head], enbox![body])
        }

        Rule::either_type => {
            let mut children = inner.into_inner();

            let a = type_expr_to_ast(children.next().unwrap());
            let b = type_expr_to_ast(children.next().unwrap());

            Type::Either(enbox![a], enbox![b])
        }

        Rule::path_type => {
            let mut children = inner.into_inner();

            let a = term_expr_to_ast(children.next().unwrap());
            let ty = type_expr_to_ast(children.next().unwrap());
            let b = term_expr_to_ast(children.next().unwrap());

            Type::Path(enbox![ty], enbox![a], enbox![b])
        }

        Rule::function_reduction => {
            let (head, arg) = function_reduction_to_ast(inner);

            Type::FunctionApplication(enbox![head], enbox![arg])
        }

        Rule::type_expr => {
            span = span_to_pos(inner.as_span());

            type_expr_to_ast(inner)
        }

        Rule::identifier => {
            Type::TypeName(inner.as_str().to_string())
        }

        Rule::unit_type => { Type::Unit }
        Rule::zero_type => { Type::Zero }

        _ => panic!("Unexpected rule {:?}", inner.as_rule())
    }
}


fn function_reduction_to_ast(rule: Pair<Rule>) -> (Expr, Expr) {
    let mut children = rule.into_inner();

    let first = children.next().unwrap();
    let first_span = span_to_pos(first.as_span());

    match first.as_rule() {
        Rule::function_reduction_compact => {
            let second = children.next();
            let head = function_reduction_to_ast(first);

            if let Some(arg_rule) = second {
                let arg = term_expr_to_ast(arg_rule);

                (Expr::FunctionApplication(enbox![head.0], enbox![head.1]), arg)

            } else {
                head
            }
        }

        Rule::atom_expr_init => {
            let head = term_expr_to_ast(first);
            let second = children.next().unwrap();

            match second.as_rule() {
                Rule::term_expr => {
                    (head, term_expr_to_ast(second))
                }

                Rule::atom_expr => {
                    let mut span = span_to_pos(second.as_span());
                    span = (first_span.0 + span.0, first_span.1 + span.1);

                    let mut ret_head = head;
                    let mut ret_arg = term_expr_to_ast(second);

                    while let Some(arg) = children.next() {
                        let arg_span = span_to_pos(arg.as_span());

                        ret_head = Expr::FunctionApplication(enbox![ret_head], enbox![ret_arg]);
                        ret_arg = term_expr_to_ast(arg);

                        span = (span.0 + arg_span.0, span.1 + arg_span.1);
                    }

                    (ret_head, ret_arg)
                }

                _ => unreachable!()
            }
        }

        _ => unreachable!()
    }
}
