use std::collections::HashMap;

use crate::parsing::ast::*;
use crate::utils::errors::TypeError;


pub struct TypeChecker {
    term_types: HashMap<String, Type>,
    term_vals: HashMap<String, Expression>,

    items: Vec<Item>
}

impl TypeChecker {
    pub fn new(items: Vec<Item>) -> TypeChecker {
        TypeChecker {
            term_types: HashMap::new(),
            term_vals: HashMap::new(),

            items,
        }
    }

    fn types_equal(&self, t1: &Type, t2: &Type) -> bool {
        match t1.body() {
            TypeExpr::Unit => { if let TypeExpr::Unit = t2.body() { true } else { false } }
            TypeExpr::Zero => { if let TypeExpr::Zero = t2.body() { true } else { false } }

            TypeExpr::Either(box a1, box b1) => {
                if let TypeExpr::Either(box a2, box b2) = t2.body() {
                    (self.types_equal(a1, a2) && self.types_equal(b1, b2)) || (self.types_equal(a1, b2) && self.types_equal(b1, a2))

                } else {
                    false
                }
            }

            TypeExpr::Function(box head1, box ret_ty1) => {
                if let TypeExpr::Function(box head2, box ret_ty2) = t2.body() {
                    self.types_equal(ret_ty1, ret_ty2) &&
                }
            }
        }
    }

    pub fn infer_type(&self, expr: Expression) -> Type {
        //
    }

    pub fn check(&self, expr: Expression, t2: Type) -> Result<(), TypeError> {
        let t1 = self.infer_type(expr);

        if self.types_equal(&t1, &t2) {
            Ok(())

        } else {
            Err(TypeError::TypesDoNotMatch(expr, t2))
        }
    }
}
