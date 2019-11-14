use std::fmt;


macro_rules! boxed { ($ty:ty) => { Box< $ty > } }
macro_rules! enbox { ($expr:expr) => { Box::new($expr) } }


/// Term eliminator
///
#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
pub enum TermElim {
    Unit,
    Identifier(String),

    Pair(boxed![TermElim], boxed![TermElim]),
    Lambda(boxed![TermElim], boxed![Option<Type>], boxed![TermElim]),
}


/// Inner representation of a type
///
#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
pub enum Type {
    Unit,
    Zero,

    TypeName(String),
    FunctionApplication(boxed![Expr], boxed![Expr]),

    Either(boxed![Type], boxed![Type]),
    Pair(Option<TermElim>, boxed![Type], boxed![Type]),
    Function(Option<TermElim>, boxed![Type], boxed![Type]),

    Path(boxed![Type], boxed![Expr], boxed![Expr]),
}

/// Inner representation of an expression involving dimension variables
///
#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
pub enum DimExpr {
    Zero,
    One,

    Name(String),

    Invert(boxed![DimExpr]),
    Or(boxed![DimExpr], boxed![DimExpr]),// |
    And(boxed![DimExpr], boxed![DimExpr]),// &
}

/// Inner representation of an expression
///
#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
pub enum Expr {
    UnitTerm,

    TermValue(String),
    TypeValue(Type),
    // IntegerValue(Integer),
    //
    // Add(boxed![Expr], boxed![Expr]),
    // Sub(boxed![Expr], boxed![Expr]),
    // Mul(boxed![Expr], boxed![Expr]),
    // Div(boxed![Expr], boxed![Expr]),

    FunctionApplication(boxed![Expr], boxed![Expr]),
    PathReduction(boxed![Expr], DimExpr),

    LambdaExpr(boxed![TermElim], Option<Type>, boxed![Expr]),
    PathExpr(String, boxed![Expr]),

    PairFirst(boxed![Expr]),
    PairSecond(boxed![Expr]),
}

#[derive(Debug)]
pub enum Item {
    Declaration(TermElim, Type, Vec<boxed![Item]>),
    Definition(TermElim, Expr, Vec<boxed![Item]>),

    EOI
}


/// Display Schenanigans
///
impl fmt::Display for TermElim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TermElim::Unit => write![f, "[TermElim  ()]"],

            TermElim::Pair(box a, box b) => write![f, "[TermElim  ({}, {})]", a, b],

            TermElim::Lambda(box arg, box Some(t), box ret) => write![f, "[TermElim  \\{}: {} -> {}]", arg, t, ret],
            TermElim::Lambda(box arg, box None, box ret) => write![f, "[TermElim  \\{}: _ -> {}]", arg, ret],

            TermElim::Identifier(s) => write![f, "[TermElim  {}]", s],
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Unit => write![f, "[Type  1t]"],
            Type::Zero => write![f, "[Type  0t]"],

            Type::TypeName(s) => write![f, "[Type  {}]", s],
            Type::FunctionApplication(box a, box b) => write![f, "[Type  {} {}]", a, b],

            Type::Either(box a, box b) => write![f, "[Type  {} | {}]", a, b],

            Type::Pair(Some(elim), box a, box b) => write![f, "[Type  ({} : {}) # {}]", elim, a, b],
            Type::Pair(None, box a, box b) => write![f, "[Type  {} # {}]", a, b],

            Type::Function(Some(elim), box a, box b) => write![f, "[Type  ({} : {}) -> {}]", elim, a, b],
            Type::Function(None, box a, box b) => write![f, "[Type  {} -> {}]", a, b],

            Type::Path(box t, box a, box b) => write![f, "[Type  {} ==[{}] {}]", a, t, b],
        }
    }
}

impl fmt::Display for DimExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DimExpr::Zero => write![f, "[DimExpr  0i]"],
            DimExpr::One => write![f, "[DimExpr  1i]"],

            DimExpr::Name(s) => write![f, "[DimExpr  {}]", s],

            DimExpr::Invert(box exp) => write![f, "[DimExpr  ~{}]", exp],
            DimExpr::Or(box a, box b) => write![f, "[DimExpr  {} | {}]", a, b],
            DimExpr::And(box a, box b) => write![f, "[DimExpr  {} & {}]", a, b],
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::UnitTerm => write![f, "[Expr  ()]"],

            Expr::TermValue(s) => write![f, "[Expr  {}]", s],
            Expr::TypeValue(t) => write![f, "[Expr  {}]", t],
            // Expr::IntegerValue(i) => write![f, "[Expr  {}]", i],
            //
            // Expr::Add(box a, box b) => write![f, "[Expr  {} + {}]", a, b],
            // Expr::Sub(box a, box b) => write![f, "[Expr  {} - {}]", a, b],
            // Expr::Mul(box a, box b) => write![f, "[Expr  {} * {}]", a, b],
            // Expr::Div(box a, box b) => write![f, "[Expr  {} / {}]", a, b],

            Expr::FunctionApplication(box head, box arg) => write![f, "[Expr  {} {}]", head, arg],
            Expr::PathReduction(box head, dim_exp) => write![f, "[Expr  {} @ {}]", head, dim_exp],

            Expr::LambdaExpr(box arg, Some(t), box ret) => write![f, "[Expr  \\{}: {} -> {}]", arg, t, ret],
            Expr::LambdaExpr(box arg, None, box ret) => write![f, "[Expr  \\{}: _ -> {}]", arg, ret],

            Expr::PathExpr(dim_name, box ret) => write![f, "[Expr  <{}> {}]", dim_name, ret],

            Expr::PairFirst(box exp) => write![f, "[Expr  {}.1]", exp],
            Expr::PairSecond(box exp) => write![f, "[Expr  {}.2]", exp],
        }
    }
}

impl fmt::Display for Item {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Item::Declaration(elim, ty, wheres) => {
                let mut s = String::new();

                for box item in wheres {
                    s.push_str(&format!["{}", item]);
                }

                write![f, "[Item  {} : {}  where {}]", elim, ty, s]
            }

            Item::Definition(elim, expr, wheres) => {
                let mut s = String::new();

                for box item in wheres {
                    s.push_str(&format!["{}", item]);
                }

                write![f, "[Item  {} = {}  where {}]", elim, expr, s]
            }

            Item::EOI => { write![f, "[Item EOI]"] }
        }
    }
}
