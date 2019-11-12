use std::fmt;


/// Tools for representing and manipulating AST.


/// Creates a structure implementing the `Node` trait, adding extra attributes.
///
#[macro_export]
macro_rules! mk_node {
    ($name:ident => $($field:ident : $ty:ty),*) => {
        #[derive(Clone)]
        #[derive(Debug)]
        pub struct $name {
            position: (usize, usize),
            index: usize,
            span: usize,

            $($field: $ty),*
        }

        impl Node for $name {
            fn position(&self) -> &(usize, usize) { &self.position }
            fn index(&self) -> &usize { &self.index }
            fn span(&self) -> &usize { &self.span }
        }

        impl $name {
            pub fn new(rule_span: &(usize, usize), $($field : $ty),*) -> $name {
                let (position, index, span) = ((rule_span.0, rule_span.1), rule_span.0, rule_span.1 - rule_span.0);

                $name {
                    position,
                    index,
                    span,

                    $(
                        $field
                    ),*
                }
            }

            $(
                pub fn $field ( &self ) -> & $ty { &self. $field }
            )*
        }
    }
}

#[macro_export]
macro_rules! mk_node_display {
    ($name:ident => $($field:ident : $ty:ty),*) => {
        #[derive(Clone)]
        #[derive(Debug)]
        pub struct $name {
            position: (usize, usize),
            index: usize,
            span: usize,

            $($field: $ty),*
        }

        impl Node for $name {
            fn position(&self) -> &(usize, usize) { &self.position }
            fn index(&self) -> &usize { &self.index }
            fn span(&self) -> &usize { &self.span }
        }

        impl $name {
            pub fn new(rule_span: &(usize, usize), $($field : $ty),*) -> $name {
                let (position, index, span) = ((rule_span.0, rule_span.1), rule_span.0, rule_span.1 - rule_span.0);

                $name {
                    position,
                    index,
                    span,

                    $(
                        $field
                    ),*
                }
            }

            $(
                pub fn $field ( &self ) -> & $ty { &self. $field }
            )*
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let mut s = String::new();

                $(
                    s.push_str(&format!["{}, ", self. $field]);
                )*

                write![f, "[{}  {}]", stringify![ $name ], s]
            }
        }
    }
}

/// Shorthand for declaring recursive types
///
#[macro_export]
macro_rules! boxed {
    ($ty:ty) => { Box<$ty> }
}

/// Shorthand for initialising recursive types
///
#[macro_export]
macro_rules! enbox {
    ($expr:expr) => { Box::new($expr) }
}

pub trait Node {
    fn position(&self) -> &(usize, usize);
    fn index(&self) -> &usize;
    fn span(&self) -> &usize;
}



mk_node_display!{ Term => name: String }
mk_node_display!{ TermDecl => elim: TermEliminator, ty: Type }
mk_node_display!{ TermDef => elim: TermEliminator, val: Expression }

mk_node_display!{ Type => body: TypeExpr }//   So that nested expressions are properly indexed.
mk_node_display!{ Expression => body: Expr }//                ~| ditto |~
mk_node_display!{ DimensionExpression => body: DimExpr }//    ~| ditto |~

mk_node_display!{ TermEliminator => body: TermElim }

mk_node_display!{ Integer => value: i64 }

mk_node!{ DependentHead => bound_term: Option<TermEliminator>, ty: Type }
impl fmt::Display for DependentHead {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.bound_term {
            Some(elim) => {
                write![f, "[DependentHead  {}: {}]", elim, self.ty]
            }

            None => {
                write![f, "[DependentHead  _: {}]", self.ty]
            }
        }
    }
}


/// Term eliminator
///
#[derive(Clone)]
#[derive(Debug)]
pub enum TermElim {
    Unit,
    Identifier(String),

    Pair(boxed![TermEliminator], boxed![TermEliminator]),
    Lambda(boxed![TermEliminator], Option<Type>, boxed![TermEliminator]),
}


/// Inner representation of a type
///
#[derive(Clone)]
#[derive(Debug)]
pub enum TypeExpr {
    Unit,
    Zero,

    TypeName(String),
    FunctionApplication(boxed![Expression], boxed![Expression]),

    Either(boxed![Type], boxed![Type]),
    Pair(boxed![DependentHead], boxed![Type]),
    Function(boxed![DependentHead], boxed![Type]),

    Path(boxed![Type], boxed![Expression], boxed![Expression]),
}

/// Inner representation of an expression involving dimension variables
///
#[derive(Clone)]
#[derive(Debug)]
pub enum DimExpr {
    Zero,
    One,

    Name(String),

    Invert(boxed![DimensionExpression]),
    Or(boxed![DimensionExpression], boxed![DimensionExpression]),// |
    And(boxed![DimensionExpression], boxed![DimensionExpression]),// &
}

/// Inner representation of an expression
///
#[derive(Clone)]
#[derive(Debug)]
pub enum Expr {
    UnitTerm,

    TermValue(String),
    TypeValue(Type),
    // IntegerValue(Integer),
    //
    // Add(boxed![Expression], boxed![Expression]),
    // Sub(boxed![Expression], boxed![Expression]),
    // Mul(boxed![Expression], boxed![Expression]),
    // Div(boxed![Expression], boxed![Expression]),

    FunctionApplication(boxed![Expression], boxed![Expression]),
    PathReduction(boxed![Expression], DimensionExpression),

    LambdaExpression(boxed![TermEliminator], Option<Type>, boxed![Expression]),
    PathExpression(Term, boxed![Expression]),

    PairFirst(boxed![Expression]),
    PairSecond(boxed![Expression]),
}

#[derive(Debug)]
pub enum Item {
    Declaration(TermDecl, Vec<boxed![Item]>),
    Definition(TermDef, Vec<boxed![Item]>),

    EOI
}


/// Display Schenanigans
///
impl fmt::Display for TermElim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TermElim::Unit => write![f, "[TermElim  ()]"],

            TermElim::Pair(box a, box b) => write![f, "[TermElim  ({}, {})]", a, b],

            TermElim::Lambda(box arg, Some(t), box ret) => write![f, "[TermElim  \\{}: {} -> {}]", arg, t, ret],
            TermElim::Lambda(box arg, None, box ret) => write![f, "[TermElim  \\{}: _ -> {}]", arg, ret],

            TermElim::Identifier(s) => write![f, "[TermElim  {}]", s],
        }
    }
}

impl fmt::Display for TypeExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TypeExpr::Unit => write![f, "[TypeExpr  1t]"],
            TypeExpr::Zero => write![f, "[TypeExpr  0t]"],

            TypeExpr::TypeName(s) => write![f, "[TypeExpr  {}]", s],
            TypeExpr::FunctionApplication(box a, box b) => write![f, "[TypeExpr  {} {}]", a, b],

            TypeExpr::Either(box a, box b) => write![f, "[TypeExpr  {} | {}]", a, b],
            TypeExpr::Pair(box a, box b) => write![f, "[TypeExpr  {} # {}]", a, b],
            TypeExpr::Function(box a, box b) => write![f, "[TypeExpr  {} -> {}]", a, b],

            TypeExpr::Path(box t, box a, box b) => write![f, "[TypeExpr  {} ==[{}] {}]", a, t, b],
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

            Expr::LambdaExpression(box arg, Some(t), box ret) => write![f, "[Expr  \\{}: {} -> {}]", arg, t, ret],
            Expr::LambdaExpression(box arg, None, box ret) => write![f, "[Expr  \\{}: _ -> {}]", arg, ret],

            Expr::PathExpression(dim_name, box ret) => write![f, "[Expr  <{}> {}]", dim_name, ret],

            Expr::PairFirst(box exp) => write![f, "[Expr  {}.1]", exp],
            Expr::PairSecond(box exp) => write![f, "[Expr  {}.2]", exp],
        }
    }
}

impl fmt::Display for Item {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Item::Declaration(decl, wheres) => {
                let mut s = String::new();

                for box item in wheres {
                    s.push_str(&format!["{}", item]);
                }

                write![f, "[Item  {} where {}]", decl, s]
            }

            Item::Definition(def, wheres) => {
                let mut s = String::new();

                for box item in wheres {
                    s.push_str(&format!["{}", item]);
                }

                write![f, "[Item  {} where {}]", def, s]
            }

            Item::EOI => { write![f, "[Item EOI]"] }
        }
    }
}
