use std::{fmt, rc::Rc};

use crate::{
    ExpressionNodeStringifierError,
    stringifier::{ExpNodeStringifierDeBrujin, ExpressionNodeStringifier},
};

#[derive(Clone)]
pub enum ExpressionNode {
    /// Holds the name of the free variable
    FreeVariable(String),
    /// Holds the DeBrujin index to the binding lambda abstraction
    BoundVariable(usize),
    Application {
        function: Rc<ExpressionNode>,
        argument: Rc<ExpressionNode>,
    },
    Abstraction {
        parameter: String,
        body: Rc<ExpressionNode>,
    },
}

impl ExpressionNode {
    pub fn to_expression_str(&self) -> Result<String, ExpressionNodeStringifierError> {
        ExpressionNodeStringifier::new().build(self)
    }

    pub fn to_expression_str_de_brujin(&self) -> String {
        ExpNodeStringifierDeBrujin::new().build(self)
    }

    pub fn search_and_beta_reduce(self: &Rc<Self>) -> Option<Rc<Self>> {
        match self.as_ref() {
            ExpressionNode::FreeVariable(_) | ExpressionNode::BoundVariable(_) => None,
            ExpressionNode::Abstraction { parameter, body } => {
                body.search_and_beta_reduce().map(|body| {
                    Rc::new(ExpressionNode::Abstraction {
                        parameter: parameter.clone(),
                        body: body,
                    })
                })
            }
            ExpressionNode::Application { function, argument } => {
                if let ExpressionNode::Abstraction { parameter: _, body } = function.as_ref() {
                    Some(body.substitute(argument))
                } else if let Some(reduced_function) = function.search_and_beta_reduce() {
                    Some(Rc::new(ExpressionNode::Application {
                        function: reduced_function,
                        argument: Rc::clone(argument),
                    }))
                } else if let Some(reduced_argument) = argument.search_and_beta_reduce() {
                    Some(Rc::new(ExpressionNode::Application {
                        function: Rc::clone(function),
                        argument: reduced_argument,
                    }))
                } else {
                    None
                }
            }
        }
    }

    fn _substitute(
        self: &Rc<Self>,
        target_expr: &Rc<Self>,
        relative_lambda_depth: usize,
    ) -> Rc<Self> {
        match self.as_ref() {
            ExpressionNode::FreeVariable(_) => Rc::clone(self),
            ExpressionNode::BoundVariable(idx) => {
                if *idx == relative_lambda_depth {
                    Rc::clone(target_expr)
                } else {
                    Rc::clone(self)
                }
            }
            ExpressionNode::Application { function, argument } => {
                Rc::new(ExpressionNode::Application {
                    function: function._substitute(target_expr, relative_lambda_depth),
                    argument: argument._substitute(target_expr, relative_lambda_depth),
                })
            }
            ExpressionNode::Abstraction { parameter, body } => {
                Rc::new(ExpressionNode::Abstraction {
                    parameter: parameter.clone(),
                    body: body._substitute(target_expr, relative_lambda_depth + 1),
                })
            }
        }
    }

    fn substitute(self: &Rc<Self>, target_expr: &Rc<Self>) -> Rc<Self> {
        self._substitute(target_expr, 1)
    }
}

impl fmt::Debug for ExpressionNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ExpressionNode: {}", self.to_expression_str_de_brujin())
    }
}

/// Equality (`==`) for `Expr` tests alpha-equivalence. So differences in the `parameter` of [ExpressionNode::Abstraction] is ignored.
///
/// Since `Expr` uses De Bruijn indices, this corresponds to structural comparison modulo variable renaming
impl PartialEq for ExpressionNode {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::FreeVariable(l0), Self::FreeVariable(r0)) => l0 == r0,
            (Self::BoundVariable(l0), Self::BoundVariable(r0)) => l0 == r0,
            (
                Self::Application {
                    function: l_function,
                    argument: l_argument,
                },
                Self::Application {
                    function: r_function,
                    argument: r_argument,
                },
            ) => l_function == r_function && l_argument == r_argument,
            (
                Self::Abstraction {
                    parameter: _,
                    body: l_body,
                },
                Self::Abstraction {
                    parameter: _,
                    body: r_body,
                },
            ) => l_body == r_body,
            _ => false,
        }
    }
}

impl Eq for ExpressionNode {}

#[cfg(test)]
mod test {
    use crate::ExpressionTree;

    use super::*;

    #[test]
    fn test_deep_cloning() {
        let node = ExpressionNode::Abstraction {
            parameter: String::from("a"),
            body: Rc::new(ExpressionNode::Abstraction {
                parameter: String::from("b"),
                body: Rc::new(ExpressionNode::FreeVariable(String::from("c"))),
            }),
        };
        assert_eq!(
            node.to_expression_str().unwrap(),
            String::from("(a->(b->c))")
        );
        let mut node2 = node.clone();
        assert_eq!(
            node2.to_expression_str().unwrap(),
            String::from("(a->(b->c))"),
            "Node changed on clone"
        );
        if let ExpressionNode::Abstraction { parameter: _, body } = &mut node2 {
            if let ExpressionNode::Abstraction { parameter: _, body } = Rc::make_mut(body) {
                *body = Rc::new(ExpressionNode::FreeVariable(String::from("d")))
            }
        }
        assert_eq!(
            node.to_expression_str().unwrap(),
            String::from("(a->(b->c))"),
            "Original node changed"
        );
        assert_eq!(
            node2.to_expression_str().unwrap(),
            String::from("(a->(b->d))"),
            "Cloned node did not change"
        );
    }
    #[test]
    fn substitution() {
        fn check_substitution(src: ExpressionNode, target_expr: &str, expected_expr: &str) {
            let substituted_exp = Rc::new(src).substitute(
                &ExpressionTree::from_line(target_expr)
                    .expect("Failed to parse target expression")
                    .root,
            );
            let expected = ExpressionTree::from_line(expected_expr).unwrap().root;
            assert_eq!(
                substituted_exp, expected,
                "Substituted expression incorrect"
            );
        }
        check_substitution(
            ExpressionNode::Application {
                function: Rc::new(ExpressionNode::Abstraction {
                    parameter: String::from("a"),
                    body: Rc::new(ExpressionNode::BoundVariable(2)),
                }),
                argument: Rc::new(ExpressionNode::FreeVariable(String::from("c"))),
            },
            "x y",
            "((a->(x y)) c)",
        );
        check_substitution(
            ExpressionNode::Application {
                function: Rc::new(ExpressionNode::Abstraction {
                    parameter: String::from("a"),
                    body: Rc::new(ExpressionNode::BoundVariable(2)),
                }),
                argument: Rc::new(ExpressionNode::Abstraction {
                    parameter: String::from("c"),
                    body: Rc::new(ExpressionNode::FreeVariable(String::from("d"))),
                }),
            },
            "(d->c)",
            "((a->(d->c)) (c->d))",
        );
    }

    #[test]
    fn rc_clones() {
        let mut node1 = ExpressionTree::from_line("((a->((a a) (a a))) b)")
            .expect("Failed to parse tree")
            .root;
        while let Some(exp) = node1.search_and_beta_reduce() {
            node1 = exp
        }
        if let ExpressionNode::Application {
            function,
            argument: _,
        } = node1.as_ref()
        {
            if let ExpressionNode::Application {
                function,
                argument: _,
            } = function.as_ref()
            {
                if let ExpressionNode::FreeVariable(name) = function.as_ref() {
                    assert_eq!(name, "b", "Unexpected variable name")
                } else {
                    panic!("ExpressionNode is not a free variable")
                }
                assert_eq!(
                    Rc::strong_count(function),
                    4,
                    "Unexpected reference count of variable \"b\""
                )
            } else {
                panic!("Function of tree root is not an application")
            }
        } else {
            panic!("Tree root is not an abstraction!")
        }
    }
}
